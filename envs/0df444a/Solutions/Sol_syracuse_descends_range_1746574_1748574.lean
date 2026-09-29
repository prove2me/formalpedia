-- Prove2me | solution 1 for syracuse_descends_range_1746574_1748574
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:35:37.735097+00:00
-- url     : https://prove2.me/submissions/1455b29b-bfe0-40b2-ad9c-0150b172500e

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


theorem B1966081 : Blo 1746574 1966081 := bbase (se 2 (by rfl) ⟨737280, by rfl⟩ : syracuseStep 1966081 = 1474561) (by norm_num)
theorem B4423693 : Blo 1746574 4423693 := bbase (se 3 (by rfl) ⟨829442, by rfl⟩ : syracuseStep 4423693 = 1658885) (by norm_num)
theorem B2621453 : Blo 1746574 2621453 := bbase (se 3 (by rfl) ⟨491522, by rfl⟩ : syracuseStep 2621453 = 983045) (by norm_num)
theorem B3932189 : Blo 1746574 3932189 := bbase (se 3 (by rfl) ⟨737285, by rfl⟩ : syracuseStep 3932189 = 1474571) (by norm_num)
theorem B2949149 : Blo 1746574 2949149 := bbase (se 3 (by rfl) ⟨552965, by rfl⟩ : syracuseStep 2949149 = 1105931) (by norm_num)
theorem B2621477 : Blo 1746574 2621477 := bbase (se 4 (by rfl) ⟨245763, by rfl⟩ : syracuseStep 2621477 = 491527) (by norm_num)
theorem B2211877 : Blo 1746574 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1966117 : Blo 1746574 1966117 := bbase (se 4 (by rfl) ⟨184323, by rfl⟩ : syracuseStep 1966117 = 368647) (by norm_num)
theorem B2621501 : Blo 1746574 2621501 := bbase (se 3 (by rfl) ⟨491531, by rfl⟩ : syracuseStep 2621501 = 983063) (by norm_num)
theorem B1966153 : Blo 1746574 1966153 := bbase (se 2 (by rfl) ⟨737307, by rfl⟩ : syracuseStep 1966153 = 1474615) (by norm_num)
theorem B2621525 : Blo 1746574 2621525 := bbase (se 8 (by rfl) ⟨15360, by rfl⟩ : syracuseStep 2621525 = 30721) (by norm_num)
theorem B3932261 : Blo 1746574 3932261 := bbase (se 4 (by rfl) ⟨368649, by rfl⟩ : syracuseStep 3932261 = 737299) (by norm_num)
theorem B3317861 : Blo 1746574 3317861 := bbase (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) (by norm_num)
theorem B2621549 : Blo 1746574 2621549 := bbase (se 3 (by rfl) ⟨491540, by rfl⟩ : syracuseStep 2621549 = 983081) (by norm_num)
theorem B1966189 : Blo 1746574 1966189 := bbase (se 3 (by rfl) ⟨368660, by rfl⟩ : syracuseStep 1966189 = 737321) (by norm_num)
theorem B4423805 : Blo 1746574 4423805 := bbase (se 3 (by rfl) ⟨829463, by rfl⟩ : syracuseStep 4423805 = 1658927) (by norm_num)
theorem B2621573 : Blo 1746574 2621573 := bbase (se 4 (by rfl) ⟨245772, by rfl⟩ : syracuseStep 2621573 = 491545) (by norm_num)
theorem B1966225 : Blo 1746574 1966225 := bbase (se 2 (by rfl) ⟨737334, by rfl⟩ : syracuseStep 1966225 = 1474669) (by norm_num)
theorem B2949277 : Blo 1746574 2949277 := bbase (se 3 (by rfl) ⟨552989, by rfl⟩ : syracuseStep 2949277 = 1105979) (by norm_num)
theorem B2621597 : Blo 1746574 2621597 := bbase (se 3 (by rfl) ⟨491549, by rfl⟩ : syracuseStep 2621597 = 983099) (by norm_num)
theorem B2875565 : Blo 1746574 2875565 := bbase (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) (by norm_num)
theorem B3932333 : Blo 1746574 3932333 := bbase (se 3 (by rfl) ⟨737312, by rfl⟩ : syracuseStep 3932333 = 1474625) (by norm_num)
theorem B2621621 : Blo 1746574 2621621 := bbase (se 5 (by rfl) ⟨122888, by rfl⟩ : syracuseStep 2621621 = 245777) (by norm_num)
theorem B1966261 : Blo 1746574 1966261 := bbase (se 5 (by rfl) ⟨92168, by rfl⟩ : syracuseStep 1966261 = 184337) (by norm_num)
theorem B2621645 : Blo 1746574 2621645 := bbase (se 3 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 2621645 = 983117) (by norm_num)
theorem B2212049 : Blo 1746574 2212049 := bbase (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) (by norm_num)
theorem B1966297 : Blo 1746574 1966297 := bbase (se 2 (by rfl) ⟨737361, by rfl⟩ : syracuseStep 1966297 = 1474723) (by norm_num)
theorem B2621669 : Blo 1746574 2621669 := bbase (se 4 (by rfl) ⟨245781, by rfl⟩ : syracuseStep 2621669 = 491563) (by norm_num)
theorem B3932405 : Blo 1746574 3932405 := bbase (se 5 (by rfl) ⟨184331, by rfl⟩ : syracuseStep 3932405 = 368663) (by norm_num)
theorem B2949365 : Blo 1746574 2949365 := bbase (se 5 (by rfl) ⟨138251, by rfl⟩ : syracuseStep 2949365 = 276503) (by norm_num)
theorem B6299893 : Blo 1746574 6299893 := bbase (se 5 (by rfl) ⟨295307, by rfl⟩ : syracuseStep 6299893 = 590615) (by norm_num)
theorem B3318013 : Blo 1746574 3318013 := bbase (se 3 (by rfl) ⟨622127, by rfl⟩ : syracuseStep 3318013 = 1244255) (by norm_num)
theorem B2621693 : Blo 1746574 2621693 := bbase (se 3 (by rfl) ⟨491567, by rfl⟩ : syracuseStep 2621693 = 983135) (by norm_num)
theorem B1966333 : Blo 1746574 1966333 := bbase (se 3 (by rfl) ⟨368687, by rfl⟩ : syracuseStep 1966333 = 737375) (by norm_num)
theorem B2212105 : Blo 1746574 2212105 := bbase (se 2 (by rfl) ⟨829539, by rfl⟩ : syracuseStep 2212105 = 1659079) (by norm_num)
theorem B2621717 : Blo 1746574 2621717 := bbase (se 6 (by rfl) ⟨61446, by rfl⟩ : syracuseStep 2621717 = 122893) (by norm_num)
theorem B1966369 : Blo 1746574 1966369 := bbase (se 2 (by rfl) ⟨737388, by rfl⟩ : syracuseStep 1966369 = 1474777) (by norm_num)
theorem B2621741 : Blo 1746574 2621741 := bbase (se 3 (by rfl) ⟨491576, by rfl⟩ : syracuseStep 2621741 = 983153) (by norm_num)
theorem B4423997 : Blo 1746574 4423997 := bbase (se 3 (by rfl) ⟨829499, by rfl⟩ : syracuseStep 4423997 = 1658999) (by norm_num)
theorem B3932477 : Blo 1746574 3932477 := bbase (se 3 (by rfl) ⟨737339, by rfl⟩ : syracuseStep 3932477 = 1474679) (by norm_num)
theorem B2621765 : Blo 1746574 2621765 := bbase (se 4 (by rfl) ⟨245790, by rfl⟩ : syracuseStep 2621765 = 491581) (by norm_num)
theorem B1966405 : Blo 1746574 1966405 := bbase (se 4 (by rfl) ⟨184350, by rfl⟩ : syracuseStep 1966405 = 368701) (by norm_num)
theorem B5898581 : Blo 1746574 5898581 := bbase (se 10 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 5898581 = 17281) (by norm_num)
theorem B2621789 : Blo 1746574 2621789 := bbase (se 3 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 2621789 = 983171) (by norm_num)
theorem B2212201 : Blo 1746574 2212201 := bbase (se 2 (by rfl) ⟨829575, by rfl⟩ : syracuseStep 2212201 = 1659151) (by norm_num)
theorem B1966441 : Blo 1746574 1966441 := bbase (se 2 (by rfl) ⟨737415, by rfl⟩ : syracuseStep 1966441 = 1474831) (by norm_num)
theorem B2949493 : Blo 1746574 2949493 := bbase (se 5 (by rfl) ⟨138257, by rfl⟩ : syracuseStep 2949493 = 276515) (by norm_num)
theorem B2621813 : Blo 1746574 2621813 := bbase (se 5 (by rfl) ⟨122897, by rfl⟩ : syracuseStep 2621813 = 245795) (by norm_num)
theorem B3932549 : Blo 1746574 3932549 := bbase (se 4 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 3932549 = 737353) (by norm_num)
theorem B2621837 : Blo 1746574 2621837 := bbase (se 3 (by rfl) ⟨491594, by rfl⟩ : syracuseStep 2621837 = 983189) (by norm_num)
theorem B1966477 : Blo 1746574 1966477 := bbase (se 3 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 1966477 = 737429) (by norm_num)
theorem B2621861 : Blo 1746574 2621861 := bbase (se 4 (by rfl) ⟨245799, by rfl⟩ : syracuseStep 2621861 = 491599) (by norm_num)
theorem B1966513 : Blo 1746574 1966513 := bbase (se 2 (by rfl) ⟨737442, by rfl⟩ : syracuseStep 1966513 = 1474885) (by norm_num)
theorem B2621885 : Blo 1746574 2621885 := bbase (se 3 (by rfl) ⟨491603, by rfl⟩ : syracuseStep 2621885 = 983207) (by norm_num)
theorem B3932621 : Blo 1746574 3932621 := bbase (se 3 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 3932621 = 1474733) (by norm_num)
theorem B2949581 : Blo 1746574 2949581 := bbase (se 3 (by rfl) ⟨553046, by rfl⟩ : syracuseStep 2949581 = 1106093) (by norm_num)
theorem B2621909 : Blo 1746574 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B1966549 : Blo 1746574 1966549 := bbase (se 7 (by rfl) ⟨23045, by rfl⟩ : syracuseStep 1966549 = 46091) (by norm_num)
theorem B5317093 : Blo 1746574 5317093 := bbase (se 4 (by rfl) ⟨498477, by rfl⟩ : syracuseStep 5317093 = 996955) (by norm_num)
theorem B2621933 : Blo 1746574 2621933 := bbase (se 3 (by rfl) ⟨491612, by rfl⟩ : syracuseStep 2621933 = 983225) (by norm_num)
theorem B5595637 : Blo 1746574 5595637 := bbase (se 5 (by rfl) ⟨262295, by rfl⟩ : syracuseStep 5595637 = 524591) (by norm_num)
theorem B1966585 : Blo 1746574 1966585 := bbase (se 2 (by rfl) ⟨737469, by rfl⟩ : syracuseStep 1966585 = 1474939) (by norm_num)
theorem B2621957 : Blo 1746574 2621957 := bbase (se 4 (by rfl) ⟨245808, by rfl⟩ : syracuseStep 2621957 = 491617) (by norm_num)
theorem B3932693 : Blo 1746574 3932693 := bbase (se 6 (by rfl) ⟨92172, by rfl⟩ : syracuseStep 3932693 = 184345) (by norm_num)
theorem B2212373 : Blo 1746574 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B2621981 : Blo 1746574 2621981 := bbase (se 3 (by rfl) ⟨491621, by rfl⟩ : syracuseStep 2621981 = 983243) (by norm_num)
theorem B1966621 : Blo 1746574 1966621 := bbase (se 3 (by rfl) ⟨368741, by rfl⟩ : syracuseStep 1966621 = 737483) (by norm_num)
theorem B3318317 : Blo 1746574 3318317 := bbase (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) (by norm_num)
theorem B2622005 : Blo 1746574 2622005 := bbase (se 5 (by rfl) ⟨122906, by rfl⟩ : syracuseStep 2622005 = 245813) (by norm_num)
theorem B1966657 : Blo 1746574 1966657 := bbase (se 2 (by rfl) ⟨737496, by rfl⟩ : syracuseStep 1966657 = 1474993) (by norm_num)
theorem B2949709 : Blo 1746574 2949709 := bbase (se 3 (by rfl) ⟨553070, by rfl⟩ : syracuseStep 2949709 = 1106141) (by norm_num)
theorem B2622029 : Blo 1746574 2622029 := bbase (se 3 (by rfl) ⟨491630, by rfl⟩ : syracuseStep 2622029 = 983261) (by norm_num)
theorem B2212429 : Blo 1746574 2212429 := bbase (se 3 (by rfl) ⟨414830, by rfl⟩ : syracuseStep 2212429 = 829661) (by norm_num)
theorem B3932765 : Blo 1746574 3932765 := bbase (se 3 (by rfl) ⟨737393, by rfl⟩ : syracuseStep 3932765 = 1474787) (by norm_num)
theorem B2622053 : Blo 1746574 2622053 := bbase (se 4 (by rfl) ⟨245817, by rfl⟩ : syracuseStep 2622053 = 491635) (by norm_num)
theorem B1966693 : Blo 1746574 1966693 := bbase (se 4 (by rfl) ⟨184377, by rfl⟩ : syracuseStep 1966693 = 368755) (by norm_num)
theorem B2622077 : Blo 1746574 2622077 := bbase (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) (by norm_num)
theorem B1966729 : Blo 1746574 1966729 := bbase (se 2 (by rfl) ⟨737523, by rfl⟩ : syracuseStep 1966729 = 1475047) (by norm_num)
theorem B4424341 : Blo 1746574 4424341 := bbase (se 6 (by rfl) ⟨103695, by rfl⟩ : syracuseStep 4424341 = 207391) (by norm_num)
theorem B2622101 : Blo 1746574 2622101 := bbase (se 6 (by rfl) ⟨61455, by rfl⟩ : syracuseStep 2622101 = 122911) (by norm_num)
theorem B3932837 : Blo 1746574 3932837 := bbase (se 4 (by rfl) ⟨368703, by rfl⟩ : syracuseStep 3932837 = 737407) (by norm_num)
theorem B2949797 : Blo 1746574 2949797 := bbase (se 4 (by rfl) ⟨276543, by rfl⟩ : syracuseStep 2949797 = 553087) (by norm_num)
theorem B2622125 : Blo 1746574 2622125 := bbase (se 3 (by rfl) ⟨491648, by rfl⟩ : syracuseStep 2622125 = 983297) (by norm_num)
theorem B2212525 : Blo 1746574 2212525 := bbase (se 3 (by rfl) ⟨414848, by rfl⟩ : syracuseStep 2212525 = 829697) (by norm_num)
theorem B1966765 : Blo 1746574 1966765 := bbase (se 3 (by rfl) ⟨368768, by rfl⟩ : syracuseStep 1966765 = 737537) (by norm_num)
theorem B14926517 : Blo 1746574 14926517 := bbase (se 5 (by rfl) ⟨699680, by rfl⟩ : syracuseStep 14926517 = 1399361) (by norm_num)
theorem B2622149 : Blo 1746574 2622149 := bbase (se 4 (by rfl) ⟨245826, by rfl⟩ : syracuseStep 2622149 = 491653) (by norm_num)
theorem B1966801 : Blo 1746574 1966801 := bbase (se 2 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 1966801 = 1475101) (by norm_num)
theorem B2622173 : Blo 1746574 2622173 := bbase (se 3 (by rfl) ⟨491657, by rfl⟩ : syracuseStep 2622173 = 983315) (by norm_num)
theorem B3932909 : Blo 1746574 3932909 := bbase (se 3 (by rfl) ⟨737420, by rfl⟩ : syracuseStep 3932909 = 1474841) (by norm_num)
theorem B2622197 : Blo 1746574 2622197 := bbase (se 5 (by rfl) ⟨122915, by rfl⟩ : syracuseStep 2622197 = 245831) (by norm_num)
theorem B1966837 : Blo 1746574 1966837 := bbase (se 5 (by rfl) ⟨92195, by rfl⟩ : syracuseStep 1966837 = 184391) (by norm_num)
theorem B5899013 : Blo 1746574 5899013 := bbase (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) (by norm_num)
theorem B4424453 : Blo 1746574 4424453 := bbase (se 4 (by rfl) ⟨414792, by rfl⟩ : syracuseStep 4424453 = 829585) (by norm_num)
theorem B5677829 : Blo 1746574 5677829 := bbase (se 4 (by rfl) ⟨532296, by rfl⟩ : syracuseStep 5677829 = 1064593) (by norm_num)
theorem B2622221 : Blo 1746574 2622221 := bbase (se 3 (by rfl) ⟨491666, by rfl⟩ : syracuseStep 2622221 = 983333) (by norm_num)
theorem B1966873 : Blo 1746574 1966873 := bbase (se 2 (by rfl) ⟨737577, by rfl⟩ : syracuseStep 1966873 = 1475155) (by norm_num)
theorem B2949925 : Blo 1746574 2949925 := bbase (se 4 (by rfl) ⟨276555, by rfl⟩ : syracuseStep 2949925 = 553111) (by norm_num)
theorem B2622245 : Blo 1746574 2622245 := bbase (se 4 (by rfl) ⟨245835, by rfl⟩ : syracuseStep 2622245 = 491671) (by norm_num)
theorem B3932981 : Blo 1746574 3932981 := bbase (se 5 (by rfl) ⟨184358, by rfl⟩ : syracuseStep 3932981 = 368717) (by norm_num)
theorem B2622269 : Blo 1746574 2622269 := bbase (se 3 (by rfl) ⟨491675, by rfl⟩ : syracuseStep 2622269 = 983351) (by norm_num)
theorem B1966909 : Blo 1746574 1966909 := bbase (se 3 (by rfl) ⟨368795, by rfl⟩ : syracuseStep 1966909 = 737591) (by norm_num)
theorem B37798741 : Blo 1746574 37798741 := bbase (se 9 (by rfl) ⟨110738, by rfl⟩ : syracuseStep 37798741 = 221477) (by norm_num)
theorem B2622293 : Blo 1746574 2622293 := bbase (se 9 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 2622293 = 15365) (by norm_num)
theorem B2212697 : Blo 1746574 2212697 := bbase (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) (by norm_num)
theorem B1966945 : Blo 1746574 1966945 := bbase (se 2 (by rfl) ⟨737604, by rfl⟩ : syracuseStep 1966945 = 1475209) (by norm_num)
theorem B2622317 : Blo 1746574 2622317 := bbase (se 3 (by rfl) ⟨491684, by rfl⟩ : syracuseStep 2622317 = 983369) (by norm_num)
theorem B3933053 : Blo 1746574 3933053 := bbase (se 3 (by rfl) ⟨737447, by rfl⟩ : syracuseStep 3933053 = 1474895) (by norm_num)
theorem B2950013 : Blo 1746574 2950013 := bbase (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) (by norm_num)
theorem B2622341 : Blo 1746574 2622341 := bbase (se 4 (by rfl) ⟨245844, by rfl⟩ : syracuseStep 2622341 = 491689) (by norm_num)
theorem B1966981 : Blo 1746574 1966981 := bbase (se 4 (by rfl) ⟨184404, by rfl⟩ : syracuseStep 1966981 = 368809) (by norm_num)
theorem B2212753 : Blo 1746574 2212753 := bbase (se 2 (by rfl) ⟨829782, by rfl⟩ : syracuseStep 2212753 = 1659565) (by norm_num)
theorem B8848277 : Blo 1746574 8848277 := bbase (se 6 (by rfl) ⟨207381, by rfl⟩ : syracuseStep 8848277 = 414763) (by norm_num)
theorem B6636437 : Blo 1746574 6636437 := bbase (se 6 (by rfl) ⟨155541, by rfl⟩ : syracuseStep 6636437 = 311083) (by norm_num)
theorem B2622365 : Blo 1746574 2622365 := bbase (se 3 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 2622365 = 983387) (by norm_num)
theorem B1967017 : Blo 1746574 1967017 := bbase (se 2 (by rfl) ⟨737631, by rfl⟩ : syracuseStep 1967017 = 1475263) (by norm_num)
theorem B2622389 : Blo 1746574 2622389 := bbase (se 5 (by rfl) ⟨122924, by rfl⟩ : syracuseStep 2622389 = 245849) (by norm_num)
theorem B4424645 : Blo 1746574 4424645 := bbase (se 4 (by rfl) ⟨414810, by rfl⟩ : syracuseStep 4424645 = 829621) (by norm_num)
theorem B3933125 : Blo 1746574 3933125 := bbase (se 4 (by rfl) ⟨368730, by rfl⟩ : syracuseStep 3933125 = 737461) (by norm_num)
theorem B2622413 : Blo 1746574 2622413 := bbase (se 3 (by rfl) ⟨491702, by rfl⟩ : syracuseStep 2622413 = 983405) (by norm_num)
theorem B1967053 : Blo 1746574 1967053 := bbase (se 3 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 1967053 = 737645) (by norm_num)
theorem B45376469 : Blo 1746574 45376469 := bbase (se 7 (by rfl) ⟨531755, by rfl⟩ : syracuseStep 45376469 = 1063511) (by norm_num)
theorem B6300629 : Blo 1746574 6300629 := bbase (se 7 (by rfl) ⟨73835, by rfl⟩ : syracuseStep 6300629 = 147671) (by norm_num)
theorem B2622437 : Blo 1746574 2622437 := bbase (se 4 (by rfl) ⟨245853, by rfl⟩ : syracuseStep 2622437 = 491707) (by norm_num)
theorem B2212849 : Blo 1746574 2212849 := bbase (se 2 (by rfl) ⟨829818, by rfl⟩ : syracuseStep 2212849 = 1659637) (by norm_num)
theorem B1967089 : Blo 1746574 1967089 := bbase (se 2 (by rfl) ⟨737658, by rfl⟩ : syracuseStep 1967089 = 1475317) (by norm_num)
theorem B2950141 : Blo 1746574 2950141 := bbase (se 3 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 2950141 = 1106303) (by norm_num)
theorem B2622461 : Blo 1746574 2622461 := bbase (se 3 (by rfl) ⟨491711, by rfl⟩ : syracuseStep 2622461 = 983423) (by norm_num)
theorem B3933197 : Blo 1746574 3933197 := bbase (se 3 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 3933197 = 1474949) (by norm_num)
theorem B2622485 : Blo 1746574 2622485 := bbase (se 6 (by rfl) ⟨61464, by rfl⟩ : syracuseStep 2622485 = 122929) (by norm_num)
theorem B1967125 : Blo 1746574 1967125 := bbase (se 6 (by rfl) ⟨46104, by rfl⟩ : syracuseStep 1967125 = 92209) (by norm_num)
theorem B2622509 : Blo 1746574 2622509 := bbase (se 3 (by rfl) ⟨491720, by rfl⟩ : syracuseStep 2622509 = 983441) (by norm_num)
theorem B2622533 : Blo 1746574 2622533 := bbase (se 4 (by rfl) ⟨245862, by rfl⟩ : syracuseStep 2622533 = 491725) (by norm_num)
theorem B3933269 : Blo 1746574 3933269 := bbase (se 8 (by rfl) ⟨23046, by rfl⟩ : syracuseStep 3933269 = 46093) (by norm_num)
theorem B2950229 : Blo 1746574 2950229 := bbase (se 8 (by rfl) ⟨17286, by rfl⟩ : syracuseStep 2950229 = 34573) (by norm_num)
theorem B2622557 : Blo 1746574 2622557 := bbase (se 3 (by rfl) ⟨491729, by rfl⟩ : syracuseStep 2622557 = 983459) (by norm_num)
theorem B2098273 : Blo 1746574 2098273 := bbase (se 2 (by rfl) ⟨786852, by rfl⟩ : syracuseStep 2098273 = 1573705) (by norm_num)
theorem B2622581 : Blo 1746574 2622581 := bbase (se 5 (by rfl) ⟨122933, by rfl⟩ : syracuseStep 2622581 = 245867) (by norm_num)
theorem B2622605 : Blo 1746574 2622605 := bbase (se 3 (by rfl) ⟨491738, by rfl⟩ : syracuseStep 2622605 = 983477) (by norm_num)
theorem B4973717 : Blo 1746574 4973717 := bbase (se 6 (by rfl) ⟨116571, by rfl⟩ : syracuseStep 4973717 = 233143) (by norm_num)
theorem B3933341 : Blo 1746574 3933341 := bbase (se 3 (by rfl) ⟨737501, by rfl⟩ : syracuseStep 3933341 = 1475003) (by norm_num)
theorem B2213021 : Blo 1746574 2213021 := bbase (se 3 (by rfl) ⟨414941, by rfl⟩ : syracuseStep 2213021 = 829883) (by norm_num)
theorem B2622629 : Blo 1746574 2622629 := bbase (se 4 (by rfl) ⟨245871, by rfl⟩ : syracuseStep 2622629 = 491743) (by norm_num)
theorem B6636725 : Blo 1746574 6636725 := bbase (se 5 (by rfl) ⟨311096, by rfl⟩ : syracuseStep 6636725 = 622193) (by norm_num)
theorem B5899445 : Blo 1746574 5899445 := bbase (se 5 (by rfl) ⟨276536, by rfl⟩ : syracuseStep 5899445 = 553073) (by norm_num)
theorem B2622653 : Blo 1746574 2622653 := bbase (se 3 (by rfl) ⟨491747, by rfl⟩ : syracuseStep 2622653 = 983495) (by norm_num)
theorem B21251285 : Blo 1746574 21251285 := bbase (se 7 (by rfl) ⟨249038, by rfl⟩ : syracuseStep 21251285 = 498077) (by norm_num)
theorem B27280597 : Blo 1746574 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B2950357 : Blo 1746574 2950357 := bbase (se 7 (by rfl) ⟨34574, by rfl⟩ : syracuseStep 2950357 = 69149) (by norm_num)
theorem B2622677 : Blo 1746574 2622677 := bbase (se 7 (by rfl) ⟨30734, by rfl⟩ : syracuseStep 2622677 = 61469) (by norm_num)
theorem B3933413 : Blo 1746574 3933413 := bbase (se 4 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 3933413 = 737515) (by norm_num)
theorem B2622701 : Blo 1746574 2622701 := bbase (se 3 (by rfl) ⟨491756, by rfl⟩ : syracuseStep 2622701 = 983513) (by norm_num)
theorem B2622725 : Blo 1746574 2622725 := bbase (se 4 (by rfl) ⟨245880, by rfl⟩ : syracuseStep 2622725 = 491761) (by norm_num)
theorem B2303257 : Blo 1746574 2303257 := bbase (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) (by norm_num)
theorem B4424989 : Blo 1746574 4424989 := bbase (se 3 (by rfl) ⟨829685, by rfl⟩ : syracuseStep 4424989 = 1659371) (by norm_num)
theorem B3319069 : Blo 1746574 3319069 := bbase (se 3 (by rfl) ⟨622325, by rfl⟩ : syracuseStep 3319069 = 1244651) (by norm_num)
theorem B2622749 : Blo 1746574 2622749 := bbase (se 3 (by rfl) ⟨491765, by rfl⟩ : syracuseStep 2622749 = 983531) (by norm_num)
theorem B3933485 : Blo 1746574 3933485 := bbase (se 3 (by rfl) ⟨737528, by rfl⟩ : syracuseStep 3933485 = 1475057) (by norm_num)
theorem B2950445 : Blo 1746574 2950445 := bbase (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) (by norm_num)
theorem B2622773 : Blo 1746574 2622773 := bbase (se 5 (by rfl) ⟨122942, by rfl⟩ : syracuseStep 2622773 = 245885) (by norm_num)
theorem B2622797 : Blo 1746574 2622797 := bbase (se 3 (by rfl) ⟨491774, by rfl⟩ : syracuseStep 2622797 = 983549) (by norm_num)
theorem B2622821 : Blo 1746574 2622821 := bbase (se 4 (by rfl) ⟨245889, by rfl⟩ : syracuseStep 2622821 = 491779) (by norm_num)
theorem B9954677 : Blo 1746574 9954677 := bbase (se 5 (by rfl) ⟨466625, by rfl⟩ : syracuseStep 9954677 = 933251) (by norm_num)
theorem B3933557 : Blo 1746574 3933557 := bbase (se 5 (by rfl) ⟨184385, by rfl⟩ : syracuseStep 3933557 = 368771) (by norm_num)
theorem B2622845 : Blo 1746574 2622845 := bbase (se 3 (by rfl) ⟨491783, by rfl⟩ : syracuseStep 2622845 = 983567) (by norm_num)
theorem B4973957 : Blo 1746574 4973957 := bbase (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) (by norm_num)
theorem B4425101 : Blo 1746574 4425101 := bbase (se 3 (by rfl) ⟨829706, by rfl⟩ : syracuseStep 4425101 = 1659413) (by norm_num)
theorem B2098585 : Blo 1746574 2098585 := bbase (se 2 (by rfl) ⟨786969, by rfl⟩ : syracuseStep 2098585 = 1573939) (by norm_num)
theorem B3319213 : Blo 1746574 3319213 := bbase (se 3 (by rfl) ⟨622352, by rfl⟩ : syracuseStep 3319213 = 1244705) (by norm_num)
theorem B2950573 : Blo 1746574 2950573 := bbase (se 3 (by rfl) ⟨553232, by rfl⟩ : syracuseStep 2950573 = 1106465) (by norm_num)
theorem B3933629 : Blo 1746574 3933629 := bbase (se 3 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 3933629 = 1475111) (by norm_num)
theorem B1770949 : Blo 1746574 1770949 := bbase (se 4 (by rfl) ⟨166026, by rfl⟩ : syracuseStep 1770949 = 332053) (by norm_num)
theorem B7464437 : Blo 1746574 7464437 := bbase (se 5 (by rfl) ⟨349895, by rfl⟩ : syracuseStep 7464437 = 699791) (by norm_num)
theorem B3933701 : Blo 1746574 3933701 := bbase (se 4 (by rfl) ⟨368784, by rfl⟩ : syracuseStep 3933701 = 737569) (by norm_num)
theorem B2950661 : Blo 1746574 2950661 := bbase (se 4 (by rfl) ⟨276624, by rfl⟩ : syracuseStep 2950661 = 553249) (by norm_num)
theorem B1992209 : Blo 1746574 1992209 := bbase (se 2 (by rfl) ⟨747078, by rfl⟩ : syracuseStep 1992209 = 1494157) (by norm_num)
theorem B4974149 : Blo 1746574 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B4425293 : Blo 1746574 4425293 := bbase (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) (by norm_num)
theorem B3933773 : Blo 1746574 3933773 := bbase (se 3 (by rfl) ⟨737582, by rfl⟩ : syracuseStep 3933773 = 1475165) (by norm_num)
theorem B3319373 : Blo 1746574 3319373 := bbase (se 3 (by rfl) ⟨622382, by rfl⟩ : syracuseStep 3319373 = 1244765) (by norm_num)
theorem B5899877 : Blo 1746574 5899877 := bbase (se 4 (by rfl) ⟨553113, by rfl⟩ : syracuseStep 5899877 = 1106227) (by norm_num)
theorem B5113477 : Blo 1746574 5113477 := bbase (se 4 (by rfl) ⟨479388, by rfl⟩ : syracuseStep 5113477 = 958777) (by norm_num)
theorem B3933845 : Blo 1746574 3933845 := bbase (se 6 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 3933845 = 184399) (by norm_num)
theorem B2303641 : Blo 1746574 2303641 := bbase (se 2 (by rfl) ⟨863865, by rfl⟩ : syracuseStep 2303641 = 1727731) (by norm_num)
theorem B3933917 : Blo 1746574 3933917 := bbase (se 3 (by rfl) ⟨737609, by rfl⟩ : syracuseStep 3933917 = 1475219) (by norm_num)
theorem B3319517 : Blo 1746574 3319517 := bbase (se 3 (by rfl) ⟨622409, by rfl⟩ : syracuseStep 3319517 = 1244819) (by norm_num)
theorem B2655973 : Blo 1746574 2655973 := bbase (se 4 (by rfl) ⟨248997, by rfl⟩ : syracuseStep 2655973 = 497995) (by norm_num)
theorem B3933989 : Blo 1746574 3933989 := bbase (se 4 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 3933989 = 737623) (by norm_num)
theorem B3934061 : Blo 1746574 3934061 := bbase (se 3 (by rfl) ⟨737636, by rfl⟩ : syracuseStep 3934061 = 1475273) (by norm_num)
theorem B4425637 : Blo 1746574 4425637 := bbase (se 4 (by rfl) ⟨414903, by rfl⟩ : syracuseStep 4425637 = 829807) (by norm_num)
theorem B3934133 : Blo 1746574 3934133 := bbase (se 5 (by rfl) ⟨184412, by rfl⟩ : syracuseStep 3934133 = 368825) (by norm_num)
theorem B1992637 : Blo 1746574 1992637 := bbase (se 3 (by rfl) ⟨373619, by rfl⟩ : syracuseStep 1992637 = 747239) (by norm_num)
theorem B3934205 : Blo 1746574 3934205 := bbase (se 3 (by rfl) ⟨737663, by rfl⟩ : syracuseStep 3934205 = 1475327) (by norm_num)
theorem B5900309 : Blo 1746574 5900309 := bbase (se 6 (by rfl) ⟨138288, by rfl⟩ : syracuseStep 5900309 = 276577) (by norm_num)
theorem B4425749 : Blo 1746574 4425749 := bbase (se 6 (by rfl) ⟨103728, by rfl⟩ : syracuseStep 4425749 = 207457) (by norm_num)
theorem B3934277 : Blo 1746574 3934277 := bbase (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) (by norm_num)
theorem B3147893 : Blo 1746574 3147893 := bbase (se 5 (by rfl) ⟨147557, by rfl⟩ : syracuseStep 3147893 = 295115) (by norm_num)
theorem B8849573 : Blo 1746574 8849573 := bbase (se 4 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 8849573 = 1659295) (by norm_num)
theorem B23914709 : Blo 1746574 23914709 := bbase (se 7 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 23914709 = 560501) (by norm_num)
theorem B4425941 : Blo 1746574 4425941 := bbase (se 7 (by rfl) ⟨51866, by rfl⟩ : syracuseStep 4425941 = 103733) (by norm_num)
theorem B1771849 : Blo 1746574 1771849 := bbase (se 2 (by rfl) ⟨664443, by rfl⟩ : syracuseStep 1771849 = 1328887) (by norm_num)
theorem B6637909 : Blo 1746574 6637909 := bbase (se 10 (by rfl) ⟨9723, by rfl⟩ : syracuseStep 6637909 = 19447) (by norm_num)
theorem B2460061 : Blo 1746574 2460061 := bbase (se 3 (by rfl) ⟨461261, by rfl⟩ : syracuseStep 2460061 = 922523) (by norm_num)
theorem B5900741 : Blo 1746574 5900741 := bbase (se 4 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 5900741 = 1106389) (by norm_num)
theorem B4975141 : Blo 1746574 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B8399413 : Blo 1746574 8399413 := bbase (se 5 (by rfl) ⟨393722, by rfl⟩ : syracuseStep 8399413 = 787445) (by norm_num)
theorem B7088725 : Blo 1746574 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B15944309 : Blo 1746574 15944309 := bbase (se 5 (by rfl) ⟨747389, by rfl⟩ : syracuseStep 15944309 = 1494779) (by norm_num)
theorem B6638213 : Blo 1746574 6638213 := bbase (se 4 (by rfl) ⟨622332, by rfl⟩ : syracuseStep 6638213 = 1244665) (by norm_num)
theorem B3361421 : Blo 1746574 3361421 := bbase (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) (by norm_num)
theorem B2100065 : Blo 1746574 2100065 := bbase (se 2 (by rfl) ⟨787524, by rfl⟩ : syracuseStep 2100065 = 1575049) (by norm_num)
theorem B3984245 : Blo 1746574 3984245 := bbase (se 5 (by rfl) ⟨186761, by rfl⟩ : syracuseStep 3984245 = 373523) (by norm_num)
theorem B2657141 : Blo 1746574 2657141 := bbase (se 5 (by rfl) ⟨124553, by rfl⟩ : syracuseStep 2657141 = 249107) (by norm_num)
theorem B5901173 : Blo 1746574 5901173 := bbase (se 5 (by rfl) ⟨276617, by rfl⟩ : syracuseStep 5901173 = 553235) (by norm_num)
theorem B15944597 : Blo 1746574 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B2100161 : Blo 1746574 2100161 := bbase (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) (by norm_num)
theorem B2100181 : Blo 1746574 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B11955221 : Blo 1746574 11955221 := bbase (se 6 (by rfl) ⟨280200, by rfl⟩ : syracuseStep 11955221 = 560401) (by norm_num)
theorem B3542069 : Blo 1746574 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B2100325 : Blo 1746574 2100325 := bbase (se 4 (by rfl) ⟨196905, by rfl⟩ : syracuseStep 2100325 = 393811) (by norm_num)
theorem B1993877 : Blo 1746574 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B1993933 : Blo 1746574 1993933 := bbase (se 3 (by rfl) ⟨373862, by rfl⟩ : syracuseStep 1993933 = 747725) (by norm_num)
theorem B5598533 : Blo 1746574 5598533 := bbase (se 4 (by rfl) ⟨524862, by rfl⟩ : syracuseStep 5598533 = 1049725) (by norm_num)
theorem B12119381 : Blo 1746574 12119381 := bbase (se 11 (by rfl) ⟨8876, by rfl⟩ : syracuseStep 12119381 = 17753) (by norm_num)
theorem B2657701 : Blo 1746574 2657701 := bbase (se 4 (by rfl) ⟨249159, by rfl⟩ : syracuseStep 2657701 = 498319) (by norm_num)
theorem B8850869 : Blo 1746574 8850869 := bbase (se 5 (by rfl) ⟨414884, by rfl⟩ : syracuseStep 8850869 = 829769) (by norm_num)
theorem B4197901 : Blo 1746574 4197901 := bbase (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) (by norm_num)
theorem B4976245 : Blo 1746574 4976245 := bbase (se 5 (by rfl) ⟨233261, by rfl⟩ : syracuseStep 4976245 = 466523) (by norm_num)
theorem B3149485 : Blo 1746574 3149485 := bbase (se 3 (by rfl) ⟨590528, by rfl⟩ : syracuseStep 3149485 = 1181057) (by norm_num)
theorem B3731125 : Blo 1746574 3731125 := bbase (se 5 (by rfl) ⟨174896, by rfl⟩ : syracuseStep 3731125 = 349793) (by norm_num)
theorem B2657981 : Blo 1746574 2657981 := bbase (se 3 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 2657981 = 996743) (by norm_num)
theorem B11202293 : Blo 1746574 11202293 := bbase (se 5 (by rfl) ⟨525107, by rfl⟩ : syracuseStep 11202293 = 1050215) (by norm_num)
theorem B2838277 : Blo 1746574 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B8843093 : Blo 1746574 8843093 := bbase (se 9 (by rfl) ⟨25907, by rfl⟩ : syracuseStep 8843093 = 51815) (by norm_num)
theorem B3731501 : Blo 1746574 3731501 := bbase (se 3 (by rfl) ⟨699656, by rfl⟩ : syracuseStep 3731501 = 1399313) (by norm_num)
theorem B8966213 : Blo 1746574 8966213 := bbase (se 4 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 8966213 = 1681165) (by norm_num)
theorem B9949301 : Blo 1746574 9949301 := bbase (se 5 (by rfl) ⟨466373, by rfl⟩ : syracuseStep 9949301 = 932747) (by norm_num)
theorem B4198517 : Blo 1746574 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B31510741 : Blo 1746574 31510741 := bbase (se 7 (by rfl) ⟨369266, by rfl⟩ : syracuseStep 31510741 = 738533) (by norm_num)
theorem B3543373 : Blo 1746574 3543373 := bbase (se 3 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 3543373 = 1328765) (by norm_num)
theorem B2797973 : Blo 1746574 2797973 := bbase (se 6 (by rfl) ⟨65577, by rfl⟩ : syracuseStep 2797973 = 131155) (by norm_num)
theorem B2798005 : Blo 1746574 2798005 := bbase (se 5 (by rfl) ⟨131156, by rfl⟩ : syracuseStep 2798005 = 262313) (by norm_num)
theorem B4198853 : Blo 1746574 4198853 := bbase (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) (by norm_num)
theorem B3985949 : Blo 1746574 3985949 := bbase (se 3 (by rfl) ⟨747365, by rfl⟩ : syracuseStep 3985949 = 1494731) (by norm_num)
theorem B5894693 : Blo 1746574 5894693 := bbase (se 4 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 5894693 = 1105255) (by norm_num)
theorem B4723397 : Blo 1746574 4723397 := bbase (se 4 (by rfl) ⟨442818, by rfl⟩ : syracuseStep 4723397 = 885637) (by norm_num)
theorem B2487029 : Blo 1746574 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B3543821 : Blo 1746574 3543821 := bbase (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) (by norm_num)
theorem B4199245 : Blo 1746574 4199245 := bbase (se 3 (by rfl) ⟨787358, by rfl⟩ : syracuseStep 4199245 = 1574717) (by norm_num)
theorem B22688597 : Blo 1746574 22688597 := bbase (se 9 (by rfl) ⟨66470, by rfl⟩ : syracuseStep 22688597 = 132941) (by norm_num)
theorem B8967029 : Blo 1746574 8967029 := bbase (se 5 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 8967029 = 840659) (by norm_num)
theorem B3150733 : Blo 1746574 3150733 := bbase (se 3 (by rfl) ⟨590762, by rfl⟩ : syracuseStep 3150733 = 1181525) (by norm_num)
theorem B5895125 : Blo 1746574 5895125 := bbase (se 7 (by rfl) ⟨69083, by rfl⟩ : syracuseStep 5895125 = 138167) (by norm_num)
theorem B2126905 : Blo 1746574 2126905 := bbase (se 2 (by rfl) ⟨797589, by rfl⟩ : syracuseStep 2126905 = 1595179) (by norm_num)
theorem B4977749 : Blo 1746574 4977749 := bbase (se 8 (by rfl) ⟨29166, by rfl⟩ : syracuseStep 4977749 = 58333) (by norm_num)
theorem B6632549 : Blo 1746574 6632549 := bbase (se 4 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 6632549 = 1243603) (by norm_num)
theorem B8844389 : Blo 1746574 8844389 := bbase (se 4 (by rfl) ⟨829161, by rfl⟩ : syracuseStep 8844389 = 1658323) (by norm_num)
theorem B2126965 : Blo 1746574 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B9950485 : Blo 1746574 9950485 := bbase (se 6 (by rfl) ⟨233214, by rfl⟩ : syracuseStep 9950485 = 466429) (by norm_num)
theorem B2798933 : Blo 1746574 2798933 := bbase (se 13 (by rfl) ⟨512, by rfl⟩ : syracuseStep 2798933 = 1025) (by norm_num)
theorem B5895557 : Blo 1746574 5895557 := bbase (se 4 (by rfl) ⟨552708, by rfl⟩ : syracuseStep 5895557 = 1105417) (by norm_num)
theorem B6632837 : Blo 1746574 6632837 := bbase (se 4 (by rfl) ⟨621828, by rfl⟩ : syracuseStep 6632837 = 1243657) (by norm_num)
theorem B7468469 : Blo 1746574 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B3544541 : Blo 1746574 3544541 := bbase (se 3 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 3544541 = 1329203) (by norm_num)
theorem B2487781 : Blo 1746574 2487781 := bbase (se 4 (by rfl) ⟨233229, by rfl⟩ : syracuseStep 2487781 = 466459) (by norm_num)
theorem B4421101 : Blo 1746574 4421101 := bbase (se 3 (by rfl) ⟨828956, by rfl⟩ : syracuseStep 4421101 = 1657913) (by norm_num)
theorem B25187861 : Blo 1746574 25187861 := bbase (se 6 (by rfl) ⟨590340, by rfl⟩ : syracuseStep 25187861 = 1180681) (by norm_num)
theorem B5600789 : Blo 1746574 5600789 := bbase (se 6 (by rfl) ⟨131268, by rfl⟩ : syracuseStep 5600789 = 262537) (by norm_num)
theorem B4421213 : Blo 1746574 4421213 := bbase (se 3 (by rfl) ⟨828977, by rfl⟩ : syracuseStep 4421213 = 1657955) (by norm_num)
theorem B3733141 : Blo 1746574 3733141 := bbase (se 6 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 3733141 = 174991) (by norm_num)
theorem B2987725 : Blo 1746574 2987725 := bbase (se 3 (by rfl) ⟨560198, by rfl⟩ : syracuseStep 2987725 = 1120397) (by norm_num)
theorem B3929813 : Blo 1746574 3929813 := bbase (se 7 (by rfl) ⟨46052, by rfl⟩ : syracuseStep 3929813 = 92105) (by norm_num)
theorem B1865477 : Blo 1746574 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B14923541 : Blo 1746574 14923541 := bbase (se 6 (by rfl) ⟨349770, by rfl⟩ : syracuseStep 14923541 = 699541) (by norm_num)
theorem B3929885 : Blo 1746574 3929885 := bbase (se 3 (by rfl) ⟨736853, by rfl⟩ : syracuseStep 3929885 = 1473707) (by norm_num)
theorem B4421405 : Blo 1746574 4421405 := bbase (se 3 (by rfl) ⟨829013, by rfl⟩ : syracuseStep 4421405 = 1658027) (by norm_num)
theorem B5895989 : Blo 1746574 5895989 := bbase (se 5 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 5895989 = 552749) (by norm_num)
theorem B7460677 : Blo 1746574 7460677 := bbase (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) (by norm_num)
theorem B11196245 : Blo 1746574 11196245 := bbase (se 9 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 11196245 = 65603) (by norm_num)
theorem B3929957 : Blo 1746574 3929957 := bbase (se 4 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 3929957 = 736867) (by norm_num)
theorem B5314405 : Blo 1746574 5314405 := bbase (se 4 (by rfl) ⟨498225, by rfl⟩ : syracuseStep 5314405 = 996451) (by norm_num)
theorem B3987317 : Blo 1746574 3987317 := bbase (se 5 (by rfl) ⟨186905, by rfl⟩ : syracuseStep 3987317 = 373811) (by norm_num)
theorem B3930029 : Blo 1746574 3930029 := bbase (se 3 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 3930029 = 1473761) (by norm_num)
theorem B3930101 : Blo 1746574 3930101 := bbase (se 5 (by rfl) ⟨184223, by rfl⟩ : syracuseStep 3930101 = 368447) (by norm_num)
theorem B2799613 : Blo 1746574 2799613 := bbase (se 3 (by rfl) ⟨524927, by rfl⟩ : syracuseStep 2799613 = 1049855) (by norm_num)
theorem B3930173 : Blo 1746574 3930173 := bbase (se 3 (by rfl) ⟨736907, by rfl⟩ : syracuseStep 3930173 = 1473815) (by norm_num)
theorem B2799677 : Blo 1746574 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B2242657 : Blo 1746574 2242657 := bbase (se 2 (by rfl) ⟨840996, by rfl⟩ : syracuseStep 2242657 = 1681993) (by norm_num)
theorem B5314661 : Blo 1746574 5314661 := bbase (se 4 (by rfl) ⟨498249, by rfl⟩ : syracuseStep 5314661 = 996499) (by norm_num)
theorem B4421749 : Blo 1746574 4421749 := bbase (se 5 (by rfl) ⟨207269, by rfl⟩ : syracuseStep 4421749 = 414539) (by norm_num)
theorem B3930245 : Blo 1746574 3930245 := bbase (se 4 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 3930245 = 736921) (by norm_num)
theorem B25540757 : Blo 1746574 25540757 := bbase (se 6 (by rfl) ⟨598611, by rfl⟩ : syracuseStep 25540757 = 1197223) (by norm_num)
theorem B1865921 : Blo 1746574 1865921 := bbase (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) (by norm_num)
theorem B3315917 : Blo 1746574 3315917 := bbase (se 3 (by rfl) ⟨621734, by rfl⟩ : syracuseStep 3315917 = 1243469) (by norm_num)
theorem B3930317 : Blo 1746574 3930317 := bbase (se 3 (by rfl) ⟨736934, by rfl⟩ : syracuseStep 3930317 = 1473869) (by norm_num)
theorem B4421861 : Blo 1746574 4421861 := bbase (se 4 (by rfl) ⟨414549, by rfl⟩ : syracuseStep 4421861 = 829099) (by norm_num)
theorem B5896421 : Blo 1746574 5896421 := bbase (se 4 (by rfl) ⟨552789, by rfl⟩ : syracuseStep 5896421 = 1105579) (by norm_num)
theorem B2488573 : Blo 1746574 2488573 := bbase (se 3 (by rfl) ⟨466607, by rfl⟩ : syracuseStep 2488573 = 933215) (by norm_num)
theorem B3930389 : Blo 1746574 3930389 := bbase (se 6 (by rfl) ⟨92118, by rfl⟩ : syracuseStep 3930389 = 184237) (by norm_num)
theorem B5601557 : Blo 1746574 5601557 := bbase (se 6 (by rfl) ⟨131286, by rfl⟩ : syracuseStep 5601557 = 262573) (by norm_num)
theorem B2947421 : Blo 1746574 2947421 := bbase (se 3 (by rfl) ⟨552641, by rfl⟩ : syracuseStep 2947421 = 1105283) (by norm_num)
theorem B3930461 : Blo 1746574 3930461 := bbase (se 3 (by rfl) ⟨736961, by rfl⟩ : syracuseStep 3930461 = 1473923) (by norm_num)
theorem B3316069 : Blo 1746574 3316069 := bbase (se 4 (by rfl) ⟨310881, by rfl⟩ : syracuseStep 3316069 = 621763) (by norm_num)
theorem B8395109 : Blo 1746574 8395109 := bbase (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) (by norm_num)
theorem B8845685 : Blo 1746574 8845685 := bbase (se 5 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 8845685 = 829283) (by norm_num)
theorem B3930533 : Blo 1746574 3930533 := bbase (se 4 (by rfl) ⟨368487, by rfl⟩ : syracuseStep 3930533 = 736975) (by norm_num)
theorem B4422053 : Blo 1746574 4422053 := bbase (se 4 (by rfl) ⟨414567, by rfl⟩ : syracuseStep 4422053 = 829135) (by norm_num)
theorem B1866169 : Blo 1746574 1866169 := bbase (se 2 (by rfl) ⟨699813, by rfl⟩ : syracuseStep 1866169 = 1399627) (by norm_num)
theorem B2619869 : Blo 1746574 2619869 := bbase (se 3 (by rfl) ⟨491225, by rfl⟩ : syracuseStep 2619869 = 982451) (by norm_num)
theorem B2947549 : Blo 1746574 2947549 := bbase (se 3 (by rfl) ⟨552665, by rfl⟩ : syracuseStep 2947549 = 1105331) (by norm_num)
theorem B3193309 : Blo 1746574 3193309 := bbase (se 3 (by rfl) ⟨598745, by rfl⟩ : syracuseStep 3193309 = 1197491) (by norm_num)
theorem B3930605 : Blo 1746574 3930605 := bbase (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) (by norm_num)
theorem B2619893 : Blo 1746574 2619893 := bbase (se 5 (by rfl) ⟨122807, by rfl⟩ : syracuseStep 2619893 = 245615) (by norm_num)
theorem B2619917 : Blo 1746574 2619917 := bbase (se 3 (by rfl) ⟨491234, by rfl⟩ : syracuseStep 2619917 = 982469) (by norm_num)
theorem B3734029 : Blo 1746574 3734029 := bbase (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) (by norm_num)
theorem B2521621 : Blo 1746574 2521621 := bbase (se 6 (by rfl) ⟨59100, by rfl⟩ : syracuseStep 2521621 = 118201) (by norm_num)
theorem B2619941 : Blo 1746574 2619941 := bbase (se 4 (by rfl) ⟨245619, by rfl⟩ : syracuseStep 2619941 = 491239) (by norm_num)
theorem B8395301 : Blo 1746574 8395301 := bbase (se 4 (by rfl) ⟨787059, by rfl⟩ : syracuseStep 8395301 = 1574119) (by norm_num)
theorem B6634021 : Blo 1746574 6634021 := bbase (se 4 (by rfl) ⟨621939, by rfl⟩ : syracuseStep 6634021 = 1243879) (by norm_num)
theorem B2947637 : Blo 1746574 2947637 := bbase (se 5 (by rfl) ⟨138170, by rfl⟩ : syracuseStep 2947637 = 276341) (by norm_num)
theorem B3930677 : Blo 1746574 3930677 := bbase (se 5 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 3930677 = 368501) (by norm_num)
theorem B2619965 : Blo 1746574 2619965 := bbase (se 3 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 2619965 = 982487) (by norm_num)
theorem B2488909 : Blo 1746574 2488909 := bbase (se 3 (by rfl) ⟨466670, by rfl⟩ : syracuseStep 2488909 = 933341) (by norm_num)
theorem B2619989 : Blo 1746574 2619989 := bbase (se 8 (by rfl) ⟨15351, by rfl⟩ : syracuseStep 2619989 = 30703) (by norm_num)
theorem B18889301 : Blo 1746574 18889301 := bbase (se 8 (by rfl) ⟨110679, by rfl⟩ : syracuseStep 18889301 = 221359) (by norm_num)
theorem B2620013 : Blo 1746574 2620013 := bbase (se 3 (by rfl) ⟨491252, by rfl⟩ : syracuseStep 2620013 = 982505) (by norm_num)
theorem B3930749 : Blo 1746574 3930749 := bbase (se 3 (by rfl) ⟨737015, by rfl⟩ : syracuseStep 3930749 = 1474031) (by norm_num)
theorem B2620037 : Blo 1746574 2620037 := bbase (se 4 (by rfl) ⟨245628, by rfl⟩ : syracuseStep 2620037 = 491257) (by norm_num)
theorem B4979333 : Blo 1746574 4979333 := bbase (se 4 (by rfl) ⟨466812, by rfl⟩ : syracuseStep 4979333 = 933625) (by norm_num)
theorem B3316373 : Blo 1746574 3316373 := bbase (se 6 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 3316373 = 155455) (by norm_num)
theorem B5896853 : Blo 1746574 5896853 := bbase (se 6 (by rfl) ⟨138207, by rfl⟩ : syracuseStep 5896853 = 276415) (by norm_num)
theorem B2620061 : Blo 1746574 2620061 := bbase (se 3 (by rfl) ⟨491261, by rfl⟩ : syracuseStep 2620061 = 982523) (by norm_num)
theorem B2620085 : Blo 1746574 2620085 := bbase (se 5 (by rfl) ⟨122816, by rfl⟩ : syracuseStep 2620085 = 245633) (by norm_num)
theorem B2947765 : Blo 1746574 2947765 := bbase (se 5 (by rfl) ⟨138176, by rfl⟩ : syracuseStep 2947765 = 276353) (by norm_num)
theorem B3930821 : Blo 1746574 3930821 := bbase (se 4 (by rfl) ⟨368514, by rfl⟩ : syracuseStep 3930821 = 737029) (by norm_num)
theorem B2620109 : Blo 1746574 2620109 := bbase (se 3 (by rfl) ⟨491270, by rfl⟩ : syracuseStep 2620109 = 982541) (by norm_num)
theorem B2620133 : Blo 1746574 2620133 := bbase (se 4 (by rfl) ⟨245637, by rfl⟩ : syracuseStep 2620133 = 491275) (by norm_num)
theorem B2620157 : Blo 1746574 2620157 := bbase (se 3 (by rfl) ⟨491279, by rfl⟩ : syracuseStep 2620157 = 982559) (by norm_num)
theorem B4422397 : Blo 1746574 4422397 := bbase (se 3 (by rfl) ⟨829199, by rfl⟩ : syracuseStep 4422397 = 1658399) (by norm_num)
theorem B2947853 : Blo 1746574 2947853 := bbase (se 3 (by rfl) ⟨552722, by rfl⟩ : syracuseStep 2947853 = 1105445) (by norm_num)
theorem B3930893 : Blo 1746574 3930893 := bbase (se 3 (by rfl) ⟨737042, by rfl⟩ : syracuseStep 3930893 = 1474085) (by norm_num)
theorem B2210581 : Blo 1746574 2210581 := bbase (se 6 (by rfl) ⟨51810, by rfl⟩ : syracuseStep 2210581 = 103621) (by norm_num)
theorem B2620181 : Blo 1746574 2620181 := bbase (se 6 (by rfl) ⟨61410, by rfl⟩ : syracuseStep 2620181 = 122821) (by norm_num)
theorem B2489125 : Blo 1746574 2489125 := bbase (se 4 (by rfl) ⟨233355, by rfl⟩ : syracuseStep 2489125 = 466711) (by norm_num)
theorem B2620205 : Blo 1746574 2620205 := bbase (se 3 (by rfl) ⟨491288, by rfl⟩ : syracuseStep 2620205 = 982577) (by norm_num)
theorem B4315949 : Blo 1746574 4315949 := bbase (se 3 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 4315949 = 1618481) (by norm_num)
theorem B13278005 : Blo 1746574 13278005 := bbase (se 5 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 13278005 = 1244813) (by norm_num)
theorem B2620229 : Blo 1746574 2620229 := bbase (se 4 (by rfl) ⟨245646, by rfl⟩ : syracuseStep 2620229 = 491293) (by norm_num)
theorem B3930965 : Blo 1746574 3930965 := bbase (se 9 (by rfl) ⟨11516, by rfl⟩ : syracuseStep 3930965 = 23033) (by norm_num)
theorem B6634325 : Blo 1746574 6634325 := bbase (se 9 (by rfl) ⟨19436, by rfl⟩ : syracuseStep 6634325 = 38873) (by norm_num)
theorem B2620253 : Blo 1746574 2620253 := bbase (se 3 (by rfl) ⟨491297, by rfl⟩ : syracuseStep 2620253 = 982595) (by norm_num)
theorem B1866601 : Blo 1746574 1866601 := bbase (se 2 (by rfl) ⟨699975, by rfl⟩ : syracuseStep 1866601 = 1399951) (by norm_num)
theorem B4422509 : Blo 1746574 4422509 := bbase (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) (by norm_num)
theorem B2620277 : Blo 1746574 2620277 := bbase (se 5 (by rfl) ⟨122825, by rfl⟩ : syracuseStep 2620277 = 245651) (by norm_num)
theorem B1964929 : Blo 1746574 1964929 := bbase (se 2 (by rfl) ⟨736848, by rfl⟩ : syracuseStep 1964929 = 1473697) (by norm_num)
theorem B2620301 : Blo 1746574 2620301 := bbase (se 3 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 2620301 = 982613) (by norm_num)
theorem B2947981 : Blo 1746574 2947981 := bbase (se 3 (by rfl) ⟨552746, by rfl⟩ : syracuseStep 2947981 = 1105493) (by norm_num)
theorem B3931037 : Blo 1746574 3931037 := bbase (se 3 (by rfl) ⟨737069, by rfl⟩ : syracuseStep 3931037 = 1474139) (by norm_num)
theorem B1964965 : Blo 1746574 1964965 := bbase (se 4 (by rfl) ⟨184215, by rfl⟩ : syracuseStep 1964965 = 368431) (by norm_num)
theorem B2620325 : Blo 1746574 2620325 := bbase (se 4 (by rfl) ⟨245655, by rfl⟩ : syracuseStep 2620325 = 491311) (by norm_num)
theorem B1866673 : Blo 1746574 1866673 := bbase (se 2 (by rfl) ⟨700002, by rfl⟩ : syracuseStep 1866673 = 1400005) (by norm_num)
theorem B2620349 : Blo 1746574 2620349 := bbase (se 3 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 2620349 = 982631) (by norm_num)
theorem B2210753 : Blo 1746574 2210753 := bbase (se 2 (by rfl) ⟨829032, by rfl⟩ : syracuseStep 2210753 = 1658065) (by norm_num)
theorem B1965001 : Blo 1746574 1965001 := bbase (se 2 (by rfl) ⟨736875, by rfl⟩ : syracuseStep 1965001 = 1473751) (by norm_num)
theorem B2620373 : Blo 1746574 2620373 := bbase (se 7 (by rfl) ⟨30707, by rfl⟩ : syracuseStep 2620373 = 61415) (by norm_num)
theorem B18889685 : Blo 1746574 18889685 := bbase (se 7 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 18889685 = 442727) (by norm_num)
theorem B2948069 : Blo 1746574 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B3931109 : Blo 1746574 3931109 := bbase (se 4 (by rfl) ⟨368541, by rfl⟩ : syracuseStep 3931109 = 737083) (by norm_num)
theorem B1965037 : Blo 1746574 1965037 := bbase (se 3 (by rfl) ⟨368444, by rfl⟩ : syracuseStep 1965037 = 736889) (by norm_num)
theorem B2620397 : Blo 1746574 2620397 := bbase (se 3 (by rfl) ⟨491324, by rfl⟩ : syracuseStep 2620397 = 982649) (by norm_num)
theorem B2210809 : Blo 1746574 2210809 := bbase (se 2 (by rfl) ⟨829053, by rfl⟩ : syracuseStep 2210809 = 1658107) (by norm_num)
theorem B2128889 : Blo 1746574 2128889 := bbase (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) (by norm_num)
theorem B2620421 : Blo 1746574 2620421 := bbase (se 4 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 2620421 = 491329) (by norm_num)
theorem B1965073 : Blo 1746574 1965073 := bbase (se 2 (by rfl) ⟨736902, by rfl⟩ : syracuseStep 1965073 = 1473805) (by norm_num)
theorem B2620445 : Blo 1746574 2620445 := bbase (se 3 (by rfl) ⟨491333, by rfl⟩ : syracuseStep 2620445 = 982667) (by norm_num)
theorem B3931181 : Blo 1746574 3931181 := bbase (se 3 (by rfl) ⟨737096, by rfl⟩ : syracuseStep 3931181 = 1474193) (by norm_num)
theorem B4422701 : Blo 1746574 4422701 := bbase (se 3 (by rfl) ⟨829256, by rfl⟩ : syracuseStep 4422701 = 1658513) (by norm_num)
theorem B1965109 : Blo 1746574 1965109 := bbase (se 5 (by rfl) ⟨92114, by rfl⟩ : syracuseStep 1965109 = 184229) (by norm_num)
theorem B2620469 : Blo 1746574 2620469 := bbase (se 5 (by rfl) ⟨122834, by rfl⟩ : syracuseStep 2620469 = 245669) (by norm_num)
theorem B5897285 : Blo 1746574 5897285 := bbase (se 4 (by rfl) ⟨552870, by rfl⟩ : syracuseStep 5897285 = 1105741) (by norm_num)
theorem B2620493 : Blo 1746574 2620493 := bbase (se 3 (by rfl) ⟨491342, by rfl⟩ : syracuseStep 2620493 = 982685) (by norm_num)
theorem B1965145 : Blo 1746574 1965145 := bbase (se 2 (by rfl) ⟨736929, by rfl⟩ : syracuseStep 1965145 = 1473859) (by norm_num)
theorem B2210905 : Blo 1746574 2210905 := bbase (se 2 (by rfl) ⟨829089, by rfl⟩ : syracuseStep 2210905 = 1658179) (by norm_num)
theorem B2620517 : Blo 1746574 2620517 := bbase (se 4 (by rfl) ⟨245673, by rfl⟩ : syracuseStep 2620517 = 491347) (by norm_num)
theorem B2948197 : Blo 1746574 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B3931253 : Blo 1746574 3931253 := bbase (se 5 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 3931253 = 368555) (by norm_num)
theorem B1965181 : Blo 1746574 1965181 := bbase (se 3 (by rfl) ⟨368471, by rfl⟩ : syracuseStep 1965181 = 736943) (by norm_num)
theorem B2620541 : Blo 1746574 2620541 := bbase (se 3 (by rfl) ⟨491351, by rfl⟩ : syracuseStep 2620541 = 982703) (by norm_num)
theorem B2620565 : Blo 1746574 2620565 := bbase (se 6 (by rfl) ⟨61419, by rfl⟩ : syracuseStep 2620565 = 122839) (by norm_num)
theorem B2489501 : Blo 1746574 2489501 := bbase (se 3 (by rfl) ⟨466781, by rfl⟩ : syracuseStep 2489501 = 933563) (by norm_num)
theorem B1965217 : Blo 1746574 1965217 := bbase (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) (by norm_num)
theorem B2620589 : Blo 1746574 2620589 := bbase (se 3 (by rfl) ⟨491360, by rfl⟩ : syracuseStep 2620589 = 982721) (by norm_num)
theorem B16792757 : Blo 1746574 16792757 := bbase (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) (by norm_num)
theorem B2948285 : Blo 1746574 2948285 := bbase (se 3 (by rfl) ⟨552803, by rfl⟩ : syracuseStep 2948285 = 1105607) (by norm_num)
theorem B3931325 : Blo 1746574 3931325 := bbase (se 3 (by rfl) ⟨737123, by rfl⟩ : syracuseStep 3931325 = 1474247) (by norm_num)
theorem B1965253 : Blo 1746574 1965253 := bbase (se 4 (by rfl) ⟨184242, by rfl⟩ : syracuseStep 1965253 = 368485) (by norm_num)
theorem B2620613 : Blo 1746574 2620613 := bbase (se 4 (by rfl) ⟨245682, by rfl⟩ : syracuseStep 2620613 = 491365) (by norm_num)
theorem B9952469 : Blo 1746574 9952469 := bbase (se 7 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 9952469 = 233261) (by norm_num)
theorem B13270229 : Blo 1746574 13270229 := bbase (se 7 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 13270229 = 311021) (by norm_num)
theorem B2620637 : Blo 1746574 2620637 := bbase (se 3 (by rfl) ⟨491369, by rfl⟩ : syracuseStep 2620637 = 982739) (by norm_num)
theorem B1965289 : Blo 1746574 1965289 := bbase (se 2 (by rfl) ⟨736983, by rfl⟩ : syracuseStep 1965289 = 1473967) (by norm_num)
theorem B2620661 : Blo 1746574 2620661 := bbase (se 5 (by rfl) ⟨122843, by rfl⟩ : syracuseStep 2620661 = 245687) (by norm_num)
theorem B2211077 : Blo 1746574 2211077 := bbase (se 4 (by rfl) ⟨207288, by rfl⟩ : syracuseStep 2211077 = 414577) (by norm_num)
theorem B3931397 : Blo 1746574 3931397 := bbase (se 4 (by rfl) ⟨368568, by rfl⟩ : syracuseStep 3931397 = 737137) (by norm_num)
theorem B1965325 : Blo 1746574 1965325 := bbase (se 3 (by rfl) ⟨368498, by rfl⟩ : syracuseStep 1965325 = 736997) (by norm_num)
theorem B2620685 : Blo 1746574 2620685 := bbase (se 3 (by rfl) ⟨491378, by rfl⟩ : syracuseStep 2620685 = 982757) (by norm_num)
theorem B7462165 : Blo 1746574 7462165 := bbase (se 6 (by rfl) ⟨174894, by rfl⟩ : syracuseStep 7462165 = 349789) (by norm_num)
theorem B2989333 : Blo 1746574 2989333 := bbase (se 6 (by rfl) ⟨70062, by rfl⟩ : syracuseStep 2989333 = 140125) (by norm_num)
theorem B7462181 : Blo 1746574 7462181 := bbase (se 4 (by rfl) ⟨699579, by rfl⟩ : syracuseStep 7462181 = 1399159) (by norm_num)
theorem B2620709 : Blo 1746574 2620709 := bbase (se 4 (by rfl) ⟨245691, by rfl⟩ : syracuseStep 2620709 = 491383) (by norm_num)
theorem B1867045 : Blo 1746574 1867045 := bbase (se 4 (by rfl) ⟨175035, by rfl⟩ : syracuseStep 1867045 = 350071) (by norm_num)
theorem B1965361 : Blo 1746574 1965361 := bbase (se 2 (by rfl) ⟨737010, by rfl⟩ : syracuseStep 1965361 = 1474021) (by norm_num)
theorem B2211133 : Blo 1746574 2211133 := bbase (se 3 (by rfl) ⟨414587, by rfl⟩ : syracuseStep 2211133 = 829175) (by norm_num)
theorem B2620733 : Blo 1746574 2620733 := bbase (se 3 (by rfl) ⟨491387, by rfl⟩ : syracuseStep 2620733 = 982775) (by norm_num)
theorem B2948413 : Blo 1746574 2948413 := bbase (se 3 (by rfl) ⟨552827, by rfl⟩ : syracuseStep 2948413 = 1105655) (by norm_num)
theorem B3931469 : Blo 1746574 3931469 := bbase (se 3 (by rfl) ⟨737150, by rfl⟩ : syracuseStep 3931469 = 1474301) (by norm_num)
theorem B1965397 : Blo 1746574 1965397 := bbase (se 11 (by rfl) ⟨1439, by rfl⟩ : syracuseStep 1965397 = 2879) (by norm_num)
theorem B2620757 : Blo 1746574 2620757 := bbase (se 11 (by rfl) ⟨1919, by rfl⟩ : syracuseStep 2620757 = 3839) (by norm_num)
theorem B2620781 : Blo 1746574 2620781 := bbase (se 3 (by rfl) ⟨491396, by rfl⟩ : syracuseStep 2620781 = 982793) (by norm_num)
theorem B1965433 : Blo 1746574 1965433 := bbase (se 2 (by rfl) ⟨737037, by rfl⟩ : syracuseStep 1965433 = 1474075) (by norm_num)
theorem B3317125 : Blo 1746574 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B2620805 : Blo 1746574 2620805 := bbase (se 4 (by rfl) ⟨245700, by rfl⟩ : syracuseStep 2620805 = 491401) (by norm_num)
theorem B4423045 : Blo 1746574 4423045 := bbase (se 4 (by rfl) ⟨414660, by rfl⟩ : syracuseStep 4423045 = 829321) (by norm_num)
theorem B9444757 : Blo 1746574 9444757 := bbase (se 6 (by rfl) ⟨221361, by rfl⟩ : syracuseStep 9444757 = 442723) (by norm_num)
theorem B2948501 : Blo 1746574 2948501 := bbase (se 6 (by rfl) ⟨69105, by rfl⟩ : syracuseStep 2948501 = 138211) (by norm_num)
theorem B3931541 : Blo 1746574 3931541 := bbase (se 6 (by rfl) ⟨92145, by rfl⟩ : syracuseStep 3931541 = 184291) (by norm_num)
theorem B1965469 : Blo 1746574 1965469 := bbase (se 3 (by rfl) ⟨368525, by rfl⟩ : syracuseStep 1965469 = 737051) (by norm_num)
theorem B2211229 : Blo 1746574 2211229 := bbase (se 3 (by rfl) ⟨414605, by rfl⟩ : syracuseStep 2211229 = 829211) (by norm_num)
theorem B2620829 : Blo 1746574 2620829 := bbase (se 3 (by rfl) ⟨491405, by rfl⟩ : syracuseStep 2620829 = 982811) (by norm_num)
theorem B2620853 : Blo 1746574 2620853 := bbase (se 5 (by rfl) ⟨122852, by rfl⟩ : syracuseStep 2620853 = 245705) (by norm_num)
theorem B1965505 : Blo 1746574 1965505 := bbase (se 2 (by rfl) ⟨737064, by rfl⟩ : syracuseStep 1965505 = 1474129) (by norm_num)
theorem B2620877 : Blo 1746574 2620877 := bbase (se 3 (by rfl) ⟨491414, by rfl⟩ : syracuseStep 2620877 = 982829) (by norm_num)
theorem B3931613 : Blo 1746574 3931613 := bbase (se 3 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 3931613 = 1474355) (by norm_num)
theorem B1965541 : Blo 1746574 1965541 := bbase (se 4 (by rfl) ⟨184269, by rfl⟩ : syracuseStep 1965541 = 368539) (by norm_num)
theorem B2620901 : Blo 1746574 2620901 := bbase (se 4 (by rfl) ⟨245709, by rfl⟩ : syracuseStep 2620901 = 491419) (by norm_num)
theorem B4423157 : Blo 1746574 4423157 := bbase (se 5 (by rfl) ⟨207335, by rfl⟩ : syracuseStep 4423157 = 414671) (by norm_num)
theorem B5897717 : Blo 1746574 5897717 := bbase (se 5 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 5897717 = 552911) (by norm_num)
theorem B2620925 : Blo 1746574 2620925 := bbase (se 3 (by rfl) ⟨491423, by rfl⟩ : syracuseStep 2620925 = 982847) (by norm_num)
theorem B1965577 : Blo 1746574 1965577 := bbase (se 2 (by rfl) ⟨737091, by rfl⟩ : syracuseStep 1965577 = 1474183) (by norm_num)
theorem B2620949 : Blo 1746574 2620949 := bbase (se 6 (by rfl) ⟨61428, by rfl⟩ : syracuseStep 2620949 = 122857) (by norm_num)
theorem B2948629 : Blo 1746574 2948629 := bbase (se 6 (by rfl) ⟨69108, by rfl⟩ : syracuseStep 2948629 = 138217) (by norm_num)
theorem B3317269 : Blo 1746574 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B3931685 : Blo 1746574 3931685 := bbase (se 4 (by rfl) ⟨368595, by rfl⟩ : syracuseStep 3931685 = 737191) (by norm_num)
theorem B1965613 : Blo 1746574 1965613 := bbase (se 3 (by rfl) ⟨368552, by rfl⟩ : syracuseStep 1965613 = 737105) (by norm_num)
theorem B2620973 : Blo 1746574 2620973 := bbase (se 3 (by rfl) ⟨491432, by rfl⟩ : syracuseStep 2620973 = 982865) (by norm_num)
theorem B2620997 : Blo 1746574 2620997 := bbase (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) (by norm_num)
theorem B2211401 : Blo 1746574 2211401 := bbase (se 2 (by rfl) ⟨829275, by rfl⟩ : syracuseStep 2211401 = 1658551) (by norm_num)
theorem B1965649 : Blo 1746574 1965649 := bbase (se 2 (by rfl) ⟨737118, by rfl⟩ : syracuseStep 1965649 = 1474237) (by norm_num)
theorem B2621021 : Blo 1746574 2621021 := bbase (se 3 (by rfl) ⟨491441, by rfl⟩ : syracuseStep 2621021 = 982883) (by norm_num)
theorem B2948717 : Blo 1746574 2948717 := bbase (se 3 (by rfl) ⟨552884, by rfl⟩ : syracuseStep 2948717 = 1105769) (by norm_num)
theorem B3931757 : Blo 1746574 3931757 := bbase (se 3 (by rfl) ⟨737204, by rfl⟩ : syracuseStep 3931757 = 1474409) (by norm_num)
theorem B1965685 : Blo 1746574 1965685 := bbase (se 5 (by rfl) ⟨92141, by rfl⟩ : syracuseStep 1965685 = 184283) (by norm_num)
theorem B2621045 : Blo 1746574 2621045 := bbase (se 5 (by rfl) ⟨122861, by rfl⟩ : syracuseStep 2621045 = 245723) (by norm_num)
theorem B2211457 : Blo 1746574 2211457 := bbase (se 2 (by rfl) ⟨829296, by rfl⟩ : syracuseStep 2211457 = 1658593) (by norm_num)
theorem B8846981 : Blo 1746574 8846981 := bbase (se 4 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 8846981 = 1658809) (by norm_num)
theorem B2621069 : Blo 1746574 2621069 := bbase (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) (by norm_num)
theorem B1965721 : Blo 1746574 1965721 := bbase (se 2 (by rfl) ⟨737145, by rfl⟩ : syracuseStep 1965721 = 1474291) (by norm_num)
theorem B2621093 : Blo 1746574 2621093 := bbase (se 4 (by rfl) ⟨245727, by rfl⟩ : syracuseStep 2621093 = 491455) (by norm_num)
theorem B3317429 : Blo 1746574 3317429 := bbase (se 5 (by rfl) ⟨155504, by rfl⟩ : syracuseStep 3317429 = 311009) (by norm_num)
theorem B3931829 : Blo 1746574 3931829 := bbase (se 5 (by rfl) ⟨184304, by rfl⟩ : syracuseStep 3931829 = 368609) (by norm_num)
theorem B4423349 : Blo 1746574 4423349 := bbase (se 5 (by rfl) ⟨207344, by rfl⟩ : syracuseStep 4423349 = 414689) (by norm_num)
theorem B1916605 : Blo 1746574 1916605 := bbase (se 3 (by rfl) ⟨359363, by rfl⟩ : syracuseStep 1916605 = 718727) (by norm_num)
theorem B1965757 : Blo 1746574 1965757 := bbase (se 3 (by rfl) ⟨368579, by rfl⟩ : syracuseStep 1965757 = 737159) (by norm_num)
theorem B2621117 : Blo 1746574 2621117 := bbase (se 3 (by rfl) ⟨491459, by rfl⟩ : syracuseStep 2621117 = 982919) (by norm_num)
theorem B2621141 : Blo 1746574 2621141 := bbase (se 7 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 2621141 = 61433) (by norm_num)
theorem B1965793 : Blo 1746574 1965793 := bbase (se 2 (by rfl) ⟨737172, by rfl⟩ : syracuseStep 1965793 = 1474345) (by norm_num)
theorem B2211553 : Blo 1746574 2211553 := bbase (se 2 (by rfl) ⟨829332, by rfl⟩ : syracuseStep 2211553 = 1658665) (by norm_num)
theorem B3784421 : Blo 1746574 3784421 := bbase (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) (by norm_num)
theorem B2621165 : Blo 1746574 2621165 := bbase (se 3 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 2621165 = 982937) (by norm_num)
theorem B2948845 : Blo 1746574 2948845 := bbase (se 3 (by rfl) ⟨552908, by rfl⟩ : syracuseStep 2948845 = 1105817) (by norm_num)
theorem B3931901 : Blo 1746574 3931901 := bbase (se 3 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 3931901 = 1474463) (by norm_num)
theorem B1965829 : Blo 1746574 1965829 := bbase (se 4 (by rfl) ⟨184296, by rfl⟩ : syracuseStep 1965829 = 368593) (by norm_num)
theorem B2621189 : Blo 1746574 2621189 := bbase (se 4 (by rfl) ⟨245736, by rfl⟩ : syracuseStep 2621189 = 491473) (by norm_num)
theorem B2621213 : Blo 1746574 2621213 := bbase (se 3 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 2621213 = 982955) (by norm_num)
theorem B1965865 : Blo 1746574 1965865 := bbase (se 2 (by rfl) ⟨737199, by rfl⟩ : syracuseStep 1965865 = 1474399) (by norm_num)
theorem B2621237 : Blo 1746574 2621237 := bbase (se 5 (by rfl) ⟨122870, by rfl⟩ : syracuseStep 2621237 = 245741) (by norm_num)
theorem B2948933 : Blo 1746574 2948933 := bbase (se 4 (by rfl) ⟨276462, by rfl⟩ : syracuseStep 2948933 = 552925) (by norm_num)
theorem B3317573 : Blo 1746574 3317573 := bbase (se 4 (by rfl) ⟨311022, by rfl⟩ : syracuseStep 3317573 = 622045) (by norm_num)
theorem B3931973 : Blo 1746574 3931973 := bbase (se 4 (by rfl) ⟨368622, by rfl⟩ : syracuseStep 3931973 = 737245) (by norm_num)
theorem B1965901 : Blo 1746574 1965901 := bbase (se 3 (by rfl) ⟨368606, by rfl⟩ : syracuseStep 1965901 = 737213) (by norm_num)
theorem B2621261 : Blo 1746574 2621261 := bbase (se 3 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 2621261 = 982973) (by norm_num)
theorem B6299477 : Blo 1746574 6299477 := bbase (se 9 (by rfl) ⟨18455, by rfl⟩ : syracuseStep 6299477 = 36911) (by norm_num)
theorem B2621285 : Blo 1746574 2621285 := bbase (se 4 (by rfl) ⟨245745, by rfl⟩ : syracuseStep 2621285 = 491491) (by norm_num)
theorem B1965937 : Blo 1746574 1965937 := bbase (se 2 (by rfl) ⟨737226, by rfl⟩ : syracuseStep 1965937 = 1474453) (by norm_num)
theorem B2621309 : Blo 1746574 2621309 := bbase (se 3 (by rfl) ⟨491495, by rfl⟩ : syracuseStep 2621309 = 982991) (by norm_num)
theorem B2211725 : Blo 1746574 2211725 := bbase (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) (by norm_num)
theorem B3932045 : Blo 1746574 3932045 := bbase (se 3 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 3932045 = 1474517) (by norm_num)
theorem B1965973 : Blo 1746574 1965973 := bbase (se 6 (by rfl) ⟨46077, by rfl⟩ : syracuseStep 1965973 = 92155) (by norm_num)
theorem B2621333 : Blo 1746574 2621333 := bbase (se 6 (by rfl) ⟨61437, by rfl⟩ : syracuseStep 2621333 = 122875) (by norm_num)
theorem B1892245 : Blo 1746574 1892245 := bbase (se 6 (by rfl) ⟨44349, by rfl⟩ : syracuseStep 1892245 = 88699) (by norm_num)
theorem B5898149 : Blo 1746574 5898149 := bbase (se 4 (by rfl) ⟨552951, by rfl⟩ : syracuseStep 5898149 = 1105903) (by norm_num)
theorem B2621357 : Blo 1746574 2621357 := bbase (se 3 (by rfl) ⟨491504, by rfl⟩ : syracuseStep 2621357 = 983009) (by norm_num)
theorem B1966009 : Blo 1746574 1966009 := bbase (se 2 (by rfl) ⟨737253, by rfl⟩ : syracuseStep 1966009 = 1474507) (by norm_num)
theorem B2211781 : Blo 1746574 2211781 := bbase (se 4 (by rfl) ⟨207354, by rfl⟩ : syracuseStep 2211781 = 414709) (by norm_num)
theorem B2621381 : Blo 1746574 2621381 := bbase (se 4 (by rfl) ⟨245754, by rfl⟩ : syracuseStep 2621381 = 491509) (by norm_num)
theorem B2949061 : Blo 1746574 2949061 := bbase (se 4 (by rfl) ⟨276474, by rfl⟩ : syracuseStep 2949061 = 552949) (by norm_num)
theorem B3932117 : Blo 1746574 3932117 := bbase (se 7 (by rfl) ⟨46079, by rfl⟩ : syracuseStep 3932117 = 92159) (by norm_num)
theorem B1966045 : Blo 1746574 1966045 := bbase (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) (by norm_num)
theorem B2621405 : Blo 1746574 2621405 := bbase (se 3 (by rfl) ⟨491513, by rfl⟩ : syracuseStep 2621405 = 983027) (by norm_num)
theorem B2621429 : Blo 1746574 2621429 := bbase (se 5 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 2621429 = 245759) (by norm_num)
theorem B2621441 : Blo 1746574 2621441 := bstep (se 2 (by rfl) ⟨983040, by rfl⟩ : syracuseStep 2621441 = 1966081) B1966081
theorem B5898257 : Blo 1746574 5898257 := bstep (se 2 (by rfl) ⟨2211846, by rfl⟩ : syracuseStep 5898257 = 4423693) B4423693
theorem B2621459 : Blo 1746574 2621459 := bstep (se 1 (by rfl) ⟨1966094, by rfl⟩ : syracuseStep 2621459 = 3932189) B3932189
theorem B1966099 : Blo 1746574 1966099 := bstep (se 1 (by rfl) ⟨1474574, by rfl⟩ : syracuseStep 1966099 = 2949149) B2949149
theorem B2949169 : Blo 1746574 2949169 := bstep (se 2 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 2949169 = 2211877) B2211877
theorem B2621489 : Blo 1746574 2621489 := bstep (se 2 (by rfl) ⟨983058, by rfl⟩ : syracuseStep 2621489 = 1966117) B1966117
theorem B2621507 : Blo 1746574 2621507 := bstep (se 1 (by rfl) ⟨1966130, by rfl⟩ : syracuseStep 2621507 = 3932261) B3932261
theorem B19914821 : Blo 1746574 19914821 := bstep (se 4 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 19914821 = 3734029) B3734029
theorem B2949203 : Blo 1746574 2949203 := bstep (se 1 (by rfl) ⟨2211902, by rfl⟩ : syracuseStep 2949203 = 4423805) B4423805
theorem B2621537 : Blo 1746574 2621537 := bstep (se 2 (by rfl) ⟨983076, by rfl⟩ : syracuseStep 2621537 = 1966153) B1966153
theorem B2621555 : Blo 1746574 2621555 := bstep (se 1 (by rfl) ⟨1966166, by rfl⟩ : syracuseStep 2621555 = 3932333) B3932333
theorem B2990209 : Blo 1746574 2990209 := bstep (se 2 (by rfl) ⟨1121328, by rfl⟩ : syracuseStep 2990209 = 2242657) B2242657
theorem B9445517 : Blo 1746574 9445517 := bstep (se 3 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 9445517 = 3542069) B3542069
theorem B2621585 : Blo 1746574 2621585 := bstep (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) B1966189
theorem B2621603 : Blo 1746574 2621603 := bstep (se 1 (by rfl) ⟨1966202, by rfl⟩ : syracuseStep 2621603 = 3932405) B3932405
theorem B1966243 : Blo 1746574 1966243 := bstep (se 1 (by rfl) ⟨1474682, by rfl⟩ : syracuseStep 1966243 = 2949365) B2949365
theorem B2621633 : Blo 1746574 2621633 := bstep (se 2 (by rfl) ⟨983112, by rfl⟩ : syracuseStep 2621633 = 1966225) B1966225
theorem B3932369 : Blo 1746574 3932369 := bstep (se 2 (by rfl) ⟨1474638, by rfl⟩ : syracuseStep 3932369 = 2949277) B2949277
theorem B2949331 : Blo 1746574 2949331 := bstep (se 1 (by rfl) ⟨2211998, by rfl⟩ : syracuseStep 2949331 = 4423997) B4423997
theorem B2621651 : Blo 1746574 2621651 := bstep (se 1 (by rfl) ⟨1966238, by rfl⟩ : syracuseStep 2621651 = 3932477) B3932477
theorem B3932387 : Blo 1746574 3932387 := bstep (se 1 (by rfl) ⟨2949290, by rfl⟩ : syracuseStep 3932387 = 5898581) B5898581
theorem B2621681 : Blo 1746574 2621681 := bstep (se 2 (by rfl) ⟨983130, by rfl⟩ : syracuseStep 2621681 = 1966261) B1966261
theorem B2621699 : Blo 1746574 2621699 := bstep (se 1 (by rfl) ⟨1966274, by rfl⟩ : syracuseStep 2621699 = 3932549) B3932549
theorem B8847629 : Blo 1746574 8847629 := bstep (se 3 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 8847629 = 3317861) B3317861
theorem B2621729 : Blo 1746574 2621729 := bstep (se 2 (by rfl) ⟨983148, by rfl⟩ : syracuseStep 2621729 = 1966297) B1966297
theorem B2621747 : Blo 1746574 2621747 := bstep (se 1 (by rfl) ⟨1966310, by rfl⟩ : syracuseStep 2621747 = 3932621) B3932621
theorem B1966387 : Blo 1746574 1966387 := bstep (se 1 (by rfl) ⟨1474790, by rfl⟩ : syracuseStep 1966387 = 2949581) B2949581
theorem B4424017 : Blo 1746574 4424017 := bstep (se 2 (by rfl) ⟨1659006, by rfl⟩ : syracuseStep 4424017 = 3318013) B3318013
theorem B3318097 : Blo 1746574 3318097 := bstep (se 2 (by rfl) ⟨1244286, by rfl⟩ : syracuseStep 3318097 = 2488573) B2488573
theorem B2621777 : Blo 1746574 2621777 := bstep (se 2 (by rfl) ⟨983166, by rfl⟩ : syracuseStep 2621777 = 1966333) B1966333
theorem B2949473 : Blo 1746574 2949473 := bstep (se 2 (by rfl) ⟨1106052, by rfl⟩ : syracuseStep 2949473 = 2212105) B2212105
theorem B2621795 : Blo 1746574 2621795 := bstep (se 1 (by rfl) ⟨1966346, by rfl⟩ : syracuseStep 2621795 = 3932693) B3932693
theorem B2212211 : Blo 1746574 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B2621825 : Blo 1746574 2621825 := bstep (se 2 (by rfl) ⟨983184, by rfl⟩ : syracuseStep 2621825 = 1966369) B1966369
theorem B2621843 : Blo 1746574 2621843 := bstep (se 1 (by rfl) ⟨1966382, by rfl⟩ : syracuseStep 2621843 = 3932765) B3932765
theorem B2621873 : Blo 1746574 2621873 := bstep (se 2 (by rfl) ⟨983202, by rfl⟩ : syracuseStep 2621873 = 1966405) B1966405
theorem B2621891 : Blo 1746574 2621891 := bstep (se 1 (by rfl) ⟨1966418, by rfl⟩ : syracuseStep 2621891 = 3932837) B3932837
theorem B1966531 : Blo 1746574 1966531 := bstep (se 1 (by rfl) ⟨1474898, by rfl⟩ : syracuseStep 1966531 = 2949797) B2949797
theorem B37806533 : Blo 1746574 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B7668173 : Blo 1746574 7668173 := bstep (se 3 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 7668173 = 2875565) B2875565
theorem B2949601 : Blo 1746574 2949601 := bstep (se 2 (by rfl) ⟨1106100, by rfl⟩ : syracuseStep 2949601 = 2212201) B2212201
theorem B2621921 : Blo 1746574 2621921 := bstep (se 2 (by rfl) ⟨983220, by rfl⟩ : syracuseStep 2621921 = 1966441) B1966441
theorem B3932657 : Blo 1746574 3932657 := bstep (se 2 (by rfl) ⟨1474746, by rfl⟩ : syracuseStep 3932657 = 2949493) B2949493
theorem B2621939 : Blo 1746574 2621939 := bstep (se 1 (by rfl) ⟨1966454, by rfl⟩ : syracuseStep 2621939 = 3932909) B3932909
theorem B3932675 : Blo 1746574 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B2949635 : Blo 1746574 2949635 := bstep (se 1 (by rfl) ⟨2212226, by rfl⟩ : syracuseStep 2949635 = 4424453) B4424453
theorem B3785219 : Blo 1746574 3785219 := bstep (se 1 (by rfl) ⟨2838914, by rfl⟩ : syracuseStep 3785219 = 5677829) B5677829
theorem B2621969 : Blo 1746574 2621969 := bstep (se 2 (by rfl) ⟨983238, by rfl⟩ : syracuseStep 2621969 = 1966477) B1966477
theorem B49136149 : Blo 1746574 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B2621987 : Blo 1746574 2621987 := bstep (se 1 (by rfl) ⟨1966490, by rfl⟩ : syracuseStep 2621987 = 3932981) B3932981
theorem B5898797 : Blo 1746574 5898797 := bstep (se 3 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 5898797 = 2212049) B2212049
theorem B2622017 : Blo 1746574 2622017 := bstep (se 2 (by rfl) ⟨983256, by rfl⟩ : syracuseStep 2622017 = 1966513) B1966513
theorem B2622035 : Blo 1746574 2622035 := bstep (se 1 (by rfl) ⟨1966526, by rfl⟩ : syracuseStep 2622035 = 3933053) B3933053
theorem B1966675 : Blo 1746574 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B5898851 : Blo 1746574 5898851 := bstep (se 1 (by rfl) ⟨4424138, by rfl⟩ : syracuseStep 5898851 = 8848277) B8848277
theorem B4424291 : Blo 1746574 4424291 := bstep (se 1 (by rfl) ⟨3318218, by rfl⟩ : syracuseStep 4424291 = 6636437) B6636437
theorem B2622065 : Blo 1746574 2622065 := bstep (se 2 (by rfl) ⟨983274, by rfl⟩ : syracuseStep 2622065 = 1966549) B1966549
theorem B2949763 : Blo 1746574 2949763 := bstep (se 1 (by rfl) ⟨2212322, by rfl⟩ : syracuseStep 2949763 = 4424645) B4424645
theorem B2622083 : Blo 1746574 2622083 := bstep (se 1 (by rfl) ⟨1966562, by rfl⟩ : syracuseStep 2622083 = 3933125) B3933125
theorem B2622113 : Blo 1746574 2622113 := bstep (se 2 (by rfl) ⟨983292, by rfl⟩ : syracuseStep 2622113 = 1966585) B1966585
theorem B2622131 : Blo 1746574 2622131 := bstep (se 1 (by rfl) ⟨1966598, by rfl⟩ : syracuseStep 2622131 = 3933197) B3933197
theorem B2622161 : Blo 1746574 2622161 := bstep (se 2 (by rfl) ⟨983310, by rfl⟩ : syracuseStep 2622161 = 1966621) B1966621
theorem B3318499 : Blo 1746574 3318499 := bstep (se 1 (by rfl) ⟨2488874, by rfl⟩ : syracuseStep 3318499 = 4977749) B4977749
theorem B2622179 : Blo 1746574 2622179 := bstep (se 1 (by rfl) ⟨1966634, by rfl⟩ : syracuseStep 2622179 = 3933269) B3933269
theorem B1966819 : Blo 1746574 1966819 := bstep (se 1 (by rfl) ⟨1475114, by rfl⟩ : syracuseStep 1966819 = 2950229) B2950229
theorem B11199217 : Blo 1746574 11199217 := bstep (se 2 (by rfl) ⟨4199706, by rfl⟩ : syracuseStep 11199217 = 8399413) B8399413
theorem B2622209 : Blo 1746574 2622209 := bstep (se 2 (by rfl) ⟨983328, by rfl⟩ : syracuseStep 2622209 = 1966657) B1966657
theorem B3932945 : Blo 1746574 3932945 := bstep (se 2 (by rfl) ⟨1474854, by rfl⟩ : syracuseStep 3932945 = 2949709) B2949709
theorem B3318545 : Blo 1746574 3318545 := bstep (se 2 (by rfl) ⟨1244454, by rfl⟩ : syracuseStep 3318545 = 2488909) B2488909
theorem B2949905 : Blo 1746574 2949905 := bstep (se 2 (by rfl) ⟨1106214, by rfl⟩ : syracuseStep 2949905 = 2212429) B2212429
theorem B2622227 : Blo 1746574 2622227 := bstep (se 1 (by rfl) ⟨1966670, by rfl⟩ : syracuseStep 2622227 = 3933341) B3933341
theorem B4424483 : Blo 1746574 4424483 := bstep (se 1 (by rfl) ⟨3318362, by rfl⟩ : syracuseStep 4424483 = 6636725) B6636725
theorem B3932963 : Blo 1746574 3932963 := bstep (se 1 (by rfl) ⟨2949722, by rfl⟩ : syracuseStep 3932963 = 5899445) B5899445
theorem B2622257 : Blo 1746574 2622257 := bstep (se 2 (by rfl) ⟨983346, by rfl⟩ : syracuseStep 2622257 = 1966693) B1966693
theorem B2622275 : Blo 1746574 2622275 := bstep (se 1 (by rfl) ⟨1966706, by rfl⟩ : syracuseStep 2622275 = 3933413) B3933413
theorem B2622305 : Blo 1746574 2622305 := bstep (se 2 (by rfl) ⟨983364, by rfl⟩ : syracuseStep 2622305 = 1966729) B1966729
theorem B5899121 : Blo 1746574 5899121 := bstep (se 2 (by rfl) ⟨2212170, by rfl⟩ : syracuseStep 5899121 = 4424341) B4424341
theorem B2622323 : Blo 1746574 2622323 := bstep (se 1 (by rfl) ⟨1966742, by rfl⟩ : syracuseStep 2622323 = 3933485) B3933485
theorem B1966963 : Blo 1746574 1966963 := bstep (se 1 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 1966963 = 2950445) B2950445
theorem B7463821 : Blo 1746574 7463821 := bstep (se 3 (by rfl) ⟨1399466, by rfl⟩ : syracuseStep 7463821 = 2798933) B2798933
theorem B2950033 : Blo 1746574 2950033 := bstep (se 2 (by rfl) ⟨1106262, by rfl⟩ : syracuseStep 2950033 = 2212525) B2212525
theorem B2622353 : Blo 1746574 2622353 := bstep (se 2 (by rfl) ⟨983382, by rfl⟩ : syracuseStep 2622353 = 1966765) B1966765
theorem B6636451 : Blo 1746574 6636451 := bstep (se 1 (by rfl) ⟨4977338, by rfl⟩ : syracuseStep 6636451 = 9954677) B9954677
theorem B2622371 : Blo 1746574 2622371 := bstep (se 1 (by rfl) ⟨1966778, by rfl⟩ : syracuseStep 2622371 = 3933557) B3933557
theorem B2950067 : Blo 1746574 2950067 := bstep (se 1 (by rfl) ⟨2212550, by rfl⟩ : syracuseStep 2950067 = 4425101) B4425101
theorem B2622401 : Blo 1746574 2622401 := bstep (se 2 (by rfl) ⟨983400, by rfl⟩ : syracuseStep 2622401 = 1966801) B1966801
theorem B2622419 : Blo 1746574 2622419 := bstep (se 1 (by rfl) ⟨1966814, by rfl⟩ : syracuseStep 2622419 = 3933629) B3933629
theorem B2622449 : Blo 1746574 2622449 := bstep (se 2 (by rfl) ⟨983418, by rfl⟩ : syracuseStep 2622449 = 1966837) B1966837
theorem B2622467 : Blo 1746574 2622467 := bstep (se 1 (by rfl) ⟨1966850, by rfl⟩ : syracuseStep 2622467 = 3933701) B3933701
theorem B1967107 : Blo 1746574 1967107 := bstep (se 1 (by rfl) ⟨1475330, by rfl⟩ : syracuseStep 1967107 = 2950661) B2950661
theorem B2622497 : Blo 1746574 2622497 := bstep (se 2 (by rfl) ⟨983436, by rfl⟩ : syracuseStep 2622497 = 1966873) B1966873
theorem B3933233 : Blo 1746574 3933233 := bstep (se 2 (by rfl) ⟨1474962, by rfl⟩ : syracuseStep 3933233 = 2949925) B2949925
theorem B3318833 : Blo 1746574 3318833 := bstep (se 2 (by rfl) ⟨1244562, by rfl⟩ : syracuseStep 3318833 = 2489125) B2489125
theorem B2950195 : Blo 1746574 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B2622515 : Blo 1746574 2622515 := bstep (se 1 (by rfl) ⟨1966886, by rfl⟩ : syracuseStep 2622515 = 3933773) B3933773
theorem B2212915 : Blo 1746574 2212915 := bstep (se 1 (by rfl) ⟨1659686, by rfl⟩ : syracuseStep 2212915 = 3319373) B3319373
theorem B3933251 : Blo 1746574 3933251 := bstep (se 1 (by rfl) ⟨2949938, by rfl⟩ : syracuseStep 3933251 = 5899877) B5899877
theorem B2622545 : Blo 1746574 2622545 := bstep (se 2 (by rfl) ⟨983454, by rfl⟩ : syracuseStep 2622545 = 1966909) B1966909
theorem B2622563 : Blo 1746574 2622563 := bstep (se 1 (by rfl) ⟨1966922, by rfl⟩ : syracuseStep 2622563 = 3933845) B3933845
theorem B50398321 : Blo 1746574 50398321 := bstep (se 2 (by rfl) ⟨18899370, by rfl⟩ : syracuseStep 50398321 = 37798741) B37798741
theorem B2622593 : Blo 1746574 2622593 := bstep (se 2 (by rfl) ⟨983472, by rfl⟩ : syracuseStep 2622593 = 1966945) B1966945
theorem B2622611 : Blo 1746574 2622611 := bstep (se 1 (by rfl) ⟨1966958, by rfl⟩ : syracuseStep 2622611 = 3933917) B3933917
theorem B2213011 : Blo 1746574 2213011 := bstep (se 1 (by rfl) ⟨1659758, by rfl⟩ : syracuseStep 2213011 = 3319517) B3319517
theorem B2622641 : Blo 1746574 2622641 := bstep (se 2 (by rfl) ⟨983490, by rfl⟩ : syracuseStep 2622641 = 1966981) B1966981
theorem B2950337 : Blo 1746574 2950337 := bstep (se 2 (by rfl) ⟨1106376, by rfl⟩ : syracuseStep 2950337 = 2212753) B2212753
theorem B2622659 : Blo 1746574 2622659 := bstep (se 1 (by rfl) ⟨1966994, by rfl⟩ : syracuseStep 2622659 = 3933989) B3933989
theorem B14165189 : Blo 1746574 14165189 := bstep (se 4 (by rfl) ⟨1327986, by rfl⟩ : syracuseStep 14165189 = 2655973) B2655973
theorem B2622689 : Blo 1746574 2622689 := bstep (se 2 (by rfl) ⟨983508, by rfl⟩ : syracuseStep 2622689 = 1967017) B1967017
theorem B7464163 : Blo 1746574 7464163 := bstep (se 1 (by rfl) ⟨5598122, by rfl⟩ : syracuseStep 7464163 = 11196245) B11196245
theorem B2622707 : Blo 1746574 2622707 := bstep (se 1 (by rfl) ⟨1967030, by rfl⟩ : syracuseStep 2622707 = 3934061) B3934061
theorem B2622737 : Blo 1746574 2622737 := bstep (se 2 (by rfl) ⟨983526, by rfl⟩ : syracuseStep 2622737 = 1967053) B1967053
theorem B2622755 : Blo 1746574 2622755 := bstep (se 1 (by rfl) ⟨1967066, by rfl⟩ : syracuseStep 2622755 = 3934133) B3934133
theorem B2950465 : Blo 1746574 2950465 := bstep (se 2 (by rfl) ⟨1106424, by rfl⟩ : syracuseStep 2950465 = 2212849) B2212849
theorem B2622785 : Blo 1746574 2622785 := bstep (se 2 (by rfl) ⟨983544, by rfl⟩ : syracuseStep 2622785 = 1967089) B1967089
theorem B3933521 : Blo 1746574 3933521 := bstep (se 2 (by rfl) ⟨1475070, by rfl⟩ : syracuseStep 3933521 = 2950141) B2950141
theorem B2622803 : Blo 1746574 2622803 := bstep (se 1 (by rfl) ⟨1967102, by rfl⟩ : syracuseStep 2622803 = 3934205) B3934205
theorem B3933539 : Blo 1746574 3933539 := bstep (se 1 (by rfl) ⟨2950154, by rfl⟩ : syracuseStep 3933539 = 5900309) B5900309
theorem B2950499 : Blo 1746574 2950499 := bstep (se 1 (by rfl) ⟨2212874, by rfl⟩ : syracuseStep 2950499 = 4425749) B4425749
theorem B2622833 : Blo 1746574 2622833 := bstep (se 2 (by rfl) ⟨983562, by rfl⟩ : syracuseStep 2622833 = 1967125) B1967125
theorem B2622851 : Blo 1746574 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B5899661 : Blo 1746574 5899661 := bstep (se 3 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 5899661 = 2212373) B2212373
theorem B2098595 : Blo 1746574 2098595 := bstep (se 1 (by rfl) ⟨1573946, by rfl⟩ : syracuseStep 2098595 = 3147893) B3147893
theorem B5899715 : Blo 1746574 5899715 := bstep (se 1 (by rfl) ⟨4424786, by rfl⟩ : syracuseStep 5899715 = 8849573) B8849573
theorem B15943139 : Blo 1746574 15943139 := bstep (se 1 (by rfl) ⟨11957354, by rfl⟩ : syracuseStep 15943139 = 23914709) B23914709
theorem B2950627 : Blo 1746574 2950627 := bstep (se 1 (by rfl) ⟨2212970, by rfl⟩ : syracuseStep 2950627 = 4425941) B4425941
theorem B2835953 : Blo 1746574 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B13264397 : Blo 1746574 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B21268021 : Blo 1746574 21268021 := bstep (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) B1993877
theorem B5596739 : Blo 1746574 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B36374129 : Blo 1746574 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B3933809 : Blo 1746574 3933809 := bstep (se 2 (by rfl) ⟨1475178, by rfl⟩ : syracuseStep 3933809 = 2950357) B2950357
theorem B3933827 : Blo 1746574 3933827 := bstep (se 1 (by rfl) ⟨2950370, by rfl⟩ : syracuseStep 3933827 = 5900741) B5900741
theorem B1746579 : Blo 1746574 1746579 := bstep (se 1 (by rfl) ⟨1309934, by rfl⟩ : syracuseStep 1746579 = 2619869) B2619869
theorem B1746595 : Blo 1746574 1746595 := bstep (se 1 (by rfl) ⟨1309946, by rfl⟩ : syracuseStep 1746595 = 2619893) B2619893
theorem B1746611 : Blo 1746574 1746611 := bstep (se 1 (by rfl) ⟨1309958, by rfl⟩ : syracuseStep 1746611 = 2619917) B2619917
theorem B1746627 : Blo 1746574 1746627 := bstep (se 1 (by rfl) ⟨1309970, by rfl⟩ : syracuseStep 1746627 = 2619941) B2619941
theorem B5596867 : Blo 1746574 5596867 := bstep (se 1 (by rfl) ⟨4197650, by rfl⟩ : syracuseStep 5596867 = 8395301) B8395301
theorem B5899985 : Blo 1746574 5899985 := bstep (se 2 (by rfl) ⟨2212494, by rfl⟩ : syracuseStep 5899985 = 4424989) B4424989
theorem B4425425 : Blo 1746574 4425425 := bstep (se 2 (by rfl) ⟨1659534, by rfl⟩ : syracuseStep 4425425 = 3319069) B3319069
theorem B1746643 : Blo 1746574 1746643 := bstep (se 1 (by rfl) ⟨1309982, by rfl⟩ : syracuseStep 1746643 = 2619965) B2619965
theorem B1746659 : Blo 1746574 1746659 := bstep (se 1 (by rfl) ⟨1309994, by rfl⟩ : syracuseStep 1746659 = 2619989) B2619989
theorem B12592867 : Blo 1746574 12592867 := bstep (se 1 (by rfl) ⟨9444650, by rfl⟩ : syracuseStep 12592867 = 18889301) B18889301
theorem B1746675 : Blo 1746574 1746675 := bstep (se 1 (by rfl) ⟨1310006, by rfl⟩ : syracuseStep 1746675 = 2620013) B2620013
theorem B1746691 : Blo 1746574 1746691 := bstep (se 1 (by rfl) ⟨1310018, by rfl⟩ : syracuseStep 1746691 = 2620037) B2620037
theorem B4425475 : Blo 1746574 4425475 := bstep (se 1 (by rfl) ⟨3319106, by rfl⟩ : syracuseStep 4425475 = 6638213) B6638213
theorem B3319555 : Blo 1746574 3319555 := bstep (se 1 (by rfl) ⟨2489666, by rfl⟩ : syracuseStep 3319555 = 4979333) B4979333
theorem B1746707 : Blo 1746574 1746707 := bstep (se 1 (by rfl) ⟨1310030, by rfl⟩ : syracuseStep 1746707 = 2620061) B2620061
theorem B1746723 : Blo 1746574 1746723 := bstep (se 1 (by rfl) ⟨1310042, by rfl⟩ : syracuseStep 1746723 = 2620085) B2620085
theorem B1746739 : Blo 1746574 1746739 := bstep (se 1 (by rfl) ⟨1310054, by rfl⟩ : syracuseStep 1746739 = 2620109) B2620109
theorem B1746755 : Blo 1746574 1746755 := bstep (se 1 (by rfl) ⟨1310066, by rfl⟩ : syracuseStep 1746755 = 2620133) B2620133
theorem B7087949 : Blo 1746574 7087949 := bstep (se 3 (by rfl) ⟨1328990, by rfl⟩ : syracuseStep 7087949 = 2657981) B2657981
theorem B1746771 : Blo 1746574 1746771 := bstep (se 1 (by rfl) ⟨1310078, by rfl⟩ : syracuseStep 1746771 = 2620157) B2620157
theorem B1746787 : Blo 1746574 1746787 := bstep (se 1 (by rfl) ⟨1310090, by rfl⟩ : syracuseStep 1746787 = 2620181) B2620181
theorem B12593009 : Blo 1746574 12593009 := bstep (se 2 (by rfl) ⟨4722378, by rfl⟩ : syracuseStep 12593009 = 9444757) B9444757
theorem B1746803 : Blo 1746574 1746803 := bstep (se 1 (by rfl) ⟨1310102, by rfl⟩ : syracuseStep 1746803 = 2620205) B2620205
theorem B2877299 : Blo 1746574 2877299 := bstep (se 1 (by rfl) ⟨2157974, by rfl⟩ : syracuseStep 2877299 = 4315949) B4315949
theorem B1746819 : Blo 1746574 1746819 := bstep (se 1 (by rfl) ⟨1310114, by rfl⟩ : syracuseStep 1746819 = 2620229) B2620229
theorem B4425617 : Blo 1746574 4425617 := bstep (se 2 (by rfl) ⟨1659606, by rfl⟩ : syracuseStep 4425617 = 3319213) B3319213
theorem B3934097 : Blo 1746574 3934097 := bstep (se 2 (by rfl) ⟨1475286, by rfl⟩ : syracuseStep 3934097 = 2950573) B2950573
theorem B1746835 : Blo 1746574 1746835 := bstep (se 1 (by rfl) ⟨1310126, by rfl⟩ : syracuseStep 1746835 = 2620253) B2620253
theorem B1746851 : Blo 1746574 1746851 := bstep (se 1 (by rfl) ⟨1310138, by rfl⟩ : syracuseStep 1746851 = 2620277) B2620277
theorem B2656163 : Blo 1746574 2656163 := bstep (se 1 (by rfl) ⟨1992122, by rfl⟩ : syracuseStep 2656163 = 3984245) B3984245
theorem B1771427 : Blo 1746574 1771427 := bstep (se 1 (by rfl) ⟨1328570, by rfl⟩ : syracuseStep 1771427 = 2657141) B2657141
theorem B3934115 : Blo 1746574 3934115 := bstep (se 1 (by rfl) ⟨2950586, by rfl⟩ : syracuseStep 3934115 = 5901173) B5901173
theorem B1746867 : Blo 1746574 1746867 := bstep (se 1 (by rfl) ⟨1310150, by rfl⟩ : syracuseStep 1746867 = 2620301) B2620301
theorem B1746883 : Blo 1746574 1746883 := bstep (se 1 (by rfl) ⟨1310162, by rfl⟩ : syracuseStep 1746883 = 2620325) B2620325
theorem B1746899 : Blo 1746574 1746899 := bstep (se 1 (by rfl) ⟨1310174, by rfl⟩ : syracuseStep 1746899 = 2620349) B2620349
theorem B1746915 : Blo 1746574 1746915 := bstep (se 1 (by rfl) ⟨1310186, by rfl⟩ : syracuseStep 1746915 = 2620373) B2620373
theorem B12593123 : Blo 1746574 12593123 := bstep (se 1 (by rfl) ⟨9444842, by rfl⟩ : syracuseStep 12593123 = 18889685) B18889685
theorem B1746931 : Blo 1746574 1746931 := bstep (se 1 (by rfl) ⟨1310198, by rfl⟩ : syracuseStep 1746931 = 2620397) B2620397
theorem B1746947 : Blo 1746574 1746947 := bstep (se 1 (by rfl) ⟨1310210, by rfl⟩ : syracuseStep 1746947 = 2620421) B2620421
theorem B4974605 : Blo 1746574 4974605 := bstep (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) B1865477
theorem B5597201 : Blo 1746574 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B1746963 : Blo 1746574 1746963 := bstep (se 1 (by rfl) ⟨1310222, by rfl⟩ : syracuseStep 1746963 = 2620445) B2620445
theorem B1746979 : Blo 1746574 1746979 := bstep (se 1 (by rfl) ⟨1310234, by rfl⟩ : syracuseStep 1746979 = 2620469) B2620469
theorem B1746995 : Blo 1746574 1746995 := bstep (se 1 (by rfl) ⟨1310246, by rfl⟩ : syracuseStep 1746995 = 2620493) B2620493
theorem B1747011 : Blo 1746574 1747011 := bstep (se 1 (by rfl) ⟨1310258, by rfl⟩ : syracuseStep 1747011 = 2620517) B2620517
theorem B1747027 : Blo 1746574 1747027 := bstep (se 1 (by rfl) ⟨1310270, by rfl⟩ : syracuseStep 1747027 = 2620541) B2620541
theorem B1747043 : Blo 1746574 1747043 := bstep (se 1 (by rfl) ⟨1310282, by rfl⟩ : syracuseStep 1747043 = 2620565) B2620565
theorem B1747059 : Blo 1746574 1747059 := bstep (se 1 (by rfl) ⟨1310294, by rfl⟩ : syracuseStep 1747059 = 2620589) B2620589
theorem B1747075 : Blo 1746574 1747075 := bstep (se 1 (by rfl) ⟨1310306, by rfl⟩ : syracuseStep 1747075 = 2620613) B2620613
theorem B1747091 : Blo 1746574 1747091 := bstep (se 1 (by rfl) ⟨1310318, by rfl⟩ : syracuseStep 1747091 = 2620637) B2620637
theorem B1747107 : Blo 1746574 1747107 := bstep (se 1 (by rfl) ⟨1310330, by rfl⟩ : syracuseStep 1747107 = 2620661) B2620661
theorem B6817969 : Blo 1746574 6817969 := bstep (se 2 (by rfl) ⟨2556738, by rfl⟩ : syracuseStep 6817969 = 5113477) B5113477
theorem B1747123 : Blo 1746574 1747123 := bstep (se 1 (by rfl) ⟨1310342, by rfl⟩ : syracuseStep 1747123 = 2620685) B2620685
theorem B4974787 : Blo 1746574 4974787 := bstep (se 1 (by rfl) ⟨3731090, by rfl⟩ : syracuseStep 4974787 = 7462181) B7462181
theorem B1747139 : Blo 1746574 1747139 := bstep (se 1 (by rfl) ⟨1310354, by rfl⟩ : syracuseStep 1747139 = 2620709) B2620709
theorem B1747155 : Blo 1746574 1747155 := bstep (se 1 (by rfl) ⟨1310366, by rfl⟩ : syracuseStep 1747155 = 2620733) B2620733
theorem B1747171 : Blo 1746574 1747171 := bstep (se 1 (by rfl) ⟨1310378, by rfl⟩ : syracuseStep 1747171 = 2620757) B2620757
theorem B8079587 : Blo 1746574 8079587 := bstep (se 1 (by rfl) ⟨6059690, by rfl⟩ : syracuseStep 8079587 = 12119381) B12119381
theorem B5900525 : Blo 1746574 5900525 := bstep (se 3 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 5900525 = 2212697) B2212697
theorem B4974833 : Blo 1746574 4974833 := bstep (se 2 (by rfl) ⟨1865562, by rfl⟩ : syracuseStep 4974833 = 3731125) B3731125
theorem B1747187 : Blo 1746574 1747187 := bstep (se 1 (by rfl) ⟨1310390, by rfl⟩ : syracuseStep 1747187 = 2620781) B2620781
theorem B1747203 : Blo 1746574 1747203 := bstep (se 1 (by rfl) ⟨1310402, by rfl⟩ : syracuseStep 1747203 = 2620805) B2620805
theorem B3983633 : Blo 1746574 3983633 := bstep (se 2 (by rfl) ⟨1493862, by rfl⟩ : syracuseStep 3983633 = 2987725) B2987725
theorem B1747219 : Blo 1746574 1747219 := bstep (se 1 (by rfl) ⟨1310414, by rfl⟩ : syracuseStep 1747219 = 2620829) B2620829
theorem B1747235 : Blo 1746574 1747235 := bstep (se 1 (by rfl) ⟨1310426, by rfl⟩ : syracuseStep 1747235 = 2620853) B2620853
theorem B5900579 : Blo 1746574 5900579 := bstep (se 1 (by rfl) ⟨4425434, by rfl⟩ : syracuseStep 5900579 = 8850869) B8850869
theorem B1747251 : Blo 1746574 1747251 := bstep (se 1 (by rfl) ⟨1310438, by rfl⟩ : syracuseStep 1747251 = 2620877) B2620877
theorem B1747267 : Blo 1746574 1747267 := bstep (se 1 (by rfl) ⟨1310450, by rfl⟩ : syracuseStep 1747267 = 2620901) B2620901
theorem B1747283 : Blo 1746574 1747283 := bstep (se 1 (by rfl) ⟨1310462, by rfl⟩ : syracuseStep 1747283 = 2620925) B2620925
theorem B1747299 : Blo 1746574 1747299 := bstep (se 1 (by rfl) ⟨1310474, by rfl⟩ : syracuseStep 1747299 = 2620949) B2620949
theorem B1747315 : Blo 1746574 1747315 := bstep (se 1 (by rfl) ⟨1310486, by rfl⟩ : syracuseStep 1747315 = 2620973) B2620973
theorem B1747331 : Blo 1746574 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B1747347 : Blo 1746574 1747347 := bstep (se 1 (by rfl) ⟨1310510, by rfl⟩ : syracuseStep 1747347 = 2621021) B2621021
theorem B1747363 : Blo 1746574 1747363 := bstep (se 1 (by rfl) ⟨1310522, by rfl⟩ : syracuseStep 1747363 = 2621045) B2621045
theorem B9947569 : Blo 1746574 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B1747379 : Blo 1746574 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B1747395 : Blo 1746574 1747395 := bstep (se 1 (by rfl) ⟨1310546, by rfl⟩ : syracuseStep 1747395 = 2621093) B2621093
theorem B1747411 : Blo 1746574 1747411 := bstep (se 1 (by rfl) ⟨1310558, by rfl⟩ : syracuseStep 1747411 = 2621117) B2621117
theorem B1747427 : Blo 1746574 1747427 := bstep (se 1 (by rfl) ⟨1310570, by rfl⟩ : syracuseStep 1747427 = 2621141) B2621141
theorem B1747443 : Blo 1746574 1747443 := bstep (se 1 (by rfl) ⟨1310582, by rfl⟩ : syracuseStep 1747443 = 2621165) B2621165
theorem B1747459 : Blo 1746574 1747459 := bstep (se 1 (by rfl) ⟨1310594, by rfl⟩ : syracuseStep 1747459 = 2621189) B2621189
theorem B1747475 : Blo 1746574 1747475 := bstep (se 1 (by rfl) ⟨1310606, by rfl⟩ : syracuseStep 1747475 = 2621213) B2621213
theorem B1747491 : Blo 1746574 1747491 := bstep (se 1 (by rfl) ⟨1310618, by rfl⟩ : syracuseStep 1747491 = 2621237) B2621237
theorem B5900849 : Blo 1746574 5900849 := bstep (se 2 (by rfl) ⟨2212818, by rfl⟩ : syracuseStep 5900849 = 4425637) B4425637
theorem B1747507 : Blo 1746574 1747507 := bstep (se 1 (by rfl) ⟨1310630, by rfl⟩ : syracuseStep 1747507 = 2621261) B2621261
theorem B1747523 : Blo 1746574 1747523 := bstep (se 1 (by rfl) ⟨1310642, by rfl⟩ : syracuseStep 1747523 = 2621285) B2621285
theorem B2656849 : Blo 1746574 2656849 := bstep (se 2 (by rfl) ⟨996318, by rfl⟩ : syracuseStep 2656849 = 1992637) B1992637
theorem B1747539 : Blo 1746574 1747539 := bstep (se 1 (by rfl) ⟨1310654, by rfl⟩ : syracuseStep 1747539 = 2621309) B2621309
theorem B1747555 : Blo 1746574 1747555 := bstep (se 1 (by rfl) ⟨1310666, by rfl⟩ : syracuseStep 1747555 = 2621333) B2621333
theorem B1747571 : Blo 1746574 1747571 := bstep (se 1 (by rfl) ⟨1310678, by rfl⟩ : syracuseStep 1747571 = 2621357) B2621357
theorem B1747587 : Blo 1746574 1747587 := bstep (se 1 (by rfl) ⟨1310690, by rfl⟩ : syracuseStep 1747587 = 2621381) B2621381
theorem B1747603 : Blo 1746574 1747603 := bstep (se 1 (by rfl) ⟨1310702, by rfl⟩ : syracuseStep 1747603 = 2621405) B2621405
theorem B1747619 : Blo 1746574 1747619 := bstep (se 1 (by rfl) ⟨1310714, by rfl⟩ : syracuseStep 1747619 = 2621429) B2621429
theorem B1747635 : Blo 1746574 1747635 := bstep (se 1 (by rfl) ⟨1310726, by rfl⟩ : syracuseStep 1747635 = 2621453) B2621453
theorem B1747651 : Blo 1746574 1747651 := bstep (se 1 (by rfl) ⟨1310738, by rfl⟩ : syracuseStep 1747651 = 2621477) B2621477
theorem B1747667 : Blo 1746574 1747667 := bstep (se 1 (by rfl) ⟨1310750, by rfl⟩ : syracuseStep 1747667 = 2621501) B2621501
theorem B1747683 : Blo 1746574 1747683 := bstep (se 1 (by rfl) ⟨1310762, by rfl⟩ : syracuseStep 1747683 = 2621525) B2621525
theorem B1747699 : Blo 1746574 1747699 := bstep (se 1 (by rfl) ⟨1310774, by rfl⟩ : syracuseStep 1747699 = 2621549) B2621549
theorem B1747715 : Blo 1746574 1747715 := bstep (se 1 (by rfl) ⟨1310786, by rfl⟩ : syracuseStep 1747715 = 2621573) B2621573
theorem B1747731 : Blo 1746574 1747731 := bstep (se 1 (by rfl) ⟨1310798, by rfl⟩ : syracuseStep 1747731 = 2621597) B2621597
theorem B1747747 : Blo 1746574 1747747 := bstep (se 1 (by rfl) ⟨1310810, by rfl⟩ : syracuseStep 1747747 = 2621621) B2621621
theorem B1747763 : Blo 1746574 1747763 := bstep (se 1 (by rfl) ⟨1310822, by rfl⟩ : syracuseStep 1747763 = 2621645) B2621645
theorem B1747779 : Blo 1746574 1747779 := bstep (se 1 (by rfl) ⟨1310834, by rfl⟩ : syracuseStep 1747779 = 2621669) B2621669
theorem B1747795 : Blo 1746574 1747795 := bstep (se 1 (by rfl) ⟨1310846, by rfl⟩ : syracuseStep 1747795 = 2621693) B2621693
theorem B1747811 : Blo 1746574 1747811 := bstep (se 1 (by rfl) ⟨1310858, by rfl⟩ : syracuseStep 1747811 = 2621717) B2621717
theorem B1747827 : Blo 1746574 1747827 := bstep (se 1 (by rfl) ⟨1310870, by rfl⟩ : syracuseStep 1747827 = 2621741) B2621741
theorem B1747843 : Blo 1746574 1747843 := bstep (se 1 (by rfl) ⟨1310882, by rfl⟩ : syracuseStep 1747843 = 2621765) B2621765
theorem B1747859 : Blo 1746574 1747859 := bstep (se 1 (by rfl) ⟨1310894, by rfl⟩ : syracuseStep 1747859 = 2621789) B2621789
theorem B1747875 : Blo 1746574 1747875 := bstep (se 1 (by rfl) ⟨1310906, by rfl⟩ : syracuseStep 1747875 = 2621813) B2621813
theorem B1747891 : Blo 1746574 1747891 := bstep (se 1 (by rfl) ⟨1310918, by rfl⟩ : syracuseStep 1747891 = 2621837) B2621837
theorem B1747907 : Blo 1746574 1747907 := bstep (se 1 (by rfl) ⟨1310930, by rfl⟩ : syracuseStep 1747907 = 2621861) B2621861
theorem B1747923 : Blo 1746574 1747923 := bstep (se 1 (by rfl) ⟨1310942, by rfl⟩ : syracuseStep 1747923 = 2621885) B2621885
theorem B1747939 : Blo 1746574 1747939 := bstep (se 1 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 1747939 = 2621909) B2621909
theorem B8399857 : Blo 1746574 8399857 := bstep (se 2 (by rfl) ⟨3149946, by rfl⟩ : syracuseStep 8399857 = 6299893) B6299893
theorem B1747955 : Blo 1746574 1747955 := bstep (se 1 (by rfl) ⟨1310966, by rfl⟩ : syracuseStep 1747955 = 2621933) B2621933
theorem B1747971 : Blo 1746574 1747971 := bstep (se 1 (by rfl) ⟨1310978, by rfl⟩ : syracuseStep 1747971 = 2621957) B2621957
theorem B1747987 : Blo 1746574 1747987 := bstep (se 1 (by rfl) ⟨1310990, by rfl⟩ : syracuseStep 1747987 = 2621981) B2621981
theorem B1748003 : Blo 1746574 1748003 := bstep (se 1 (by rfl) ⟨1311002, by rfl⟩ : syracuseStep 1748003 = 2622005) B2622005
theorem B1748019 : Blo 1746574 1748019 := bstep (se 1 (by rfl) ⟨1311014, by rfl⟩ : syracuseStep 1748019 = 2622029) B2622029
theorem B1748035 : Blo 1746574 1748035 := bstep (se 1 (by rfl) ⟨1311026, by rfl⟩ : syracuseStep 1748035 = 2622053) B2622053
theorem B6638669 : Blo 1746574 6638669 := bstep (se 3 (by rfl) ⟨1244750, by rfl⟩ : syracuseStep 6638669 = 2489501) B2489501
theorem B5901389 : Blo 1746574 5901389 := bstep (se 3 (by rfl) ⟨1106510, by rfl⟩ : syracuseStep 5901389 = 2213021) B2213021
theorem B1748051 : Blo 1746574 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B2362465 : Blo 1746574 2362465 := bstep (se 2 (by rfl) ⟨885924, by rfl⟩ : syracuseStep 2362465 = 1771849) B1771849
theorem B1748067 : Blo 1746574 1748067 := bstep (se 1 (by rfl) ⟨1311050, by rfl⟩ : syracuseStep 1748067 = 2622101) B2622101
theorem B8850545 : Blo 1746574 8850545 := bstep (se 2 (by rfl) ⟨3318954, by rfl⟩ : syracuseStep 8850545 = 6637909) B6637909
theorem B1748083 : Blo 1746574 1748083 := bstep (se 1 (by rfl) ⟨1311062, by rfl⟩ : syracuseStep 1748083 = 2622125) B2622125
theorem B3148931 : Blo 1746574 3148931 := bstep (se 1 (by rfl) ⟨2361698, by rfl⟩ : syracuseStep 3148931 = 4723397) B4723397
theorem B1748099 : Blo 1746574 1748099 := bstep (se 1 (by rfl) ⟨1311074, by rfl⟩ : syracuseStep 1748099 = 2622149) B2622149
theorem B1748115 : Blo 1746574 1748115 := bstep (se 1 (by rfl) ⟨1311086, by rfl⟩ : syracuseStep 1748115 = 2622173) B2622173
theorem B1748131 : Blo 1746574 1748131 := bstep (se 1 (by rfl) ⟨1311098, by rfl⟩ : syracuseStep 1748131 = 2622197) B2622197
theorem B2362547 : Blo 1746574 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B1748147 : Blo 1746574 1748147 := bstep (se 1 (by rfl) ⟨1311110, by rfl⟩ : syracuseStep 1748147 = 2622221) B2622221
theorem B1748163 : Blo 1746574 1748163 := bstep (se 1 (by rfl) ⟨1311122, by rfl⟩ : syracuseStep 1748163 = 2622245) B2622245
theorem B8842445 : Blo 1746574 8842445 := bstep (se 3 (by rfl) ⟨1657958, by rfl⟩ : syracuseStep 8842445 = 3315917) B3315917
theorem B3280081 : Blo 1746574 3280081 := bstep (se 2 (by rfl) ⟨1230030, by rfl⟩ : syracuseStep 3280081 = 2460061) B2460061
theorem B1748179 : Blo 1746574 1748179 := bstep (se 1 (by rfl) ⟨1311134, by rfl⟩ : syracuseStep 1748179 = 2622269) B2622269
theorem B1748195 : Blo 1746574 1748195 := bstep (se 1 (by rfl) ⟨1311146, by rfl⟩ : syracuseStep 1748195 = 2622293) B2622293
theorem B3730673 : Blo 1746574 3730673 := bstep (se 2 (by rfl) ⟨1399002, by rfl⟩ : syracuseStep 3730673 = 2798005) B2798005
theorem B1748211 : Blo 1746574 1748211 := bstep (se 1 (by rfl) ⟨1311158, by rfl⟩ : syracuseStep 1748211 = 2622317) B2622317
theorem B1748227 : Blo 1746574 1748227 := bstep (se 1 (by rfl) ⟨1311170, by rfl⟩ : syracuseStep 1748227 = 2622341) B2622341
theorem B1748243 : Blo 1746574 1748243 := bstep (se 1 (by rfl) ⟨1311182, by rfl⟩ : syracuseStep 1748243 = 2622365) B2622365
theorem B1748259 : Blo 1746574 1748259 := bstep (se 1 (by rfl) ⟨1311194, by rfl⟩ : syracuseStep 1748259 = 2622389) B2622389
theorem B7089457 : Blo 1746574 7089457 := bstep (se 2 (by rfl) ⟨2658546, by rfl⟩ : syracuseStep 7089457 = 5317093) B5317093
theorem B1748275 : Blo 1746574 1748275 := bstep (se 1 (by rfl) ⟨1311206, by rfl⟩ : syracuseStep 1748275 = 2622413) B2622413
theorem B1748291 : Blo 1746574 1748291 := bstep (se 1 (by rfl) ⟨1311218, by rfl⟩ : syracuseStep 1748291 = 2622437) B2622437
theorem B1748307 : Blo 1746574 1748307 := bstep (se 1 (by rfl) ⟨1311230, by rfl⟩ : syracuseStep 1748307 = 2622461) B2622461
theorem B1748323 : Blo 1746574 1748323 := bstep (se 1 (by rfl) ⟨1311242, by rfl⟩ : syracuseStep 1748323 = 2622485) B2622485
theorem B3362161 : Blo 1746574 3362161 := bstep (se 2 (by rfl) ⟨1260810, by rfl⟩ : syracuseStep 3362161 = 2521621) B2521621
theorem B1748339 : Blo 1746574 1748339 := bstep (se 1 (by rfl) ⟨1311254, by rfl⟩ : syracuseStep 1748339 = 2622509) B2622509
theorem B1748355 : Blo 1746574 1748355 := bstep (se 1 (by rfl) ⟨1311266, by rfl⟩ : syracuseStep 1748355 = 2622533) B2622533
theorem B1748371 : Blo 1746574 1748371 := bstep (se 1 (by rfl) ⟨1311278, by rfl⟩ : syracuseStep 1748371 = 2622557) B2622557
theorem B1748387 : Blo 1746574 1748387 := bstep (se 1 (by rfl) ⟨1311290, by rfl⟩ : syracuseStep 1748387 = 2622581) B2622581
theorem B1748403 : Blo 1746574 1748403 := bstep (se 1 (by rfl) ⟨1311302, by rfl⟩ : syracuseStep 1748403 = 2622605) B2622605
theorem B1748419 : Blo 1746574 1748419 := bstep (se 1 (by rfl) ⟨1311314, by rfl⟩ : syracuseStep 1748419 = 2622629) B2622629
theorem B1748435 : Blo 1746574 1748435 := bstep (se 1 (by rfl) ⟨1311326, by rfl⟩ : syracuseStep 1748435 = 2622653) B2622653
theorem B14167523 : Blo 1746574 14167523 := bstep (se 1 (by rfl) ⟨10625642, by rfl⟩ : syracuseStep 14167523 = 21251285) B21251285
theorem B1748451 : Blo 1746574 1748451 := bstep (se 1 (by rfl) ⟨1311338, by rfl⟩ : syracuseStep 1748451 = 2622677) B2622677
theorem B1748467 : Blo 1746574 1748467 := bstep (se 1 (by rfl) ⟨1311350, by rfl⟩ : syracuseStep 1748467 = 2622701) B2622701
theorem B1748483 : Blo 1746574 1748483 := bstep (se 1 (by rfl) ⟨1311362, by rfl⟩ : syracuseStep 1748483 = 2622725) B2622725
theorem B1748499 : Blo 1746574 1748499 := bstep (se 1 (by rfl) ⟨1311374, by rfl⟩ : syracuseStep 1748499 = 2622749) B2622749
theorem B1748515 : Blo 1746574 1748515 := bstep (se 1 (by rfl) ⟨1311386, by rfl⟩ : syracuseStep 1748515 = 2622773) B2622773
theorem B1748531 : Blo 1746574 1748531 := bstep (se 1 (by rfl) ⟨1311398, by rfl⟩ : syracuseStep 1748531 = 2622797) B2622797
theorem B1748547 : Blo 1746574 1748547 := bstep (se 1 (by rfl) ⟨1311410, by rfl⟩ : syracuseStep 1748547 = 2622821) B2622821
theorem B16797253 : Blo 1746574 16797253 := bstep (se 4 (by rfl) ⟨1574742, by rfl⟩ : syracuseStep 16797253 = 3149485) B3149485
theorem B1748563 : Blo 1746574 1748563 := bstep (se 1 (by rfl) ⟨1311422, by rfl⟩ : syracuseStep 1748563 = 2622845) B2622845
theorem B2363027 : Blo 1746574 2363027 := bstep (se 1 (by rfl) ⟨1772270, by rfl⟩ : syracuseStep 2363027 = 3544541) B3544541
theorem B4976291 : Blo 1746574 4976291 := bstep (se 1 (by rfl) ⟨3732218, by rfl⟩ : syracuseStep 4976291 = 7464437) B7464437
theorem B9949027 : Blo 1746574 9949027 := bstep (se 1 (by rfl) ⟨7461770, by rfl⟩ : syracuseStep 9949027 = 14923541) B14923541
theorem B5312557 : Blo 1746574 5312557 := bstep (se 3 (by rfl) ⟨996104, by rfl⟩ : syracuseStep 5312557 = 1992209) B1992209
theorem B3543107 : Blo 1746574 3543107 := bstep (se 1 (by rfl) ⟨2657330, by rfl⟩ : syracuseStep 3543107 = 5314661) B5314661
theorem B10629197 : Blo 1746574 10629197 := bstep (se 3 (by rfl) ⟨1992974, by rfl⟩ : syracuseStep 10629197 = 3985949) B3985949
theorem B17027171 : Blo 1746574 17027171 := bstep (se 1 (by rfl) ⟨12770378, by rfl⟩ : syracuseStep 17027171 = 25540757) B25540757
theorem B2797697 : Blo 1746574 2797697 := bstep (se 2 (by rfl) ⟨1049136, by rfl⟩ : syracuseStep 2797697 = 2098273) B2098273
theorem B2658577 : Blo 1746574 2658577 := bstep (se 2 (by rfl) ⟨996966, by rfl⟩ : syracuseStep 2658577 = 1993933) B1993933
theorem B9949553 : Blo 1746574 9949553 := bstep (se 2 (by rfl) ⟨3731082, by rfl⟩ : syracuseStep 9949553 = 7462165) B7462165
theorem B13267313 : Blo 1746574 13267313 := bstep (se 2 (by rfl) ⟨4975242, by rfl⟩ : syracuseStep 13267313 = 9950485) B9950485
theorem B3985777 : Blo 1746574 3985777 := bstep (se 2 (by rfl) ⟨1494666, by rfl⟩ : syracuseStep 3985777 = 2989333) B2989333
theorem B10629539 : Blo 1746574 10629539 := bstep (se 1 (by rfl) ⟨7972154, by rfl⟩ : syracuseStep 10629539 = 15944309) B15944309
theorem B2240947 : Blo 1746574 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B2798113 : Blo 1746574 2798113 := bstep (se 2 (by rfl) ⟨1049292, by rfl⟩ : syracuseStep 2798113 = 2098585) B2098585
theorem B8852003 : Blo 1746574 8852003 := bstep (se 1 (by rfl) ⟨6639002, by rfl⟩ : syracuseStep 8852003 = 13278005) B13278005
theorem B3543601 : Blo 1746574 3543601 := bstep (se 2 (by rfl) ⟨1328850, by rfl⟩ : syracuseStep 3543601 = 2657701) B2657701
theorem B10629731 : Blo 1746574 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B6632077 : Blo 1746574 6632077 := bstep (se 3 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 6632077 = 2487029) B2487029
theorem B5894801 : Blo 1746574 5894801 := bstep (se 2 (by rfl) ⟨2210550, by rfl⟩ : syracuseStep 5894801 = 4421101) B4421101
theorem B19903157 : Blo 1746574 19903157 := bstep (se 5 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 19903157 = 1865921) B1865921
theorem B11195171 : Blo 1746574 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B4977521 : Blo 1746574 4977521 := bstep (se 2 (by rfl) ⟨1866570, by rfl⟩ : syracuseStep 4977521 = 3733141) B3733141
theorem B3732355 : Blo 1746574 3732355 := bstep (se 1 (by rfl) ⟨2799266, by rfl⟩ : syracuseStep 3732355 = 5598533) B5598533
theorem B60502925 : Blo 1746574 60502925 := bstep (se 3 (by rfl) ⟨11344298, by rfl⟩ : syracuseStep 60502925 = 22688597) B22688597
theorem B5600173 : Blo 1746574 5600173 := bstep (se 3 (by rfl) ⟨1050032, by rfl⟩ : syracuseStep 5600173 = 2100065) B2100065
theorem B7468195 : Blo 1746574 7468195 := bstep (se 1 (by rfl) ⟨5601146, by rfl⟩ : syracuseStep 7468195 = 11202293) B11202293
theorem B5895341 : Blo 1746574 5895341 := bstep (se 3 (by rfl) ⟨1105376, by rfl⟩ : syracuseStep 5895341 = 2210753) B2210753
theorem B5600429 : Blo 1746574 5600429 := bstep (se 3 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 5600429 = 2100161) B2100161
theorem B5895395 : Blo 1746574 5895395 := bstep (se 1 (by rfl) ⟨4421546, by rfl⟩ : syracuseStep 5895395 = 8843093) B8843093
theorem B4199651 : Blo 1746574 4199651 := bstep (se 1 (by rfl) ⟨3149738, by rfl⟩ : syracuseStep 4199651 = 6299477) B6299477
theorem B3732817 : Blo 1746574 3732817 := bstep (se 2 (by rfl) ⟨1399806, by rfl⟩ : syracuseStep 3732817 = 2799613) B2799613
theorem B2487667 : Blo 1746574 2487667 := bstep (se 1 (by rfl) ⟨1865750, by rfl⟩ : syracuseStep 2487667 = 3731501) B3731501
theorem B5977475 : Blo 1746574 5977475 := bstep (se 1 (by rfl) ⟨4483106, by rfl⟩ : syracuseStep 5977475 = 8966213) B8966213
theorem B6632867 : Blo 1746574 6632867 := bstep (se 1 (by rfl) ⟨4974650, by rfl⟩ : syracuseStep 6632867 = 9949301) B9949301
theorem B2799011 : Blo 1746574 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B5895665 : Blo 1746574 5895665 := bstep (se 2 (by rfl) ⟨2210874, by rfl⟩ : syracuseStep 5895665 = 4421749) B4421749
theorem B1865315 : Blo 1746574 1865315 := bstep (se 1 (by rfl) ⟨1398986, by rfl⟩ : syracuseStep 1865315 = 2797973) B2797973
theorem B42014321 : Blo 1746574 42014321 := bstep (se 2 (by rfl) ⟨15755370, by rfl⟩ : syracuseStep 42014321 = 31510741) B31510741
theorem B2799235 : Blo 1746574 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B11343493 : Blo 1746574 11343493 := bstep (se 4 (by rfl) ⟨1063452, by rfl⟩ : syracuseStep 11343493 = 2126905) B2126905
theorem B3929795 : Blo 1746574 3929795 := bstep (se 1 (by rfl) ⟨2947346, by rfl⟩ : syracuseStep 3929795 = 5894693) B5894693
theorem B4724497 : Blo 1746574 4724497 := bstep (se 2 (by rfl) ⟨1771686, by rfl⟩ : syracuseStep 4724497 = 3543373) B3543373
theorem B9951011 : Blo 1746574 9951011 := bstep (se 1 (by rfl) ⟨7463258, by rfl⟩ : syracuseStep 9951011 = 14926517) B14926517
theorem B4421425 : Blo 1746574 4421425 := bstep (se 2 (by rfl) ⟨1658034, by rfl⟩ : syracuseStep 4421425 = 3316069) B3316069
theorem B3930065 : Blo 1746574 3930065 := bstep (se 2 (by rfl) ⟨1473774, by rfl⟩ : syracuseStep 3930065 = 2947549) B2947549
theorem B30250979 : Blo 1746574 30250979 := bstep (se 1 (by rfl) ⟨22688234, by rfl⟩ : syracuseStep 30250979 = 45376469) B45376469
theorem B3930083 : Blo 1746574 3930083 := bstep (se 1 (by rfl) ⟨2947562, by rfl⟩ : syracuseStep 3930083 = 5895125) B5895125
theorem B4200419 : Blo 1746574 4200419 := bstep (se 1 (by rfl) ⟨3150314, by rfl⟩ : syracuseStep 4200419 = 6300629) B6300629
theorem B7460849 : Blo 1746574 7460849 := bstep (se 2 (by rfl) ⟨2797818, by rfl⟩ : syracuseStep 7460849 = 5595637) B5595637
theorem B5896205 : Blo 1746574 5896205 := bstep (se 3 (by rfl) ⟨1105538, by rfl⟩ : syracuseStep 5896205 = 2211077) B2211077
theorem B6633521 : Blo 1746574 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B8845361 : Blo 1746574 8845361 := bstep (se 2 (by rfl) ⟨3317010, by rfl⟩ : syracuseStep 8845361 = 6634021) B6634021
theorem B4421699 : Blo 1746574 4421699 := bstep (se 1 (by rfl) ⟨3316274, by rfl⟩ : syracuseStep 4421699 = 6632549) B6632549
theorem B5896259 : Blo 1746574 5896259 := bstep (se 1 (by rfl) ⟨4422194, by rfl⟩ : syracuseStep 5896259 = 8844389) B8844389
theorem B3315811 : Blo 1746574 3315811 := bstep (se 1 (by rfl) ⟨2486858, by rfl⟩ : syracuseStep 3315811 = 4973717) B4973717
theorem B3930353 : Blo 1746574 3930353 := bstep (se 2 (by rfl) ⟨1473882, by rfl⟩ : syracuseStep 3930353 = 2947765) B2947765
theorem B3315971 : Blo 1746574 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B3930371 : Blo 1746574 3930371 := bstep (se 1 (by rfl) ⟨2947778, by rfl⟩ : syracuseStep 3930371 = 5895557) B5895557
theorem B4421891 : Blo 1746574 4421891 := bstep (se 1 (by rfl) ⟨3316418, by rfl⟩ : syracuseStep 4421891 = 6632837) B6632837
theorem B4978979 : Blo 1746574 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B10221893 : Blo 1746574 10221893 := bstep (se 4 (by rfl) ⟨958302, by rfl⟩ : syracuseStep 10221893 = 1916605) B1916605
theorem B5896529 : Blo 1746574 5896529 := bstep (se 2 (by rfl) ⟨2211198, by rfl⟩ : syracuseStep 5896529 = 4422397) B4422397
theorem B16791907 : Blo 1746574 16791907 := bstep (se 1 (by rfl) ⟨12593930, by rfl⟩ : syracuseStep 16791907 = 25187861) B25187861
theorem B3733859 : Blo 1746574 3733859 := bstep (se 1 (by rfl) ⟨2800394, by rfl⟩ : syracuseStep 3733859 = 5600789) B5600789
theorem B2947441 : Blo 1746574 2947441 := bstep (se 2 (by rfl) ⟨1105290, by rfl⟩ : syracuseStep 2947441 = 2210581) B2210581
theorem B2947475 : Blo 1746574 2947475 := bstep (se 1 (by rfl) ⟨2210606, by rfl⟩ : syracuseStep 2947475 = 4421213) B4421213
theorem B2488801 : Blo 1746574 2488801 := bstep (se 2 (by rfl) ⟨933300, by rfl⟩ : syracuseStep 2488801 = 1866601) B1866601
theorem B2619875 : Blo 1746574 2619875 := bstep (se 1 (by rfl) ⟨1964906, by rfl⟩ : syracuseStep 2619875 = 3929813) B3929813
theorem B2619905 : Blo 1746574 2619905 := bstep (se 2 (by rfl) ⟨982464, by rfl⟩ : syracuseStep 2619905 = 1964929) B1964929
theorem B3930641 : Blo 1746574 3930641 := bstep (se 2 (by rfl) ⟨1473990, by rfl⟩ : syracuseStep 3930641 = 2947981) B2947981
theorem B2619923 : Blo 1746574 2619923 := bstep (se 1 (by rfl) ⟨1964942, by rfl⟩ : syracuseStep 2619923 = 3929885) B3929885
theorem B2947603 : Blo 1746574 2947603 := bstep (se 1 (by rfl) ⟨2210702, by rfl⟩ : syracuseStep 2947603 = 4421405) B4421405
theorem B4200977 : Blo 1746574 4200977 := bstep (se 2 (by rfl) ⟨1575366, by rfl⟩ : syracuseStep 4200977 = 3150733) B3150733
theorem B3930659 : Blo 1746574 3930659 := bstep (se 1 (by rfl) ⟨2947994, by rfl⟩ : syracuseStep 3930659 = 5895989) B5895989
theorem B2619953 : Blo 1746574 2619953 := bstep (se 2 (by rfl) ⟨982482, by rfl⟩ : syracuseStep 2619953 = 1964965) B1964965
theorem B95648309 : Blo 1746574 95648309 := bstep (se 5 (by rfl) ⟨4483514, by rfl⟩ : syracuseStep 95648309 = 8967029) B8967029
theorem B2488897 : Blo 1746574 2488897 := bstep (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) B1866673
theorem B2619971 : Blo 1746574 2619971 := bstep (se 1 (by rfl) ⟨1964978, by rfl⟩ : syracuseStep 2619971 = 3929957) B3929957
theorem B2620001 : Blo 1746574 2620001 := bstep (se 2 (by rfl) ⟨982500, by rfl⟩ : syracuseStep 2620001 = 1965001) B1965001
theorem B2800241 : Blo 1746574 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B2620019 : Blo 1746574 2620019 := bstep (se 1 (by rfl) ⟨1965014, by rfl⟩ : syracuseStep 2620019 = 3930029) B3930029
theorem B2620049 : Blo 1746574 2620049 := bstep (se 2 (by rfl) ⟨982518, by rfl⟩ : syracuseStep 2620049 = 1965037) B1965037
theorem B2947745 : Blo 1746574 2947745 := bstep (se 2 (by rfl) ⟨1105404, by rfl⟩ : syracuseStep 2947745 = 2210809) B2210809
theorem B2620067 : Blo 1746574 2620067 := bstep (se 1 (by rfl) ⟨1965050, by rfl⟩ : syracuseStep 2620067 = 3930101) B3930101
theorem B2620097 : Blo 1746574 2620097 := bstep (se 2 (by rfl) ⟨982536, by rfl⟩ : syracuseStep 2620097 = 1965073) B1965073
theorem B2620115 : Blo 1746574 2620115 := bstep (se 1 (by rfl) ⟨1965086, by rfl⟩ : syracuseStep 2620115 = 3930173) B3930173
theorem B1866451 : Blo 1746574 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B2620145 : Blo 1746574 2620145 := bstep (se 2 (by rfl) ⟨982554, by rfl⟩ : syracuseStep 2620145 = 1965109) B1965109
theorem B2620163 : Blo 1746574 2620163 := bstep (se 1 (by rfl) ⟨1965122, by rfl⟩ : syracuseStep 2620163 = 3930245) B3930245
theorem B2620193 : Blo 1746574 2620193 := bstep (se 2 (by rfl) ⟨982572, by rfl⟩ : syracuseStep 2620193 = 1965145) B1965145
theorem B2947873 : Blo 1746574 2947873 := bstep (se 2 (by rfl) ⟨1105452, by rfl⟩ : syracuseStep 2947873 = 2210905) B2210905
theorem B3930929 : Blo 1746574 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B2800433 : Blo 1746574 2800433 := bstep (se 2 (by rfl) ⟨1050162, by rfl⟩ : syracuseStep 2800433 = 2100325) B2100325
theorem B2620211 : Blo 1746574 2620211 := bstep (se 1 (by rfl) ⟨1965158, by rfl⟩ : syracuseStep 2620211 = 3930317) B3930317
theorem B2947907 : Blo 1746574 2947907 := bstep (se 1 (by rfl) ⟨2210930, by rfl⟩ : syracuseStep 2947907 = 4421861) B4421861
theorem B3930947 : Blo 1746574 3930947 := bstep (se 1 (by rfl) ⟨2948210, by rfl⟩ : syracuseStep 3930947 = 5896421) B5896421
theorem B2620241 : Blo 1746574 2620241 := bstep (se 2 (by rfl) ⟨982590, by rfl⟩ : syracuseStep 2620241 = 1965181) B1965181
theorem B2620259 : Blo 1746574 2620259 := bstep (se 1 (by rfl) ⟨1965194, by rfl⟩ : syracuseStep 2620259 = 3930389) B3930389
theorem B3734371 : Blo 1746574 3734371 := bstep (se 1 (by rfl) ⟨2800778, by rfl⟩ : syracuseStep 3734371 = 5601557) B5601557
theorem B5897069 : Blo 1746574 5897069 := bstep (se 3 (by rfl) ⟨1105700, by rfl⟩ : syracuseStep 5897069 = 2211401) B2211401
theorem B2620289 : Blo 1746574 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1964947 : Blo 1746574 1964947 := bstep (se 1 (by rfl) ⟨1473710, by rfl⟩ : syracuseStep 1964947 = 2947421) B2947421
theorem B2620307 : Blo 1746574 2620307 := bstep (se 1 (by rfl) ⟨1965230, by rfl⟩ : syracuseStep 2620307 = 3930461) B3930461
theorem B5897123 : Blo 1746574 5897123 := bstep (se 1 (by rfl) ⟨4422842, by rfl⟩ : syracuseStep 5897123 = 8845685) B8845685
theorem B2620337 : Blo 1746574 2620337 := bstep (se 2 (by rfl) ⟨982626, by rfl⟩ : syracuseStep 2620337 = 1965253) B1965253
theorem B2620355 : Blo 1746574 2620355 := bstep (se 1 (by rfl) ⟨1965266, by rfl⟩ : syracuseStep 2620355 = 3930533) B3930533
theorem B2948035 : Blo 1746574 2948035 := bstep (se 1 (by rfl) ⟨2211026, by rfl⟩ : syracuseStep 2948035 = 4422053) B4422053
theorem B2620385 : Blo 1746574 2620385 := bstep (se 2 (by rfl) ⟨982644, by rfl⟩ : syracuseStep 2620385 = 1965289) B1965289
theorem B2620403 : Blo 1746574 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B2620433 : Blo 1746574 2620433 := bstep (se 2 (by rfl) ⟨982662, by rfl⟩ : syracuseStep 2620433 = 1965325) B1965325
theorem B1965091 : Blo 1746574 1965091 := bstep (se 1 (by rfl) ⟨1473818, by rfl⟩ : syracuseStep 1965091 = 2947637) B2947637
theorem B2620451 : Blo 1746574 2620451 := bstep (se 1 (by rfl) ⟨1965338, by rfl⟩ : syracuseStep 2620451 = 3930677) B3930677
theorem B2489393 : Blo 1746574 2489393 := bstep (se 2 (by rfl) ⟨933522, by rfl⟩ : syracuseStep 2489393 = 1867045) B1867045
theorem B2620481 : Blo 1746574 2620481 := bstep (se 2 (by rfl) ⟨982680, by rfl⟩ : syracuseStep 2620481 = 1965361) B1965361
theorem B22395973 : Blo 1746574 22395973 := bstep (se 4 (by rfl) ⟨2099622, by rfl⟩ : syracuseStep 22395973 = 4199245) B4199245
theorem B2948177 : Blo 1746574 2948177 := bstep (se 2 (by rfl) ⟨1105566, by rfl⟩ : syracuseStep 2948177 = 2211133) B2211133
theorem B3931217 : Blo 1746574 3931217 := bstep (se 2 (by rfl) ⟨1474206, by rfl⟩ : syracuseStep 3931217 = 2948413) B2948413
theorem B2620499 : Blo 1746574 2620499 := bstep (se 1 (by rfl) ⟨1965374, by rfl⟩ : syracuseStep 2620499 = 3930749) B3930749
theorem B2210915 : Blo 1746574 2210915 := bstep (se 1 (by rfl) ⟨1658186, by rfl⟩ : syracuseStep 2210915 = 3316373) B3316373
theorem B3931235 : Blo 1746574 3931235 := bstep (se 1 (by rfl) ⟨2948426, by rfl⟩ : syracuseStep 3931235 = 5896853) B5896853
theorem B2620529 : Blo 1746574 2620529 := bstep (se 2 (by rfl) ⟨982698, by rfl⟩ : syracuseStep 2620529 = 1965397) B1965397
theorem B2620547 : Blo 1746574 2620547 := bstep (se 1 (by rfl) ⟨1965410, by rfl⟩ : syracuseStep 2620547 = 3930821) B3930821
theorem B2620577 : Blo 1746574 2620577 := bstep (se 2 (by rfl) ⟨982716, by rfl⟩ : syracuseStep 2620577 = 1965433) B1965433
theorem B4422833 : Blo 1746574 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B1965235 : Blo 1746574 1965235 := bstep (se 1 (by rfl) ⟨1473926, by rfl⟩ : syracuseStep 1965235 = 2947853) B2947853
theorem B2620595 : Blo 1746574 2620595 := bstep (se 1 (by rfl) ⟨1965446, by rfl⟩ : syracuseStep 2620595 = 3930893) B3930893
theorem B5897393 : Blo 1746574 5897393 := bstep (se 2 (by rfl) ⟨2211522, by rfl⟩ : syracuseStep 5897393 = 4423045) B4423045
theorem B2620625 : Blo 1746574 2620625 := bstep (se 2 (by rfl) ⟨982734, by rfl⟩ : syracuseStep 2620625 = 1965469) B1965469
theorem B2948305 : Blo 1746574 2948305 := bstep (se 2 (by rfl) ⟨1105614, by rfl⟩ : syracuseStep 2948305 = 2211229) B2211229
theorem B2620643 : Blo 1746574 2620643 := bstep (se 1 (by rfl) ⟨1965482, by rfl⟩ : syracuseStep 2620643 = 3930965) B3930965
theorem B4422883 : Blo 1746574 4422883 := bstep (se 1 (by rfl) ⟨3317162, by rfl⟩ : syracuseStep 4422883 = 6634325) B6634325
theorem B2948339 : Blo 1746574 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B2620673 : Blo 1746574 2620673 := bstep (se 2 (by rfl) ⟨982752, by rfl⟩ : syracuseStep 2620673 = 1965505) B1965505
theorem B2620691 : Blo 1746574 2620691 := bstep (se 1 (by rfl) ⟨1965518, by rfl⟩ : syracuseStep 2620691 = 3931037) B3931037
theorem B2620721 : Blo 1746574 2620721 := bstep (se 2 (by rfl) ⟨982770, by rfl⟩ : syracuseStep 2620721 = 1965541) B1965541
theorem B3317041 : Blo 1746574 3317041 := bstep (se 2 (by rfl) ⟨1243890, by rfl⟩ : syracuseStep 3317041 = 2487781) B2487781
theorem B1965379 : Blo 1746574 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B2620739 : Blo 1746574 2620739 := bstep (se 1 (by rfl) ⟨1965554, by rfl⟩ : syracuseStep 2620739 = 3931109) B3931109
theorem B2620769 : Blo 1746574 2620769 := bstep (se 2 (by rfl) ⟨982788, by rfl⟩ : syracuseStep 2620769 = 1965577) B1965577
theorem B7970147 : Blo 1746574 7970147 := bstep (se 1 (by rfl) ⟨5977610, by rfl⟩ : syracuseStep 7970147 = 11955221) B11955221
theorem B3931505 : Blo 1746574 3931505 := bstep (se 2 (by rfl) ⟨1474314, by rfl⟩ : syracuseStep 3931505 = 2948629) B2948629
theorem B4423025 : Blo 1746574 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B2620787 : Blo 1746574 2620787 := bstep (se 1 (by rfl) ⟨1965590, by rfl⟩ : syracuseStep 2620787 = 3931181) B3931181
theorem B2948467 : Blo 1746574 2948467 := bstep (se 1 (by rfl) ⟨2211350, by rfl⟩ : syracuseStep 2948467 = 4422701) B4422701
theorem B3931523 : Blo 1746574 3931523 := bstep (se 1 (by rfl) ⟨2948642, by rfl⟩ : syracuseStep 3931523 = 5897285) B5897285
theorem B2620817 : Blo 1746574 2620817 := bstep (se 2 (by rfl) ⟨982806, by rfl⟩ : syracuseStep 2620817 = 1965613) B1965613
theorem B2620835 : Blo 1746574 2620835 := bstep (se 1 (by rfl) ⟨1965626, by rfl⟩ : syracuseStep 2620835 = 3931253) B3931253
theorem B2620865 : Blo 1746574 2620865 := bstep (se 2 (by rfl) ⟨982824, by rfl⟩ : syracuseStep 2620865 = 1965649) B1965649
theorem B1965523 : Blo 1746574 1965523 := bstep (se 1 (by rfl) ⟨1474142, by rfl⟩ : syracuseStep 1965523 = 2948285) B2948285
theorem B2620883 : Blo 1746574 2620883 := bstep (se 1 (by rfl) ⟨1965662, by rfl⟩ : syracuseStep 2620883 = 3931325) B3931325
theorem B6634979 : Blo 1746574 6634979 := bstep (se 1 (by rfl) ⟨4976234, by rfl⟩ : syracuseStep 6634979 = 9952469) B9952469
theorem B8846819 : Blo 1746574 8846819 := bstep (se 1 (by rfl) ⟨6635114, by rfl⟩ : syracuseStep 8846819 = 13270229) B13270229
theorem B2620913 : Blo 1746574 2620913 := bstep (se 2 (by rfl) ⟨982842, by rfl⟩ : syracuseStep 2620913 = 1965685) B1965685
theorem B6634993 : Blo 1746574 6634993 := bstep (se 2 (by rfl) ⟨2488122, by rfl⟩ : syracuseStep 6634993 = 4976245) B4976245
theorem B2948609 : Blo 1746574 2948609 := bstep (se 2 (by rfl) ⟨1105728, by rfl⟩ : syracuseStep 2948609 = 2211457) B2211457
theorem B2620931 : Blo 1746574 2620931 := bstep (se 1 (by rfl) ⟨1965698, by rfl⟩ : syracuseStep 2620931 = 3931397) B3931397
theorem B2620961 : Blo 1746574 2620961 := bstep (se 2 (by rfl) ⟨982860, by rfl⟩ : syracuseStep 2620961 = 1965721) B1965721
theorem B3071521 : Blo 1746574 3071521 := bstep (se 2 (by rfl) ⟨1151820, by rfl⟩ : syracuseStep 3071521 = 2303641) B2303641
theorem B2620979 : Blo 1746574 2620979 := bstep (se 1 (by rfl) ⟨1965734, by rfl⟩ : syracuseStep 2620979 = 3931469) B3931469
theorem B2621009 : Blo 1746574 2621009 := bstep (se 2 (by rfl) ⟨982878, by rfl⟩ : syracuseStep 2621009 = 1965757) B1965757
theorem B1965667 : Blo 1746574 1965667 := bstep (se 1 (by rfl) ⟨1474250, by rfl⟩ : syracuseStep 1965667 = 2948501) B2948501
theorem B2621027 : Blo 1746574 2621027 := bstep (se 1 (by rfl) ⟨1965770, by rfl⟩ : syracuseStep 2621027 = 3931541) B3931541
theorem B2621057 : Blo 1746574 2621057 := bstep (se 2 (by rfl) ⟨982896, by rfl⟩ : syracuseStep 2621057 = 1965793) B1965793
theorem B2948737 : Blo 1746574 2948737 := bstep (se 2 (by rfl) ⟨1105776, by rfl⟩ : syracuseStep 2948737 = 2211553) B2211553
theorem B9952901 : Blo 1746574 9952901 := bstep (se 4 (by rfl) ⟨933084, by rfl⟩ : syracuseStep 9952901 = 1866169) B1866169
theorem B10632845 : Blo 1746574 10632845 := bstep (se 3 (by rfl) ⟨1993658, by rfl⟩ : syracuseStep 10632845 = 3987317) B3987317
theorem B3931793 : Blo 1746574 3931793 := bstep (se 2 (by rfl) ⟨1474422, by rfl⟩ : syracuseStep 3931793 = 2948845) B2948845
theorem B2621075 : Blo 1746574 2621075 := bstep (se 1 (by rfl) ⟨1965806, by rfl⟩ : syracuseStep 2621075 = 3931613) B3931613
theorem B2948771 : Blo 1746574 2948771 := bstep (se 1 (by rfl) ⟨2211578, by rfl⟩ : syracuseStep 2948771 = 4423157) B4423157
theorem B3931811 : Blo 1746574 3931811 := bstep (se 1 (by rfl) ⟨2948858, by rfl⟩ : syracuseStep 3931811 = 5897717) B5897717
theorem B2621105 : Blo 1746574 2621105 := bstep (se 2 (by rfl) ⟨982914, by rfl⟩ : syracuseStep 2621105 = 1965829) B1965829
theorem B3784369 : Blo 1746574 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B2621123 : Blo 1746574 2621123 := bstep (se 1 (by rfl) ⟨1965842, by rfl⟩ : syracuseStep 2621123 = 3931685) B3931685
theorem B9445061 : Blo 1746574 9445061 := bstep (se 4 (by rfl) ⟨885474, by rfl⟩ : syracuseStep 9445061 = 1770949) B1770949
theorem B5897933 : Blo 1746574 5897933 := bstep (se 3 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 5897933 = 2211725) B2211725
theorem B2621153 : Blo 1746574 2621153 := bstep (se 2 (by rfl) ⟨982932, by rfl⟩ : syracuseStep 2621153 = 1965865) B1965865
theorem B1965811 : Blo 1746574 1965811 := bstep (se 1 (by rfl) ⟨1474358, by rfl⟩ : syracuseStep 1965811 = 2948717) B2948717
theorem B2621171 : Blo 1746574 2621171 := bstep (se 1 (by rfl) ⟨1965878, by rfl⟩ : syracuseStep 2621171 = 3931757) B3931757
theorem B5897987 : Blo 1746574 5897987 := bstep (se 1 (by rfl) ⟨4423490, by rfl⟩ : syracuseStep 5897987 = 8846981) B8846981
theorem B2621201 : Blo 1746574 2621201 := bstep (se 2 (by rfl) ⟨982950, by rfl⟩ : syracuseStep 2621201 = 1965901) B1965901
theorem B2211619 : Blo 1746574 2211619 := bstep (se 1 (by rfl) ⟨1658714, by rfl⟩ : syracuseStep 2211619 = 3317429) B3317429
theorem B2621219 : Blo 1746574 2621219 := bstep (se 1 (by rfl) ⟨1965914, by rfl⟩ : syracuseStep 2621219 = 3931829) B3931829
theorem B2948899 : Blo 1746574 2948899 := bstep (se 1 (by rfl) ⟨2211674, by rfl⟩ : syracuseStep 2948899 = 4423349) B4423349
theorem B7085873 : Blo 1746574 7085873 := bstep (se 2 (by rfl) ⟨2657202, by rfl⟩ : syracuseStep 7085873 = 5314405) B5314405
theorem B2621249 : Blo 1746574 2621249 := bstep (se 2 (by rfl) ⟨982968, by rfl⟩ : syracuseStep 2621249 = 1965937) B1965937
theorem B2522947 : Blo 1746574 2522947 := bstep (se 1 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 2522947 = 3784421) B3784421
theorem B17030981 : Blo 1746574 17030981 := bstep (se 4 (by rfl) ⟨1596654, by rfl⟩ : syracuseStep 17030981 = 3193309) B3193309
theorem B2621267 : Blo 1746574 2621267 := bstep (se 1 (by rfl) ⟨1965950, by rfl⟩ : syracuseStep 2621267 = 3931901) B3931901
theorem B2621297 : Blo 1746574 2621297 := bstep (se 2 (by rfl) ⟨982986, by rfl⟩ : syracuseStep 2621297 = 1965973) B1965973
theorem B2522993 : Blo 1746574 2522993 := bstep (se 2 (by rfl) ⟨946122, by rfl⟩ : syracuseStep 2522993 = 1892245) B1892245
theorem B1965955 : Blo 1746574 1965955 := bstep (se 1 (by rfl) ⟨1474466, by rfl⟩ : syracuseStep 1965955 = 2948933) B2948933
theorem B2211715 : Blo 1746574 2211715 := bstep (se 1 (by rfl) ⟨1658786, by rfl⟩ : syracuseStep 2211715 = 3317573) B3317573
theorem B2621315 : Blo 1746574 2621315 := bstep (se 1 (by rfl) ⟨1965986, by rfl⟩ : syracuseStep 2621315 = 3931973) B3931973
theorem B2621345 : Blo 1746574 2621345 := bstep (se 2 (by rfl) ⟨983004, by rfl⟩ : syracuseStep 2621345 = 1966009) B1966009
theorem B2949041 : Blo 1746574 2949041 := bstep (se 2 (by rfl) ⟨1105890, by rfl⟩ : syracuseStep 2949041 = 2211781) B2211781
theorem B3932081 : Blo 1746574 3932081 := bstep (se 2 (by rfl) ⟨1474530, by rfl⟩ : syracuseStep 3932081 = 2949061) B2949061
theorem B2621363 : Blo 1746574 2621363 := bstep (se 1 (by rfl) ⟨1966022, by rfl⟩ : syracuseStep 2621363 = 3932045) B3932045
theorem B3932099 : Blo 1746574 3932099 := bstep (se 1 (by rfl) ⟨2949074, by rfl⟩ : syracuseStep 3932099 = 5898149) B5898149
theorem B2621393 : Blo 1746574 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B2621411 : Blo 1746574 2621411 := bstep (se 1 (by rfl) ⟨1966058, by rfl⟩ : syracuseStep 2621411 = 3932117) B3932117
theorem B5677037 : Blo 1746574 5677037 := bstep (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) B2128889
theorem B3932171 : Blo 1746574 3932171 := bstep (se 1 (by rfl) ⟨2949128, by rfl⟩ : syracuseStep 3932171 = 5898257) B5898257
theorem B2621465 : Blo 1746574 2621465 := bstep (se 2 (by rfl) ⟨983049, by rfl⟩ : syracuseStep 2621465 = 1966099) B1966099
theorem B7086131 : Blo 1746574 7086131 := bstep (se 1 (by rfl) ⟨5314598, by rfl⟩ : syracuseStep 7086131 = 10629197) B10629197
theorem B1966135 : Blo 1746574 1966135 := bstep (se 1 (by rfl) ⟨1474601, by rfl⟩ : syracuseStep 1966135 = 2949203) B2949203
theorem B3932225 : Blo 1746574 3932225 := bstep (se 2 (by rfl) ⟨1474584, by rfl⟩ : syracuseStep 3932225 = 2949169) B2949169
theorem B2621579 : Blo 1746574 2621579 := bstep (se 1 (by rfl) ⟨1966184, by rfl⟩ : syracuseStep 2621579 = 3932369) B3932369
theorem B2621591 : Blo 1746574 2621591 := bstep (se 1 (by rfl) ⟨1966193, by rfl⟩ : syracuseStep 2621591 = 3932387) B3932387
theorem B5898419 : Blo 1746574 5898419 := bstep (se 1 (by rfl) ⟨4423814, by rfl⟩ : syracuseStep 5898419 = 8847629) B8847629
theorem B2621657 : Blo 1746574 2621657 := bstep (se 2 (by rfl) ⟨983121, by rfl⟩ : syracuseStep 2621657 = 1966243) B1966243
theorem B1966315 : Blo 1746574 1966315 := bstep (se 1 (by rfl) ⟨1474736, by rfl⟩ : syracuseStep 1966315 = 2949473) B2949473
theorem B7086359 : Blo 1746574 7086359 := bstep (se 1 (by rfl) ⟨5314769, by rfl⟩ : syracuseStep 7086359 = 10629539) B10629539
theorem B3932441 : Blo 1746574 3932441 := bstep (se 2 (by rfl) ⟨1474665, by rfl⟩ : syracuseStep 3932441 = 2949331) B2949331
theorem B5112115 : Blo 1746574 5112115 := bstep (se 1 (by rfl) ⟨3834086, by rfl⟩ : syracuseStep 5112115 = 7668173) B7668173
theorem B2621771 : Blo 1746574 2621771 := bstep (se 1 (by rfl) ⟨1966328, by rfl⟩ : syracuseStep 2621771 = 3932657) B3932657
theorem B2621783 : Blo 1746574 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B1966423 : Blo 1746574 1966423 := bstep (se 1 (by rfl) ⟨1474817, by rfl⟩ : syracuseStep 1966423 = 2949635) B2949635
theorem B2523479 : Blo 1746574 2523479 := bstep (se 1 (by rfl) ⟨1892609, by rfl⟩ : syracuseStep 2523479 = 3785219) B3785219
theorem B3932531 : Blo 1746574 3932531 := bstep (se 1 (by rfl) ⟨2949398, by rfl⟩ : syracuseStep 3932531 = 5898797) B5898797
theorem B3932567 : Blo 1746574 3932567 := bstep (se 1 (by rfl) ⟨2949425, by rfl⟩ : syracuseStep 3932567 = 5898851) B5898851
theorem B2949527 : Blo 1746574 2949527 := bstep (se 1 (by rfl) ⟨2212145, by rfl⟩ : syracuseStep 2949527 = 4424291) B4424291
theorem B2621849 : Blo 1746574 2621849 := bstep (se 2 (by rfl) ⟨983193, by rfl⟩ : syracuseStep 2621849 = 1966387) B1966387
theorem B5898689 : Blo 1746574 5898689 := bstep (se 2 (by rfl) ⟨2212008, by rfl⟩ : syracuseStep 5898689 = 4424017) B4424017
theorem B4424129 : Blo 1746574 4424129 := bstep (se 2 (by rfl) ⟨1659048, by rfl⟩ : syracuseStep 4424129 = 3318097) B3318097
theorem B22389209 : Blo 1746574 22389209 := bstep (se 2 (by rfl) ⟨8395953, by rfl⟩ : syracuseStep 22389209 = 16791907) B16791907
theorem B6300125 : Blo 1746574 6300125 := bstep (se 3 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 6300125 = 2362547) B2362547
theorem B12599813 : Blo 1746574 12599813 := bstep (se 4 (by rfl) ⟨1181232, by rfl⟩ : syracuseStep 12599813 = 2362465) B2362465
theorem B2621963 : Blo 1746574 2621963 := bstep (se 1 (by rfl) ⟨1966472, by rfl⟩ : syracuseStep 2621963 = 3932945) B3932945
theorem B2212363 : Blo 1746574 2212363 := bstep (se 1 (by rfl) ⟨1659272, by rfl⟩ : syracuseStep 2212363 = 3318545) B3318545
theorem B1966603 : Blo 1746574 1966603 := bstep (se 1 (by rfl) ⟨1474952, by rfl⟩ : syracuseStep 1966603 = 2949905) B2949905
theorem B7463447 : Blo 1746574 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B2949655 : Blo 1746574 2949655 := bstep (se 1 (by rfl) ⟨2212241, by rfl⟩ : syracuseStep 2949655 = 4424483) B4424483
theorem B2621975 : Blo 1746574 2621975 := bstep (se 1 (by rfl) ⟨1966481, by rfl⟩ : syracuseStep 2621975 = 3932963) B3932963
theorem B13263425 : Blo 1746574 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B3932747 : Blo 1746574 3932747 := bstep (se 1 (by rfl) ⟨2949560, by rfl⟩ : syracuseStep 3932747 = 5899121) B5899121
theorem B3318347 : Blo 1746574 3318347 := bstep (se 1 (by rfl) ⟨2488760, by rfl⟩ : syracuseStep 3318347 = 4977521) B4977521
theorem B2622041 : Blo 1746574 2622041 := bstep (se 2 (by rfl) ⟨983265, by rfl⟩ : syracuseStep 2622041 = 1966531) B1966531
theorem B1966711 : Blo 1746574 1966711 := bstep (se 1 (by rfl) ⟨1475033, by rfl⟩ : syracuseStep 1966711 = 2950067) B2950067
theorem B3932801 : Blo 1746574 3932801 := bstep (se 2 (by rfl) ⟨1474800, by rfl⟩ : syracuseStep 3932801 = 2949601) B2949601
theorem B3318401 : Blo 1746574 3318401 := bstep (se 2 (by rfl) ⟨1244400, by rfl⟩ : syracuseStep 3318401 = 2488801) B2488801
theorem B2622155 : Blo 1746574 2622155 := bstep (se 1 (by rfl) ⟨1966616, by rfl⟩ : syracuseStep 2622155 = 3933233) B3933233
theorem B2622167 : Blo 1746574 2622167 := bstep (se 1 (by rfl) ⟨1966625, by rfl⟩ : syracuseStep 2622167 = 3933251) B3933251
theorem B2622233 : Blo 1746574 2622233 := bstep (se 2 (by rfl) ⟨983337, by rfl⟩ : syracuseStep 2622233 = 1966675) B1966675
theorem B1966891 : Blo 1746574 1966891 := bstep (se 1 (by rfl) ⟨1475168, by rfl⟩ : syracuseStep 1966891 = 2950337) B2950337
theorem B3933017 : Blo 1746574 3933017 := bstep (se 2 (by rfl) ⟨1474881, by rfl⟩ : syracuseStep 3933017 = 2949763) B2949763
theorem B2622347 : Blo 1746574 2622347 := bstep (se 1 (by rfl) ⟨1966760, by rfl⟩ : syracuseStep 2622347 = 3933521) B3933521
theorem B2622359 : Blo 1746574 2622359 := bstep (se 1 (by rfl) ⟨1966769, by rfl⟩ : syracuseStep 2622359 = 3933539) B3933539
theorem B1966999 : Blo 1746574 1966999 := bstep (se 1 (by rfl) ⟨1475249, by rfl⟩ : syracuseStep 1966999 = 2950499) B2950499
theorem B3933107 : Blo 1746574 3933107 := bstep (se 1 (by rfl) ⟨2949830, by rfl⟩ : syracuseStep 3933107 = 5899661) B5899661
theorem B3933143 : Blo 1746574 3933143 := bstep (se 1 (by rfl) ⟨2949857, by rfl⟩ : syracuseStep 3933143 = 5899715) B5899715
theorem B4424665 : Blo 1746574 4424665 := bstep (se 2 (by rfl) ⟨1659249, by rfl⟩ : syracuseStep 4424665 = 3318499) B3318499
theorem B2622425 : Blo 1746574 2622425 := bstep (se 2 (by rfl) ⟨983409, by rfl⟩ : syracuseStep 2622425 = 1966819) B1966819
theorem B5899229 : Blo 1746574 5899229 := bstep (se 3 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 5899229 = 2212211) B2212211
theorem B28009547 : Blo 1746574 28009547 := bstep (se 1 (by rfl) ⟨21007160, by rfl⟩ : syracuseStep 28009547 = 42014321) B42014321
theorem B24249419 : Blo 1746574 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B2622539 : Blo 1746574 2622539 := bstep (se 1 (by rfl) ⟨1966904, by rfl⟩ : syracuseStep 2622539 = 3933809) B3933809
theorem B2622551 : Blo 1746574 2622551 := bstep (se 1 (by rfl) ⟨1966913, by rfl⟩ : syracuseStep 2622551 = 3933827) B3933827
theorem B5596253 : Blo 1746574 5596253 := bstep (se 3 (by rfl) ⟨1049297, by rfl⟩ : syracuseStep 5596253 = 2098595) B2098595
theorem B3933323 : Blo 1746574 3933323 := bstep (se 1 (by rfl) ⟨2949992, by rfl⟩ : syracuseStep 3933323 = 5899985) B5899985
theorem B2950283 : Blo 1746574 2950283 := bstep (se 1 (by rfl) ⟨2212712, by rfl⟩ : syracuseStep 2950283 = 4425425) B4425425
theorem B2622617 : Blo 1746574 2622617 := bstep (se 2 (by rfl) ⟨983481, by rfl⟩ : syracuseStep 2622617 = 1966963) B1966963
theorem B26911925 : Blo 1746574 26911925 := bstep (se 5 (by rfl) ⟨1261496, by rfl⟩ : syracuseStep 26911925 = 2522993) B2522993
theorem B3933377 : Blo 1746574 3933377 := bstep (se 2 (by rfl) ⟨1475016, by rfl⟩ : syracuseStep 3933377 = 2950033) B2950033
theorem B8848601 : Blo 1746574 8848601 := bstep (se 2 (by rfl) ⟨3318225, by rfl⟩ : syracuseStep 8848601 = 6636451) B6636451
theorem B1918199 : Blo 1746574 1918199 := bstep (se 1 (by rfl) ⟨1438649, by rfl⟩ : syracuseStep 1918199 = 2877299) B2877299
theorem B2950411 : Blo 1746574 2950411 := bstep (se 1 (by rfl) ⟨2212808, by rfl⟩ : syracuseStep 2950411 = 4425617) B4425617
theorem B2622731 : Blo 1746574 2622731 := bstep (se 1 (by rfl) ⟨1967048, by rfl⟩ : syracuseStep 2622731 = 3934097) B3934097
theorem B2622743 : Blo 1746574 2622743 := bstep (se 1 (by rfl) ⟨1967057, by rfl⟩ : syracuseStep 2622743 = 3934115) B3934115
theorem B11199809 : Blo 1746574 11199809 := bstep (se 2 (by rfl) ⟨4199928, by rfl⟩ : syracuseStep 11199809 = 8399857) B8399857
theorem B4973899 : Blo 1746574 4973899 := bstep (se 1 (by rfl) ⟨3730424, by rfl⟩ : syracuseStep 4973899 = 7460849) B7460849
theorem B2622809 : Blo 1746574 2622809 := bstep (se 2 (by rfl) ⟨983553, by rfl⟩ : syracuseStep 2622809 = 1967107) B1967107
theorem B3933593 : Blo 1746574 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B2950553 : Blo 1746574 2950553 := bstep (se 2 (by rfl) ⟨1106457, by rfl⟩ : syracuseStep 2950553 = 2212915) B2212915
theorem B29861297 : Blo 1746574 29861297 := bstep (se 2 (by rfl) ⟨11197986, by rfl⟩ : syracuseStep 29861297 = 22395973) B22395973
theorem B3933683 : Blo 1746574 3933683 := bstep (se 1 (by rfl) ⟨2950262, by rfl⟩ : syracuseStep 3933683 = 5900525) B5900525
theorem B2655755 : Blo 1746574 2655755 := bstep (se 1 (by rfl) ⟨1991816, by rfl⟩ : syracuseStep 2655755 = 3983633) B3983633
theorem B3933719 : Blo 1746574 3933719 := bstep (se 1 (by rfl) ⟨2950289, by rfl⟩ : syracuseStep 3933719 = 5900579) B5900579
theorem B3319319 : Blo 1746574 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2950681 : Blo 1746574 2950681 := bstep (se 2 (by rfl) ⟨1106505, by rfl⟩ : syracuseStep 2950681 = 2213011) B2213011
theorem B4974173 : Blo 1746574 4974173 := bstep (se 3 (by rfl) ⟨932657, by rfl⟩ : syracuseStep 4974173 = 1865315) B1865315
theorem B28345949 : Blo 1746574 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B1746583 : Blo 1746574 1746583 := bstep (se 1 (by rfl) ⟨1309937, by rfl⟩ : syracuseStep 1746583 = 2619875) B2619875
theorem B1746603 : Blo 1746574 1746603 := bstep (se 1 (by rfl) ⟨1309952, by rfl⟩ : syracuseStep 1746603 = 2619905) B2619905
theorem B1746615 : Blo 1746574 1746615 := bstep (se 1 (by rfl) ⟨1309961, by rfl⟩ : syracuseStep 1746615 = 2619923) B2619923
theorem B1746635 : Blo 1746574 1746635 := bstep (se 1 (by rfl) ⟨1309976, by rfl⟩ : syracuseStep 1746635 = 2619953) B2619953
theorem B3933899 : Blo 1746574 3933899 := bstep (se 1 (by rfl) ⟨2950424, by rfl⟩ : syracuseStep 3933899 = 5900849) B5900849
theorem B1746647 : Blo 1746574 1746647 := bstep (se 1 (by rfl) ⟨1309985, by rfl⟩ : syracuseStep 1746647 = 2619971) B2619971
theorem B6301405 : Blo 1746574 6301405 := bstep (se 3 (by rfl) ⟨1181513, by rfl⟩ : syracuseStep 6301405 = 2363027) B2363027
theorem B1746667 : Blo 1746574 1746667 := bstep (se 1 (by rfl) ⟨1310000, by rfl⟩ : syracuseStep 1746667 = 2620001) B2620001
theorem B1746679 : Blo 1746574 1746679 := bstep (se 1 (by rfl) ⟨1310009, by rfl⟩ : syracuseStep 1746679 = 2620019) B2620019
theorem B3933953 : Blo 1746574 3933953 := bstep (se 2 (by rfl) ⟨1475232, by rfl⟩ : syracuseStep 3933953 = 2950465) B2950465
theorem B1746699 : Blo 1746574 1746699 := bstep (se 1 (by rfl) ⟨1310024, by rfl⟩ : syracuseStep 1746699 = 2620049) B2620049
theorem B1746711 : Blo 1746574 1746711 := bstep (se 1 (by rfl) ⟨1310033, by rfl⟩ : syracuseStep 1746711 = 2620067) B2620067
theorem B1746731 : Blo 1746574 1746731 := bstep (se 1 (by rfl) ⟨1310048, by rfl⟩ : syracuseStep 1746731 = 2620097) B2620097
theorem B1746743 : Blo 1746574 1746743 := bstep (se 1 (by rfl) ⟨1310057, by rfl⟩ : syracuseStep 1746743 = 2620115) B2620115
theorem B4482881 : Blo 1746574 4482881 := bstep (se 2 (by rfl) ⟨1681080, by rfl⟩ : syracuseStep 4482881 = 3362161) B3362161
theorem B1746763 : Blo 1746574 1746763 := bstep (se 1 (by rfl) ⟨1310072, by rfl⟩ : syracuseStep 1746763 = 2620145) B2620145
theorem B1746775 : Blo 1746574 1746775 := bstep (se 1 (by rfl) ⟨1310081, by rfl⟩ : syracuseStep 1746775 = 2620163) B2620163
theorem B1746795 : Blo 1746574 1746795 := bstep (se 1 (by rfl) ⟨1310096, by rfl⟩ : syracuseStep 1746795 = 2620193) B2620193
theorem B1746807 : Blo 1746574 1746807 := bstep (se 1 (by rfl) ⟨1310105, by rfl⟩ : syracuseStep 1746807 = 2620211) B2620211
theorem B1746827 : Blo 1746574 1746827 := bstep (se 1 (by rfl) ⟨1310120, by rfl⟩ : syracuseStep 1746827 = 2620241) B2620241
theorem B1746839 : Blo 1746574 1746839 := bstep (se 1 (by rfl) ⟨1310129, by rfl⟩ : syracuseStep 1746839 = 2620259) B2620259
theorem B1746859 : Blo 1746574 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B1746871 : Blo 1746574 1746871 := bstep (se 1 (by rfl) ⟨1310153, by rfl⟩ : syracuseStep 1746871 = 2620307) B2620307
theorem B1746891 : Blo 1746574 1746891 := bstep (se 1 (by rfl) ⟨1310168, by rfl⟩ : syracuseStep 1746891 = 2620337) B2620337
theorem B1746903 : Blo 1746574 1746903 := bstep (se 1 (by rfl) ⟨1310177, by rfl⟩ : syracuseStep 1746903 = 2620355) B2620355
theorem B3934169 : Blo 1746574 3934169 := bstep (se 2 (by rfl) ⟨1475313, by rfl⟩ : syracuseStep 3934169 = 2950627) B2950627
theorem B1746923 : Blo 1746574 1746923 := bstep (se 1 (by rfl) ⟨1310192, by rfl⟩ : syracuseStep 1746923 = 2620385) B2620385
theorem B1746935 : Blo 1746574 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B1746955 : Blo 1746574 1746955 := bstep (se 1 (by rfl) ⟨1310216, by rfl⟩ : syracuseStep 1746955 = 2620433) B2620433
theorem B1746967 : Blo 1746574 1746967 := bstep (se 1 (by rfl) ⟨1310225, by rfl⟩ : syracuseStep 1746967 = 2620451) B2620451
theorem B1746987 : Blo 1746574 1746987 := bstep (se 1 (by rfl) ⟨1310240, by rfl⟩ : syracuseStep 1746987 = 2620481) B2620481
theorem B4425779 : Blo 1746574 4425779 := bstep (se 1 (by rfl) ⟨3319334, by rfl⟩ : syracuseStep 4425779 = 6638669) B6638669
theorem B3934259 : Blo 1746574 3934259 := bstep (se 1 (by rfl) ⟨2950694, by rfl⟩ : syracuseStep 3934259 = 5901389) B5901389
theorem B1746999 : Blo 1746574 1746999 := bstep (se 1 (by rfl) ⟨1310249, by rfl⟩ : syracuseStep 1746999 = 2620499) B2620499
theorem B1747019 : Blo 1746574 1747019 := bstep (se 1 (by rfl) ⟨1310264, by rfl⟩ : syracuseStep 1747019 = 2620529) B2620529
theorem B5900363 : Blo 1746574 5900363 := bstep (se 1 (by rfl) ⟨4425272, by rfl⟩ : syracuseStep 5900363 = 8850545) B8850545
theorem B1747031 : Blo 1746574 1747031 := bstep (se 1 (by rfl) ⟨1310273, by rfl⟩ : syracuseStep 1747031 = 2620547) B2620547
theorem B2099287 : Blo 1746574 2099287 := bstep (se 1 (by rfl) ⟨1574465, by rfl⟩ : syracuseStep 2099287 = 3148931) B3148931
theorem B1747051 : Blo 1746574 1747051 := bstep (se 1 (by rfl) ⟨1310288, by rfl⟩ : syracuseStep 1747051 = 2620577) B2620577
theorem B1747063 : Blo 1746574 1747063 := bstep (se 1 (by rfl) ⟨1310297, by rfl⟩ : syracuseStep 1747063 = 2620595) B2620595
theorem B1747083 : Blo 1746574 1747083 := bstep (se 1 (by rfl) ⟨1310312, by rfl⟩ : syracuseStep 1747083 = 2620625) B2620625
theorem B1747095 : Blo 1746574 1747095 := bstep (se 1 (by rfl) ⟨1310321, by rfl⟩ : syracuseStep 1747095 = 2620643) B2620643
theorem B1747115 : Blo 1746574 1747115 := bstep (se 1 (by rfl) ⟨1310336, by rfl⟩ : syracuseStep 1747115 = 2620673) B2620673
theorem B15124657 : Blo 1746574 15124657 := bstep (se 2 (by rfl) ⟨5671746, by rfl⟩ : syracuseStep 15124657 = 11343493) B11343493
theorem B1747127 : Blo 1746574 1747127 := bstep (se 1 (by rfl) ⟨1310345, by rfl⟩ : syracuseStep 1747127 = 2620691) B2620691
theorem B1747147 : Blo 1746574 1747147 := bstep (se 1 (by rfl) ⟨1310360, by rfl⟩ : syracuseStep 1747147 = 2620721) B2620721
theorem B1747159 : Blo 1746574 1747159 := bstep (se 1 (by rfl) ⟨1310369, by rfl⟩ : syracuseStep 1747159 = 2620739) B2620739
theorem B1747179 : Blo 1746574 1747179 := bstep (se 1 (by rfl) ⟨1310384, by rfl⟩ : syracuseStep 1747179 = 2620769) B2620769
theorem B1747191 : Blo 1746574 1747191 := bstep (se 1 (by rfl) ⟨1310393, by rfl⟩ : syracuseStep 1747191 = 2620787) B2620787
theorem B1747211 : Blo 1746574 1747211 := bstep (se 1 (by rfl) ⟨1310408, by rfl⟩ : syracuseStep 1747211 = 2620817) B2620817
theorem B1747223 : Blo 1746574 1747223 := bstep (se 1 (by rfl) ⟨1310417, by rfl⟩ : syracuseStep 1747223 = 2620835) B2620835
theorem B1747243 : Blo 1746574 1747243 := bstep (se 1 (by rfl) ⟨1310432, by rfl⟩ : syracuseStep 1747243 = 2620865) B2620865
theorem B1747255 : Blo 1746574 1747255 := bstep (se 1 (by rfl) ⟨1310441, by rfl⟩ : syracuseStep 1747255 = 2620883) B2620883
theorem B1747275 : Blo 1746574 1747275 := bstep (se 1 (by rfl) ⟨1310456, by rfl⟩ : syracuseStep 1747275 = 2620913) B2620913
theorem B1747287 : Blo 1746574 1747287 := bstep (se 1 (by rfl) ⟨1310465, by rfl⟩ : syracuseStep 1747287 = 2620931) B2620931
theorem B5900633 : Blo 1746574 5900633 := bstep (se 2 (by rfl) ⟨2212737, by rfl⟩ : syracuseStep 5900633 = 4425475) B4425475
theorem B4426073 : Blo 1746574 4426073 := bstep (se 2 (by rfl) ⟨1659777, by rfl⟩ : syracuseStep 4426073 = 3319555) B3319555
theorem B1747307 : Blo 1746574 1747307 := bstep (se 1 (by rfl) ⟨1310480, by rfl⟩ : syracuseStep 1747307 = 2620961) B2620961
theorem B1747319 : Blo 1746574 1747319 := bstep (se 1 (by rfl) ⟨1310489, by rfl⟩ : syracuseStep 1747319 = 2620979) B2620979
theorem B1747339 : Blo 1746574 1747339 := bstep (se 1 (by rfl) ⟨1310504, by rfl⟩ : syracuseStep 1747339 = 2621009) B2621009
theorem B1747351 : Blo 1746574 1747351 := bstep (se 1 (by rfl) ⟨1310513, by rfl⟩ : syracuseStep 1747351 = 2621027) B2621027
theorem B1747371 : Blo 1746574 1747371 := bstep (se 1 (by rfl) ⟨1310528, by rfl⟩ : syracuseStep 1747371 = 2621057) B2621057
theorem B7088563 : Blo 1746574 7088563 := bstep (se 1 (by rfl) ⟨5316422, by rfl⟩ : syracuseStep 7088563 = 10632845) B10632845
theorem B1747383 : Blo 1746574 1747383 := bstep (se 1 (by rfl) ⟨1310537, by rfl⟩ : syracuseStep 1747383 = 2621075) B2621075
theorem B1747403 : Blo 1746574 1747403 := bstep (se 1 (by rfl) ⟨1310552, by rfl⟩ : syracuseStep 1747403 = 2621105) B2621105
theorem B1747415 : Blo 1746574 1747415 := bstep (se 1 (by rfl) ⟨1310561, by rfl⟩ : syracuseStep 1747415 = 2621123) B2621123
theorem B13265369 : Blo 1746574 13265369 := bstep (se 2 (by rfl) ⟨4974513, by rfl⟩ : syracuseStep 13265369 = 9949027) B9949027
theorem B1747435 : Blo 1746574 1747435 := bstep (se 1 (by rfl) ⟨1310576, by rfl⟩ : syracuseStep 1747435 = 2621153) B2621153
theorem B1747447 : Blo 1746574 1747447 := bstep (se 1 (by rfl) ⟨1310585, by rfl⟩ : syracuseStep 1747447 = 2621171) B2621171
theorem B1747467 : Blo 1746574 1747467 := bstep (se 1 (by rfl) ⟨1310600, by rfl⟩ : syracuseStep 1747467 = 2621201) B2621201
theorem B1747479 : Blo 1746574 1747479 := bstep (se 1 (by rfl) ⟨1310609, by rfl⟩ : syracuseStep 1747479 = 2621219) B2621219
theorem B1747499 : Blo 1746574 1747499 := bstep (se 1 (by rfl) ⟨1310624, by rfl⟩ : syracuseStep 1747499 = 2621249) B2621249
theorem B1747511 : Blo 1746574 1747511 := bstep (se 1 (by rfl) ⟨1310633, by rfl⟩ : syracuseStep 1747511 = 2621267) B2621267
theorem B1747531 : Blo 1746574 1747531 := bstep (se 1 (by rfl) ⟨1310648, by rfl⟩ : syracuseStep 1747531 = 2621297) B2621297
theorem B1747543 : Blo 1746574 1747543 := bstep (se 1 (by rfl) ⟨1310657, by rfl⟩ : syracuseStep 1747543 = 2621315) B2621315
theorem B1747563 : Blo 1746574 1747563 := bstep (se 1 (by rfl) ⟨1310672, by rfl⟩ : syracuseStep 1747563 = 2621345) B2621345
theorem B1747575 : Blo 1746574 1747575 := bstep (se 1 (by rfl) ⟨1310681, by rfl⟩ : syracuseStep 1747575 = 2621363) B2621363
theorem B1747595 : Blo 1746574 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B1747607 : Blo 1746574 1747607 := bstep (se 1 (by rfl) ⟨1310705, by rfl⟩ : syracuseStep 1747607 = 2621411) B2621411
theorem B1747627 : Blo 1746574 1747627 := bstep (se 1 (by rfl) ⟨1310720, by rfl⟩ : syracuseStep 1747627 = 2621441) B2621441
theorem B1747639 : Blo 1746574 1747639 := bstep (se 1 (by rfl) ⟨1310729, by rfl⟩ : syracuseStep 1747639 = 2621459) B2621459
theorem B1747659 : Blo 1746574 1747659 := bstep (se 1 (by rfl) ⟨1310744, by rfl⟩ : syracuseStep 1747659 = 2621489) B2621489
theorem B1747671 : Blo 1746574 1747671 := bstep (se 1 (by rfl) ⟨1310753, by rfl⟩ : syracuseStep 1747671 = 2621507) B2621507
theorem B1747691 : Blo 1746574 1747691 := bstep (se 1 (by rfl) ⟨1310768, by rfl⟩ : syracuseStep 1747691 = 2621537) B2621537
theorem B1747703 : Blo 1746574 1747703 := bstep (se 1 (by rfl) ⟨1310777, by rfl⟩ : syracuseStep 1747703 = 2621555) B2621555
theorem B1747723 : Blo 1746574 1747723 := bstep (se 1 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 1747723 = 2621585) B2621585
theorem B1747735 : Blo 1746574 1747735 := bstep (se 1 (by rfl) ⟨1310801, by rfl⟩ : syracuseStep 1747735 = 2621603) B2621603
theorem B1747755 : Blo 1746574 1747755 := bstep (se 1 (by rfl) ⟨1310816, by rfl⟩ : syracuseStep 1747755 = 2621633) B2621633
theorem B8850221 : Blo 1746574 8850221 := bstep (se 3 (by rfl) ⟨1659416, by rfl⟩ : syracuseStep 8850221 = 3318833) B3318833
theorem B6638381 : Blo 1746574 6638381 := bstep (se 3 (by rfl) ⟨1244696, by rfl⟩ : syracuseStep 6638381 = 2489393) B2489393
theorem B1747767 : Blo 1746574 1747767 := bstep (se 1 (by rfl) ⟨1310825, by rfl⟩ : syracuseStep 1747767 = 2621651) B2621651
theorem B1747787 : Blo 1746574 1747787 := bstep (se 1 (by rfl) ⟨1310840, by rfl⟩ : syracuseStep 1747787 = 2621681) B2621681
theorem B1747799 : Blo 1746574 1747799 := bstep (se 1 (by rfl) ⟨1310849, by rfl⟩ : syracuseStep 1747799 = 2621699) B2621699
theorem B9448285 : Blo 1746574 9448285 := bstep (se 3 (by rfl) ⟨1771553, by rfl⟩ : syracuseStep 9448285 = 3543107) B3543107
theorem B1747819 : Blo 1746574 1747819 := bstep (se 1 (by rfl) ⟨1310864, by rfl⟩ : syracuseStep 1747819 = 2621729) B2621729
theorem B1747831 : Blo 1746574 1747831 := bstep (se 1 (by rfl) ⟨1310873, by rfl⟩ : syracuseStep 1747831 = 2621747) B2621747
theorem B1747851 : Blo 1746574 1747851 := bstep (se 1 (by rfl) ⟨1310888, by rfl⟩ : syracuseStep 1747851 = 2621777) B2621777
theorem B1747863 : Blo 1746574 1747863 := bstep (se 1 (by rfl) ⟨1310897, by rfl⟩ : syracuseStep 1747863 = 2621795) B2621795
theorem B1747883 : Blo 1746574 1747883 := bstep (se 1 (by rfl) ⟨1310912, by rfl⟩ : syracuseStep 1747883 = 2621825) B2621825
theorem B1747895 : Blo 1746574 1747895 := bstep (se 1 (by rfl) ⟨1310921, by rfl⟩ : syracuseStep 1747895 = 2621843) B2621843
theorem B1747915 : Blo 1746574 1747915 := bstep (se 1 (by rfl) ⟨1310936, by rfl⟩ : syracuseStep 1747915 = 2621873) B2621873
theorem B1747927 : Blo 1746574 1747927 := bstep (se 1 (by rfl) ⟨1310945, by rfl⟩ : syracuseStep 1747927 = 2621891) B2621891
theorem B1747947 : Blo 1746574 1747947 := bstep (se 1 (by rfl) ⟨1310960, by rfl⟩ : syracuseStep 1747947 = 2621921) B2621921
theorem B1747959 : Blo 1746574 1747959 := bstep (se 1 (by rfl) ⟨1310969, by rfl⟩ : syracuseStep 1747959 = 2621939) B2621939
theorem B13274117 : Blo 1746574 13274117 := bstep (se 4 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 13274117 = 2488897) B2488897
theorem B1747979 : Blo 1746574 1747979 := bstep (se 1 (by rfl) ⟨1310984, by rfl⟩ : syracuseStep 1747979 = 2621969) B2621969
theorem B1747991 : Blo 1746574 1747991 := bstep (se 1 (by rfl) ⟨1310993, by rfl⟩ : syracuseStep 1747991 = 2621987) B2621987
theorem B5901335 : Blo 1746574 5901335 := bstep (se 1 (by rfl) ⟨4426001, by rfl⟩ : syracuseStep 5901335 = 8852003) B8852003
theorem B1748011 : Blo 1746574 1748011 := bstep (se 1 (by rfl) ⟨1311008, by rfl⟩ : syracuseStep 1748011 = 2622017) B2622017
theorem B1748023 : Blo 1746574 1748023 := bstep (se 1 (by rfl) ⟨1311017, by rfl⟩ : syracuseStep 1748023 = 2622035) B2622035
theorem B1748043 : Blo 1746574 1748043 := bstep (se 1 (by rfl) ⟨1311032, by rfl⟩ : syracuseStep 1748043 = 2622065) B2622065
theorem B1748055 : Blo 1746574 1748055 := bstep (se 1 (by rfl) ⟨1311041, by rfl⟩ : syracuseStep 1748055 = 2622083) B2622083
theorem B1748075 : Blo 1746574 1748075 := bstep (se 1 (by rfl) ⟨1311056, by rfl⟩ : syracuseStep 1748075 = 2622113) B2622113
theorem B1748087 : Blo 1746574 1748087 := bstep (se 1 (by rfl) ⟨1311065, by rfl⟩ : syracuseStep 1748087 = 2622131) B2622131
theorem B1748107 : Blo 1746574 1748107 := bstep (se 1 (by rfl) ⟨1311080, by rfl⟩ : syracuseStep 1748107 = 2622161) B2622161
theorem B1748119 : Blo 1746574 1748119 := bstep (se 1 (by rfl) ⟨1311089, by rfl⟩ : syracuseStep 1748119 = 2622179) B2622179
theorem B1748139 : Blo 1746574 1748139 := bstep (se 1 (by rfl) ⟨1311104, by rfl⟩ : syracuseStep 1748139 = 2622209) B2622209
theorem B1748151 : Blo 1746574 1748151 := bstep (se 1 (by rfl) ⟨1311113, by rfl⟩ : syracuseStep 1748151 = 2622227) B2622227
theorem B1748171 : Blo 1746574 1748171 := bstep (se 1 (by rfl) ⟨1311128, by rfl⟩ : syracuseStep 1748171 = 2622257) B2622257
theorem B1748183 : Blo 1746574 1748183 := bstep (se 1 (by rfl) ⟨1311137, by rfl⟩ : syracuseStep 1748183 = 2622275) B2622275
theorem B1748203 : Blo 1746574 1748203 := bstep (se 1 (by rfl) ⟨1311152, by rfl⟩ : syracuseStep 1748203 = 2622305) B2622305
theorem B1748215 : Blo 1746574 1748215 := bstep (se 1 (by rfl) ⟨1311161, by rfl⟩ : syracuseStep 1748215 = 2622323) B2622323
theorem B1748235 : Blo 1746574 1748235 := bstep (se 1 (by rfl) ⟨1311176, by rfl⟩ : syracuseStep 1748235 = 2622353) B2622353
theorem B1748247 : Blo 1746574 1748247 := bstep (se 1 (by rfl) ⟨1311185, by rfl⟩ : syracuseStep 1748247 = 2622371) B2622371
theorem B1748267 : Blo 1746574 1748267 := bstep (se 1 (by rfl) ⟨1311200, by rfl⟩ : syracuseStep 1748267 = 2622401) B2622401
theorem B1748279 : Blo 1746574 1748279 := bstep (se 1 (by rfl) ⟨1311209, by rfl⟩ : syracuseStep 1748279 = 2622419) B2622419
theorem B1748299 : Blo 1746574 1748299 := bstep (se 1 (by rfl) ⟨1311224, by rfl⟩ : syracuseStep 1748299 = 2622449) B2622449
theorem B1748311 : Blo 1746574 1748311 := bstep (se 1 (by rfl) ⟨1311233, by rfl⟩ : syracuseStep 1748311 = 2622467) B2622467
theorem B1748331 : Blo 1746574 1748331 := bstep (se 1 (by rfl) ⟨1311248, by rfl⟩ : syracuseStep 1748331 = 2622497) B2622497
theorem B65514865 : Blo 1746574 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B1748343 : Blo 1746574 1748343 := bstep (se 1 (by rfl) ⟨1311257, by rfl⟩ : syracuseStep 1748343 = 2622515) B2622515
theorem B3730817 : Blo 1746574 3730817 := bstep (se 2 (by rfl) ⟨1399056, by rfl⟩ : syracuseStep 3730817 = 2798113) B2798113
theorem B1748363 : Blo 1746574 1748363 := bstep (se 1 (by rfl) ⟨1311272, by rfl⟩ : syracuseStep 1748363 = 2622545) B2622545
theorem B1748375 : Blo 1746574 1748375 := bstep (se 1 (by rfl) ⟨1311281, by rfl⟩ : syracuseStep 1748375 = 2622563) B2622563
theorem B1748395 : Blo 1746574 1748395 := bstep (se 1 (by rfl) ⟨1311296, by rfl⟩ : syracuseStep 1748395 = 2622593) B2622593
theorem B1748407 : Blo 1746574 1748407 := bstep (se 1 (by rfl) ⟨1311305, by rfl⟩ : syracuseStep 1748407 = 2622611) B2622611
theorem B3542465 : Blo 1746574 3542465 := bstep (se 2 (by rfl) ⟨1328424, by rfl⟩ : syracuseStep 3542465 = 2656849) B2656849
theorem B1748427 : Blo 1746574 1748427 := bstep (se 1 (by rfl) ⟨1311320, by rfl⟩ : syracuseStep 1748427 = 2622641) B2622641
theorem B1748439 : Blo 1746574 1748439 := bstep (se 1 (by rfl) ⟨1311329, by rfl⟩ : syracuseStep 1748439 = 2622659) B2622659
theorem B1748459 : Blo 1746574 1748459 := bstep (se 1 (by rfl) ⟨1311344, by rfl⟩ : syracuseStep 1748459 = 2622689) B2622689
theorem B1748471 : Blo 1746574 1748471 := bstep (se 1 (by rfl) ⟨1311353, by rfl⟩ : syracuseStep 1748471 = 2622707) B2622707
theorem B1748491 : Blo 1746574 1748491 := bstep (se 1 (by rfl) ⟨1311368, by rfl⟩ : syracuseStep 1748491 = 2622737) B2622737
theorem B8842769 : Blo 1746574 8842769 := bstep (se 2 (by rfl) ⟨3316038, by rfl⟩ : syracuseStep 8842769 = 6632077) B6632077
theorem B1748503 : Blo 1746574 1748503 := bstep (se 1 (by rfl) ⟨1311377, by rfl⟩ : syracuseStep 1748503 = 2622755) B2622755
theorem B1748523 : Blo 1746574 1748523 := bstep (se 1 (by rfl) ⟨1311392, by rfl⟩ : syracuseStep 1748523 = 2622785) B2622785
theorem B1748535 : Blo 1746574 1748535 := bstep (se 1 (by rfl) ⟨1311401, by rfl⟩ : syracuseStep 1748535 = 2622803) B2622803
theorem B1748555 : Blo 1746574 1748555 := bstep (se 1 (by rfl) ⟨1311416, by rfl⟩ : syracuseStep 1748555 = 2622833) B2622833
theorem B3984983 : Blo 1746574 3984983 := bstep (se 1 (by rfl) ⟨2988737, by rfl⟩ : syracuseStep 3984983 = 5977475) B5977475
theorem B1748567 : Blo 1746574 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B10628759 : Blo 1746574 10628759 := bstep (se 1 (by rfl) ⟨7971569, by rfl⟩ : syracuseStep 10628759 = 15943139) B15943139
theorem B8842931 : Blo 1746574 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B3731159 : Blo 1746574 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B4976473 : Blo 1746574 4976473 := bstep (se 2 (by rfl) ⟨1866177, by rfl⟩ : syracuseStep 4976473 = 3732355) B3732355
theorem B7466897 : Blo 1746574 7466897 := bstep (se 2 (by rfl) ⟨2800086, by rfl⟩ : syracuseStep 7466897 = 5600173) B5600173
theorem B3731467 : Blo 1746574 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B5386391 : Blo 1746574 5386391 := bstep (se 1 (by rfl) ⟨4039793, by rfl⟩ : syracuseStep 5386391 = 8079587) B8079587
theorem B9957593 : Blo 1746574 9957593 := bstep (se 2 (by rfl) ⟨3734097, by rfl⟩ : syracuseStep 9957593 = 7468195) B7468195
theorem B4977089 : Blo 1746574 4977089 := bstep (se 2 (by rfl) ⟨1866408, by rfl⟩ : syracuseStep 4977089 = 3732817) B3732817
theorem B28357361 : Blo 1746574 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B7467821 : Blo 1746574 7467821 := bstep (se 3 (by rfl) ⟨1400216, by rfl⟩ : syracuseStep 7467821 = 2800433) B2800433
theorem B5894963 : Blo 1746574 5894963 := bstep (se 1 (by rfl) ⟨4421222, by rfl⟩ : syracuseStep 5894963 = 8842445) B8842445
theorem B2487115 : Blo 1746574 2487115 := bstep (se 1 (by rfl) ⟨1865336, by rfl⟩ : syracuseStep 2487115 = 3730673) B3730673
theorem B3732313 : Blo 1746574 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B5313431 : Blo 1746574 5313431 := bstep (se 1 (by rfl) ⟨3985073, by rfl⟩ : syracuseStep 5313431 = 7970147) B7970147
theorem B16790489 : Blo 1746574 16790489 := bstep (se 2 (by rfl) ⟨6296433, by rfl⟩ : syracuseStep 16790489 = 12592867) B12592867
theorem B5895233 : Blo 1746574 5895233 := bstep (se 2 (by rfl) ⟨2210712, by rfl⟩ : syracuseStep 5895233 = 4421425) B4421425
theorem B3363929 : Blo 1746574 3363929 := bstep (se 2 (by rfl) ⟨1261473, by rfl⟩ : syracuseStep 3363929 = 2522947) B2522947
theorem B7083101 : Blo 1746574 7083101 := bstep (se 3 (by rfl) ⟨1328081, by rfl⟩ : syracuseStep 7083101 = 2656163) B2656163
theorem B4723805 : Blo 1746574 4723805 := bstep (se 3 (by rfl) ⟨885713, by rfl⟩ : syracuseStep 4723805 = 1771427) B1771427
theorem B6296707 : Blo 1746574 6296707 := bstep (se 1 (by rfl) ⟨4722530, by rfl⟩ : syracuseStep 6296707 = 9445061) B9445061
theorem B4723915 : Blo 1746574 4723915 := bstep (se 1 (by rfl) ⟨3542936, by rfl⟩ : syracuseStep 4723915 = 7085873) B7085873
theorem B13276547 : Blo 1746574 13276547 := bstep (se 1 (by rfl) ⟨9957410, by rfl⟩ : syracuseStep 13276547 = 19914821) B19914821
theorem B7083409 : Blo 1746574 7083409 := bstep (se 2 (by rfl) ⟨2656278, by rfl⟩ : syracuseStep 7083409 = 5312557) B5312557
theorem B11351447 : Blo 1746574 11351447 := bstep (se 1 (by rfl) ⟨8513585, by rfl⟩ : syracuseStep 11351447 = 17027171) B17027171
theorem B6297011 : Blo 1746574 6297011 := bstep (se 1 (by rfl) ⟨4722758, by rfl⟩ : syracuseStep 6297011 = 9445517) B9445517
theorem B4421081 : Blo 1746574 4421081 := bstep (se 2 (by rfl) ⟨1657905, by rfl⟩ : syracuseStep 4421081 = 3315811) B3315811
theorem B3986945 : Blo 1746574 3986945 := bstep (se 2 (by rfl) ⟨1495104, by rfl⟩ : syracuseStep 3986945 = 2990209) B2990209
theorem B9090625 : Blo 1746574 9090625 := bstep (se 2 (by rfl) ⟨3408984, by rfl⟩ : syracuseStep 9090625 = 6817969) B6817969
theorem B6633035 : Blo 1746574 6633035 := bstep (se 1 (by rfl) ⟨4974776, by rfl⟩ : syracuseStep 6633035 = 9949553) B9949553
theorem B8844875 : Blo 1746574 8844875 := bstep (se 1 (by rfl) ⟨6633656, by rfl⟩ : syracuseStep 8844875 = 13267313) B13267313
theorem B6633049 : Blo 1746574 6633049 := bstep (se 2 (by rfl) ⟨2487393, by rfl⟩ : syracuseStep 6633049 = 4974787) B4974787
theorem B5895773 : Blo 1746574 5895773 := bstep (se 3 (by rfl) ⟨1105457, by rfl⟩ : syracuseStep 5895773 = 2210915) B2210915
theorem B25204355 : Blo 1746574 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B7460525 : Blo 1746574 7460525 := bstep (se 3 (by rfl) ⟨1398848, by rfl⟩ : syracuseStep 7460525 = 2797697) B2797697
theorem B3544769 : Blo 1746574 3544769 := bstep (se 2 (by rfl) ⟨1329288, by rfl⟩ : syracuseStep 3544769 = 2658577) B2658577
theorem B3929867 : Blo 1746574 3929867 := bstep (se 1 (by rfl) ⟨2947400, by rfl⟩ : syracuseStep 3929867 = 5894801) B5894801
theorem B13268771 : Blo 1746574 13268771 := bstep (se 1 (by rfl) ⟨9951578, by rfl⟩ : syracuseStep 13268771 = 19903157) B19903157
theorem B3929921 : Blo 1746574 3929921 := bstep (se 2 (by rfl) ⟨1473720, by rfl⟩ : syracuseStep 3929921 = 2947441) B2947441
theorem B5314369 : Blo 1746574 5314369 := bstep (se 2 (by rfl) ⟨1992888, by rfl⟩ : syracuseStep 5314369 = 3985777) B3985777
theorem B2987929 : Blo 1746574 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B40335283 : Blo 1746574 40335283 := bstep (se 1 (by rfl) ⟨30251462, by rfl⟩ : syracuseStep 40335283 = 60502925) B60502925
theorem B3930137 : Blo 1746574 3930137 := bstep (se 2 (by rfl) ⟨1473801, by rfl⟩ : syracuseStep 3930137 = 2947603) B2947603
theorem B4724801 : Blo 1746574 4724801 := bstep (se 2 (by rfl) ⟨1771800, by rfl⟩ : syracuseStep 4724801 = 3543601) B3543601
theorem B3930227 : Blo 1746574 3930227 := bstep (se 1 (by rfl) ⟨2947670, by rfl⟩ : syracuseStep 3930227 = 5895341) B5895341
theorem B3733619 : Blo 1746574 3733619 := bstep (se 1 (by rfl) ⟨2800214, by rfl⟩ : syracuseStep 3733619 = 5600429) B5600429
theorem B9443459 : Blo 1746574 9443459 := bstep (se 1 (by rfl) ⟨7082594, by rfl⟩ : syracuseStep 9443459 = 14165189) B14165189
theorem B3930263 : Blo 1746574 3930263 := bstep (se 1 (by rfl) ⟨2947697, by rfl⟩ : syracuseStep 3930263 = 5895395) B5895395
theorem B2799767 : Blo 1746574 2799767 := bstep (se 1 (by rfl) ⟨2099825, by rfl⟩ : syracuseStep 2799767 = 4199651) B4199651
theorem B4421911 : Blo 1746574 4421911 := bstep (se 1 (by rfl) ⟨3316433, by rfl⟩ : syracuseStep 4421911 = 6632867) B6632867
theorem B1866007 : Blo 1746574 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B2488601 : Blo 1746574 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B14932289 : Blo 1746574 14932289 := bstep (se 2 (by rfl) ⟨5599608, by rfl⟩ : syracuseStep 14932289 = 11199217) B11199217
theorem B1890635 : Blo 1746574 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B3930443 : Blo 1746574 3930443 := bstep (se 1 (by rfl) ⟨2947832, by rfl⟩ : syracuseStep 3930443 = 5895665) B5895665
theorem B3930497 : Blo 1746574 3930497 := bstep (se 2 (by rfl) ⟨1473936, by rfl⟩ : syracuseStep 3930497 = 2947873) B2947873
theorem B2619863 : Blo 1746574 2619863 := bstep (se 1 (by rfl) ⟨1964897, by rfl⟩ : syracuseStep 2619863 = 3929795) B3929795
theorem B4979161 : Blo 1746574 4979161 := bstep (se 2 (by rfl) ⟨1867185, by rfl⟩ : syracuseStep 4979161 = 3734371) B3734371
theorem B9951761 : Blo 1746574 9951761 := bstep (se 2 (by rfl) ⟨3731910, by rfl⟩ : syracuseStep 9951761 = 7463821) B7463821
theorem B6634007 : Blo 1746574 6634007 := bstep (se 1 (by rfl) ⟨4975505, by rfl⟩ : syracuseStep 6634007 = 9951011) B9951011
theorem B2619929 : Blo 1746574 2619929 := bstep (se 2 (by rfl) ⟨982473, by rfl⟩ : syracuseStep 2619929 = 1964947) B1964947
theorem B4725299 : Blo 1746574 4725299 := bstep (se 1 (by rfl) ⟨3543974, by rfl⟩ : syracuseStep 4725299 = 7087949) B7087949
theorem B8395339 : Blo 1746574 8395339 := bstep (se 1 (by rfl) ⟨6296504, by rfl⟩ : syracuseStep 8395339 = 12593009) B12593009
theorem B3930713 : Blo 1746574 3930713 := bstep (se 2 (by rfl) ⟨1474017, by rfl⟩ : syracuseStep 3930713 = 2948035) B2948035
theorem B2620043 : Blo 1746574 2620043 := bstep (se 1 (by rfl) ⟨1965032, by rfl⟩ : syracuseStep 2620043 = 3930065) B3930065
theorem B20167319 : Blo 1746574 20167319 := bstep (se 1 (by rfl) ⟨15125489, by rfl⟩ : syracuseStep 20167319 = 30250979) B30250979
theorem B2620055 : Blo 1746574 2620055 := bstep (se 1 (by rfl) ⟨1965041, by rfl⟩ : syracuseStep 2620055 = 3930083) B3930083
theorem B8395415 : Blo 1746574 8395415 := bstep (se 1 (by rfl) ⟨6296561, by rfl⟩ : syracuseStep 8395415 = 12593123) B12593123
theorem B2800279 : Blo 1746574 2800279 := bstep (se 1 (by rfl) ⟨2100209, by rfl⟩ : syracuseStep 2800279 = 4200419) B4200419
theorem B3316403 : Blo 1746574 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B3930803 : Blo 1746574 3930803 := bstep (se 1 (by rfl) ⟨2948102, by rfl⟩ : syracuseStep 3930803 = 5896205) B5896205
theorem B4422347 : Blo 1746574 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B5896907 : Blo 1746574 5896907 := bstep (se 1 (by rfl) ⟨4422680, by rfl⟩ : syracuseStep 5896907 = 8845361) B8845361
theorem B2947799 : Blo 1746574 2947799 := bstep (se 1 (by rfl) ⟨2210849, by rfl⟩ : syracuseStep 2947799 = 4421699) B4421699
theorem B3930839 : Blo 1746574 3930839 := bstep (se 1 (by rfl) ⟨2948129, by rfl⟩ : syracuseStep 3930839 = 5896259) B5896259
theorem B2620121 : Blo 1746574 2620121 := bstep (se 2 (by rfl) ⟨982545, by rfl⟩ : syracuseStep 2620121 = 1965091) B1965091
theorem B25197317 : Blo 1746574 25197317 := bstep (se 4 (by rfl) ⟨2362248, by rfl⟩ : syracuseStep 25197317 = 4724497) B4724497
theorem B67197761 : Blo 1746574 67197761 := bstep (se 2 (by rfl) ⟨25199160, by rfl⟩ : syracuseStep 67197761 = 50398321) B50398321
theorem B2620235 : Blo 1746574 2620235 := bstep (se 1 (by rfl) ⟨1965176, by rfl⟩ : syracuseStep 2620235 = 3930353) B3930353
theorem B3316555 : Blo 1746574 3316555 := bstep (se 1 (by rfl) ⟨2487416, by rfl⟩ : syracuseStep 3316555 = 4974833) B4974833
theorem B2210647 : Blo 1746574 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B2620247 : Blo 1746574 2620247 := bstep (se 1 (by rfl) ⟨1965185, by rfl⟩ : syracuseStep 2620247 = 3930371) B3930371
theorem B2947927 : Blo 1746574 2947927 := bstep (se 1 (by rfl) ⟨2210945, by rfl⟩ : syracuseStep 2947927 = 4421891) B4421891
theorem B6814595 : Blo 1746574 6814595 := bstep (se 1 (by rfl) ⟨5110946, by rfl⟩ : syracuseStep 6814595 = 10221893) B10221893
theorem B3931019 : Blo 1746574 3931019 := bstep (se 1 (by rfl) ⟨2948264, by rfl⟩ : syracuseStep 3931019 = 5896529) B5896529
theorem B2489239 : Blo 1746574 2489239 := bstep (se 1 (by rfl) ⟨1866929, by rfl⟩ : syracuseStep 2489239 = 3733859) B3733859
theorem B2620313 : Blo 1746574 2620313 := bstep (se 2 (by rfl) ⟨982617, by rfl⟩ : syracuseStep 2620313 = 1965235) B1965235
theorem B1964983 : Blo 1746574 1964983 := bstep (se 1 (by rfl) ⟨1473737, by rfl⟩ : syracuseStep 1964983 = 2947475) B2947475
theorem B3931073 : Blo 1746574 3931073 := bstep (se 2 (by rfl) ⟨1474152, by rfl⟩ : syracuseStep 3931073 = 2948305) B2948305
theorem B4373441 : Blo 1746574 4373441 := bstep (se 2 (by rfl) ⟨1640040, by rfl⟩ : syracuseStep 4373441 = 3280081) B3280081
theorem B5897177 : Blo 1746574 5897177 := bstep (se 2 (by rfl) ⟨2211441, by rfl⟩ : syracuseStep 5897177 = 4422883) B4422883
theorem B9952217 : Blo 1746574 9952217 := bstep (se 2 (by rfl) ⟨3732081, by rfl⟩ : syracuseStep 9952217 = 7464163) B7464163
theorem B2620427 : Blo 1746574 2620427 := bstep (se 1 (by rfl) ⟨1965320, by rfl⟩ : syracuseStep 2620427 = 3930641) B3930641
theorem B2800651 : Blo 1746574 2800651 := bstep (se 1 (by rfl) ⟨2100488, by rfl⟩ : syracuseStep 2800651 = 4200977) B4200977
theorem B2620439 : Blo 1746574 2620439 := bstep (se 1 (by rfl) ⟨1965329, by rfl⟩ : syracuseStep 2620439 = 3930659) B3930659
theorem B63765539 : Blo 1746574 63765539 := bstep (se 1 (by rfl) ⟨47824154, by rfl⟩ : syracuseStep 63765539 = 95648309) B95648309
theorem B4422721 : Blo 1746574 4422721 := bstep (se 2 (by rfl) ⟨1658520, by rfl⟩ : syracuseStep 4422721 = 3317041) B3317041
theorem B9452609 : Blo 1746574 9452609 := bstep (se 2 (by rfl) ⟨3544728, by rfl⟩ : syracuseStep 9452609 = 7089457) B7089457
theorem B1866827 : Blo 1746574 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B2620505 : Blo 1746574 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B1965163 : Blo 1746574 1965163 := bstep (se 1 (by rfl) ⟨1473872, by rfl⟩ : syracuseStep 1965163 = 2947745) B2947745
theorem B3316889 : Blo 1746574 3316889 := bstep (se 2 (by rfl) ⟨1243833, by rfl⟩ : syracuseStep 3316889 = 2487667) B2487667
theorem B3931289 : Blo 1746574 3931289 := bstep (se 2 (by rfl) ⟨1474233, by rfl⟩ : syracuseStep 3931289 = 2948467) B2948467
theorem B2620619 : Blo 1746574 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B1965271 : Blo 1746574 1965271 := bstep (se 1 (by rfl) ⟨1473953, by rfl⟩ : syracuseStep 1965271 = 2947907) B2947907
theorem B2620631 : Blo 1746574 2620631 := bstep (se 1 (by rfl) ⟨1965473, by rfl⟩ : syracuseStep 2620631 = 3930947) B3930947
theorem B3931379 : Blo 1746574 3931379 := bstep (se 1 (by rfl) ⟨2948534, by rfl⟩ : syracuseStep 3931379 = 5897069) B5897069
theorem B3931415 : Blo 1746574 3931415 := bstep (se 1 (by rfl) ⟨2948561, by rfl⟩ : syracuseStep 3931415 = 5897123) B5897123
theorem B2620697 : Blo 1746574 2620697 := bstep (se 2 (by rfl) ⟨982761, by rfl⟩ : syracuseStep 2620697 = 1965523) B1965523
theorem B8846657 : Blo 1746574 8846657 := bstep (se 2 (by rfl) ⟨3317496, by rfl⟩ : syracuseStep 8846657 = 6634993) B6634993
theorem B4095361 : Blo 1746574 4095361 := bstep (se 2 (by rfl) ⟨1535760, by rfl⟩ : syracuseStep 4095361 = 3071521) B3071521
theorem B1965451 : Blo 1746574 1965451 := bstep (se 1 (by rfl) ⟨1474088, by rfl⟩ : syracuseStep 1965451 = 2948177) B2948177
theorem B2620811 : Blo 1746574 2620811 := bstep (se 1 (by rfl) ⟨1965608, by rfl⟩ : syracuseStep 2620811 = 3931217) B3931217
theorem B2620823 : Blo 1746574 2620823 := bstep (se 1 (by rfl) ⟨1965617, by rfl⟩ : syracuseStep 2620823 = 3931235) B3931235
theorem B22396337 : Blo 1746574 22396337 := bstep (se 2 (by rfl) ⟨8398626, by rfl⟩ : syracuseStep 22396337 = 16797253) B16797253
theorem B2948555 : Blo 1746574 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B3931595 : Blo 1746574 3931595 := bstep (se 1 (by rfl) ⟨2948696, by rfl⟩ : syracuseStep 3931595 = 5897393) B5897393
theorem B2620889 : Blo 1746574 2620889 := bstep (se 2 (by rfl) ⟨982833, by rfl⟩ : syracuseStep 2620889 = 1965667) B1965667
theorem B1965559 : Blo 1746574 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B3931649 : Blo 1746574 3931649 := bstep (se 2 (by rfl) ⟨1474368, by rfl⟩ : syracuseStep 3931649 = 2948737) B2948737
theorem B5045825 : Blo 1746574 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B2621003 : Blo 1746574 2621003 := bstep (se 1 (by rfl) ⟨1965752, by rfl⟩ : syracuseStep 2621003 = 3931505) B3931505
theorem B2948683 : Blo 1746574 2948683 := bstep (se 1 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 2948683 = 4423025) B4423025
theorem B2621015 : Blo 1746574 2621015 := bstep (se 1 (by rfl) ⟨1965761, by rfl⟩ : syracuseStep 2621015 = 3931523) B3931523
theorem B7462489 : Blo 1746574 7462489 := bstep (se 2 (by rfl) ⟨2798433, by rfl⟩ : syracuseStep 7462489 = 5596867) B5596867
theorem B9445015 : Blo 1746574 9445015 := bstep (se 1 (by rfl) ⟨7083761, by rfl⟩ : syracuseStep 9445015 = 14167523) B14167523
theorem B4423319 : Blo 1746574 4423319 := bstep (se 1 (by rfl) ⟨3317489, by rfl⟩ : syracuseStep 4423319 = 6634979) B6634979
theorem B2621081 : Blo 1746574 2621081 := bstep (se 2 (by rfl) ⟨982905, by rfl⟩ : syracuseStep 2621081 = 1965811) B1965811
theorem B5897879 : Blo 1746574 5897879 := bstep (se 1 (by rfl) ⟨4423409, by rfl⟩ : syracuseStep 5897879 = 8846819) B8846819
theorem B1965739 : Blo 1746574 1965739 := bstep (se 1 (by rfl) ⟨1474304, by rfl⟩ : syracuseStep 1965739 = 2948609) B2948609
theorem B2948825 : Blo 1746574 2948825 := bstep (se 2 (by rfl) ⟨1105809, by rfl⟩ : syracuseStep 2948825 = 2211619) B2211619
theorem B3931865 : Blo 1746574 3931865 := bstep (se 2 (by rfl) ⟨1474449, by rfl⟩ : syracuseStep 3931865 = 2948899) B2948899
theorem B6635267 : Blo 1746574 6635267 := bstep (se 1 (by rfl) ⟨4976450, by rfl⟩ : syracuseStep 6635267 = 9952901) B9952901
theorem B2621195 : Blo 1746574 2621195 := bstep (se 1 (by rfl) ⟨1965896, by rfl⟩ : syracuseStep 2621195 = 3931793) B3931793
theorem B1965847 : Blo 1746574 1965847 := bstep (se 1 (by rfl) ⟨1474385, by rfl⟩ : syracuseStep 1965847 = 2948771) B2948771
theorem B2621207 : Blo 1746574 2621207 := bstep (se 1 (by rfl) ⟨1965905, by rfl⟩ : syracuseStep 2621207 = 3931811) B3931811
theorem B3317527 : Blo 1746574 3317527 := bstep (se 1 (by rfl) ⟨2488145, by rfl⟩ : syracuseStep 3317527 = 4976291) B4976291
theorem B3931955 : Blo 1746574 3931955 := bstep (se 1 (by rfl) ⟨2948966, by rfl⟩ : syracuseStep 3931955 = 5897933) B5897933
theorem B3931991 : Blo 1746574 3931991 := bstep (se 1 (by rfl) ⟨2948993, by rfl⟩ : syracuseStep 3931991 = 5897987) B5897987
theorem B2621273 : Blo 1746574 2621273 := bstep (se 2 (by rfl) ⟨982977, by rfl⟩ : syracuseStep 2621273 = 1965955) B1965955
theorem B2948953 : Blo 1746574 2948953 := bstep (se 2 (by rfl) ⟨1105857, by rfl⟩ : syracuseStep 2948953 = 2211715) B2211715
theorem B11353987 : Blo 1746574 11353987 := bstep (se 1 (by rfl) ⟨8515490, by rfl⟩ : syracuseStep 11353987 = 17030981) B17030981
theorem B1966027 : Blo 1746574 1966027 := bstep (se 1 (by rfl) ⟨1474520, by rfl⟩ : syracuseStep 1966027 = 2949041) B2949041
theorem B2621387 : Blo 1746574 2621387 := bstep (se 1 (by rfl) ⟨1966040, by rfl⟩ : syracuseStep 2621387 = 3932081) B3932081
theorem B2621399 : Blo 1746574 2621399 := bstep (se 1 (by rfl) ⟨1966049, by rfl⟩ : syracuseStep 2621399 = 3932099) B3932099
theorem B3784691 : Blo 1746574 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B2621447 : Blo 1746574 2621447 := bstep (se 1 (by rfl) ⟨1966085, by rfl⟩ : syracuseStep 2621447 = 3932171) B3932171
theorem B2621483 : Blo 1746574 2621483 := bstep (se 1 (by rfl) ⟨1966112, by rfl⟩ : syracuseStep 2621483 = 3932225) B3932225
theorem B2621513 : Blo 1746574 2621513 := bstep (se 2 (by rfl) ⟨983067, by rfl⟩ : syracuseStep 2621513 = 1966135) B1966135
theorem B3932279 : Blo 1746574 3932279 := bstep (se 1 (by rfl) ⟨2949209, by rfl⟩ : syracuseStep 3932279 = 5898419) B5898419
theorem B2621627 : Blo 1746574 2621627 := bstep (se 1 (by rfl) ⟨1966220, by rfl⟩ : syracuseStep 2621627 = 3932441) B3932441
theorem B2621687 : Blo 1746574 2621687 := bstep (se 1 (by rfl) ⟨1966265, by rfl⟩ : syracuseStep 2621687 = 3932531) B3932531
theorem B2621711 : Blo 1746574 2621711 := bstep (se 1 (by rfl) ⟨1966283, by rfl⟩ : syracuseStep 2621711 = 3932567) B3932567
theorem B1966351 : Blo 1746574 1966351 := bstep (se 1 (by rfl) ⟨1474763, by rfl⟩ : syracuseStep 1966351 = 2949527) B2949527
theorem B3932459 : Blo 1746574 3932459 := bstep (se 1 (by rfl) ⟨2949344, by rfl⟩ : syracuseStep 3932459 = 5898689) B5898689
theorem B3318059 : Blo 1746574 3318059 := bstep (se 1 (by rfl) ⟨2488544, by rfl⟩ : syracuseStep 3318059 = 4977089) B4977089
theorem B2949419 : Blo 1746574 2949419 := bstep (se 1 (by rfl) ⟨2212064, by rfl⟩ : syracuseStep 2949419 = 4424129) B4424129
theorem B2621753 : Blo 1746574 2621753 := bstep (se 2 (by rfl) ⟨983157, by rfl⟩ : syracuseStep 2621753 = 1966315) B1966315
theorem B14926139 : Blo 1746574 14926139 := bstep (se 1 (by rfl) ⟨11194604, by rfl⟩ : syracuseStep 14926139 = 22389209) B22389209
theorem B2621831 : Blo 1746574 2621831 := bstep (se 1 (by rfl) ⟨1966373, by rfl⟩ : syracuseStep 2621831 = 3932747) B3932747
theorem B2621867 : Blo 1746574 2621867 := bstep (se 1 (by rfl) ⟨1966400, by rfl⟩ : syracuseStep 2621867 = 3932801) B3932801
theorem B2212267 : Blo 1746574 2212267 := bstep (se 1 (by rfl) ⟨1659200, by rfl⟩ : syracuseStep 2212267 = 3318401) B3318401
theorem B2621897 : Blo 1746574 2621897 := bstep (se 2 (by rfl) ⟨983211, by rfl⟩ : syracuseStep 2621897 = 1966423) B1966423
theorem B2622011 : Blo 1746574 2622011 := bstep (se 1 (by rfl) ⟨1966508, by rfl⟩ : syracuseStep 2622011 = 3933017) B3933017
theorem B2622071 : Blo 1746574 2622071 := bstep (se 1 (by rfl) ⟨1966553, by rfl⟩ : syracuseStep 2622071 = 3933107) B3933107
theorem B2622095 : Blo 1746574 2622095 := bstep (se 1 (by rfl) ⟨1966571, by rfl⟩ : syracuseStep 2622095 = 3933143) B3933143
theorem B3932819 : Blo 1746574 3932819 := bstep (se 1 (by rfl) ⟨2949614, by rfl⟩ : syracuseStep 3932819 = 5899229) B5899229
theorem B2949817 : Blo 1746574 2949817 := bstep (se 2 (by rfl) ⟨1106181, by rfl⟩ : syracuseStep 2949817 = 2212363) B2212363
theorem B2622137 : Blo 1746574 2622137 := bstep (se 2 (by rfl) ⟨983301, by rfl⟩ : syracuseStep 2622137 = 1966603) B1966603
theorem B3932873 : Blo 1746574 3932873 := bstep (se 2 (by rfl) ⟨1474827, by rfl⟩ : syracuseStep 3932873 = 2949655) B2949655
theorem B6636269 : Blo 1746574 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B2622215 : Blo 1746574 2622215 := bstep (se 1 (by rfl) ⟨1966661, by rfl⟩ : syracuseStep 2622215 = 3933323) B3933323
theorem B1966855 : Blo 1746574 1966855 := bstep (se 1 (by rfl) ⟨1475141, by rfl⟩ : syracuseStep 1966855 = 2950283) B2950283
theorem B50373413 : Blo 1746574 50373413 := bstep (se 4 (by rfl) ⟨4722507, by rfl⟩ : syracuseStep 50373413 = 9445015) B9445015
theorem B17941283 : Blo 1746574 17941283 := bstep (se 1 (by rfl) ⟨13455962, by rfl⟩ : syracuseStep 17941283 = 26911925) B26911925
theorem B2622251 : Blo 1746574 2622251 := bstep (se 1 (by rfl) ⟨1966688, by rfl⟩ : syracuseStep 2622251 = 3933377) B3933377
theorem B5899067 : Blo 1746574 5899067 := bstep (se 1 (by rfl) ⟨4424300, by rfl⟩ : syracuseStep 5899067 = 8848601) B8848601
theorem B2622281 : Blo 1746574 2622281 := bstep (se 2 (by rfl) ⟨983355, by rfl⟩ : syracuseStep 2622281 = 1966711) B1966711
theorem B2622395 : Blo 1746574 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B1967035 : Blo 1746574 1967035 := bstep (se 1 (by rfl) ⟨1475276, by rfl⟩ : syracuseStep 1967035 = 2950553) B2950553
theorem B19907531 : Blo 1746574 19907531 := bstep (se 1 (by rfl) ⟨14930648, by rfl⟩ : syracuseStep 19907531 = 29861297) B29861297
theorem B2622455 : Blo 1746574 2622455 := bstep (se 1 (by rfl) ⟨1966841, by rfl⟩ : syracuseStep 2622455 = 3933683) B3933683
theorem B1770503 : Blo 1746574 1770503 := bstep (se 1 (by rfl) ⟨1327877, by rfl⟩ : syracuseStep 1770503 = 2655755) B2655755
theorem B2622479 : Blo 1746574 2622479 := bstep (se 1 (by rfl) ⟨1966859, by rfl⟩ : syracuseStep 2622479 = 3933719) B3933719
theorem B2622521 : Blo 1746574 2622521 := bstep (se 2 (by rfl) ⟨983445, by rfl⟩ : syracuseStep 2622521 = 1966891) B1966891
theorem B16802903 : Blo 1746574 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B4973683 : Blo 1746574 4973683 := bstep (se 1 (by rfl) ⟨3730262, by rfl⟩ : syracuseStep 4973683 = 7460525) B7460525
theorem B2622599 : Blo 1746574 2622599 := bstep (se 1 (by rfl) ⟨1966949, by rfl⟩ : syracuseStep 2622599 = 3933899) B3933899
theorem B2622635 : Blo 1746574 2622635 := bstep (se 1 (by rfl) ⟨1966976, by rfl⟩ : syracuseStep 2622635 = 3933953) B3933953
theorem B3318985 : Blo 1746574 3318985 := bstep (se 2 (by rfl) ⟨1244619, by rfl⟩ : syracuseStep 3318985 = 2489239) B2489239
theorem B2622665 : Blo 1746574 2622665 := bstep (se 2 (by rfl) ⟨983499, by rfl⟩ : syracuseStep 2622665 = 1966999) B1966999
theorem B5899553 : Blo 1746574 5899553 := bstep (se 2 (by rfl) ⟨2212332, by rfl⟩ : syracuseStep 5899553 = 4424665) B4424665
theorem B2622779 : Blo 1746574 2622779 := bstep (se 1 (by rfl) ⟨1967084, by rfl⟩ : syracuseStep 2622779 = 3934169) B3934169
theorem B2950519 : Blo 1746574 2950519 := bstep (se 1 (by rfl) ⟨2212889, by rfl⟩ : syracuseStep 2950519 = 4425779) B4425779
theorem B2622839 : Blo 1746574 2622839 := bstep (se 1 (by rfl) ⟨1967129, by rfl⟩ : syracuseStep 2622839 = 3934259) B3934259
theorem B3933575 : Blo 1746574 3933575 := bstep (se 1 (by rfl) ⟨2950181, by rfl⟩ : syracuseStep 3933575 = 5900363) B5900363
theorem B8848925 : Blo 1746574 8848925 := bstep (se 3 (by rfl) ⟨1659173, by rfl⟩ : syracuseStep 8848925 = 3318347) B3318347
theorem B9954859 : Blo 1746574 9954859 := bstep (se 1 (by rfl) ⟨7466144, by rfl⟩ : syracuseStep 9954859 = 14932289) B14932289
theorem B3933755 : Blo 1746574 3933755 := bstep (se 1 (by rfl) ⟨2950316, by rfl⟩ : syracuseStep 3933755 = 5900633) B5900633
theorem B2950715 : Blo 1746574 2950715 := bstep (se 1 (by rfl) ⟨2213036, by rfl⟩ : syracuseStep 2950715 = 4426073) B4426073
theorem B27264613 : Blo 1746574 27264613 := bstep (se 4 (by rfl) ⟨2556057, by rfl⟩ : syracuseStep 27264613 = 5112115) B5112115
theorem B1746575 : Blo 1746574 1746575 := bstep (se 1 (by rfl) ⟨1309931, by rfl⟩ : syracuseStep 1746575 = 2619863) B2619863
theorem B3933881 : Blo 1746574 3933881 := bstep (se 2 (by rfl) ⟨1475205, by rfl⟩ : syracuseStep 3933881 = 2950411) B2950411
theorem B1746619 : Blo 1746574 1746619 := bstep (se 1 (by rfl) ⟨1309964, by rfl⟩ : syracuseStep 1746619 = 2619929) B2619929
theorem B1746695 : Blo 1746574 1746695 := bstep (se 1 (by rfl) ⟨1310021, by rfl⟩ : syracuseStep 1746695 = 2620043) B2620043
theorem B13444879 : Blo 1746574 13444879 := bstep (se 1 (by rfl) ⟨10083659, by rfl⟩ : syracuseStep 13444879 = 20167319) B20167319
theorem B1746703 : Blo 1746574 1746703 := bstep (se 1 (by rfl) ⟨1310027, by rfl⟩ : syracuseStep 1746703 = 2620055) B2620055
theorem B5596943 : Blo 1746574 5596943 := bstep (se 1 (by rfl) ⟨4197707, by rfl⟩ : syracuseStep 5596943 = 8395415) B8395415
theorem B1746747 : Blo 1746574 1746747 := bstep (se 1 (by rfl) ⟨1310060, by rfl⟩ : syracuseStep 1746747 = 2620121) B2620121
theorem B87353153 : Blo 1746574 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B5900147 : Blo 1746574 5900147 := bstep (se 1 (by rfl) ⟨4425110, by rfl⟩ : syracuseStep 5900147 = 8850221) B8850221
theorem B4425587 : Blo 1746574 4425587 := bstep (se 1 (by rfl) ⟨3319190, by rfl⟩ : syracuseStep 4425587 = 6638381) B6638381
theorem B1746823 : Blo 1746574 1746823 := bstep (se 1 (by rfl) ⟨1310117, by rfl⟩ : syracuseStep 1746823 = 2620235) B2620235
theorem B1746831 : Blo 1746574 1746831 := bstep (se 1 (by rfl) ⟨1310123, by rfl⟩ : syracuseStep 1746831 = 2620247) B2620247
theorem B1746875 : Blo 1746574 1746875 := bstep (se 1 (by rfl) ⟨1310156, by rfl⟩ : syracuseStep 1746875 = 2620313) B2620313
theorem B8849411 : Blo 1746574 8849411 := bstep (se 1 (by rfl) ⟨6637058, by rfl⟩ : syracuseStep 8849411 = 13274117) B13274117
theorem B1746951 : Blo 1746574 1746951 := bstep (se 1 (by rfl) ⟨1310213, by rfl⟩ : syracuseStep 1746951 = 2620427) B2620427
theorem B1746959 : Blo 1746574 1746959 := bstep (se 1 (by rfl) ⟨1310219, by rfl⟩ : syracuseStep 1746959 = 2620439) B2620439
theorem B3934223 : Blo 1746574 3934223 := bstep (se 1 (by rfl) ⟨2950667, by rfl⟩ : syracuseStep 3934223 = 5901335) B5901335
theorem B42510359 : Blo 1746574 42510359 := bstep (se 1 (by rfl) ⟨31882769, by rfl⟩ : syracuseStep 42510359 = 63765539) B63765539
theorem B3934241 : Blo 1746574 3934241 := bstep (se 2 (by rfl) ⟨1475340, by rfl⟩ : syracuseStep 3934241 = 2950681) B2950681
theorem B6301739 : Blo 1746574 6301739 := bstep (se 1 (by rfl) ⟨4726304, by rfl⟩ : syracuseStep 6301739 = 9452609) B9452609
theorem B1747003 : Blo 1746574 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1747079 : Blo 1746574 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1747087 : Blo 1746574 1747087 := bstep (se 1 (by rfl) ⟨1310315, by rfl⟩ : syracuseStep 1747087 = 2620631) B2620631
theorem B1747131 : Blo 1746574 1747131 := bstep (se 1 (by rfl) ⟨1310348, by rfl⟩ : syracuseStep 1747131 = 2620697) B2620697
theorem B1747207 : Blo 1746574 1747207 := bstep (se 1 (by rfl) ⟨1310405, by rfl⟩ : syracuseStep 1747207 = 2620811) B2620811
theorem B1747215 : Blo 1746574 1747215 := bstep (se 1 (by rfl) ⟨1310411, by rfl⟩ : syracuseStep 1747215 = 2620823) B2620823
theorem B2361643 : Blo 1746574 2361643 := bstep (se 1 (by rfl) ⟨1771232, by rfl⟩ : syracuseStep 2361643 = 3542465) B3542465
theorem B1747259 : Blo 1746574 1747259 := bstep (se 1 (by rfl) ⟨1310444, by rfl⟩ : syracuseStep 1747259 = 2620889) B2620889
theorem B18172253 : Blo 1746574 18172253 := bstep (se 3 (by rfl) ⟨3407297, by rfl⟩ : syracuseStep 18172253 = 6814595) B6814595
theorem B1747335 : Blo 1746574 1747335 := bstep (se 1 (by rfl) ⟨1310501, by rfl⟩ : syracuseStep 1747335 = 2621003) B2621003
theorem B2656655 : Blo 1746574 2656655 := bstep (se 1 (by rfl) ⟨1992491, by rfl⟩ : syracuseStep 2656655 = 3984983) B3984983
theorem B1747343 : Blo 1746574 1747343 := bstep (se 1 (by rfl) ⟨1310507, by rfl⟩ : syracuseStep 1747343 = 2621015) B2621015
theorem B1747387 : Blo 1746574 1747387 := bstep (se 1 (by rfl) ⟨1310540, by rfl⟩ : syracuseStep 1747387 = 2621081) B2621081
theorem B1747463 : Blo 1746574 1747463 := bstep (se 1 (by rfl) ⟨1310597, by rfl⟩ : syracuseStep 1747463 = 2621195) B2621195
theorem B1747471 : Blo 1746574 1747471 := bstep (se 1 (by rfl) ⟨1310603, by rfl⟩ : syracuseStep 1747471 = 2621207) B2621207
theorem B3983905 : Blo 1746574 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B1747515 : Blo 1746574 1747515 := bstep (se 1 (by rfl) ⟨1310636, by rfl⟩ : syracuseStep 1747515 = 2621273) B2621273
theorem B1747591 : Blo 1746574 1747591 := bstep (se 1 (by rfl) ⟨1310693, by rfl⟩ : syracuseStep 1747591 = 2621387) B2621387
theorem B1747599 : Blo 1746574 1747599 := bstep (se 1 (by rfl) ⟨1310699, by rfl⟩ : syracuseStep 1747599 = 2621399) B2621399
theorem B4975289 : Blo 1746574 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B1747643 : Blo 1746574 1747643 := bstep (se 1 (by rfl) ⟨1310732, by rfl⟩ : syracuseStep 1747643 = 2621465) B2621465
theorem B1747719 : Blo 1746574 1747719 := bstep (se 1 (by rfl) ⟨1310789, by rfl⟩ : syracuseStep 1747719 = 2621579) B2621579
theorem B3590927 : Blo 1746574 3590927 := bstep (se 1 (by rfl) ⟨2693195, by rfl⟩ : syracuseStep 3590927 = 5386391) B5386391
theorem B1747727 : Blo 1746574 1747727 := bstep (se 1 (by rfl) ⟨1310795, by rfl⟩ : syracuseStep 1747727 = 2621591) B2621591
theorem B1747771 : Blo 1746574 1747771 := bstep (se 1 (by rfl) ⟨1310828, by rfl⟩ : syracuseStep 1747771 = 2621657) B2621657
theorem B6638395 : Blo 1746574 6638395 := bstep (se 1 (by rfl) ⟨4978796, by rfl⟩ : syracuseStep 6638395 = 9957593) B9957593
theorem B1747847 : Blo 1746574 1747847 := bstep (se 1 (by rfl) ⟨1310885, by rfl⟩ : syracuseStep 1747847 = 2621771) B2621771
theorem B1747855 : Blo 1746574 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B1747899 : Blo 1746574 1747899 := bstep (se 1 (by rfl) ⟨1310924, by rfl⟩ : syracuseStep 1747899 = 2621849) B2621849
theorem B9956317 : Blo 1746574 9956317 := bstep (se 3 (by rfl) ⟨1866809, by rfl⟩ : syracuseStep 9956317 = 3733619) B3733619
theorem B8399875 : Blo 1746574 8399875 := bstep (se 1 (by rfl) ⟨6299906, by rfl⟩ : syracuseStep 8399875 = 12599813) B12599813
theorem B1747975 : Blo 1746574 1747975 := bstep (se 1 (by rfl) ⟨1310981, by rfl⟩ : syracuseStep 1747975 = 2621963) B2621963
theorem B4975631 : Blo 1746574 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B1747983 : Blo 1746574 1747983 := bstep (se 1 (by rfl) ⟨1310987, by rfl⟩ : syracuseStep 1747983 = 2621975) B2621975
theorem B8842283 : Blo 1746574 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B1748027 : Blo 1746574 1748027 := bstep (se 1 (by rfl) ⟨1311020, by rfl⟩ : syracuseStep 1748027 = 2622041) B2622041
theorem B1748103 : Blo 1746574 1748103 := bstep (se 1 (by rfl) ⟨1311077, by rfl⟩ : syracuseStep 1748103 = 2622155) B2622155
theorem B1748111 : Blo 1746574 1748111 := bstep (se 1 (by rfl) ⟨1311083, by rfl⟩ : syracuseStep 1748111 = 2622167) B2622167
theorem B1748155 : Blo 1746574 1748155 := bstep (se 1 (by rfl) ⟨1311116, by rfl⟩ : syracuseStep 1748155 = 2622233) B2622233
theorem B1748231 : Blo 1746574 1748231 := bstep (se 1 (by rfl) ⟨1311173, by rfl⟩ : syracuseStep 1748231 = 2622347) B2622347
theorem B3542287 : Blo 1746574 3542287 := bstep (se 1 (by rfl) ⟨2656715, by rfl⟩ : syracuseStep 3542287 = 5313431) B5313431
theorem B1748239 : Blo 1746574 1748239 := bstep (se 1 (by rfl) ⟨1311179, by rfl⟩ : syracuseStep 1748239 = 2622359) B2622359
theorem B6638881 : Blo 1746574 6638881 := bstep (se 2 (by rfl) ⟨2489580, by rfl⟩ : syracuseStep 6638881 = 4979161) B4979161
theorem B11193659 : Blo 1746574 11193659 := bstep (se 1 (by rfl) ⟨8395244, by rfl⟩ : syracuseStep 11193659 = 16790489) B16790489
theorem B1748283 : Blo 1746574 1748283 := bstep (se 1 (by rfl) ⟨1311212, by rfl⟩ : syracuseStep 1748283 = 2622425) B2622425
theorem B5115197 : Blo 1746574 5115197 := bstep (se 3 (by rfl) ⟨959099, by rfl⟩ : syracuseStep 5115197 = 1918199) B1918199
theorem B18673031 : Blo 1746574 18673031 := bstep (se 1 (by rfl) ⟨14004773, by rfl⟩ : syracuseStep 18673031 = 28009547) B28009547
theorem B16166279 : Blo 1746574 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B1748359 : Blo 1746574 1748359 := bstep (se 1 (by rfl) ⟨1311269, by rfl⟩ : syracuseStep 1748359 = 2622539) B2622539
theorem B1748367 : Blo 1746574 1748367 := bstep (se 1 (by rfl) ⟨1311275, by rfl⟩ : syracuseStep 1748367 = 2622551) B2622551
theorem B3730835 : Blo 1746574 3730835 := bstep (se 1 (by rfl) ⟨2798126, by rfl⟩ : syracuseStep 3730835 = 5596253) B5596253
theorem B4722067 : Blo 1746574 4722067 := bstep (se 1 (by rfl) ⟨3541550, by rfl⟩ : syracuseStep 4722067 = 7083101) B7083101
theorem B11193785 : Blo 1746574 11193785 := bstep (se 2 (by rfl) ⟨4197669, by rfl⟩ : syracuseStep 11193785 = 8395339) B8395339
theorem B1748411 : Blo 1746574 1748411 := bstep (se 1 (by rfl) ⟨1311308, by rfl⟩ : syracuseStep 1748411 = 2622617) B2622617
theorem B1748487 : Blo 1746574 1748487 := bstep (se 1 (by rfl) ⟨1311365, by rfl⟩ : syracuseStep 1748487 = 2622731) B2622731
theorem B1748495 : Blo 1746574 1748495 := bstep (se 1 (by rfl) ⟨1311371, by rfl⟩ : syracuseStep 1748495 = 2622743) B2622743
theorem B5041693 : Blo 1746574 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B7466539 : Blo 1746574 7466539 := bstep (se 1 (by rfl) ⟨5599904, by rfl⟩ : syracuseStep 7466539 = 11199809) B11199809
theorem B6729277 : Blo 1746574 6729277 := bstep (se 3 (by rfl) ⟨1261739, by rfl⟩ : syracuseStep 6729277 = 2523479) B2523479
theorem B1748539 : Blo 1746574 1748539 := bstep (se 1 (by rfl) ⟨1311404, by rfl⟩ : syracuseStep 1748539 = 2622809) B2622809
theorem B8851031 : Blo 1746574 8851031 := bstep (se 1 (by rfl) ⟨6638273, by rfl⟩ : syracuseStep 8851031 = 13276547) B13276547
theorem B4198007 : Blo 1746574 4198007 := bstep (se 1 (by rfl) ⟨3148505, by rfl⟩ : syracuseStep 4198007 = 6297011) B6297011
theorem B2657963 : Blo 1746574 2657963 := bstep (se 1 (by rfl) ⟨1993472, by rfl⟩ : syracuseStep 2657963 = 3986945) B3986945
theorem B9948845 : Blo 1746574 9948845 := bstep (se 3 (by rfl) ⟨1865408, by rfl⟩ : syracuseStep 9948845 = 3730817) B3730817
theorem B4976417 : Blo 1746574 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B2363179 : Blo 1746574 2363179 := bstep (se 1 (by rfl) ⟨1772384, by rfl⟩ : syracuseStep 2363179 = 3544769) B3544769
theorem B33607493 : Blo 1746574 33607493 := bstep (se 4 (by rfl) ⟨3150702, by rfl⟩ : syracuseStep 33607493 = 6301405) B6301405
theorem B3149867 : Blo 1746574 3149867 := bstep (se 1 (by rfl) ⟨2362400, by rfl⟩ : syracuseStep 3149867 = 4724801) B4724801
theorem B8851517 : Blo 1746574 8851517 := bstep (se 3 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 8851517 = 3319319) B3319319
theorem B6295639 : Blo 1746574 6295639 := bstep (se 1 (by rfl) ⟨4721729, by rfl⟩ : syracuseStep 6295639 = 9443459) B9443459
theorem B13455533 : Blo 1746574 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B8843579 : Blo 1746574 8843579 := bstep (se 1 (by rfl) ⟨6632684, by rfl⟩ : syracuseStep 8843579 = 13265369) B13265369
theorem B3150199 : Blo 1746574 3150199 := bstep (se 1 (by rfl) ⟨2362649, by rfl⟩ : syracuseStep 3150199 = 4725299) B4725299
theorem B6631865 : Blo 1746574 6631865 := bstep (se 2 (by rfl) ⟨2486949, by rfl⟩ : syracuseStep 6631865 = 4973899) B4973899
theorem B8843741 : Blo 1746574 8843741 := bstep (se 3 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 8843741 = 3316403) B3316403
theorem B5460481 : Blo 1746574 5460481 := bstep (se 2 (by rfl) ⟨2047680, by rfl⟩ : syracuseStep 5460481 = 4095361) B4095361
theorem B16798211 : Blo 1746574 16798211 := bstep (se 1 (by rfl) ⟨12598658, by rfl⟩ : syracuseStep 16798211 = 25197317) B25197317
theorem B44798507 : Blo 1746574 44798507 := bstep (se 1 (by rfl) ⟨33598880, by rfl⟩ : syracuseStep 44798507 = 67197761) B67197761
theorem B12120833 : Blo 1746574 12120833 := bstep (se 2 (by rfl) ⟨4545312, by rfl⟩ : syracuseStep 12120833 = 9090625) B9090625
theorem B8844065 : Blo 1746574 8844065 := bstep (se 2 (by rfl) ⟨3316524, by rfl⟩ : syracuseStep 8844065 = 6633049) B6633049
theorem B9949985 : Blo 1746574 9949985 := bstep (se 2 (by rfl) ⟨3731244, by rfl⟩ : syracuseStep 9949985 = 7462489) B7462489
theorem B14930891 : Blo 1746574 14930891 := bstep (se 1 (by rfl) ⟨11198168, by rfl⟩ : syracuseStep 14930891 = 22396337) B22396337
theorem B5895179 : Blo 1746574 5895179 := bstep (se 1 (by rfl) ⟨4421384, by rfl⟩ : syracuseStep 5895179 = 8842769) B8842769
theorem B5895287 : Blo 1746574 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B2487439 : Blo 1746574 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B4977931 : Blo 1746574 4977931 := bstep (se 1 (by rfl) ⟨3733448, by rfl⟩ : syracuseStep 4977931 = 7466897) B7466897
theorem B4724087 : Blo 1746574 4724087 := bstep (se 1 (by rfl) ⟨3543065, by rfl⟩ : syracuseStep 4724087 = 7086131) B7086131
theorem B2799049 : Blo 1746574 2799049 := bstep (se 2 (by rfl) ⟨1049643, by rfl⟩ : syracuseStep 2799049 = 2099287) B2099287
theorem B4724239 : Blo 1746574 4724239 := bstep (se 1 (by rfl) ⟨3543179, by rfl⟩ : syracuseStep 4724239 = 7086359) B7086359
theorem B4978205 : Blo 1746574 4978205 := bstep (se 3 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 4978205 = 1866827) B1866827
theorem B20166209 : Blo 1746574 20166209 := bstep (se 2 (by rfl) ⟨7562328, by rfl⟩ : syracuseStep 20166209 = 15124657) B15124657
theorem B12596813 : Blo 1746574 12596813 := bstep (se 3 (by rfl) ⟨2361902, by rfl⟩ : syracuseStep 12596813 = 4723805) B4723805
theorem B4200083 : Blo 1746574 4200083 := bstep (se 1 (by rfl) ⟨3150062, by rfl⟩ : syracuseStep 4200083 = 6300125) B6300125
theorem B5895881 : Blo 1746574 5895881 := bstep (se 2 (by rfl) ⟨2210955, by rfl⟩ : syracuseStep 5895881 = 4421911) B4421911
theorem B2488009 : Blo 1746574 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B8845037 : Blo 1746574 8845037 := bstep (se 3 (by rfl) ⟨1658444, by rfl⟩ : syracuseStep 8845037 = 3316889) B3316889
theorem B18904907 : Blo 1746574 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B4978547 : Blo 1746574 4978547 := bstep (se 1 (by rfl) ⟨3733910, by rfl⟩ : syracuseStep 4978547 = 7467821) B7467821
theorem B3929975 : Blo 1746574 3929975 := bstep (se 1 (by rfl) ⟨2947481, by rfl⟩ : syracuseStep 3929975 = 5894963) B5894963
theorem B9451417 : Blo 1746574 9451417 := bstep (se 2 (by rfl) ⟨3544281, by rfl⟩ : syracuseStep 9451417 = 7088563) B7088563
theorem B3930155 : Blo 1746574 3930155 := bstep (se 1 (by rfl) ⟨2947616, by rfl⟩ : syracuseStep 3930155 = 5895233) B5895233
theorem B2242619 : Blo 1746574 2242619 := bstep (se 1 (by rfl) ⟨1681964, by rfl⟩ : syracuseStep 2242619 = 3363929) B3363929
theorem B3733705 : Blo 1746574 3733705 := bstep (se 2 (by rfl) ⟨1400139, by rfl⟩ : syracuseStep 3733705 = 2800279) B2800279
theorem B7567631 : Blo 1746574 7567631 := bstep (se 1 (by rfl) ⟨5675723, by rfl⟩ : syracuseStep 7567631 = 11351447) B11351447
theorem B2947387 : Blo 1746574 2947387 := bstep (se 1 (by rfl) ⟨2210540, by rfl⟩ : syracuseStep 2947387 = 4421081) B4421081
theorem B4422023 : Blo 1746574 4422023 := bstep (se 1 (by rfl) ⟨3316517, by rfl⟩ : syracuseStep 4422023 = 6633035) B6633035
theorem B5896583 : Blo 1746574 5896583 := bstep (se 1 (by rfl) ⟨4422437, by rfl⟩ : syracuseStep 5896583 = 8844875) B8844875
theorem B3316115 : Blo 1746574 3316115 := bstep (se 1 (by rfl) ⟨2487086, by rfl⟩ : syracuseStep 3316115 = 4974173) B4974173
theorem B3930515 : Blo 1746574 3930515 := bstep (se 1 (by rfl) ⟨2947886, by rfl⟩ : syracuseStep 3930515 = 5895773) B5895773
theorem B18897299 : Blo 1746574 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B3316153 : Blo 1746574 3316153 := bstep (se 2 (by rfl) ⟨1243557, by rfl⟩ : syracuseStep 3316153 = 2487115) B2487115
theorem B4422073 : Blo 1746574 4422073 := bstep (se 2 (by rfl) ⟨1658277, by rfl⟩ : syracuseStep 4422073 = 3316555) B3316555
theorem B2947529 : Blo 1746574 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B3930569 : Blo 1746574 3930569 := bstep (se 2 (by rfl) ⟨1473963, by rfl⟩ : syracuseStep 3930569 = 2947927) B2947927
theorem B12597713 : Blo 1746574 12597713 := bstep (se 2 (by rfl) ⟨4724142, by rfl⟩ : syracuseStep 12597713 = 9448285) B9448285
theorem B2619911 : Blo 1746574 2619911 := bstep (se 1 (by rfl) ⟨1964933, by rfl⟩ : syracuseStep 2619911 = 3929867) B3929867
theorem B8845847 : Blo 1746574 8845847 := bstep (se 1 (by rfl) ⟨6634385, by rfl⟩ : syracuseStep 8845847 = 13268771) B13268771
theorem B2619947 : Blo 1746574 2619947 := bstep (se 1 (by rfl) ⟨1964960, by rfl⟩ : syracuseStep 2619947 = 3929921) B3929921
theorem B2988587 : Blo 1746574 2988587 := bstep (se 1 (by rfl) ⟨2241440, by rfl⟩ : syracuseStep 2988587 = 4482881) B4482881
theorem B2619977 : Blo 1746574 2619977 := bstep (se 2 (by rfl) ⟨982491, by rfl⟩ : syracuseStep 2619977 = 1964983) B1964983
theorem B3734201 : Blo 1746574 3734201 := bstep (se 2 (by rfl) ⟨1400325, by rfl⟩ : syracuseStep 3734201 = 2800651) B2800651
theorem B2620091 : Blo 1746574 2620091 := bstep (se 1 (by rfl) ⟨1965068, by rfl⟩ : syracuseStep 2620091 = 3930137) B3930137
theorem B2620151 : Blo 1746574 2620151 := bstep (se 1 (by rfl) ⟨1965113, by rfl⟩ : syracuseStep 2620151 = 3930227) B3930227
theorem B5896961 : Blo 1746574 5896961 := bstep (se 2 (by rfl) ⟨2211360, by rfl⟩ : syracuseStep 5896961 = 4422721) B4422721
theorem B2620175 : Blo 1746574 2620175 := bstep (se 1 (by rfl) ⟨1965131, by rfl⟩ : syracuseStep 2620175 = 3930263) B3930263
theorem B1866511 : Blo 1746574 1866511 := bstep (se 1 (by rfl) ⟨1399883, by rfl⟩ : syracuseStep 1866511 = 2799767) B2799767
theorem B2620217 : Blo 1746574 2620217 := bstep (se 2 (by rfl) ⟨982581, by rfl⟩ : syracuseStep 2620217 = 1965163) B1965163
theorem B8395609 : Blo 1746574 8395609 := bstep (se 2 (by rfl) ⟨3148353, by rfl⟩ : syracuseStep 8395609 = 6296707) B6296707
theorem B2620295 : Blo 1746574 2620295 := bstep (se 1 (by rfl) ⟨1965221, by rfl⟩ : syracuseStep 2620295 = 3930443) B3930443
theorem B2620331 : Blo 1746574 2620331 := bstep (se 1 (by rfl) ⟨1965248, by rfl⟩ : syracuseStep 2620331 = 3930497) B3930497
theorem B6298553 : Blo 1746574 6298553 := bstep (se 2 (by rfl) ⟨2361957, by rfl⟩ : syracuseStep 6298553 = 4723915) B4723915
theorem B2620361 : Blo 1746574 2620361 := bstep (se 2 (by rfl) ⟨982635, by rfl⟩ : syracuseStep 2620361 = 1965271) B1965271
theorem B6634507 : Blo 1746574 6634507 := bstep (se 1 (by rfl) ⟨4975880, by rfl⟩ : syracuseStep 6634507 = 9951761) B9951761
theorem B4422671 : Blo 1746574 4422671 := bstep (se 1 (by rfl) ⟨3317003, by rfl⟩ : syracuseStep 4422671 = 6634007) B6634007
theorem B2620475 : Blo 1746574 2620475 := bstep (se 1 (by rfl) ⟨1965356, by rfl⟩ : syracuseStep 2620475 = 3930713) B3930713
theorem B2620535 : Blo 1746574 2620535 := bstep (se 1 (by rfl) ⟨1965401, by rfl⟩ : syracuseStep 2620535 = 3930803) B3930803
theorem B2948231 : Blo 1746574 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B3931271 : Blo 1746574 3931271 := bstep (se 1 (by rfl) ⟨2948453, by rfl⟩ : syracuseStep 3931271 = 5896907) B5896907
theorem B1965199 : Blo 1746574 1965199 := bstep (se 1 (by rfl) ⟨1473899, by rfl⟩ : syracuseStep 1965199 = 2947799) B2947799
theorem B2620559 : Blo 1746574 2620559 := bstep (se 1 (by rfl) ⟨1965419, by rfl⟩ : syracuseStep 2620559 = 3930839) B3930839
theorem B2620601 : Blo 1746574 2620601 := bstep (se 2 (by rfl) ⟨982725, by rfl⟩ : syracuseStep 2620601 = 1965451) B1965451
theorem B9444545 : Blo 1746574 9444545 := bstep (se 2 (by rfl) ⟨3541704, by rfl⟩ : syracuseStep 9444545 = 7083409) B7083409
theorem B2620679 : Blo 1746574 2620679 := bstep (se 1 (by rfl) ⟨1965509, by rfl⟩ : syracuseStep 2620679 = 3931019) B3931019
theorem B2620715 : Blo 1746574 2620715 := bstep (se 1 (by rfl) ⟨1965536, by rfl⟩ : syracuseStep 2620715 = 3931073) B3931073
theorem B2915627 : Blo 1746574 2915627 := bstep (se 1 (by rfl) ⟨2186720, by rfl⟩ : syracuseStep 2915627 = 4373441) B4373441
theorem B3931451 : Blo 1746574 3931451 := bstep (se 1 (by rfl) ⟨2948588, by rfl⟩ : syracuseStep 3931451 = 5897177) B5897177
theorem B6634811 : Blo 1746574 6634811 := bstep (se 1 (by rfl) ⟨4976108, by rfl⟩ : syracuseStep 6634811 = 9952217) B9952217
theorem B2620745 : Blo 1746574 2620745 := bstep (se 2 (by rfl) ⟨982779, by rfl⟩ : syracuseStep 2620745 = 1965559) B1965559
theorem B3931577 : Blo 1746574 3931577 := bstep (se 2 (by rfl) ⟨1474341, by rfl⟩ : syracuseStep 3931577 = 2948683) B2948683
theorem B2620859 : Blo 1746574 2620859 := bstep (se 1 (by rfl) ⟨1965644, by rfl⟩ : syracuseStep 2620859 = 3931289) B3931289
theorem B2620919 : Blo 1746574 2620919 := bstep (se 1 (by rfl) ⟨1965689, by rfl⟩ : syracuseStep 2620919 = 3931379) B3931379
theorem B2620943 : Blo 1746574 2620943 := bstep (se 1 (by rfl) ⟨1965707, by rfl⟩ : syracuseStep 2620943 = 3931415) B3931415
theorem B5897771 : Blo 1746574 5897771 := bstep (se 1 (by rfl) ⟨4423328, by rfl⟩ : syracuseStep 5897771 = 8846657) B8846657
theorem B2620985 : Blo 1746574 2620985 := bstep (se 2 (by rfl) ⟨982869, by rfl⟩ : syracuseStep 2620985 = 1965739) B1965739
theorem B1965703 : Blo 1746574 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B2621063 : Blo 1746574 2621063 := bstep (se 1 (by rfl) ⟨1965797, by rfl⟩ : syracuseStep 2621063 = 3931595) B3931595
theorem B2621099 : Blo 1746574 2621099 := bstep (se 1 (by rfl) ⟨1965824, by rfl⟩ : syracuseStep 2621099 = 3931649) B3931649
theorem B2621129 : Blo 1746574 2621129 := bstep (se 2 (by rfl) ⟨982923, by rfl⟩ : syracuseStep 2621129 = 1965847) B1965847
theorem B4423369 : Blo 1746574 4423369 := bstep (se 2 (by rfl) ⟨1658763, by rfl⟩ : syracuseStep 4423369 = 3317527) B3317527
theorem B7085825 : Blo 1746574 7085825 := bstep (se 2 (by rfl) ⟨2657184, by rfl⟩ : syracuseStep 7085825 = 5314369) B5314369
theorem B2948879 : Blo 1746574 2948879 := bstep (se 1 (by rfl) ⟨2211659, by rfl⟩ : syracuseStep 2948879 = 4423319) B4423319
theorem B3931919 : Blo 1746574 3931919 := bstep (se 1 (by rfl) ⟨2948939, by rfl⟩ : syracuseStep 3931919 = 5897879) B5897879
theorem B7085839 : Blo 1746574 7085839 := bstep (se 1 (by rfl) ⟨5314379, by rfl⟩ : syracuseStep 7085839 = 10628759) B10628759
theorem B3931937 : Blo 1746574 3931937 := bstep (se 2 (by rfl) ⟨1474476, by rfl⟩ : syracuseStep 3931937 = 2948953) B2948953
theorem B6635297 : Blo 1746574 6635297 := bstep (se 2 (by rfl) ⟨2488236, by rfl⟩ : syracuseStep 6635297 = 4976473) B4976473
theorem B1965883 : Blo 1746574 1965883 := bstep (se 1 (by rfl) ⟨1474412, by rfl⟩ : syracuseStep 1965883 = 2948825) B2948825
theorem B2621243 : Blo 1746574 2621243 := bstep (se 1 (by rfl) ⟨1965932, by rfl⟩ : syracuseStep 2621243 = 3931865) B3931865
theorem B4423511 : Blo 1746574 4423511 := bstep (se 1 (by rfl) ⟨3317633, by rfl⟩ : syracuseStep 4423511 = 6635267) B6635267
theorem B15138649 : Blo 1746574 15138649 := bstep (se 2 (by rfl) ⟨5676993, by rfl⟩ : syracuseStep 15138649 = 11353987) B11353987
theorem B2621303 : Blo 1746574 2621303 := bstep (se 1 (by rfl) ⟨1965977, by rfl⟩ : syracuseStep 2621303 = 3931955) B3931955
theorem B2621327 : Blo 1746574 2621327 := bstep (se 1 (by rfl) ⟨1965995, by rfl⟩ : syracuseStep 2621327 = 3931991) B3931991
theorem B53780377 : Blo 1746574 53780377 := bstep (se 2 (by rfl) ⟨20167641, by rfl⟩ : syracuseStep 53780377 = 40335283) B40335283
theorem B2621369 : Blo 1746574 2621369 := bstep (se 2 (by rfl) ⟨983013, by rfl⟩ : syracuseStep 2621369 = 1966027) B1966027
theorem B10092509 : Blo 1746574 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B2621519 : Blo 1746574 2621519 := bstep (se 1 (by rfl) ⟨1966139, by rfl⟩ : syracuseStep 2621519 = 3932279) B3932279
theorem B8970355 : Blo 1746574 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B2621639 : Blo 1746574 2621639 := bstep (se 1 (by rfl) ⟨1966229, by rfl⟩ : syracuseStep 2621639 = 3932459) B3932459
theorem B2212039 : Blo 1746574 2212039 := bstep (se 1 (by rfl) ⟨1659029, by rfl⟩ : syracuseStep 2212039 = 3318059) B3318059
theorem B1966279 : Blo 1746574 1966279 := bstep (se 1 (by rfl) ⟨1474709, by rfl⟩ : syracuseStep 1966279 = 2949419) B2949419
theorem B11198807 : Blo 1746574 11198807 := bstep (se 1 (by rfl) ⟨8399105, by rfl⟩ : syracuseStep 11198807 = 16798211) B16798211
theorem B2621801 : Blo 1746574 2621801 := bstep (se 2 (by rfl) ⟨983175, by rfl⟩ : syracuseStep 2621801 = 1966351) B1966351
theorem B2621879 : Blo 1746574 2621879 := bstep (se 1 (by rfl) ⟨1966409, by rfl⟩ : syracuseStep 2621879 = 3932819) B3932819
theorem B2621915 : Blo 1746574 2621915 := bstep (se 1 (by rfl) ⟨1966436, by rfl⟩ : syracuseStep 2621915 = 3932873) B3932873
theorem B4424179 : Blo 1746574 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B11960855 : Blo 1746574 11960855 := bstep (se 1 (by rfl) ⟨8970641, by rfl⟩ : syracuseStep 11960855 = 17941283) B17941283
theorem B3932711 : Blo 1746574 3932711 := bstep (se 1 (by rfl) ⟨2949533, by rfl⟩ : syracuseStep 3932711 = 5899067) B5899067
theorem B2949689 : Blo 1746574 2949689 := bstep (se 2 (by rfl) ⟨1106133, by rfl⟩ : syracuseStep 2949689 = 2212267) B2212267
theorem B13271687 : Blo 1746574 13271687 := bstep (se 1 (by rfl) ⟨9953765, by rfl⟩ : syracuseStep 13271687 = 19907531) B19907531
theorem B9953927 : Blo 1746574 9953927 := bstep (se 1 (by rfl) ⟨7465445, by rfl⟩ : syracuseStep 9953927 = 14930891) B14930891
theorem B13640525 : Blo 1746574 13640525 := bstep (se 3 (by rfl) ⟨2557598, by rfl⟩ : syracuseStep 13640525 = 5115197) B5115197
theorem B3933035 : Blo 1746574 3933035 := bstep (se 1 (by rfl) ⟨2949776, by rfl⟩ : syracuseStep 3933035 = 5899553) B5899553
theorem B3933089 : Blo 1746574 3933089 := bstep (se 2 (by rfl) ⟨1474908, by rfl⟩ : syracuseStep 3933089 = 2949817) B2949817
theorem B2622383 : Blo 1746574 2622383 := bstep (se 1 (by rfl) ⟨1966787, by rfl⟩ : syracuseStep 2622383 = 3933575) B3933575
theorem B2622473 : Blo 1746574 2622473 := bstep (se 2 (by rfl) ⟨983427, by rfl⟩ : syracuseStep 2622473 = 1966855) B1966855
theorem B5899283 : Blo 1746574 5899283 := bstep (se 1 (by rfl) ⟨4424462, by rfl⟩ : syracuseStep 5899283 = 8848925) B8848925
theorem B3318803 : Blo 1746574 3318803 := bstep (se 1 (by rfl) ⟨2489102, by rfl⟩ : syracuseStep 3318803 = 4978205) B4978205
theorem B2622503 : Blo 1746574 2622503 := bstep (se 1 (by rfl) ⟨1966877, by rfl⟩ : syracuseStep 2622503 = 3933755) B3933755
theorem B1967143 : Blo 1746574 1967143 := bstep (se 1 (by rfl) ⟨1475357, by rfl⟩ : syracuseStep 1967143 = 2950715) B2950715
theorem B13444139 : Blo 1746574 13444139 := bstep (se 1 (by rfl) ⟨10083104, by rfl⟩ : syracuseStep 13444139 = 20166209) B20166209
theorem B8397875 : Blo 1746574 8397875 := bstep (se 1 (by rfl) ⟨6298406, by rfl⟩ : syracuseStep 8397875 = 12596813) B12596813
theorem B2622587 : Blo 1746574 2622587 := bstep (se 1 (by rfl) ⟨1966940, by rfl⟩ : syracuseStep 2622587 = 3933881) B3933881
theorem B3933431 : Blo 1746574 3933431 := bstep (se 1 (by rfl) ⟨2950073, by rfl⟩ : syracuseStep 3933431 = 5900147) B5900147
theorem B3319031 : Blo 1746574 3319031 := bstep (se 1 (by rfl) ⟨2489273, by rfl⟩ : syracuseStep 3319031 = 4978547) B4978547
theorem B2950391 : Blo 1746574 2950391 := bstep (se 1 (by rfl) ⟨2212793, by rfl⟩ : syracuseStep 2950391 = 4425587) B4425587
theorem B2622713 : Blo 1746574 2622713 := bstep (se 2 (by rfl) ⟨983517, by rfl⟩ : syracuseStep 2622713 = 1967035) B1967035
theorem B5899607 : Blo 1746574 5899607 := bstep (se 1 (by rfl) ⟨4424705, by rfl⟩ : syracuseStep 5899607 = 8849411) B8849411
theorem B11199833 : Blo 1746574 11199833 := bstep (se 2 (by rfl) ⟨4199937, by rfl⟩ : syracuseStep 11199833 = 8399875) B8399875
theorem B2622815 : Blo 1746574 2622815 := bstep (se 1 (by rfl) ⟨1967111, by rfl⟩ : syracuseStep 2622815 = 3934223) B3934223
theorem B2622827 : Blo 1746574 2622827 := bstep (se 1 (by rfl) ⟨1967120, by rfl⟩ : syracuseStep 2622827 = 3934241) B3934241
theorem B1771103 : Blo 1746574 1771103 := bstep (se 1 (by rfl) ⟨1328327, by rfl⟩ : syracuseStep 1771103 = 2656655) B2656655
theorem B4425313 : Blo 1746574 4425313 := bstep (se 2 (by rfl) ⟨1659492, by rfl⟩ : syracuseStep 4425313 = 3318985) B3318985
theorem B8398475 : Blo 1746574 8398475 := bstep (se 1 (by rfl) ⟨6298856, by rfl⟩ : syracuseStep 8398475 = 12597713) B12597713
theorem B1746607 : Blo 1746574 1746607 := bstep (se 1 (by rfl) ⟨1309955, by rfl⟩ : syracuseStep 1746607 = 2619911) B2619911
theorem B6637241 : Blo 1746574 6637241 := bstep (se 2 (by rfl) ⟨2488965, by rfl⟩ : syracuseStep 6637241 = 4977931) B4977931
theorem B1746631 : Blo 1746574 1746631 := bstep (se 1 (by rfl) ⟨1309973, by rfl⟩ : syracuseStep 1746631 = 2619947) B2619947
theorem B1746651 : Blo 1746574 1746651 := bstep (se 1 (by rfl) ⟨1309988, by rfl⟩ : syracuseStep 1746651 = 2619977) B2619977
theorem B1746727 : Blo 1746574 1746727 := bstep (se 1 (by rfl) ⟨1310045, by rfl⟩ : syracuseStep 1746727 = 2620091) B2620091
theorem B3934025 : Blo 1746574 3934025 := bstep (se 2 (by rfl) ⟨1475259, by rfl⟩ : syracuseStep 3934025 = 2950519) B2950519
theorem B1746767 : Blo 1746574 1746767 := bstep (se 1 (by rfl) ⟨1310075, by rfl⟩ : syracuseStep 1746767 = 2620151) B2620151
theorem B1746783 : Blo 1746574 1746783 := bstep (se 1 (by rfl) ⟨1310087, by rfl⟩ : syracuseStep 1746783 = 2620175) B2620175
theorem B1746811 : Blo 1746574 1746811 := bstep (se 1 (by rfl) ⟨1310108, by rfl⟩ : syracuseStep 1746811 = 2620217) B2620217
theorem B1746863 : Blo 1746574 1746863 := bstep (se 1 (by rfl) ⟨1310147, by rfl⟩ : syracuseStep 1746863 = 2620295) B2620295
theorem B1746887 : Blo 1746574 1746887 := bstep (se 1 (by rfl) ⟨1310165, by rfl⟩ : syracuseStep 1746887 = 2620331) B2620331
theorem B1746907 : Blo 1746574 1746907 := bstep (se 1 (by rfl) ⟨1310180, by rfl⟩ : syracuseStep 1746907 = 2620361) B2620361
theorem B1746983 : Blo 1746574 1746983 := bstep (se 1 (by rfl) ⟨1310237, by rfl⟩ : syracuseStep 1746983 = 2620475) B2620475
theorem B13273145 : Blo 1746574 13273145 := bstep (se 2 (by rfl) ⟨4977429, by rfl⟩ : syracuseStep 13273145 = 9954859) B9954859
theorem B9955385 : Blo 1746574 9955385 := bstep (se 2 (by rfl) ⟨3733269, by rfl⟩ : syracuseStep 9955385 = 7466539) B7466539
theorem B1747023 : Blo 1746574 1747023 := bstep (se 1 (by rfl) ⟨1310267, by rfl⟩ : syracuseStep 1747023 = 2620535) B2620535
theorem B8972369 : Blo 1746574 8972369 := bstep (se 2 (by rfl) ⟨3364638, by rfl⟩ : syracuseStep 8972369 = 6729277) B6729277
theorem B1747039 : Blo 1746574 1747039 := bstep (se 1 (by rfl) ⟨1310279, by rfl⟩ : syracuseStep 1747039 = 2620559) B2620559
theorem B1747067 : Blo 1746574 1747067 := bstep (se 1 (by rfl) ⟨1310300, by rfl⟩ : syracuseStep 1747067 = 2620601) B2620601
theorem B1747119 : Blo 1746574 1747119 := bstep (se 1 (by rfl) ⟨1310339, by rfl⟩ : syracuseStep 1747119 = 2620679) B2620679
theorem B1747143 : Blo 1746574 1747143 := bstep (se 1 (by rfl) ⟨1310357, by rfl⟩ : syracuseStep 1747143 = 2620715) B2620715
theorem B1747163 : Blo 1746574 1747163 := bstep (se 1 (by rfl) ⟨1310372, by rfl⟩ : syracuseStep 1747163 = 2620745) B2620745
theorem B1747239 : Blo 1746574 1747239 := bstep (se 1 (by rfl) ⟨1310429, by rfl⟩ : syracuseStep 1747239 = 2620859) B2620859
theorem B1747279 : Blo 1746574 1747279 := bstep (se 1 (by rfl) ⟨1310459, by rfl⟩ : syracuseStep 1747279 = 2620919) B2620919
theorem B1747295 : Blo 1746574 1747295 := bstep (se 1 (by rfl) ⟨1310471, by rfl⟩ : syracuseStep 1747295 = 2620943) B2620943
theorem B17926505 : Blo 1746574 17926505 := bstep (se 2 (by rfl) ⟨6722439, by rfl⟩ : syracuseStep 17926505 = 13444879) B13444879
theorem B9447785 : Blo 1746574 9447785 := bstep (se 2 (by rfl) ⟨3542919, by rfl⟩ : syracuseStep 9447785 = 7085839) B7085839
theorem B1747323 : Blo 1746574 1747323 := bstep (se 1 (by rfl) ⟨1310492, by rfl⟩ : syracuseStep 1747323 = 2620985) B2620985
theorem B5900687 : Blo 1746574 5900687 := bstep (se 1 (by rfl) ⟨4425515, by rfl⟩ : syracuseStep 5900687 = 8851031) B8851031
theorem B1747375 : Blo 1746574 1747375 := bstep (se 1 (by rfl) ⟨1310531, by rfl⟩ : syracuseStep 1747375 = 2621063) B2621063
theorem B1747399 : Blo 1746574 1747399 := bstep (se 1 (by rfl) ⟨1310549, by rfl⟩ : syracuseStep 1747399 = 2621099) B2621099
theorem B1771975 : Blo 1746574 1771975 := bstep (se 1 (by rfl) ⟨1328981, by rfl⟩ : syracuseStep 1771975 = 2657963) B2657963
theorem B95685077 : Blo 1746574 95685077 := bstep (se 7 (by rfl) ⟨1121309, by rfl⟩ : syracuseStep 95685077 = 2242619) B2242619
theorem B1747419 : Blo 1746574 1747419 := bstep (se 1 (by rfl) ⟨1310564, by rfl⟩ : syracuseStep 1747419 = 2621129) B2621129
theorem B71707169 : Blo 1746574 71707169 := bstep (se 2 (by rfl) ⟨26890188, by rfl⟩ : syracuseStep 71707169 = 53780377) B53780377
theorem B12601889 : Blo 1746574 12601889 := bstep (se 2 (by rfl) ⟨4725708, by rfl⟩ : syracuseStep 12601889 = 9451417) B9451417
theorem B1747495 : Blo 1746574 1747495 := bstep (se 1 (by rfl) ⟨1310621, by rfl⟩ : syracuseStep 1747495 = 2621243) B2621243
theorem B1747535 : Blo 1746574 1747535 := bstep (se 1 (by rfl) ⟨1310651, by rfl⟩ : syracuseStep 1747535 = 2621303) B2621303
theorem B1747551 : Blo 1746574 1747551 := bstep (se 1 (by rfl) ⟨1310663, by rfl⟩ : syracuseStep 1747551 = 2621327) B2621327
theorem B1747579 : Blo 1746574 1747579 := bstep (se 1 (by rfl) ⟨1310684, by rfl⟩ : syracuseStep 1747579 = 2621369) B2621369
theorem B6728339 : Blo 1746574 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B1747631 : Blo 1746574 1747631 := bstep (se 1 (by rfl) ⟨1310723, by rfl⟩ : syracuseStep 1747631 = 2621447) B2621447
theorem B4721341 : Blo 1746574 4721341 := bstep (se 3 (by rfl) ⟨885251, by rfl⟩ : syracuseStep 4721341 = 1770503) B1770503
theorem B1747655 : Blo 1746574 1747655 := bstep (se 1 (by rfl) ⟨1310741, by rfl⟩ : syracuseStep 1747655 = 2621483) B2621483
theorem B5901011 : Blo 1746574 5901011 := bstep (se 1 (by rfl) ⟨4425758, by rfl⟩ : syracuseStep 5901011 = 8851517) B8851517
theorem B1747675 : Blo 1746574 1747675 := bstep (se 1 (by rfl) ⟨1310756, by rfl⟩ : syracuseStep 1747675 = 2621513) B2621513
theorem B8399645 : Blo 1746574 8399645 := bstep (se 3 (by rfl) ⟨1574933, by rfl⟩ : syracuseStep 8399645 = 3149867) B3149867
theorem B1747751 : Blo 1746574 1747751 := bstep (se 1 (by rfl) ⟨1310813, by rfl⟩ : syracuseStep 1747751 = 2621627) B2621627
theorem B26889029 : Blo 1746574 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B1747791 : Blo 1746574 1747791 := bstep (se 1 (by rfl) ⟨1310843, by rfl⟩ : syracuseStep 1747791 = 2621687) B2621687
theorem B1747807 : Blo 1746574 1747807 := bstep (se 1 (by rfl) ⟨1310855, by rfl⟩ : syracuseStep 1747807 = 2621711) B2621711
theorem B1747835 : Blo 1746574 1747835 := bstep (se 1 (by rfl) ⟨1310876, by rfl⟩ : syracuseStep 1747835 = 2621753) B2621753
theorem B1747887 : Blo 1746574 1747887 := bstep (se 1 (by rfl) ⟨1310915, by rfl⟩ : syracuseStep 1747887 = 2621831) B2621831
theorem B1747911 : Blo 1746574 1747911 := bstep (se 1 (by rfl) ⟨1310933, by rfl⟩ : syracuseStep 1747911 = 2621867) B2621867
theorem B1747931 : Blo 1746574 1747931 := bstep (se 1 (by rfl) ⟨1310948, by rfl⟩ : syracuseStep 1747931 = 2621897) B2621897
theorem B1748007 : Blo 1746574 1748007 := bstep (se 1 (by rfl) ⟨1311005, by rfl⟩ : syracuseStep 1748007 = 2622011) B2622011
theorem B1748047 : Blo 1746574 1748047 := bstep (se 1 (by rfl) ⟨1311035, by rfl⟩ : syracuseStep 1748047 = 2622071) B2622071
theorem B1748063 : Blo 1746574 1748063 := bstep (se 1 (by rfl) ⟨1311047, by rfl⟩ : syracuseStep 1748063 = 2622095) B2622095
theorem B31100021 : Blo 1746574 31100021 := bstep (se 5 (by rfl) ⟨1457813, by rfl⟩ : syracuseStep 31100021 = 2915627) B2915627
theorem B1748091 : Blo 1746574 1748091 := bstep (se 1 (by rfl) ⟨1311068, by rfl⟩ : syracuseStep 1748091 = 2622137) B2622137
theorem B8080555 : Blo 1746574 8080555 := bstep (se 1 (by rfl) ⟨6060416, by rfl⟩ : syracuseStep 8080555 = 12120833) B12120833
theorem B1748143 : Blo 1746574 1748143 := bstep (se 1 (by rfl) ⟨1311107, by rfl⟩ : syracuseStep 1748143 = 2622215) B2622215
theorem B33582275 : Blo 1746574 33582275 := bstep (se 1 (by rfl) ⟨25186706, by rfl⟩ : syracuseStep 33582275 = 50373413) B50373413
theorem B1748167 : Blo 1746574 1748167 := bstep (se 1 (by rfl) ⟨1311125, by rfl⟩ : syracuseStep 1748167 = 2622251) B2622251
theorem B1748187 : Blo 1746574 1748187 := bstep (se 1 (by rfl) ⟨1311140, by rfl⟩ : syracuseStep 1748187 = 2622281) B2622281
theorem B1748263 : Blo 1746574 1748263 := bstep (se 1 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 1748263 = 2622395) B2622395
theorem B1748303 : Blo 1746574 1748303 := bstep (se 1 (by rfl) ⟨1311227, by rfl⟩ : syracuseStep 1748303 = 2622455) B2622455
theorem B1748319 : Blo 1746574 1748319 := bstep (se 1 (by rfl) ⟨1311239, by rfl⟩ : syracuseStep 1748319 = 2622479) B2622479
theorem B1748347 : Blo 1746574 1748347 := bstep (se 1 (by rfl) ⟨1311260, by rfl⟩ : syracuseStep 1748347 = 2622521) B2622521
theorem B5311873 : Blo 1746574 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B11201935 : Blo 1746574 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B13266341 : Blo 1746574 13266341 := bstep (se 4 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 13266341 = 2487439) B2487439
theorem B1748399 : Blo 1746574 1748399 := bstep (se 1 (by rfl) ⟨1311299, by rfl⟩ : syracuseStep 1748399 = 2622599) B2622599
theorem B1748423 : Blo 1746574 1748423 := bstep (se 1 (by rfl) ⟨1311317, by rfl⟩ : syracuseStep 1748423 = 2622635) B2622635
theorem B1748443 : Blo 1746574 1748443 := bstep (se 1 (by rfl) ⟨1311332, by rfl⟩ : syracuseStep 1748443 = 2622665) B2622665
theorem B1748519 : Blo 1746574 1748519 := bstep (se 1 (by rfl) ⟨1311389, by rfl⟩ : syracuseStep 1748519 = 2622779) B2622779
theorem B48459341 : Blo 1746574 48459341 := bstep (se 3 (by rfl) ⟨9086126, by rfl⟩ : syracuseStep 48459341 = 18172253) B18172253
theorem B1748559 : Blo 1746574 1748559 := bstep (se 1 (by rfl) ⟨1311419, by rfl⟩ : syracuseStep 1748559 = 2622839) B2622839
theorem B8851193 : Blo 1746574 8851193 := bstep (se 2 (by rfl) ⟨3319197, by rfl⟩ : syracuseStep 8851193 = 6638395) B6638395
theorem B11194145 : Blo 1746574 11194145 := bstep (se 2 (by rfl) ⟨4197804, by rfl⟩ : syracuseStep 11194145 = 8395609) B8395609
theorem B12603271 : Blo 1746574 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B13275089 : Blo 1746574 13275089 := bstep (se 2 (by rfl) ⟨4978158, by rfl⟩ : syracuseStep 13275089 = 9956317) B9956317
theorem B28340239 : Blo 1746574 28340239 := bstep (se 1 (by rfl) ⟨21255179, by rfl⟩ : syracuseStep 28340239 = 42510359) B42510359
theorem B6631577 : Blo 1746574 6631577 := bstep (se 2 (by rfl) ⟨2486841, by rfl⟩ : syracuseStep 6631577 = 4973683) B4973683
theorem B12595429 : Blo 1746574 12595429 := bstep (se 4 (by rfl) ⟨1180821, by rfl⟩ : syracuseStep 12595429 = 2361643) B2361643
theorem B11194685 : Blo 1746574 11194685 := bstep (se 3 (by rfl) ⟨2099003, by rfl⟩ : syracuseStep 11194685 = 4198007) B4198007
theorem B4723049 : Blo 1746574 4723049 := bstep (se 2 (by rfl) ⟨1771143, by rfl⟩ : syracuseStep 4723049 = 3542287) B3542287
theorem B8851841 : Blo 1746574 8851841 := bstep (se 2 (by rfl) ⟨3319440, by rfl⟩ : syracuseStep 8851841 = 6638881) B6638881
theorem B6296089 : Blo 1746574 6296089 := bstep (se 2 (by rfl) ⟨2361033, by rfl⟩ : syracuseStep 6296089 = 4722067) B4722067
theorem B3732065 : Blo 1746574 3732065 := bstep (se 2 (by rfl) ⟨1399524, by rfl⟩ : syracuseStep 3732065 = 2799049) B2799049
theorem B4199035 : Blo 1746574 4199035 := bstep (se 1 (by rfl) ⟨3149276, by rfl⟩ : syracuseStep 4199035 = 6298553) B6298553
theorem B5894855 : Blo 1746574 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B6296363 : Blo 1746574 6296363 := bstep (se 1 (by rfl) ⟨4722272, by rfl⟩ : syracuseStep 6296363 = 9444545) B9444545
theorem B36352817 : Blo 1746574 36352817 := bstep (se 2 (by rfl) ⟨13632306, by rfl⟩ : syracuseStep 36352817 = 27264613) B27264613
theorem B12448687 : Blo 1746574 12448687 := bstep (se 1 (by rfl) ⟨9336515, by rfl⟩ : syracuseStep 12448687 = 18673031) B18673031
theorem B10777519 : Blo 1746574 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B2487223 : Blo 1746574 2487223 := bstep (se 1 (by rfl) ⟨1865417, by rfl⟩ : syracuseStep 2487223 = 3730835) B3730835
theorem B3150905 : Blo 1746574 3150905 := bstep (se 2 (by rfl) ⟨1181589, by rfl⟩ : syracuseStep 3150905 = 2363179) B2363179
theorem B6632563 : Blo 1746574 6632563 := bstep (se 1 (by rfl) ⟨4974422, by rfl⟩ : syracuseStep 6632563 = 9948845) B9948845
theorem B4723883 : Blo 1746574 4723883 := bstep (se 1 (by rfl) ⟨3542912, by rfl⟩ : syracuseStep 4723883 = 7085825) B7085825
theorem B8394185 : Blo 1746574 8394185 := bstep (se 2 (by rfl) ⟨3147819, by rfl⟩ : syracuseStep 8394185 = 6295639) B6295639
theorem B38303221 : Blo 1746574 38303221 := bstep (se 5 (by rfl) ⟨1795463, by rfl⟩ : syracuseStep 38303221 = 3590927) B3590927
theorem B5895719 : Blo 1746574 5895719 := bstep (se 1 (by rfl) ⟨4421789, by rfl⟩ : syracuseStep 5895719 = 8843579) B8843579
theorem B9950759 : Blo 1746574 9950759 := bstep (se 1 (by rfl) ⟨7463069, by rfl⟩ : syracuseStep 9950759 = 14926139) B14926139
theorem B4978273 : Blo 1746574 4978273 := bstep (se 2 (by rfl) ⟨1866852, by rfl⟩ : syracuseStep 4978273 = 3733705) B3733705
theorem B4421243 : Blo 1746574 4421243 := bstep (se 1 (by rfl) ⟨3315932, by rfl⟩ : syracuseStep 4421243 = 6631865) B6631865
theorem B5895827 : Blo 1746574 5895827 := bstep (se 1 (by rfl) ⟨4421870, by rfl⟩ : syracuseStep 5895827 = 8843741) B8843741
theorem B29865671 : Blo 1746574 29865671 := bstep (se 1 (by rfl) ⟨22399253, by rfl⟩ : syracuseStep 29865671 = 44798507) B44798507
theorem B3929849 : Blo 1746574 3929849 := bstep (se 2 (by rfl) ⟨1473693, by rfl⟩ : syracuseStep 3929849 = 2947387) B2947387
theorem B4200265 : Blo 1746574 4200265 := bstep (se 2 (by rfl) ⟨1575099, by rfl⟩ : syracuseStep 4200265 = 3150199) B3150199
theorem B5896043 : Blo 1746574 5896043 := bstep (se 1 (by rfl) ⟨4422032, by rfl⟩ : syracuseStep 5896043 = 8844065) B8844065
theorem B6633323 : Blo 1746574 6633323 := bstep (se 1 (by rfl) ⟨4974992, by rfl⟩ : syracuseStep 6633323 = 9949985) B9949985
theorem B4421537 : Blo 1746574 4421537 := bstep (se 2 (by rfl) ⟨1658076, by rfl⟩ : syracuseStep 4421537 = 3316153) B3316153
theorem B5896097 : Blo 1746574 5896097 := bstep (se 2 (by rfl) ⟨2211036, by rfl⟩ : syracuseStep 5896097 = 4422073) B4422073
theorem B7280641 : Blo 1746574 7280641 := bstep (se 2 (by rfl) ⟨2730240, by rfl⟩ : syracuseStep 7280641 = 5460481) B5460481
theorem B3930119 : Blo 1746574 3930119 := bstep (se 1 (by rfl) ⟨2947589, by rfl⟩ : syracuseStep 3930119 = 5895179) B5895179
theorem B3930191 : Blo 1746574 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B12597565 : Blo 1746574 12597565 := bstep (se 3 (by rfl) ⟨2362043, by rfl⟩ : syracuseStep 12597565 = 4724087) B4724087
theorem B2488681 : Blo 1746574 2488681 := bstep (se 2 (by rfl) ⟨933255, by rfl⟩ : syracuseStep 2488681 = 1866511) B1866511
theorem B2800055 : Blo 1746574 2800055 := bstep (se 1 (by rfl) ⟨2100041, by rfl⟩ : syracuseStep 2800055 = 4200083) B4200083
theorem B3930587 : Blo 1746574 3930587 := bstep (se 1 (by rfl) ⟨2947940, by rfl⟩ : syracuseStep 3930587 = 5895881) B5895881
theorem B5896691 : Blo 1746574 5896691 := bstep (se 1 (by rfl) ⟨4422518, by rfl⟩ : syracuseStep 5896691 = 8845037) B8845037
theorem B58235435 : Blo 1746574 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B2619983 : Blo 1746574 2619983 := bstep (se 1 (by rfl) ⟨1964987, by rfl⟩ : syracuseStep 2619983 = 3929975) B3929975
theorem B8846009 : Blo 1746574 8846009 := bstep (se 2 (by rfl) ⟨3317253, by rfl⟩ : syracuseStep 8846009 = 6634507) B6634507
theorem B2620103 : Blo 1746574 2620103 := bstep (se 1 (by rfl) ⟨1965077, by rfl⟩ : syracuseStep 2620103 = 3930155) B3930155
theorem B4201159 : Blo 1746574 4201159 := bstep (se 1 (by rfl) ⟨3150869, by rfl⟩ : syracuseStep 4201159 = 6301739) B6301739
theorem B7969565 : Blo 1746574 7969565 := bstep (se 3 (by rfl) ⟨1494293, by rfl⟩ : syracuseStep 7969565 = 2988587) B2988587
theorem B5045087 : Blo 1746574 5045087 := bstep (se 1 (by rfl) ⟨3783815, by rfl⟩ : syracuseStep 5045087 = 7567631) B7567631
theorem B2620265 : Blo 1746574 2620265 := bstep (se 2 (by rfl) ⟨982599, by rfl⟩ : syracuseStep 2620265 = 1965199) B1965199
theorem B2948015 : Blo 1746574 2948015 := bstep (se 1 (by rfl) ⟨2211011, by rfl⟩ : syracuseStep 2948015 = 4422023) B4422023
theorem B3931055 : Blo 1746574 3931055 := bstep (se 1 (by rfl) ⟨2948291, by rfl⟩ : syracuseStep 3931055 = 5896583) B5896583
theorem B2210743 : Blo 1746574 2210743 := bstep (se 1 (by rfl) ⟨1658057, by rfl⟩ : syracuseStep 2210743 = 3316115) B3316115
theorem B2620343 : Blo 1746574 2620343 := bstep (se 1 (by rfl) ⟨1965257, by rfl⟩ : syracuseStep 2620343 = 3930515) B3930515
theorem B12598199 : Blo 1746574 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B1965019 : Blo 1746574 1965019 := bstep (se 1 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 1965019 = 2947529) B2947529
theorem B2620379 : Blo 1746574 2620379 := bstep (se 1 (by rfl) ⟨1965284, by rfl⟩ : syracuseStep 2620379 = 3930569) B3930569
theorem B5897231 : Blo 1746574 5897231 := bstep (se 1 (by rfl) ⟨4422923, by rfl⟩ : syracuseStep 5897231 = 8845847) B8845847
theorem B3316859 : Blo 1746574 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B2489467 : Blo 1746574 2489467 := bstep (se 1 (by rfl) ⟨1867100, by rfl⟩ : syracuseStep 2489467 = 3734201) B3734201
theorem B80739461 : Blo 1746574 80739461 := bstep (se 4 (by rfl) ⟨7569324, by rfl⟩ : syracuseStep 80739461 = 15138649) B15138649
theorem B3931307 : Blo 1746574 3931307 := bstep (se 1 (by rfl) ⟨2948480, by rfl⟩ : syracuseStep 3931307 = 5896961) B5896961
theorem B2948447 : Blo 1746574 2948447 := bstep (se 1 (by rfl) ⟨2211335, by rfl⟩ : syracuseStep 2948447 = 4422671) B4422671
theorem B3317087 : Blo 1746574 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B6298985 : Blo 1746574 6298985 := bstep (se 2 (by rfl) ⟨2362119, by rfl⟩ : syracuseStep 6298985 = 4724239) B4724239
theorem B14925181 : Blo 1746574 14925181 := bstep (se 3 (by rfl) ⟨2798471, by rfl⟩ : syracuseStep 14925181 = 5596943) B5596943
theorem B1965487 : Blo 1746574 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B2620847 : Blo 1746574 2620847 := bstep (se 1 (by rfl) ⟨1965635, by rfl⟩ : syracuseStep 2620847 = 3931271) B3931271
theorem B2620937 : Blo 1746574 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B7462439 : Blo 1746574 7462439 := bstep (se 1 (by rfl) ⟨5596829, by rfl⟩ : syracuseStep 7462439 = 11193659) B11193659
theorem B2620967 : Blo 1746574 2620967 := bstep (se 1 (by rfl) ⟨1965725, by rfl⟩ : syracuseStep 2620967 = 3931451) B3931451
theorem B4423207 : Blo 1746574 4423207 := bstep (se 1 (by rfl) ⟨3317405, by rfl⟩ : syracuseStep 4423207 = 6634811) B6634811
theorem B3317345 : Blo 1746574 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B5897825 : Blo 1746574 5897825 := bstep (se 2 (by rfl) ⟨2211684, by rfl⟩ : syracuseStep 5897825 = 4423369) B4423369
theorem B7462523 : Blo 1746574 7462523 := bstep (se 1 (by rfl) ⟨5596892, by rfl⟩ : syracuseStep 7462523 = 11193785) B11193785
theorem B2621051 : Blo 1746574 2621051 := bstep (se 1 (by rfl) ⟨1965788, by rfl⟩ : syracuseStep 2621051 = 3931577) B3931577
theorem B3931847 : Blo 1746574 3931847 := bstep (se 1 (by rfl) ⟨2948885, by rfl⟩ : syracuseStep 3931847 = 5897771) B5897771
theorem B2621177 : Blo 1746574 2621177 := bstep (se 2 (by rfl) ⟨982941, by rfl⟩ : syracuseStep 2621177 = 1965883) B1965883
theorem B1965919 : Blo 1746574 1965919 := bstep (se 1 (by rfl) ⟨1474439, by rfl⟩ : syracuseStep 1965919 = 2948879) B2948879
theorem B2621279 : Blo 1746574 2621279 := bstep (se 1 (by rfl) ⟨1965959, by rfl⟩ : syracuseStep 2621279 = 3931919) B3931919
theorem B2621291 : Blo 1746574 2621291 := bstep (se 1 (by rfl) ⟨1965968, by rfl⟩ : syracuseStep 2621291 = 3931937) B3931937
theorem B3317611 : Blo 1746574 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B4423531 : Blo 1746574 4423531 := bstep (se 1 (by rfl) ⟨3317648, by rfl⟩ : syracuseStep 4423531 = 6635297) B6635297
theorem B22404995 : Blo 1746574 22404995 := bstep (se 1 (by rfl) ⟨16803746, by rfl⟩ : syracuseStep 22404995 = 33607493) B33607493
theorem B2949007 : Blo 1746574 2949007 := bstep (se 1 (by rfl) ⟨2211755, by rfl⟩ : syracuseStep 2949007 = 4423511) B4423511
theorem B9707521 : Blo 1746574 9707521 := bstep (se 2 (by rfl) ⟨3640320, by rfl⟩ : syracuseStep 9707521 = 7280641) B7280641
theorem B11960473 : Blo 1746574 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B7463123 : Blo 1746574 7463123 := bstep (se 1 (by rfl) ⟨5597342, by rfl⟩ : syracuseStep 7463123 = 11194685) B11194685
theorem B2949385 : Blo 1746574 2949385 := bstep (se 2 (by rfl) ⟨1106019, by rfl⟩ : syracuseStep 2949385 = 2212039) B2212039
theorem B2621705 : Blo 1746574 2621705 := bstep (se 2 (by rfl) ⟨983139, by rfl⟩ : syracuseStep 2621705 = 1966279) B1966279
theorem B16793905 : Blo 1746574 16793905 := bstep (se 2 (by rfl) ⟨6297714, by rfl⟩ : syracuseStep 16793905 = 12595429) B12595429
theorem B2621807 : Blo 1746574 2621807 := bstep (se 1 (by rfl) ⟨1966355, by rfl⟩ : syracuseStep 2621807 = 3932711) B3932711
theorem B1966459 : Blo 1746574 1966459 := bstep (se 1 (by rfl) ⟨1474844, by rfl⟩ : syracuseStep 1966459 = 2949689) B2949689
theorem B8847791 : Blo 1746574 8847791 := bstep (se 1 (by rfl) ⟨6635843, by rfl⟩ : syracuseStep 8847791 = 13271687) B13271687
theorem B6635951 : Blo 1746574 6635951 := bstep (se 1 (by rfl) ⟨4976963, by rfl⟩ : syracuseStep 6635951 = 9953927) B9953927
theorem B3318241 : Blo 1746574 3318241 := bstep (se 2 (by rfl) ⟨1244340, by rfl⟩ : syracuseStep 3318241 = 2488681) B2488681
theorem B9093683 : Blo 1746574 9093683 := bstep (se 1 (by rfl) ⟨6820262, by rfl⟩ : syracuseStep 9093683 = 13640525) B13640525
theorem B2622023 : Blo 1746574 2622023 := bstep (se 1 (by rfl) ⟨1966517, by rfl⟩ : syracuseStep 2622023 = 3933035) B3933035
theorem B2622059 : Blo 1746574 2622059 := bstep (se 1 (by rfl) ⟨1966544, by rfl⟩ : syracuseStep 2622059 = 3933089) B3933089
theorem B5898905 : Blo 1746574 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B3932855 : Blo 1746574 3932855 := bstep (se 1 (by rfl) ⟨2949641, by rfl⟩ : syracuseStep 3932855 = 5899283) B5899283
theorem B2212535 : Blo 1746574 2212535 := bstep (se 1 (by rfl) ⟨1659401, by rfl⟩ : syracuseStep 2212535 = 3318803) B3318803
theorem B8962759 : Blo 1746574 8962759 := bstep (se 1 (by rfl) ⟨6722069, by rfl⟩ : syracuseStep 8962759 = 13444139) B13444139
theorem B2622287 : Blo 1746574 2622287 := bstep (se 1 (by rfl) ⟨1966715, by rfl⟩ : syracuseStep 2622287 = 3933431) B3933431
theorem B2212687 : Blo 1746574 2212687 := bstep (se 1 (by rfl) ⟨1659515, by rfl⟩ : syracuseStep 2212687 = 3319031) B3319031
theorem B1966927 : Blo 1746574 1966927 := bstep (se 1 (by rfl) ⟨1475195, by rfl⟩ : syracuseStep 1966927 = 2950391) B2950391
theorem B3933071 : Blo 1746574 3933071 := bstep (se 1 (by rfl) ⟨2949803, by rfl⟩ : syracuseStep 3933071 = 5899607) B5899607
theorem B5596123 : Blo 1746574 5596123 := bstep (se 1 (by rfl) ⟨4197092, by rfl⟩ : syracuseStep 5596123 = 8394185) B8394185
theorem B4424827 : Blo 1746574 4424827 := bstep (se 1 (by rfl) ⟨3318620, by rfl⟩ : syracuseStep 4424827 = 6637241) B6637241
theorem B2622683 : Blo 1746574 2622683 := bstep (se 1 (by rfl) ⟨1967012, by rfl⟩ : syracuseStep 2622683 = 3934025) B3934025
theorem B16598249 : Blo 1746574 16598249 := bstep (se 2 (by rfl) ⟨6224343, by rfl⟩ : syracuseStep 16598249 = 12448687) B12448687
theorem B8848763 : Blo 1746574 8848763 := bstep (se 1 (by rfl) ⟨6636572, by rfl⟩ : syracuseStep 8848763 = 13273145) B13273145
theorem B6636923 : Blo 1746574 6636923 := bstep (se 1 (by rfl) ⟨4977692, by rfl⟩ : syracuseStep 6636923 = 9955385) B9955385
theorem B2622857 : Blo 1746574 2622857 := bstep (se 2 (by rfl) ⟨983571, by rfl⟩ : syracuseStep 2622857 = 1967143) B1967143
theorem B5981579 : Blo 1746574 5981579 := bstep (se 1 (by rfl) ⟨4486184, by rfl⟩ : syracuseStep 5981579 = 8972369) B8972369
theorem B3319289 : Blo 1746574 3319289 := bstep (se 2 (by rfl) ⟨1244733, by rfl⟩ : syracuseStep 3319289 = 2489467) B2489467
theorem B10774073 : Blo 1746574 10774073 := bstep (se 2 (by rfl) ⟨4040277, by rfl⟩ : syracuseStep 10774073 = 8080555) B8080555
theorem B3933791 : Blo 1746574 3933791 := bstep (se 1 (by rfl) ⟨2950343, by rfl⟩ : syracuseStep 3933791 = 5900687) B5900687
theorem B38823623 : Blo 1746574 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B1746655 : Blo 1746574 1746655 := bstep (se 1 (by rfl) ⟨1309991, by rfl⟩ : syracuseStep 1746655 = 2619983) B2619983
theorem B1746735 : Blo 1746574 1746735 := bstep (se 1 (by rfl) ⟨1310051, by rfl⟩ : syracuseStep 1746735 = 2620103) B2620103
theorem B3934007 : Blo 1746574 3934007 := bstep (se 1 (by rfl) ⟨2950505, by rfl⟩ : syracuseStep 3934007 = 5901011) B5901011
theorem B19900241 : Blo 1746574 19900241 := bstep (se 2 (by rfl) ⟨7462590, by rfl⟩ : syracuseStep 19900241 = 14925181) B14925181
theorem B14935913 : Blo 1746574 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B17926019 : Blo 1746574 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B1746843 : Blo 1746574 1746843 := bstep (se 1 (by rfl) ⟨1310132, by rfl⟩ : syracuseStep 1746843 = 2620265) B2620265
theorem B1746895 : Blo 1746574 1746895 := bstep (se 1 (by rfl) ⟨1310171, by rfl⟩ : syracuseStep 1746895 = 2620343) B2620343
theorem B8398799 : Blo 1746574 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B1746919 : Blo 1746574 1746919 := bstep (se 1 (by rfl) ⟨1310189, by rfl⟩ : syracuseStep 1746919 = 2620379) B2620379
theorem B51070961 : Blo 1746574 51070961 := bstep (se 2 (by rfl) ⟨19151610, by rfl⟩ : syracuseStep 51070961 = 38303221) B38303221
theorem B6637697 : Blo 1746574 6637697 := bstep (se 2 (by rfl) ⟨2489136, by rfl⟩ : syracuseStep 6637697 = 4978273) B4978273
theorem B5900417 : Blo 1746574 5900417 := bstep (se 2 (by rfl) ⟨2212656, by rfl⟩ : syracuseStep 5900417 = 4425313) B4425313
theorem B1747231 : Blo 1746574 1747231 := bstep (se 1 (by rfl) ⟨1310423, by rfl⟩ : syracuseStep 1747231 = 2620847) B2620847
theorem B1747291 : Blo 1746574 1747291 := bstep (se 1 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 1747291 = 2620937) B2620937
theorem B4974959 : Blo 1746574 4974959 := bstep (se 1 (by rfl) ⟨3731219, by rfl⟩ : syracuseStep 4974959 = 7462439) B7462439
theorem B1747311 : Blo 1746574 1747311 := bstep (se 1 (by rfl) ⟨1310483, by rfl⟩ : syracuseStep 1747311 = 2620967) B2620967
theorem B4975015 : Blo 1746574 4975015 := bstep (se 1 (by rfl) ⟨3731261, by rfl⟩ : syracuseStep 4975015 = 7462523) B7462523
theorem B1747367 : Blo 1746574 1747367 := bstep (se 1 (by rfl) ⟨1310525, by rfl⟩ : syracuseStep 1747367 = 2621051) B2621051
theorem B1747451 : Blo 1746574 1747451 := bstep (se 1 (by rfl) ⟨1310588, by rfl⟩ : syracuseStep 1747451 = 2621177) B2621177
theorem B5900795 : Blo 1746574 5900795 := bstep (se 1 (by rfl) ⟨4425596, by rfl⟩ : syracuseStep 5900795 = 8851193) B8851193
theorem B16804361 : Blo 1746574 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B1747519 : Blo 1746574 1747519 := bstep (se 1 (by rfl) ⟨1310639, by rfl⟩ : syracuseStep 1747519 = 2621279) B2621279
theorem B1747527 : Blo 1746574 1747527 := bstep (se 1 (by rfl) ⟨1310645, by rfl⟩ : syracuseStep 1747527 = 2621291) B2621291
theorem B14936663 : Blo 1746574 14936663 := bstep (se 1 (by rfl) ⟨11202497, by rfl⟩ : syracuseStep 14936663 = 22404995) B22404995
theorem B8850059 : Blo 1746574 8850059 := bstep (se 1 (by rfl) ⟨6637544, by rfl⟩ : syracuseStep 8850059 = 13275089) B13275089
theorem B1747679 : Blo 1746574 1747679 := bstep (se 1 (by rfl) ⟨1310759, by rfl⟩ : syracuseStep 1747679 = 2621519) B2621519
theorem B1747759 : Blo 1746574 1747759 := bstep (se 1 (by rfl) ⟨1310819, by rfl⟩ : syracuseStep 1747759 = 2621639) B2621639
theorem B7465871 : Blo 1746574 7465871 := bstep (se 1 (by rfl) ⟨5599403, by rfl⟩ : syracuseStep 7465871 = 11198807) B11198807
theorem B1747867 : Blo 1746574 1747867 := bstep (se 1 (by rfl) ⟨1310900, by rfl⟩ : syracuseStep 1747867 = 2621801) B2621801
theorem B5901227 : Blo 1746574 5901227 := bstep (se 1 (by rfl) ⟨4425920, by rfl⟩ : syracuseStep 5901227 = 8851841) B8851841
theorem B1747919 : Blo 1746574 1747919 := bstep (se 1 (by rfl) ⟨1310939, by rfl⟩ : syracuseStep 1747919 = 2621879) B2621879
theorem B1747943 : Blo 1746574 1747943 := bstep (se 1 (by rfl) ⟨1310957, by rfl⟩ : syracuseStep 1747943 = 2621915) B2621915
theorem B215305229 : Blo 1746574 215305229 := bstep (se 3 (by rfl) ⟨40369730, by rfl⟩ : syracuseStep 215305229 = 80739461) B80739461
theorem B7973903 : Blo 1746574 7973903 := bstep (se 1 (by rfl) ⟨5980427, by rfl⟩ : syracuseStep 7973903 = 11960855) B11960855
theorem B16796753 : Blo 1746574 16796753 := bstep (se 2 (by rfl) ⟨6298782, by rfl⟩ : syracuseStep 16796753 = 12597565) B12597565
theorem B4197575 : Blo 1746574 4197575 := bstep (se 1 (by rfl) ⟨3148181, by rfl⟩ : syracuseStep 4197575 = 6296363) B6296363
theorem B24235211 : Blo 1746574 24235211 := bstep (se 1 (by rfl) ⟨18176408, by rfl⟩ : syracuseStep 24235211 = 36352817) B36352817
theorem B1748255 : Blo 1746574 1748255 := bstep (se 1 (by rfl) ⟨1311191, by rfl⟩ : syracuseStep 1748255 = 2622383) B2622383
theorem B1748315 : Blo 1746574 1748315 := bstep (se 1 (by rfl) ⟨1311236, by rfl⟩ : syracuseStep 1748315 = 2622473) B2622473
theorem B1748335 : Blo 1746574 1748335 := bstep (se 1 (by rfl) ⟨1311251, by rfl⟩ : syracuseStep 1748335 = 2622503) B2622503
theorem B1748391 : Blo 1746574 1748391 := bstep (se 1 (by rfl) ⟨1311293, by rfl⟩ : syracuseStep 1748391 = 2622587) B2622587
theorem B3149255 : Blo 1746574 3149255 := bstep (se 1 (by rfl) ⟨2361941, by rfl⟩ : syracuseStep 3149255 = 4723883) B4723883
theorem B5598713 : Blo 1746574 5598713 := bstep (se 2 (by rfl) ⟨2099517, by rfl⟩ : syracuseStep 5598713 = 4199035) B4199035
theorem B1748475 : Blo 1746574 1748475 := bstep (se 1 (by rfl) ⟨1311356, by rfl⟩ : syracuseStep 1748475 = 2622713) B2622713
theorem B7466555 : Blo 1746574 7466555 := bstep (se 1 (by rfl) ⟨5599916, by rfl⟩ : syracuseStep 7466555 = 11199833) B11199833
theorem B1748543 : Blo 1746574 1748543 := bstep (se 1 (by rfl) ⟨1311407, by rfl⟩ : syracuseStep 1748543 = 2622815) B2622815
theorem B1748551 : Blo 1746574 1748551 := bstep (se 1 (by rfl) ⟨1311413, by rfl⟩ : syracuseStep 1748551 = 2622827) B2622827
theorem B6295121 : Blo 1746574 6295121 := bstep (se 2 (by rfl) ⟨2360670, by rfl⟩ : syracuseStep 6295121 = 4721341) B4721341
theorem B12594797 : Blo 1746574 12594797 := bstep (se 3 (by rfl) ⟨2361524, by rfl⟩ : syracuseStep 12594797 = 4723049) B4723049
theorem B5598983 : Blo 1746574 5598983 := bstep (se 1 (by rfl) ⟨4199237, by rfl⟩ : syracuseStep 5598983 = 8398475) B8398475
theorem B19910447 : Blo 1746574 19910447 := bstep (se 1 (by rfl) ⟨14932835, by rfl⟩ : syracuseStep 19910447 = 29865671) B29865671
theorem B7466813 : Blo 1746574 7466813 := bstep (se 3 (by rfl) ⟨1400027, by rfl⟩ : syracuseStep 7466813 = 2800055) B2800055
theorem B8843417 : Blo 1746574 8843417 := bstep (se 2 (by rfl) ⟨3316281, by rfl⟩ : syracuseStep 8843417 = 6632563) B6632563
theorem B129224909 : Blo 1746574 129224909 := bstep (se 3 (by rfl) ⟨24229670, by rfl⟩ : syracuseStep 129224909 = 48459341) B48459341
theorem B4722941 : Blo 1746574 4722941 := bstep (se 3 (by rfl) ⟨885551, by rfl⟩ : syracuseStep 4722941 = 1771103) B1771103
theorem B47804779 : Blo 1746574 47804779 := bstep (se 1 (by rfl) ⟨35853584, by rfl⟩ : syracuseStep 47804779 = 71707169) B71707169
theorem B8401259 : Blo 1746574 8401259 := bstep (se 1 (by rfl) ⟨6300944, by rfl⟩ : syracuseStep 8401259 = 12601889) B12601889
theorem B4485559 : Blo 1746574 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B7082497 : Blo 1746574 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B5313043 : Blo 1746574 5313043 := bstep (se 1 (by rfl) ⟨3984782, by rfl⟩ : syracuseStep 5313043 = 7969565) B7969565
theorem B5599763 : Blo 1746574 5599763 := bstep (se 1 (by rfl) ⟨4199822, by rfl⟩ : syracuseStep 5599763 = 8399645) B8399645
theorem B3363391 : Blo 1746574 3363391 := bstep (se 1 (by rfl) ⟨2522543, by rfl⟩ : syracuseStep 3363391 = 5045087) B5045087
theorem B4199323 : Blo 1746574 4199323 := bstep (se 1 (by rfl) ⟨3149492, by rfl⟩ : syracuseStep 4199323 = 6298985) B6298985
theorem B57480101 : Blo 1746574 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B8844227 : Blo 1746574 8844227 := bstep (se 1 (by rfl) ⟨6633170, by rfl⟩ : syracuseStep 8844227 = 13266341) B13266341
theorem B9450533 : Blo 1746574 9450533 := bstep (se 4 (by rfl) ⟨885987, by rfl⟩ : syracuseStep 9450533 = 1771975) B1771975
theorem B5600353 : Blo 1746574 5600353 := bstep (se 2 (by rfl) ⟨2100132, by rfl⟩ : syracuseStep 5600353 = 4200265) B4200265
theorem B37786985 : Blo 1746574 37786985 := bstep (se 2 (by rfl) ⟨14170119, by rfl⟩ : syracuseStep 37786985 = 28340239) B28340239
theorem B4421051 : Blo 1746574 4421051 := bstep (se 1 (by rfl) ⟨3315788, by rfl⟩ : syracuseStep 4421051 = 6631577) B6631577
theorem B22394333 : Blo 1746574 22394333 := bstep (se 3 (by rfl) ⟨4198937, by rfl⟩ : syracuseStep 22394333 = 8397875) B8397875
theorem B8402413 : Blo 1746574 8402413 := bstep (se 3 (by rfl) ⟨1575452, by rfl⟩ : syracuseStep 8402413 = 3150905) B3150905
theorem B2488043 : Blo 1746574 2488043 := bstep (se 1 (by rfl) ⟨1866032, by rfl⟩ : syracuseStep 2488043 = 3732065) B3732065
theorem B3929903 : Blo 1746574 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B8394785 : Blo 1746574 8394785 := bstep (se 2 (by rfl) ⟨3148044, by rfl⟩ : syracuseStep 8394785 = 6296089) B6296089
theorem B5601545 : Blo 1746574 5601545 := bstep (se 2 (by rfl) ⟨2100579, by rfl⟩ : syracuseStep 5601545 = 4201159) B4201159
theorem B3930479 : Blo 1746574 3930479 := bstep (se 1 (by rfl) ⟨2947859, by rfl⟩ : syracuseStep 3930479 = 5895719) B5895719
theorem B6633839 : Blo 1746574 6633839 := bstep (se 1 (by rfl) ⟨4975379, by rfl⟩ : syracuseStep 6633839 = 9950759) B9950759
theorem B2947495 : Blo 1746574 2947495 := bstep (se 1 (by rfl) ⟨2210621, by rfl⟩ : syracuseStep 2947495 = 4421243) B4421243
theorem B3930551 : Blo 1746574 3930551 := bstep (se 1 (by rfl) ⟨2947913, by rfl⟩ : syracuseStep 3930551 = 5895827) B5895827
theorem B2619899 : Blo 1746574 2619899 := bstep (se 1 (by rfl) ⟨1964924, by rfl⟩ : syracuseStep 2619899 = 3929849) B3929849
theorem B3930695 : Blo 1746574 3930695 := bstep (se 1 (by rfl) ⟨2948021, by rfl⟩ : syracuseStep 3930695 = 5896043) B5896043
theorem B4422215 : Blo 1746574 4422215 := bstep (se 1 (by rfl) ⟨3316661, by rfl⟩ : syracuseStep 4422215 = 6633323) B6633323
theorem B2947657 : Blo 1746574 2947657 := bstep (se 2 (by rfl) ⟨1105371, by rfl⟩ : syracuseStep 2947657 = 2210743) B2210743
theorem B3316297 : Blo 1746574 3316297 := bstep (se 2 (by rfl) ⟨1243611, by rfl⟩ : syracuseStep 3316297 = 2487223) B2487223
theorem B2947691 : Blo 1746574 2947691 := bstep (se 1 (by rfl) ⟨2210768, by rfl⟩ : syracuseStep 2947691 = 4421537) B4421537
theorem B3930731 : Blo 1746574 3930731 := bstep (se 1 (by rfl) ⟨2948048, by rfl⟩ : syracuseStep 3930731 = 5896097) B5896097
theorem B2620025 : Blo 1746574 2620025 := bstep (se 2 (by rfl) ⟨982509, by rfl⟩ : syracuseStep 2620025 = 1965019) B1965019
theorem B2620079 : Blo 1746574 2620079 := bstep (se 1 (by rfl) ⟨1965059, by rfl⟩ : syracuseStep 2620079 = 3930119) B3930119
theorem B2620127 : Blo 1746574 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B11951003 : Blo 1746574 11951003 := bstep (se 1 (by rfl) ⟨8963252, by rfl⟩ : syracuseStep 11951003 = 17926505) B17926505
theorem B6298523 : Blo 1746574 6298523 := bstep (se 1 (by rfl) ⟨4723892, by rfl⟩ : syracuseStep 6298523 = 9447785) B9447785
theorem B63790051 : Blo 1746574 63790051 := bstep (se 1 (by rfl) ⟨47842538, by rfl⟩ : syracuseStep 63790051 = 95685077) B95685077
theorem B2620391 : Blo 1746574 2620391 := bstep (se 1 (by rfl) ⟨1965293, by rfl⟩ : syracuseStep 2620391 = 3930587) B3930587
theorem B3931127 : Blo 1746574 3931127 := bstep (se 1 (by rfl) ⟨2948345, by rfl⟩ : syracuseStep 3931127 = 5896691) B5896691
theorem B5897339 : Blo 1746574 5897339 := bstep (se 1 (by rfl) ⟨4423004, by rfl⟩ : syracuseStep 5897339 = 8846009) B8846009
theorem B2620649 : Blo 1746574 2620649 := bstep (se 2 (by rfl) ⟨982743, by rfl⟩ : syracuseStep 2620649 = 1965487) B1965487
theorem B1965343 : Blo 1746574 1965343 := bstep (se 1 (by rfl) ⟨1474007, by rfl⟩ : syracuseStep 1965343 = 2948015) B2948015
theorem B2620703 : Blo 1746574 2620703 := bstep (se 1 (by rfl) ⟨1965527, by rfl⟩ : syracuseStep 2620703 = 3931055) B3931055
theorem B3931487 : Blo 1746574 3931487 := bstep (se 1 (by rfl) ⟨2948615, by rfl⟩ : syracuseStep 3931487 = 5897231) B5897231
theorem B5897609 : Blo 1746574 5897609 := bstep (se 2 (by rfl) ⟨2211603, by rfl⟩ : syracuseStep 5897609 = 4423207) B4423207
theorem B20733347 : Blo 1746574 20733347 := bstep (se 1 (by rfl) ⟨15550010, by rfl⟩ : syracuseStep 20733347 = 31100021) B31100021
theorem B2211239 : Blo 1746574 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B2620871 : Blo 1746574 2620871 := bstep (se 1 (by rfl) ⟨1965653, by rfl⟩ : syracuseStep 2620871 = 3931307) B3931307
theorem B22388183 : Blo 1746574 22388183 := bstep (se 1 (by rfl) ⟨16791137, by rfl⟩ : syracuseStep 22388183 = 33582275) B33582275
theorem B1965631 : Blo 1746574 1965631 := bstep (se 1 (by rfl) ⟨1474223, by rfl⟩ : syracuseStep 1965631 = 2948447) B2948447
theorem B2211391 : Blo 1746574 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B2211563 : Blo 1746574 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B3931883 : Blo 1746574 3931883 := bstep (se 1 (by rfl) ⟨2948912, by rfl⟩ : syracuseStep 3931883 = 5897825) B5897825
theorem B2621225 : Blo 1746574 2621225 := bstep (se 2 (by rfl) ⟨982959, by rfl⟩ : syracuseStep 2621225 = 1965919) B1965919
theorem B2621231 : Blo 1746574 2621231 := bstep (se 1 (by rfl) ⟨1965923, by rfl⟩ : syracuseStep 2621231 = 3931847) B3931847
theorem B4423481 : Blo 1746574 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B5898041 : Blo 1746574 5898041 := bstep (se 2 (by rfl) ⟨2211765, by rfl⟩ : syracuseStep 5898041 = 4423531) B4423531
theorem B3932009 : Blo 1746574 3932009 := bstep (se 2 (by rfl) ⟨1474503, by rfl⟩ : syracuseStep 3932009 = 2949007) B2949007
theorem B7462763 : Blo 1746574 7462763 := bstep (se 1 (by rfl) ⟨5597072, by rfl⟩ : syracuseStep 7462763 = 11194145) B11194145
theorem B12943361 : Blo 1746574 12943361 := bstep (se 2 (by rfl) ⟨4853760, by rfl⟩ : syracuseStep 12943361 = 9707521) B9707521
theorem B37773317 : Blo 1746574 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B5898527 : Blo 1746574 5898527 := bstep (se 1 (by rfl) ⟨4423895, by rfl⟩ : syracuseStep 5898527 = 8847791) B8847791
theorem B4423967 : Blo 1746574 4423967 := bstep (se 1 (by rfl) ⟨3317975, by rfl⟩ : syracuseStep 4423967 = 6635951) B6635951
theorem B3932513 : Blo 1746574 3932513 := bstep (se 2 (by rfl) ⟨1474692, by rfl⟩ : syracuseStep 3932513 = 2949385) B2949385
theorem B6062455 : Blo 1746574 6062455 := bstep (se 1 (by rfl) ⟨4546841, by rfl⟩ : syracuseStep 6062455 = 9093683) B9093683
theorem B3932603 : Blo 1746574 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B2621903 : Blo 1746574 2621903 := bstep (se 1 (by rfl) ⟨1966427, by rfl⟩ : syracuseStep 2621903 = 3932855) B3932855
theorem B2621945 : Blo 1746574 2621945 := bstep (se 2 (by rfl) ⟨983229, by rfl⟩ : syracuseStep 2621945 = 1966459) B1966459
theorem B64627229 : Blo 1746574 64627229 := bstep (se 3 (by rfl) ⟨12117605, by rfl⟩ : syracuseStep 64627229 = 24235211) B24235211
theorem B5980745 : Blo 1746574 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B2622047 : Blo 1746574 2622047 := bstep (se 1 (by rfl) ⟨1966535, by rfl⟩ : syracuseStep 2622047 = 3933071) B3933071
theorem B4424321 : Blo 1746574 4424321 := bstep (se 2 (by rfl) ⟨1659120, by rfl⟩ : syracuseStep 4424321 = 3318241) B3318241
theorem B6300355 : Blo 1746574 6300355 := bstep (se 1 (by rfl) ⟨4725266, by rfl⟩ : syracuseStep 6300355 = 9450533) B9450533
theorem B25191323 : Blo 1746574 25191323 := bstep (se 1 (by rfl) ⟨18893492, by rfl⟩ : syracuseStep 25191323 = 37786985) B37786985
theorem B5899175 : Blo 1746574 5899175 := bstep (se 1 (by rfl) ⟨4424381, by rfl⟩ : syracuseStep 5899175 = 8848763) B8848763
theorem B4424615 : Blo 1746574 4424615 := bstep (se 1 (by rfl) ⟨3318461, by rfl⟩ : syracuseStep 4424615 = 6636923) B6636923
theorem B2212859 : Blo 1746574 2212859 := bstep (se 1 (by rfl) ⟨1659644, by rfl⟩ : syracuseStep 2212859 = 3319289) B3319289
theorem B2622527 : Blo 1746574 2622527 := bstep (se 1 (by rfl) ⟨1966895, by rfl⟩ : syracuseStep 2622527 = 3933791) B3933791
theorem B55288925 : Blo 1746574 55288925 := bstep (se 3 (by rfl) ⟨10366673, by rfl⟩ : syracuseStep 55288925 = 20733347) B20733347
theorem B2950249 : Blo 1746574 2950249 := bstep (se 2 (by rfl) ⟨1106343, by rfl⟩ : syracuseStep 2950249 = 2212687) B2212687
theorem B2622569 : Blo 1746574 2622569 := bstep (se 2 (by rfl) ⟨983463, by rfl⟩ : syracuseStep 2622569 = 1966927) B1966927
theorem B2622671 : Blo 1746574 2622671 := bstep (se 1 (by rfl) ⟨1967003, by rfl⟩ : syracuseStep 2622671 = 3934007) B3934007
theorem B34047307 : Blo 1746574 34047307 := bstep (se 1 (by rfl) ⟨25535480, by rfl⟩ : syracuseStep 34047307 = 51070961) B51070961
theorem B5596523 : Blo 1746574 5596523 := bstep (se 1 (by rfl) ⟨4197392, by rfl⟩ : syracuseStep 5596523 = 8394785) B8394785
theorem B44811629 : Blo 1746574 44811629 := bstep (se 3 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 44811629 = 16804361) B16804361
theorem B4425131 : Blo 1746574 4425131 := bstep (se 1 (by rfl) ⟨3318848, by rfl⟩ : syracuseStep 4425131 = 6637697) B6637697
theorem B3933611 : Blo 1746574 3933611 := bstep (se 1 (by rfl) ⟨2950208, by rfl⟩ : syracuseStep 3933611 = 5900417) B5900417
theorem B28730861 : Blo 1746574 28730861 := bstep (se 3 (by rfl) ⟨5387036, by rfl⟩ : syracuseStep 28730861 = 10774073) B10774073
theorem B5899769 : Blo 1746574 5899769 := bstep (se 2 (by rfl) ⟨2212413, by rfl⟩ : syracuseStep 5899769 = 4424827) B4424827
theorem B1746599 : Blo 1746574 1746599 := bstep (se 1 (by rfl) ⟨1309949, by rfl⟩ : syracuseStep 1746599 = 2619899) B2619899
theorem B3933863 : Blo 1746574 3933863 := bstep (se 1 (by rfl) ⟨2950397, by rfl⟩ : syracuseStep 3933863 = 5900795) B5900795
theorem B1746683 : Blo 1746574 1746683 := bstep (se 1 (by rfl) ⟨1310012, by rfl⟩ : syracuseStep 1746683 = 2620025) B2620025
theorem B5900039 : Blo 1746574 5900039 := bstep (se 1 (by rfl) ⟨4425029, by rfl⟩ : syracuseStep 5900039 = 8850059) B8850059
theorem B1746719 : Blo 1746574 1746719 := bstep (se 1 (by rfl) ⟨1310039, by rfl⟩ : syracuseStep 1746719 = 2620079) B2620079
theorem B5900093 : Blo 1746574 5900093 := bstep (se 3 (by rfl) ⟨1106267, by rfl⟩ : syracuseStep 5900093 = 2212535) B2212535
theorem B1746751 : Blo 1746574 1746751 := bstep (se 1 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 1746751 = 2620127) B2620127
theorem B3934151 : Blo 1746574 3934151 := bstep (se 1 (by rfl) ⟨2950613, by rfl⟩ : syracuseStep 3934151 = 5901227) B5901227
theorem B1746927 : Blo 1746574 1746927 := bstep (se 1 (by rfl) ⟨1310195, by rfl⟩ : syracuseStep 1746927 = 2620391) B2620391
theorem B1747099 : Blo 1746574 1747099 := bstep (se 1 (by rfl) ⟨1310324, by rfl⟩ : syracuseStep 1747099 = 2620649) B2620649
theorem B1747135 : Blo 1746574 1747135 := bstep (se 1 (by rfl) ⟨1310351, by rfl⟩ : syracuseStep 1747135 = 2620703) B2620703
theorem B1747247 : Blo 1746574 1747247 := bstep (se 1 (by rfl) ⟨1310435, by rfl⟩ : syracuseStep 1747247 = 2620871) B2620871
theorem B2099503 : Blo 1746574 2099503 := bstep (se 1 (by rfl) ⟨1574627, by rfl⟩ : syracuseStep 2099503 = 3149255) B3149255
theorem B19908989 : Blo 1746574 19908989 := bstep (se 3 (by rfl) ⟨3732935, by rfl⟩ : syracuseStep 19908989 = 7465871) B7465871
theorem B4196747 : Blo 1746574 4196747 := bstep (se 1 (by rfl) ⟨3147560, by rfl⟩ : syracuseStep 4196747 = 6295121) B6295121
theorem B1747483 : Blo 1746574 1747483 := bstep (se 1 (by rfl) ⟨1310612, by rfl⟩ : syracuseStep 1747483 = 2621225) B2621225
theorem B1747487 : Blo 1746574 1747487 := bstep (se 1 (by rfl) ⟨1310615, by rfl⟩ : syracuseStep 1747487 = 2621231) B2621231
theorem B13273631 : Blo 1746574 13273631 := bstep (se 1 (by rfl) ⟨9955223, by rfl⟩ : syracuseStep 13273631 = 19910447) B19910447
theorem B4975175 : Blo 1746574 4975175 := bstep (se 1 (by rfl) ⟨3731381, by rfl⟩ : syracuseStep 4975175 = 7462763) B7462763
theorem B86149939 : Blo 1746574 86149939 := bstep (se 1 (by rfl) ⟨64612454, by rfl⟩ : syracuseStep 86149939 = 129224909) B129224909
theorem B4975415 : Blo 1746574 4975415 := bstep (se 1 (by rfl) ⟨3731561, by rfl⟩ : syracuseStep 4975415 = 7463123) B7463123
theorem B3148627 : Blo 1746574 3148627 := bstep (se 1 (by rfl) ⟨2361470, by rfl⟩ : syracuseStep 3148627 = 4722941) B4722941
theorem B1747803 : Blo 1746574 1747803 := bstep (se 1 (by rfl) ⟨1310852, by rfl⟩ : syracuseStep 1747803 = 2621705) B2621705
theorem B1747871 : Blo 1746574 1747871 := bstep (se 1 (by rfl) ⟨1310903, by rfl⟩ : syracuseStep 1747871 = 2621807) B2621807
theorem B1748015 : Blo 1746574 1748015 := bstep (se 1 (by rfl) ⟨1311011, by rfl⟩ : syracuseStep 1748015 = 2622023) B2622023
theorem B22391873 : Blo 1746574 22391873 := bstep (se 2 (by rfl) ⟨8396952, by rfl⟩ : syracuseStep 22391873 = 16793905) B16793905
theorem B1748039 : Blo 1746574 1748039 := bstep (se 1 (by rfl) ⟨1311029, by rfl⟩ : syracuseStep 1748039 = 2622059) B2622059
theorem B1748191 : Blo 1746574 1748191 := bstep (se 1 (by rfl) ⟨1311143, by rfl⟩ : syracuseStep 1748191 = 2622287) B2622287
theorem B4484521 : Blo 1746574 4484521 := bstep (se 2 (by rfl) ⟨1681695, by rfl⟩ : syracuseStep 4484521 = 3363391) B3363391
theorem B1748455 : Blo 1746574 1748455 := bstep (se 1 (by rfl) ⟨1311341, by rfl⟩ : syracuseStep 1748455 = 2622683) B2622683
theorem B1748571 : Blo 1746574 1748571 := bstep (se 1 (by rfl) ⟨1311428, by rfl⟩ : syracuseStep 1748571 = 2622857) B2622857
theorem B14929555 : Blo 1746574 14929555 := bstep (se 1 (by rfl) ⟨11197166, by rfl⟩ : syracuseStep 14929555 = 22394333) B22394333
theorem B25882415 : Blo 1746574 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B5599097 : Blo 1746574 5599097 := bstep (se 2 (by rfl) ⟨2099661, by rfl⟩ : syracuseStep 5599097 = 4199323) B4199323
theorem B13266827 : Blo 1746574 13266827 := bstep (se 1 (by rfl) ⟨9950120, by rfl⟩ : syracuseStep 13266827 = 19900241) B19900241
theorem B9957275 : Blo 1746574 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B85053401 : Blo 1746574 85053401 := bstep (se 2 (by rfl) ⟨31895025, by rfl⟩ : syracuseStep 85053401 = 63790051) B63790051
theorem B5599199 : Blo 1746574 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B7467137 : Blo 1746574 7467137 := bstep (se 2 (by rfl) ⟨2800176, by rfl⟩ : syracuseStep 7467137 = 5600353) B5600353
theorem B9957775 : Blo 1746574 9957775 := bstep (se 1 (by rfl) ⟨7468331, by rfl⟩ : syracuseStep 9957775 = 14936663) B14936663
theorem B7967335 : Blo 1746574 7967335 := bstep (se 1 (by rfl) ⟨5975501, by rfl⟩ : syracuseStep 7967335 = 11951003) B11951003
theorem B4199015 : Blo 1746574 4199015 := bstep (se 1 (by rfl) ⟨3149261, by rfl⟩ : syracuseStep 4199015 = 6298523) B6298523
theorem B11203217 : Blo 1746574 11203217 := bstep (se 2 (by rfl) ⟨4201206, by rfl⟩ : syracuseStep 11203217 = 8402413) B8402413
theorem B143536819 : Blo 1746574 143536819 := bstep (se 1 (by rfl) ⟨107652614, by rfl⟩ : syracuseStep 143536819 = 215305229) B215305229
theorem B2798383 : Blo 1746574 2798383 := bstep (se 1 (by rfl) ⟨2098787, by rfl⟩ : syracuseStep 2798383 = 4197575) B4197575
theorem B3732475 : Blo 1746574 3732475 := bstep (se 1 (by rfl) ⟨2799356, by rfl⟩ : syracuseStep 3732475 = 5598713) B5598713
theorem B4977703 : Blo 1746574 4977703 := bstep (se 1 (by rfl) ⟨3733277, by rfl⟩ : syracuseStep 4977703 = 7466555) B7466555
theorem B3732655 : Blo 1746574 3732655 := bstep (se 1 (by rfl) ⟨2799491, by rfl⟩ : syracuseStep 3732655 = 5598983) B5598983
theorem B4977875 : Blo 1746574 4977875 := bstep (se 1 (by rfl) ⟨3733406, by rfl⟩ : syracuseStep 4977875 = 7466813) B7466813
theorem B21263741 : Blo 1746574 21263741 := bstep (se 3 (by rfl) ⟨3986951, by rfl⟩ : syracuseStep 21263741 = 7973903) B7973903
theorem B5895611 : Blo 1746574 5895611 := bstep (se 1 (by rfl) ⟨4421708, by rfl⟩ : syracuseStep 5895611 = 8843417) B8843417
theorem B15947297 : Blo 1746574 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B5600839 : Blo 1746574 5600839 := bstep (se 1 (by rfl) ⟨4200629, by rfl⟩ : syracuseStep 5600839 = 8401259) B8401259
theorem B3733175 : Blo 1746574 3733175 := bstep (se 1 (by rfl) ⟨2799881, by rfl⟩ : syracuseStep 3733175 = 5599763) B5599763
theorem B63739705 : Blo 1746574 63739705 := bstep (se 2 (by rfl) ⟨23902389, by rfl⟩ : syracuseStep 63739705 = 47804779) B47804779
theorem B3929993 : Blo 1746574 3929993 := bstep (se 2 (by rfl) ⟨1473747, by rfl⟩ : syracuseStep 3929993 = 2947495) B2947495
theorem B6633353 : Blo 1746574 6633353 := bstep (se 2 (by rfl) ⟨2487507, by rfl⟩ : syracuseStep 6633353 = 4975015) B4975015
theorem B38320067 : Blo 1746574 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B5896151 : Blo 1746574 5896151 := bstep (se 1 (by rfl) ⟨4422113, by rfl⟩ : syracuseStep 5896151 = 8844227) B8844227
theorem B7084057 : Blo 1746574 7084057 := bstep (se 2 (by rfl) ⟨2656521, by rfl⟩ : syracuseStep 7084057 = 5313043) B5313043
theorem B3930209 : Blo 1746574 3930209 := bstep (se 2 (by rfl) ⟨1473828, by rfl⟩ : syracuseStep 3930209 = 2947657) B2947657
theorem B4421729 : Blo 1746574 4421729 := bstep (se 2 (by rfl) ⟨1658148, by rfl⟩ : syracuseStep 4421729 = 3316297) B3316297
theorem B11065499 : Blo 1746574 11065499 := bstep (se 1 (by rfl) ⟨8299124, by rfl⟩ : syracuseStep 11065499 = 16598249) B16598249
theorem B3987719 : Blo 1746574 3987719 := bstep (se 1 (by rfl) ⟨2990789, by rfl⟩ : syracuseStep 3987719 = 5981579) B5981579
theorem B11950345 : Blo 1746574 11950345 := bstep (se 2 (by rfl) ⟨4481379, by rfl⟩ : syracuseStep 11950345 = 8962759) B8962759
theorem B2947367 : Blo 1746574 2947367 := bstep (se 1 (by rfl) ⟨2210525, by rfl⟩ : syracuseStep 2947367 = 4421051) B4421051
theorem B5896637 : Blo 1746574 5896637 := bstep (se 3 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 5896637 = 2211239) B2211239
theorem B2619935 : Blo 1746574 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B11950679 : Blo 1746574 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B7461497 : Blo 1746574 7461497 := bstep (se 2 (by rfl) ⟨2798061, by rfl⟩ : syracuseStep 7461497 = 5596123) B5596123
theorem B3734363 : Blo 1746574 3734363 := bstep (se 1 (by rfl) ⟨2800772, by rfl⟩ : syracuseStep 3734363 = 5601545) B5601545
theorem B2620319 : Blo 1746574 2620319 := bstep (se 1 (by rfl) ⟨1965239, by rfl⟩ : syracuseStep 2620319 = 3930479) B3930479
theorem B3316639 : Blo 1746574 3316639 := bstep (se 1 (by rfl) ⟨2487479, by rfl⟩ : syracuseStep 3316639 = 4974959) B4974959
theorem B4422559 : Blo 1746574 4422559 := bstep (se 1 (by rfl) ⟨3316919, by rfl⟩ : syracuseStep 4422559 = 6633839) B6633839
theorem B2620367 : Blo 1746574 2620367 := bstep (se 1 (by rfl) ⟨1965275, by rfl⟩ : syracuseStep 2620367 = 3930551) B3930551
theorem B2620457 : Blo 1746574 2620457 := bstep (se 2 (by rfl) ⟨982671, by rfl⟩ : syracuseStep 2620457 = 1965343) B1965343
theorem B2620463 : Blo 1746574 2620463 := bstep (se 1 (by rfl) ⟨1965347, by rfl⟩ : syracuseStep 2620463 = 3930695) B3930695
theorem B2948143 : Blo 1746574 2948143 := bstep (se 1 (by rfl) ⟨2211107, by rfl⟩ : syracuseStep 2948143 = 4422215) B4422215
theorem B1965127 : Blo 1746574 1965127 := bstep (se 1 (by rfl) ⟨1473845, by rfl⟩ : syracuseStep 1965127 = 2947691) B2947691
theorem B2620487 : Blo 1746574 2620487 := bstep (se 1 (by rfl) ⟨1965365, by rfl⟩ : syracuseStep 2620487 = 3930731) B3930731
theorem B5897501 : Blo 1746574 5897501 := bstep (se 3 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 5897501 = 2211563) B2211563
theorem B6634781 : Blo 1746574 6634781 := bstep (se 3 (by rfl) ⟨1244021, by rfl⟩ : syracuseStep 6634781 = 2488043) B2488043
theorem B2620751 : Blo 1746574 2620751 := bstep (se 1 (by rfl) ⟨1965563, by rfl⟩ : syracuseStep 2620751 = 3931127) B3931127
theorem B11197835 : Blo 1746574 11197835 := bstep (se 1 (by rfl) ⟨8398376, by rfl⟩ : syracuseStep 11197835 = 16796753) B16796753
theorem B3931559 : Blo 1746574 3931559 := bstep (se 1 (by rfl) ⟨2948669, by rfl⟩ : syracuseStep 3931559 = 5897339) B5897339
theorem B2620841 : Blo 1746574 2620841 := bstep (se 2 (by rfl) ⟨982815, by rfl⟩ : syracuseStep 2620841 = 1965631) B1965631
theorem B2948521 : Blo 1746574 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B2620991 : Blo 1746574 2620991 := bstep (se 1 (by rfl) ⟨1965743, by rfl⟩ : syracuseStep 2620991 = 3931487) B3931487
theorem B3931739 : Blo 1746574 3931739 := bstep (se 1 (by rfl) ⟨2948804, by rfl⟩ : syracuseStep 3931739 = 5897609) B5897609
theorem B14925455 : Blo 1746574 14925455 := bstep (se 1 (by rfl) ⟨11194091, by rfl⟩ : syracuseStep 14925455 = 22388183) B22388183
theorem B8396531 : Blo 1746574 8396531 := bstep (se 1 (by rfl) ⟨6297398, by rfl⟩ : syracuseStep 8396531 = 12594797) B12594797
theorem B2621255 : Blo 1746574 2621255 := bstep (se 1 (by rfl) ⟨1965941, by rfl⟩ : syracuseStep 2621255 = 3931883) B3931883
theorem B2948987 : Blo 1746574 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B3932027 : Blo 1746574 3932027 := bstep (se 1 (by rfl) ⟨2949020, by rfl⟩ : syracuseStep 3932027 = 5898041) B5898041
theorem B2621339 : Blo 1746574 2621339 := bstep (se 1 (by rfl) ⟨1966004, by rfl⟩ : syracuseStep 2621339 = 3932009) B3932009
theorem B25182211 : Blo 1746574 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B9445409 : Blo 1746574 9445409 := bstep (se 2 (by rfl) ⟨3542028, by rfl⟩ : syracuseStep 9445409 = 7084057) B7084057
theorem B3932351 : Blo 1746574 3932351 := bstep (se 1 (by rfl) ⟨2949263, by rfl⟩ : syracuseStep 3932351 = 5898527) B5898527
theorem B2949311 : Blo 1746574 2949311 := bstep (se 1 (by rfl) ⟨2211983, by rfl⟩ : syracuseStep 2949311 = 4423967) B4423967
theorem B2621675 : Blo 1746574 2621675 := bstep (se 1 (by rfl) ⟨1966256, by rfl⟩ : syracuseStep 2621675 = 3932513) B3932513
theorem B2621735 : Blo 1746574 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B2949547 : Blo 1746574 2949547 := bstep (se 1 (by rfl) ⟨2212160, by rfl⟩ : syracuseStep 2949547 = 4424321) B4424321
theorem B16794215 : Blo 1746574 16794215 := bstep (se 1 (by rfl) ⟨12595661, by rfl⟩ : syracuseStep 16794215 = 25191323) B25191323
theorem B3932783 : Blo 1746574 3932783 := bstep (se 1 (by rfl) ⟨2949587, by rfl⟩ : syracuseStep 3932783 = 5899175) B5899175
theorem B2949743 : Blo 1746574 2949743 := bstep (se 1 (by rfl) ⟨2212307, by rfl⟩ : syracuseStep 2949743 = 4424615) B4424615
theorem B3318583 : Blo 1746574 3318583 := bstep (se 1 (by rfl) ⟨2488937, by rfl⟩ : syracuseStep 3318583 = 4977875) B4977875
theorem B191382425 : Blo 1746574 191382425 := bstep (se 2 (by rfl) ⟨71768409, by rfl⟩ : syracuseStep 191382425 = 143536819) B143536819
theorem B2950087 : Blo 1746574 2950087 := bstep (se 1 (by rfl) ⟨2212565, by rfl⟩ : syracuseStep 2950087 = 4425131) B4425131
theorem B2622407 : Blo 1746574 2622407 := bstep (se 1 (by rfl) ⟨1966805, by rfl⟩ : syracuseStep 2622407 = 3933611) B3933611
theorem B19153907 : Blo 1746574 19153907 := bstep (se 1 (by rfl) ⟨14365430, by rfl⟩ : syracuseStep 19153907 = 28730861) B28730861
theorem B3933179 : Blo 1746574 3933179 := bstep (se 1 (by rfl) ⟨2949884, by rfl⟩ : syracuseStep 3933179 = 5899769) B5899769
theorem B2622575 : Blo 1746574 2622575 := bstep (se 1 (by rfl) ⟨1966931, by rfl⟩ : syracuseStep 2622575 = 3933863) B3933863
theorem B3933359 : Blo 1746574 3933359 := bstep (se 1 (by rfl) ⟨2950019, by rfl⟩ : syracuseStep 3933359 = 5900039) B5900039
theorem B3933395 : Blo 1746574 3933395 := bstep (se 1 (by rfl) ⟨2950046, by rfl⟩ : syracuseStep 3933395 = 5900093) B5900093
theorem B2622767 : Blo 1746574 2622767 := bstep (se 1 (by rfl) ⟨1967075, by rfl⟩ : syracuseStep 2622767 = 3934151) B3934151
theorem B63735173 : Blo 1746574 63735173 := bstep (se 4 (by rfl) ⟨5975172, by rfl⟩ : syracuseStep 63735173 = 11950345) B11950345
theorem B6636937 : Blo 1746574 6636937 := bstep (se 2 (by rfl) ⟨2488851, by rfl⟩ : syracuseStep 6636937 = 4977703) B4977703
theorem B3933665 : Blo 1746574 3933665 := bstep (se 2 (by rfl) ⟨1475124, by rfl⟩ : syracuseStep 3933665 = 2950249) B2950249
theorem B13272659 : Blo 1746574 13272659 := bstep (se 1 (by rfl) ⟨9954494, by rfl⟩ : syracuseStep 13272659 = 19908989) B19908989
theorem B1746623 : Blo 1746574 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B8849087 : Blo 1746574 8849087 := bstep (se 1 (by rfl) ⟨6636815, by rfl⟩ : syracuseStep 8849087 = 13273631) B13273631
theorem B9955133 : Blo 1746574 9955133 := bstep (se 3 (by rfl) ⟨1866587, by rfl⟩ : syracuseStep 9955133 = 3733175) B3733175
theorem B1746879 : Blo 1746574 1746879 := bstep (se 1 (by rfl) ⟨1310159, by rfl⟩ : syracuseStep 1746879 = 2620319) B2620319
theorem B1746911 : Blo 1746574 1746911 := bstep (se 1 (by rfl) ⟨1310183, by rfl⟩ : syracuseStep 1746911 = 2620367) B2620367
theorem B1746971 : Blo 1746574 1746971 := bstep (se 1 (by rfl) ⟨1310228, by rfl⟩ : syracuseStep 1746971 = 2620457) B2620457
theorem B1746975 : Blo 1746574 1746975 := bstep (se 1 (by rfl) ⟨1310231, by rfl⟩ : syracuseStep 1746975 = 2620463) B2620463
theorem B14927915 : Blo 1746574 14927915 := bstep (se 1 (by rfl) ⟨11195936, by rfl⟩ : syracuseStep 14927915 = 22391873) B22391873
theorem B1746991 : Blo 1746574 1746991 := bstep (se 1 (by rfl) ⟨1310243, by rfl⟩ : syracuseStep 1746991 = 2620487) B2620487
theorem B1747167 : Blo 1746574 1747167 := bstep (se 1 (by rfl) ⟨1310375, by rfl⟩ : syracuseStep 1747167 = 2620751) B2620751
theorem B7465223 : Blo 1746574 7465223 := bstep (se 1 (by rfl) ⟨5598917, by rfl⟩ : syracuseStep 7465223 = 11197835) B11197835
theorem B1747227 : Blo 1746574 1747227 := bstep (se 1 (by rfl) ⟨1310420, by rfl⟩ : syracuseStep 1747227 = 2620841) B2620841
theorem B1747327 : Blo 1746574 1747327 := bstep (se 1 (by rfl) ⟨1310495, by rfl⟩ : syracuseStep 1747327 = 2620991) B2620991
theorem B84986273 : Blo 1746574 84986273 := bstep (se 2 (by rfl) ⟨31869852, by rfl⟩ : syracuseStep 84986273 = 63739705) B63739705
theorem B5597687 : Blo 1746574 5597687 := bstep (se 1 (by rfl) ⟨4198265, by rfl⟩ : syracuseStep 5597687 = 8396531) B8396531
theorem B17254943 : Blo 1746574 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B1747503 : Blo 1746574 1747503 := bstep (se 1 (by rfl) ⟨1310627, by rfl⟩ : syracuseStep 1747503 = 2621255) B2621255
theorem B1747559 : Blo 1746574 1747559 := bstep (se 1 (by rfl) ⟨1310669, by rfl⟩ : syracuseStep 1747559 = 2621339) B2621339
theorem B6638183 : Blo 1746574 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B5900957 : Blo 1746574 5900957 := bstep (se 3 (by rfl) ⟨1106429, by rfl⟩ : syracuseStep 5900957 = 2212859) B2212859
theorem B34515629 : Blo 1746574 34515629 := bstep (se 3 (by rfl) ⟨6471680, by rfl⟩ : syracuseStep 34515629 = 12943361) B12943361
theorem B1747935 : Blo 1746574 1747935 := bstep (se 1 (by rfl) ⟨1310951, by rfl⟩ : syracuseStep 1747935 = 2621903) B2621903
theorem B1747963 : Blo 1746574 1747963 := bstep (se 1 (by rfl) ⟨1310972, by rfl⟩ : syracuseStep 1747963 = 2621945) B2621945
theorem B43084819 : Blo 1746574 43084819 := bstep (se 1 (by rfl) ⟨32313614, by rfl⟩ : syracuseStep 43084819 = 64627229) B64627229
theorem B1748031 : Blo 1746574 1748031 := bstep (se 1 (by rfl) ⟨1311023, by rfl⟩ : syracuseStep 1748031 = 2622047) B2622047
theorem B1748351 : Blo 1746574 1748351 := bstep (se 1 (by rfl) ⟨1311263, by rfl⟩ : syracuseStep 1748351 = 2622527) B2622527
theorem B36859283 : Blo 1746574 36859283 := bstep (se 1 (by rfl) ⟨27644462, by rfl⟩ : syracuseStep 36859283 = 55288925) B55288925
theorem B1748379 : Blo 1746574 1748379 := bstep (se 1 (by rfl) ⟨1311284, by rfl⟩ : syracuseStep 1748379 = 2622569) B2622569
theorem B1748447 : Blo 1746574 1748447 := bstep (se 1 (by rfl) ⟨1311335, by rfl⟩ : syracuseStep 1748447 = 2622671) B2622671
theorem B3731015 : Blo 1746574 3731015 := bstep (se 1 (by rfl) ⟨2798261, by rfl⟩ : syracuseStep 3731015 = 5596523) B5596523
theorem B14175827 : Blo 1746574 14175827 := bstep (se 1 (by rfl) ⟨10631870, by rfl⟩ : syracuseStep 14175827 = 21263741) B21263741
theorem B8400473 : Blo 1746574 8400473 := bstep (se 2 (by rfl) ⟨3150177, by rfl⟩ : syracuseStep 8400473 = 6300355) B6300355
theorem B3731177 : Blo 1746574 3731177 := bstep (se 2 (by rfl) ⟨1399191, by rfl⟩ : syracuseStep 3731177 = 2798383) B2798383
theorem B4198169 : Blo 1746574 4198169 := bstep (se 2 (by rfl) ⟨1574313, by rfl⟩ : syracuseStep 4198169 = 3148627) B3148627
theorem B25546711 : Blo 1746574 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B4976633 : Blo 1746574 4976633 := bstep (se 2 (by rfl) ⟨1866237, by rfl⟩ : syracuseStep 4976633 = 3732475) B3732475
theorem B7376999 : Blo 1746574 7376999 := bstep (se 1 (by rfl) ⟨5532749, by rfl⟩ : syracuseStep 7376999 = 11065499) B11065499
theorem B2658479 : Blo 1746574 2658479 := bstep (se 1 (by rfl) ⟨1993859, by rfl⟩ : syracuseStep 2658479 = 3987719) B3987719
theorem B4976873 : Blo 1746574 4976873 := bstep (se 2 (by rfl) ⟨1866327, by rfl⟩ : syracuseStep 4976873 = 3732655) B3732655
theorem B2797831 : Blo 1746574 2797831 := bstep (se 1 (by rfl) ⟨2098373, by rfl⟩ : syracuseStep 2797831 = 4196747) B4196747
theorem B7967119 : Blo 1746574 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B45396409 : Blo 1746574 45396409 := bstep (se 2 (by rfl) ⟨17023653, by rfl⟩ : syracuseStep 45396409 = 34047307) B34047307
theorem B7467785 : Blo 1746574 7467785 := bstep (se 2 (by rfl) ⟨2800419, by rfl⟩ : syracuseStep 7467785 = 5600839) B5600839
theorem B9958301 : Blo 1746574 9958301 := bstep (se 3 (by rfl) ⟨1867181, by rfl⟩ : syracuseStep 9958301 = 3734363) B3734363
theorem B9950303 : Blo 1746574 9950303 := bstep (se 1 (by rfl) ⟨7462727, by rfl⟩ : syracuseStep 9950303 = 14925455) B14925455
theorem B3732731 : Blo 1746574 3732731 := bstep (se 1 (by rfl) ⟨2799548, by rfl⟩ : syracuseStep 3732731 = 5599097) B5599097
theorem B8844551 : Blo 1746574 8844551 := bstep (se 1 (by rfl) ⟨6633413, by rfl⟩ : syracuseStep 8844551 = 13266827) B13266827
theorem B56702267 : Blo 1746574 56702267 := bstep (se 1 (by rfl) ⟨42526700, by rfl⟩ : syracuseStep 56702267 = 85053401) B85053401
theorem B3732799 : Blo 1746574 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B4978091 : Blo 1746574 4978091 := bstep (se 1 (by rfl) ⟨3733568, by rfl⟩ : syracuseStep 4978091 = 7467137) B7467137
theorem B3987163 : Blo 1746574 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B2799343 : Blo 1746574 2799343 := bstep (se 1 (by rfl) ⟨2099507, by rfl⟩ : syracuseStep 2799343 = 4199015) B4199015
theorem B7468811 : Blo 1746574 7468811 := bstep (se 1 (by rfl) ⟨5601608, by rfl⟩ : syracuseStep 7468811 = 11203217) B11203217
theorem B8083273 : Blo 1746574 8083273 := bstep (se 2 (by rfl) ⟨3031227, by rfl⟩ : syracuseStep 8083273 = 6062455) B6062455
theorem B13277033 : Blo 1746574 13277033 := bstep (se 2 (by rfl) ⟨4978887, by rfl⟩ : syracuseStep 13277033 = 9957775) B9957775
theorem B10623113 : Blo 1746574 10623113 := bstep (se 2 (by rfl) ⟨3983667, by rfl⟩ : syracuseStep 10623113 = 7967335) B7967335
theorem B29874419 : Blo 1746574 29874419 := bstep (se 1 (by rfl) ⟨22405814, by rfl⟩ : syracuseStep 29874419 = 44811629) B44811629
theorem B3930407 : Blo 1746574 3930407 := bstep (se 1 (by rfl) ⟨2947805, by rfl⟩ : syracuseStep 3930407 = 5895611) B5895611
theorem B10631531 : Blo 1746574 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B114866585 : Blo 1746574 114866585 := bstep (se 2 (by rfl) ⟨43074969, by rfl⟩ : syracuseStep 114866585 = 86149939) B86149939
theorem B4422185 : Blo 1746574 4422185 := bstep (se 2 (by rfl) ⟨1658319, by rfl⟩ : syracuseStep 4422185 = 3316639) B3316639
theorem B5896745 : Blo 1746574 5896745 := bstep (se 2 (by rfl) ⟨2211279, by rfl⟩ : syracuseStep 5896745 = 4422559) B4422559
theorem B2619995 : Blo 1746574 2619995 := bstep (se 1 (by rfl) ⟨1964996, by rfl⟩ : syracuseStep 2619995 = 3929993) B3929993
theorem B4422235 : Blo 1746574 4422235 := bstep (se 1 (by rfl) ⟨3316676, by rfl⟩ : syracuseStep 4422235 = 6633353) B6633353
theorem B3930767 : Blo 1746574 3930767 := bstep (se 1 (by rfl) ⟨2948075, by rfl⟩ : syracuseStep 3930767 = 5896151) B5896151
theorem B3930857 : Blo 1746574 3930857 := bstep (se 2 (by rfl) ⟨1474071, by rfl⟩ : syracuseStep 3930857 = 2948143) B2948143
theorem B2620139 : Blo 1746574 2620139 := bstep (se 1 (by rfl) ⟨1965104, by rfl⟩ : syracuseStep 2620139 = 3930209) B3930209
theorem B2947819 : Blo 1746574 2947819 := bstep (se 1 (by rfl) ⟨2210864, by rfl⟩ : syracuseStep 2947819 = 4421729) B4421729
theorem B2620169 : Blo 1746574 2620169 := bstep (se 2 (by rfl) ⟨982563, by rfl⟩ : syracuseStep 2620169 = 1965127) B1965127
theorem B1964911 : Blo 1746574 1964911 := bstep (se 1 (by rfl) ⟨1473683, by rfl⟩ : syracuseStep 1964911 = 2947367) B2947367
theorem B11197349 : Blo 1746574 11197349 := bstep (se 4 (by rfl) ⟨1049751, by rfl⟩ : syracuseStep 11197349 = 2099503) B2099503
theorem B3931091 : Blo 1746574 3931091 := bstep (se 1 (by rfl) ⟨2948318, by rfl⟩ : syracuseStep 3931091 = 5896637) B5896637
theorem B19897325 : Blo 1746574 19897325 := bstep (se 3 (by rfl) ⟨3730748, by rfl⟩ : syracuseStep 19897325 = 7461497) B7461497
theorem B3316783 : Blo 1746574 3316783 := bstep (se 1 (by rfl) ⟨2487587, by rfl⟩ : syracuseStep 3316783 = 4975175) B4975175
theorem B3316943 : Blo 1746574 3316943 := bstep (se 1 (by rfl) ⟨2487707, by rfl⟩ : syracuseStep 3316943 = 4975415) B4975415
theorem B3931361 : Blo 1746574 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B5979361 : Blo 1746574 5979361 := bstep (se 2 (by rfl) ⟨2242260, by rfl⟩ : syracuseStep 5979361 = 4484521) B4484521
theorem B3931667 : Blo 1746574 3931667 := bstep (se 1 (by rfl) ⟨2948750, by rfl⟩ : syracuseStep 3931667 = 5897501) B5897501
theorem B4423187 : Blo 1746574 4423187 := bstep (se 1 (by rfl) ⟨3317390, by rfl⟩ : syracuseStep 4423187 = 6634781) B6634781
theorem B19906073 : Blo 1746574 19906073 := bstep (se 2 (by rfl) ⟨7464777, by rfl⟩ : syracuseStep 19906073 = 14929555) B14929555
theorem B2621039 : Blo 1746574 2621039 := bstep (se 1 (by rfl) ⟨1965779, by rfl⟩ : syracuseStep 2621039 = 3931559) B3931559
theorem B2621159 : Blo 1746574 2621159 := bstep (se 1 (by rfl) ⟨1965869, by rfl⟩ : syracuseStep 2621159 = 3931739) B3931739
theorem B1965991 : Blo 1746574 1965991 := bstep (se 1 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 1965991 = 2948987) B2948987
theorem B2621351 : Blo 1746574 2621351 := bstep (se 1 (by rfl) ⟨1966013, by rfl⟩ : syracuseStep 2621351 = 3932027) B3932027
theorem B2621567 : Blo 1746574 2621567 := bstep (se 1 (by rfl) ⟨1966175, by rfl⟩ : syracuseStep 2621567 = 3932351) B3932351
theorem B1966207 : Blo 1746574 1966207 := bstep (se 1 (by rfl) ⟨1474655, by rfl⟩ : syracuseStep 1966207 = 2949311) B2949311
theorem B3317915 : Blo 1746574 3317915 := bstep (se 1 (by rfl) ⟨2488436, by rfl⟩ : syracuseStep 3317915 = 4976873) B4976873
theorem B2621855 : Blo 1746574 2621855 := bstep (se 1 (by rfl) ⟨1966391, by rfl⟩ : syracuseStep 2621855 = 3932783) B3932783
theorem B1966495 : Blo 1746574 1966495 := bstep (se 1 (by rfl) ⟨1474871, by rfl⟩ : syracuseStep 1966495 = 2949743) B2949743
theorem B3932729 : Blo 1746574 3932729 := bstep (se 2 (by rfl) ⟨1474773, by rfl⟩ : syracuseStep 3932729 = 2949547) B2949547
theorem B2622119 : Blo 1746574 2622119 := bstep (se 1 (by rfl) ⟨1966589, by rfl⟩ : syracuseStep 2622119 = 3933179) B3933179
theorem B2622239 : Blo 1746574 2622239 := bstep (se 1 (by rfl) ⟨1966679, by rfl⟩ : syracuseStep 2622239 = 3933359) B3933359
theorem B2622263 : Blo 1746574 2622263 := bstep (se 1 (by rfl) ⟨1966697, by rfl⟩ : syracuseStep 2622263 = 3933395) B3933395
theorem B3318727 : Blo 1746574 3318727 := bstep (se 1 (by rfl) ⟨2489045, by rfl⟩ : syracuseStep 3318727 = 4978091) B4978091
theorem B2622443 : Blo 1746574 2622443 := bstep (se 1 (by rfl) ⟨1966832, by rfl⟩ : syracuseStep 2622443 = 3933665) B3933665
theorem B8848439 : Blo 1746574 8848439 := bstep (se 1 (by rfl) ⟨6636329, by rfl⟩ : syracuseStep 8848439 = 13272659) B13272659
theorem B4424777 : Blo 1746574 4424777 := bstep (se 2 (by rfl) ⟨1659291, by rfl⟩ : syracuseStep 4424777 = 3318583) B3318583
theorem B5899391 : Blo 1746574 5899391 := bstep (se 1 (by rfl) ⟨4424543, by rfl⟩ : syracuseStep 5899391 = 8849087) B8849087
theorem B6636755 : Blo 1746574 6636755 := bstep (se 1 (by rfl) ⟨4977566, by rfl⟩ : syracuseStep 6636755 = 9955133) B9955133
theorem B3933449 : Blo 1746574 3933449 := bstep (se 2 (by rfl) ⟨1475043, by rfl⟩ : syracuseStep 3933449 = 2950087) B2950087
theorem B14927165 : Blo 1746574 14927165 := bstep (se 3 (by rfl) ⟨2798843, by rfl⟩ : syracuseStep 14927165 = 5597687) B5597687
theorem B19916279 : Blo 1746574 19916279 := bstep (se 1 (by rfl) ⟨14937209, by rfl⟩ : syracuseStep 19916279 = 29874419) B29874419
theorem B56657515 : Blo 1746574 56657515 := bstep (se 1 (by rfl) ⟨42493136, by rfl⟩ : syracuseStep 56657515 = 84986273) B84986273
theorem B7972481 : Blo 1746574 7972481 := bstep (se 2 (by rfl) ⟨2989680, by rfl⟩ : syracuseStep 7972481 = 5979361) B5979361
theorem B11503295 : Blo 1746574 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B1746663 : Blo 1746574 1746663 := bstep (se 1 (by rfl) ⟨1309997, by rfl⟩ : syracuseStep 1746663 = 2619995) B2619995
theorem B4425455 : Blo 1746574 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B3933971 : Blo 1746574 3933971 := bstep (se 1 (by rfl) ⟨2950478, by rfl⟩ : syracuseStep 3933971 = 5900957) B5900957
theorem B1746759 : Blo 1746574 1746759 := bstep (se 1 (by rfl) ⟨1310069, by rfl⟩ : syracuseStep 1746759 = 2620139) B2620139
theorem B1746779 : Blo 1746574 1746779 := bstep (se 1 (by rfl) ⟨1310084, by rfl⟩ : syracuseStep 1746779 = 2620169) B2620169
theorem B8849249 : Blo 1746574 8849249 := bstep (se 2 (by rfl) ⟨3318468, by rfl⟩ : syracuseStep 8849249 = 6636937) B6636937
theorem B7464899 : Blo 1746574 7464899 := bstep (se 1 (by rfl) ⟨5598674, by rfl⟩ : syracuseStep 7464899 = 11197349) B11197349
theorem B13264883 : Blo 1746574 13264883 := bstep (se 1 (by rfl) ⟨9948662, by rfl⟩ : syracuseStep 13264883 = 19897325) B19897325
theorem B1747359 : Blo 1746574 1747359 := bstep (se 1 (by rfl) ⟨1310519, by rfl⟩ : syracuseStep 1747359 = 2621039) B2621039
theorem B1747439 : Blo 1746574 1747439 := bstep (se 1 (by rfl) ⟨1310579, by rfl⟩ : syracuseStep 1747439 = 2621159) B2621159
theorem B1747567 : Blo 1746574 1747567 := bstep (se 1 (by rfl) ⟨1310675, by rfl⟩ : syracuseStep 1747567 = 2621351) B2621351
theorem B1747783 : Blo 1746574 1747783 := bstep (se 1 (by rfl) ⟨1310837, by rfl⟩ : syracuseStep 1747783 = 2621675) B2621675
theorem B1747823 : Blo 1746574 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B19671997 : Blo 1746574 19671997 := bstep (se 3 (by rfl) ⟨3688499, by rfl⟩ : syracuseStep 19671997 = 7376999) B7376999
theorem B7089277 : Blo 1746574 7089277 := bstep (se 3 (by rfl) ⟨1329239, by rfl⟩ : syracuseStep 7089277 = 2658479) B2658479
theorem B6638867 : Blo 1746574 6638867 := bstep (se 1 (by rfl) ⟨4979150, by rfl⟩ : syracuseStep 6638867 = 9958301) B9958301
theorem B1748271 : Blo 1746574 1748271 := bstep (se 1 (by rfl) ⟨1311203, by rfl⟩ : syracuseStep 1748271 = 2622407) B2622407
theorem B1748383 : Blo 1746574 1748383 := bstep (se 1 (by rfl) ⟨1311287, by rfl⟩ : syracuseStep 1748383 = 2622575) B2622575
theorem B1748511 : Blo 1746574 1748511 := bstep (se 1 (by rfl) ⟨1311383, by rfl⟩ : syracuseStep 1748511 = 2622767) B2622767
theorem B37801511 : Blo 1746574 37801511 := bstep (se 1 (by rfl) ⟨28351133, by rfl⟩ : syracuseStep 37801511 = 56702267) B56702267
theorem B8851355 : Blo 1746574 8851355 := bstep (se 1 (by rfl) ⟨6638516, by rfl⟩ : syracuseStep 8851355 = 13277033) B13277033
theorem B14929829 : Blo 1746574 14929829 := bstep (se 4 (by rfl) ⟨1399671, by rfl⟩ : syracuseStep 14929829 = 2799343) B2799343
theorem B57446425 : Blo 1746574 57446425 := bstep (se 2 (by rfl) ⟨21542409, by rfl⟩ : syracuseStep 57446425 = 43084819) B43084819
theorem B14921765 : Blo 1746574 14921765 := bstep (se 4 (by rfl) ⟨1398915, by rfl⟩ : syracuseStep 14921765 = 2797831) B2797831
theorem B7082075 : Blo 1746574 7082075 := bstep (se 1 (by rfl) ⟨5311556, by rfl⟩ : syracuseStep 7082075 = 10623113) B10623113
theorem B4976815 : Blo 1746574 4976815 := bstep (se 1 (by rfl) ⟨3732611, by rfl⟩ : syracuseStep 4976815 = 7465223) B7465223
theorem B4977065 : Blo 1746574 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B11195117 : Blo 1746574 11195117 := bstep (se 3 (by rfl) ⟨2099084, by rfl⟩ : syracuseStep 11195117 = 4198169) B4198169
theorem B24572855 : Blo 1746574 24572855 := bstep (se 1 (by rfl) ⟨18429641, by rfl⟩ : syracuseStep 24572855 = 36859283) B36859283
theorem B2487343 : Blo 1746574 2487343 := bstep (se 1 (by rfl) ⟨1865507, by rfl⟩ : syracuseStep 2487343 = 3731015) B3731015
theorem B9450551 : Blo 1746574 9450551 := bstep (se 1 (by rfl) ⟨7087913, by rfl⟩ : syracuseStep 9450551 = 14175827) B14175827
theorem B5600315 : Blo 1746574 5600315 := bstep (se 1 (by rfl) ⟨4200236, by rfl⟩ : syracuseStep 5600315 = 8400473) B8400473
theorem B10777697 : Blo 1746574 10777697 := bstep (se 2 (by rfl) ⟨4041636, by rfl⟩ : syracuseStep 10777697 = 8083273) B8083273
theorem B2487451 : Blo 1746574 2487451 := bstep (se 1 (by rfl) ⟨1865588, by rfl⟩ : syracuseStep 2487451 = 3731177) B3731177
theorem B3317755 : Blo 1746574 3317755 := bstep (se 1 (by rfl) ⟨2488316, by rfl⟩ : syracuseStep 3317755 = 4976633) B4976633
theorem B33576281 : Blo 1746574 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B6296939 : Blo 1746574 6296939 := bstep (se 1 (by rfl) ⟨4722704, by rfl⟩ : syracuseStep 6296939 = 9445409) B9445409
theorem B11196143 : Blo 1746574 11196143 := bstep (se 1 (by rfl) ⟨8397107, by rfl⟩ : syracuseStep 11196143 = 16794215) B16794215
theorem B4978523 : Blo 1746574 4978523 := bstep (se 1 (by rfl) ⟨3733892, by rfl⟩ : syracuseStep 4978523 = 7467785) B7467785
theorem B10622825 : Blo 1746574 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B60528545 : Blo 1746574 60528545 := bstep (se 2 (by rfl) ⟨22698204, by rfl⟩ : syracuseStep 60528545 = 45396409) B45396409
theorem B127588283 : Blo 1746574 127588283 := bstep (se 1 (by rfl) ⟨95691212, by rfl⟩ : syracuseStep 127588283 = 191382425) B191382425
theorem B12769271 : Blo 1746574 12769271 := bstep (se 1 (by rfl) ⟨9576953, by rfl⟩ : syracuseStep 12769271 = 19153907) B19153907
theorem B6633535 : Blo 1746574 6633535 := bstep (se 1 (by rfl) ⟨4975151, by rfl⟩ : syracuseStep 6633535 = 9950303) B9950303
theorem B5896313 : Blo 1746574 5896313 := bstep (se 2 (by rfl) ⟨2211117, by rfl⟩ : syracuseStep 5896313 = 4422235) B4422235
theorem B2488487 : Blo 1746574 2488487 := bstep (se 1 (by rfl) ⟨1866365, by rfl⟩ : syracuseStep 2488487 = 3732731) B3732731
theorem B5896367 : Blo 1746574 5896367 := bstep (se 1 (by rfl) ⟨4422275, by rfl⟩ : syracuseStep 5896367 = 8844551) B8844551
theorem B42490115 : Blo 1746574 42490115 := bstep (se 1 (by rfl) ⟨31867586, by rfl⟩ : syracuseStep 42490115 = 63735173) B63735173
theorem B28350749 : Blo 1746574 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B3930425 : Blo 1746574 3930425 := bstep (se 2 (by rfl) ⟨1473909, by rfl⟩ : syracuseStep 3930425 = 2947819) B2947819
theorem B21264869 : Blo 1746574 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B2619881 : Blo 1746574 2619881 := bstep (se 2 (by rfl) ⟨982455, by rfl⟩ : syracuseStep 2619881 = 1964911) B1964911
theorem B4979207 : Blo 1746574 4979207 := bstep (se 1 (by rfl) ⟨3734405, by rfl⟩ : syracuseStep 4979207 = 7468811) B7468811
theorem B9951943 : Blo 1746574 9951943 := bstep (se 1 (by rfl) ⟨7463957, by rfl⟩ : syracuseStep 9951943 = 14927915) B14927915
theorem B4422377 : Blo 1746574 4422377 := bstep (se 2 (by rfl) ⟨1658391, by rfl⟩ : syracuseStep 4422377 = 3316783) B3316783
theorem B2620271 : Blo 1746574 2620271 := bstep (se 1 (by rfl) ⟨1965203, by rfl⟩ : syracuseStep 2620271 = 3930407) B3930407
theorem B76577723 : Blo 1746574 76577723 := bstep (se 1 (by rfl) ⟨57433292, by rfl⟩ : syracuseStep 76577723 = 114866585) B114866585
theorem B2948123 : Blo 1746574 2948123 := bstep (se 1 (by rfl) ⟨2211092, by rfl⟩ : syracuseStep 2948123 = 4422185) B4422185
theorem B3931163 : Blo 1746574 3931163 := bstep (se 1 (by rfl) ⟨2948372, by rfl⟩ : syracuseStep 3931163 = 5896745) B5896745
theorem B2620511 : Blo 1746574 2620511 := bstep (se 1 (by rfl) ⟨1965383, by rfl⟩ : syracuseStep 2620511 = 3930767) B3930767
theorem B23010419 : Blo 1746574 23010419 := bstep (se 1 (by rfl) ⟨17257814, by rfl⟩ : syracuseStep 23010419 = 34515629) B34515629
theorem B2620571 : Blo 1746574 2620571 := bstep (se 1 (by rfl) ⟨1965428, by rfl⟩ : syracuseStep 2620571 = 3930857) B3930857
theorem B2620727 : Blo 1746574 2620727 := bstep (se 1 (by rfl) ⟨1965545, by rfl⟩ : syracuseStep 2620727 = 3931091) B3931091
theorem B2211295 : Blo 1746574 2211295 := bstep (se 1 (by rfl) ⟨1658471, by rfl⟩ : syracuseStep 2211295 = 3316943) B3316943
theorem B2620907 : Blo 1746574 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B2621111 : Blo 1746574 2621111 := bstep (se 1 (by rfl) ⟨1965833, by rfl⟩ : syracuseStep 2621111 = 3931667) B3931667
theorem B2948791 : Blo 1746574 2948791 := bstep (se 1 (by rfl) ⟨2211593, by rfl⟩ : syracuseStep 2948791 = 4423187) B4423187
theorem B13270715 : Blo 1746574 13270715 := bstep (se 1 (by rfl) ⟨9953036, by rfl⟩ : syracuseStep 13270715 = 19906073) B19906073
theorem B2621321 : Blo 1746574 2621321 := bstep (se 2 (by rfl) ⟨982995, by rfl⟩ : syracuseStep 2621321 = 1965991) B1965991
theorem B34062281 : Blo 1746574 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B76595233 : Blo 1746574 76595233 := bstep (se 2 (by rfl) ⟨28723212, by rfl⟩ : syracuseStep 76595233 = 57446425) B57446425
theorem B2211943 : Blo 1746574 2211943 := bstep (se 1 (by rfl) ⟨1658957, by rfl⟩ : syracuseStep 2211943 = 3317915) B3317915
theorem B2621609 : Blo 1746574 2621609 := bstep (se 2 (by rfl) ⟨983103, by rfl⟩ : syracuseStep 2621609 = 1966207) B1966207
theorem B6635753 : Blo 1746574 6635753 := bstep (se 2 (by rfl) ⟨2488407, by rfl⟩ : syracuseStep 6635753 = 4976815) B4976815
theorem B2621819 : Blo 1746574 2621819 := bstep (se 1 (by rfl) ⟨1966364, by rfl⟩ : syracuseStep 2621819 = 3932729) B3932729
theorem B6635965 : Blo 1746574 6635965 := bstep (se 3 (by rfl) ⟨1244243, by rfl⟩ : syracuseStep 6635965 = 2488487) B2488487
theorem B7463411 : Blo 1746574 7463411 := bstep (se 1 (by rfl) ⟨5597558, by rfl⟩ : syracuseStep 7463411 = 11195117) B11195117
theorem B2621993 : Blo 1746574 2621993 := bstep (se 2 (by rfl) ⟨983247, by rfl⟩ : syracuseStep 2621993 = 1966495) B1966495
theorem B5898959 : Blo 1746574 5898959 := bstep (se 1 (by rfl) ⟨4424219, by rfl⟩ : syracuseStep 5898959 = 8848439) B8848439
theorem B2949851 : Blo 1746574 2949851 := bstep (se 1 (by rfl) ⟨2212388, by rfl⟩ : syracuseStep 2949851 = 4424777) B4424777
theorem B7185131 : Blo 1746574 7185131 := bstep (se 1 (by rfl) ⟨5388848, by rfl⟩ : syracuseStep 7185131 = 10777697) B10777697
theorem B3932927 : Blo 1746574 3932927 := bstep (se 1 (by rfl) ⟨2949695, by rfl⟩ : syracuseStep 3932927 = 5899391) B5899391
theorem B4424503 : Blo 1746574 4424503 := bstep (se 1 (by rfl) ⟨3318377, by rfl⟩ : syracuseStep 4424503 = 6636755) B6636755
theorem B2622299 : Blo 1746574 2622299 := bstep (se 1 (by rfl) ⟨1966724, by rfl⟩ : syracuseStep 2622299 = 3933449) B3933449
theorem B13272173 : Blo 1746574 13272173 := bstep (se 3 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 13272173 = 4977065) B4977065
theorem B7668863 : Blo 1746574 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B7464095 : Blo 1746574 7464095 := bstep (se 1 (by rfl) ⟨5598071, by rfl⟩ : syracuseStep 7464095 = 11196143) B11196143
theorem B2950303 : Blo 1746574 2950303 := bstep (se 1 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 2950303 = 4425455) B4425455
theorem B2622647 : Blo 1746574 2622647 := bstep (se 1 (by rfl) ⟨1966985, by rfl⟩ : syracuseStep 2622647 = 3933971) B3933971
theorem B5899499 : Blo 1746574 5899499 := bstep (se 1 (by rfl) ⟨4424624, by rfl⟩ : syracuseStep 5899499 = 8849249) B8849249
theorem B4424969 : Blo 1746574 4424969 := bstep (se 2 (by rfl) ⟨1659363, by rfl⟩ : syracuseStep 4424969 = 3318727) B3318727
theorem B85058855 : Blo 1746574 85058855 := bstep (se 1 (by rfl) ⟨63794141, by rfl⟩ : syracuseStep 85058855 = 127588283) B127588283
theorem B8512847 : Blo 1746574 8512847 := bstep (se 1 (by rfl) ⟨6384635, by rfl⟩ : syracuseStep 8512847 = 12769271) B12769271
theorem B18900499 : Blo 1746574 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B1746587 : Blo 1746574 1746587 := bstep (se 1 (by rfl) ⟨1309940, by rfl⟩ : syracuseStep 1746587 = 2619881) B2619881
theorem B3319471 : Blo 1746574 3319471 := bstep (se 1 (by rfl) ⟨2489603, by rfl⟩ : syracuseStep 3319471 = 4979207) B4979207
theorem B1746847 : Blo 1746574 1746847 := bstep (se 1 (by rfl) ⟨1310135, by rfl⟩ : syracuseStep 1746847 = 2620271) B2620271
theorem B1747007 : Blo 1746574 1747007 := bstep (se 1 (by rfl) ⟨1310255, by rfl⟩ : syracuseStep 1747007 = 2620511) B2620511
theorem B1747047 : Blo 1746574 1747047 := bstep (se 1 (by rfl) ⟨1310285, by rfl⟩ : syracuseStep 1747047 = 2620571) B2620571
theorem B4425911 : Blo 1746574 4425911 := bstep (se 1 (by rfl) ⟨3319433, by rfl⟩ : syracuseStep 4425911 = 6638867) B6638867
theorem B1747151 : Blo 1746574 1747151 := bstep (se 1 (by rfl) ⟨1310363, by rfl⟩ : syracuseStep 1747151 = 2620727) B2620727
theorem B1747271 : Blo 1746574 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B25201007 : Blo 1746574 25201007 := bstep (se 1 (by rfl) ⟨18900755, by rfl⟩ : syracuseStep 25201007 = 37801511) B37801511
theorem B1747407 : Blo 1746574 1747407 := bstep (se 1 (by rfl) ⟨1310555, by rfl⟩ : syracuseStep 1747407 = 2621111) B2621111
theorem B1747547 : Blo 1746574 1747547 := bstep (se 1 (by rfl) ⟨1310660, by rfl⟩ : syracuseStep 1747547 = 2621321) B2621321
theorem B5900903 : Blo 1746574 5900903 := bstep (se 1 (by rfl) ⟨4425677, by rfl⟩ : syracuseStep 5900903 = 8851355) B8851355
theorem B9947843 : Blo 1746574 9947843 := bstep (se 1 (by rfl) ⟨7460882, by rfl⟩ : syracuseStep 9947843 = 14921765) B14921765
theorem B4721383 : Blo 1746574 4721383 := bstep (se 1 (by rfl) ⟨3541037, by rfl⟩ : syracuseStep 4721383 = 7082075) B7082075
theorem B1747711 : Blo 1746574 1747711 := bstep (se 1 (by rfl) ⟨1310783, by rfl⟩ : syracuseStep 1747711 = 2621567) B2621567
theorem B25201469 : Blo 1746574 25201469 := bstep (se 3 (by rfl) ⟨4725275, by rfl⟩ : syracuseStep 25201469 = 9450551) B9450551
theorem B1747903 : Blo 1746574 1747903 := bstep (se 1 (by rfl) ⟨1310927, by rfl⟩ : syracuseStep 1747903 = 2621855) B2621855
theorem B1748079 : Blo 1746574 1748079 := bstep (se 1 (by rfl) ⟨1311059, by rfl⟩ : syracuseStep 1748079 = 2622119) B2622119
theorem B1748159 : Blo 1746574 1748159 := bstep (se 1 (by rfl) ⟨1311119, by rfl⟩ : syracuseStep 1748159 = 2622239) B2622239
theorem B1748175 : Blo 1746574 1748175 := bstep (se 1 (by rfl) ⟨1311131, by rfl⟩ : syracuseStep 1748175 = 2622263) B2622263
theorem B1748295 : Blo 1746574 1748295 := bstep (se 1 (by rfl) ⟨1311221, by rfl⟩ : syracuseStep 1748295 = 2622443) B2622443
theorem B22384187 : Blo 1746574 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B4197959 : Blo 1746574 4197959 := bstep (se 1 (by rfl) ⟨3148469, by rfl⟩ : syracuseStep 4197959 = 6296939) B6296939
theorem B7081883 : Blo 1746574 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B4976599 : Blo 1746574 4976599 := bstep (se 1 (by rfl) ⟨3732449, by rfl⟩ : syracuseStep 4976599 = 7464899) B7464899
theorem B8843255 : Blo 1746574 8843255 := bstep (se 1 (by rfl) ⟨6632441, by rfl⟩ : syracuseStep 8843255 = 13264883) B13264883
theorem B14176579 : Blo 1746574 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B15340279 : Blo 1746574 15340279 := bstep (se 1 (by rfl) ⟨11505209, by rfl⟩ : syracuseStep 15340279 = 23010419) B23010419
theorem B75543353 : Blo 1746574 75543353 := bstep (se 2 (by rfl) ⟨28328757, by rfl⟩ : syracuseStep 75543353 = 56657515) B56657515
theorem B13276061 : Blo 1746574 13276061 := bstep (se 3 (by rfl) ⟨2489261, by rfl⟩ : syracuseStep 13276061 = 4978523) B4978523
theorem B8844713 : Blo 1746574 8844713 := bstep (se 2 (by rfl) ⟨3316767, by rfl⟩ : syracuseStep 8844713 = 6633535) B6633535
theorem B3733543 : Blo 1746574 3733543 := bstep (se 1 (by rfl) ⟨2800157, by rfl⟩ : syracuseStep 3733543 = 5600315) B5600315
theorem B9951443 : Blo 1746574 9951443 := bstep (se 1 (by rfl) ⟨7463582, by rfl⟩ : syracuseStep 9951443 = 14927165) B14927165
theorem B13269257 : Blo 1746574 13269257 := bstep (se 2 (by rfl) ⟨4975971, by rfl⟩ : syracuseStep 13269257 = 9951943) B9951943
theorem B13277519 : Blo 1746574 13277519 := bstep (se 1 (by rfl) ⟨9958139, by rfl⟩ : syracuseStep 13277519 = 19916279) B19916279
theorem B5314987 : Blo 1746574 5314987 := bstep (se 1 (by rfl) ⟨3986240, by rfl⟩ : syracuseStep 5314987 = 7972481) B7972481
theorem B26229329 : Blo 1746574 26229329 := bstep (se 2 (by rfl) ⟨9835998, by rfl⟩ : syracuseStep 26229329 = 19671997) B19671997
theorem B40352363 : Blo 1746574 40352363 := bstep (se 1 (by rfl) ⟨30264272, by rfl⟩ : syracuseStep 40352363 = 60528545) B60528545
theorem B3316457 : Blo 1746574 3316457 := bstep (se 2 (by rfl) ⟨1243671, by rfl⟩ : syracuseStep 3316457 = 2487343) B2487343
theorem B3930875 : Blo 1746574 3930875 := bstep (se 1 (by rfl) ⟨2948156, by rfl⟩ : syracuseStep 3930875 = 5896313) B5896313
theorem B3930911 : Blo 1746574 3930911 := bstep (se 1 (by rfl) ⟨2948183, by rfl⟩ : syracuseStep 3930911 = 5896367) B5896367
theorem B9452369 : Blo 1746574 9452369 := bstep (se 2 (by rfl) ⟨3544638, by rfl⟩ : syracuseStep 9452369 = 7089277) B7089277
theorem B28326743 : Blo 1746574 28326743 := bstep (se 1 (by rfl) ⟨21245057, by rfl⟩ : syracuseStep 28326743 = 42490115) B42490115
theorem B3316601 : Blo 1746574 3316601 := bstep (se 2 (by rfl) ⟨1243725, by rfl⟩ : syracuseStep 3316601 = 2487451) B2487451
theorem B2620283 : Blo 1746574 2620283 := bstep (se 1 (by rfl) ⟨1965212, by rfl⟩ : syracuseStep 2620283 = 3930425) B3930425
theorem B4423673 : Blo 1746574 4423673 := bstep (se 2 (by rfl) ⟨1658877, by rfl⟩ : syracuseStep 4423673 = 3317755) B3317755
theorem B2948251 : Blo 1746574 2948251 := bstep (se 1 (by rfl) ⟨2211188, by rfl⟩ : syracuseStep 2948251 = 4422377) B4422377
theorem B51051815 : Blo 1746574 51051815 := bstep (se 1 (by rfl) ⟨38288861, by rfl⟩ : syracuseStep 51051815 = 76577723) B76577723
theorem B2948393 : Blo 1746574 2948393 := bstep (se 2 (by rfl) ⟨1105647, by rfl⟩ : syracuseStep 2948393 = 2211295) B2211295
theorem B1965415 : Blo 1746574 1965415 := bstep (se 1 (by rfl) ⟨1474061, by rfl⟩ : syracuseStep 1965415 = 2948123) B2948123
theorem B2620775 : Blo 1746574 2620775 := bstep (se 1 (by rfl) ⟨1965581, by rfl⟩ : syracuseStep 2620775 = 3931163) B3931163
theorem B3931721 : Blo 1746574 3931721 := bstep (se 2 (by rfl) ⟨1474395, by rfl⟩ : syracuseStep 3931721 = 2948791) B2948791
theorem B8847143 : Blo 1746574 8847143 := bstep (se 1 (by rfl) ⟨6635357, by rfl⟩ : syracuseStep 8847143 = 13270715) B13270715
theorem B65527613 : Blo 1746574 65527613 := bstep (se 3 (by rfl) ⟨12286427, by rfl⟩ : syracuseStep 65527613 = 24572855) B24572855
theorem B9953219 : Blo 1746574 9953219 := bstep (se 1 (by rfl) ⟨7464914, by rfl⟩ : syracuseStep 9953219 = 14929829) B14929829
theorem B22708187 : Blo 1746574 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B2949257 : Blo 1746574 2949257 := bstep (se 2 (by rfl) ⟨1105971, by rfl⟩ : syracuseStep 2949257 = 2211943) B2211943
theorem B4423835 : Blo 1746574 4423835 := bstep (se 1 (by rfl) ⟨3317876, by rfl⟩ : syracuseStep 4423835 = 6635753) B6635753
theorem B3932639 : Blo 1746574 3932639 := bstep (se 1 (by rfl) ⟨2949479, by rfl⟩ : syracuseStep 3932639 = 5898959) B5898959
theorem B1966567 : Blo 1746574 1966567 := bstep (se 1 (by rfl) ⟨1474925, by rfl⟩ : syracuseStep 1966567 = 2949851) B2949851
theorem B2621951 : Blo 1746574 2621951 := bstep (se 1 (by rfl) ⟨1966463, by rfl⟩ : syracuseStep 2621951 = 3932927) B3932927
theorem B8847953 : Blo 1746574 8847953 := bstep (se 2 (by rfl) ⟨3317982, by rfl⟩ : syracuseStep 8847953 = 6635965) B6635965
theorem B8848115 : Blo 1746574 8848115 := bstep (se 1 (by rfl) ⟨6636086, by rfl⟩ : syracuseStep 8848115 = 13272173) B13272173
theorem B5112575 : Blo 1746574 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B3932999 : Blo 1746574 3932999 := bstep (se 1 (by rfl) ⟨2949749, by rfl⟩ : syracuseStep 3932999 = 5899499) B5899499
theorem B2949979 : Blo 1746574 2949979 := bstep (se 1 (by rfl) ⟨2212484, by rfl⟩ : syracuseStep 2949979 = 4424969) B4424969
theorem B56705903 : Blo 1746574 56705903 := bstep (se 1 (by rfl) ⟨42529427, by rfl⟩ : syracuseStep 56705903 = 85058855) B85058855
theorem B5899337 : Blo 1746574 5899337 := bstep (se 2 (by rfl) ⟨2212251, by rfl⟩ : syracuseStep 5899337 = 4424503) B4424503
theorem B2950607 : Blo 1746574 2950607 := bstep (se 1 (by rfl) ⟨2212955, by rfl⟩ : syracuseStep 2950607 = 4425911) B4425911
theorem B3933737 : Blo 1746574 3933737 := bstep (se 2 (by rfl) ⟨1475151, by rfl⟩ : syracuseStep 3933737 = 2950303) B2950303
theorem B3933935 : Blo 1746574 3933935 := bstep (se 1 (by rfl) ⟨2950451, by rfl⟩ : syracuseStep 3933935 = 5900903) B5900903
theorem B6301579 : Blo 1746574 6301579 := bstep (se 1 (by rfl) ⟨4726184, by rfl⟩ : syracuseStep 6301579 = 9452369) B9452369
theorem B18884495 : Blo 1746574 18884495 := bstep (se 1 (by rfl) ⟨14163371, by rfl⟩ : syracuseStep 18884495 = 28326743) B28326743
theorem B1746855 : Blo 1746574 1746855 := bstep (se 1 (by rfl) ⟨1310141, by rfl⟩ : syracuseStep 1746855 = 2620283) B2620283
theorem B2949115 : Blo 1746574 2949115 := bstep (se 1 (by rfl) ⟨2211836, by rfl⟩ : syracuseStep 2949115 = 4423673) B4423673
theorem B25200665 : Blo 1746574 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B28346597 : Blo 1746574 28346597 := bstep (se 4 (by rfl) ⟨2657493, by rfl⟩ : syracuseStep 28346597 = 5314987) B5314987
theorem B4425961 : Blo 1746574 4425961 := bstep (se 2 (by rfl) ⟨1659735, by rfl⟩ : syracuseStep 4425961 = 3319471) B3319471
theorem B1747183 : Blo 1746574 1747183 := bstep (se 1 (by rfl) ⟨1310387, by rfl⟩ : syracuseStep 1747183 = 2620775) B2620775
theorem B4721255 : Blo 1746574 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B1747739 : Blo 1746574 1747739 := bstep (se 1 (by rfl) ⟨1310804, by rfl⟩ : syracuseStep 1747739 = 2621609) B2621609
theorem B1747879 : Blo 1746574 1747879 := bstep (se 1 (by rfl) ⟨1310909, by rfl⟩ : syracuseStep 1747879 = 2621819) B2621819
theorem B4975607 : Blo 1746574 4975607 := bstep (se 1 (by rfl) ⟨3731705, by rfl⟩ : syracuseStep 4975607 = 7463411) B7463411
theorem B1747995 : Blo 1746574 1747995 := bstep (se 1 (by rfl) ⟨1310996, by rfl⟩ : syracuseStep 1747995 = 2621993) B2621993
theorem B18902105 : Blo 1746574 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B1748199 : Blo 1746574 1748199 := bstep (se 1 (by rfl) ⟨1311149, by rfl⟩ : syracuseStep 1748199 = 2622299) B2622299
theorem B8850707 : Blo 1746574 8850707 := bstep (se 1 (by rfl) ⟨6638030, by rfl⟩ : syracuseStep 8850707 = 13276061) B13276061
theorem B4976063 : Blo 1746574 4976063 := bstep (se 1 (by rfl) ⟨3732047, by rfl⟩ : syracuseStep 4976063 = 7464095) B7464095
theorem B1748431 : Blo 1746574 1748431 := bstep (se 1 (by rfl) ⟨1311323, by rfl⟩ : syracuseStep 1748431 = 2622647) B2622647
theorem B6295177 : Blo 1746574 6295177 := bstep (se 2 (by rfl) ⟨2360691, by rfl⟩ : syracuseStep 6295177 = 4721383) B4721383
theorem B8851679 : Blo 1746574 8851679 := bstep (se 1 (by rfl) ⟨6638759, by rfl⟩ : syracuseStep 8851679 = 13277519) B13277519
theorem B17486219 : Blo 1746574 17486219 := bstep (se 1 (by rfl) ⟨13114664, by rfl⟩ : syracuseStep 17486219 = 26229329) B26229329
theorem B6631895 : Blo 1746574 6631895 := bstep (se 1 (by rfl) ⟨4973921, by rfl⟩ : syracuseStep 6631895 = 9947843) B9947843
theorem B34034543 : Blo 1746574 34034543 := bstep (se 1 (by rfl) ⟨25525907, by rfl⟩ : syracuseStep 34034543 = 51051815) B51051815
theorem B14922791 : Blo 1746574 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B2798639 : Blo 1746574 2798639 := bstep (se 1 (by rfl) ⟨2098979, by rfl⟩ : syracuseStep 2798639 = 4197959) B4197959
theorem B43685075 : Blo 1746574 43685075 := bstep (se 1 (by rfl) ⟨32763806, by rfl⟩ : syracuseStep 43685075 = 65527613) B65527613
theorem B5895503 : Blo 1746574 5895503 := bstep (se 1 (by rfl) ⟨4421627, by rfl⟩ : syracuseStep 5895503 = 8843255) B8843255
theorem B102126977 : Blo 1746574 102126977 := bstep (se 2 (by rfl) ⟨38297616, by rfl⟩ : syracuseStep 102126977 = 76595233) B76595233
theorem B4978057 : Blo 1746574 4978057 := bstep (se 2 (by rfl) ⟨1866771, by rfl⟩ : syracuseStep 4978057 = 3733543) B3733543
theorem B4790087 : Blo 1746574 4790087 := bstep (se 1 (by rfl) ⟨3592565, by rfl⟩ : syracuseStep 4790087 = 7185131) B7185131
theorem B50362235 : Blo 1746574 50362235 := bstep (se 1 (by rfl) ⟨37771676, by rfl⟩ : syracuseStep 50362235 = 75543353) B75543353
theorem B5675231 : Blo 1746574 5675231 := bstep (se 1 (by rfl) ⟨4256423, by rfl⟩ : syracuseStep 5675231 = 8512847) B8512847
theorem B5896475 : Blo 1746574 5896475 := bstep (se 1 (by rfl) ⟨4422356, by rfl⟩ : syracuseStep 5896475 = 8844713) B8844713
theorem B20453705 : Blo 1746574 20453705 := bstep (se 2 (by rfl) ⟨7670139, by rfl⟩ : syracuseStep 20453705 = 15340279) B15340279
theorem B6634295 : Blo 1746574 6634295 := bstep (se 1 (by rfl) ⟨4975721, by rfl⟩ : syracuseStep 6634295 = 9951443) B9951443
theorem B8846171 : Blo 1746574 8846171 := bstep (se 1 (by rfl) ⟨6634628, by rfl⟩ : syracuseStep 8846171 = 13269257) B13269257
theorem B3931001 : Blo 1746574 3931001 := bstep (se 2 (by rfl) ⟨1474125, by rfl⟩ : syracuseStep 3931001 = 2948251) B2948251
theorem B16800671 : Blo 1746574 16800671 := bstep (se 1 (by rfl) ⟨12600503, by rfl⟩ : syracuseStep 16800671 = 25201007) B25201007
theorem B26901575 : Blo 1746574 26901575 := bstep (se 1 (by rfl) ⟨20176181, by rfl⟩ : syracuseStep 26901575 = 40352363) B40352363
theorem B2620553 : Blo 1746574 2620553 := bstep (se 2 (by rfl) ⟨982707, by rfl⟩ : syracuseStep 2620553 = 1965415) B1965415
theorem B2210971 : Blo 1746574 2210971 := bstep (se 1 (by rfl) ⟨1658228, by rfl⟩ : syracuseStep 2210971 = 3316457) B3316457
theorem B2620583 : Blo 1746574 2620583 := bstep (se 1 (by rfl) ⟨1965437, by rfl⟩ : syracuseStep 2620583 = 3930875) B3930875
theorem B2620607 : Blo 1746574 2620607 := bstep (se 1 (by rfl) ⟨1965455, by rfl⟩ : syracuseStep 2620607 = 3930911) B3930911
theorem B16800979 : Blo 1746574 16800979 := bstep (se 1 (by rfl) ⟨12600734, by rfl⟩ : syracuseStep 16800979 = 25201469) B25201469
theorem B2211067 : Blo 1746574 2211067 := bstep (se 1 (by rfl) ⟨1658300, by rfl⟩ : syracuseStep 2211067 = 3316601) B3316601
theorem B1965595 : Blo 1746574 1965595 := bstep (se 1 (by rfl) ⟨1474196, by rfl⟩ : syracuseStep 1965595 = 2948393) B2948393
theorem B2621147 : Blo 1746574 2621147 := bstep (se 1 (by rfl) ⟨1965860, by rfl⟩ : syracuseStep 2621147 = 3931721) B3931721
theorem B5898095 : Blo 1746574 5898095 := bstep (se 1 (by rfl) ⟨4423571, by rfl⟩ : syracuseStep 5898095 = 8847143) B8847143
theorem B6635465 : Blo 1746574 6635465 := bstep (se 2 (by rfl) ⟨2488299, by rfl⟩ : syracuseStep 6635465 = 4976599) B4976599
theorem B6635479 : Blo 1746574 6635479 := bstep (se 1 (by rfl) ⟨4976609, by rfl⟩ : syracuseStep 6635479 = 9953219) B9953219
theorem B15138791 : Blo 1746574 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B1966171 : Blo 1746574 1966171 := bstep (se 1 (by rfl) ⟨1474628, by rfl⟩ : syracuseStep 1966171 = 2949257) B2949257
theorem B2949223 : Blo 1746574 2949223 := bstep (se 1 (by rfl) ⟨2211917, by rfl⟩ : syracuseStep 2949223 = 4423835) B4423835
theorem B11657479 : Blo 1746574 11657479 := bstep (se 1 (by rfl) ⟨8743109, by rfl⟩ : syracuseStep 11657479 = 17486219) B17486219
theorem B2621759 : Blo 1746574 2621759 := bstep (se 1 (by rfl) ⟨1966319, by rfl⟩ : syracuseStep 2621759 = 3932639) B3932639
theorem B5898635 : Blo 1746574 5898635 := bstep (se 1 (by rfl) ⟨4423976, by rfl⟩ : syracuseStep 5898635 = 8847953) B8847953
theorem B5898743 : Blo 1746574 5898743 := bstep (se 1 (by rfl) ⟨4424057, by rfl⟩ : syracuseStep 5898743 = 8848115) B8848115
theorem B3408383 : Blo 1746574 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B2621999 : Blo 1746574 2621999 := bstep (se 1 (by rfl) ⟨1966499, by rfl⟩ : syracuseStep 2621999 = 3932999) B3932999
theorem B2622089 : Blo 1746574 2622089 := bstep (se 2 (by rfl) ⟨983283, by rfl⟩ : syracuseStep 2622089 = 1966567) B1966567
theorem B3932891 : Blo 1746574 3932891 := bstep (se 1 (by rfl) ⟨2949668, by rfl⟩ : syracuseStep 3932891 = 5899337) B5899337
theorem B29123383 : Blo 1746574 29123383 := bstep (se 1 (by rfl) ⟨21842537, by rfl⟩ : syracuseStep 29123383 = 43685075) B43685075
theorem B68084651 : Blo 1746574 68084651 := bstep (se 1 (by rfl) ⟨51063488, by rfl⟩ : syracuseStep 68084651 = 102126977) B102126977
theorem B1967071 : Blo 1746574 1967071 := bstep (se 1 (by rfl) ⟨1475303, by rfl⟩ : syracuseStep 1967071 = 2950607) B2950607
theorem B2622491 : Blo 1746574 2622491 := bstep (se 1 (by rfl) ⟨1966868, by rfl⟩ : syracuseStep 2622491 = 3933737) B3933737
theorem B3933305 : Blo 1746574 3933305 := bstep (se 2 (by rfl) ⟨1474989, by rfl⟩ : syracuseStep 3933305 = 2949979) B2949979
theorem B2622623 : Blo 1746574 2622623 := bstep (se 1 (by rfl) ⟨1966967, by rfl⟩ : syracuseStep 2622623 = 3933935) B3933935
theorem B3147503 : Blo 1746574 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B6637409 : Blo 1746574 6637409 := bstep (se 2 (by rfl) ⟨2489028, by rfl⟩ : syracuseStep 6637409 = 4978057) B4978057
theorem B11200447 : Blo 1746574 11200447 := bstep (se 1 (by rfl) ⟨8400335, by rfl⟩ : syracuseStep 11200447 = 16800671) B16800671
theorem B17934383 : Blo 1746574 17934383 := bstep (se 1 (by rfl) ⟨13450787, by rfl⟩ : syracuseStep 17934383 = 26901575) B26901575
theorem B12601403 : Blo 1746574 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B1747035 : Blo 1746574 1747035 := bstep (se 1 (by rfl) ⟨1310276, by rfl⟩ : syracuseStep 1747035 = 2620553) B2620553
theorem B1747055 : Blo 1746574 1747055 := bstep (se 1 (by rfl) ⟨1310291, by rfl⟩ : syracuseStep 1747055 = 2620583) B2620583
theorem B1747071 : Blo 1746574 1747071 := bstep (se 1 (by rfl) ⟨1310303, by rfl⟩ : syracuseStep 1747071 = 2620607) B2620607
theorem B5900471 : Blo 1746574 5900471 := bstep (se 1 (by rfl) ⟨4425353, by rfl⟩ : syracuseStep 5900471 = 8850707) B8850707
theorem B1747431 : Blo 1746574 1747431 := bstep (se 1 (by rfl) ⟨1310573, by rfl⟩ : syracuseStep 1747431 = 2621147) B2621147
theorem B5901119 : Blo 1746574 5901119 := bstep (se 1 (by rfl) ⟨4425839, by rfl⟩ : syracuseStep 5901119 = 8851679) B8851679
theorem B5901281 : Blo 1746574 5901281 := bstep (se 2 (by rfl) ⟨2212980, by rfl⟩ : syracuseStep 5901281 = 4425961) B4425961
theorem B1747967 : Blo 1746574 1747967 := bstep (se 1 (by rfl) ⟨1310975, by rfl⟩ : syracuseStep 1747967 = 2621951) B2621951
theorem B15133949 : Blo 1746574 15133949 := bstep (se 3 (by rfl) ⟨2837615, by rfl⟩ : syracuseStep 15133949 = 5675231) B5675231
theorem B9948527 : Blo 1746574 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B33574277 : Blo 1746574 33574277 := bstep (se 4 (by rfl) ⟨3147588, by rfl⟩ : syracuseStep 33574277 = 6295177) B6295177
theorem B33574823 : Blo 1746574 33574823 := bstep (se 1 (by rfl) ⟨25181117, by rfl⟩ : syracuseStep 33574823 = 50362235) B50362235
theorem B13635803 : Blo 1746574 13635803 := bstep (se 1 (by rfl) ⟨10226852, by rfl⟩ : syracuseStep 13635803 = 20453705) B20453705
theorem B22401305 : Blo 1746574 22401305 := bstep (se 2 (by rfl) ⟨8400489, by rfl⟩ : syracuseStep 22401305 = 16800979) B16800979
theorem B8402105 : Blo 1746574 8402105 := bstep (se 2 (by rfl) ⟨3150789, by rfl⟩ : syracuseStep 8402105 = 6301579) B6301579
theorem B13268285 : Blo 1746574 13268285 := bstep (se 3 (by rfl) ⟨2487803, by rfl⟩ : syracuseStep 13268285 = 4975607) B4975607
theorem B4421263 : Blo 1746574 4421263 := bstep (se 1 (by rfl) ⟨3315947, by rfl⟩ : syracuseStep 4421263 = 6631895) B6631895
theorem B22689695 : Blo 1746574 22689695 := bstep (se 1 (by rfl) ⟨17017271, by rfl⟩ : syracuseStep 22689695 = 34034543) B34034543
theorem B37803935 : Blo 1746574 37803935 := bstep (se 1 (by rfl) ⟨28352951, by rfl⟩ : syracuseStep 37803935 = 56705903) B56705903
theorem B1865759 : Blo 1746574 1865759 := bstep (se 1 (by rfl) ⟨1399319, by rfl⟩ : syracuseStep 1865759 = 2798639) B2798639
theorem B3930335 : Blo 1746574 3930335 := bstep (se 1 (by rfl) ⟨2947751, by rfl⟩ : syracuseStep 3930335 = 5895503) B5895503
theorem B3193391 : Blo 1746574 3193391 := bstep (se 1 (by rfl) ⟨2395043, by rfl⟩ : syracuseStep 3193391 = 4790087) B4790087
theorem B12589663 : Blo 1746574 12589663 := bstep (se 1 (by rfl) ⟨9442247, by rfl⟩ : syracuseStep 12589663 = 18884495) B18884495
theorem B16800443 : Blo 1746574 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B18897731 : Blo 1746574 18897731 := bstep (se 1 (by rfl) ⟨14173298, by rfl⟩ : syracuseStep 18897731 = 28346597) B28346597
theorem B3930983 : Blo 1746574 3930983 := bstep (se 1 (by rfl) ⟨2948237, by rfl⟩ : syracuseStep 3930983 = 5896475) B5896475
theorem B2947961 : Blo 1746574 2947961 := bstep (se 2 (by rfl) ⟨1105485, by rfl⟩ : syracuseStep 2947961 = 2210971) B2210971
theorem B2948089 : Blo 1746574 2948089 := bstep (se 2 (by rfl) ⟨1105533, by rfl⟩ : syracuseStep 2948089 = 2211067) B2211067
theorem B4422863 : Blo 1746574 4422863 := bstep (se 1 (by rfl) ⟨3317147, by rfl⟩ : syracuseStep 4422863 = 6634295) B6634295
theorem B5897447 : Blo 1746574 5897447 := bstep (se 1 (by rfl) ⟨4423085, by rfl⟩ : syracuseStep 5897447 = 8846171) B8846171
theorem B2620667 : Blo 1746574 2620667 := bstep (se 1 (by rfl) ⟨1965500, by rfl⟩ : syracuseStep 2620667 = 3931001) B3931001
theorem B2620793 : Blo 1746574 2620793 := bstep (se 2 (by rfl) ⟨982797, by rfl⟩ : syracuseStep 2620793 = 1965595) B1965595
theorem B3317375 : Blo 1746574 3317375 := bstep (se 1 (by rfl) ⟨2488031, by rfl⟩ : syracuseStep 3317375 = 4976063) B4976063
theorem B3932063 : Blo 1746574 3932063 := bstep (se 1 (by rfl) ⟨2949047, by rfl⟩ : syracuseStep 3932063 = 5898095) B5898095
theorem B8847305 : Blo 1746574 8847305 := bstep (se 2 (by rfl) ⟨3317739, by rfl⟩ : syracuseStep 8847305 = 6635479) B6635479
theorem B4423643 : Blo 1746574 4423643 := bstep (se 1 (by rfl) ⟨3317732, by rfl⟩ : syracuseStep 4423643 = 6635465) B6635465
theorem B10092527 : Blo 1746574 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B3932153 : Blo 1746574 3932153 := bstep (se 2 (by rfl) ⟨1474557, by rfl⟩ : syracuseStep 3932153 = 2949115) B2949115
theorem B2621561 : Blo 1746574 2621561 := bstep (se 2 (by rfl) ⟨983085, by rfl⟩ : syracuseStep 2621561 = 1966171) B1966171
theorem B3932297 : Blo 1746574 3932297 := bstep (se 2 (by rfl) ⟨1474611, by rfl⟩ : syracuseStep 3932297 = 2949223) B2949223
theorem B14934203 : Blo 1746574 14934203 := bstep (se 1 (by rfl) ⟨11200652, by rfl⟩ : syracuseStep 14934203 = 22401305) B22401305
theorem B3932423 : Blo 1746574 3932423 := bstep (se 1 (by rfl) ⟨2949317, by rfl⟩ : syracuseStep 3932423 = 5898635) B5898635
theorem B3932495 : Blo 1746574 3932495 := bstep (se 1 (by rfl) ⟨2949371, by rfl⟩ : syracuseStep 3932495 = 5898743) B5898743
theorem B2621927 : Blo 1746574 2621927 := bstep (se 1 (by rfl) ⟨1966445, by rfl⟩ : syracuseStep 2621927 = 3932891) B3932891
theorem B2622203 : Blo 1746574 2622203 := bstep (se 1 (by rfl) ⟨1966652, by rfl⟩ : syracuseStep 2622203 = 3933305) B3933305
theorem B16786217 : Blo 1746574 16786217 := bstep (se 2 (by rfl) ⟨6294831, by rfl⟩ : syracuseStep 16786217 = 12589663) B12589663
theorem B38831177 : Blo 1746574 38831177 := bstep (se 2 (by rfl) ⟨14561691, by rfl⟩ : syracuseStep 38831177 = 29123383) B29123383
theorem B4424939 : Blo 1746574 4424939 := bstep (se 1 (by rfl) ⟨3318704, by rfl⟩ : syracuseStep 4424939 = 6637409) B6637409
theorem B2622761 : Blo 1746574 2622761 := bstep (se 2 (by rfl) ⟨983535, by rfl⟩ : syracuseStep 2622761 = 1967071) B1967071
theorem B3933647 : Blo 1746574 3933647 := bstep (se 1 (by rfl) ⟨2950235, by rfl⟩ : syracuseStep 3933647 = 5900471) B5900471
theorem B11200295 : Blo 1746574 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B3934079 : Blo 1746574 3934079 := bstep (se 1 (by rfl) ⟨2950559, by rfl⟩ : syracuseStep 3934079 = 5901119) B5901119
theorem B3934187 : Blo 1746574 3934187 := bstep (se 1 (by rfl) ⟨2950640, by rfl⟩ : syracuseStep 3934187 = 5901281) B5901281
theorem B1747111 : Blo 1746574 1747111 := bstep (se 1 (by rfl) ⟨1310333, by rfl⟩ : syracuseStep 1747111 = 2620667) B2620667
theorem B1747195 : Blo 1746574 1747195 := bstep (se 1 (by rfl) ⟨1310396, by rfl⟩ : syracuseStep 1747195 = 2620793) B2620793
theorem B22382851 : Blo 1746574 22382851 := bstep (se 1 (by rfl) ⟨16787138, by rfl⟩ : syracuseStep 22382851 = 33574277) B33574277
theorem B22383215 : Blo 1746574 22383215 := bstep (se 1 (by rfl) ⟨16787411, by rfl⟩ : syracuseStep 22383215 = 33574823) B33574823
theorem B6728351 : Blo 1746574 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B4975357 : Blo 1746574 4975357 := bstep (se 3 (by rfl) ⟨932879, by rfl⟩ : syracuseStep 4975357 = 1865759) B1865759
theorem B1747839 : Blo 1746574 1747839 := bstep (se 1 (by rfl) ⟨1310879, by rfl⟩ : syracuseStep 1747839 = 2621759) B2621759
theorem B2272255 : Blo 1746574 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B15543305 : Blo 1746574 15543305 := bstep (se 2 (by rfl) ⟨5828739, by rfl⟩ : syracuseStep 15543305 = 11657479) B11657479
theorem B1747999 : Blo 1746574 1747999 := bstep (se 1 (by rfl) ⟨1310999, by rfl⟩ : syracuseStep 1747999 = 2621999) B2621999
theorem B1748059 : Blo 1746574 1748059 := bstep (se 1 (by rfl) ⟨1311044, by rfl⟩ : syracuseStep 1748059 = 2622089) B2622089
theorem B1748327 : Blo 1746574 1748327 := bstep (se 1 (by rfl) ⟨1311245, by rfl⟩ : syracuseStep 1748327 = 2622491) B2622491
theorem B1748415 : Blo 1746574 1748415 := bstep (se 1 (by rfl) ⟨1311311, by rfl⟩ : syracuseStep 1748415 = 2622623) B2622623
theorem B15126463 : Blo 1746574 15126463 := bstep (se 1 (by rfl) ⟨11344847, by rfl⟩ : syracuseStep 15126463 = 22689695) B22689695
theorem B25202623 : Blo 1746574 25202623 := bstep (se 1 (by rfl) ⟨18901967, by rfl⟩ : syracuseStep 25202623 = 37803935) B37803935
theorem B11956255 : Blo 1746574 11956255 := bstep (se 1 (by rfl) ⟨8967191, by rfl⟩ : syracuseStep 11956255 = 17934383) B17934383
theorem B8400935 : Blo 1746574 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B8393341 : Blo 1746574 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B10089299 : Blo 1746574 10089299 := bstep (se 1 (by rfl) ⟨7566974, by rfl⟩ : syracuseStep 10089299 = 15133949) B15133949
theorem B5895017 : Blo 1746574 5895017 := bstep (se 2 (by rfl) ⟨2210631, by rfl⟩ : syracuseStep 5895017 = 4421263) B4421263
theorem B6632351 : Blo 1746574 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B36362141 : Blo 1746574 36362141 := bstep (se 3 (by rfl) ⟨6817901, by rfl⟩ : syracuseStep 36362141 = 13635803) B13635803
theorem B5601403 : Blo 1746574 5601403 := bstep (se 1 (by rfl) ⟨4201052, by rfl⟩ : syracuseStep 5601403 = 8402105) B8402105
theorem B8845523 : Blo 1746574 8845523 := bstep (se 1 (by rfl) ⟨6634142, by rfl⟩ : syracuseStep 8845523 = 13268285) B13268285
theorem B3930785 : Blo 1746574 3930785 := bstep (se 2 (by rfl) ⟨1474044, by rfl⟩ : syracuseStep 3930785 = 2948089) B2948089
theorem B2620223 : Blo 1746574 2620223 := bstep (se 1 (by rfl) ⟨1965167, by rfl⟩ : syracuseStep 2620223 = 3930335) B3930335
theorem B8846333 : Blo 1746574 8846333 := bstep (se 3 (by rfl) ⟨1658687, by rfl⟩ : syracuseStep 8846333 = 3317375) B3317375
theorem B2128927 : Blo 1746574 2128927 := bstep (se 1 (by rfl) ⟨1596695, by rfl⟩ : syracuseStep 2128927 = 3193391) B3193391
theorem B12598487 : Blo 1746574 12598487 := bstep (se 1 (by rfl) ⟨9448865, by rfl⟩ : syracuseStep 12598487 = 18897731) B18897731
theorem B2620655 : Blo 1746574 2620655 := bstep (se 1 (by rfl) ⟨1965491, by rfl⟩ : syracuseStep 2620655 = 3930983) B3930983
theorem B1965307 : Blo 1746574 1965307 := bstep (se 1 (by rfl) ⟨1473980, by rfl⟩ : syracuseStep 1965307 = 2947961) B2947961
theorem B2948575 : Blo 1746574 2948575 := bstep (se 1 (by rfl) ⟨2211431, by rfl⟩ : syracuseStep 2948575 = 4422863) B4422863
theorem B3931631 : Blo 1746574 3931631 := bstep (se 1 (by rfl) ⟨2948723, by rfl⟩ : syracuseStep 3931631 = 5897447) B5897447
theorem B181559069 : Blo 1746574 181559069 := bstep (se 3 (by rfl) ⟨34042325, by rfl⟩ : syracuseStep 181559069 = 68084651) B68084651
theorem B14933929 : Blo 1746574 14933929 := bstep (se 2 (by rfl) ⟨5600223, by rfl⟩ : syracuseStep 14933929 = 11200447) B11200447
theorem B2621375 : Blo 1746574 2621375 := bstep (se 1 (by rfl) ⟨1966031, by rfl⟩ : syracuseStep 2621375 = 3932063) B3932063
theorem B5898203 : Blo 1746574 5898203 := bstep (se 1 (by rfl) ⟨4423652, by rfl⟩ : syracuseStep 5898203 = 8847305) B8847305
theorem B2949095 : Blo 1746574 2949095 := bstep (se 1 (by rfl) ⟨2211821, by rfl⟩ : syracuseStep 2949095 = 4423643) B4423643
theorem B2621435 : Blo 1746574 2621435 := bstep (se 1 (by rfl) ⟨1966076, by rfl⟩ : syracuseStep 2621435 = 3932153) B3932153
theorem B2621531 : Blo 1746574 2621531 := bstep (se 1 (by rfl) ⟨1966148, by rfl⟩ : syracuseStep 2621531 = 3932297) B3932297
theorem B63766693 : Blo 1746574 63766693 := bstep (se 4 (by rfl) ⟨5978127, by rfl⟩ : syracuseStep 63766693 = 11956255) B11956255
theorem B2621615 : Blo 1746574 2621615 := bstep (se 1 (by rfl) ⟨1966211, by rfl⟩ : syracuseStep 2621615 = 3932423) B3932423
theorem B2621663 : Blo 1746574 2621663 := bstep (se 1 (by rfl) ⟨1966247, by rfl⟩ : syracuseStep 2621663 = 3932495) B3932495
theorem B29843801 : Blo 1746574 29843801 := bstep (se 2 (by rfl) ⟨11191425, by rfl⟩ : syracuseStep 29843801 = 22382851) B22382851
theorem B11190811 : Blo 1746574 11190811 := bstep (se 1 (by rfl) ⟨8393108, by rfl⟩ : syracuseStep 11190811 = 16786217) B16786217
theorem B6726199 : Blo 1746574 6726199 := bstep (se 1 (by rfl) ⟨5044649, by rfl⟩ : syracuseStep 6726199 = 10089299) B10089299
theorem B25887451 : Blo 1746574 25887451 := bstep (se 1 (by rfl) ⟨19415588, by rfl⟩ : syracuseStep 25887451 = 38831177) B38831177
theorem B2949959 : Blo 1746574 2949959 := bstep (se 1 (by rfl) ⟨2212469, by rfl⟩ : syracuseStep 2949959 = 4424939) B4424939
theorem B11191121 : Blo 1746574 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B2622431 : Blo 1746574 2622431 := bstep (se 1 (by rfl) ⟨1966823, by rfl⟩ : syracuseStep 2622431 = 3933647) B3933647
theorem B2622719 : Blo 1746574 2622719 := bstep (se 1 (by rfl) ⟨1967039, by rfl⟩ : syracuseStep 2622719 = 3934079) B3934079
theorem B24241427 : Blo 1746574 24241427 := bstep (se 1 (by rfl) ⟨18181070, by rfl⟩ : syracuseStep 24241427 = 36362141) B36362141
theorem B2622791 : Blo 1746574 2622791 := bstep (se 1 (by rfl) ⟨1967093, by rfl⟩ : syracuseStep 2622791 = 3934187) B3934187
theorem B17942269 : Blo 1746574 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B1746815 : Blo 1746574 1746815 := bstep (se 1 (by rfl) ⟨1310111, by rfl⟩ : syracuseStep 1746815 = 2620223) B2620223
theorem B8398991 : Blo 1746574 8398991 := bstep (se 1 (by rfl) ⟨6299243, by rfl⟩ : syracuseStep 8398991 = 12598487) B12598487
theorem B1747103 : Blo 1746574 1747103 := bstep (se 1 (by rfl) ⟨1310327, by rfl⟩ : syracuseStep 1747103 = 2620655) B2620655
theorem B121039379 : Blo 1746574 121039379 := bstep (se 1 (by rfl) ⟨90779534, by rfl⟩ : syracuseStep 121039379 = 181559069) B181559069
theorem B1747583 : Blo 1746574 1747583 := bstep (se 1 (by rfl) ⟨1310687, by rfl⟩ : syracuseStep 1747583 = 2621375) B2621375
theorem B48474773 : Blo 1746574 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B1747623 : Blo 1746574 1747623 := bstep (se 1 (by rfl) ⟨1310717, by rfl⟩ : syracuseStep 1747623 = 2621435) B2621435
theorem B1747707 : Blo 1746574 1747707 := bstep (se 1 (by rfl) ⟨1310780, by rfl⟩ : syracuseStep 1747707 = 2621561) B2621561
theorem B9956135 : Blo 1746574 9956135 := bstep (se 1 (by rfl) ⟨7467101, by rfl⟩ : syracuseStep 9956135 = 14934203) B14934203
theorem B1747951 : Blo 1746574 1747951 := bstep (se 1 (by rfl) ⟨1310963, by rfl⟩ : syracuseStep 1747951 = 2621927) B2621927
theorem B1748135 : Blo 1746574 1748135 := bstep (se 1 (by rfl) ⟨1311101, by rfl⟩ : syracuseStep 1748135 = 2622203) B2622203
theorem B1748507 : Blo 1746574 1748507 := bstep (se 1 (by rfl) ⟨1311380, by rfl⟩ : syracuseStep 1748507 = 2622761) B2622761
theorem B7466863 : Blo 1746574 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B2838569 : Blo 1746574 2838569 := bstep (se 2 (by rfl) ⟨1064463, by rfl⟩ : syracuseStep 2838569 = 2128927) B2128927
theorem B14922143 : Blo 1746574 14922143 := bstep (se 1 (by rfl) ⟨11191607, by rfl⟩ : syracuseStep 14922143 = 22383215) B22383215
theorem B19911905 : Blo 1746574 19911905 := bstep (se 2 (by rfl) ⟨7466964, by rfl⟩ : syracuseStep 19911905 = 14933929) B14933929
theorem B5600623 : Blo 1746574 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B7468537 : Blo 1746574 7468537 := bstep (se 2 (by rfl) ⟨2800701, by rfl⟩ : syracuseStep 7468537 = 5601403) B5601403
theorem B3930011 : Blo 1746574 3930011 := bstep (se 1 (by rfl) ⟨2947508, by rfl⟩ : syracuseStep 3930011 = 5895017) B5895017
theorem B4421567 : Blo 1746574 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B6633809 : Blo 1746574 6633809 := bstep (se 2 (by rfl) ⟨2487678, by rfl⟩ : syracuseStep 6633809 = 4975357) B4975357
theorem B5897015 : Blo 1746574 5897015 := bstep (se 1 (by rfl) ⟨4422761, by rfl⟩ : syracuseStep 5897015 = 8845523) B8845523
theorem B2620409 : Blo 1746574 2620409 := bstep (se 2 (by rfl) ⟨982653, by rfl⟩ : syracuseStep 2620409 = 1965307) B1965307
theorem B2620523 : Blo 1746574 2620523 := bstep (se 1 (by rfl) ⟨1965392, by rfl⟩ : syracuseStep 2620523 = 3930785) B3930785
theorem B3931433 : Blo 1746574 3931433 := bstep (se 2 (by rfl) ⟨1474287, by rfl⟩ : syracuseStep 3931433 = 2948575) B2948575
theorem B5897555 : Blo 1746574 5897555 := bstep (se 1 (by rfl) ⟨4423166, by rfl⟩ : syracuseStep 5897555 = 8846333) B8846333
theorem B10362203 : Blo 1746574 10362203 := bstep (se 1 (by rfl) ⟨7771652, by rfl⟩ : syracuseStep 10362203 = 15543305) B15543305
theorem B2621087 : Blo 1746574 2621087 := bstep (se 1 (by rfl) ⟨1965815, by rfl⟩ : syracuseStep 2621087 = 3931631) B3931631
theorem B20168617 : Blo 1746574 20168617 := bstep (se 2 (by rfl) ⟨7563231, by rfl⟩ : syracuseStep 20168617 = 15126463) B15126463
theorem B33603497 : Blo 1746574 33603497 := bstep (se 2 (by rfl) ⟨12601311, by rfl⟩ : syracuseStep 33603497 = 25202623) B25202623
theorem B3932135 : Blo 1746574 3932135 := bstep (se 1 (by rfl) ⟨2949101, by rfl⟩ : syracuseStep 3932135 = 5898203) B5898203
theorem B1966063 : Blo 1746574 1966063 := bstep (se 1 (by rfl) ⟨1474547, by rfl⟩ : syracuseStep 1966063 = 2949095) B2949095
theorem B22397309 : Blo 1746574 22397309 := bstep (se 3 (by rfl) ⟨4199495, by rfl⟩ : syracuseStep 22397309 = 8398991) B8398991
theorem B30278069 : Blo 1746574 30278069 := bstep (se 5 (by rfl) ⟨1419284, by rfl⟩ : syracuseStep 30278069 = 2838569) B2838569
theorem B1966639 : Blo 1746574 1966639 := bstep (se 1 (by rfl) ⟨1474979, by rfl⟩ : syracuseStep 1966639 = 2949959) B2949959
theorem B80692919 : Blo 1746574 80692919 := bstep (se 1 (by rfl) ⟨60519689, by rfl⟩ : syracuseStep 80692919 = 121039379) B121039379
theorem B6637423 : Blo 1746574 6637423 := bstep (se 1 (by rfl) ⟨4978067, by rfl⟩ : syracuseStep 6637423 = 9956135) B9956135
theorem B1746939 : Blo 1746574 1746939 := bstep (se 1 (by rfl) ⟨1310204, by rfl⟩ : syracuseStep 1746939 = 2620409) B2620409
theorem B1747015 : Blo 1746574 1747015 := bstep (se 1 (by rfl) ⟨1310261, by rfl⟩ : syracuseStep 1747015 = 2620523) B2620523
theorem B6908135 : Blo 1746574 6908135 := bstep (se 1 (by rfl) ⟨5181101, by rfl⟩ : syracuseStep 6908135 = 10362203) B10362203
theorem B23923025 : Blo 1746574 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B1747391 : Blo 1746574 1747391 := bstep (se 1 (by rfl) ⟨1310543, by rfl⟩ : syracuseStep 1747391 = 2621087) B2621087
theorem B9955817 : Blo 1746574 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B1747687 : Blo 1746574 1747687 := bstep (se 1 (by rfl) ⟨1310765, by rfl⟩ : syracuseStep 1747687 = 2621531) B2621531
theorem B1747743 : Blo 1746574 1747743 := bstep (se 1 (by rfl) ⟨1310807, by rfl⟩ : syracuseStep 1747743 = 2621615) B2621615
theorem B1747775 : Blo 1746574 1747775 := bstep (se 1 (by rfl) ⟨1310831, by rfl⟩ : syracuseStep 1747775 = 2621663) B2621663
theorem B9948095 : Blo 1746574 9948095 := bstep (se 1 (by rfl) ⟨7461071, by rfl⟩ : syracuseStep 9948095 = 14922143) B14922143
theorem B1748287 : Blo 1746574 1748287 := bstep (se 1 (by rfl) ⟨1311215, by rfl⟩ : syracuseStep 1748287 = 2622431) B2622431
theorem B14921081 : Blo 1746574 14921081 := bstep (se 2 (by rfl) ⟨5595405, by rfl⟩ : syracuseStep 14921081 = 11190811) B11190811
theorem B13274603 : Blo 1746574 13274603 := bstep (se 1 (by rfl) ⟨9955952, by rfl⟩ : syracuseStep 13274603 = 19911905) B19911905
theorem B1748479 : Blo 1746574 1748479 := bstep (se 1 (by rfl) ⟨1311359, by rfl⟩ : syracuseStep 1748479 = 2622719) B2622719
theorem B1748527 : Blo 1746574 1748527 := bstep (se 1 (by rfl) ⟨1311395, by rfl⟩ : syracuseStep 1748527 = 2622791) B2622791
theorem B34516601 : Blo 1746574 34516601 := bstep (se 2 (by rfl) ⟨12943725, by rfl⟩ : syracuseStep 34516601 = 25887451) B25887451
theorem B7467497 : Blo 1746574 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B9958049 : Blo 1746574 9958049 := bstep (se 2 (by rfl) ⟨3734268, by rfl⟩ : syracuseStep 9958049 = 7468537) B7468537
theorem B26891489 : Blo 1746574 26891489 := bstep (se 2 (by rfl) ⟨10084308, by rfl⟩ : syracuseStep 26891489 = 20168617) B20168617
theorem B22402331 : Blo 1746574 22402331 := bstep (se 1 (by rfl) ⟨16801748, by rfl⟩ : syracuseStep 22402331 = 33603497) B33603497
theorem B85022257 : Blo 1746574 85022257 := bstep (se 2 (by rfl) ⟨31883346, by rfl⟩ : syracuseStep 85022257 = 63766693) B63766693
theorem B19895867 : Blo 1746574 19895867 := bstep (se 1 (by rfl) ⟨14921900, by rfl⟩ : syracuseStep 19895867 = 29843801) B29843801
theorem B7460747 : Blo 1746574 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B8968265 : Blo 1746574 8968265 := bstep (se 2 (by rfl) ⟨3363099, by rfl⟩ : syracuseStep 8968265 = 6726199) B6726199
theorem B16160951 : Blo 1746574 16160951 := bstep (se 1 (by rfl) ⟨12120713, by rfl⟩ : syracuseStep 16160951 = 24241427) B24241427
theorem B2620007 : Blo 1746574 2620007 := bstep (se 1 (by rfl) ⟨1965005, by rfl⟩ : syracuseStep 2620007 = 3930011) B3930011
theorem B2947711 : Blo 1746574 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B4422539 : Blo 1746574 4422539 := bstep (se 1 (by rfl) ⟨3316904, by rfl⟩ : syracuseStep 4422539 = 6633809) B6633809
theorem B32316515 : Blo 1746574 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B3931343 : Blo 1746574 3931343 := bstep (se 1 (by rfl) ⟨2948507, by rfl⟩ : syracuseStep 3931343 = 5897015) B5897015
theorem B2620955 : Blo 1746574 2620955 := bstep (se 1 (by rfl) ⟨1965716, by rfl⟩ : syracuseStep 2620955 = 3931433) B3931433
theorem B3931703 : Blo 1746574 3931703 := bstep (se 1 (by rfl) ⟨2948777, by rfl⟩ : syracuseStep 3931703 = 5897555) B5897555
theorem B2621417 : Blo 1746574 2621417 := bstep (se 2 (by rfl) ⟨983031, by rfl⟩ : syracuseStep 2621417 = 1966063) B1966063
theorem B2621423 : Blo 1746574 2621423 := bstep (se 1 (by rfl) ⟨1966067, by rfl⟩ : syracuseStep 2621423 = 3932135) B3932135
theorem B20185379 : Blo 1746574 20185379 := bstep (se 1 (by rfl) ⟨15139034, by rfl⟩ : syracuseStep 20185379 = 30278069) B30278069
theorem B2622185 : Blo 1746574 2622185 := bstep (se 2 (by rfl) ⟨983319, by rfl⟩ : syracuseStep 2622185 = 1966639) B1966639
theorem B14934887 : Blo 1746574 14934887 := bstep (se 1 (by rfl) ⟨11201165, by rfl⟩ : syracuseStep 14934887 = 22402331) B22402331
theorem B13263911 : Blo 1746574 13263911 := bstep (se 1 (by rfl) ⟨9947933, by rfl⟩ : syracuseStep 13263911 = 19895867) B19895867
theorem B4973831 : Blo 1746574 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B10773967 : Blo 1746574 10773967 := bstep (se 1 (by rfl) ⟨8080475, by rfl⟩ : syracuseStep 10773967 = 16160951) B16160951
theorem B6637211 : Blo 1746574 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B1746671 : Blo 1746574 1746671 := bstep (se 1 (by rfl) ⟨1310003, by rfl⟩ : syracuseStep 1746671 = 2620007) B2620007
theorem B113363009 : Blo 1746574 113363009 := bstep (se 2 (by rfl) ⟨42511128, by rfl⟩ : syracuseStep 113363009 = 85022257) B85022257
theorem B9947387 : Blo 1746574 9947387 := bstep (se 1 (by rfl) ⟨7460540, by rfl⟩ : syracuseStep 9947387 = 14921081) B14921081
theorem B8849735 : Blo 1746574 8849735 := bstep (se 1 (by rfl) ⟨6637301, by rfl⟩ : syracuseStep 8849735 = 13274603) B13274603
theorem B1747303 : Blo 1746574 1747303 := bstep (se 1 (by rfl) ⟨1310477, by rfl⟩ : syracuseStep 1747303 = 2620955) B2620955
theorem B8849897 : Blo 1746574 8849897 := bstep (se 2 (by rfl) ⟨3318711, by rfl⟩ : syracuseStep 8849897 = 6637423) B6637423
theorem B1747611 : Blo 1746574 1747611 := bstep (se 1 (by rfl) ⟨1310708, by rfl⟩ : syracuseStep 1747611 = 2621417) B2621417
theorem B1747615 : Blo 1746574 1747615 := bstep (se 1 (by rfl) ⟨1310711, by rfl⟩ : syracuseStep 1747615 = 2621423) B2621423
theorem B6638699 : Blo 1746574 6638699 := bstep (se 1 (by rfl) ⟨4979024, by rfl⟩ : syracuseStep 6638699 = 9958049) B9958049
theorem B17927659 : Blo 1746574 17927659 := bstep (se 1 (by rfl) ⟨13445744, by rfl⟩ : syracuseStep 17927659 = 26891489) B26891489
theorem B6632063 : Blo 1746574 6632063 := bstep (se 1 (by rfl) ⟨4974047, by rfl⟩ : syracuseStep 6632063 = 9948095) B9948095
theorem B14931539 : Blo 1746574 14931539 := bstep (se 1 (by rfl) ⟨11198654, by rfl⟩ : syracuseStep 14931539 = 22397309) B22397309
theorem B4978331 : Blo 1746574 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B3930281 : Blo 1746574 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B53795279 : Blo 1746574 53795279 := bstep (se 1 (by rfl) ⟨40346459, by rfl⟩ : syracuseStep 53795279 = 80692919) B80692919
theorem B5978843 : Blo 1746574 5978843 := bstep (se 1 (by rfl) ⟨4484132, by rfl⟩ : syracuseStep 5978843 = 8968265) B8968265
theorem B15948683 : Blo 1746574 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B2948359 : Blo 1746574 2948359 := bstep (se 1 (by rfl) ⟨2211269, by rfl⟩ : syracuseStep 2948359 = 4422539) B4422539
theorem B21544343 : Blo 1746574 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B2620895 : Blo 1746574 2620895 := bstep (se 1 (by rfl) ⟨1965671, by rfl⟩ : syracuseStep 2620895 = 3931343) B3931343
theorem B2621135 : Blo 1746574 2621135 := bstep (se 1 (by rfl) ⟨1965851, by rfl⟩ : syracuseStep 2621135 = 3931703) B3931703
theorem B73686773 : Blo 1746574 73686773 := bstep (se 5 (by rfl) ⟨3454067, by rfl⟩ : syracuseStep 73686773 = 6908135) B6908135
theorem B23011067 : Blo 1746574 23011067 := bstep (se 1 (by rfl) ⟨17258300, by rfl⟩ : syracuseStep 23011067 = 34516601) B34516601
theorem B9954359 : Blo 1746574 9954359 := bstep (se 1 (by rfl) ⟨7465769, by rfl⟩ : syracuseStep 9954359 = 14931539) B14931539
theorem B4424807 : Blo 1746574 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B3318887 : Blo 1746574 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B5899823 : Blo 1746574 5899823 := bstep (se 1 (by rfl) ⟨4424867, by rfl⟩ : syracuseStep 5899823 = 8849735) B8849735
theorem B5899931 : Blo 1746574 5899931 := bstep (se 1 (by rfl) ⟨4424948, by rfl⟩ : syracuseStep 5899931 = 8849897) B8849897
theorem B4425799 : Blo 1746574 4425799 := bstep (se 1 (by rfl) ⟨3319349, by rfl⟩ : syracuseStep 4425799 = 6638699) B6638699
theorem B14362895 : Blo 1746574 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B1747263 : Blo 1746574 1747263 := bstep (se 1 (by rfl) ⟨1310447, by rfl⟩ : syracuseStep 1747263 = 2620895) B2620895
theorem B1747423 : Blo 1746574 1747423 := bstep (se 1 (by rfl) ⟨1310567, by rfl⟩ : syracuseStep 1747423 = 2621135) B2621135
theorem B1748123 : Blo 1746574 1748123 := bstep (se 1 (by rfl) ⟨1311092, by rfl⟩ : syracuseStep 1748123 = 2622185) B2622185
theorem B9956591 : Blo 1746574 9956591 := bstep (se 1 (by rfl) ⟨7467443, by rfl⟩ : syracuseStep 9956591 = 14934887) B14934887
theorem B8842607 : Blo 1746574 8842607 := bstep (se 1 (by rfl) ⟨6631955, by rfl⟩ : syracuseStep 8842607 = 13263911) B13263911
theorem B75575339 : Blo 1746574 75575339 := bstep (se 1 (by rfl) ⟨56681504, by rfl⟩ : syracuseStep 75575339 = 113363009) B113363009
theorem B6631591 : Blo 1746574 6631591 := bstep (se 1 (by rfl) ⟨4973693, by rfl⟩ : syracuseStep 6631591 = 9947387) B9947387
theorem B3985895 : Blo 1746574 3985895 := bstep (se 1 (by rfl) ⟨2989421, by rfl⟩ : syracuseStep 3985895 = 5978843) B5978843
theorem B14365289 : Blo 1746574 14365289 := bstep (se 2 (by rfl) ⟨5386983, by rfl⟩ : syracuseStep 14365289 = 10773967) B10773967
theorem B49124515 : Blo 1746574 49124515 := bstep (se 1 (by rfl) ⟨36843386, by rfl⟩ : syracuseStep 49124515 = 73686773) B73686773
theorem B15340711 : Blo 1746574 15340711 := bstep (se 1 (by rfl) ⟨11505533, by rfl⟩ : syracuseStep 15340711 = 23011067) B23011067
theorem B13456919 : Blo 1746574 13456919 := bstep (se 1 (by rfl) ⟨10092689, by rfl⟩ : syracuseStep 13456919 = 20185379) B20185379
theorem B4421375 : Blo 1746574 4421375 := bstep (se 1 (by rfl) ⟨3316031, by rfl⟩ : syracuseStep 4421375 = 6632063) B6632063
theorem B3315887 : Blo 1746574 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B2620187 : Blo 1746574 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B35863519 : Blo 1746574 35863519 := bstep (se 1 (by rfl) ⟨26897639, by rfl⟩ : syracuseStep 35863519 = 53795279) B53795279
theorem B3931145 : Blo 1746574 3931145 := bstep (se 2 (by rfl) ⟨1474179, by rfl⟩ : syracuseStep 3931145 = 2948359) B2948359
theorem B10632455 : Blo 1746574 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B23903545 : Blo 1746574 23903545 := bstep (se 2 (by rfl) ⟨8963829, by rfl⟩ : syracuseStep 23903545 = 17927659) B17927659
theorem B6636239 : Blo 1746574 6636239 := bstep (se 1 (by rfl) ⟨4977179, by rfl⟩ : syracuseStep 6636239 = 9954359) B9954359
theorem B2949871 : Blo 1746574 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B2212591 : Blo 1746574 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B8971279 : Blo 1746574 8971279 := bstep (se 1 (by rfl) ⟨6728459, by rfl⟩ : syracuseStep 8971279 = 13456919) B13456919
theorem B3933215 : Blo 1746574 3933215 := bstep (se 1 (by rfl) ⟨2949911, by rfl⟩ : syracuseStep 3933215 = 5899823) B5899823
theorem B3933287 : Blo 1746574 3933287 := bstep (se 1 (by rfl) ⟨2949965, by rfl⟩ : syracuseStep 3933287 = 5899931) B5899931
theorem B47818025 : Blo 1746574 47818025 := bstep (se 2 (by rfl) ⟨17931759, by rfl⟩ : syracuseStep 47818025 = 35863519) B35863519
theorem B38307437 : Blo 1746574 38307437 := bstep (se 3 (by rfl) ⟨7182644, by rfl⟩ : syracuseStep 38307437 = 14365289) B14365289
theorem B1746791 : Blo 1746574 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B6637727 : Blo 1746574 6637727 := bstep (se 1 (by rfl) ⟨4978295, by rfl⟩ : syracuseStep 6637727 = 9956591) B9956591
theorem B7088303 : Blo 1746574 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B50383559 : Blo 1746574 50383559 := bstep (se 1 (by rfl) ⟨37787669, by rfl⟩ : syracuseStep 50383559 = 75575339) B75575339
theorem B5901065 : Blo 1746574 5901065 := bstep (se 2 (by rfl) ⟨2212899, by rfl⟩ : syracuseStep 5901065 = 4425799) B4425799
theorem B8842121 : Blo 1746574 8842121 := bstep (se 2 (by rfl) ⟨3315795, by rfl⟩ : syracuseStep 8842121 = 6631591) B6631591
theorem B10629053 : Blo 1746574 10629053 := bstep (se 3 (by rfl) ⟨1992947, by rfl⟩ : syracuseStep 10629053 = 3985895) B3985895
theorem B65499353 : Blo 1746574 65499353 := bstep (se 2 (by rfl) ⟨24562257, by rfl⟩ : syracuseStep 65499353 = 49124515) B49124515
theorem B31871393 : Blo 1746574 31871393 := bstep (se 2 (by rfl) ⟨11951772, by rfl⟩ : syracuseStep 31871393 = 23903545) B23903545
theorem B5895071 : Blo 1746574 5895071 := bstep (se 1 (by rfl) ⟨4421303, by rfl⟩ : syracuseStep 5895071 = 8842607) B8842607
theorem B2947583 : Blo 1746574 2947583 := bstep (se 1 (by rfl) ⟨2210687, by rfl⟩ : syracuseStep 2947583 = 4421375) B4421375
theorem B2210591 : Blo 1746574 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B9575263 : Blo 1746574 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B20454281 : Blo 1746574 20454281 := bstep (se 2 (by rfl) ⟨7670355, by rfl⟩ : syracuseStep 20454281 = 15340711) B15340711
theorem B2620763 : Blo 1746574 2620763 := bstep (se 1 (by rfl) ⟨1965572, by rfl⟩ : syracuseStep 2620763 = 3931145) B3931145
theorem B4424159 : Blo 1746574 4424159 := bstep (se 1 (by rfl) ⟨3318119, by rfl⟩ : syracuseStep 4424159 = 6636239) B6636239
theorem B2622143 : Blo 1746574 2622143 := bstep (se 1 (by rfl) ⟨1966607, by rfl⟩ : syracuseStep 2622143 = 3933215) B3933215
theorem B2622191 : Blo 1746574 2622191 := bstep (se 1 (by rfl) ⟨1966643, by rfl⟩ : syracuseStep 2622191 = 3933287) B3933287
theorem B3933161 : Blo 1746574 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B2950121 : Blo 1746574 2950121 := bstep (se 2 (by rfl) ⟨1106295, by rfl⟩ : syracuseStep 2950121 = 2212591) B2212591
theorem B4425151 : Blo 1746574 4425151 := bstep (se 1 (by rfl) ⟨3318863, by rfl⟩ : syracuseStep 4425151 = 6637727) B6637727
theorem B33589039 : Blo 1746574 33589039 := bstep (se 1 (by rfl) ⟨25191779, by rfl⟩ : syracuseStep 33589039 = 50383559) B50383559
theorem B3934043 : Blo 1746574 3934043 := bstep (se 1 (by rfl) ⟨2950532, by rfl⟩ : syracuseStep 3934043 = 5901065) B5901065
theorem B1747175 : Blo 1746574 1747175 := bstep (se 1 (by rfl) ⟨1310381, by rfl⟩ : syracuseStep 1747175 = 2620763) B2620763
theorem B43666235 : Blo 1746574 43666235 := bstep (se 1 (by rfl) ⟨32749676, by rfl⟩ : syracuseStep 43666235 = 65499353) B65499353
theorem B31878683 : Blo 1746574 31878683 := bstep (se 1 (by rfl) ⟨23909012, by rfl⟩ : syracuseStep 31878683 = 47818025) B47818025
theorem B25538291 : Blo 1746574 25538291 := bstep (se 1 (by rfl) ⟨19153718, by rfl⟩ : syracuseStep 25538291 = 38307437) B38307437
theorem B5894747 : Blo 1746574 5894747 := bstep (se 1 (by rfl) ⟨4421060, by rfl⟩ : syracuseStep 5894747 = 8842121) B8842121
theorem B13636187 : Blo 1746574 13636187 := bstep (se 1 (by rfl) ⟨10227140, by rfl⟩ : syracuseStep 13636187 = 20454281) B20454281
theorem B5894909 : Blo 1746574 5894909 := bstep (se 3 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 5894909 = 2210591) B2210591
theorem B47846821 : Blo 1746574 47846821 := bstep (se 4 (by rfl) ⟨4485639, by rfl⟩ : syracuseStep 47846821 = 8971279) B8971279
theorem B21247595 : Blo 1746574 21247595 := bstep (se 1 (by rfl) ⟨15935696, by rfl⟩ : syracuseStep 21247595 = 31871393) B31871393
theorem B3930047 : Blo 1746574 3930047 := bstep (se 1 (by rfl) ⟨2947535, by rfl⟩ : syracuseStep 3930047 = 5895071) B5895071
theorem B4725535 : Blo 1746574 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B1965055 : Blo 1746574 1965055 := bstep (se 1 (by rfl) ⟨1473791, by rfl⟩ : syracuseStep 1965055 = 2947583) B2947583
theorem B51068069 : Blo 1746574 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B7086035 : Blo 1746574 7086035 := bstep (se 1 (by rfl) ⟨5314526, by rfl⟩ : syracuseStep 7086035 = 10629053) B10629053
theorem B2949439 : Blo 1746574 2949439 := bstep (se 1 (by rfl) ⟨2212079, by rfl⟩ : syracuseStep 2949439 = 4424159) B4424159
theorem B2622107 : Blo 1746574 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B1966747 : Blo 1746574 1966747 := bstep (se 1 (by rfl) ⟨1475060, by rfl⟩ : syracuseStep 1966747 = 2950121) B2950121
theorem B6300713 : Blo 1746574 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B14165063 : Blo 1746574 14165063 := bstep (se 1 (by rfl) ⟨10623797, by rfl⟩ : syracuseStep 14165063 = 21247595) B21247595
theorem B2622695 : Blo 1746574 2622695 := bstep (se 1 (by rfl) ⟨1967021, by rfl⟩ : syracuseStep 2622695 = 3934043) B3934043
theorem B5900201 : Blo 1746574 5900201 := bstep (se 2 (by rfl) ⟨2212575, by rfl⟩ : syracuseStep 5900201 = 4425151) B4425151
theorem B21252455 : Blo 1746574 21252455 := bstep (se 1 (by rfl) ⟨15939341, by rfl⟩ : syracuseStep 21252455 = 31878683) B31878683
theorem B17025527 : Blo 1746574 17025527 := bstep (se 1 (by rfl) ⟨12769145, by rfl⟩ : syracuseStep 17025527 = 25538291) B25538291
theorem B1748095 : Blo 1746574 1748095 := bstep (se 1 (by rfl) ⟨1311071, by rfl⟩ : syracuseStep 1748095 = 2622143) B2622143
theorem B1748127 : Blo 1746574 1748127 := bstep (se 1 (by rfl) ⟨1311095, by rfl⟩ : syracuseStep 1748127 = 2622191) B2622191
theorem B29110823 : Blo 1746574 29110823 := bstep (se 1 (by rfl) ⟨21833117, by rfl⟩ : syracuseStep 29110823 = 43666235) B43666235
theorem B63795761 : Blo 1746574 63795761 := bstep (se 2 (by rfl) ⟨23923410, by rfl⟩ : syracuseStep 63795761 = 47846821) B47846821
theorem B4724023 : Blo 1746574 4724023 := bstep (se 1 (by rfl) ⟨3543017, by rfl⟩ : syracuseStep 4724023 = 7086035) B7086035
theorem B3929831 : Blo 1746574 3929831 := bstep (se 1 (by rfl) ⟨2947373, by rfl⟩ : syracuseStep 3929831 = 5894747) B5894747
theorem B9090791 : Blo 1746574 9090791 := bstep (se 1 (by rfl) ⟨6818093, by rfl⟩ : syracuseStep 9090791 = 13636187) B13636187
theorem B3929939 : Blo 1746574 3929939 := bstep (se 1 (by rfl) ⟨2947454, by rfl⟩ : syracuseStep 3929939 = 5894909) B5894909
theorem B2620031 : Blo 1746574 2620031 := bstep (se 1 (by rfl) ⟨1965023, by rfl⟩ : syracuseStep 2620031 = 3930047) B3930047
theorem B2620073 : Blo 1746574 2620073 := bstep (se 2 (by rfl) ⟨982527, by rfl⟩ : syracuseStep 2620073 = 1965055) B1965055
theorem B34045379 : Blo 1746574 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B44785385 : Blo 1746574 44785385 := bstep (se 2 (by rfl) ⟨16794519, by rfl⟩ : syracuseStep 44785385 = 33589039) B33589039
theorem B16801901 : Blo 1746574 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B19407215 : Blo 1746574 19407215 := bstep (se 1 (by rfl) ⟨14555411, by rfl⟩ : syracuseStep 19407215 = 29110823) B29110823
theorem B3932585 : Blo 1746574 3932585 := bstep (se 2 (by rfl) ⟨1474719, by rfl⟩ : syracuseStep 3932585 = 2949439) B2949439
theorem B2622329 : Blo 1746574 2622329 := bstep (se 2 (by rfl) ⟨983373, by rfl⟩ : syracuseStep 2622329 = 1966747) B1966747
theorem B3933467 : Blo 1746574 3933467 := bstep (se 1 (by rfl) ⟨2950100, by rfl⟩ : syracuseStep 3933467 = 5900201) B5900201
theorem B1746687 : Blo 1746574 1746687 := bstep (se 1 (by rfl) ⟨1310015, by rfl⟩ : syracuseStep 1746687 = 2620031) B2620031
theorem B1746715 : Blo 1746574 1746715 := bstep (se 1 (by rfl) ⟨1310036, by rfl⟩ : syracuseStep 1746715 = 2620073) B2620073
theorem B1748071 : Blo 1746574 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B1748463 : Blo 1746574 1748463 := bstep (se 1 (by rfl) ⟨1311347, by rfl⟩ : syracuseStep 1748463 = 2622695) B2622695
theorem B14168303 : Blo 1746574 14168303 := bstep (se 1 (by rfl) ⟨10626227, by rfl⟩ : syracuseStep 14168303 = 21252455) B21252455
theorem B11350351 : Blo 1746574 11350351 := bstep (se 1 (by rfl) ⟨8512763, by rfl⟩ : syracuseStep 11350351 = 17025527) B17025527
theorem B22696919 : Blo 1746574 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B29856923 : Blo 1746574 29856923 := bstep (se 1 (by rfl) ⟨22392692, by rfl⟩ : syracuseStep 29856923 = 44785385) B44785385
theorem B42530507 : Blo 1746574 42530507 := bstep (se 1 (by rfl) ⟨31897880, by rfl⟩ : syracuseStep 42530507 = 63795761) B63795761
theorem B9443375 : Blo 1746574 9443375 := bstep (se 1 (by rfl) ⟨7082531, by rfl⟩ : syracuseStep 9443375 = 14165063) B14165063
theorem B2619887 : Blo 1746574 2619887 := bstep (se 1 (by rfl) ⟨1964915, by rfl⟩ : syracuseStep 2619887 = 3929831) B3929831
theorem B6060527 : Blo 1746574 6060527 := bstep (se 1 (by rfl) ⟨4545395, by rfl⟩ : syracuseStep 6060527 = 9090791) B9090791
theorem B2619959 : Blo 1746574 2619959 := bstep (se 1 (by rfl) ⟨1964969, by rfl⟩ : syracuseStep 2619959 = 3929939) B3929939
theorem B6298697 : Blo 1746574 6298697 := bstep (se 2 (by rfl) ⟨2362011, by rfl⟩ : syracuseStep 6298697 = 4724023) B4724023
theorem B9445535 : Blo 1746574 9445535 := bstep (se 1 (by rfl) ⟨7084151, by rfl⟩ : syracuseStep 9445535 = 14168303) B14168303
theorem B2621723 : Blo 1746574 2621723 := bstep (se 1 (by rfl) ⟨1966292, by rfl⟩ : syracuseStep 2621723 = 3932585) B3932585
theorem B15131279 : Blo 1746574 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B2622311 : Blo 1746574 2622311 := bstep (se 1 (by rfl) ⟨1966733, by rfl⟩ : syracuseStep 2622311 = 3933467) B3933467
theorem B28353671 : Blo 1746574 28353671 := bstep (se 1 (by rfl) ⟨21265253, by rfl⟩ : syracuseStep 28353671 = 42530507) B42530507
theorem B1746591 : Blo 1746574 1746591 := bstep (se 1 (by rfl) ⟨1309943, by rfl⟩ : syracuseStep 1746591 = 2619887) B2619887
theorem B4040351 : Blo 1746574 4040351 := bstep (se 1 (by rfl) ⟨3030263, by rfl⟩ : syracuseStep 4040351 = 6060527) B6060527
theorem B1746639 : Blo 1746574 1746639 := bstep (se 1 (by rfl) ⟨1309979, by rfl⟩ : syracuseStep 1746639 = 2619959) B2619959
theorem B11201267 : Blo 1746574 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B12938143 : Blo 1746574 12938143 := bstep (se 1 (by rfl) ⟨9703607, by rfl⟩ : syracuseStep 12938143 = 19407215) B19407215
theorem B15133801 : Blo 1746574 15133801 := bstep (se 2 (by rfl) ⟨5675175, by rfl⟩ : syracuseStep 15133801 = 11350351) B11350351
theorem B1748219 : Blo 1746574 1748219 := bstep (se 1 (by rfl) ⟨1311164, by rfl⟩ : syracuseStep 1748219 = 2622329) B2622329
theorem B6295583 : Blo 1746574 6295583 := bstep (se 1 (by rfl) ⟨4721687, by rfl⟩ : syracuseStep 6295583 = 9443375) B9443375
theorem B4199131 : Blo 1746574 4199131 := bstep (se 1 (by rfl) ⟨3149348, by rfl⟩ : syracuseStep 4199131 = 6298697) B6298697
theorem B19904615 : Blo 1746574 19904615 := bstep (se 1 (by rfl) ⟨14928461, by rfl⟩ : syracuseStep 19904615 = 29856923) B29856923
theorem B20178401 : Blo 1746574 20178401 := bstep (se 2 (by rfl) ⟨7566900, by rfl⟩ : syracuseStep 20178401 = 15133801) B15133801
theorem B29870045 : Blo 1746574 29870045 := bstep (se 3 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 29870045 = 11201267) B11201267
theorem B4197055 : Blo 1746574 4197055 := bstep (se 1 (by rfl) ⟨3147791, by rfl⟩ : syracuseStep 4197055 = 6295583) B6295583
theorem B1747815 : Blo 1746574 1747815 := bstep (se 1 (by rfl) ⟨1310861, by rfl⟩ : syracuseStep 1747815 = 2621723) B2621723
theorem B10087519 : Blo 1746574 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B1748207 : Blo 1746574 1748207 := bstep (se 1 (by rfl) ⟨1311155, by rfl⟩ : syracuseStep 1748207 = 2622311) B2622311
theorem B18902447 : Blo 1746574 18902447 := bstep (se 1 (by rfl) ⟨14176835, by rfl⟩ : syracuseStep 18902447 = 28353671) B28353671
theorem B5598841 : Blo 1746574 5598841 := bstep (se 2 (by rfl) ⟨2099565, by rfl⟩ : syracuseStep 5598841 = 4199131) B4199131
theorem B6297023 : Blo 1746574 6297023 := bstep (se 1 (by rfl) ⟨4722767, by rfl⟩ : syracuseStep 6297023 = 9445535) B9445535
theorem B2693567 : Blo 1746574 2693567 := bstep (se 1 (by rfl) ⟨2020175, by rfl⟩ : syracuseStep 2693567 = 4040351) B4040351
theorem B17250857 : Blo 1746574 17250857 := bstep (se 2 (by rfl) ⟨6469071, by rfl⟩ : syracuseStep 17250857 = 12938143) B12938143
theorem B13269743 : Blo 1746574 13269743 := bstep (se 1 (by rfl) ⟨9952307, by rfl⟩ : syracuseStep 13269743 = 19904615) B19904615
theorem B5596073 : Blo 1746574 5596073 := bstep (se 2 (by rfl) ⟨2098527, by rfl⟩ : syracuseStep 5596073 = 4197055) B4197055
theorem B7465121 : Blo 1746574 7465121 := bstep (se 2 (by rfl) ⟨2799420, by rfl⟩ : syracuseStep 7465121 = 5598841) B5598841
theorem B12601631 : Blo 1746574 12601631 := bstep (se 1 (by rfl) ⟨9451223, by rfl⟩ : syracuseStep 12601631 = 18902447) B18902447
theorem B4198015 : Blo 1746574 4198015 := bstep (se 1 (by rfl) ⟨3148511, by rfl⟩ : syracuseStep 4198015 = 6297023) B6297023
theorem B53809069 : Blo 1746574 53809069 := bstep (se 3 (by rfl) ⟨10089200, by rfl⟩ : syracuseStep 53809069 = 20178401) B20178401
theorem B7182845 : Blo 1746574 7182845 := bstep (se 3 (by rfl) ⟨1346783, by rfl⟩ : syracuseStep 7182845 = 2693567) B2693567
theorem B19913363 : Blo 1746574 19913363 := bstep (se 1 (by rfl) ⟨14935022, by rfl⟩ : syracuseStep 19913363 = 29870045) B29870045
theorem B13450025 : Blo 1746574 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B11500571 : Blo 1746574 11500571 := bstep (se 1 (by rfl) ⟨8625428, by rfl⟩ : syracuseStep 11500571 = 17250857) B17250857
theorem B8846495 : Blo 1746574 8846495 := bstep (se 1 (by rfl) ⟨6634871, by rfl⟩ : syracuseStep 8846495 = 13269743) B13269743
theorem B5597353 : Blo 1746574 5597353 := bstep (se 2 (by rfl) ⟨2099007, by rfl⟩ : syracuseStep 5597353 = 4198015) B4198015
theorem B3730715 : Blo 1746574 3730715 := bstep (se 1 (by rfl) ⟨2798036, by rfl⟩ : syracuseStep 3730715 = 5596073) B5596073
theorem B4976747 : Blo 1746574 4976747 := bstep (se 1 (by rfl) ⟨3732560, by rfl⟩ : syracuseStep 4976747 = 7465121) B7465121
theorem B8401087 : Blo 1746574 8401087 := bstep (se 1 (by rfl) ⟨6300815, by rfl⟩ : syracuseStep 8401087 = 12601631) B12601631
theorem B4788563 : Blo 1746574 4788563 := bstep (se 1 (by rfl) ⟨3591422, by rfl⟩ : syracuseStep 4788563 = 7182845) B7182845
theorem B13275575 : Blo 1746574 13275575 := bstep (se 1 (by rfl) ⟨9956681, by rfl⟩ : syracuseStep 13275575 = 19913363) B19913363
theorem B8966683 : Blo 1746574 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B7667047 : Blo 1746574 7667047 := bstep (se 1 (by rfl) ⟨5750285, by rfl⟩ : syracuseStep 7667047 = 11500571) B11500571
theorem B5897663 : Blo 1746574 5897663 := bstep (se 1 (by rfl) ⟨4423247, by rfl⟩ : syracuseStep 5897663 = 8846495) B8846495
theorem B71745425 : Blo 1746574 71745425 := bstep (se 2 (by rfl) ⟨26904534, by rfl⟩ : syracuseStep 71745425 = 53809069) B53809069
theorem B3317831 : Blo 1746574 3317831 := bstep (se 1 (by rfl) ⟨2488373, by rfl⟩ : syracuseStep 3317831 = 4976747) B4976747
theorem B29852549 : Blo 1746574 29852549 := bstep (se 4 (by rfl) ⟨2798676, by rfl⟩ : syracuseStep 29852549 = 5597353) B5597353
theorem B11201449 : Blo 1746574 11201449 := bstep (se 2 (by rfl) ⟨4200543, by rfl⟩ : syracuseStep 11201449 = 8401087) B8401087
theorem B8850383 : Blo 1746574 8850383 := bstep (se 1 (by rfl) ⟨6637787, by rfl⟩ : syracuseStep 8850383 = 13275575) B13275575
theorem B2487143 : Blo 1746574 2487143 := bstep (se 1 (by rfl) ⟨1865357, by rfl⟩ : syracuseStep 2487143 = 3730715) B3730715
theorem B47830283 : Blo 1746574 47830283 := bstep (se 1 (by rfl) ⟨35872712, by rfl⟩ : syracuseStep 47830283 = 71745425) B71745425
theorem B47822309 : Blo 1746574 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B12769501 : Blo 1746574 12769501 := bstep (se 3 (by rfl) ⟨2394281, by rfl⟩ : syracuseStep 12769501 = 4788563) B4788563
theorem B10222729 : Blo 1746574 10222729 := bstep (se 2 (by rfl) ⟨3833523, by rfl⟩ : syracuseStep 10222729 = 7667047) B7667047
theorem B3931775 : Blo 1746574 3931775 := bstep (se 1 (by rfl) ⟨2948831, by rfl⟩ : syracuseStep 3931775 = 5897663) B5897663
theorem B2211887 : Blo 1746574 2211887 := bstep (se 1 (by rfl) ⟨1658915, by rfl⟩ : syracuseStep 2211887 = 3317831) B3317831
theorem B14935265 : Blo 1746574 14935265 := bstep (se 2 (by rfl) ⟨5600724, by rfl⟩ : syracuseStep 14935265 = 11201449) B11201449
theorem B5900255 : Blo 1746574 5900255 := bstep (se 1 (by rfl) ⟨4425191, by rfl⟩ : syracuseStep 5900255 = 8850383) B8850383
theorem B17026001 : Blo 1746574 17026001 := bstep (se 2 (by rfl) ⟨6384750, by rfl⟩ : syracuseStep 17026001 = 12769501) B12769501
theorem B19901699 : Blo 1746574 19901699 := bstep (se 1 (by rfl) ⟨14926274, by rfl⟩ : syracuseStep 19901699 = 29852549) B29852549
theorem B54521221 : Blo 1746574 54521221 := bstep (se 4 (by rfl) ⟨5111364, by rfl⟩ : syracuseStep 54521221 = 10222729) B10222729
theorem B31886855 : Blo 1746574 31886855 := bstep (se 1 (by rfl) ⟨23915141, by rfl⟩ : syracuseStep 31886855 = 47830283) B47830283
theorem B6632381 : Blo 1746574 6632381 := bstep (se 3 (by rfl) ⟨1243571, by rfl⟩ : syracuseStep 6632381 = 2487143) B2487143
theorem B31881539 : Blo 1746574 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B2621183 : Blo 1746574 2621183 := bstep (se 1 (by rfl) ⟨1965887, by rfl⟩ : syracuseStep 2621183 = 3931775) B3931775
theorem B5898365 : Blo 1746574 5898365 := bstep (se 3 (by rfl) ⟨1105943, by rfl⟩ : syracuseStep 5898365 = 2211887) B2211887
theorem B3933503 : Blo 1746574 3933503 := bstep (se 1 (by rfl) ⟨2950127, by rfl⟩ : syracuseStep 3933503 = 5900255) B5900255
theorem B1747455 : Blo 1746574 1747455 := bstep (se 1 (by rfl) ⟨1310591, by rfl⟩ : syracuseStep 1747455 = 2621183) B2621183
theorem B9956843 : Blo 1746574 9956843 := bstep (se 1 (by rfl) ⟨7467632, by rfl⟩ : syracuseStep 9956843 = 14935265) B14935265
theorem B21254359 : Blo 1746574 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B11350667 : Blo 1746574 11350667 := bstep (se 1 (by rfl) ⟨8513000, by rfl⟩ : syracuseStep 11350667 = 17026001) B17026001
theorem B13267799 : Blo 1746574 13267799 := bstep (se 1 (by rfl) ⟨9950849, by rfl⟩ : syracuseStep 13267799 = 19901699) B19901699
theorem B4421587 : Blo 1746574 4421587 := bstep (se 1 (by rfl) ⟨3316190, by rfl⟩ : syracuseStep 4421587 = 6632381) B6632381
theorem B72694961 : Blo 1746574 72694961 := bstep (se 2 (by rfl) ⟨27260610, by rfl⟩ : syracuseStep 72694961 = 54521221) B54521221
theorem B21257903 : Blo 1746574 21257903 := bstep (se 1 (by rfl) ⟨15943427, by rfl⟩ : syracuseStep 21257903 = 31886855) B31886855
theorem B3932243 : Blo 1746574 3932243 := bstep (se 1 (by rfl) ⟨2949182, by rfl⟩ : syracuseStep 3932243 = 5898365) B5898365
theorem B2622335 : Blo 1746574 2622335 := bstep (se 1 (by rfl) ⟨1966751, by rfl⟩ : syracuseStep 2622335 = 3933503) B3933503
theorem B6637895 : Blo 1746574 6637895 := bstep (se 1 (by rfl) ⟨4978421, by rfl⟩ : syracuseStep 6637895 = 9956843) B9956843
theorem B28339145 : Blo 1746574 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B5895449 : Blo 1746574 5895449 := bstep (se 2 (by rfl) ⟨2210793, by rfl⟩ : syracuseStep 5895449 = 4421587) B4421587
theorem B7567111 : Blo 1746574 7567111 := bstep (se 1 (by rfl) ⟨5675333, by rfl⟩ : syracuseStep 7567111 = 11350667) B11350667
theorem B8845199 : Blo 1746574 8845199 := bstep (se 1 (by rfl) ⟨6633899, by rfl⟩ : syracuseStep 8845199 = 13267799) B13267799
theorem B48463307 : Blo 1746574 48463307 := bstep (se 1 (by rfl) ⟨36347480, by rfl⟩ : syracuseStep 48463307 = 72694961) B72694961
theorem B14171935 : Blo 1746574 14171935 := bstep (se 1 (by rfl) ⟨10628951, by rfl⟩ : syracuseStep 14171935 = 21257903) B21257903
theorem B2621495 : Blo 1746574 2621495 := bstep (se 1 (by rfl) ⟨1966121, by rfl⟩ : syracuseStep 2621495 = 3932243) B3932243
theorem B4425263 : Blo 1746574 4425263 := bstep (se 1 (by rfl) ⟨3318947, by rfl⟩ : syracuseStep 4425263 = 6637895) B6637895
theorem B18892763 : Blo 1746574 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B1748223 : Blo 1746574 1748223 := bstep (se 1 (by rfl) ⟨1311167, by rfl⟩ : syracuseStep 1748223 = 2622335) B2622335
theorem B10089481 : Blo 1746574 10089481 := bstep (se 2 (by rfl) ⟨3783555, by rfl⟩ : syracuseStep 10089481 = 7567111) B7567111
theorem B18895913 : Blo 1746574 18895913 := bstep (se 2 (by rfl) ⟨7085967, by rfl⟩ : syracuseStep 18895913 = 14171935) B14171935
theorem B3930299 : Blo 1746574 3930299 := bstep (se 1 (by rfl) ⟨2947724, by rfl⟩ : syracuseStep 3930299 = 5895449) B5895449
theorem B5896799 : Blo 1746574 5896799 := bstep (se 1 (by rfl) ⟨4422599, by rfl⟩ : syracuseStep 5896799 = 8845199) B8845199
theorem B32308871 : Blo 1746574 32308871 := bstep (se 1 (by rfl) ⟨24231653, by rfl⟩ : syracuseStep 32308871 = 48463307) B48463307
theorem B2950175 : Blo 1746574 2950175 := bstep (se 1 (by rfl) ⟨2212631, by rfl⟩ : syracuseStep 2950175 = 4425263) B4425263
theorem B13452641 : Blo 1746574 13452641 := bstep (se 2 (by rfl) ⟨5044740, by rfl⟩ : syracuseStep 13452641 = 10089481) B10089481
theorem B86156989 : Blo 1746574 86156989 := bstep (se 3 (by rfl) ⟨16154435, by rfl⟩ : syracuseStep 86156989 = 32308871) B32308871
theorem B1747663 : Blo 1746574 1747663 := bstep (se 1 (by rfl) ⟨1310747, by rfl⟩ : syracuseStep 1747663 = 2621495) B2621495
theorem B12595175 : Blo 1746574 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B12597275 : Blo 1746574 12597275 := bstep (se 1 (by rfl) ⟨9447956, by rfl⟩ : syracuseStep 12597275 = 18895913) B18895913
theorem B2620199 : Blo 1746574 2620199 := bstep (se 1 (by rfl) ⟨1965149, by rfl⟩ : syracuseStep 2620199 = 3930299) B3930299
theorem B3931199 : Blo 1746574 3931199 := bstep (se 1 (by rfl) ⟨2948399, by rfl⟩ : syracuseStep 3931199 = 5896799) B5896799
theorem B1966783 : Blo 1746574 1966783 := bstep (se 1 (by rfl) ⟨1475087, by rfl⟩ : syracuseStep 1966783 = 2950175) B2950175
theorem B8398183 : Blo 1746574 8398183 := bstep (se 1 (by rfl) ⟨6298637, by rfl⟩ : syracuseStep 8398183 = 12597275) B12597275
theorem B1746799 : Blo 1746574 1746799 := bstep (se 1 (by rfl) ⟨1310099, by rfl⟩ : syracuseStep 1746799 = 2620199) B2620199
theorem B8968427 : Blo 1746574 8968427 := bstep (se 1 (by rfl) ⟨6726320, by rfl⟩ : syracuseStep 8968427 = 13452641) B13452641
theorem B459503941 : Blo 1746574 459503941 := bstep (se 4 (by rfl) ⟨43078494, by rfl⟩ : syracuseStep 459503941 = 86156989) B86156989
theorem B2620799 : Blo 1746574 2620799 := bstep (se 1 (by rfl) ⟨1965599, by rfl⟩ : syracuseStep 2620799 = 3931199) B3931199
theorem B8396783 : Blo 1746574 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B612671921 : Blo 1746574 612671921 := bstep (se 2 (by rfl) ⟨229751970, by rfl⟩ : syracuseStep 612671921 = 459503941) B459503941
theorem B2622377 : Blo 1746574 2622377 := bstep (se 2 (by rfl) ⟨983391, by rfl⟩ : syracuseStep 2622377 = 1966783) B1966783
theorem B1747199 : Blo 1746574 1747199 := bstep (se 1 (by rfl) ⟨1310399, by rfl⟩ : syracuseStep 1747199 = 2620799) B2620799
theorem B5597855 : Blo 1746574 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B5978951 : Blo 1746574 5978951 := bstep (se 1 (by rfl) ⟨4484213, by rfl⟩ : syracuseStep 5978951 = 8968427) B8968427
theorem B11197577 : Blo 1746574 11197577 := bstep (se 2 (by rfl) ⟨4199091, by rfl⟩ : syracuseStep 11197577 = 8398183) B8398183
theorem B7465051 : Blo 1746574 7465051 := bstep (se 1 (by rfl) ⟨5598788, by rfl⟩ : syracuseStep 7465051 = 11197577) B11197577
theorem B408447947 : Blo 1746574 408447947 := bstep (se 1 (by rfl) ⟨306335960, by rfl⟩ : syracuseStep 408447947 = 612671921) B612671921
theorem B1748251 : Blo 1746574 1748251 := bstep (se 1 (by rfl) ⟨1311188, by rfl⟩ : syracuseStep 1748251 = 2622377) B2622377
theorem B3731903 : Blo 1746574 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B3985967 : Blo 1746574 3985967 := bstep (se 1 (by rfl) ⟨2989475, by rfl⟩ : syracuseStep 3985967 = 5978951) B5978951
theorem B9953401 : Blo 1746574 9953401 := bstep (se 2 (by rfl) ⟨3732525, by rfl⟩ : syracuseStep 9953401 = 7465051) B7465051
theorem B10629245 : Blo 1746574 10629245 := bstep (se 3 (by rfl) ⟨1992983, by rfl⟩ : syracuseStep 10629245 = 3985967) B3985967
theorem B272298631 : Blo 1746574 272298631 := bstep (se 1 (by rfl) ⟨204223973, by rfl⟩ : syracuseStep 272298631 = 408447947) B408447947
theorem B2487935 : Blo 1746574 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B7086163 : Blo 1746574 7086163 := bstep (se 1 (by rfl) ⟨5314622, by rfl⟩ : syracuseStep 7086163 = 10629245) B10629245
theorem B13271201 : Blo 1746574 13271201 := bstep (se 2 (by rfl) ⟨4976700, by rfl⟩ : syracuseStep 13271201 = 9953401) B9953401
theorem B363064841 : Blo 1746574 363064841 := bstep (se 2 (by rfl) ⟨136149315, by rfl⟩ : syracuseStep 363064841 = 272298631) B272298631
theorem B6634493 : Blo 1746574 6634493 := bstep (se 3 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 6634493 = 2487935) B2487935
theorem B8847467 : Blo 1746574 8847467 := bstep (se 1 (by rfl) ⟨6635600, by rfl⟩ : syracuseStep 8847467 = 13271201) B13271201
theorem B242043227 : Blo 1746574 242043227 := bstep (se 1 (by rfl) ⟨181532420, by rfl⟩ : syracuseStep 242043227 = 363064841) B363064841
theorem B9448217 : Blo 1746574 9448217 := bstep (se 2 (by rfl) ⟨3543081, by rfl⟩ : syracuseStep 9448217 = 7086163) B7086163
theorem B4422995 : Blo 1746574 4422995 := bstep (se 1 (by rfl) ⟨3317246, by rfl⟩ : syracuseStep 4422995 = 6634493) B6634493
theorem B5898311 : Blo 1746574 5898311 := bstep (se 1 (by rfl) ⟨4423733, by rfl⟩ : syracuseStep 5898311 = 8847467) B8847467
theorem B161362151 : Blo 1746574 161362151 := bstep (se 1 (by rfl) ⟨121021613, by rfl⟩ : syracuseStep 161362151 = 242043227) B242043227
theorem B6298811 : Blo 1746574 6298811 := bstep (se 1 (by rfl) ⟨4724108, by rfl⟩ : syracuseStep 6298811 = 9448217) B9448217
theorem B2948663 : Blo 1746574 2948663 := bstep (se 1 (by rfl) ⟨2211497, by rfl⟩ : syracuseStep 2948663 = 4422995) B4422995
theorem B3932207 : Blo 1746574 3932207 := bstep (se 1 (by rfl) ⟨2949155, by rfl⟩ : syracuseStep 3932207 = 5898311) B5898311
theorem B4199207 : Blo 1746574 4199207 := bstep (se 1 (by rfl) ⟨3149405, by rfl⟩ : syracuseStep 4199207 = 6298811) B6298811
theorem B107574767 : Blo 1746574 107574767 := bstep (se 1 (by rfl) ⟨80681075, by rfl⟩ : syracuseStep 107574767 = 161362151) B161362151
theorem B1965775 : Blo 1746574 1965775 := bstep (se 1 (by rfl) ⟨1474331, by rfl⟩ : syracuseStep 1965775 = 2948663) B2948663
theorem B2621471 : Blo 1746574 2621471 := bstep (se 1 (by rfl) ⟨1966103, by rfl⟩ : syracuseStep 2621471 = 3932207) B3932207
theorem B71716511 : Blo 1746574 71716511 := bstep (se 1 (by rfl) ⟨53787383, by rfl⟩ : syracuseStep 71716511 = 107574767) B107574767
theorem B11197885 : Blo 1746574 11197885 := bstep (se 3 (by rfl) ⟨2099603, by rfl⟩ : syracuseStep 11197885 = 4199207) B4199207
theorem B2621033 : Blo 1746574 2621033 := bstep (se 2 (by rfl) ⟨982887, by rfl⟩ : syracuseStep 2621033 = 1965775) B1965775
theorem B1747355 : Blo 1746574 1747355 := bstep (se 1 (by rfl) ⟨1310516, by rfl⟩ : syracuseStep 1747355 = 2621033) B2621033
theorem B47811007 : Blo 1746574 47811007 := bstep (se 1 (by rfl) ⟨35858255, by rfl⟩ : syracuseStep 47811007 = 71716511) B71716511
theorem B1747647 : Blo 1746574 1747647 := bstep (se 1 (by rfl) ⟨1310735, by rfl⟩ : syracuseStep 1747647 = 2621471) B2621471
theorem B14930513 : Blo 1746574 14930513 := bstep (se 2 (by rfl) ⟨5598942, by rfl⟩ : syracuseStep 14930513 = 11197885) B11197885
theorem B9953675 : Blo 1746574 9953675 := bstep (se 1 (by rfl) ⟨7465256, by rfl⟩ : syracuseStep 9953675 = 14930513) B14930513
theorem B63748009 : Blo 1746574 63748009 := bstep (se 2 (by rfl) ⟨23905503, by rfl⟩ : syracuseStep 63748009 = 47811007) B47811007
theorem B6635783 : Blo 1746574 6635783 := bstep (se 1 (by rfl) ⟨4976837, by rfl⟩ : syracuseStep 6635783 = 9953675) B9953675
theorem B84997345 : Blo 1746574 84997345 := bstep (se 2 (by rfl) ⟨31874004, by rfl⟩ : syracuseStep 84997345 = 63748009) B63748009
theorem B4423855 : Blo 1746574 4423855 := bstep (se 1 (by rfl) ⟨3317891, by rfl⟩ : syracuseStep 4423855 = 6635783) B6635783
theorem B113329793 : Blo 1746574 113329793 := bstep (se 2 (by rfl) ⟨42498672, by rfl⟩ : syracuseStep 113329793 = 84997345) B84997345
theorem B5898473 : Blo 1746574 5898473 := bstep (se 2 (by rfl) ⟨2211927, by rfl⟩ : syracuseStep 5898473 = 4423855) B4423855
theorem B75553195 : Blo 1746574 75553195 := bstep (se 1 (by rfl) ⟨56664896, by rfl⟩ : syracuseStep 75553195 = 113329793) B113329793
theorem B3932315 : Blo 1746574 3932315 := bstep (se 1 (by rfl) ⟨2949236, by rfl⟩ : syracuseStep 3932315 = 5898473) B5898473
theorem B100737593 : Blo 1746574 100737593 := bstep (se 2 (by rfl) ⟨37776597, by rfl⟩ : syracuseStep 100737593 = 75553195) B75553195
theorem B2621543 : Blo 1746574 2621543 := bstep (se 1 (by rfl) ⟨1966157, by rfl⟩ : syracuseStep 2621543 = 3932315) B3932315
theorem B67158395 : Blo 1746574 67158395 := bstep (se 1 (by rfl) ⟨50368796, by rfl⟩ : syracuseStep 67158395 = 100737593) B100737593
theorem B1747695 : Blo 1746574 1747695 := bstep (se 1 (by rfl) ⟨1310771, by rfl⟩ : syracuseStep 1747695 = 2621543) B2621543
theorem B44772263 : Blo 1746574 44772263 := bstep (se 1 (by rfl) ⟨33579197, by rfl⟩ : syracuseStep 44772263 = 67158395) B67158395
theorem B29848175 : Blo 1746574 29848175 := bstep (se 1 (by rfl) ⟨22386131, by rfl⟩ : syracuseStep 29848175 = 44772263) B44772263
theorem B19898783 : Blo 1746574 19898783 := bstep (se 1 (by rfl) ⟨14924087, by rfl⟩ : syracuseStep 19898783 = 29848175) B29848175
theorem B13265855 : Blo 1746574 13265855 := bstep (se 1 (by rfl) ⟨9949391, by rfl⟩ : syracuseStep 13265855 = 19898783) B19898783
theorem B8843903 : Blo 1746574 8843903 := bstep (se 1 (by rfl) ⟨6632927, by rfl⟩ : syracuseStep 8843903 = 13265855) B13265855
theorem B5895935 : Blo 1746574 5895935 := bstep (se 1 (by rfl) ⟨4421951, by rfl⟩ : syracuseStep 5895935 = 8843903) B8843903
theorem B3930623 : Blo 1746574 3930623 := bstep (se 1 (by rfl) ⟨2947967, by rfl⟩ : syracuseStep 3930623 = 5895935) B5895935
theorem B2620415 : Blo 1746574 2620415 := bstep (se 1 (by rfl) ⟨1965311, by rfl⟩ : syracuseStep 2620415 = 3930623) B3930623
theorem B1746943 : Blo 1746574 1746943 := bstep (se 1 (by rfl) ⟨1310207, by rfl⟩ : syracuseStep 1746943 = 2620415) B2620415

theorem C0 (j : ℕ) (h1 : 436643 ≤ j) (h2 : j ≤ 437142) : Blo 1746574 (4 * j + 3) := by
  interval_cases j
  · exact B1746575
  · exact B1746579
  · exact B1746583
  · exact B1746587
  · exact B1746591
  · exact B1746595
  · exact B1746599
  · exact B1746603
  · exact B1746607
  · exact B1746611
  · exact B1746615
  · exact B1746619
  · exact B1746623
  · exact B1746627
  · exact B1746631
  · exact B1746635
  · exact B1746639
  · exact B1746643
  · exact B1746647
  · exact B1746651
  · exact B1746655
  · exact B1746659
  · exact B1746663
  · exact B1746667
  · exact B1746671
  · exact B1746675
  · exact B1746679
  · exact B1746683
  · exact B1746687
  · exact B1746691
  · exact B1746695
  · exact B1746699
  · exact B1746703
  · exact B1746707
  · exact B1746711
  · exact B1746715
  · exact B1746719
  · exact B1746723
  · exact B1746727
  · exact B1746731
  · exact B1746735
  · exact B1746739
  · exact B1746743
  · exact B1746747
  · exact B1746751
  · exact B1746755
  · exact B1746759
  · exact B1746763
  · exact B1746767
  · exact B1746771
  · exact B1746775
  · exact B1746779
  · exact B1746783
  · exact B1746787
  · exact B1746791
  · exact B1746795
  · exact B1746799
  · exact B1746803
  · exact B1746807
  · exact B1746811
  · exact B1746815
  · exact B1746819
  · exact B1746823
  · exact B1746827
  · exact B1746831
  · exact B1746835
  · exact B1746839
  · exact B1746843
  · exact B1746847
  · exact B1746851
  · exact B1746855
  · exact B1746859
  · exact B1746863
  · exact B1746867
  · exact B1746871
  · exact B1746875
  · exact B1746879
  · exact B1746883
  · exact B1746887
  · exact B1746891
  · exact B1746895
  · exact B1746899
  · exact B1746903
  · exact B1746907
  · exact B1746911
  · exact B1746915
  · exact B1746919
  · exact B1746923
  · exact B1746927
  · exact B1746931
  · exact B1746935
  · exact B1746939
  · exact B1746943
  · exact B1746947
  · exact B1746951
  · exact B1746955
  · exact B1746959
  · exact B1746963
  · exact B1746967
  · exact B1746971
  · exact B1746975
  · exact B1746979
  · exact B1746983
  · exact B1746987
  · exact B1746991
  · exact B1746995
  · exact B1746999
  · exact B1747003
  · exact B1747007
  · exact B1747011
  · exact B1747015
  · exact B1747019
  · exact B1747023
  · exact B1747027
  · exact B1747031
  · exact B1747035
  · exact B1747039
  · exact B1747043
  · exact B1747047
  · exact B1747051
  · exact B1747055
  · exact B1747059
  · exact B1747063
  · exact B1747067
  · exact B1747071
  · exact B1747075
  · exact B1747079
  · exact B1747083
  · exact B1747087
  · exact B1747091
  · exact B1747095
  · exact B1747099
  · exact B1747103
  · exact B1747107
  · exact B1747111
  · exact B1747115
  · exact B1747119
  · exact B1747123
  · exact B1747127
  · exact B1747131
  · exact B1747135
  · exact B1747139
  · exact B1747143
  · exact B1747147
  · exact B1747151
  · exact B1747155
  · exact B1747159
  · exact B1747163
  · exact B1747167
  · exact B1747171
  · exact B1747175
  · exact B1747179
  · exact B1747183
  · exact B1747187
  · exact B1747191
  · exact B1747195
  · exact B1747199
  · exact B1747203
  · exact B1747207
  · exact B1747211
  · exact B1747215
  · exact B1747219
  · exact B1747223
  · exact B1747227
  · exact B1747231
  · exact B1747235
  · exact B1747239
  · exact B1747243
  · exact B1747247
  · exact B1747251
  · exact B1747255
  · exact B1747259
  · exact B1747263
  · exact B1747267
  · exact B1747271
  · exact B1747275
  · exact B1747279
  · exact B1747283
  · exact B1747287
  · exact B1747291
  · exact B1747295
  · exact B1747299
  · exact B1747303
  · exact B1747307
  · exact B1747311
  · exact B1747315
  · exact B1747319
  · exact B1747323
  · exact B1747327
  · exact B1747331
  · exact B1747335
  · exact B1747339
  · exact B1747343
  · exact B1747347
  · exact B1747351
  · exact B1747355
  · exact B1747359
  · exact B1747363
  · exact B1747367
  · exact B1747371
  · exact B1747375
  · exact B1747379
  · exact B1747383
  · exact B1747387
  · exact B1747391
  · exact B1747395
  · exact B1747399
  · exact B1747403
  · exact B1747407
  · exact B1747411
  · exact B1747415
  · exact B1747419
  · exact B1747423
  · exact B1747427
  · exact B1747431
  · exact B1747435
  · exact B1747439
  · exact B1747443
  · exact B1747447
  · exact B1747451
  · exact B1747455
  · exact B1747459
  · exact B1747463
  · exact B1747467
  · exact B1747471
  · exact B1747475
  · exact B1747479
  · exact B1747483
  · exact B1747487
  · exact B1747491
  · exact B1747495
  · exact B1747499
  · exact B1747503
  · exact B1747507
  · exact B1747511
  · exact B1747515
  · exact B1747519
  · exact B1747523
  · exact B1747527
  · exact B1747531
  · exact B1747535
  · exact B1747539
  · exact B1747543
  · exact B1747547
  · exact B1747551
  · exact B1747555
  · exact B1747559
  · exact B1747563
  · exact B1747567
  · exact B1747571
  · exact B1747575
  · exact B1747579
  · exact B1747583
  · exact B1747587
  · exact B1747591
  · exact B1747595
  · exact B1747599
  · exact B1747603
  · exact B1747607
  · exact B1747611
  · exact B1747615
  · exact B1747619
  · exact B1747623
  · exact B1747627
  · exact B1747631
  · exact B1747635
  · exact B1747639
  · exact B1747643
  · exact B1747647
  · exact B1747651
  · exact B1747655
  · exact B1747659
  · exact B1747663
  · exact B1747667
  · exact B1747671
  · exact B1747675
  · exact B1747679
  · exact B1747683
  · exact B1747687
  · exact B1747691
  · exact B1747695
  · exact B1747699
  · exact B1747703
  · exact B1747707
  · exact B1747711
  · exact B1747715
  · exact B1747719
  · exact B1747723
  · exact B1747727
  · exact B1747731
  · exact B1747735
  · exact B1747739
  · exact B1747743
  · exact B1747747
  · exact B1747751
  · exact B1747755
  · exact B1747759
  · exact B1747763
  · exact B1747767
  · exact B1747771
  · exact B1747775
  · exact B1747779
  · exact B1747783
  · exact B1747787
  · exact B1747791
  · exact B1747795
  · exact B1747799
  · exact B1747803
  · exact B1747807
  · exact B1747811
  · exact B1747815
  · exact B1747819
  · exact B1747823
  · exact B1747827
  · exact B1747831
  · exact B1747835
  · exact B1747839
  · exact B1747843
  · exact B1747847
  · exact B1747851
  · exact B1747855
  · exact B1747859
  · exact B1747863
  · exact B1747867
  · exact B1747871
  · exact B1747875
  · exact B1747879
  · exact B1747883
  · exact B1747887
  · exact B1747891
  · exact B1747895
  · exact B1747899
  · exact B1747903
  · exact B1747907
  · exact B1747911
  · exact B1747915
  · exact B1747919
  · exact B1747923
  · exact B1747927
  · exact B1747931
  · exact B1747935
  · exact B1747939
  · exact B1747943
  · exact B1747947
  · exact B1747951
  · exact B1747955
  · exact B1747959
  · exact B1747963
  · exact B1747967
  · exact B1747971
  · exact B1747975
  · exact B1747979
  · exact B1747983
  · exact B1747987
  · exact B1747991
  · exact B1747995
  · exact B1747999
  · exact B1748003
  · exact B1748007
  · exact B1748011
  · exact B1748015
  · exact B1748019
  · exact B1748023
  · exact B1748027
  · exact B1748031
  · exact B1748035
  · exact B1748039
  · exact B1748043
  · exact B1748047
  · exact B1748051
  · exact B1748055
  · exact B1748059
  · exact B1748063
  · exact B1748067
  · exact B1748071
  · exact B1748075
  · exact B1748079
  · exact B1748083
  · exact B1748087
  · exact B1748091
  · exact B1748095
  · exact B1748099
  · exact B1748103
  · exact B1748107
  · exact B1748111
  · exact B1748115
  · exact B1748119
  · exact B1748123
  · exact B1748127
  · exact B1748131
  · exact B1748135
  · exact B1748139
  · exact B1748143
  · exact B1748147
  · exact B1748151
  · exact B1748155
  · exact B1748159
  · exact B1748163
  · exact B1748167
  · exact B1748171
  · exact B1748175
  · exact B1748179
  · exact B1748183
  · exact B1748187
  · exact B1748191
  · exact B1748195
  · exact B1748199
  · exact B1748203
  · exact B1748207
  · exact B1748211
  · exact B1748215
  · exact B1748219
  · exact B1748223
  · exact B1748227
  · exact B1748231
  · exact B1748235
  · exact B1748239
  · exact B1748243
  · exact B1748247
  · exact B1748251
  · exact B1748255
  · exact B1748259
  · exact B1748263
  · exact B1748267
  · exact B1748271
  · exact B1748275
  · exact B1748279
  · exact B1748283
  · exact B1748287
  · exact B1748291
  · exact B1748295
  · exact B1748299
  · exact B1748303
  · exact B1748307
  · exact B1748311
  · exact B1748315
  · exact B1748319
  · exact B1748323
  · exact B1748327
  · exact B1748331
  · exact B1748335
  · exact B1748339
  · exact B1748343
  · exact B1748347
  · exact B1748351
  · exact B1748355
  · exact B1748359
  · exact B1748363
  · exact B1748367
  · exact B1748371
  · exact B1748375
  · exact B1748379
  · exact B1748383
  · exact B1748387
  · exact B1748391
  · exact B1748395
  · exact B1748399
  · exact B1748403
  · exact B1748407
  · exact B1748411
  · exact B1748415
  · exact B1748419
  · exact B1748423
  · exact B1748427
  · exact B1748431
  · exact B1748435
  · exact B1748439
  · exact B1748443
  · exact B1748447
  · exact B1748451
  · exact B1748455
  · exact B1748459
  · exact B1748463
  · exact B1748467
  · exact B1748471
  · exact B1748475
  · exact B1748479
  · exact B1748483
  · exact B1748487
  · exact B1748491
  · exact B1748495
  · exact B1748499
  · exact B1748503
  · exact B1748507
  · exact B1748511
  · exact B1748515
  · exact B1748519
  · exact B1748523
  · exact B1748527
  · exact B1748531
  · exact B1748535
  · exact B1748539
  · exact B1748543
  · exact B1748547
  · exact B1748551
  · exact B1748555
  · exact B1748559
  · exact B1748563
  · exact B1748567
  · exact B1748571

theorem solution (m : ℕ) (hlo : 1746574 ≤ m) (hhi : m ≤ 1748574) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 436643 ≤ j := by omega
    have hj2 : j ≤ 437142 := by omega
    have hb : Blo 1746574 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
