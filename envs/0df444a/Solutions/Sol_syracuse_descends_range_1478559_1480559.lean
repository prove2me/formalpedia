-- Prove2me | solution 1 for syracuse_descends_range_1478559_1480559
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:45:29.848569+00:00
-- url     : https://prove2.me/submissions/52f8ef92-4c3d-4b8f-9c97-7c4090f46db7

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


theorem B2220053 : Blo 1478559 2220053 := bbase (se 6 (by rfl) ⟨52032, by rfl⟩ : syracuseStep 2220053 = 104065) (by norm_num)
theorem B2809885 : Blo 1478559 2809885 := bbase (se 3 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 2809885 = 1053707) (by norm_num)
theorem B2220077 : Blo 1478559 2220077 := bbase (se 3 (by rfl) ⟨416264, by rfl⟩ : syracuseStep 2220077 = 832529) (by norm_num)
theorem B2220101 : Blo 1478559 2220101 := bbase (se 4 (by rfl) ⟨208134, by rfl⟩ : syracuseStep 2220101 = 416269) (by norm_num)
theorem B2220125 : Blo 1478559 2220125 := bbase (se 3 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 2220125 = 832547) (by norm_num)
theorem B2220149 : Blo 1478559 2220149 := bbase (se 5 (by rfl) ⟨104069, by rfl⟩ : syracuseStep 2220149 = 208139) (by norm_num)
theorem B2220173 : Blo 1478559 2220173 := bbase (se 3 (by rfl) ⟨416282, by rfl⟩ : syracuseStep 2220173 = 832565) (by norm_num)
theorem B2220197 : Blo 1478559 2220197 := bbase (se 4 (by rfl) ⟨208143, by rfl⟩ : syracuseStep 2220197 = 416287) (by norm_num)
theorem B2220221 : Blo 1478559 2220221 := bbase (se 3 (by rfl) ⟨416291, by rfl⟩ : syracuseStep 2220221 = 832583) (by norm_num)
theorem B2810045 : Blo 1478559 2810045 := bbase (se 3 (by rfl) ⟨526883, by rfl⟩ : syracuseStep 2810045 = 1053767) (by norm_num)
theorem B3743941 : Blo 1478559 3743941 := bbase (se 4 (by rfl) ⟨350994, by rfl⟩ : syracuseStep 3743941 = 701989) (by norm_num)
theorem B1851589 : Blo 1478559 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B7798997 : Blo 1478559 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B2220245 : Blo 1478559 2220245 := bbase (se 7 (by rfl) ⟨26018, by rfl⟩ : syracuseStep 2220245 = 52037) (by norm_num)
theorem B2220269 : Blo 1478559 2220269 := bbase (se 3 (by rfl) ⟨416300, by rfl⟩ : syracuseStep 2220269 = 832601) (by norm_num)
theorem B2220293 : Blo 1478559 2220293 := bbase (se 4 (by rfl) ⟨208152, by rfl⟩ : syracuseStep 2220293 = 416305) (by norm_num)
theorem B2220317 : Blo 1478559 2220317 := bbase (se 3 (by rfl) ⟨416309, by rfl⟩ : syracuseStep 2220317 = 832619) (by norm_num)
theorem B3744053 : Blo 1478559 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B2220341 : Blo 1478559 2220341 := bbase (se 5 (by rfl) ⟨104078, by rfl⟩ : syracuseStep 2220341 = 208157) (by norm_num)
theorem B2220365 : Blo 1478559 2220365 := bbase (se 3 (by rfl) ⟨416318, by rfl⟩ : syracuseStep 2220365 = 832637) (by norm_num)
theorem B2810189 : Blo 1478559 2810189 := bbase (se 3 (by rfl) ⟨526910, by rfl⟩ : syracuseStep 2810189 = 1053821) (by norm_num)
theorem B3039581 : Blo 1478559 3039581 := bbase (se 3 (by rfl) ⟨569921, by rfl⟩ : syracuseStep 3039581 = 1139843) (by norm_num)
theorem B2220389 : Blo 1478559 2220389 := bbase (se 4 (by rfl) ⟨208161, by rfl⟩ : syracuseStep 2220389 = 416323) (by norm_num)
theorem B2220413 : Blo 1478559 2220413 := bbase (se 3 (by rfl) ⟨416327, by rfl⟩ : syracuseStep 2220413 = 832655) (by norm_num)
theorem B2220437 : Blo 1478559 2220437 := bbase (se 6 (by rfl) ⟨52041, by rfl⟩ : syracuseStep 2220437 = 104083) (by norm_num)
theorem B1663393 : Blo 1478559 1663393 := bbase (se 2 (by rfl) ⟨623772, by rfl⟩ : syracuseStep 1663393 = 1247545) (by norm_num)
theorem B2220461 : Blo 1478559 2220461 := bbase (se 3 (by rfl) ⟨416336, by rfl⟩ : syracuseStep 2220461 = 832673) (by norm_num)
theorem B1663429 : Blo 1478559 1663429 := bbase (se 4 (by rfl) ⟨155946, by rfl⟩ : syracuseStep 1663429 = 311893) (by norm_num)
theorem B2220485 : Blo 1478559 2220485 := bbase (se 4 (by rfl) ⟨208170, by rfl⟩ : syracuseStep 2220485 = 416341) (by norm_num)
theorem B6316501 : Blo 1478559 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B2220509 : Blo 1478559 2220509 := bbase (se 3 (by rfl) ⟨416345, by rfl⟩ : syracuseStep 2220509 = 832691) (by norm_num)
theorem B2998757 : Blo 1478559 2998757 := bbase (se 4 (by rfl) ⟨281133, by rfl⟩ : syracuseStep 2998757 = 562267) (by norm_num)
theorem B1663465 : Blo 1478559 1663465 := bbase (se 2 (by rfl) ⟨623799, by rfl⟩ : syracuseStep 1663465 = 1247599) (by norm_num)
theorem B3744245 : Blo 1478559 3744245 := bbase (se 5 (by rfl) ⟨175511, by rfl⟩ : syracuseStep 3744245 = 351023) (by norm_num)
theorem B2220533 : Blo 1478559 2220533 := bbase (se 5 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 2220533 = 208175) (by norm_num)
theorem B1663501 : Blo 1478559 1663501 := bbase (se 3 (by rfl) ⟨311906, by rfl⟩ : syracuseStep 1663501 = 623813) (by norm_num)
theorem B2220557 : Blo 1478559 2220557 := bbase (se 3 (by rfl) ⟨416354, by rfl⟩ : syracuseStep 2220557 = 832709) (by norm_num)
theorem B2220581 : Blo 1478559 2220581 := bbase (se 4 (by rfl) ⟨208179, by rfl⟩ : syracuseStep 2220581 = 416359) (by norm_num)
theorem B1663537 : Blo 1478559 1663537 := bbase (se 2 (by rfl) ⟨623826, by rfl⟩ : syracuseStep 1663537 = 1247653) (by norm_num)
theorem B2220605 : Blo 1478559 2220605 := bbase (se 3 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 2220605 = 832727) (by norm_num)
theorem B1663573 : Blo 1478559 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B7111253 : Blo 1478559 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B2220629 : Blo 1478559 2220629 := bbase (se 8 (by rfl) ⟨13011, by rfl⟩ : syracuseStep 2220629 = 26023) (by norm_num)
theorem B2810477 : Blo 1478559 2810477 := bbase (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) (by norm_num)
theorem B2220653 : Blo 1478559 2220653 := bbase (se 3 (by rfl) ⟨416372, by rfl⟩ : syracuseStep 2220653 = 832745) (by norm_num)
theorem B1663609 : Blo 1478559 1663609 := bbase (se 2 (by rfl) ⟨623853, by rfl⟩ : syracuseStep 1663609 = 1247707) (by norm_num)
theorem B2220677 : Blo 1478559 2220677 := bbase (se 4 (by rfl) ⟨208188, by rfl⟩ : syracuseStep 2220677 = 416377) (by norm_num)
theorem B1663645 : Blo 1478559 1663645 := bbase (se 3 (by rfl) ⟨311933, by rfl⟩ : syracuseStep 1663645 = 623867) (by norm_num)
theorem B2106013 : Blo 1478559 2106013 := bbase (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) (by norm_num)
theorem B2220701 : Blo 1478559 2220701 := bbase (se 3 (by rfl) ⟨416381, by rfl⟩ : syracuseStep 2220701 = 832763) (by norm_num)
theorem B4211365 : Blo 1478559 4211365 := bbase (se 4 (by rfl) ⟨394815, by rfl⟩ : syracuseStep 4211365 = 789631) (by norm_num)
theorem B2220725 : Blo 1478559 2220725 := bbase (se 5 (by rfl) ⟨104096, by rfl⟩ : syracuseStep 2220725 = 208193) (by norm_num)
theorem B1663681 : Blo 1478559 1663681 := bbase (se 2 (by rfl) ⟨623880, by rfl⟩ : syracuseStep 1663681 = 1247761) (by norm_num)
theorem B5333701 : Blo 1478559 5333701 := bbase (se 4 (by rfl) ⟨500034, by rfl⟩ : syracuseStep 5333701 = 1000069) (by norm_num)
theorem B2220749 : Blo 1478559 2220749 := bbase (se 3 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 2220749 = 832781) (by norm_num)
theorem B1663717 : Blo 1478559 1663717 := bbase (se 4 (by rfl) ⟨155973, by rfl⟩ : syracuseStep 1663717 = 311947) (by norm_num)
theorem B2220773 : Blo 1478559 2220773 := bbase (se 4 (by rfl) ⟨208197, by rfl⟩ : syracuseStep 2220773 = 416395) (by norm_num)
theorem B2220797 : Blo 1478559 2220797 := bbase (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) (by norm_num)
theorem B2810629 : Blo 1478559 2810629 := bbase (se 4 (by rfl) ⟨263496, by rfl⟩ : syracuseStep 2810629 = 526993) (by norm_num)
theorem B1663753 : Blo 1478559 1663753 := bbase (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) (by norm_num)
theorem B2220821 : Blo 1478559 2220821 := bbase (se 6 (by rfl) ⟨52050, by rfl⟩ : syracuseStep 2220821 = 104101) (by norm_num)
theorem B1663789 : Blo 1478559 1663789 := bbase (se 3 (by rfl) ⟨311960, by rfl⟩ : syracuseStep 1663789 = 623921) (by norm_num)
theorem B3556165 : Blo 1478559 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B3744589 : Blo 1478559 3744589 := bbase (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) (by norm_num)
theorem B1663825 : Blo 1478559 1663825 := bbase (se 2 (by rfl) ⟨623934, by rfl⟩ : syracuseStep 1663825 = 1247869) (by norm_num)
theorem B3326813 : Blo 1478559 3326813 := bbase (se 3 (by rfl) ⟨623777, by rfl⟩ : syracuseStep 3326813 = 1247555) (by norm_num)
theorem B1663861 : Blo 1478559 1663861 := bbase (se 5 (by rfl) ⟨77993, by rfl⟩ : syracuseStep 1663861 = 155987) (by norm_num)
theorem B2368381 : Blo 1478559 2368381 := bbase (se 3 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 2368381 = 888143) (by norm_num)
theorem B1663897 : Blo 1478559 1663897 := bbase (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) (by norm_num)
theorem B3326885 : Blo 1478559 3326885 := bbase (se 4 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 3326885 = 623791) (by norm_num)
theorem B1663933 : Blo 1478559 1663933 := bbase (se 3 (by rfl) ⟨311987, by rfl⟩ : syracuseStep 1663933 = 623975) (by norm_num)
theorem B3744701 : Blo 1478559 3744701 := bbase (se 3 (by rfl) ⟨702131, by rfl⟩ : syracuseStep 3744701 = 1404263) (by norm_num)
theorem B21341141 : Blo 1478559 21341141 := bbase (se 7 (by rfl) ⟨250091, by rfl⟩ : syracuseStep 21341141 = 500183) (by norm_num)
theorem B1663969 : Blo 1478559 1663969 := bbase (se 2 (by rfl) ⟨623988, by rfl⟩ : syracuseStep 1663969 = 1247977) (by norm_num)
theorem B3326957 : Blo 1478559 3326957 := bbase (se 3 (by rfl) ⟨623804, by rfl⟩ : syracuseStep 3326957 = 1247609) (by norm_num)
theorem B2532341 : Blo 1478559 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B1664005 : Blo 1478559 1664005 := bbase (se 4 (by rfl) ⟨156000, by rfl⟩ : syracuseStep 1664005 = 312001) (by norm_num)
theorem B2704421 : Blo 1478559 2704421 := bbase (se 4 (by rfl) ⟨253539, by rfl⟩ : syracuseStep 2704421 = 507079) (by norm_num)
theorem B1664041 : Blo 1478559 1664041 := bbase (se 2 (by rfl) ⟨624015, by rfl⟩ : syracuseStep 1664041 = 1248031) (by norm_num)
theorem B3327029 : Blo 1478559 3327029 := bbase (se 5 (by rfl) ⟨155954, by rfl⟩ : syracuseStep 3327029 = 311909) (by norm_num)
theorem B1500233 : Blo 1478559 1500233 := bbase (se 2 (by rfl) ⟨562587, by rfl⟩ : syracuseStep 1500233 = 1125175) (by norm_num)
theorem B3793997 : Blo 1478559 3793997 := bbase (se 3 (by rfl) ⟨711374, by rfl⟩ : syracuseStep 3793997 = 1422749) (by norm_num)
theorem B1664077 : Blo 1478559 1664077 := bbase (se 3 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 1664077 = 624029) (by norm_num)
theorem B1999949 : Blo 1478559 1999949 := bbase (se 3 (by rfl) ⟨374990, by rfl⟩ : syracuseStep 1999949 = 749981) (by norm_num)
theorem B1664113 : Blo 1478559 1664113 := bbase (se 2 (by rfl) ⟨624042, by rfl⟩ : syracuseStep 1664113 = 1248085) (by norm_num)
theorem B12633205 : Blo 1478559 12633205 := bbase (se 5 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 12633205 = 1184363) (by norm_num)
theorem B3327101 : Blo 1478559 3327101 := bbase (se 3 (by rfl) ⟨623831, by rfl⟩ : syracuseStep 3327101 = 1247663) (by norm_num)
theorem B3744893 : Blo 1478559 3744893 := bbase (se 3 (by rfl) ⟨702167, by rfl⟩ : syracuseStep 3744893 = 1404335) (by norm_num)
theorem B1664149 : Blo 1478559 1664149 := bbase (se 6 (by rfl) ⟨39003, by rfl⟩ : syracuseStep 1664149 = 78007) (by norm_num)
theorem B2925733 : Blo 1478559 2925733 := bbase (se 4 (by rfl) ⟨274287, by rfl⟩ : syracuseStep 2925733 = 548575) (by norm_num)
theorem B2999477 : Blo 1478559 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B1664185 : Blo 1478559 1664185 := bbase (se 2 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 1664185 = 1248139) (by norm_num)
theorem B3556541 : Blo 1478559 3556541 := bbase (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) (by norm_num)
theorem B3327173 : Blo 1478559 3327173 := bbase (se 4 (by rfl) ⟨311922, by rfl⟩ : syracuseStep 3327173 = 623845) (by norm_num)
theorem B1664221 : Blo 1478559 1664221 := bbase (se 3 (by rfl) ⟨312041, by rfl⟩ : syracuseStep 1664221 = 624083) (by norm_num)
theorem B2106605 : Blo 1478559 2106605 := bbase (se 3 (by rfl) ⟨394988, by rfl⟩ : syracuseStep 2106605 = 789977) (by norm_num)
theorem B11240693 : Blo 1478559 11240693 := bbase (se 5 (by rfl) ⟨526907, by rfl⟩ : syracuseStep 11240693 = 1053815) (by norm_num)
theorem B1664257 : Blo 1478559 1664257 := bbase (se 2 (by rfl) ⟨624096, by rfl⟩ : syracuseStep 1664257 = 1248193) (by norm_num)
theorem B7488773 : Blo 1478559 7488773 := bbase (se 4 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 7488773 = 1404145) (by norm_num)
theorem B3327245 : Blo 1478559 3327245 := bbase (se 3 (by rfl) ⟨623858, by rfl⟩ : syracuseStep 3327245 = 1247717) (by norm_num)
theorem B1664293 : Blo 1478559 1664293 := bbase (se 4 (by rfl) ⟨156027, by rfl⟩ : syracuseStep 1664293 = 312055) (by norm_num)
theorem B2368829 : Blo 1478559 2368829 := bbase (se 3 (by rfl) ⟨444155, by rfl⟩ : syracuseStep 2368829 = 888311) (by norm_num)
theorem B2106685 : Blo 1478559 2106685 := bbase (se 3 (by rfl) ⟨395003, by rfl⟩ : syracuseStep 2106685 = 790007) (by norm_num)
theorem B1664329 : Blo 1478559 1664329 := bbase (se 2 (by rfl) ⟨624123, by rfl⟩ : syracuseStep 1664329 = 1248247) (by norm_num)
theorem B1500493 : Blo 1478559 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B3327317 : Blo 1478559 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B1664365 : Blo 1478559 1664365 := bbase (se 3 (by rfl) ⟨312068, by rfl⟩ : syracuseStep 1664365 = 624137) (by norm_num)
theorem B1664401 : Blo 1478559 1664401 := bbase (se 2 (by rfl) ⟨624150, by rfl⟩ : syracuseStep 1664401 = 1248301) (by norm_num)
theorem B3327389 : Blo 1478559 3327389 := bbase (se 3 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 3327389 = 1247771) (by norm_num)
theorem B1664437 : Blo 1478559 1664437 := bbase (se 5 (by rfl) ⟨78020, by rfl⟩ : syracuseStep 1664437 = 156041) (by norm_num)
theorem B2106805 : Blo 1478559 2106805 := bbase (se 5 (by rfl) ⟨98756, by rfl⟩ : syracuseStep 2106805 = 197513) (by norm_num)
theorem B3745237 : Blo 1478559 3745237 := bbase (se 7 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 3745237 = 87779) (by norm_num)
theorem B1664473 : Blo 1478559 1664473 := bbase (se 2 (by rfl) ⟨624177, by rfl⟩ : syracuseStep 1664473 = 1248355) (by norm_num)
theorem B3327461 : Blo 1478559 3327461 := bbase (se 4 (by rfl) ⟨311949, by rfl⟩ : syracuseStep 3327461 = 623899) (by norm_num)
theorem B1664509 : Blo 1478559 1664509 := bbase (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) (by norm_num)
theorem B2106901 : Blo 1478559 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B1664545 : Blo 1478559 1664545 := bbase (se 2 (by rfl) ⟨624204, by rfl⟩ : syracuseStep 1664545 = 1248409) (by norm_num)
theorem B3327533 : Blo 1478559 3327533 := bbase (se 3 (by rfl) ⟨623912, by rfl⟩ : syracuseStep 3327533 = 1247825) (by norm_num)
theorem B4990517 : Blo 1478559 4990517 := bbase (se 5 (by rfl) ⟨233930, by rfl⟩ : syracuseStep 4990517 = 467861) (by norm_num)
theorem B5064245 : Blo 1478559 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B1664581 : Blo 1478559 1664581 := bbase (se 4 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 1664581 = 312109) (by norm_num)
theorem B3745349 : Blo 1478559 3745349 := bbase (se 4 (by rfl) ⟨351126, by rfl⟩ : syracuseStep 3745349 = 702253) (by norm_num)
theorem B1664617 : Blo 1478559 1664617 := bbase (se 2 (by rfl) ⟨624231, by rfl⟩ : syracuseStep 1664617 = 1248463) (by norm_num)
theorem B3556973 : Blo 1478559 3556973 := bbase (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) (by norm_num)
theorem B3327605 : Blo 1478559 3327605 := bbase (se 5 (by rfl) ⟨155981, by rfl⟩ : syracuseStep 3327605 = 311963) (by norm_num)
theorem B1664653 : Blo 1478559 1664653 := bbase (se 3 (by rfl) ⟨312122, by rfl⟩ : syracuseStep 1664653 = 624245) (by norm_num)
theorem B11232917 : Blo 1478559 11232917 := bbase (se 6 (by rfl) ⟨263271, by rfl⟩ : syracuseStep 11232917 = 526543) (by norm_num)
theorem B1664689 : Blo 1478559 1664689 := bbase (se 2 (by rfl) ⟨624258, by rfl⟩ : syracuseStep 1664689 = 1248517) (by norm_num)
theorem B3327677 : Blo 1478559 3327677 := bbase (se 3 (by rfl) ⟨623939, by rfl⟩ : syracuseStep 3327677 = 1247879) (by norm_num)
theorem B2000581 : Blo 1478559 2000581 := bbase (se 4 (by rfl) ⟨187554, by rfl⟩ : syracuseStep 2000581 = 375109) (by norm_num)
theorem B1664725 : Blo 1478559 1664725 := bbase (se 7 (by rfl) ⟨19508, by rfl⟩ : syracuseStep 1664725 = 39017) (by norm_num)
theorem B1664761 : Blo 1478559 1664761 := bbase (se 2 (by rfl) ⟨624285, by rfl⟩ : syracuseStep 1664761 = 1248571) (by norm_num)
theorem B3327749 : Blo 1478559 3327749 := bbase (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) (by norm_num)
theorem B3745541 : Blo 1478559 3745541 := bbase (se 4 (by rfl) ⟨351144, by rfl⟩ : syracuseStep 3745541 = 702289) (by norm_num)
theorem B1664797 : Blo 1478559 1664797 := bbase (se 3 (by rfl) ⟨312149, by rfl⟩ : syracuseStep 1664797 = 624299) (by norm_num)
theorem B1664833 : Blo 1478559 1664833 := bbase (se 2 (by rfl) ⟨624312, by rfl⟩ : syracuseStep 1664833 = 1248625) (by norm_num)
theorem B4736837 : Blo 1478559 4736837 := bbase (se 4 (by rfl) ⟨444078, by rfl⟩ : syracuseStep 4736837 = 888157) (by norm_num)
theorem B3327821 : Blo 1478559 3327821 := bbase (se 3 (by rfl) ⟨623966, by rfl⟩ : syracuseStep 3327821 = 1247933) (by norm_num)
theorem B1664869 : Blo 1478559 1664869 := bbase (se 4 (by rfl) ⟨156081, by rfl⟩ : syracuseStep 1664869 = 312163) (by norm_num)
theorem B1664905 : Blo 1478559 1664905 := bbase (se 2 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 1664905 = 1248679) (by norm_num)
theorem B3327893 : Blo 1478559 3327893 := bbase (se 6 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 3327893 = 155995) (by norm_num)
theorem B1664941 : Blo 1478559 1664941 := bbase (se 3 (by rfl) ⟨312176, by rfl⟩ : syracuseStep 1664941 = 624353) (by norm_num)
theorem B1664977 : Blo 1478559 1664977 := bbase (se 2 (by rfl) ⟨624366, by rfl⟩ : syracuseStep 1664977 = 1248733) (by norm_num)
theorem B5998549 : Blo 1478559 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B3327965 : Blo 1478559 3327965 := bbase (se 3 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 3327965 = 1247987) (by norm_num)
theorem B4990949 : Blo 1478559 4990949 := bbase (se 4 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 4990949 = 935803) (by norm_num)
theorem B1665013 : Blo 1478559 1665013 := bbase (se 5 (by rfl) ⟨78047, by rfl⟩ : syracuseStep 1665013 = 156095) (by norm_num)
theorem B2107397 : Blo 1478559 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B1665049 : Blo 1478559 1665049 := bbase (se 2 (by rfl) ⟨624393, by rfl⟩ : syracuseStep 1665049 = 1248787) (by norm_num)
theorem B3328037 : Blo 1478559 3328037 := bbase (se 4 (by rfl) ⟨312003, by rfl⟩ : syracuseStep 3328037 = 624007) (by norm_num)
theorem B4499509 : Blo 1478559 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B1665085 : Blo 1478559 1665085 := bbase (se 3 (by rfl) ⟨312203, by rfl⟩ : syracuseStep 1665085 = 624407) (by norm_num)
theorem B3745885 : Blo 1478559 3745885 := bbase (se 3 (by rfl) ⟨702353, by rfl⟩ : syracuseStep 3745885 = 1404707) (by norm_num)
theorem B1665121 : Blo 1478559 1665121 := bbase (se 2 (by rfl) ⟨624420, by rfl⟩ : syracuseStep 1665121 = 1248841) (by norm_num)
theorem B3328109 : Blo 1478559 3328109 := bbase (se 3 (by rfl) ⟨624020, by rfl⟩ : syracuseStep 3328109 = 1248041) (by norm_num)
theorem B1665157 : Blo 1478559 1665157 := bbase (se 4 (by rfl) ⟨156108, by rfl⟩ : syracuseStep 1665157 = 312217) (by norm_num)
theorem B1665193 : Blo 1478559 1665193 := bbase (se 2 (by rfl) ⟨624447, by rfl⟩ : syracuseStep 1665193 = 1248895) (by norm_num)
theorem B3328181 : Blo 1478559 3328181 := bbase (se 5 (by rfl) ⟨156008, by rfl⟩ : syracuseStep 3328181 = 312017) (by norm_num)
theorem B3745997 : Blo 1478559 3745997 := bbase (se 3 (by rfl) ⟨702374, by rfl⟩ : syracuseStep 3745997 = 1404749) (by norm_num)
theorem B1665229 : Blo 1478559 1665229 := bbase (se 3 (by rfl) ⟨312230, by rfl⟩ : syracuseStep 1665229 = 624461) (by norm_num)
theorem B1665265 : Blo 1478559 1665265 := bbase (se 2 (by rfl) ⟨624474, by rfl⟩ : syracuseStep 1665265 = 1248949) (by norm_num)
theorem B3328253 : Blo 1478559 3328253 := bbase (se 3 (by rfl) ⟨624047, by rfl⟩ : syracuseStep 3328253 = 1248095) (by norm_num)
theorem B1665301 : Blo 1478559 1665301 := bbase (se 6 (by rfl) ⟨39030, by rfl⟩ : syracuseStep 1665301 = 78061) (by norm_num)
theorem B1665337 : Blo 1478559 1665337 := bbase (se 2 (by rfl) ⟨624501, by rfl⟩ : syracuseStep 1665337 = 1249003) (by norm_num)
theorem B3328325 : Blo 1478559 3328325 := bbase (se 4 (by rfl) ⟨312030, by rfl⟩ : syracuseStep 3328325 = 624061) (by norm_num)
theorem B14223701 : Blo 1478559 14223701 := bbase (se 10 (by rfl) ⟨20835, by rfl⟩ : syracuseStep 14223701 = 41671) (by norm_num)
theorem B1665373 : Blo 1478559 1665373 := bbase (se 3 (by rfl) ⟨312257, by rfl⟩ : syracuseStep 1665373 = 624515) (by norm_num)
theorem B1665409 : Blo 1478559 1665409 := bbase (se 2 (by rfl) ⟨624528, by rfl⟩ : syracuseStep 1665409 = 1249057) (by norm_num)
theorem B3328397 : Blo 1478559 3328397 := bbase (se 3 (by rfl) ⟨624074, by rfl⟩ : syracuseStep 3328397 = 1248149) (by norm_num)
theorem B3746189 : Blo 1478559 3746189 := bbase (se 3 (by rfl) ⟨702410, by rfl⟩ : syracuseStep 3746189 = 1404821) (by norm_num)
theorem B4991381 : Blo 1478559 4991381 := bbase (se 6 (by rfl) ⟨116985, by rfl⟩ : syracuseStep 4991381 = 233971) (by norm_num)
theorem B1665445 : Blo 1478559 1665445 := bbase (se 4 (by rfl) ⟨156135, by rfl⟩ : syracuseStep 1665445 = 312271) (by norm_num)
theorem B1665481 : Blo 1478559 1665481 := bbase (se 2 (by rfl) ⟨624555, by rfl⟩ : syracuseStep 1665481 = 1249111) (by norm_num)
theorem B3328469 : Blo 1478559 3328469 := bbase (se 7 (by rfl) ⟨39005, by rfl⟩ : syracuseStep 3328469 = 78011) (by norm_num)
theorem B1665517 : Blo 1478559 1665517 := bbase (se 3 (by rfl) ⟨312284, by rfl⟩ : syracuseStep 1665517 = 624569) (by norm_num)
theorem B1665553 : Blo 1478559 1665553 := bbase (se 2 (by rfl) ⟨624582, by rfl⟩ : syracuseStep 1665553 = 1249165) (by norm_num)
theorem B7490069 : Blo 1478559 7490069 := bbase (se 6 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 7490069 = 351097) (by norm_num)
theorem B3328541 : Blo 1478559 3328541 := bbase (se 3 (by rfl) ⟨624101, by rfl⟩ : syracuseStep 3328541 = 1248203) (by norm_num)
theorem B2107949 : Blo 1478559 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B1665589 : Blo 1478559 1665589 := bbase (se 5 (by rfl) ⟨78074, by rfl⟩ : syracuseStep 1665589 = 156149) (by norm_num)
theorem B8538709 : Blo 1478559 8538709 := bbase (se 8 (by rfl) ⟨50031, by rfl⟩ : syracuseStep 8538709 = 100063) (by norm_num)
theorem B1665625 : Blo 1478559 1665625 := bbase (se 2 (by rfl) ⟨624609, by rfl⟩ : syracuseStep 1665625 = 1249219) (by norm_num)
theorem B5614181 : Blo 1478559 5614181 := bbase (se 4 (by rfl) ⟨526329, by rfl⟩ : syracuseStep 5614181 = 1052659) (by norm_num)
theorem B3328613 : Blo 1478559 3328613 := bbase (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) (by norm_num)
theorem B3328685 : Blo 1478559 3328685 := bbase (se 3 (by rfl) ⟨624128, by rfl⟩ : syracuseStep 3328685 = 1248257) (by norm_num)
theorem B11995829 : Blo 1478559 11995829 := bbase (se 5 (by rfl) ⟨562304, by rfl⟩ : syracuseStep 11995829 = 1124609) (by norm_num)
theorem B11389621 : Blo 1478559 11389621 := bbase (se 5 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 11389621 = 1067777) (by norm_num)
theorem B3746533 : Blo 1478559 3746533 := bbase (se 4 (by rfl) ⟨351237, by rfl⟩ : syracuseStep 3746533 = 702475) (by norm_num)
theorem B3328757 : Blo 1478559 3328757 := bbase (se 5 (by rfl) ⟨156035, by rfl⟩ : syracuseStep 3328757 = 312071) (by norm_num)
theorem B2370341 : Blo 1478559 2370341 := bbase (se 4 (by rfl) ⟨222219, by rfl⟩ : syracuseStep 2370341 = 444439) (by norm_num)
theorem B3328829 : Blo 1478559 3328829 := bbase (se 3 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 3328829 = 1248311) (by norm_num)
theorem B4991813 : Blo 1478559 4991813 := bbase (se 4 (by rfl) ⟨467982, by rfl⟩ : syracuseStep 4991813 = 935965) (by norm_num)
theorem B3746645 : Blo 1478559 3746645 := bbase (se 9 (by rfl) ⟨10976, by rfl⟩ : syracuseStep 3746645 = 21953) (by norm_num)
theorem B3328901 : Blo 1478559 3328901 := bbase (se 4 (by rfl) ⟨312084, by rfl⟩ : syracuseStep 3328901 = 624169) (by norm_num)
theorem B2370469 : Blo 1478559 2370469 := bbase (se 4 (by rfl) ⟨222231, by rfl⟩ : syracuseStep 2370469 = 444463) (by norm_num)
theorem B3328973 : Blo 1478559 3328973 := bbase (se 3 (by rfl) ⟨624182, by rfl⟩ : syracuseStep 3328973 = 1248365) (by norm_num)
theorem B3329045 : Blo 1478559 3329045 := bbase (se 6 (by rfl) ⟨78024, by rfl⟩ : syracuseStep 3329045 = 156049) (by norm_num)
theorem B3746837 : Blo 1478559 3746837 := bbase (se 6 (by rfl) ⟨87816, by rfl⟩ : syracuseStep 3746837 = 175633) (by norm_num)
theorem B12635189 : Blo 1478559 12635189 := bbase (se 5 (by rfl) ⟨592274, by rfl⟩ : syracuseStep 12635189 = 1184549) (by norm_num)
theorem B3329117 : Blo 1478559 3329117 := bbase (se 3 (by rfl) ⟨624209, by rfl⟩ : syracuseStep 3329117 = 1248419) (by norm_num)
theorem B7588981 : Blo 1478559 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B3329189 : Blo 1478559 3329189 := bbase (se 4 (by rfl) ⟨312111, by rfl⟩ : syracuseStep 3329189 = 624223) (by norm_num)
theorem B7204069 : Blo 1478559 7204069 := bbase (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) (by norm_num)
theorem B3329261 : Blo 1478559 3329261 := bbase (se 3 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 3329261 = 1248473) (by norm_num)
theorem B4992245 : Blo 1478559 4992245 := bbase (se 5 (by rfl) ⟨234011, by rfl⟩ : syracuseStep 4992245 = 468023) (by norm_num)
theorem B3329333 : Blo 1478559 3329333 := bbase (se 5 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 3329333 = 312125) (by norm_num)
theorem B21318997 : Blo 1478559 21318997 := bbase (se 11 (by rfl) ⟨15614, by rfl⟩ : syracuseStep 21318997 = 31229) (by norm_num)
theorem B2665813 : Blo 1478559 2665813 := bbase (se 11 (by rfl) ⟨1952, by rfl⟩ : syracuseStep 2665813 = 3905) (by norm_num)
theorem B3747181 : Blo 1478559 3747181 := bbase (se 3 (by rfl) ⟨702596, by rfl⟩ : syracuseStep 3747181 = 1405193) (by norm_num)
theorem B3329405 : Blo 1478559 3329405 := bbase (se 3 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 3329405 = 1248527) (by norm_num)
theorem B2665885 : Blo 1478559 2665885 := bbase (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) (by norm_num)
theorem B3329477 : Blo 1478559 3329477 := bbase (se 4 (by rfl) ⟨312138, by rfl⟩ : syracuseStep 3329477 = 624277) (by norm_num)
theorem B4214213 : Blo 1478559 4214213 := bbase (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) (by norm_num)
theorem B8424917 : Blo 1478559 8424917 := bbase (se 7 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 8424917 = 197459) (by norm_num)
theorem B3747293 : Blo 1478559 3747293 := bbase (se 3 (by rfl) ⟨702617, by rfl⟩ : syracuseStep 3747293 = 1405235) (by norm_num)
theorem B1871353 : Blo 1478559 1871353 := bbase (se 2 (by rfl) ⟨701757, by rfl⟩ : syracuseStep 1871353 = 1403515) (by norm_num)
theorem B3329549 : Blo 1478559 3329549 := bbase (se 3 (by rfl) ⟨624290, by rfl⟩ : syracuseStep 3329549 = 1248581) (by norm_num)
theorem B2666029 : Blo 1478559 2666029 := bbase (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) (by norm_num)
theorem B3329621 : Blo 1478559 3329621 := bbase (se 8 (by rfl) ⟨19509, by rfl⟩ : syracuseStep 3329621 = 39019) (by norm_num)
theorem B3329693 : Blo 1478559 3329693 := bbase (se 3 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 3329693 = 1248635) (by norm_num)
theorem B3747485 : Blo 1478559 3747485 := bbase (se 3 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 3747485 = 1405307) (by norm_num)
theorem B1871525 : Blo 1478559 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B4992677 : Blo 1478559 4992677 := bbase (se 4 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 4992677 = 936127) (by norm_num)
theorem B1871581 : Blo 1478559 1871581 := bbase (se 3 (by rfl) ⟨350921, by rfl⟩ : syracuseStep 1871581 = 701843) (by norm_num)
theorem B3329765 : Blo 1478559 3329765 := bbase (se 4 (by rfl) ⟨312165, by rfl⟩ : syracuseStep 3329765 = 624331) (by norm_num)
theorem B1601281 : Blo 1478559 1601281 := bbase (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) (by norm_num)
theorem B5615365 : Blo 1478559 5615365 := bbase (se 4 (by rfl) ⟨526440, by rfl⟩ : syracuseStep 5615365 = 1052881) (by norm_num)
theorem B4738837 : Blo 1478559 4738837 := bbase (se 6 (by rfl) ⟨111066, by rfl⟩ : syracuseStep 4738837 = 222133) (by norm_num)
theorem B7491365 : Blo 1478559 7491365 := bbase (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) (by norm_num)
theorem B3329837 : Blo 1478559 3329837 := bbase (se 3 (by rfl) ⟨624344, by rfl⟩ : syracuseStep 3329837 = 1248689) (by norm_num)
theorem B1871677 : Blo 1478559 1871677 := bbase (se 3 (by rfl) ⟨350939, by rfl⟩ : syracuseStep 1871677 = 701879) (by norm_num)
theorem B1601389 : Blo 1478559 1601389 := bbase (se 3 (by rfl) ⟨300260, by rfl⟩ : syracuseStep 1601389 = 600521) (by norm_num)
theorem B3329909 : Blo 1478559 3329909 := bbase (se 5 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 3329909 = 312179) (by norm_num)
theorem B3329981 : Blo 1478559 3329981 := bbase (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) (by norm_num)
theorem B1871849 : Blo 1478559 1871849 := bbase (se 2 (by rfl) ⟨701943, by rfl⟩ : syracuseStep 1871849 = 1403887) (by norm_num)
theorem B3158021 : Blo 1478559 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B3330053 : Blo 1478559 3330053 := bbase (se 4 (by rfl) ⟨312192, by rfl⟩ : syracuseStep 3330053 = 624385) (by norm_num)
theorem B1871905 : Blo 1478559 1871905 := bbase (se 2 (by rfl) ⟨701964, by rfl⟩ : syracuseStep 1871905 = 1403929) (by norm_num)
theorem B5615669 : Blo 1478559 5615669 := bbase (se 5 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 5615669 = 526469) (by norm_num)
theorem B3330125 : Blo 1478559 3330125 := bbase (se 3 (by rfl) ⟨624398, by rfl⟩ : syracuseStep 3330125 = 1248797) (by norm_num)
theorem B4993109 : Blo 1478559 4993109 := bbase (se 8 (by rfl) ⟨29256, by rfl⟩ : syracuseStep 4993109 = 58513) (by norm_num)
theorem B1872001 : Blo 1478559 1872001 := bbase (se 2 (by rfl) ⟨702000, by rfl⟩ : syracuseStep 1872001 = 1404001) (by norm_num)
theorem B3158165 : Blo 1478559 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B3330197 : Blo 1478559 3330197 := bbase (se 6 (by rfl) ⟨78051, by rfl⟩ : syracuseStep 3330197 = 156103) (by norm_num)
theorem B4002005 : Blo 1478559 4002005 := bbase (se 7 (by rfl) ⟨46898, by rfl⟩ : syracuseStep 4002005 = 93797) (by norm_num)
theorem B3330269 : Blo 1478559 3330269 := bbase (se 3 (by rfl) ⟨624425, by rfl⟩ : syracuseStep 3330269 = 1248851) (by norm_num)
theorem B3330341 : Blo 1478559 3330341 := bbase (se 4 (by rfl) ⟨312219, by rfl⟩ : syracuseStep 3330341 = 624439) (by norm_num)
theorem B1872173 : Blo 1478559 1872173 := bbase (se 3 (by rfl) ⟨351032, by rfl⟩ : syracuseStep 1872173 = 702065) (by norm_num)
theorem B16847189 : Blo 1478559 16847189 := bbase (se 10 (by rfl) ⟨24678, by rfl⟩ : syracuseStep 16847189 = 49357) (by norm_num)
theorem B2666837 : Blo 1478559 2666837 := bbase (se 10 (by rfl) ⟨3906, by rfl⟩ : syracuseStep 2666837 = 7813) (by norm_num)
theorem B1872229 : Blo 1478559 1872229 := bbase (se 4 (by rfl) ⟨175521, by rfl⟩ : syracuseStep 1872229 = 351043) (by norm_num)
theorem B3330413 : Blo 1478559 3330413 := bbase (se 3 (by rfl) ⟨624452, by rfl⟩ : syracuseStep 3330413 = 1248905) (by norm_num)
theorem B2666893 : Blo 1478559 2666893 := bbase (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) (by norm_num)
theorem B3330485 : Blo 1478559 3330485 := bbase (se 5 (by rfl) ⟨156116, by rfl⟩ : syracuseStep 3330485 = 312233) (by norm_num)
theorem B1872325 : Blo 1478559 1872325 := bbase (se 4 (by rfl) ⟨175530, by rfl⟩ : syracuseStep 1872325 = 351061) (by norm_num)
theorem B2666981 : Blo 1478559 2666981 := bbase (se 4 (by rfl) ⟨250029, by rfl⟩ : syracuseStep 2666981 = 500059) (by norm_num)
theorem B3330557 : Blo 1478559 3330557 := bbase (se 3 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 3330557 = 1248959) (by norm_num)
theorem B4993541 : Blo 1478559 4993541 := bbase (se 4 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 4993541 = 936289) (by norm_num)
theorem B3330629 : Blo 1478559 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B4215397 : Blo 1478559 4215397 := bbase (se 4 (by rfl) ⟨395193, by rfl⟩ : syracuseStep 4215397 = 790387) (by norm_num)
theorem B1872497 : Blo 1478559 1872497 := bbase (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) (by norm_num)
theorem B9474677 : Blo 1478559 9474677 := bbase (se 5 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 9474677 = 888251) (by norm_num)
theorem B2495117 : Blo 1478559 2495117 := bbase (se 3 (by rfl) ⟨467834, by rfl⟩ : syracuseStep 2495117 = 935669) (by norm_num)
theorem B3330701 : Blo 1478559 3330701 := bbase (se 3 (by rfl) ⟨624506, by rfl⟩ : syracuseStep 3330701 = 1249013) (by norm_num)
theorem B1872553 : Blo 1478559 1872553 := bbase (se 2 (by rfl) ⟨702207, by rfl⟩ : syracuseStep 1872553 = 1404415) (by norm_num)
theorem B3330773 : Blo 1478559 3330773 := bbase (se 7 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 3330773 = 78065) (by norm_num)
theorem B2847469 : Blo 1478559 2847469 := bbase (se 3 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 2847469 = 1067801) (by norm_num)
theorem B2667269 : Blo 1478559 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B4215557 : Blo 1478559 4215557 := bbase (se 4 (by rfl) ⟨395208, by rfl⟩ : syracuseStep 4215557 = 790417) (by norm_num)
theorem B1872649 : Blo 1478559 1872649 := bbase (se 2 (by rfl) ⟨702243, by rfl⟩ : syracuseStep 1872649 = 1404487) (by norm_num)
theorem B2495245 : Blo 1478559 2495245 := bbase (se 3 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 2495245 = 935717) (by norm_num)
theorem B3330845 : Blo 1478559 3330845 := bbase (se 3 (by rfl) ⟨624533, by rfl⟩ : syracuseStep 3330845 = 1249067) (by norm_num)
theorem B2495333 : Blo 1478559 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B3330917 : Blo 1478559 3330917 := bbase (se 4 (by rfl) ⟨312273, by rfl⟩ : syracuseStep 3330917 = 624547) (by norm_num)
theorem B3158909 : Blo 1478559 3158909 := bbase (se 3 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 3158909 = 1184591) (by norm_num)
theorem B2667413 : Blo 1478559 2667413 := bbase (se 6 (by rfl) ⟨62517, by rfl⟩ : syracuseStep 2667413 = 125035) (by norm_num)
theorem B2847653 : Blo 1478559 2847653 := bbase (se 4 (by rfl) ⟨266967, by rfl⟩ : syracuseStep 2847653 = 533935) (by norm_num)
theorem B3330989 : Blo 1478559 3330989 := bbase (se 3 (by rfl) ⟨624560, by rfl⟩ : syracuseStep 3330989 = 1249121) (by norm_num)
theorem B4993973 : Blo 1478559 4993973 := bbase (se 5 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 4993973 = 468185) (by norm_num)
theorem B1872821 : Blo 1478559 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B2495461 : Blo 1478559 2495461 := bbase (se 4 (by rfl) ⟨233949, by rfl⟩ : syracuseStep 2495461 = 467899) (by norm_num)
theorem B1872877 : Blo 1478559 1872877 := bbase (se 3 (by rfl) ⟨351164, by rfl⟩ : syracuseStep 1872877 = 702329) (by norm_num)
theorem B4215797 : Blo 1478559 4215797 := bbase (se 5 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 4215797 = 395231) (by norm_num)
theorem B3331061 : Blo 1478559 3331061 := bbase (se 5 (by rfl) ⟨156143, by rfl⟩ : syracuseStep 3331061 = 312287) (by norm_num)
theorem B5329925 : Blo 1478559 5329925 := bbase (se 4 (by rfl) ⟨499680, by rfl⟩ : syracuseStep 5329925 = 999361) (by norm_num)
theorem B2135093 : Blo 1478559 2135093 := bbase (se 5 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 2135093 = 200165) (by norm_num)
theorem B7492661 : Blo 1478559 7492661 := bbase (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) (by norm_num)
theorem B2495549 : Blo 1478559 2495549 := bbase (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) (by norm_num)
theorem B3331133 : Blo 1478559 3331133 := bbase (se 3 (by rfl) ⟨624587, by rfl⟩ : syracuseStep 3331133 = 1249175) (by norm_num)
theorem B1872973 : Blo 1478559 1872973 := bbase (se 3 (by rfl) ⟨351182, by rfl⟩ : syracuseStep 1872973 = 702365) (by norm_num)
theorem B1897573 : Blo 1478559 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B3372149 : Blo 1478559 3372149 := bbase (se 5 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 3372149 = 316139) (by norm_num)
theorem B2249845 : Blo 1478559 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B3331205 : Blo 1478559 3331205 := bbase (se 4 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 3331205 = 624601) (by norm_num)
theorem B2667701 : Blo 1478559 2667701 := bbase (se 5 (by rfl) ⟨125048, by rfl⟩ : syracuseStep 2667701 = 250097) (by norm_num)
theorem B4215989 : Blo 1478559 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B2495677 : Blo 1478559 2495677 := bbase (se 3 (by rfl) ⟨467939, by rfl⟩ : syracuseStep 2495677 = 935879) (by norm_num)
theorem B1873145 : Blo 1478559 1873145 := bbase (se 2 (by rfl) ⟨702429, by rfl⟩ : syracuseStep 1873145 = 1404859) (by norm_num)
theorem B2667773 : Blo 1478559 2667773 := bbase (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) (by norm_num)
theorem B2807045 : Blo 1478559 2807045 := bbase (se 4 (by rfl) ⟨263160, by rfl⟩ : syracuseStep 2807045 = 526321) (by norm_num)
theorem B2495765 : Blo 1478559 2495765 := bbase (se 6 (by rfl) ⟨58494, by rfl⟩ : syracuseStep 2495765 = 116989) (by norm_num)
theorem B1873201 : Blo 1478559 1873201 := bbase (se 2 (by rfl) ⟨702450, by rfl⟩ : syracuseStep 1873201 = 1404901) (by norm_num)
theorem B4994405 : Blo 1478559 4994405 := bbase (se 4 (by rfl) ⟨468225, by rfl⟩ : syracuseStep 4994405 = 936451) (by norm_num)
theorem B6321509 : Blo 1478559 6321509 := bbase (se 4 (by rfl) ⟨592641, by rfl⟩ : syracuseStep 6321509 = 1185283) (by norm_num)
theorem B1873297 : Blo 1478559 1873297 := bbase (se 2 (by rfl) ⟨702486, by rfl⟩ : syracuseStep 1873297 = 1404973) (by norm_num)
theorem B2495893 : Blo 1478559 2495893 := bbase (se 6 (by rfl) ⟨58497, by rfl⟩ : syracuseStep 2495893 = 116995) (by norm_num)
theorem B5330357 : Blo 1478559 5330357 := bbase (se 5 (by rfl) ⟨249860, by rfl⟩ : syracuseStep 5330357 = 499721) (by norm_num)
theorem B19207637 : Blo 1478559 19207637 := bbase (se 7 (by rfl) ⟨225089, by rfl⟩ : syracuseStep 19207637 = 450179) (by norm_num)
theorem B38426069 : Blo 1478559 38426069 := bbase (se 7 (by rfl) ⟨450305, by rfl⟩ : syracuseStep 38426069 = 900611) (by norm_num)
theorem B2495981 : Blo 1478559 2495981 := bbase (se 3 (by rfl) ⟨467996, by rfl⟩ : syracuseStep 2495981 = 935993) (by norm_num)
theorem B3421709 : Blo 1478559 3421709 := bbase (se 3 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 3421709 = 1283141) (by norm_num)
theorem B1873469 : Blo 1478559 1873469 := bbase (se 3 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 1873469 = 702551) (by norm_num)
theorem B2496109 : Blo 1478559 2496109 := bbase (se 3 (by rfl) ⟨468020, by rfl⟩ : syracuseStep 2496109 = 936041) (by norm_num)
theorem B3159661 : Blo 1478559 3159661 := bbase (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) (by norm_num)
theorem B1873525 : Blo 1478559 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B6321797 : Blo 1478559 6321797 := bbase (se 4 (by rfl) ⟨592668, by rfl⟩ : syracuseStep 6321797 = 1185337) (by norm_num)
theorem B2496197 : Blo 1478559 2496197 := bbase (se 4 (by rfl) ⟨234018, by rfl⟩ : syracuseStep 2496197 = 468037) (by norm_num)
theorem B1873621 : Blo 1478559 1873621 := bbase (se 7 (by rfl) ⟨21956, by rfl⟩ : syracuseStep 1873621 = 43913) (by norm_num)
theorem B3159805 : Blo 1478559 3159805 := bbase (se 3 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 3159805 = 1184927) (by norm_num)
theorem B4994837 : Blo 1478559 4994837 := bbase (se 6 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 4994837 = 234133) (by norm_num)
theorem B2496325 : Blo 1478559 2496325 := bbase (se 4 (by rfl) ⟨234030, by rfl⟩ : syracuseStep 2496325 = 468061) (by norm_num)
theorem B2217845 : Blo 1478559 2217845 := bbase (se 5 (by rfl) ⟨103961, by rfl⟩ : syracuseStep 2217845 = 207923) (by norm_num)
theorem B7108469 : Blo 1478559 7108469 := bbase (se 5 (by rfl) ⟨333209, by rfl⟩ : syracuseStep 7108469 = 666419) (by norm_num)
theorem B1873793 : Blo 1478559 1873793 := bbase (se 2 (by rfl) ⟨702672, by rfl⟩ : syracuseStep 1873793 = 1405345) (by norm_num)
theorem B2217869 : Blo 1478559 2217869 := bbase (se 3 (by rfl) ⟨415850, by rfl⟩ : syracuseStep 2217869 = 831701) (by norm_num)
theorem B2496413 : Blo 1478559 2496413 := bbase (se 3 (by rfl) ⟨468077, by rfl⟩ : syracuseStep 2496413 = 936155) (by norm_num)
theorem B2217893 : Blo 1478559 2217893 := bbase (se 4 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 2217893 = 415855) (by norm_num)
theorem B2217917 : Blo 1478559 2217917 := bbase (se 3 (by rfl) ⟨415859, by rfl⟩ : syracuseStep 2217917 = 831719) (by norm_num)
theorem B2217941 : Blo 1478559 2217941 := bbase (se 7 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 2217941 = 51983) (by norm_num)
theorem B22763477 : Blo 1478559 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B2217965 : Blo 1478559 2217965 := bbase (se 3 (by rfl) ⟨415868, by rfl⟩ : syracuseStep 2217965 = 831737) (by norm_num)
theorem B1578997 : Blo 1478559 1578997 := bbase (se 5 (by rfl) ⟨74015, by rfl⟩ : syracuseStep 1578997 = 148031) (by norm_num)
theorem B2807797 : Blo 1478559 2807797 := bbase (se 5 (by rfl) ⟨131615, by rfl⟩ : syracuseStep 2807797 = 263231) (by norm_num)
theorem B2217989 : Blo 1478559 2217989 := bbase (se 4 (by rfl) ⟨207936, by rfl⟩ : syracuseStep 2217989 = 415873) (by norm_num)
theorem B2218013 : Blo 1478559 2218013 := bbase (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) (by norm_num)
theorem B2496541 : Blo 1478559 2496541 := bbase (se 3 (by rfl) ⟨468101, by rfl⟩ : syracuseStep 2496541 = 936203) (by norm_num)
theorem B2218037 : Blo 1478559 2218037 := bbase (se 5 (by rfl) ⟨103970, by rfl⟩ : syracuseStep 2218037 = 207941) (by norm_num)
theorem B2218061 : Blo 1478559 2218061 := bbase (se 3 (by rfl) ⟨415886, by rfl⟩ : syracuseStep 2218061 = 831773) (by norm_num)
theorem B2218085 : Blo 1478559 2218085 := bbase (se 4 (by rfl) ⟨207945, by rfl⟩ : syracuseStep 2218085 = 415891) (by norm_num)
theorem B3553397 : Blo 1478559 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B2496629 : Blo 1478559 2496629 := bbase (se 5 (by rfl) ⟨117029, by rfl⟩ : syracuseStep 2496629 = 234059) (by norm_num)
theorem B5617781 : Blo 1478559 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B3160181 : Blo 1478559 3160181 := bbase (se 5 (by rfl) ⟨148133, by rfl⟩ : syracuseStep 3160181 = 296267) (by norm_num)
theorem B2218109 : Blo 1478559 2218109 := bbase (se 3 (by rfl) ⟨415895, by rfl⟩ : syracuseStep 2218109 = 831791) (by norm_num)
theorem B2807941 : Blo 1478559 2807941 := bbase (se 4 (by rfl) ⟨263244, by rfl⟩ : syracuseStep 2807941 = 526489) (by norm_num)
theorem B2218133 : Blo 1478559 2218133 := bbase (se 6 (by rfl) ⟨51987, by rfl⟩ : syracuseStep 2218133 = 103975) (by norm_num)
theorem B2218157 : Blo 1478559 2218157 := bbase (se 3 (by rfl) ⟨415904, by rfl⟩ : syracuseStep 2218157 = 831809) (by norm_num)
theorem B1579181 : Blo 1478559 1579181 := bbase (se 3 (by rfl) ⟨296096, by rfl⟩ : syracuseStep 1579181 = 592193) (by norm_num)
theorem B2218181 : Blo 1478559 2218181 := bbase (se 4 (by rfl) ⟨207954, by rfl⟩ : syracuseStep 2218181 = 415909) (by norm_num)
theorem B4995269 : Blo 1478559 4995269 := bbase (se 4 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 4995269 = 936613) (by norm_num)
theorem B2218205 : Blo 1478559 2218205 := bbase (se 3 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 2218205 = 831827) (by norm_num)
theorem B1710301 : Blo 1478559 1710301 := bbase (se 3 (by rfl) ⟨320681, by rfl⟩ : syracuseStep 1710301 = 641363) (by norm_num)
theorem B2218229 : Blo 1478559 2218229 := bbase (se 5 (by rfl) ⟨103979, by rfl⟩ : syracuseStep 2218229 = 207959) (by norm_num)
theorem B14219509 : Blo 1478559 14219509 := bbase (se 5 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 14219509 = 1333079) (by norm_num)
theorem B2496757 : Blo 1478559 2496757 := bbase (se 5 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 2496757 = 234071) (by norm_num)
theorem B2218253 : Blo 1478559 2218253 := bbase (se 3 (by rfl) ⟨415922, by rfl⟩ : syracuseStep 2218253 = 831845) (by norm_num)
theorem B2218277 : Blo 1478559 2218277 := bbase (se 4 (by rfl) ⟨207963, by rfl⟩ : syracuseStep 2218277 = 415927) (by norm_num)
theorem B2808101 : Blo 1478559 2808101 := bbase (se 4 (by rfl) ⟨263259, by rfl⟩ : syracuseStep 2808101 = 526519) (by norm_num)
theorem B2218301 : Blo 1478559 2218301 := bbase (se 3 (by rfl) ⟨415931, by rfl⟩ : syracuseStep 2218301 = 831863) (by norm_num)
theorem B1562941 : Blo 1478559 1562941 := bbase (se 3 (by rfl) ⟨293051, by rfl⟩ : syracuseStep 1562941 = 586103) (by norm_num)
theorem B7493957 : Blo 1478559 7493957 := bbase (se 4 (by rfl) ⟨702558, by rfl⟩ : syracuseStep 7493957 = 1405117) (by norm_num)
theorem B2496845 : Blo 1478559 2496845 := bbase (se 3 (by rfl) ⟨468158, by rfl⟩ : syracuseStep 2496845 = 936317) (by norm_num)
theorem B2218325 : Blo 1478559 2218325 := bbase (se 10 (by rfl) ⟨3249, by rfl⟩ : syracuseStep 2218325 = 6499) (by norm_num)
theorem B1898845 : Blo 1478559 1898845 := bbase (se 3 (by rfl) ⟨356033, by rfl⟩ : syracuseStep 1898845 = 712067) (by norm_num)
theorem B2218349 : Blo 1478559 2218349 := bbase (se 3 (by rfl) ⟨415940, by rfl⟩ : syracuseStep 2218349 = 831881) (by norm_num)
theorem B6322549 : Blo 1478559 6322549 := bbase (se 5 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 6322549 = 592739) (by norm_num)
theorem B2218373 : Blo 1478559 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B5618069 : Blo 1478559 5618069 := bbase (se 6 (by rfl) ⟨131673, by rfl⟩ : syracuseStep 5618069 = 263347) (by norm_num)
theorem B2218397 : Blo 1478559 2218397 := bbase (se 3 (by rfl) ⟨415949, by rfl⟩ : syracuseStep 2218397 = 831899) (by norm_num)
theorem B2218421 : Blo 1478559 2218421 := bbase (se 5 (by rfl) ⟨103988, by rfl⟩ : syracuseStep 2218421 = 207977) (by norm_num)
theorem B2808245 : Blo 1478559 2808245 := bbase (se 5 (by rfl) ⟨131636, by rfl⟩ : syracuseStep 2808245 = 263273) (by norm_num)
theorem B2218445 : Blo 1478559 2218445 := bbase (se 3 (by rfl) ⟨415958, by rfl⟩ : syracuseStep 2218445 = 831917) (by norm_num)
theorem B2496973 : Blo 1478559 2496973 := bbase (se 3 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 2496973 = 936365) (by norm_num)
theorem B10664405 : Blo 1478559 10664405 := bbase (se 7 (by rfl) ⟨124973, by rfl⟩ : syracuseStep 10664405 = 249947) (by norm_num)
theorem B2218469 : Blo 1478559 2218469 := bbase (se 4 (by rfl) ⟨207981, by rfl⟩ : syracuseStep 2218469 = 415963) (by norm_num)
theorem B3160549 : Blo 1478559 3160549 := bbase (se 4 (by rfl) ⟨296301, by rfl⟩ : syracuseStep 3160549 = 592603) (by norm_num)
theorem B2218493 : Blo 1478559 2218493 := bbase (se 3 (by rfl) ⟨415967, by rfl⟩ : syracuseStep 2218493 = 831935) (by norm_num)
theorem B5061125 : Blo 1478559 5061125 := bbase (se 4 (by rfl) ⟨474480, by rfl⟩ : syracuseStep 5061125 = 948961) (by norm_num)
theorem B2218517 : Blo 1478559 2218517 := bbase (se 6 (by rfl) ⟨51996, by rfl⟩ : syracuseStep 2218517 = 103993) (by norm_num)
theorem B2497061 : Blo 1478559 2497061 := bbase (se 4 (by rfl) ⟨234099, by rfl⟩ : syracuseStep 2497061 = 468199) (by norm_num)
theorem B2218541 : Blo 1478559 2218541 := bbase (se 3 (by rfl) ⟨415976, by rfl⟩ : syracuseStep 2218541 = 831953) (by norm_num)
theorem B2218565 : Blo 1478559 2218565 := bbase (se 4 (by rfl) ⟨207990, by rfl⟩ : syracuseStep 2218565 = 415981) (by norm_num)
theorem B37935701 : Blo 1478559 37935701 := bbase (se 8 (by rfl) ⟨222279, by rfl⟩ : syracuseStep 37935701 = 444559) (by norm_num)
theorem B2218589 : Blo 1478559 2218589 := bbase (se 3 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 2218589 = 831971) (by norm_num)
theorem B2218613 : Blo 1478559 2218613 := bbase (se 5 (by rfl) ⟨103997, by rfl⟩ : syracuseStep 2218613 = 207995) (by norm_num)
theorem B4995701 : Blo 1478559 4995701 := bbase (se 5 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 4995701 = 468347) (by norm_num)
theorem B2218637 : Blo 1478559 2218637 := bbase (se 3 (by rfl) ⟨415994, by rfl⟩ : syracuseStep 2218637 = 831989) (by norm_num)
theorem B2218661 : Blo 1478559 2218661 := bbase (se 4 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 2218661 = 415999) (by norm_num)
theorem B2497189 : Blo 1478559 2497189 := bbase (se 4 (by rfl) ⟨234111, by rfl⟩ : syracuseStep 2497189 = 468223) (by norm_num)
theorem B2218685 : Blo 1478559 2218685 := bbase (se 3 (by rfl) ⟨416003, by rfl⟩ : syracuseStep 2218685 = 832007) (by norm_num)
theorem B2218709 : Blo 1478559 2218709 := bbase (se 7 (by rfl) ⟨26000, by rfl⟩ : syracuseStep 2218709 = 52001) (by norm_num)
theorem B2808533 : Blo 1478559 2808533 := bbase (se 7 (by rfl) ⟨32912, by rfl⟩ : syracuseStep 2808533 = 65825) (by norm_num)
theorem B7486181 : Blo 1478559 7486181 := bbase (se 4 (by rfl) ⟨701829, by rfl⟩ : syracuseStep 7486181 = 1403659) (by norm_num)
theorem B4741861 : Blo 1478559 4741861 := bbase (se 4 (by rfl) ⟨444549, by rfl⟩ : syracuseStep 4741861 = 889099) (by norm_num)
theorem B2218733 : Blo 1478559 2218733 := bbase (se 3 (by rfl) ⟨416012, by rfl⟩ : syracuseStep 2218733 = 832025) (by norm_num)
theorem B2497277 : Blo 1478559 2497277 := bbase (se 3 (by rfl) ⟨468239, by rfl⟩ : syracuseStep 2497277 = 936479) (by norm_num)
theorem B2218757 : Blo 1478559 2218757 := bbase (se 4 (by rfl) ⟨208008, by rfl⟩ : syracuseStep 2218757 = 416017) (by norm_num)
theorem B2218781 : Blo 1478559 2218781 := bbase (se 3 (by rfl) ⟨416021, by rfl⟩ : syracuseStep 2218781 = 832043) (by norm_num)
theorem B1776425 : Blo 1478559 1776425 := bbase (se 2 (by rfl) ⟨666159, by rfl⟩ : syracuseStep 1776425 = 1332319) (by norm_num)
theorem B2218805 : Blo 1478559 2218805 := bbase (se 5 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 2218805 = 208013) (by norm_num)
theorem B1776449 : Blo 1478559 1776449 := bbase (se 2 (by rfl) ⟨666168, by rfl⟩ : syracuseStep 1776449 = 1332337) (by norm_num)
theorem B2218829 : Blo 1478559 2218829 := bbase (se 3 (by rfl) ⟨416030, by rfl⟩ : syracuseStep 2218829 = 832061) (by norm_num)
theorem B3373901 : Blo 1478559 3373901 := bbase (se 3 (by rfl) ⟨632606, by rfl⟩ : syracuseStep 3373901 = 1265213) (by norm_num)
theorem B2218853 : Blo 1478559 2218853 := bbase (se 4 (by rfl) ⟨208017, by rfl⟩ : syracuseStep 2218853 = 416035) (by norm_num)
theorem B2808685 : Blo 1478559 2808685 := bbase (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) (by norm_num)
theorem B12647285 : Blo 1478559 12647285 := bbase (se 5 (by rfl) ⟨592841, by rfl⟩ : syracuseStep 12647285 = 1185683) (by norm_num)
theorem B2218877 : Blo 1478559 2218877 := bbase (se 3 (by rfl) ⟨416039, by rfl⟩ : syracuseStep 2218877 = 832079) (by norm_num)
theorem B2497405 : Blo 1478559 2497405 := bbase (se 3 (by rfl) ⟨468263, by rfl⟩ : syracuseStep 2497405 = 936527) (by norm_num)
theorem B2218901 : Blo 1478559 2218901 := bbase (se 6 (by rfl) ⟨52005, by rfl⟩ : syracuseStep 2218901 = 104011) (by norm_num)
theorem B1579933 : Blo 1478559 1579933 := bbase (se 3 (by rfl) ⟨296237, by rfl⟩ : syracuseStep 1579933 = 592475) (by norm_num)
theorem B2218925 : Blo 1478559 2218925 := bbase (se 3 (by rfl) ⟨416048, by rfl⟩ : syracuseStep 2218925 = 832097) (by norm_num)
theorem B3742645 : Blo 1478559 3742645 := bbase (se 5 (by rfl) ⟨175436, by rfl⟩ : syracuseStep 3742645 = 350873) (by norm_num)
theorem B2218949 : Blo 1478559 2218949 := bbase (se 4 (by rfl) ⟨208026, by rfl⟩ : syracuseStep 2218949 = 416053) (by norm_num)
theorem B2497493 : Blo 1478559 2497493 := bbase (se 7 (by rfl) ⟨29267, by rfl⟩ : syracuseStep 2497493 = 58535) (by norm_num)
theorem B2218973 : Blo 1478559 2218973 := bbase (se 3 (by rfl) ⟨416057, by rfl⟩ : syracuseStep 2218973 = 832115) (by norm_num)
theorem B1580005 : Blo 1478559 1580005 := bbase (se 4 (by rfl) ⟨148125, by rfl⟩ : syracuseStep 1580005 = 296251) (by norm_num)
theorem B2218997 : Blo 1478559 2218997 := bbase (se 5 (by rfl) ⟨104015, by rfl⟩ : syracuseStep 2218997 = 208031) (by norm_num)
theorem B2219021 : Blo 1478559 2219021 := bbase (se 3 (by rfl) ⟨416066, by rfl⟩ : syracuseStep 2219021 = 832133) (by norm_num)
theorem B3742757 : Blo 1478559 3742757 := bbase (se 4 (by rfl) ⟨350883, by rfl⟩ : syracuseStep 3742757 = 701767) (by norm_num)
theorem B2219045 : Blo 1478559 2219045 := bbase (se 4 (by rfl) ⟨208035, by rfl⟩ : syracuseStep 2219045 = 416071) (by norm_num)
theorem B4996133 : Blo 1478559 4996133 := bbase (se 4 (by rfl) ⟨468387, by rfl⟩ : syracuseStep 4996133 = 936775) (by norm_num)
theorem B2219069 : Blo 1478559 2219069 := bbase (se 3 (by rfl) ⟨416075, by rfl⟩ : syracuseStep 2219069 = 832151) (by norm_num)
theorem B2219093 : Blo 1478559 2219093 := bbase (se 8 (by rfl) ⟨13002, by rfl⟩ : syracuseStep 2219093 = 26005) (by norm_num)
theorem B2497621 : Blo 1478559 2497621 := bbase (se 8 (by rfl) ⟨14634, by rfl⟩ : syracuseStep 2497621 = 29269) (by norm_num)
theorem B6323285 : Blo 1478559 6323285 := bbase (se 8 (by rfl) ⟨37050, by rfl⟩ : syracuseStep 6323285 = 74101) (by norm_num)
theorem B2219117 : Blo 1478559 2219117 := bbase (se 3 (by rfl) ⟨416084, by rfl⟩ : syracuseStep 2219117 = 832169) (by norm_num)
theorem B1776757 : Blo 1478559 1776757 := bbase (se 5 (by rfl) ⟨83285, by rfl⟩ : syracuseStep 1776757 = 166571) (by norm_num)
theorem B2219141 : Blo 1478559 2219141 := bbase (se 4 (by rfl) ⟨208044, by rfl⟩ : syracuseStep 2219141 = 416089) (by norm_num)
theorem B1580185 : Blo 1478559 1580185 := bbase (se 2 (by rfl) ⟨592569, by rfl⟩ : syracuseStep 1580185 = 1185139) (by norm_num)
theorem B2219165 : Blo 1478559 2219165 := bbase (se 3 (by rfl) ⟨416093, by rfl⟩ : syracuseStep 2219165 = 832187) (by norm_num)
theorem B2808989 : Blo 1478559 2808989 := bbase (se 3 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 2808989 = 1053371) (by norm_num)
theorem B2497709 : Blo 1478559 2497709 := bbase (se 3 (by rfl) ⟨468320, by rfl⟩ : syracuseStep 2497709 = 936641) (by norm_num)
theorem B2219189 : Blo 1478559 2219189 := bbase (se 5 (by rfl) ⟨104024, by rfl⟩ : syracuseStep 2219189 = 208049) (by norm_num)
theorem B2219213 : Blo 1478559 2219213 := bbase (se 3 (by rfl) ⟨416102, by rfl⟩ : syracuseStep 2219213 = 832205) (by norm_num)
theorem B3742949 : Blo 1478559 3742949 := bbase (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) (by norm_num)
theorem B2219237 : Blo 1478559 2219237 := bbase (se 4 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 2219237 = 416107) (by norm_num)
theorem B2219261 : Blo 1478559 2219261 := bbase (se 3 (by rfl) ⟨416111, by rfl⟩ : syracuseStep 2219261 = 832223) (by norm_num)
theorem B2219285 : Blo 1478559 2219285 := bbase (se 6 (by rfl) ⟨52014, by rfl⟩ : syracuseStep 2219285 = 104029) (by norm_num)
theorem B1776929 : Blo 1478559 1776929 := bbase (se 2 (by rfl) ⟨666348, by rfl⟩ : syracuseStep 1776929 = 1332697) (by norm_num)
theorem B2219309 : Blo 1478559 2219309 := bbase (se 3 (by rfl) ⟨416120, by rfl⟩ : syracuseStep 2219309 = 832241) (by norm_num)
theorem B2497837 : Blo 1478559 2497837 := bbase (se 3 (by rfl) ⟨468344, by rfl⟩ : syracuseStep 2497837 = 936689) (by norm_num)
theorem B2219333 : Blo 1478559 2219333 := bbase (se 4 (by rfl) ⟨208062, by rfl⟩ : syracuseStep 2219333 = 416125) (by norm_num)
theorem B2219357 : Blo 1478559 2219357 := bbase (se 3 (by rfl) ⟨416129, by rfl⟩ : syracuseStep 2219357 = 832259) (by norm_num)
theorem B2219381 : Blo 1478559 2219381 := bbase (se 5 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 2219381 = 208067) (by norm_num)
theorem B2497925 : Blo 1478559 2497925 := bbase (se 4 (by rfl) ⟨234180, by rfl⟩ : syracuseStep 2497925 = 468361) (by norm_num)
theorem B2219405 : Blo 1478559 2219405 := bbase (se 3 (by rfl) ⟨416138, by rfl⟩ : syracuseStep 2219405 = 832277) (by norm_num)
theorem B1777045 : Blo 1478559 1777045 := bbase (se 6 (by rfl) ⟨41649, by rfl⟩ : syracuseStep 1777045 = 83299) (by norm_num)
theorem B2219429 : Blo 1478559 2219429 := bbase (se 4 (by rfl) ⟨208071, by rfl⟩ : syracuseStep 2219429 = 416143) (by norm_num)
theorem B2219453 : Blo 1478559 2219453 := bbase (se 3 (by rfl) ⟨416147, by rfl⟩ : syracuseStep 2219453 = 832295) (by norm_num)
theorem B2219477 : Blo 1478559 2219477 := bbase (se 7 (by rfl) ⟨26009, by rfl⟩ : syracuseStep 2219477 = 52019) (by norm_num)
theorem B4996565 : Blo 1478559 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B2219501 : Blo 1478559 2219501 := bbase (se 3 (by rfl) ⟨416156, by rfl⟩ : syracuseStep 2219501 = 832313) (by norm_num)
theorem B1777141 : Blo 1478559 1777141 := bbase (se 5 (by rfl) ⟨83303, by rfl⟩ : syracuseStep 1777141 = 166607) (by norm_num)
theorem B1924597 : Blo 1478559 1924597 := bbase (se 5 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 1924597 = 180431) (by norm_num)
theorem B2219525 : Blo 1478559 2219525 := bbase (se 4 (by rfl) ⟨208080, by rfl⟩ : syracuseStep 2219525 = 416161) (by norm_num)
theorem B2498053 : Blo 1478559 2498053 := bbase (se 4 (by rfl) ⟨234192, by rfl⟩ : syracuseStep 2498053 = 468385) (by norm_num)
theorem B2219549 : Blo 1478559 2219549 := bbase (se 3 (by rfl) ⟨416165, by rfl⟩ : syracuseStep 2219549 = 832331) (by norm_num)
theorem B1949221 : Blo 1478559 1949221 := bbase (se 4 (by rfl) ⟨182739, by rfl⟩ : syracuseStep 1949221 = 365479) (by norm_num)
theorem B2219573 : Blo 1478559 2219573 := bbase (se 5 (by rfl) ⟨104042, by rfl⟩ : syracuseStep 2219573 = 208085) (by norm_num)
theorem B5619253 : Blo 1478559 5619253 := bbase (se 5 (by rfl) ⟨263402, by rfl⟩ : syracuseStep 5619253 = 526805) (by norm_num)
theorem B3743293 : Blo 1478559 3743293 := bbase (se 3 (by rfl) ⟨701867, by rfl⟩ : syracuseStep 3743293 = 1403735) (by norm_num)
theorem B2219597 : Blo 1478559 2219597 := bbase (se 3 (by rfl) ⟨416174, by rfl⟩ : syracuseStep 2219597 = 832349) (by norm_num)
theorem B1580629 : Blo 1478559 1580629 := bbase (se 8 (by rfl) ⟨9261, by rfl⟩ : syracuseStep 1580629 = 18523) (by norm_num)
theorem B7495253 : Blo 1478559 7495253 := bbase (se 8 (by rfl) ⟨43917, by rfl⟩ : syracuseStep 7495253 = 87835) (by norm_num)
theorem B2498141 : Blo 1478559 2498141 := bbase (se 3 (by rfl) ⟨468401, by rfl⟩ : syracuseStep 2498141 = 936803) (by norm_num)
theorem B2219621 : Blo 1478559 2219621 := bbase (se 4 (by rfl) ⟨208089, by rfl⟩ : syracuseStep 2219621 = 416179) (by norm_num)
theorem B2219645 : Blo 1478559 2219645 := bbase (se 3 (by rfl) ⟨416183, by rfl⟩ : syracuseStep 2219645 = 832367) (by norm_num)
theorem B1777285 : Blo 1478559 1777285 := bbase (se 4 (by rfl) ⟨166620, by rfl⟩ : syracuseStep 1777285 = 333241) (by norm_num)
theorem B2219669 : Blo 1478559 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B3743405 : Blo 1478559 3743405 := bbase (se 3 (by rfl) ⟨701888, by rfl⟩ : syracuseStep 3743405 = 1403777) (by norm_num)
theorem B2219693 : Blo 1478559 2219693 := bbase (se 3 (by rfl) ⟨416192, by rfl⟩ : syracuseStep 2219693 = 832385) (by norm_num)
theorem B2219717 : Blo 1478559 2219717 := bbase (se 4 (by rfl) ⟨208098, by rfl⟩ : syracuseStep 2219717 = 416197) (by norm_num)
theorem B1580753 : Blo 1478559 1580753 := bbase (se 2 (by rfl) ⟨592782, by rfl⟩ : syracuseStep 1580753 = 1185565) (by norm_num)
theorem B2219741 : Blo 1478559 2219741 := bbase (se 3 (by rfl) ⟨416201, by rfl⟩ : syracuseStep 2219741 = 832403) (by norm_num)
theorem B2498269 : Blo 1478559 2498269 := bbase (se 3 (by rfl) ⟨468425, by rfl⟩ : syracuseStep 2498269 = 936851) (by norm_num)
theorem B7995125 : Blo 1478559 7995125 := bbase (se 5 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 7995125 = 749543) (by norm_num)
theorem B2219765 : Blo 1478559 2219765 := bbase (se 5 (by rfl) ⟨104051, by rfl⟩ : syracuseStep 2219765 = 208103) (by norm_num)
theorem B2219789 : Blo 1478559 2219789 := bbase (se 3 (by rfl) ⟨416210, by rfl⟩ : syracuseStep 2219789 = 832421) (by norm_num)
theorem B2219813 : Blo 1478559 2219813 := bbase (se 4 (by rfl) ⟨208107, by rfl⟩ : syracuseStep 2219813 = 416215) (by norm_num)
theorem B2498357 : Blo 1478559 2498357 := bbase (se 5 (by rfl) ⟨117110, by rfl⟩ : syracuseStep 2498357 = 234221) (by norm_num)
theorem B2219837 : Blo 1478559 2219837 := bbase (se 3 (by rfl) ⟨416219, by rfl⟩ : syracuseStep 2219837 = 832439) (by norm_num)
theorem B4497221 : Blo 1478559 4497221 := bbase (se 4 (by rfl) ⟨421614, by rfl⟩ : syracuseStep 4497221 = 843229) (by norm_num)
theorem B2219861 : Blo 1478559 2219861 := bbase (se 9 (by rfl) ⟨6503, by rfl⟩ : syracuseStep 2219861 = 13007) (by norm_num)
theorem B3374941 : Blo 1478559 3374941 := bbase (se 3 (by rfl) ⟨632801, by rfl⟩ : syracuseStep 3374941 = 1265603) (by norm_num)
theorem B5619557 : Blo 1478559 5619557 := bbase (se 4 (by rfl) ⟨526833, by rfl⟩ : syracuseStep 5619557 = 1053667) (by norm_num)
theorem B3743597 : Blo 1478559 3743597 := bbase (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) (by norm_num)
theorem B3604333 : Blo 1478559 3604333 := bbase (se 3 (by rfl) ⟨675812, by rfl⟩ : syracuseStep 3604333 = 1351625) (by norm_num)
theorem B2219885 : Blo 1478559 2219885 := bbase (se 3 (by rfl) ⟨416228, by rfl⟩ : syracuseStep 2219885 = 832457) (by norm_num)
theorem B2219909 : Blo 1478559 2219909 := bbase (se 4 (by rfl) ⟨208116, by rfl⟩ : syracuseStep 2219909 = 416233) (by norm_num)
theorem B2809741 : Blo 1478559 2809741 := bbase (se 3 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 2809741 = 1053653) (by norm_num)
theorem B2219933 : Blo 1478559 2219933 := bbase (se 3 (by rfl) ⟨416237, by rfl⟩ : syracuseStep 2219933 = 832475) (by norm_num)
theorem B4210613 : Blo 1478559 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B2219957 : Blo 1478559 2219957 := bbase (se 5 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 2219957 = 208121) (by norm_num)
theorem B3162053 : Blo 1478559 3162053 := bbase (se 4 (by rfl) ⟨296442, by rfl⟩ : syracuseStep 3162053 = 592885) (by norm_num)
theorem B2219981 : Blo 1478559 2219981 := bbase (se 3 (by rfl) ⟨416246, by rfl⟩ : syracuseStep 2219981 = 832493) (by norm_num)
theorem B1581005 : Blo 1478559 1581005 := bbase (se 3 (by rfl) ⟨296438, by rfl⟩ : syracuseStep 1581005 = 592877) (by norm_num)
theorem B2998237 : Blo 1478559 2998237 := bbase (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) (by norm_num)
theorem B2220005 : Blo 1478559 2220005 := bbase (se 4 (by rfl) ⟨208125, by rfl⟩ : syracuseStep 2220005 = 416251) (by norm_num)
theorem B2564077 : Blo 1478559 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B7487477 : Blo 1478559 7487477 := bbase (se 5 (by rfl) ⟨350975, by rfl⟩ : syracuseStep 7487477 = 701951) (by norm_num)
theorem B2220029 : Blo 1478559 2220029 := bbase (se 3 (by rfl) ⟨416255, by rfl⟩ : syracuseStep 2220029 = 832511) (by norm_num)
theorem B2105347 : Blo 1478559 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B2220035 : Blo 1478559 2220035 := bstep (se 1 (by rfl) ⟨1665026, by rfl⟩ : syracuseStep 2220035 = 3330053) B3330053
theorem B5619725 : Blo 1478559 5619725 := bstep (se 3 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 5619725 = 2107397) B2107397
theorem B2220065 : Blo 1478559 2220065 := bstep (se 2 (by rfl) ⟨832524, by rfl⟩ : syracuseStep 2220065 = 1665049) B1665049
theorem B3743779 : Blo 1478559 3743779 := bstep (se 1 (by rfl) ⟨2807834, by rfl⟩ : syracuseStep 3743779 = 5615669) B5615669
theorem B2220083 : Blo 1478559 2220083 := bstep (se 1 (by rfl) ⟨1665062, by rfl⟩ : syracuseStep 2220083 = 3330125) B3330125
theorem B2220113 : Blo 1478559 2220113 := bstep (se 2 (by rfl) ⟨832542, by rfl⟩ : syracuseStep 2220113 = 1665085) B1665085
theorem B2105443 : Blo 1478559 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B2220131 : Blo 1478559 2220131 := bstep (se 1 (by rfl) ⟨1665098, by rfl⟩ : syracuseStep 2220131 = 3330197) B3330197
theorem B2220161 : Blo 1478559 2220161 := bstep (se 2 (by rfl) ⟨832560, by rfl⟩ : syracuseStep 2220161 = 1665121) B1665121
theorem B5693581 : Blo 1478559 5693581 := bstep (se 3 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 5693581 = 2135093) B2135093
theorem B2220179 : Blo 1478559 2220179 := bstep (se 1 (by rfl) ⟨1665134, by rfl⟩ : syracuseStep 2220179 = 3330269) B3330269
theorem B3743921 : Blo 1478559 3743921 := bstep (se 2 (by rfl) ⟨1403970, by rfl⟩ : syracuseStep 3743921 = 2807941) B2807941
theorem B2220209 : Blo 1478559 2220209 := bstep (se 2 (by rfl) ⟨832578, by rfl⟩ : syracuseStep 2220209 = 1665157) B1665157
theorem B2220227 : Blo 1478559 2220227 := bstep (se 1 (by rfl) ⟨1665170, by rfl⟩ : syracuseStep 2220227 = 3330341) B3330341
theorem B10117325 : Blo 1478559 10117325 := bstep (se 3 (by rfl) ⟨1896998, by rfl⟩ : syracuseStep 10117325 = 3793997) B3793997
theorem B5333197 : Blo 1478559 5333197 := bstep (se 3 (by rfl) ⟨999974, by rfl⟩ : syracuseStep 5333197 = 1999949) B1999949
theorem B2220257 : Blo 1478559 2220257 := bstep (se 2 (by rfl) ⟨832596, by rfl⟩ : syracuseStep 2220257 = 1665193) B1665193
theorem B11231459 : Blo 1478559 11231459 := bstep (se 1 (by rfl) ⟨8423594, by rfl⟩ : syracuseStep 11231459 = 16847189) B16847189
theorem B1777891 : Blo 1478559 1777891 := bstep (se 1 (by rfl) ⟨1333418, by rfl⟩ : syracuseStep 1777891 = 2666837) B2666837
theorem B2220275 : Blo 1478559 2220275 := bstep (se 1 (by rfl) ⟨1665206, by rfl⟩ : syracuseStep 2220275 = 3330413) B3330413
theorem B2220305 : Blo 1478559 2220305 := bstep (se 2 (by rfl) ⟨832614, by rfl⟩ : syracuseStep 2220305 = 1665229) B1665229
theorem B2220323 : Blo 1478559 2220323 := bstep (se 1 (by rfl) ⟨1665242, by rfl⟩ : syracuseStep 2220323 = 3330485) B3330485
theorem B2220353 : Blo 1478559 2220353 := bstep (se 2 (by rfl) ⟨832632, by rfl⟩ : syracuseStep 2220353 = 1665265) B1665265
theorem B1999171 : Blo 1478559 1999171 := bstep (se 1 (by rfl) ⟨1499378, by rfl⟩ : syracuseStep 1999171 = 2998757) B2998757
theorem B1777987 : Blo 1478559 1777987 := bstep (se 1 (by rfl) ⟨1333490, by rfl⟩ : syracuseStep 1777987 = 2666981) B2666981
theorem B2220371 : Blo 1478559 2220371 := bstep (se 1 (by rfl) ⟨1665278, by rfl⟩ : syracuseStep 2220371 = 3330557) B3330557
theorem B2220401 : Blo 1478559 2220401 := bstep (se 2 (by rfl) ⟨832650, by rfl⟩ : syracuseStep 2220401 = 1665301) B1665301
theorem B2220419 : Blo 1478559 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B2220449 : Blo 1478559 2220449 := bstep (se 2 (by rfl) ⟨832668, by rfl⟩ : syracuseStep 2220449 = 1665337) B1665337
theorem B6316451 : Blo 1478559 6316451 := bstep (se 1 (by rfl) ⟨4737338, by rfl⟩ : syracuseStep 6316451 = 9474677) B9474677
theorem B1663411 : Blo 1478559 1663411 := bstep (se 1 (by rfl) ⟨1247558, by rfl⟩ : syracuseStep 1663411 = 2495117) B2495117
theorem B2220467 : Blo 1478559 2220467 := bstep (se 1 (by rfl) ⟨1665350, by rfl⟩ : syracuseStep 2220467 = 3330701) B3330701
theorem B4211149 : Blo 1478559 4211149 := bstep (se 3 (by rfl) ⟨789590, by rfl⟩ : syracuseStep 4211149 = 1579181) B1579181
theorem B2220497 : Blo 1478559 2220497 := bstep (se 2 (by rfl) ⟨832686, by rfl⟩ : syracuseStep 2220497 = 1665373) B1665373
theorem B2220515 : Blo 1478559 2220515 := bstep (se 1 (by rfl) ⟨1665386, by rfl⟩ : syracuseStep 2220515 = 3330773) B3330773
theorem B8430065 : Blo 1478559 8430065 := bstep (se 2 (by rfl) ⟨3161274, by rfl⟩ : syracuseStep 8430065 = 6322549) B6322549
theorem B2220545 : Blo 1478559 2220545 := bstep (se 2 (by rfl) ⟨832704, by rfl⟩ : syracuseStep 2220545 = 1665409) B1665409
theorem B2810371 : Blo 1478559 2810371 := bstep (se 1 (by rfl) ⟨2107778, by rfl⟩ : syracuseStep 2810371 = 4215557) B4215557
theorem B3555857 : Blo 1478559 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B2220563 : Blo 1478559 2220563 := bstep (se 1 (by rfl) ⟨1665422, by rfl⟩ : syracuseStep 2220563 = 3330845) B3330845
theorem B2220593 : Blo 1478559 2220593 := bstep (se 2 (by rfl) ⟨832722, by rfl⟩ : syracuseStep 2220593 = 1665445) B1665445
theorem B1663555 : Blo 1478559 1663555 := bstep (se 1 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 1663555 = 2495333) B2495333
theorem B2220611 : Blo 1478559 2220611 := bstep (se 1 (by rfl) ⟨1665458, by rfl⟩ : syracuseStep 2220611 = 3330917) B3330917
theorem B2105939 : Blo 1478559 2105939 := bstep (se 1 (by rfl) ⟨1579454, by rfl⟩ : syracuseStep 2105939 = 3158909) B3158909
theorem B2220641 : Blo 1478559 2220641 := bstep (se 2 (by rfl) ⟨832740, by rfl⟩ : syracuseStep 2220641 = 1665481) B1665481
theorem B1778275 : Blo 1478559 1778275 := bstep (se 1 (by rfl) ⟨1333706, by rfl⟩ : syracuseStep 1778275 = 2667413) B2667413
theorem B8422001 : Blo 1478559 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B2220659 : Blo 1478559 2220659 := bstep (se 1 (by rfl) ⟨1665494, by rfl⟩ : syracuseStep 2220659 = 3330989) B3330989
theorem B2220689 : Blo 1478559 2220689 := bstep (se 2 (by rfl) ⟨832758, by rfl⟩ : syracuseStep 2220689 = 1665517) B1665517
theorem B2810531 : Blo 1478559 2810531 := bstep (se 1 (by rfl) ⟨2107898, by rfl⟩ : syracuseStep 2810531 = 4215797) B4215797
theorem B1688227 : Blo 1478559 1688227 := bstep (se 1 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 1688227 = 2532341) B2532341
theorem B2220707 : Blo 1478559 2220707 := bstep (se 1 (by rfl) ⟨1665530, by rfl⟩ : syracuseStep 2220707 = 3331061) B3331061
theorem B2220737 : Blo 1478559 2220737 := bstep (se 2 (by rfl) ⟨832776, by rfl⟩ : syracuseStep 2220737 = 1665553) B1665553
theorem B1802947 : Blo 1478559 1802947 := bstep (se 1 (by rfl) ⟨1352210, by rfl⟩ : syracuseStep 1802947 = 2704421) B2704421
theorem B9478853 : Blo 1478559 9478853 := bstep (se 4 (by rfl) ⟨888642, by rfl⟩ : syracuseStep 9478853 = 1777285) B1777285
theorem B1663699 : Blo 1478559 1663699 := bstep (se 1 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 1663699 = 2495549) B2495549
theorem B2220755 : Blo 1478559 2220755 := bstep (se 1 (by rfl) ⟨1665566, by rfl⟩ : syracuseStep 2220755 = 3331133) B3331133
theorem B2220785 : Blo 1478559 2220785 := bstep (se 2 (by rfl) ⟨832794, by rfl⟩ : syracuseStep 2220785 = 1665589) B1665589
theorem B2220803 : Blo 1478559 2220803 := bstep (se 1 (by rfl) ⟨1665602, by rfl⟩ : syracuseStep 2220803 = 3331205) B3331205
theorem B2220833 : Blo 1478559 2220833 := bstep (se 2 (by rfl) ⟨832812, by rfl⟩ : syracuseStep 2220833 = 1665625) B1665625
theorem B1999651 : Blo 1478559 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B1778467 : Blo 1478559 1778467 := bstep (se 1 (by rfl) ⟨1333850, by rfl⟩ : syracuseStep 1778467 = 2667701) B2667701
theorem B5620529 : Blo 1478559 5620529 := bstep (se 2 (by rfl) ⟨2107698, by rfl⟩ : syracuseStep 5620529 = 4215397) B4215397
theorem B1663843 : Blo 1478559 1663843 := bstep (se 1 (by rfl) ⟨1247882, by rfl⟩ : syracuseStep 1663843 = 2495765) B2495765
theorem B7111601 : Blo 1478559 7111601 := bstep (se 2 (by rfl) ⟨2666850, by rfl⟩ : syracuseStep 7111601 = 5333701) B5333701
theorem B12805091 : Blo 1478559 12805091 := bstep (se 1 (by rfl) ⟨9603818, by rfl⟩ : syracuseStep 12805091 = 19207637) B19207637
theorem B25617379 : Blo 1478559 25617379 := bstep (se 1 (by rfl) ⟨19213034, by rfl⟩ : syracuseStep 25617379 = 38426069) B38426069
theorem B1663987 : Blo 1478559 1663987 := bstep (se 1 (by rfl) ⟨1247990, by rfl⟩ : syracuseStep 1663987 = 2495981) B2495981
theorem B3326993 : Blo 1478559 3326993 := bstep (se 2 (by rfl) ⟨1247622, by rfl⟩ : syracuseStep 3326993 = 2495245) B2495245
theorem B3327011 : Blo 1478559 3327011 := bstep (se 1 (by rfl) ⟨2495258, by rfl⟩ : syracuseStep 3327011 = 4990517) B4990517
theorem B3376163 : Blo 1478559 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B7488611 : Blo 1478559 7488611 := bstep (se 1 (by rfl) ⟨5616458, by rfl⟩ : syracuseStep 7488611 = 11232917) B11232917
theorem B1664131 : Blo 1478559 1664131 := bstep (se 1 (by rfl) ⟨1248098, by rfl⟩ : syracuseStep 1664131 = 2496197) B2496197
theorem B3744913 : Blo 1478559 3744913 := bstep (se 2 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 3744913 = 2808685) B2808685
theorem B2106577 : Blo 1478559 2106577 := bstep (se 2 (by rfl) ⟨789966, by rfl⟩ : syracuseStep 2106577 = 1579933) B1579933
theorem B4990193 : Blo 1478559 4990193 := bstep (se 2 (by rfl) ⟨1871322, by rfl⟩ : syracuseStep 4990193 = 3742645) B3742645
theorem B1664275 : Blo 1478559 1664275 := bstep (se 1 (by rfl) ⟨1248206, by rfl⟩ : syracuseStep 1664275 = 2496413) B2496413
theorem B3327281 : Blo 1478559 3327281 := bstep (se 2 (by rfl) ⟨1247730, by rfl⟩ : syracuseStep 3327281 = 2495461) B2495461
theorem B3327299 : Blo 1478559 3327299 := bstep (se 1 (by rfl) ⟨2495474, by rfl⟩ : syracuseStep 3327299 = 4990949) B4990949
theorem B2368931 : Blo 1478559 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B1664419 : Blo 1478559 1664419 := bstep (se 1 (by rfl) ⟨1248314, by rfl⟩ : syracuseStep 1664419 = 2496629) B2496629
theorem B3745187 : Blo 1478559 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B5621197 : Blo 1478559 5621197 := bstep (se 3 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 5621197 = 2107949) B2107949
theorem B16844273 : Blo 1478559 16844273 := bstep (se 2 (by rfl) ⟨6316602, by rfl⟩ : syracuseStep 16844273 = 12633205) B12633205
theorem B10118641 : Blo 1478559 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B2369009 : Blo 1478559 2369009 := bstep (se 2 (by rfl) ⟨888378, by rfl⟩ : syracuseStep 2369009 = 1776757) B1776757
theorem B2106913 : Blo 1478559 2106913 := bstep (se 2 (by rfl) ⟨790092, by rfl⟩ : syracuseStep 2106913 = 1580185) B1580185
theorem B3900977 : Blo 1478559 3900977 := bstep (se 2 (by rfl) ⟨1462866, by rfl⟩ : syracuseStep 3900977 = 2925733) B2925733
theorem B1664563 : Blo 1478559 1664563 := bstep (se 1 (by rfl) ⟨1248422, by rfl⟩ : syracuseStep 1664563 = 2496845) B2496845
theorem B3327569 : Blo 1478559 3327569 := bstep (se 2 (by rfl) ⟨1247838, by rfl⟩ : syracuseStep 3327569 = 2495677) B2495677
theorem B3327587 : Blo 1478559 3327587 := bstep (se 1 (by rfl) ⟨2495690, by rfl⟩ : syracuseStep 3327587 = 4991381) B4991381
theorem B3745379 : Blo 1478559 3745379 := bstep (se 1 (by rfl) ⟨2809034, by rfl⟩ : syracuseStep 3745379 = 5618069) B5618069
theorem B1664707 : Blo 1478559 1664707 := bstep (se 1 (by rfl) ⟨1248530, by rfl⟩ : syracuseStep 1664707 = 2497061) B2497061
theorem B25290467 : Blo 1478559 25290467 := bstep (se 1 (by rfl) ⟨18967850, by rfl⟩ : syracuseStep 25290467 = 37935701) B37935701
theorem B4990733 : Blo 1478559 4990733 := bstep (se 3 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 4990733 = 1871525) B1871525
theorem B2000657 : Blo 1478559 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B7997219 : Blo 1478559 7997219 := bstep (se 1 (by rfl) ⟨5997914, by rfl⟩ : syracuseStep 7997219 = 11995829) B11995829
theorem B4990787 : Blo 1478559 4990787 := bstep (se 1 (by rfl) ⟨3743090, by rfl⟩ : syracuseStep 4990787 = 7486181) B7486181
theorem B1664851 : Blo 1478559 1664851 := bstep (se 1 (by rfl) ⟨1248638, by rfl⟩ : syracuseStep 1664851 = 2497277) B2497277
theorem B3327857 : Blo 1478559 3327857 := bstep (se 2 (by rfl) ⟨1247946, by rfl⟩ : syracuseStep 3327857 = 2495893) B2495893
theorem B2369393 : Blo 1478559 2369393 := bstep (se 2 (by rfl) ⟨888522, by rfl⟩ : syracuseStep 2369393 = 1777045) B1777045
theorem B3327875 : Blo 1478559 3327875 := bstep (se 1 (by rfl) ⟨2495906, by rfl⟩ : syracuseStep 3327875 = 4991813) B4991813
theorem B7489421 : Blo 1478559 7489421 := bstep (se 3 (by rfl) ⟨1404266, by rfl⟩ : syracuseStep 7489421 = 2808533) B2808533
theorem B8431523 : Blo 1478559 8431523 := bstep (se 1 (by rfl) ⟨6323642, by rfl⟩ : syracuseStep 8431523 = 12647285) B12647285
theorem B1664995 : Blo 1478559 1664995 := bstep (se 1 (by rfl) ⟨1248746, by rfl⟩ : syracuseStep 1664995 = 2497493) B2497493
theorem B2369521 : Blo 1478559 2369521 := bstep (se 2 (by rfl) ⟨888570, by rfl⟩ : syracuseStep 2369521 = 1777141) B1777141
theorem B2566129 : Blo 1478559 2566129 := bstep (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) B1924597
theorem B7112717 : Blo 1478559 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B8423459 : Blo 1478559 8423459 := bstep (se 1 (by rfl) ⟨6317594, by rfl⟩ : syracuseStep 8423459 = 12635189) B12635189
theorem B2598961 : Blo 1478559 2598961 := bstep (se 2 (by rfl) ⟨974610, by rfl⟩ : syracuseStep 2598961 = 1949221) B1949221
theorem B4991057 : Blo 1478559 4991057 := bstep (se 2 (by rfl) ⟨1871646, by rfl⟩ : syracuseStep 4991057 = 3743293) B3743293
theorem B4737133 : Blo 1478559 4737133 := bstep (se 3 (by rfl) ⟨888212, by rfl⟩ : syracuseStep 4737133 = 1776425) B1776425
theorem B2107505 : Blo 1478559 2107505 := bstep (se 2 (by rfl) ⟨790314, by rfl⟩ : syracuseStep 2107505 = 1580629) B1580629
theorem B1665139 : Blo 1478559 1665139 := bstep (se 1 (by rfl) ⟨1248854, by rfl⟩ : syracuseStep 1665139 = 2497709) B2497709
theorem B3328145 : Blo 1478559 3328145 := bstep (se 2 (by rfl) ⟨1248054, by rfl⟩ : syracuseStep 3328145 = 2496109) B2496109
theorem B4212881 : Blo 1478559 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B3328163 : Blo 1478559 3328163 := bstep (se 1 (by rfl) ⟨2496122, by rfl⟩ : syracuseStep 3328163 = 4992245) B4992245
theorem B4737197 : Blo 1478559 4737197 := bstep (se 3 (by rfl) ⟨888224, by rfl⟩ : syracuseStep 4737197 = 1776449) B1776449
theorem B1665283 : Blo 1478559 1665283 := bstep (se 1 (by rfl) ⟨1248962, by rfl⟩ : syracuseStep 1665283 = 2497925) B2497925
theorem B4213073 : Blo 1478559 4213073 := bstep (se 2 (by rfl) ⟨1579902, by rfl⟩ : syracuseStep 4213073 = 3159805) B3159805
theorem B6318449 : Blo 1478559 6318449 := bstep (se 2 (by rfl) ⟨2369418, by rfl⟩ : syracuseStep 6318449 = 4738837) B4738837
theorem B1665427 : Blo 1478559 1665427 := bstep (se 1 (by rfl) ⟨1249070, by rfl⟩ : syracuseStep 1665427 = 2498141) B2498141
theorem B3328433 : Blo 1478559 3328433 := bstep (se 2 (by rfl) ⟨1248162, by rfl⟩ : syracuseStep 3328433 = 2496325) B2496325
theorem B3328451 : Blo 1478559 3328451 := bstep (se 1 (by rfl) ⟨2496338, by rfl⟩ : syracuseStep 3328451 = 4992677) B4992677
theorem B4499921 : Blo 1478559 4499921 := bstep (se 2 (by rfl) ⟨1687470, by rfl⟩ : syracuseStep 4499921 = 3374941) B3374941
theorem B3746321 : Blo 1478559 3746321 := bstep (se 2 (by rfl) ⟨1404870, by rfl⟩ : syracuseStep 3746321 = 2809741) B2809741
theorem B1665571 : Blo 1478559 1665571 := bstep (se 1 (by rfl) ⟨1249178, by rfl⟩ : syracuseStep 1665571 = 2498357) B2498357
theorem B3746371 : Blo 1478559 3746371 := bstep (se 1 (by rfl) ⟨2809778, by rfl⟩ : syracuseStep 3746371 = 5619557) B5619557
theorem B4991597 : Blo 1478559 4991597 := bstep (se 3 (by rfl) ⟨935924, by rfl⟩ : syracuseStep 4991597 = 1871849) B1871849
theorem B7998065 : Blo 1478559 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B2108035 : Blo 1478559 2108035 := bstep (se 1 (by rfl) ⟨1581026, by rfl⟩ : syracuseStep 2108035 = 3162053) B3162053
theorem B3418769 : Blo 1478559 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B4991651 : Blo 1478559 4991651 := bstep (se 1 (by rfl) ⟨3743738, by rfl⟩ : syracuseStep 4991651 = 7487477) B7487477
theorem B3328721 : Blo 1478559 3328721 := bstep (se 2 (by rfl) ⟨1248270, by rfl⟩ : syracuseStep 3328721 = 2496541) B2496541
theorem B3746513 : Blo 1478559 3746513 := bstep (se 2 (by rfl) ⟨1404942, by rfl⟩ : syracuseStep 3746513 = 2809885) B2809885
theorem B3328739 : Blo 1478559 3328739 := bstep (se 1 (by rfl) ⟨2496554, by rfl⟩ : syracuseStep 3328739 = 4993109) B4993109
theorem B5999345 : Blo 1478559 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B2026387 : Blo 1478559 2026387 := bstep (se 1 (by rfl) ⟨1519790, by rfl⟩ : syracuseStep 2026387 = 3039581) B3039581
theorem B4991921 : Blo 1478559 4991921 := bstep (se 2 (by rfl) ⟨1871970, by rfl⟩ : syracuseStep 4991921 = 3743941) B3743941
theorem B2280401 : Blo 1478559 2280401 := bstep (se 2 (by rfl) ⟨855150, by rfl⟩ : syracuseStep 2280401 = 1710301) B1710301
theorem B18959345 : Blo 1478559 18959345 := bstep (se 2 (by rfl) ⟨7109754, by rfl⟩ : syracuseStep 18959345 = 14219509) B14219509
theorem B3329009 : Blo 1478559 3329009 := bstep (se 2 (by rfl) ⟨1248378, by rfl⟩ : syracuseStep 3329009 = 2496757) B2496757
theorem B3329027 : Blo 1478559 3329027 := bstep (se 1 (by rfl) ⟨2496770, by rfl⟩ : syracuseStep 3329027 = 4993541) B4993541
theorem B11242637 : Blo 1478559 11242637 := bstep (se 3 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 11242637 = 4215989) B4215989
theorem B3329297 : Blo 1478559 3329297 := bstep (se 2 (by rfl) ⟨1248486, by rfl⟩ : syracuseStep 3329297 = 2496973) B2496973
theorem B3329315 : Blo 1478559 3329315 := bstep (se 1 (by rfl) ⟨2496986, by rfl⟩ : syracuseStep 3329315 = 4993973) B4993973
theorem B4214065 : Blo 1478559 4214065 := bstep (se 2 (by rfl) ⟨1580274, by rfl⟩ : syracuseStep 4214065 = 3160549) B3160549
theorem B7114061 : Blo 1478559 7114061 := bstep (se 3 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 7114061 = 2667773) B2667773
theorem B16002485 : Blo 1478559 16002485 := bstep (se 5 (by rfl) ⟨750116, by rfl⟩ : syracuseStep 16002485 = 1500233) B1500233
theorem B4992461 : Blo 1478559 4992461 := bstep (se 3 (by rfl) ⟨936086, by rfl⟩ : syracuseStep 4992461 = 1872173) B1872173
theorem B2371027 : Blo 1478559 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B1871363 : Blo 1478559 1871363 := bstep (se 1 (by rfl) ⟨1403522, by rfl⟩ : syracuseStep 1871363 = 2807045) B2807045
theorem B4992515 : Blo 1478559 4992515 := bstep (se 1 (by rfl) ⟨3744386, by rfl⟩ : syracuseStep 4992515 = 7488773) B7488773
theorem B5615153 : Blo 1478559 5615153 := bstep (se 2 (by rfl) ⟨2105682, by rfl⟩ : syracuseStep 5615153 = 4211365) B4211365
theorem B3329585 : Blo 1478559 3329585 := bstep (se 2 (by rfl) ⟨1248594, by rfl⟩ : syracuseStep 3329585 = 2497189) B2497189
theorem B3329603 : Blo 1478559 3329603 := bstep (se 1 (by rfl) ⟨2497202, by rfl⟩ : syracuseStep 3329603 = 4994405) B4994405
theorem B4214339 : Blo 1478559 4214339 := bstep (se 1 (by rfl) ⟨3160754, by rfl⟩ : syracuseStep 4214339 = 6321509) B6321509
theorem B3796625 : Blo 1478559 3796625 := bstep (se 2 (by rfl) ⟨1423734, by rfl⟩ : syracuseStep 3796625 = 2847469) B2847469
theorem B3747505 : Blo 1478559 3747505 := bstep (se 2 (by rfl) ⟨1405314, by rfl⟩ : syracuseStep 3747505 = 2810629) B2810629
theorem B2281139 : Blo 1478559 2281139 := bstep (se 1 (by rfl) ⟨1710854, by rfl⟩ : syracuseStep 2281139 = 3421709) B3421709
theorem B9875141 : Blo 1478559 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B10669765 : Blo 1478559 10669765 := bstep (se 4 (by rfl) ⟨1000290, by rfl⟩ : syracuseStep 10669765 = 2000581) B2000581
theorem B4214531 : Blo 1478559 4214531 := bstep (se 1 (by rfl) ⟨3160898, by rfl⟩ : syracuseStep 4214531 = 6321797) B6321797
theorem B4992785 : Blo 1478559 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B3157841 : Blo 1478559 3157841 := bstep (se 2 (by rfl) ⟨1184190, by rfl⟩ : syracuseStep 3157841 = 2368381) B2368381
theorem B3329873 : Blo 1478559 3329873 := bstep (se 2 (by rfl) ⟨1248702, by rfl⟩ : syracuseStep 3329873 = 2497405) B2497405
theorem B3329891 : Blo 1478559 3329891 := bstep (se 1 (by rfl) ⟨2497418, by rfl⟩ : syracuseStep 3329891 = 4994837) B4994837
theorem B1478563 : Blo 1478559 1478563 := bstep (se 1 (by rfl) ⟨1108922, by rfl⟩ : syracuseStep 1478563 = 2217845) B2217845
theorem B4738979 : Blo 1478559 4738979 := bstep (se 1 (by rfl) ⟨3554234, by rfl⟩ : syracuseStep 4738979 = 7108469) B7108469
theorem B1478579 : Blo 1478559 1478579 := bstep (se 1 (by rfl) ⟨1108934, by rfl⟩ : syracuseStep 1478579 = 2217869) B2217869
theorem B1478595 : Blo 1478559 1478595 := bstep (se 1 (by rfl) ⟨1108946, by rfl⟩ : syracuseStep 1478595 = 2217893) B2217893
theorem B1478611 : Blo 1478559 1478611 := bstep (se 1 (by rfl) ⟨1108958, by rfl⟩ : syracuseStep 1478611 = 2217917) B2217917
theorem B1478627 : Blo 1478559 1478627 := bstep (se 1 (by rfl) ⟨1108970, by rfl⟩ : syracuseStep 1478627 = 2217941) B2217941
theorem B1478643 : Blo 1478559 1478643 := bstep (se 1 (by rfl) ⟨1108982, by rfl⟩ : syracuseStep 1478643 = 2217965) B2217965
theorem B1478659 : Blo 1478559 1478659 := bstep (se 1 (by rfl) ⟨1108994, by rfl⟩ : syracuseStep 1478659 = 2217989) B2217989
theorem B1478675 : Blo 1478559 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B1478691 : Blo 1478559 1478691 := bstep (se 1 (by rfl) ⟨1109018, by rfl⟩ : syracuseStep 1478691 = 2218037) B2218037
theorem B1478707 : Blo 1478559 1478707 := bstep (se 1 (by rfl) ⟨1109030, by rfl⟩ : syracuseStep 1478707 = 2218061) B2218061
theorem B1478723 : Blo 1478559 1478723 := bstep (se 1 (by rfl) ⟨1109042, by rfl⟩ : syracuseStep 1478723 = 2218085) B2218085
theorem B1478739 : Blo 1478559 1478739 := bstep (se 1 (by rfl) ⟨1109054, by rfl⟩ : syracuseStep 1478739 = 2218109) B2218109
theorem B1478755 : Blo 1478559 1478755 := bstep (se 1 (by rfl) ⟨1109066, by rfl⟩ : syracuseStep 1478755 = 2218133) B2218133
theorem B3330161 : Blo 1478559 3330161 := bstep (se 2 (by rfl) ⟨1248810, by rfl⟩ : syracuseStep 3330161 = 2497621) B2497621
theorem B1478771 : Blo 1478559 1478771 := bstep (se 1 (by rfl) ⟨1109078, by rfl⟩ : syracuseStep 1478771 = 2218157) B2218157
theorem B1478787 : Blo 1478559 1478787 := bstep (se 1 (by rfl) ⟨1109090, by rfl⟩ : syracuseStep 1478787 = 2218181) B2218181
theorem B3330179 : Blo 1478559 3330179 := bstep (se 1 (by rfl) ⟨2497634, by rfl⟩ : syracuseStep 3330179 = 4995269) B4995269
theorem B1478803 : Blo 1478559 1478803 := bstep (se 1 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 1478803 = 2218205) B2218205
theorem B1478819 : Blo 1478559 1478819 := bstep (se 1 (by rfl) ⟨1109114, by rfl⟩ : syracuseStep 1478819 = 2218229) B2218229
theorem B1478835 : Blo 1478559 1478835 := bstep (se 1 (by rfl) ⟨1109126, by rfl⟩ : syracuseStep 1478835 = 2218253) B2218253
theorem B1478851 : Blo 1478559 1478851 := bstep (se 1 (by rfl) ⟨1109138, by rfl⟩ : syracuseStep 1478851 = 2218277) B2218277
theorem B1872067 : Blo 1478559 1872067 := bstep (se 1 (by rfl) ⟨1404050, by rfl⟩ : syracuseStep 1872067 = 2808101) B2808101
theorem B1478867 : Blo 1478559 1478867 := bstep (se 1 (by rfl) ⟨1109150, by rfl⟩ : syracuseStep 1478867 = 2218301) B2218301
theorem B1478883 : Blo 1478559 1478883 := bstep (se 1 (by rfl) ⟨1109162, by rfl⟩ : syracuseStep 1478883 = 2218325) B2218325
theorem B9482467 : Blo 1478559 9482467 := bstep (se 1 (by rfl) ⟨7111850, by rfl⟩ : syracuseStep 9482467 = 14223701) B14223701
theorem B1478899 : Blo 1478559 1478899 := bstep (se 1 (by rfl) ⟨1109174, by rfl⟩ : syracuseStep 1478899 = 2218349) B2218349
theorem B1478915 : Blo 1478559 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B1478931 : Blo 1478559 1478931 := bstep (se 1 (by rfl) ⟨1109198, by rfl⟩ : syracuseStep 1478931 = 2218397) B2218397
theorem B1478947 : Blo 1478559 1478947 := bstep (se 1 (by rfl) ⟨1109210, by rfl⟩ : syracuseStep 1478947 = 2218421) B2218421
theorem B1872163 : Blo 1478559 1872163 := bstep (se 1 (by rfl) ⟨1404122, by rfl⟩ : syracuseStep 1872163 = 2808245) B2808245
theorem B4993325 : Blo 1478559 4993325 := bstep (se 3 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 4993325 = 1872497) B1872497
theorem B9605425 : Blo 1478559 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B1478963 : Blo 1478559 1478963 := bstep (se 1 (by rfl) ⟨1109222, by rfl⟩ : syracuseStep 1478963 = 2218445) B2218445
theorem B1478979 : Blo 1478559 1478979 := bstep (se 1 (by rfl) ⟨1109234, by rfl⟩ : syracuseStep 1478979 = 2218469) B2218469
theorem B8335685 : Blo 1478559 8335685 := bstep (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) B1562941
theorem B1478995 : Blo 1478559 1478995 := bstep (se 1 (by rfl) ⟨1109246, by rfl⟩ : syracuseStep 1478995 = 2218493) B2218493
theorem B1479011 : Blo 1478559 1479011 := bstep (se 1 (by rfl) ⟨1109258, by rfl⟩ : syracuseStep 1479011 = 2218517) B2218517
theorem B4993379 : Blo 1478559 4993379 := bstep (se 1 (by rfl) ⟨3745034, by rfl⟩ : syracuseStep 4993379 = 7490069) B7490069
theorem B1479027 : Blo 1478559 1479027 := bstep (se 1 (by rfl) ⟨1109270, by rfl⟩ : syracuseStep 1479027 = 2218541) B2218541
theorem B1479043 : Blo 1478559 1479043 := bstep (se 1 (by rfl) ⟨1109282, by rfl⟩ : syracuseStep 1479043 = 2218565) B2218565
theorem B3330449 : Blo 1478559 3330449 := bstep (se 2 (by rfl) ⟨1248918, by rfl⟩ : syracuseStep 3330449 = 2497837) B2497837
theorem B1479059 : Blo 1478559 1479059 := bstep (se 1 (by rfl) ⟨1109294, by rfl⟩ : syracuseStep 1479059 = 2218589) B2218589
theorem B1479075 : Blo 1478559 1479075 := bstep (se 1 (by rfl) ⟨1109306, by rfl⟩ : syracuseStep 1479075 = 2218613) B2218613
theorem B3330467 : Blo 1478559 3330467 := bstep (se 1 (by rfl) ⟨2497850, by rfl⟩ : syracuseStep 3330467 = 4995701) B4995701
theorem B1479091 : Blo 1478559 1479091 := bstep (se 1 (by rfl) ⟨1109318, by rfl⟩ : syracuseStep 1479091 = 2218637) B2218637
theorem B1479107 : Blo 1478559 1479107 := bstep (se 1 (by rfl) ⟨1109330, by rfl⟩ : syracuseStep 1479107 = 2218661) B2218661
theorem B1479123 : Blo 1478559 1479123 := bstep (se 1 (by rfl) ⟨1109342, by rfl⟩ : syracuseStep 1479123 = 2218685) B2218685
theorem B1479139 : Blo 1478559 1479139 := bstep (se 1 (by rfl) ⟨1109354, by rfl⟩ : syracuseStep 1479139 = 2218709) B2218709
theorem B1479155 : Blo 1478559 1479155 := bstep (se 1 (by rfl) ⟨1109366, by rfl⟩ : syracuseStep 1479155 = 2218733) B2218733
theorem B1479171 : Blo 1478559 1479171 := bstep (se 1 (by rfl) ⟨1109378, by rfl⟩ : syracuseStep 1479171 = 2218757) B2218757
theorem B1479187 : Blo 1478559 1479187 := bstep (se 1 (by rfl) ⟨1109390, by rfl⟩ : syracuseStep 1479187 = 2218781) B2218781
theorem B1479203 : Blo 1478559 1479203 := bstep (se 1 (by rfl) ⟨1109402, by rfl⟩ : syracuseStep 1479203 = 2218805) B2218805
theorem B4215341 : Blo 1478559 4215341 := bstep (se 3 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 4215341 = 1580753) B1580753
theorem B1479219 : Blo 1478559 1479219 := bstep (se 1 (by rfl) ⟨1109414, by rfl⟩ : syracuseStep 1479219 = 2218829) B2218829
theorem B2249267 : Blo 1478559 2249267 := bstep (se 1 (by rfl) ⟨1686950, by rfl⟩ : syracuseStep 2249267 = 3373901) B3373901
theorem B1479235 : Blo 1478559 1479235 := bstep (se 1 (by rfl) ⟨1109426, by rfl⟩ : syracuseStep 1479235 = 2218853) B2218853
theorem B8540741 : Blo 1478559 8540741 := bstep (se 4 (by rfl) ⟨800694, by rfl⟩ : syracuseStep 8540741 = 1601389) B1601389
theorem B1479251 : Blo 1478559 1479251 := bstep (se 1 (by rfl) ⟨1109438, by rfl⟩ : syracuseStep 1479251 = 2218877) B2218877
theorem B1479267 : Blo 1478559 1479267 := bstep (se 1 (by rfl) ⟨1109450, by rfl⟩ : syracuseStep 1479267 = 2218901) B2218901
theorem B4993649 : Blo 1478559 4993649 := bstep (se 2 (by rfl) ⟨1872618, by rfl⟩ : syracuseStep 4993649 = 3745237) B3745237
theorem B1479283 : Blo 1478559 1479283 := bstep (se 1 (by rfl) ⟨1109462, by rfl⟩ : syracuseStep 1479283 = 2218925) B2218925
theorem B1479299 : Blo 1478559 1479299 := bstep (se 1 (by rfl) ⟨1109474, by rfl⟩ : syracuseStep 1479299 = 2218949) B2218949
theorem B21320333 : Blo 1478559 21320333 := bstep (se 3 (by rfl) ⟨3997562, by rfl⟩ : syracuseStep 21320333 = 7995125) B7995125
theorem B1479315 : Blo 1478559 1479315 := bstep (se 1 (by rfl) ⟨1109486, by rfl⟩ : syracuseStep 1479315 = 2218973) B2218973
theorem B2495137 : Blo 1478559 2495137 := bstep (se 2 (by rfl) ⟨935676, by rfl⟩ : syracuseStep 2495137 = 1871353) B1871353
theorem B1479331 : Blo 1478559 1479331 := bstep (se 1 (by rfl) ⟨1109498, by rfl⟩ : syracuseStep 1479331 = 2218997) B2218997
theorem B3330737 : Blo 1478559 3330737 := bstep (se 2 (by rfl) ⟨1249026, by rfl⟩ : syracuseStep 3330737 = 2498053) B2498053
theorem B1479347 : Blo 1478559 1479347 := bstep (se 1 (by rfl) ⟨1109510, by rfl⟩ : syracuseStep 1479347 = 2219021) B2219021
theorem B2495171 : Blo 1478559 2495171 := bstep (se 1 (by rfl) ⟨1871378, by rfl⟩ : syracuseStep 2495171 = 3742757) B3742757
theorem B1479363 : Blo 1478559 1479363 := bstep (se 1 (by rfl) ⟨1109522, by rfl⟩ : syracuseStep 1479363 = 2219045) B2219045
theorem B3330755 : Blo 1478559 3330755 := bstep (se 1 (by rfl) ⟨2498066, by rfl⟩ : syracuseStep 3330755 = 4996133) B4996133
theorem B1479379 : Blo 1478559 1479379 := bstep (se 1 (by rfl) ⟨1109534, by rfl⟩ : syracuseStep 1479379 = 2219069) B2219069
theorem B1479395 : Blo 1478559 1479395 := bstep (se 1 (by rfl) ⟨1109546, by rfl⟩ : syracuseStep 1479395 = 2219093) B2219093
theorem B4215523 : Blo 1478559 4215523 := bstep (se 1 (by rfl) ⟨3161642, by rfl⟩ : syracuseStep 4215523 = 6323285) B6323285
theorem B7492337 : Blo 1478559 7492337 := bstep (se 2 (by rfl) ⟨2809626, by rfl⟩ : syracuseStep 7492337 = 5619253) B5619253
theorem B1479411 : Blo 1478559 1479411 := bstep (se 1 (by rfl) ⟨1109558, by rfl⟩ : syracuseStep 1479411 = 2219117) B2219117
theorem B1479427 : Blo 1478559 1479427 := bstep (se 1 (by rfl) ⟨1109570, by rfl⟩ : syracuseStep 1479427 = 2219141) B2219141
theorem B6320909 : Blo 1478559 6320909 := bstep (se 3 (by rfl) ⟨1185170, by rfl⟩ : syracuseStep 6320909 = 2370341) B2370341
theorem B1479443 : Blo 1478559 1479443 := bstep (se 1 (by rfl) ⟨1109582, by rfl⟩ : syracuseStep 1479443 = 2219165) B2219165
theorem B1872659 : Blo 1478559 1872659 := bstep (se 1 (by rfl) ⟨1404494, by rfl⟩ : syracuseStep 1872659 = 2808989) B2808989
theorem B1479459 : Blo 1478559 1479459 := bstep (se 1 (by rfl) ⟨1109594, by rfl⟩ : syracuseStep 1479459 = 2219189) B2219189
theorem B1479475 : Blo 1478559 1479475 := bstep (se 1 (by rfl) ⟨1109606, by rfl⟩ : syracuseStep 1479475 = 2219213) B2219213
theorem B2495299 : Blo 1478559 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B1479491 : Blo 1478559 1479491 := bstep (se 1 (by rfl) ⟨1109618, by rfl⟩ : syracuseStep 1479491 = 2219237) B2219237
theorem B1479507 : Blo 1478559 1479507 := bstep (se 1 (by rfl) ⟨1109630, by rfl⟩ : syracuseStep 1479507 = 2219261) B2219261
theorem B1479523 : Blo 1478559 1479523 := bstep (se 1 (by rfl) ⟨1109642, by rfl⟩ : syracuseStep 1479523 = 2219285) B2219285
theorem B1479539 : Blo 1478559 1479539 := bstep (se 1 (by rfl) ⟨1109654, by rfl⟩ : syracuseStep 1479539 = 2219309) B2219309
theorem B1479555 : Blo 1478559 1479555 := bstep (se 1 (by rfl) ⟨1109666, by rfl⟩ : syracuseStep 1479555 = 2219333) B2219333
theorem B1479571 : Blo 1478559 1479571 := bstep (se 1 (by rfl) ⟨1109678, by rfl⟩ : syracuseStep 1479571 = 2219357) B2219357
theorem B1479587 : Blo 1478559 1479587 := bstep (se 1 (by rfl) ⟨1109690, by rfl⟩ : syracuseStep 1479587 = 2219381) B2219381
theorem B1479603 : Blo 1478559 1479603 := bstep (se 1 (by rfl) ⟨1109702, by rfl⟩ : syracuseStep 1479603 = 2219405) B2219405
theorem B1479619 : Blo 1478559 1479619 := bstep (se 1 (by rfl) ⟨1109714, by rfl⟩ : syracuseStep 1479619 = 2219429) B2219429
theorem B2495441 : Blo 1478559 2495441 := bstep (se 2 (by rfl) ⟨935790, by rfl⟩ : syracuseStep 2495441 = 1871581) B1871581
theorem B1479635 : Blo 1478559 1479635 := bstep (se 1 (by rfl) ⟨1109726, by rfl⟩ : syracuseStep 1479635 = 2219453) B2219453
theorem B3331025 : Blo 1478559 3331025 := bstep (se 2 (by rfl) ⟨1249134, by rfl⟩ : syracuseStep 3331025 = 2498269) B2498269
theorem B5616611 : Blo 1478559 5616611 := bstep (se 1 (by rfl) ⟨4212458, by rfl⟩ : syracuseStep 5616611 = 8424917) B8424917
theorem B1479651 : Blo 1478559 1479651 := bstep (se 1 (by rfl) ⟨1109738, by rfl⟩ : syracuseStep 1479651 = 2219477) B2219477
theorem B3331043 : Blo 1478559 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B1479667 : Blo 1478559 1479667 := bstep (se 1 (by rfl) ⟨1109750, by rfl⟩ : syracuseStep 1479667 = 2219501) B2219501
theorem B2135041 : Blo 1478559 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1479683 : Blo 1478559 1479683 := bstep (se 1 (by rfl) ⟨1109762, by rfl⟩ : syracuseStep 1479683 = 2219525) B2219525
theorem B1479699 : Blo 1478559 1479699 := bstep (se 1 (by rfl) ⟨1109774, by rfl⟩ : syracuseStep 1479699 = 2219549) B2219549
theorem B1479715 : Blo 1478559 1479715 := bstep (se 1 (by rfl) ⟨1109786, by rfl⟩ : syracuseStep 1479715 = 2219573) B2219573
theorem B1479731 : Blo 1478559 1479731 := bstep (se 1 (by rfl) ⟨1109798, by rfl⟩ : syracuseStep 1479731 = 2219597) B2219597
theorem B1479747 : Blo 1478559 1479747 := bstep (se 1 (by rfl) ⟨1109810, by rfl⟩ : syracuseStep 1479747 = 2219621) B2219621
theorem B2495569 : Blo 1478559 2495569 := bstep (se 2 (by rfl) ⟨935838, by rfl⟩ : syracuseStep 2495569 = 1871677) B1871677
theorem B1479763 : Blo 1478559 1479763 := bstep (se 1 (by rfl) ⟨1109822, by rfl⟩ : syracuseStep 1479763 = 2219645) B2219645
theorem B1479779 : Blo 1478559 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B2495603 : Blo 1478559 2495603 := bstep (se 1 (by rfl) ⟨1871702, by rfl⟩ : syracuseStep 2495603 = 3743405) B3743405
theorem B1479795 : Blo 1478559 1479795 := bstep (se 1 (by rfl) ⟨1109846, by rfl⟩ : syracuseStep 1479795 = 2219693) B2219693
theorem B1479811 : Blo 1478559 1479811 := bstep (se 1 (by rfl) ⟨1109858, by rfl⟩ : syracuseStep 1479811 = 2219717) B2219717
theorem B4994189 : Blo 1478559 4994189 := bstep (se 3 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 4994189 = 1872821) B1872821
theorem B4805777 : Blo 1478559 4805777 := bstep (se 2 (by rfl) ⟨1802166, by rfl⟩ : syracuseStep 4805777 = 3604333) B3604333
theorem B1479827 : Blo 1478559 1479827 := bstep (se 1 (by rfl) ⟨1109870, by rfl⟩ : syracuseStep 1479827 = 2219741) B2219741
theorem B1479843 : Blo 1478559 1479843 := bstep (se 1 (by rfl) ⟨1109882, by rfl⟩ : syracuseStep 1479843 = 2219765) B2219765
theorem B1479859 : Blo 1478559 1479859 := bstep (se 1 (by rfl) ⟨1109894, by rfl⟩ : syracuseStep 1479859 = 2219789) B2219789
theorem B4994243 : Blo 1478559 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B1479875 : Blo 1478559 1479875 := bstep (se 1 (by rfl) ⟨1109906, by rfl⟩ : syracuseStep 1479875 = 2219813) B2219813
theorem B8426693 : Blo 1478559 8426693 := bstep (se 4 (by rfl) ⟨790002, by rfl⟩ : syracuseStep 8426693 = 1580005) B1580005
theorem B4216013 : Blo 1478559 4216013 := bstep (se 3 (by rfl) ⟨790502, by rfl⟩ : syracuseStep 4216013 = 1581005) B1581005
theorem B1479891 : Blo 1478559 1479891 := bstep (se 1 (by rfl) ⟨1109918, by rfl⟩ : syracuseStep 1479891 = 2219837) B2219837
theorem B1479907 : Blo 1478559 1479907 := bstep (se 1 (by rfl) ⟨1109930, by rfl⟩ : syracuseStep 1479907 = 2219861) B2219861
theorem B2495731 : Blo 1478559 2495731 := bstep (se 1 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 2495731 = 3743597) B3743597
theorem B1479923 : Blo 1478559 1479923 := bstep (se 1 (by rfl) ⟨1109942, by rfl⟩ : syracuseStep 1479923 = 2219885) B2219885
theorem B1479939 : Blo 1478559 1479939 := bstep (se 1 (by rfl) ⟨1109954, by rfl⟩ : syracuseStep 1479939 = 2219909) B2219909
theorem B1479955 : Blo 1478559 1479955 := bstep (se 1 (by rfl) ⟨1109966, by rfl⟩ : syracuseStep 1479955 = 2219933) B2219933
theorem B2807075 : Blo 1478559 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B1479971 : Blo 1478559 1479971 := bstep (se 1 (by rfl) ⟨1109978, by rfl⟩ : syracuseStep 1479971 = 2219957) B2219957
theorem B1479987 : Blo 1478559 1479987 := bstep (se 1 (by rfl) ⟨1109990, by rfl⟩ : syracuseStep 1479987 = 2219981) B2219981
theorem B1480003 : Blo 1478559 1480003 := bstep (se 1 (by rfl) ⟨1110002, by rfl⟩ : syracuseStep 1480003 = 2220005) B2220005
theorem B1480019 : Blo 1478559 1480019 := bstep (se 1 (by rfl) ⟨1110014, by rfl⟩ : syracuseStep 1480019 = 2220029) B2220029
theorem B1480035 : Blo 1478559 1480035 := bstep (se 1 (by rfl) ⟨1110026, by rfl⟩ : syracuseStep 1480035 = 2220053) B2220053
theorem B1480051 : Blo 1478559 1480051 := bstep (se 1 (by rfl) ⟨1110038, by rfl⟩ : syracuseStep 1480051 = 2220077) B2220077
theorem B2495873 : Blo 1478559 2495873 := bstep (se 2 (by rfl) ⟨935952, by rfl⟩ : syracuseStep 2495873 = 1871905) B1871905
theorem B1480067 : Blo 1478559 1480067 := bstep (se 1 (by rfl) ⟨1110050, by rfl⟩ : syracuseStep 1480067 = 2220101) B2220101
theorem B1480083 : Blo 1478559 1480083 := bstep (se 1 (by rfl) ⟨1110062, by rfl⟩ : syracuseStep 1480083 = 2220125) B2220125
theorem B1480099 : Blo 1478559 1480099 := bstep (se 1 (by rfl) ⟨1110074, by rfl⟩ : syracuseStep 1480099 = 2220149) B2220149
theorem B1480115 : Blo 1478559 1480115 := bstep (se 1 (by rfl) ⟨1110086, by rfl⟩ : syracuseStep 1480115 = 2220173) B2220173
theorem B1480131 : Blo 1478559 1480131 := bstep (se 1 (by rfl) ⟨1110098, by rfl⟩ : syracuseStep 1480131 = 2220197) B2220197
theorem B11236805 : Blo 1478559 11236805 := bstep (se 4 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 11236805 = 2106901) B2106901
theorem B4994513 : Blo 1478559 4994513 := bstep (se 2 (by rfl) ⟨1872942, by rfl⟩ : syracuseStep 4994513 = 3745885) B3745885
theorem B1480147 : Blo 1478559 1480147 := bstep (se 1 (by rfl) ⟨1110110, by rfl⟩ : syracuseStep 1480147 = 2220221) B2220221
theorem B1873363 : Blo 1478559 1873363 := bstep (se 1 (by rfl) ⟨1405022, by rfl⟩ : syracuseStep 1873363 = 2810045) B2810045
theorem B5199331 : Blo 1478559 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B1480163 : Blo 1478559 1480163 := bstep (se 1 (by rfl) ⟨1110122, by rfl⟩ : syracuseStep 1480163 = 2220245) B2220245
theorem B1480179 : Blo 1478559 1480179 := bstep (se 1 (by rfl) ⟨1110134, by rfl⟩ : syracuseStep 1480179 = 2220269) B2220269
theorem B2496001 : Blo 1478559 2496001 := bstep (se 2 (by rfl) ⟨936000, by rfl⟩ : syracuseStep 2496001 = 1872001) B1872001
theorem B1480195 : Blo 1478559 1480195 := bstep (se 1 (by rfl) ⟨1110146, by rfl⟩ : syracuseStep 1480195 = 2220293) B2220293
theorem B1480211 : Blo 1478559 1480211 := bstep (se 1 (by rfl) ⟨1110158, by rfl⟩ : syracuseStep 1480211 = 2220317) B2220317
theorem B2496035 : Blo 1478559 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1480227 : Blo 1478559 1480227 := bstep (se 1 (by rfl) ⟨1110170, by rfl⟩ : syracuseStep 1480227 = 2220341) B2220341
theorem B1480243 : Blo 1478559 1480243 := bstep (se 1 (by rfl) ⟨1110182, by rfl⟩ : syracuseStep 1480243 = 2220365) B2220365
theorem B1873459 : Blo 1478559 1873459 := bstep (se 1 (by rfl) ⟨1405094, by rfl⟩ : syracuseStep 1873459 = 2810189) B2810189
theorem B1480259 : Blo 1478559 1480259 := bstep (se 1 (by rfl) ⟨1110194, by rfl⟩ : syracuseStep 1480259 = 2220389) B2220389
theorem B1480275 : Blo 1478559 1480275 := bstep (se 1 (by rfl) ⟨1110206, by rfl⟩ : syracuseStep 1480275 = 2220413) B2220413
theorem B1480291 : Blo 1478559 1480291 := bstep (se 1 (by rfl) ⟨1110218, by rfl⟩ : syracuseStep 1480291 = 2220437) B2220437
theorem B1480307 : Blo 1478559 1480307 := bstep (se 1 (by rfl) ⟨1110230, by rfl⟩ : syracuseStep 1480307 = 2220461) B2220461
theorem B1480323 : Blo 1478559 1480323 := bstep (se 1 (by rfl) ⟨1110242, by rfl⟩ : syracuseStep 1480323 = 2220485) B2220485
theorem B8992397 : Blo 1478559 8992397 := bstep (se 3 (by rfl) ⟨1686074, by rfl⟩ : syracuseStep 8992397 = 3372149) B3372149
theorem B8427149 : Blo 1478559 8427149 := bstep (se 3 (by rfl) ⟨1580090, by rfl⟩ : syracuseStep 8427149 = 3160181) B3160181
theorem B1480339 : Blo 1478559 1480339 := bstep (se 1 (by rfl) ⟨1110254, by rfl⟩ : syracuseStep 1480339 = 2220509) B2220509
theorem B2496163 : Blo 1478559 2496163 := bstep (se 1 (by rfl) ⟨1872122, by rfl⟩ : syracuseStep 2496163 = 3744245) B3744245
theorem B1480355 : Blo 1478559 1480355 := bstep (se 1 (by rfl) ⟨1110266, by rfl⟩ : syracuseStep 1480355 = 2220533) B2220533
theorem B1480371 : Blo 1478559 1480371 := bstep (se 1 (by rfl) ⟨1110278, by rfl⟩ : syracuseStep 1480371 = 2220557) B2220557
theorem B18953909 : Blo 1478559 18953909 := bstep (se 5 (by rfl) ⟨888464, by rfl⟩ : syracuseStep 18953909 = 1776929) B1776929
theorem B1480387 : Blo 1478559 1480387 := bstep (se 1 (by rfl) ⟨1110290, by rfl⟩ : syracuseStep 1480387 = 2220581) B2220581
theorem B1480403 : Blo 1478559 1480403 := bstep (se 1 (by rfl) ⟨1110302, by rfl⟩ : syracuseStep 1480403 = 2220605) B2220605
theorem B1480419 : Blo 1478559 1480419 := bstep (se 1 (by rfl) ⟨1110314, by rfl⟩ : syracuseStep 1480419 = 2220629) B2220629
theorem B1480435 : Blo 1478559 1480435 := bstep (se 1 (by rfl) ⟨1110326, by rfl⟩ : syracuseStep 1480435 = 2220653) B2220653
theorem B1480451 : Blo 1478559 1480451 := bstep (se 1 (by rfl) ⟨1110338, by rfl⟩ : syracuseStep 1480451 = 2220677) B2220677
theorem B1480467 : Blo 1478559 1480467 := bstep (se 1 (by rfl) ⟨1110350, by rfl⟩ : syracuseStep 1480467 = 2220701) B2220701
theorem B1480483 : Blo 1478559 1480483 := bstep (se 1 (by rfl) ⟨1110362, by rfl⟩ : syracuseStep 1480483 = 2220725) B2220725
theorem B2496305 : Blo 1478559 2496305 := bstep (se 2 (by rfl) ⟨936114, by rfl⟩ : syracuseStep 2496305 = 1872229) B1872229
theorem B1480499 : Blo 1478559 1480499 := bstep (se 1 (by rfl) ⟨1110374, by rfl⟩ : syracuseStep 1480499 = 2220749) B2220749
theorem B1480515 : Blo 1478559 1480515 := bstep (se 1 (by rfl) ⟨1110386, by rfl⟩ : syracuseStep 1480515 = 2220773) B2220773
theorem B1480531 : Blo 1478559 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B1480547 : Blo 1478559 1480547 := bstep (se 1 (by rfl) ⟨1110410, by rfl⟩ : syracuseStep 1480547 = 2220821) B2220821
theorem B2217857 : Blo 1478559 2217857 := bstep (se 2 (by rfl) ⟨831696, by rfl⟩ : syracuseStep 2217857 = 1663393) B1663393
theorem B10672013 : Blo 1478559 10672013 := bstep (se 3 (by rfl) ⟨2001002, by rfl⟩ : syracuseStep 10672013 = 4002005) B4002005
theorem B2217875 : Blo 1478559 2217875 := bstep (se 1 (by rfl) ⟨1663406, by rfl⟩ : syracuseStep 2217875 = 3326813) B3326813
theorem B2217905 : Blo 1478559 2217905 := bstep (se 2 (by rfl) ⟨831714, by rfl⟩ : syracuseStep 2217905 = 1663429) B1663429
theorem B2496433 : Blo 1478559 2496433 := bstep (se 2 (by rfl) ⟨936162, by rfl⟩ : syracuseStep 2496433 = 1872325) B1872325
theorem B2217923 : Blo 1478559 2217923 := bstep (se 1 (by rfl) ⟨1663442, by rfl⟩ : syracuseStep 2217923 = 3326885) B3326885
theorem B1898435 : Blo 1478559 1898435 := bstep (se 1 (by rfl) ⟨1423826, by rfl⟩ : syracuseStep 1898435 = 2847653) B2847653
theorem B11999173 : Blo 1478559 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B5617613 : Blo 1478559 5617613 := bstep (se 3 (by rfl) ⟨1053302, by rfl⟩ : syracuseStep 5617613 = 2106605) B2106605
theorem B2496467 : Blo 1478559 2496467 := bstep (se 1 (by rfl) ⟨1872350, by rfl⟩ : syracuseStep 2496467 = 3744701) B3744701
theorem B2217953 : Blo 1478559 2217953 := bstep (se 2 (by rfl) ⟨831732, by rfl⟩ : syracuseStep 2217953 = 1663465) B1663465
theorem B14227427 : Blo 1478559 14227427 := bstep (se 1 (by rfl) ⟨10670570, by rfl⟩ : syracuseStep 14227427 = 21341141) B21341141
theorem B4995053 : Blo 1478559 4995053 := bstep (se 3 (by rfl) ⟨936572, by rfl⟩ : syracuseStep 4995053 = 1873145) B1873145
theorem B2217971 : Blo 1478559 2217971 := bstep (se 1 (by rfl) ⟨1663478, by rfl⟩ : syracuseStep 2217971 = 3326957) B3326957
theorem B3553283 : Blo 1478559 3553283 := bstep (se 1 (by rfl) ⟨2664962, by rfl⟩ : syracuseStep 3553283 = 5329925) B5329925
theorem B2218001 : Blo 1478559 2218001 := bstep (se 2 (by rfl) ⟨831750, by rfl⟩ : syracuseStep 2218001 = 1663501) B1663501
theorem B2218019 : Blo 1478559 2218019 := bstep (se 1 (by rfl) ⟨1663514, by rfl⟩ : syracuseStep 2218019 = 3327029) B3327029
theorem B4995107 : Blo 1478559 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B2218049 : Blo 1478559 2218049 := bstep (se 2 (by rfl) ⟨831768, by rfl⟩ : syracuseStep 2218049 = 1663537) B1663537
theorem B2218067 : Blo 1478559 2218067 := bstep (se 1 (by rfl) ⟨1663550, by rfl⟩ : syracuseStep 2218067 = 3327101) B3327101
theorem B2496595 : Blo 1478559 2496595 := bstep (se 1 (by rfl) ⟨1872446, by rfl⟩ : syracuseStep 2496595 = 3744893) B3744893
theorem B2218097 : Blo 1478559 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B11384945 : Blo 1478559 11384945 := bstep (se 2 (by rfl) ⟨4269354, by rfl⟩ : syracuseStep 11384945 = 8538709) B8538709
theorem B2218115 : Blo 1478559 2218115 := bstep (se 1 (by rfl) ⟨1663586, by rfl⟩ : syracuseStep 2218115 = 3327173) B3327173
theorem B2218145 : Blo 1478559 2218145 := bstep (se 2 (by rfl) ⟨831804, by rfl⟩ : syracuseStep 2218145 = 1663609) B1663609
theorem B7493795 : Blo 1478559 7493795 := bstep (se 1 (by rfl) ⟨5620346, by rfl⟩ : syracuseStep 7493795 = 11240693) B11240693
theorem B2218163 : Blo 1478559 2218163 := bstep (se 1 (by rfl) ⟨1663622, by rfl⟩ : syracuseStep 2218163 = 3327245) B3327245
theorem B2218193 : Blo 1478559 2218193 := bstep (se 2 (by rfl) ⟨831822, by rfl⟩ : syracuseStep 2218193 = 1663645) B1663645
theorem B2808017 : Blo 1478559 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B1579219 : Blo 1478559 1579219 := bstep (se 1 (by rfl) ⟨1184414, by rfl⟩ : syracuseStep 1579219 = 2368829) B2368829
theorem B2496737 : Blo 1478559 2496737 := bstep (se 2 (by rfl) ⟨936276, by rfl⟩ : syracuseStep 2496737 = 1872553) B1872553
theorem B2218211 : Blo 1478559 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B15186161 : Blo 1478559 15186161 := bstep (se 2 (by rfl) ⟨5694810, by rfl⟩ : syracuseStep 15186161 = 11389621) B11389621
theorem B2218241 : Blo 1478559 2218241 := bstep (se 2 (by rfl) ⟨831840, by rfl⟩ : syracuseStep 2218241 = 1663681) B1663681
theorem B2218259 : Blo 1478559 2218259 := bstep (se 1 (by rfl) ⟨1663694, by rfl⟩ : syracuseStep 2218259 = 3327389) B3327389
theorem B3553571 : Blo 1478559 3553571 := bstep (se 1 (by rfl) ⟨2665178, by rfl⟩ : syracuseStep 3553571 = 5330357) B5330357
theorem B2218289 : Blo 1478559 2218289 := bstep (se 2 (by rfl) ⟨831858, by rfl⟩ : syracuseStep 2218289 = 1663717) B1663717
theorem B4995377 : Blo 1478559 4995377 := bstep (se 2 (by rfl) ⟨1873266, by rfl⟩ : syracuseStep 4995377 = 3746533) B3746533
theorem B6322481 : Blo 1478559 6322481 := bstep (se 2 (by rfl) ⟨2370930, by rfl⟩ : syracuseStep 6322481 = 4741861) B4741861
theorem B2218307 : Blo 1478559 2218307 := bstep (se 1 (by rfl) ⟨1663730, by rfl⟩ : syracuseStep 2218307 = 3327461) B3327461
theorem B2218337 : Blo 1478559 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B2496865 : Blo 1478559 2496865 := bstep (se 2 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 2496865 = 1872649) B1872649
theorem B2218355 : Blo 1478559 2218355 := bstep (se 1 (by rfl) ⟨1663766, by rfl⟩ : syracuseStep 2218355 = 3327533) B3327533
theorem B2496899 : Blo 1478559 2496899 := bstep (se 1 (by rfl) ⟨1872674, by rfl⟩ : syracuseStep 2496899 = 3745349) B3745349
theorem B2218385 : Blo 1478559 2218385 := bstep (se 2 (by rfl) ⟨831894, by rfl⟩ : syracuseStep 2218385 = 1663789) B1663789
theorem B2218403 : Blo 1478559 2218403 := bstep (se 1 (by rfl) ⟨1663802, by rfl⟩ : syracuseStep 2218403 = 3327605) B3327605
theorem B4741553 : Blo 1478559 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B2218433 : Blo 1478559 2218433 := bstep (se 2 (by rfl) ⟨831912, by rfl⟩ : syracuseStep 2218433 = 1663825) B1663825
theorem B2218451 : Blo 1478559 2218451 := bstep (se 1 (by rfl) ⟨1663838, by rfl⟩ : syracuseStep 2218451 = 3327677) B3327677
theorem B2218481 : Blo 1478559 2218481 := bstep (se 2 (by rfl) ⟨831930, by rfl⟩ : syracuseStep 2218481 = 1663861) B1663861
theorem B2218499 : Blo 1478559 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B2497027 : Blo 1478559 2497027 := bstep (se 1 (by rfl) ⟨1872770, by rfl⟩ : syracuseStep 2497027 = 3745541) B3745541
theorem B2218529 : Blo 1478559 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B3160625 : Blo 1478559 3160625 := bstep (se 2 (by rfl) ⟨1185234, by rfl⟩ : syracuseStep 3160625 = 2370469) B2370469
theorem B2218547 : Blo 1478559 2218547 := bstep (se 1 (by rfl) ⟨1663910, by rfl⟩ : syracuseStep 2218547 = 3327821) B3327821
theorem B2218577 : Blo 1478559 2218577 := bstep (se 2 (by rfl) ⟨831966, by rfl⟩ : syracuseStep 2218577 = 1663933) B1663933
theorem B2218595 : Blo 1478559 2218595 := bstep (se 1 (by rfl) ⟨1663946, by rfl⟩ : syracuseStep 2218595 = 3327893) B3327893
theorem B2218625 : Blo 1478559 2218625 := bstep (se 2 (by rfl) ⟨831984, by rfl⟩ : syracuseStep 2218625 = 1663969) B1663969
theorem B2497169 : Blo 1478559 2497169 := bstep (se 2 (by rfl) ⟨936438, by rfl⟩ : syracuseStep 2497169 = 1872877) B1872877
theorem B2218643 : Blo 1478559 2218643 := bstep (se 1 (by rfl) ⟨1663982, by rfl⟩ : syracuseStep 2218643 = 3327965) B3327965
theorem B2218673 : Blo 1478559 2218673 := bstep (se 2 (by rfl) ⟨832002, by rfl⟩ : syracuseStep 2218673 = 1664005) B1664005
theorem B2218691 : Blo 1478559 2218691 := bstep (se 1 (by rfl) ⟨1664018, by rfl⟩ : syracuseStep 2218691 = 3328037) B3328037
theorem B2218721 : Blo 1478559 2218721 := bstep (se 2 (by rfl) ⟨832020, by rfl⟩ : syracuseStep 2218721 = 1664041) B1664041
theorem B2218739 : Blo 1478559 2218739 := bstep (se 1 (by rfl) ⟨1664054, by rfl⟩ : syracuseStep 2218739 = 3328109) B3328109
theorem B2218769 : Blo 1478559 2218769 := bstep (se 2 (by rfl) ⟨832038, by rfl⟩ : syracuseStep 2218769 = 1664077) B1664077
theorem B2497297 : Blo 1478559 2497297 := bstep (se 2 (by rfl) ⟨936486, by rfl⟩ : syracuseStep 2497297 = 1872973) B1872973
theorem B2218787 : Blo 1478559 2218787 := bstep (se 1 (by rfl) ⟨1664090, by rfl⟩ : syracuseStep 2218787 = 3328181) B3328181
theorem B2530097 : Blo 1478559 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B2497331 : Blo 1478559 2497331 := bstep (se 1 (by rfl) ⟨1872998, by rfl⟩ : syracuseStep 2497331 = 3745997) B3745997
theorem B2218817 : Blo 1478559 2218817 := bstep (se 2 (by rfl) ⟨832056, by rfl⟩ : syracuseStep 2218817 = 1664113) B1664113
theorem B4995917 : Blo 1478559 4995917 := bstep (se 3 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 4995917 = 1873469) B1873469
theorem B2218835 : Blo 1478559 2218835 := bstep (se 1 (by rfl) ⟨1664126, by rfl⟩ : syracuseStep 2218835 = 3328253) B3328253
theorem B2218865 : Blo 1478559 2218865 := bstep (se 2 (by rfl) ⟨832074, by rfl⟩ : syracuseStep 2218865 = 1664149) B1664149
theorem B2218883 : Blo 1478559 2218883 := bstep (se 1 (by rfl) ⟨1664162, by rfl⟩ : syracuseStep 2218883 = 3328325) B3328325
theorem B4995971 : Blo 1478559 4995971 := bstep (se 1 (by rfl) ⟨3746978, by rfl⟩ : syracuseStep 4995971 = 7493957) B7493957
theorem B18963341 : Blo 1478559 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B2218913 : Blo 1478559 2218913 := bstep (se 2 (by rfl) ⟨832092, by rfl⟩ : syracuseStep 2218913 = 1664185) B1664185
theorem B2218931 : Blo 1478559 2218931 := bstep (se 1 (by rfl) ⟨1664198, by rfl⟩ : syracuseStep 2218931 = 3328397) B3328397
theorem B2497459 : Blo 1478559 2497459 := bstep (se 1 (by rfl) ⟨1873094, by rfl⟩ : syracuseStep 2497459 = 3746189) B3746189
theorem B9485261 : Blo 1478559 9485261 := bstep (se 3 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 9485261 = 3556973) B3556973
theorem B7494605 : Blo 1478559 7494605 := bstep (se 3 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 7494605 = 2810477) B2810477
theorem B2218961 : Blo 1478559 2218961 := bstep (se 2 (by rfl) ⟨832110, by rfl⟩ : syracuseStep 2218961 = 1664221) B1664221
theorem B2218979 : Blo 1478559 2218979 := bstep (se 1 (by rfl) ⟨1664234, by rfl⟩ : syracuseStep 2218979 = 3328469) B3328469
theorem B7109603 : Blo 1478559 7109603 := bstep (se 1 (by rfl) ⟨5332202, by rfl⟩ : syracuseStep 7109603 = 10664405) B10664405
theorem B2219009 : Blo 1478559 2219009 := bstep (se 2 (by rfl) ⟨832128, by rfl⟩ : syracuseStep 2219009 = 1664257) B1664257
theorem B3374083 : Blo 1478559 3374083 := bstep (se 1 (by rfl) ⟨2530562, by rfl⟩ : syracuseStep 3374083 = 5061125) B5061125
theorem B2219027 : Blo 1478559 2219027 := bstep (se 1 (by rfl) ⟨1664270, by rfl⟩ : syracuseStep 2219027 = 3328541) B3328541
theorem B2219057 : Blo 1478559 2219057 := bstep (se 2 (by rfl) ⟨832146, by rfl⟩ : syracuseStep 2219057 = 1664293) B1664293
theorem B3742787 : Blo 1478559 3742787 := bstep (se 1 (by rfl) ⟨2807090, by rfl⟩ : syracuseStep 3742787 = 5614181) B5614181
theorem B2219075 : Blo 1478559 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B2497601 : Blo 1478559 2497601 := bstep (se 2 (by rfl) ⟨936600, by rfl⟩ : syracuseStep 2497601 = 1873201) B1873201
theorem B2808913 : Blo 1478559 2808913 := bstep (se 2 (by rfl) ⟨1053342, by rfl⟩ : syracuseStep 2808913 = 2106685) B2106685
theorem B2219105 : Blo 1478559 2219105 := bstep (se 2 (by rfl) ⟨832164, by rfl⟩ : syracuseStep 2219105 = 1664329) B1664329
theorem B28425329 : Blo 1478559 28425329 := bstep (se 2 (by rfl) ⟨10659498, by rfl⟩ : syracuseStep 28425329 = 21318997) B21318997
theorem B3554417 : Blo 1478559 3554417 := bstep (se 2 (by rfl) ⟨1332906, by rfl⟩ : syracuseStep 3554417 = 2665813) B2665813
theorem B2219123 : Blo 1478559 2219123 := bstep (se 1 (by rfl) ⟨1664342, by rfl⟩ : syracuseStep 2219123 = 3328685) B3328685
theorem B2219153 : Blo 1478559 2219153 := bstep (se 2 (by rfl) ⟨832182, by rfl⟩ : syracuseStep 2219153 = 1664365) B1664365
theorem B4996241 : Blo 1478559 4996241 := bstep (se 2 (by rfl) ⟨1873590, by rfl⟩ : syracuseStep 4996241 = 3747181) B3747181
theorem B2219171 : Blo 1478559 2219171 := bstep (se 1 (by rfl) ⟨1664378, by rfl⟩ : syracuseStep 2219171 = 3328757) B3328757
theorem B2219201 : Blo 1478559 2219201 := bstep (se 2 (by rfl) ⟨832200, by rfl⟩ : syracuseStep 2219201 = 1664401) B1664401
theorem B2497729 : Blo 1478559 2497729 := bstep (se 2 (by rfl) ⟨936648, by rfl⟩ : syracuseStep 2497729 = 1873297) B1873297
theorem B3554513 : Blo 1478559 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B2219219 : Blo 1478559 2219219 := bstep (se 1 (by rfl) ⟨1664414, by rfl⟩ : syracuseStep 2219219 = 3328829) B3328829
theorem B2497763 : Blo 1478559 2497763 := bstep (se 1 (by rfl) ⟨1873322, by rfl⟩ : syracuseStep 2497763 = 3746645) B3746645
theorem B2219249 : Blo 1478559 2219249 := bstep (se 2 (by rfl) ⟨832218, by rfl⟩ : syracuseStep 2219249 = 1664437) B1664437
theorem B2809073 : Blo 1478559 2809073 := bstep (se 2 (by rfl) ⟨1053402, by rfl⟩ : syracuseStep 2809073 = 2106805) B2106805
theorem B2219267 : Blo 1478559 2219267 := bstep (se 1 (by rfl) ⟨1664450, by rfl⟩ : syracuseStep 2219267 = 3328901) B3328901
theorem B40508693 : Blo 1478559 40508693 := bstep (se 6 (by rfl) ⟨949422, by rfl⟩ : syracuseStep 40508693 = 1898845) B1898845
theorem B2219297 : Blo 1478559 2219297 := bstep (se 2 (by rfl) ⟨832236, by rfl⟩ : syracuseStep 2219297 = 1664473) B1664473
theorem B2219315 : Blo 1478559 2219315 := bstep (se 1 (by rfl) ⟨1664486, by rfl⟩ : syracuseStep 2219315 = 3328973) B3328973
theorem B2219345 : Blo 1478559 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B2219363 : Blo 1478559 2219363 := bstep (se 1 (by rfl) ⟨1664522, by rfl⟩ : syracuseStep 2219363 = 3329045) B3329045
theorem B2497891 : Blo 1478559 2497891 := bstep (se 1 (by rfl) ⟨1873418, by rfl⟩ : syracuseStep 2497891 = 3746837) B3746837
theorem B2219393 : Blo 1478559 2219393 := bstep (se 2 (by rfl) ⟨832272, by rfl⟩ : syracuseStep 2219393 = 1664545) B1664545
theorem B3554705 : Blo 1478559 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B2219411 : Blo 1478559 2219411 := bstep (se 1 (by rfl) ⟨1664558, by rfl⟩ : syracuseStep 2219411 = 3329117) B3329117
theorem B2219441 : Blo 1478559 2219441 := bstep (se 2 (by rfl) ⟨832290, by rfl⟩ : syracuseStep 2219441 = 1664581) B1664581
theorem B2219459 : Blo 1478559 2219459 := bstep (se 1 (by rfl) ⟨1664594, by rfl⟩ : syracuseStep 2219459 = 3329189) B3329189
theorem B2219489 : Blo 1478559 2219489 := bstep (se 2 (by rfl) ⟨832308, by rfl⟩ : syracuseStep 2219489 = 1664617) B1664617
theorem B2498033 : Blo 1478559 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B2219507 : Blo 1478559 2219507 := bstep (se 1 (by rfl) ⟨1664630, by rfl⟩ : syracuseStep 2219507 = 3329261) B3329261
theorem B12631565 : Blo 1478559 12631565 := bstep (se 3 (by rfl) ⟨2368418, by rfl⟩ : syracuseStep 12631565 = 4736837) B4736837
theorem B2219537 : Blo 1478559 2219537 := bstep (se 2 (by rfl) ⟨832326, by rfl⟩ : syracuseStep 2219537 = 1664653) B1664653
theorem B2219555 : Blo 1478559 2219555 := bstep (se 1 (by rfl) ⟨1664666, by rfl⟩ : syracuseStep 2219555 = 3329333) B3329333
theorem B2219585 : Blo 1478559 2219585 := bstep (se 2 (by rfl) ⟨832344, by rfl⟩ : syracuseStep 2219585 = 1664689) B1664689
theorem B2219603 : Blo 1478559 2219603 := bstep (se 1 (by rfl) ⟨1664702, by rfl⟩ : syracuseStep 2219603 = 3329405) B3329405
theorem B2219633 : Blo 1478559 2219633 := bstep (se 2 (by rfl) ⟨832362, by rfl⟩ : syracuseStep 2219633 = 1664725) B1664725
theorem B2498161 : Blo 1478559 2498161 := bstep (se 2 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 2498161 = 1873621) B1873621
theorem B2219651 : Blo 1478559 2219651 := bstep (se 1 (by rfl) ⟨1664738, by rfl⟩ : syracuseStep 2219651 = 3329477) B3329477
theorem B2809475 : Blo 1478559 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B2498195 : Blo 1478559 2498195 := bstep (se 1 (by rfl) ⟨1873646, by rfl⟩ : syracuseStep 2498195 = 3747293) B3747293
theorem B2219681 : Blo 1478559 2219681 := bstep (se 2 (by rfl) ⟨832380, by rfl⟩ : syracuseStep 2219681 = 1664761) B1664761
theorem B4996781 : Blo 1478559 4996781 := bstep (se 3 (by rfl) ⟨936896, by rfl⟩ : syracuseStep 4996781 = 1873793) B1873793
theorem B7487153 : Blo 1478559 7487153 := bstep (se 2 (by rfl) ⟨2807682, by rfl⟩ : syracuseStep 7487153 = 5615365) B5615365
theorem B2219699 : Blo 1478559 2219699 := bstep (se 1 (by rfl) ⟨1664774, by rfl⟩ : syracuseStep 2219699 = 3329549) B3329549
theorem B2219729 : Blo 1478559 2219729 := bstep (se 2 (by rfl) ⟨832398, by rfl⟩ : syracuseStep 2219729 = 1664797) B1664797
theorem B2219747 : Blo 1478559 2219747 := bstep (se 1 (by rfl) ⟨1664810, by rfl⟩ : syracuseStep 2219747 = 3329621) B3329621
theorem B4996835 : Blo 1478559 4996835 := bstep (se 1 (by rfl) ⟨3747626, by rfl⟩ : syracuseStep 4996835 = 7495253) B7495253
theorem B2219777 : Blo 1478559 2219777 := bstep (se 2 (by rfl) ⟨832416, by rfl⟩ : syracuseStep 2219777 = 1664833) B1664833
theorem B2219795 : Blo 1478559 2219795 := bstep (se 1 (by rfl) ⟨1664846, by rfl⟩ : syracuseStep 2219795 = 3329693) B3329693
theorem B2498323 : Blo 1478559 2498323 := bstep (se 1 (by rfl) ⟨1873742, by rfl⟩ : syracuseStep 2498323 = 3747485) B3747485
theorem B2219825 : Blo 1478559 2219825 := bstep (se 2 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 2219825 = 1664869) B1664869
theorem B2219843 : Blo 1478559 2219843 := bstep (se 1 (by rfl) ⟨1664882, by rfl⟩ : syracuseStep 2219843 = 3329765) B3329765
theorem B2219873 : Blo 1478559 2219873 := bstep (se 2 (by rfl) ⟨832452, by rfl⟩ : syracuseStep 2219873 = 1664905) B1664905
theorem B2219891 : Blo 1478559 2219891 := bstep (se 1 (by rfl) ⟨1664918, by rfl⟩ : syracuseStep 2219891 = 3329837) B3329837
theorem B2998147 : Blo 1478559 2998147 := bstep (se 1 (by rfl) ⟨2248610, by rfl⟩ : syracuseStep 2998147 = 4497221) B4497221
theorem B60702605 : Blo 1478559 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B2219921 : Blo 1478559 2219921 := bstep (se 2 (by rfl) ⟨832470, by rfl⟩ : syracuseStep 2219921 = 1664941) B1664941
theorem B2219939 : Blo 1478559 2219939 := bstep (se 1 (by rfl) ⟨1664954, by rfl⟩ : syracuseStep 2219939 = 3329909) B3329909
theorem B2219969 : Blo 1478559 2219969 := bstep (se 2 (by rfl) ⟨832488, by rfl⟩ : syracuseStep 2219969 = 1664977) B1664977
theorem B8421317 : Blo 1478559 8421317 := bstep (se 4 (by rfl) ⟨789498, by rfl⟩ : syracuseStep 8421317 = 1578997) B1578997
theorem B3997649 : Blo 1478559 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B2219987 : Blo 1478559 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B3743729 : Blo 1478559 3743729 := bstep (se 2 (by rfl) ⟨1403898, by rfl⟩ : syracuseStep 3743729 = 2807797) B2807797
theorem B2220017 : Blo 1478559 2220017 := bstep (se 2 (by rfl) ⟨832506, by rfl⟩ : syracuseStep 2220017 = 1665013) B1665013
theorem B45547541 : Blo 1478559 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B3465281 : Blo 1478559 3465281 := bstep (se 2 (by rfl) ⟨1299480, by rfl⟩ : syracuseStep 3465281 = 2598961) B2598961
theorem B2220107 : Blo 1478559 2220107 := bstep (se 1 (by rfl) ⟨1665080, by rfl⟩ : syracuseStep 2220107 = 3330161) B3330161
theorem B2220119 : Blo 1478559 2220119 := bstep (se 1 (by rfl) ⟨1665089, by rfl⟩ : syracuseStep 2220119 = 3330179) B3330179
theorem B6316177 : Blo 1478559 6316177 := bstep (se 2 (by rfl) ⟨2368566, by rfl⟩ : syracuseStep 6316177 = 4737133) B4737133
theorem B7487639 : Blo 1478559 7487639 := bstep (se 1 (by rfl) ⟨5615729, by rfl⟩ : syracuseStep 7487639 = 11231459) B11231459
theorem B2220185 : Blo 1478559 2220185 := bstep (se 2 (by rfl) ⟨832569, by rfl⟩ : syracuseStep 2220185 = 1665139) B1665139
theorem B2220299 : Blo 1478559 2220299 := bstep (se 1 (by rfl) ⟨1665224, by rfl⟩ : syracuseStep 2220299 = 3330449) B3330449
theorem B7110929 : Blo 1478559 7110929 := bstep (se 2 (by rfl) ⟨2666598, by rfl⟩ : syracuseStep 7110929 = 5333197) B5333197
theorem B4210967 : Blo 1478559 4210967 := bstep (se 1 (by rfl) ⟨3158225, by rfl⟩ : syracuseStep 4210967 = 6316451) B6316451
theorem B2220311 : Blo 1478559 2220311 := bstep (se 1 (by rfl) ⟨1665233, by rfl⟩ : syracuseStep 2220311 = 3330467) B3330467
theorem B5620013 : Blo 1478559 5620013 := bstep (se 3 (by rfl) ⟨1053752, by rfl⟩ : syracuseStep 5620013 = 2107505) B2107505
theorem B5620043 : Blo 1478559 5620043 := bstep (se 1 (by rfl) ⟨4215032, by rfl⟩ : syracuseStep 5620043 = 8430065) B8430065
theorem B2220377 : Blo 1478559 2220377 := bstep (se 2 (by rfl) ⟨832641, by rfl⟩ : syracuseStep 2220377 = 1665283) B1665283
theorem B2810227 : Blo 1478559 2810227 := bstep (se 1 (by rfl) ⟨2107670, by rfl⟩ : syracuseStep 2810227 = 4215341) B4215341
theorem B5693827 : Blo 1478559 5693827 := bstep (se 1 (by rfl) ⟨4270370, by rfl⟩ : syracuseStep 5693827 = 8540741) B8540741
theorem B14213555 : Blo 1478559 14213555 := bstep (se 1 (by rfl) ⟨10660166, by rfl⟩ : syracuseStep 14213555 = 21320333) B21320333
theorem B2220491 : Blo 1478559 2220491 := bstep (se 1 (by rfl) ⟨1665368, by rfl⟩ : syracuseStep 2220491 = 3330737) B3330737
theorem B1663447 : Blo 1478559 1663447 := bstep (se 1 (by rfl) ⟨1247585, by rfl⟩ : syracuseStep 1663447 = 2495171) B2495171
theorem B2220503 : Blo 1478559 2220503 := bstep (se 1 (by rfl) ⟨1665377, by rfl⟩ : syracuseStep 2220503 = 3330755) B3330755
theorem B2220569 : Blo 1478559 2220569 := bstep (se 2 (by rfl) ⟨832713, by rfl⟩ : syracuseStep 2220569 = 1665427) B1665427
theorem B1663627 : Blo 1478559 1663627 := bstep (se 1 (by rfl) ⟨1247720, by rfl⟩ : syracuseStep 1663627 = 2495441) B2495441
theorem B2220683 : Blo 1478559 2220683 := bstep (se 1 (by rfl) ⟨1665512, by rfl⟩ : syracuseStep 2220683 = 3331025) B3331025
theorem B8536727 : Blo 1478559 8536727 := bstep (se 1 (by rfl) ⟨6402545, by rfl⟩ : syracuseStep 8536727 = 12805091) B12805091
theorem B3744407 : Blo 1478559 3744407 := bstep (se 1 (by rfl) ⟨2808305, by rfl⟩ : syracuseStep 3744407 = 5616611) B5616611
theorem B2220695 : Blo 1478559 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B2220761 : Blo 1478559 2220761 := bstep (se 2 (by rfl) ⟨832785, by rfl⟩ : syracuseStep 2220761 = 1665571) B1665571
theorem B1663735 : Blo 1478559 1663735 := bstep (se 1 (by rfl) ⟨1247801, by rfl⟩ : syracuseStep 1663735 = 2495603) B2495603
theorem B2810675 : Blo 1478559 2810675 := bstep (se 1 (by rfl) ⟨2108006, by rfl⟩ : syracuseStep 2810675 = 4216013) B4216013
theorem B3326795 : Blo 1478559 3326795 := bstep (se 1 (by rfl) ⟨2495096, by rfl⟩ : syracuseStep 3326795 = 4990193) B4990193
theorem B2810713 : Blo 1478559 2810713 := bstep (se 2 (by rfl) ⟨1054017, by rfl⟩ : syracuseStep 2810713 = 2108035) B2108035
theorem B3326849 : Blo 1478559 3326849 := bstep (se 2 (by rfl) ⟨1247568, by rfl⟩ : syracuseStep 3326849 = 2495137) B2495137
theorem B1663915 : Blo 1478559 1663915 := bstep (se 1 (by rfl) ⟨1247936, by rfl⟩ : syracuseStep 1663915 = 2495873) B2495873
theorem B5620697 : Blo 1478559 5620697 := bstep (se 2 (by rfl) ⟨2107761, by rfl⟩ : syracuseStep 5620697 = 4215523) B4215523
theorem B1664023 : Blo 1478559 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B3327065 : Blo 1478559 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B8422501 : Blo 1478559 8422501 := bstep (se 4 (by rfl) ⟨789609, by rfl⟩ : syracuseStep 8422501 = 1579219) B1579219
theorem B16860311 : Blo 1478559 16860311 := bstep (se 1 (by rfl) ⟨12645233, by rfl⟩ : syracuseStep 16860311 = 25290467) B25290467
theorem B3327155 : Blo 1478559 3327155 := bstep (se 1 (by rfl) ⟨2495366, by rfl⟩ : syracuseStep 3327155 = 4990733) B4990733
theorem B1664203 : Blo 1478559 1664203 := bstep (se 1 (by rfl) ⟨1248152, by rfl⟩ : syracuseStep 1664203 = 2496305) B2496305
theorem B3327191 : Blo 1478559 3327191 := bstep (se 1 (by rfl) ⟨2495393, by rfl⟩ : syracuseStep 3327191 = 4990787) B4990787
theorem B5621015 : Blo 1478559 5621015 := bstep (se 1 (by rfl) ⟨4215761, by rfl⟩ : syracuseStep 5621015 = 8431523) B8431523
theorem B3745075 : Blo 1478559 3745075 := bstep (se 1 (by rfl) ⟨2808806, by rfl⟩ : syracuseStep 3745075 = 5617613) B5617613
theorem B1664311 : Blo 1478559 1664311 := bstep (se 1 (by rfl) ⟨1248233, by rfl⟩ : syracuseStep 1664311 = 2496467) B2496467
theorem B2368855 : Blo 1478559 2368855 := bstep (se 1 (by rfl) ⟨1776641, by rfl⟩ : syracuseStep 2368855 = 3553283) B3553283
theorem B4498777 : Blo 1478559 4498777 := bstep (se 2 (by rfl) ⟨1687041, by rfl⟩ : syracuseStep 4498777 = 3374083) B3374083
theorem B4990301 : Blo 1478559 4990301 := bstep (se 3 (by rfl) ⟨935681, by rfl⟩ : syracuseStep 4990301 = 1871363) B1871363
theorem B3327371 : Blo 1478559 3327371 := bstep (se 1 (by rfl) ⟨2495528, by rfl⟩ : syracuseStep 3327371 = 4991057) B4991057
theorem B3327425 : Blo 1478559 3327425 := bstep (se 2 (by rfl) ⟨1247784, by rfl⟩ : syracuseStep 3327425 = 2495569) B2495569
theorem B3745217 : Blo 1478559 3745217 := bstep (se 2 (by rfl) ⟨1404456, by rfl⟩ : syracuseStep 3745217 = 2808913) B2808913
theorem B5998045 : Blo 1478559 5998045 := bstep (se 3 (by rfl) ⟨1124633, by rfl⟩ : syracuseStep 5998045 = 2249267) B2249267
theorem B1664491 : Blo 1478559 1664491 := bstep (se 1 (by rfl) ⟨1248368, by rfl⟩ : syracuseStep 1664491 = 2496737) B2496737
theorem B4212299 : Blo 1478559 4212299 := bstep (se 1 (by rfl) ⟨3159224, by rfl⟩ : syracuseStep 4212299 = 6318449) B6318449
theorem B1664599 : Blo 1478559 1664599 := bstep (se 1 (by rfl) ⟨1248449, by rfl⟩ : syracuseStep 1664599 = 2496899) B2496899
theorem B3327641 : Blo 1478559 3327641 := bstep (se 2 (by rfl) ⟨1247865, by rfl⟩ : syracuseStep 3327641 = 2495731) B2495731
theorem B23979725 : Blo 1478559 23979725 := bstep (se 3 (by rfl) ⟨4496198, by rfl⟩ : syracuseStep 23979725 = 8992397) B8992397
theorem B3327731 : Blo 1478559 3327731 := bstep (se 1 (by rfl) ⟨2495798, by rfl⟩ : syracuseStep 3327731 = 4991597) B4991597
theorem B2279179 : Blo 1478559 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B1664779 : Blo 1478559 1664779 := bstep (se 1 (by rfl) ⟨1248584, by rfl⟩ : syracuseStep 1664779 = 2497169) B2497169
theorem B3327767 : Blo 1478559 3327767 := bstep (se 1 (by rfl) ⟨2495825, by rfl⟩ : syracuseStep 3327767 = 4991651) B4991651
theorem B3999563 : Blo 1478559 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B1664887 : Blo 1478559 1664887 := bstep (se 1 (by rfl) ⟨1248665, by rfl⟩ : syracuseStep 1664887 = 2497331) B2497331
theorem B12642227 : Blo 1478559 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B3327947 : Blo 1478559 3327947 := bstep (se 1 (by rfl) ⟨2495960, by rfl⟩ : syracuseStep 3327947 = 4991921) B4991921
theorem B6932441 : Blo 1478559 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B3328001 : Blo 1478559 3328001 := bstep (se 2 (by rfl) ⟨1248000, by rfl⟩ : syracuseStep 3328001 = 2496001) B2496001
theorem B1665067 : Blo 1478559 1665067 := bstep (se 1 (by rfl) ⟨1248800, by rfl⟩ : syracuseStep 1665067 = 2497601) B2497601
theorem B5335085 : Blo 1478559 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B18950219 : Blo 1478559 18950219 := bstep (se 1 (by rfl) ⟨14212664, by rfl⟩ : syracuseStep 18950219 = 28425329) B28425329
theorem B2369611 : Blo 1478559 2369611 := bstep (se 1 (by rfl) ⟨1777208, by rfl⟩ : syracuseStep 2369611 = 3554417) B3554417
theorem B2369675 : Blo 1478559 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B1665175 : Blo 1478559 1665175 := bstep (se 1 (by rfl) ⟨1248881, by rfl⟩ : syracuseStep 1665175 = 2497763) B2497763
theorem B3328217 : Blo 1478559 3328217 := bstep (se 2 (by rfl) ⟨1248081, by rfl⟩ : syracuseStep 3328217 = 2496163) B2496163
theorem B2369803 : Blo 1478559 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B10668323 : Blo 1478559 10668323 := bstep (se 1 (by rfl) ⟨8001242, by rfl⟩ : syracuseStep 10668323 = 16002485) B16002485
theorem B3328307 : Blo 1478559 3328307 := bstep (se 1 (by rfl) ⟨2496230, by rfl⟩ : syracuseStep 3328307 = 4992461) B4992461
theorem B1665355 : Blo 1478559 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B3328343 : Blo 1478559 3328343 := bstep (se 1 (by rfl) ⟨2496257, by rfl⟩ : syracuseStep 3328343 = 4992515) B4992515
theorem B1665463 : Blo 1478559 1665463 := bstep (se 1 (by rfl) ⟨1249097, by rfl⟩ : syracuseStep 1665463 = 2498195) B2498195
theorem B4991435 : Blo 1478559 4991435 := bstep (se 1 (by rfl) ⟨3743576, by rfl⟩ : syracuseStep 4991435 = 7487153) B7487153
theorem B3328523 : Blo 1478559 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B3328577 : Blo 1478559 3328577 := bstep (se 2 (by rfl) ⟨1248216, by rfl⟩ : syracuseStep 3328577 = 2496433) B2496433
theorem B5614211 : Blo 1478559 5614211 := bstep (se 1 (by rfl) ⟨4210658, by rfl⟩ : syracuseStep 5614211 = 8421317) B8421317
theorem B2665099 : Blo 1478559 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B3746483 : Blo 1478559 3746483 := bstep (se 1 (by rfl) ⟨2809862, by rfl⟩ : syracuseStep 3746483 = 5619725) B5619725
theorem B4991705 : Blo 1478559 4991705 := bstep (se 2 (by rfl) ⟨1871889, by rfl⟩ : syracuseStep 4991705 = 3743779) B3743779
theorem B3328793 : Blo 1478559 3328793 := bstep (se 2 (by rfl) ⟨1248297, by rfl⟩ : syracuseStep 3328793 = 2496595) B2496595
theorem B6744883 : Blo 1478559 6744883 := bstep (se 1 (by rfl) ⟨5058662, by rfl⟩ : syracuseStep 6744883 = 10117325) B10117325
theorem B3328883 : Blo 1478559 3328883 := bstep (se 1 (by rfl) ⟨2496662, by rfl⟩ : syracuseStep 3328883 = 4993325) B4993325
theorem B5557123 : Blo 1478559 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B3328919 : Blo 1478559 3328919 := bstep (se 1 (by rfl) ⟨2496689, by rfl⟩ : syracuseStep 3328919 = 4993379) B4993379
theorem B2370521 : Blo 1478559 2370521 := bstep (se 2 (by rfl) ⟨888945, by rfl⟩ : syracuseStep 2370521 = 1777891) B1777891
theorem B12643289 : Blo 1478559 12643289 := bstep (se 2 (by rfl) ⟨4741233, by rfl⟩ : syracuseStep 12643289 = 9482467) B9482467
theorem B12815405 : Blo 1478559 12815405 := bstep (se 3 (by rfl) ⟨2402888, by rfl⟩ : syracuseStep 12815405 = 4805777) B4805777
theorem B12807233 : Blo 1478559 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B5614667 : Blo 1478559 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B3329099 : Blo 1478559 3329099 := bstep (se 1 (by rfl) ⟨2496824, by rfl⟩ : syracuseStep 3329099 = 4993649) B4993649
theorem B2665561 : Blo 1478559 2665561 := bstep (se 2 (by rfl) ⟨999585, by rfl⟩ : syracuseStep 2665561 = 1999171) B1999171
theorem B2370649 : Blo 1478559 2370649 := bstep (se 2 (by rfl) ⟨888993, by rfl⟩ : syracuseStep 2370649 = 1777987) B1777987
theorem B3329153 : Blo 1478559 3329153 := bstep (se 2 (by rfl) ⟨1248432, by rfl⟩ : syracuseStep 3329153 = 2496865) B2496865
theorem B6319235 : Blo 1478559 6319235 := bstep (se 1 (by rfl) ⟨4739426, by rfl⟩ : syracuseStep 6319235 = 9478853) B9478853
theorem B4213939 : Blo 1478559 4213939 := bstep (se 1 (by rfl) ⟨3160454, by rfl⟩ : syracuseStep 4213939 = 6320909) B6320909
theorem B26987701 : Blo 1478559 26987701 := bstep (se 5 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 26987701 = 2530097) B2530097
theorem B3747019 : Blo 1478559 3747019 := bstep (se 1 (by rfl) ⟨2810264, by rfl⟩ : syracuseStep 3747019 = 5620529) B5620529
theorem B5614865 : Blo 1478559 5614865 := bstep (se 2 (by rfl) ⟨2105574, by rfl⟩ : syracuseStep 5614865 = 4211149) B4211149
theorem B40496429 : Blo 1478559 40496429 := bstep (se 3 (by rfl) ⟨7593080, by rfl⟩ : syracuseStep 40496429 = 15186161) B15186161
theorem B3329369 : Blo 1478559 3329369 := bstep (se 2 (by rfl) ⟨1248513, by rfl⟩ : syracuseStep 3329369 = 2497027) B2497027
theorem B3747161 : Blo 1478559 3747161 := bstep (se 2 (by rfl) ⟨1405185, by rfl⟩ : syracuseStep 3747161 = 2810371) B2810371
theorem B36015509 : Blo 1478559 36015509 := bstep (se 6 (by rfl) ⟨844113, by rfl⟩ : syracuseStep 36015509 = 1688227) B1688227
theorem B4992407 : Blo 1478559 4992407 := bstep (se 1 (by rfl) ⟨3744305, by rfl⟩ : syracuseStep 4992407 = 7488611) B7488611
theorem B3329459 : Blo 1478559 3329459 := bstep (se 1 (by rfl) ⟨2497094, by rfl⟩ : syracuseStep 3329459 = 4994189) B4994189
theorem B3329495 : Blo 1478559 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B2371033 : Blo 1478559 2371033 := bstep (se 2 (by rfl) ⟨889137, by rfl⟩ : syracuseStep 2371033 = 1778275) B1778275
theorem B11234861 : Blo 1478559 11234861 := bstep (se 3 (by rfl) ⟨2106536, by rfl⟩ : syracuseStep 11234861 = 4213073) B4213073
theorem B2403929 : Blo 1478559 2403929 := bstep (se 2 (by rfl) ⟨901473, by rfl⟩ : syracuseStep 2403929 = 1802947) B1802947
theorem B7491203 : Blo 1478559 7491203 := bstep (se 1 (by rfl) ⟨5618402, by rfl⟩ : syracuseStep 7491203 = 11236805) B11236805
theorem B3329675 : Blo 1478559 3329675 := bstep (se 1 (by rfl) ⟨2497256, by rfl⟩ : syracuseStep 3329675 = 4994513) B4994513
theorem B3329729 : Blo 1478559 3329729 := bstep (se 2 (by rfl) ⟨1248648, by rfl⟩ : syracuseStep 3329729 = 2497297) B2497297
theorem B2600651 : Blo 1478559 2600651 := bstep (se 1 (by rfl) ⟨1950488, by rfl⟩ : syracuseStep 2600651 = 3900977) B3900977
theorem B2666201 : Blo 1478559 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B2371289 : Blo 1478559 2371289 := bstep (se 2 (by rfl) ⟨889233, by rfl⟩ : syracuseStep 2371289 = 1778467) B1778467
theorem B12635939 : Blo 1478559 12635939 := bstep (se 1 (by rfl) ⟨9476954, by rfl⟩ : syracuseStep 12635939 = 18953909) B18953909
theorem B3329945 : Blo 1478559 3329945 := bstep (se 2 (by rfl) ⟨1248729, by rfl⟩ : syracuseStep 3329945 = 2497459) B2497459
theorem B1478571 : Blo 1478559 1478571 := bstep (se 1 (by rfl) ⟨1108928, by rfl⟩ : syracuseStep 1478571 = 2217857) B2217857
theorem B4992947 : Blo 1478559 4992947 := bstep (se 1 (by rfl) ⟨3744710, by rfl⟩ : syracuseStep 4992947 = 7489421) B7489421
theorem B1478583 : Blo 1478559 1478583 := bstep (se 1 (by rfl) ⟨1108937, by rfl⟩ : syracuseStep 1478583 = 2217875) B2217875
theorem B1478603 : Blo 1478559 1478603 := bstep (se 1 (by rfl) ⟨1108952, by rfl⟩ : syracuseStep 1478603 = 2217905) B2217905
theorem B1478615 : Blo 1478559 1478615 := bstep (se 1 (by rfl) ⟨1108961, by rfl⟩ : syracuseStep 1478615 = 2217923) B2217923
theorem B34156505 : Blo 1478559 34156505 := bstep (se 2 (by rfl) ⟨12808689, by rfl⟩ : syracuseStep 34156505 = 25617379) B25617379
theorem B1478635 : Blo 1478559 1478635 := bstep (se 1 (by rfl) ⟨1108976, by rfl⟩ : syracuseStep 1478635 = 2217953) B2217953
theorem B3330035 : Blo 1478559 3330035 := bstep (se 1 (by rfl) ⟨2497526, by rfl⟩ : syracuseStep 3330035 = 4995053) B4995053
theorem B1478647 : Blo 1478559 1478647 := bstep (se 1 (by rfl) ⟨1108985, by rfl⟩ : syracuseStep 1478647 = 2217971) B2217971
theorem B1478667 : Blo 1478559 1478667 := bstep (se 1 (by rfl) ⟨1109000, by rfl⟩ : syracuseStep 1478667 = 2218001) B2218001
theorem B1478679 : Blo 1478559 1478679 := bstep (se 1 (by rfl) ⟨1109009, by rfl⟩ : syracuseStep 1478679 = 2218019) B2218019
theorem B5615639 : Blo 1478559 5615639 := bstep (se 1 (by rfl) ⟨4211729, by rfl⟩ : syracuseStep 5615639 = 8423459) B8423459
theorem B3330071 : Blo 1478559 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B1478699 : Blo 1478559 1478699 := bstep (se 1 (by rfl) ⟨1109024, by rfl⟩ : syracuseStep 1478699 = 2218049) B2218049
theorem B9482285 : Blo 1478559 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B1478711 : Blo 1478559 1478711 := bstep (se 1 (by rfl) ⟨1109033, by rfl⟩ : syracuseStep 1478711 = 2218067) B2218067
theorem B1478731 : Blo 1478559 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B7589963 : Blo 1478559 7589963 := bstep (se 1 (by rfl) ⟨5692472, by rfl⟩ : syracuseStep 7589963 = 11384945) B11384945
theorem B1478743 : Blo 1478559 1478743 := bstep (se 1 (by rfl) ⟨1109057, by rfl⟩ : syracuseStep 1478743 = 2218115) B2218115
theorem B1478763 : Blo 1478559 1478763 := bstep (se 1 (by rfl) ⟨1109072, by rfl⟩ : syracuseStep 1478763 = 2218145) B2218145
theorem B3158131 : Blo 1478559 3158131 := bstep (se 1 (by rfl) ⟨2368598, by rfl⟩ : syracuseStep 3158131 = 4737197) B4737197
theorem B1478775 : Blo 1478559 1478775 := bstep (se 1 (by rfl) ⟨1109081, by rfl⟩ : syracuseStep 1478775 = 2218163) B2218163
theorem B1478795 : Blo 1478559 1478795 := bstep (se 1 (by rfl) ⟨1109096, by rfl⟩ : syracuseStep 1478795 = 2218193) B2218193
theorem B1872011 : Blo 1478559 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B1478807 : Blo 1478559 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B1478827 : Blo 1478559 1478827 := bstep (se 1 (by rfl) ⟨1109120, by rfl⟩ : syracuseStep 1478827 = 2218241) B2218241
theorem B1478839 : Blo 1478559 1478839 := bstep (se 1 (by rfl) ⟨1109129, by rfl⟩ : syracuseStep 1478839 = 2218259) B2218259
theorem B4993217 : Blo 1478559 4993217 := bstep (se 2 (by rfl) ⟨1872456, by rfl⟩ : syracuseStep 4993217 = 3744913) B3744913
theorem B1478859 : Blo 1478559 1478859 := bstep (se 1 (by rfl) ⟨1109144, by rfl⟩ : syracuseStep 1478859 = 2218289) B2218289
theorem B3330251 : Blo 1478559 3330251 := bstep (se 1 (by rfl) ⟨2497688, by rfl⟩ : syracuseStep 3330251 = 4995377) B4995377
theorem B4214987 : Blo 1478559 4214987 := bstep (se 1 (by rfl) ⟨3161240, by rfl⟩ : syracuseStep 4214987 = 6322481) B6322481
theorem B1478871 : Blo 1478559 1478871 := bstep (se 1 (by rfl) ⟨1109153, by rfl⟩ : syracuseStep 1478871 = 2218307) B2218307
theorem B5615837 : Blo 1478559 5615837 := bstep (se 3 (by rfl) ⟨1052969, by rfl⟩ : syracuseStep 5615837 = 2105939) B2105939
theorem B1478891 : Blo 1478559 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B1478903 : Blo 1478559 1478903 := bstep (se 1 (by rfl) ⟨1109177, by rfl⟩ : syracuseStep 1478903 = 2218355) B2218355
theorem B3330305 : Blo 1478559 3330305 := bstep (se 2 (by rfl) ⟨1248864, by rfl⟩ : syracuseStep 3330305 = 2497729) B2497729
theorem B1478923 : Blo 1478559 1478923 := bstep (se 1 (by rfl) ⟨1109192, by rfl⟩ : syracuseStep 1478923 = 2218385) B2218385
theorem B1478935 : Blo 1478559 1478935 := bstep (se 1 (by rfl) ⟨1109201, by rfl⟩ : syracuseStep 1478935 = 2218403) B2218403
theorem B1478955 : Blo 1478559 1478955 := bstep (se 1 (by rfl) ⟨1109216, by rfl⟩ : syracuseStep 1478955 = 2218433) B2218433
theorem B1478967 : Blo 1478559 1478967 := bstep (se 1 (by rfl) ⟨1109225, by rfl⟩ : syracuseStep 1478967 = 2218451) B2218451
theorem B1478987 : Blo 1478559 1478987 := bstep (se 1 (by rfl) ⟨1109240, by rfl⟩ : syracuseStep 1478987 = 2218481) B2218481
theorem B1478999 : Blo 1478559 1478999 := bstep (se 1 (by rfl) ⟨1109249, by rfl⟩ : syracuseStep 1478999 = 2218499) B2218499
theorem B1479019 : Blo 1478559 1479019 := bstep (se 1 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 1479019 = 2218529) B2218529
theorem B25268597 : Blo 1478559 25268597 := bstep (se 5 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 25268597 = 2368931) B2368931
theorem B1479031 : Blo 1478559 1479031 := bstep (se 1 (by rfl) ⟨1109273, by rfl⟩ : syracuseStep 1479031 = 2218547) B2218547
theorem B1479051 : Blo 1478559 1479051 := bstep (se 1 (by rfl) ⟨1109288, by rfl⟩ : syracuseStep 1479051 = 2218577) B2218577
theorem B1479063 : Blo 1478559 1479063 := bstep (se 1 (by rfl) ⟨1109297, by rfl⟩ : syracuseStep 1479063 = 2218595) B2218595
theorem B1479083 : Blo 1478559 1479083 := bstep (se 1 (by rfl) ⟨1109312, by rfl⟩ : syracuseStep 1479083 = 2218625) B2218625
theorem B1479095 : Blo 1478559 1479095 := bstep (se 1 (by rfl) ⟨1109321, by rfl⟩ : syracuseStep 1479095 = 2218643) B2218643
theorem B1479115 : Blo 1478559 1479115 := bstep (se 1 (by rfl) ⟨1109336, by rfl⟩ : syracuseStep 1479115 = 2218673) B2218673
theorem B1479127 : Blo 1478559 1479127 := bstep (se 1 (by rfl) ⟨1109345, by rfl⟩ : syracuseStep 1479127 = 2218691) B2218691
theorem B3330521 : Blo 1478559 3330521 := bstep (se 2 (by rfl) ⟨1248945, by rfl⟩ : syracuseStep 3330521 = 2497891) B2497891
theorem B1479147 : Blo 1478559 1479147 := bstep (se 1 (by rfl) ⟨1109360, by rfl⟩ : syracuseStep 1479147 = 2218721) B2218721
theorem B1479159 : Blo 1478559 1479159 := bstep (se 1 (by rfl) ⟨1109369, by rfl⟩ : syracuseStep 1479159 = 2218739) B2218739
theorem B1479179 : Blo 1478559 1479179 := bstep (se 1 (by rfl) ⟨1109384, by rfl⟩ : syracuseStep 1479179 = 2218769) B2218769
theorem B1479191 : Blo 1478559 1479191 := bstep (se 1 (by rfl) ⟨1109393, by rfl⟩ : syracuseStep 1479191 = 2218787) B2218787
theorem B1479211 : Blo 1478559 1479211 := bstep (se 1 (by rfl) ⟨1109408, by rfl⟩ : syracuseStep 1479211 = 2218817) B2218817
theorem B3330611 : Blo 1478559 3330611 := bstep (se 1 (by rfl) ⟨2497958, by rfl⟩ : syracuseStep 3330611 = 4995917) B4995917
theorem B1479223 : Blo 1478559 1479223 := bstep (se 1 (by rfl) ⟨1109417, by rfl⟩ : syracuseStep 1479223 = 2218835) B2218835
theorem B1479243 : Blo 1478559 1479243 := bstep (se 1 (by rfl) ⟨1109432, by rfl⟩ : syracuseStep 1479243 = 2218865) B2218865
theorem B1479255 : Blo 1478559 1479255 := bstep (se 1 (by rfl) ⟨1109441, by rfl⟩ : syracuseStep 1479255 = 2218883) B2218883
theorem B3330647 : Blo 1478559 3330647 := bstep (se 1 (by rfl) ⟨2497985, by rfl⟩ : syracuseStep 3330647 = 4995971) B4995971
theorem B1479275 : Blo 1478559 1479275 := bstep (se 1 (by rfl) ⟨1109456, by rfl⟩ : syracuseStep 1479275 = 2218913) B2218913
theorem B1479287 : Blo 1478559 1479287 := bstep (se 1 (by rfl) ⟨1109465, by rfl⟩ : syracuseStep 1479287 = 2218931) B2218931
theorem B1479307 : Blo 1478559 1479307 := bstep (se 1 (by rfl) ⟨1109480, by rfl⟩ : syracuseStep 1479307 = 2218961) B2218961
theorem B1520267 : Blo 1478559 1520267 := bstep (se 1 (by rfl) ⟨1140200, by rfl⟩ : syracuseStep 1520267 = 2280401) B2280401
theorem B1479319 : Blo 1478559 1479319 := bstep (se 1 (by rfl) ⟨1109489, by rfl⟩ : syracuseStep 1479319 = 2218979) B2218979
theorem B4739735 : Blo 1478559 4739735 := bstep (se 1 (by rfl) ⟨3554801, by rfl⟩ : syracuseStep 4739735 = 7109603) B7109603
theorem B1479339 : Blo 1478559 1479339 := bstep (se 1 (by rfl) ⟨1109504, by rfl⟩ : syracuseStep 1479339 = 2219009) B2219009
theorem B1479351 : Blo 1478559 1479351 := bstep (se 1 (by rfl) ⟨1109513, by rfl⟩ : syracuseStep 1479351 = 2219027) B2219027
theorem B1479371 : Blo 1478559 1479371 := bstep (se 1 (by rfl) ⟨1109528, by rfl⟩ : syracuseStep 1479371 = 2219057) B2219057
theorem B2495191 : Blo 1478559 2495191 := bstep (se 1 (by rfl) ⟨1871393, by rfl⟩ : syracuseStep 2495191 = 3742787) B3742787
theorem B1479383 : Blo 1478559 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B4993757 : Blo 1478559 4993757 := bstep (se 3 (by rfl) ⟨936329, by rfl⟩ : syracuseStep 4993757 = 1872659) B1872659
theorem B1479403 : Blo 1478559 1479403 := bstep (se 1 (by rfl) ⟨1109552, by rfl⟩ : syracuseStep 1479403 = 2219105) B2219105
theorem B1479415 : Blo 1478559 1479415 := bstep (se 1 (by rfl) ⟨1109561, by rfl⟩ : syracuseStep 1479415 = 2219123) B2219123
theorem B1479435 : Blo 1478559 1479435 := bstep (se 1 (by rfl) ⟨1109576, by rfl⟩ : syracuseStep 1479435 = 2219153) B2219153
theorem B3330827 : Blo 1478559 3330827 := bstep (se 1 (by rfl) ⟨2498120, by rfl⟩ : syracuseStep 3330827 = 4996241) B4996241
theorem B1479447 : Blo 1478559 1479447 := bstep (se 1 (by rfl) ⟨1109585, by rfl⟩ : syracuseStep 1479447 = 2219171) B2219171
theorem B1479467 : Blo 1478559 1479467 := bstep (se 1 (by rfl) ⟨1109600, by rfl⟩ : syracuseStep 1479467 = 2219201) B2219201
theorem B1479479 : Blo 1478559 1479479 := bstep (se 1 (by rfl) ⟨1109609, by rfl⟩ : syracuseStep 1479479 = 2219219) B2219219
theorem B3330881 : Blo 1478559 3330881 := bstep (se 2 (by rfl) ⟨1249080, by rfl⟩ : syracuseStep 3330881 = 2498161) B2498161
theorem B1479499 : Blo 1478559 1479499 := bstep (se 1 (by rfl) ⟨1109624, by rfl⟩ : syracuseStep 1479499 = 2219249) B2219249
theorem B1872715 : Blo 1478559 1872715 := bstep (se 1 (by rfl) ⟨1404536, by rfl⟩ : syracuseStep 1872715 = 2809073) B2809073
theorem B1479511 : Blo 1478559 1479511 := bstep (se 1 (by rfl) ⟨1109633, by rfl⟩ : syracuseStep 1479511 = 2219267) B2219267
theorem B27005795 : Blo 1478559 27005795 := bstep (se 1 (by rfl) ⟨20254346, by rfl⟩ : syracuseStep 27005795 = 40508693) B40508693
theorem B1479531 : Blo 1478559 1479531 := bstep (se 1 (by rfl) ⟨1109648, by rfl⟩ : syracuseStep 1479531 = 2219297) B2219297
theorem B1479543 : Blo 1478559 1479543 := bstep (se 1 (by rfl) ⟨1109657, by rfl⟩ : syracuseStep 1479543 = 2219315) B2219315
theorem B1479563 : Blo 1478559 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B1479575 : Blo 1478559 1479575 := bstep (se 1 (by rfl) ⟨1109681, by rfl⟩ : syracuseStep 1479575 = 2219363) B2219363
theorem B1479595 : Blo 1478559 1479595 := bstep (se 1 (by rfl) ⟨1109696, by rfl⟩ : syracuseStep 1479595 = 2219393) B2219393
theorem B14226353 : Blo 1478559 14226353 := bstep (se 2 (by rfl) ⟨5334882, by rfl⟩ : syracuseStep 14226353 = 10669765) B10669765
theorem B1479607 : Blo 1478559 1479607 := bstep (se 1 (by rfl) ⟨1109705, by rfl⟩ : syracuseStep 1479607 = 2219411) B2219411
theorem B1479627 : Blo 1478559 1479627 := bstep (se 1 (by rfl) ⟨1109720, by rfl⟩ : syracuseStep 1479627 = 2219441) B2219441
theorem B1479639 : Blo 1478559 1479639 := bstep (se 1 (by rfl) ⟨1109729, by rfl⟩ : syracuseStep 1479639 = 2219459) B2219459
theorem B1479659 : Blo 1478559 1479659 := bstep (se 1 (by rfl) ⟨1109744, by rfl⟩ : syracuseStep 1479659 = 2219489) B2219489
theorem B1479671 : Blo 1478559 1479671 := bstep (se 1 (by rfl) ⟨1109753, by rfl⟩ : syracuseStep 1479671 = 2219507) B2219507
theorem B1479691 : Blo 1478559 1479691 := bstep (se 1 (by rfl) ⟨1109768, by rfl⟩ : syracuseStep 1479691 = 2219537) B2219537
theorem B1479703 : Blo 1478559 1479703 := bstep (se 1 (by rfl) ⟨1109777, by rfl⟩ : syracuseStep 1479703 = 2219555) B2219555
theorem B3331097 : Blo 1478559 3331097 := bstep (se 2 (by rfl) ⟨1249161, by rfl⟩ : syracuseStep 3331097 = 2498323) B2498323
theorem B1479723 : Blo 1478559 1479723 := bstep (se 1 (by rfl) ⟨1109792, by rfl⟩ : syracuseStep 1479723 = 2219585) B2219585
theorem B1479735 : Blo 1478559 1479735 := bstep (se 1 (by rfl) ⟨1109801, by rfl⟩ : syracuseStep 1479735 = 2219603) B2219603
theorem B1479755 : Blo 1478559 1479755 := bstep (se 1 (by rfl) ⟨1109816, by rfl⟩ : syracuseStep 1479755 = 2219633) B2219633
theorem B1479767 : Blo 1478559 1479767 := bstep (se 1 (by rfl) ⟨1109825, by rfl⟩ : syracuseStep 1479767 = 2219651) B2219651
theorem B1872983 : Blo 1478559 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B1479787 : Blo 1478559 1479787 := bstep (se 1 (by rfl) ⟨1109840, by rfl⟩ : syracuseStep 1479787 = 2219681) B2219681
theorem B1479799 : Blo 1478559 1479799 := bstep (se 1 (by rfl) ⟨1109849, by rfl⟩ : syracuseStep 1479799 = 2219699) B2219699
theorem B1520759 : Blo 1478559 1520759 := bstep (se 1 (by rfl) ⟨1140569, by rfl⟩ : syracuseStep 1520759 = 2281139) B2281139
theorem B3331187 : Blo 1478559 3331187 := bstep (se 1 (by rfl) ⟨2498390, by rfl⟩ : syracuseStep 3331187 = 4996781) B4996781
theorem B6583427 : Blo 1478559 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B1479819 : Blo 1478559 1479819 := bstep (se 1 (by rfl) ⟨1109864, by rfl⟩ : syracuseStep 1479819 = 2219729) B2219729
theorem B1479831 : Blo 1478559 1479831 := bstep (se 1 (by rfl) ⟨1109873, by rfl⟩ : syracuseStep 1479831 = 2219747) B2219747
theorem B3331223 : Blo 1478559 3331223 := bstep (se 1 (by rfl) ⟨2498417, by rfl⟩ : syracuseStep 3331223 = 4996835) B4996835
theorem B1479851 : Blo 1478559 1479851 := bstep (se 1 (by rfl) ⟨1109888, by rfl⟩ : syracuseStep 1479851 = 2219777) B2219777
theorem B1479863 : Blo 1478559 1479863 := bstep (se 1 (by rfl) ⟨1109897, by rfl⟩ : syracuseStep 1479863 = 2219795) B2219795
theorem B1479883 : Blo 1478559 1479883 := bstep (se 1 (by rfl) ⟨1109912, by rfl⟩ : syracuseStep 1479883 = 2219825) B2219825
theorem B1479895 : Blo 1478559 1479895 := bstep (se 1 (by rfl) ⟨1109921, by rfl⟩ : syracuseStep 1479895 = 2219843) B2219843
theorem B1479915 : Blo 1478559 1479915 := bstep (se 1 (by rfl) ⟨1109936, by rfl⟩ : syracuseStep 1479915 = 2219873) B2219873
theorem B1479927 : Blo 1478559 1479927 := bstep (se 1 (by rfl) ⟨1109945, by rfl⟩ : syracuseStep 1479927 = 2219891) B2219891
theorem B1479947 : Blo 1478559 1479947 := bstep (se 1 (by rfl) ⟨1109960, by rfl⟩ : syracuseStep 1479947 = 2219921) B2219921
theorem B3159319 : Blo 1478559 3159319 := bstep (se 1 (by rfl) ⟨2369489, by rfl⟩ : syracuseStep 3159319 = 4738979) B4738979
theorem B1479959 : Blo 1478559 1479959 := bstep (se 1 (by rfl) ⟨1109969, by rfl⟩ : syracuseStep 1479959 = 2219939) B2219939
theorem B1479979 : Blo 1478559 1479979 := bstep (se 1 (by rfl) ⟨1109984, by rfl⟩ : syracuseStep 1479979 = 2219969) B2219969
theorem B1479991 : Blo 1478559 1479991 := bstep (se 1 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 1479991 = 2219987) B2219987
theorem B3159361 : Blo 1478559 3159361 := bstep (se 2 (by rfl) ⟨1184760, by rfl⟩ : syracuseStep 3159361 = 2369521) B2369521
theorem B3421505 : Blo 1478559 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B2495819 : Blo 1478559 2495819 := bstep (se 1 (by rfl) ⟨1871864, by rfl⟩ : syracuseStep 2495819 = 3743729) B3743729
theorem B1480011 : Blo 1478559 1480011 := bstep (se 1 (by rfl) ⟨1110008, by rfl⟩ : syracuseStep 1480011 = 2220017) B2220017
theorem B1480023 : Blo 1478559 1480023 := bstep (se 1 (by rfl) ⟨1110017, by rfl⟩ : syracuseStep 1480023 = 2220035) B2220035
theorem B2807129 : Blo 1478559 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B1480043 : Blo 1478559 1480043 := bstep (se 1 (by rfl) ⟨1110032, by rfl⟩ : syracuseStep 1480043 = 2220065) B2220065
theorem B1480055 : Blo 1478559 1480055 := bstep (se 1 (by rfl) ⟨1110041, by rfl⟩ : syracuseStep 1480055 = 2220083) B2220083
theorem B1480075 : Blo 1478559 1480075 := bstep (se 1 (by rfl) ⟨1110056, by rfl⟩ : syracuseStep 1480075 = 2220113) B2220113
theorem B1480087 : Blo 1478559 1480087 := bstep (se 1 (by rfl) ⟨1110065, by rfl⟩ : syracuseStep 1480087 = 2220131) B2220131
theorem B1480107 : Blo 1478559 1480107 := bstep (se 1 (by rfl) ⟨1110080, by rfl⟩ : syracuseStep 1480107 = 2220161) B2220161
theorem B1480119 : Blo 1478559 1480119 := bstep (se 1 (by rfl) ⟨1110089, by rfl⟩ : syracuseStep 1480119 = 2220179) B2220179
theorem B2495947 : Blo 1478559 2495947 := bstep (se 1 (by rfl) ⟨1871960, by rfl⟩ : syracuseStep 2495947 = 3743921) B3743921
theorem B1480139 : Blo 1478559 1480139 := bstep (se 1 (by rfl) ⟨1110104, by rfl⟩ : syracuseStep 1480139 = 2220209) B2220209
theorem B1480151 : Blo 1478559 1480151 := bstep (se 1 (by rfl) ⟨1110113, by rfl⟩ : syracuseStep 1480151 = 2220227) B2220227
theorem B1480171 : Blo 1478559 1480171 := bstep (se 1 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 1480171 = 2220257) B2220257
theorem B1480183 : Blo 1478559 1480183 := bstep (se 1 (by rfl) ⟨1110137, by rfl⟩ : syracuseStep 1480183 = 2220275) B2220275
theorem B1480203 : Blo 1478559 1480203 := bstep (se 1 (by rfl) ⟨1110152, by rfl⟩ : syracuseStep 1480203 = 2220305) B2220305
theorem B1480215 : Blo 1478559 1480215 := bstep (se 1 (by rfl) ⟨1110161, by rfl⟩ : syracuseStep 1480215 = 2220323) B2220323
theorem B1480235 : Blo 1478559 1480235 := bstep (se 1 (by rfl) ⟨1110176, by rfl⟩ : syracuseStep 1480235 = 2220353) B2220353
theorem B1480247 : Blo 1478559 1480247 := bstep (se 1 (by rfl) ⟨1110185, by rfl⟩ : syracuseStep 1480247 = 2220371) B2220371
theorem B1480267 : Blo 1478559 1480267 := bstep (se 1 (by rfl) ⟨1110200, by rfl⟩ : syracuseStep 1480267 = 2220401) B2220401
theorem B1480279 : Blo 1478559 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B2496089 : Blo 1478559 2496089 := bstep (se 2 (by rfl) ⟨936033, by rfl⟩ : syracuseStep 2496089 = 1872067) B1872067
theorem B1480299 : Blo 1478559 1480299 := bstep (se 1 (by rfl) ⟨1110224, by rfl⟩ : syracuseStep 1480299 = 2220449) B2220449
theorem B1480311 : Blo 1478559 1480311 := bstep (se 1 (by rfl) ⟨1110233, by rfl⟩ : syracuseStep 1480311 = 2220467) B2220467
theorem B1480331 : Blo 1478559 1480331 := bstep (se 1 (by rfl) ⟨1110248, by rfl⟩ : syracuseStep 1480331 = 2220497) B2220497
theorem B1480343 : Blo 1478559 1480343 := bstep (se 1 (by rfl) ⟨1110257, by rfl⟩ : syracuseStep 1480343 = 2220515) B2220515
theorem B1480363 : Blo 1478559 1480363 := bstep (se 1 (by rfl) ⟨1110272, by rfl⟩ : syracuseStep 1480363 = 2220545) B2220545
theorem B1480375 : Blo 1478559 1480375 := bstep (se 1 (by rfl) ⟨1110281, by rfl⟩ : syracuseStep 1480375 = 2220563) B2220563
theorem B1480395 : Blo 1478559 1480395 := bstep (se 1 (by rfl) ⟨1110296, by rfl⟩ : syracuseStep 1480395 = 2220593) B2220593
theorem B1480407 : Blo 1478559 1480407 := bstep (se 1 (by rfl) ⟨1110305, by rfl⟩ : syracuseStep 1480407 = 2220611) B2220611
theorem B2496217 : Blo 1478559 2496217 := bstep (se 2 (by rfl) ⟨936081, by rfl⟩ : syracuseStep 2496217 = 1872163) B1872163
theorem B1480427 : Blo 1478559 1480427 := bstep (se 1 (by rfl) ⟨1110320, by rfl⟩ : syracuseStep 1480427 = 2220641) B2220641
theorem B1480439 : Blo 1478559 1480439 := bstep (se 1 (by rfl) ⟨1110329, by rfl⟩ : syracuseStep 1480439 = 2220659) B2220659
theorem B1480459 : Blo 1478559 1480459 := bstep (se 1 (by rfl) ⟨1110344, by rfl⟩ : syracuseStep 1480459 = 2220689) B2220689
theorem B1873687 : Blo 1478559 1873687 := bstep (se 1 (by rfl) ⟨1405265, by rfl⟩ : syracuseStep 1873687 = 2810531) B2810531
theorem B1480471 : Blo 1478559 1480471 := bstep (se 1 (by rfl) ⟨1110353, by rfl⟩ : syracuseStep 1480471 = 2220707) B2220707
theorem B1480491 : Blo 1478559 1480491 := bstep (se 1 (by rfl) ⟨1110368, by rfl⟩ : syracuseStep 1480491 = 2220737) B2220737
theorem B1480503 : Blo 1478559 1480503 := bstep (se 1 (by rfl) ⟨1110377, by rfl⟩ : syracuseStep 1480503 = 2220755) B2220755
theorem B4994891 : Blo 1478559 4994891 := bstep (se 1 (by rfl) ⟨3746168, by rfl⟩ : syracuseStep 4994891 = 7492337) B7492337
theorem B1480523 : Blo 1478559 1480523 := bstep (se 1 (by rfl) ⟨1110392, by rfl⟩ : syracuseStep 1480523 = 2220785) B2220785
theorem B1480535 : Blo 1478559 1480535 := bstep (se 1 (by rfl) ⟨1110401, by rfl⟩ : syracuseStep 1480535 = 2220803) B2220803
theorem B11229029 : Blo 1478559 11229029 := bstep (se 4 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 11229029 = 2105443) B2105443
theorem B1480555 : Blo 1478559 1480555 := bstep (se 1 (by rfl) ⟨1110416, by rfl⟩ : syracuseStep 1480555 = 2220833) B2220833
theorem B2217881 : Blo 1478559 2217881 := bstep (se 2 (by rfl) ⟨831705, by rfl⟩ : syracuseStep 2217881 = 1663411) B1663411
theorem B4741067 : Blo 1478559 4741067 := bstep (se 1 (by rfl) ⟨3555800, by rfl⟩ : syracuseStep 4741067 = 7111601) B7111601
theorem B2217995 : Blo 1478559 2217995 := bstep (se 1 (by rfl) ⟨1663496, by rfl⟩ : syracuseStep 2217995 = 3326993) B3326993
theorem B2218007 : Blo 1478559 2218007 := bstep (se 1 (by rfl) ⟨1663505, by rfl⟩ : syracuseStep 2218007 = 3327011) B3327011
theorem B2250775 : Blo 1478559 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B30365765 : Blo 1478559 30365765 := bstep (se 4 (by rfl) ⟨2846790, by rfl⟩ : syracuseStep 30365765 = 5693581) B5693581
theorem B2218073 : Blo 1478559 2218073 := bstep (se 2 (by rfl) ⟨831777, by rfl⟩ : syracuseStep 2218073 = 1663555) B1663555
theorem B4995161 : Blo 1478559 4995161 := bstep (se 2 (by rfl) ⟨1873185, by rfl⟩ : syracuseStep 4995161 = 3746371) B3746371
theorem B7485533 : Blo 1478559 7485533 := bstep (se 3 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 7485533 = 2807075) B2807075
theorem B9476189 : Blo 1478559 9476189 := bstep (se 3 (by rfl) ⟨1776785, by rfl⟩ : syracuseStep 9476189 = 3553571) B3553571
theorem B5617795 : Blo 1478559 5617795 := bstep (se 1 (by rfl) ⟨4213346, by rfl⟩ : syracuseStep 5617795 = 8426693) B8426693
theorem B2218187 : Blo 1478559 2218187 := bstep (se 1 (by rfl) ⟨1663640, by rfl⟩ : syracuseStep 2218187 = 3327281) B3327281
theorem B2218199 : Blo 1478559 2218199 := bstep (se 1 (by rfl) ⟨1663649, by rfl⟩ : syracuseStep 2218199 = 3327299) B3327299
theorem B2496791 : Blo 1478559 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B2218265 : Blo 1478559 2218265 := bstep (se 2 (by rfl) ⟨831849, by rfl⟩ : syracuseStep 2218265 = 1663699) B1663699
theorem B11229515 : Blo 1478559 11229515 := bstep (se 1 (by rfl) ⟨8422136, by rfl⟩ : syracuseStep 11229515 = 16844273) B16844273
theorem B1579339 : Blo 1478559 1579339 := bstep (se 1 (by rfl) ⟨1184504, by rfl⟩ : syracuseStep 1579339 = 2369009) B2369009
theorem B2218379 : Blo 1478559 2218379 := bstep (se 1 (by rfl) ⟨1663784, by rfl⟩ : syracuseStep 2218379 = 3327569) B3327569
theorem B2218391 : Blo 1478559 2218391 := bstep (se 1 (by rfl) ⟨1663793, by rfl⟩ : syracuseStep 2218391 = 3327587) B3327587
theorem B2496919 : Blo 1478559 2496919 := bstep (se 1 (by rfl) ⟨1872689, by rfl⟩ : syracuseStep 2496919 = 3745379) B3745379
theorem B5618099 : Blo 1478559 5618099 := bstep (se 1 (by rfl) ⟨4213574, by rfl⟩ : syracuseStep 5618099 = 8427149) B8427149
theorem B2218457 : Blo 1478559 2218457 := bstep (se 2 (by rfl) ⟨831921, by rfl⟩ : syracuseStep 2218457 = 1663843) B1663843
theorem B5331479 : Blo 1478559 5331479 := bstep (se 1 (by rfl) ⟨3998609, by rfl⟩ : syracuseStep 5331479 = 7997219) B7997219
theorem B2701849 : Blo 1478559 2701849 := bstep (se 2 (by rfl) ⟨1013193, by rfl⟩ : syracuseStep 2701849 = 2026387) B2026387
theorem B11999789 : Blo 1478559 11999789 := bstep (se 3 (by rfl) ⟨2249960, by rfl⟩ : syracuseStep 11999789 = 4499921) B4499921
theorem B2218571 : Blo 1478559 2218571 := bstep (se 1 (by rfl) ⟨1663928, by rfl⟩ : syracuseStep 2218571 = 3327857) B3327857
theorem B1579595 : Blo 1478559 1579595 := bstep (se 1 (by rfl) ⟨1184696, by rfl⟩ : syracuseStep 1579595 = 2369393) B2369393
theorem B2218583 : Blo 1478559 2218583 := bstep (se 1 (by rfl) ⟨1663937, by rfl⟩ : syracuseStep 2218583 = 3327875) B3327875
theorem B9484951 : Blo 1478559 9484951 := bstep (se 1 (by rfl) ⟨7113713, by rfl⟩ : syracuseStep 9484951 = 14227427) B14227427
theorem B2218649 : Blo 1478559 2218649 := bstep (se 2 (by rfl) ⟨831993, by rfl⟩ : syracuseStep 2218649 = 1663987) B1663987
theorem B4741811 : Blo 1478559 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B2218763 : Blo 1478559 2218763 := bstep (se 1 (by rfl) ⟨1664072, by rfl⟩ : syracuseStep 2218763 = 3328145) B3328145
theorem B2808587 : Blo 1478559 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B2218775 : Blo 1478559 2218775 := bstep (se 1 (by rfl) ⟨1664081, by rfl⟩ : syracuseStep 2218775 = 3328163) B3328163
theorem B4995863 : Blo 1478559 4995863 := bstep (se 1 (by rfl) ⟨3746897, by rfl⟩ : syracuseStep 4995863 = 7493795) B7493795
theorem B8428333 : Blo 1478559 8428333 := bstep (se 3 (by rfl) ⟨1580312, by rfl⟩ : syracuseStep 8428333 = 3160625) B3160625
theorem B2218841 : Blo 1478559 2218841 := bstep (se 2 (by rfl) ⟨832065, by rfl⟩ : syracuseStep 2218841 = 1664131) B1664131
theorem B2808769 : Blo 1478559 2808769 := bstep (se 2 (by rfl) ⟨1053288, by rfl⟩ : syracuseStep 2808769 = 2106577) B2106577
theorem B2218955 : Blo 1478559 2218955 := bstep (se 1 (by rfl) ⟨1664216, by rfl⟩ : syracuseStep 2218955 = 3328433) B3328433
theorem B3161035 : Blo 1478559 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B2218967 : Blo 1478559 2218967 := bstep (se 1 (by rfl) ⟨1664225, by rfl⟩ : syracuseStep 2218967 = 3328451) B3328451
theorem B2497547 : Blo 1478559 2497547 := bstep (se 1 (by rfl) ⟨1873160, by rfl⟩ : syracuseStep 2497547 = 3746321) B3746321
theorem B2219033 : Blo 1478559 2219033 := bstep (se 2 (by rfl) ⟨832137, by rfl⟩ : syracuseStep 2219033 = 1664275) B1664275
theorem B5618753 : Blo 1478559 5618753 := bstep (se 2 (by rfl) ⟨2107032, by rfl⟩ : syracuseStep 5618753 = 4214065) B4214065
theorem B5332043 : Blo 1478559 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B2219147 : Blo 1478559 2219147 := bstep (se 1 (by rfl) ⟨1664360, by rfl⟩ : syracuseStep 2219147 = 3328721) B3328721
theorem B2497675 : Blo 1478559 2497675 := bstep (se 1 (by rfl) ⟨1873256, by rfl⟩ : syracuseStep 2497675 = 3746513) B3746513
theorem B2219159 : Blo 1478559 2219159 := bstep (se 1 (by rfl) ⟨1664369, by rfl⟩ : syracuseStep 2219159 = 3328739) B3328739
theorem B2219225 : Blo 1478559 2219225 := bstep (se 2 (by rfl) ⟨832209, by rfl⟩ : syracuseStep 2219225 = 1664419) B1664419
theorem B7494929 : Blo 1478559 7494929 := bstep (se 2 (by rfl) ⟨2810598, by rfl⟩ : syracuseStep 7494929 = 5621197) B5621197
theorem B2497817 : Blo 1478559 2497817 := bstep (se 2 (by rfl) ⟨936681, by rfl⟩ : syracuseStep 2497817 = 1873363) B1873363
theorem B3161369 : Blo 1478559 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B6323507 : Blo 1478559 6323507 := bstep (se 1 (by rfl) ⟨4742630, by rfl⟩ : syracuseStep 6323507 = 9485261) B9485261
theorem B4996403 : Blo 1478559 4996403 := bstep (se 1 (by rfl) ⟨3747302, by rfl⟩ : syracuseStep 4996403 = 7494605) B7494605
theorem B13491521 : Blo 1478559 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B12639563 : Blo 1478559 12639563 := bstep (se 1 (by rfl) ⟨9479672, by rfl⟩ : syracuseStep 12639563 = 18959345) B18959345
theorem B2219339 : Blo 1478559 2219339 := bstep (se 1 (by rfl) ⟨1664504, by rfl⟩ : syracuseStep 2219339 = 3329009) B3329009
theorem B2219351 : Blo 1478559 2219351 := bstep (se 1 (by rfl) ⟨1664513, by rfl⟩ : syracuseStep 2219351 = 3329027) B3329027
theorem B11238749 : Blo 1478559 11238749 := bstep (se 3 (by rfl) ⟨2107265, by rfl⟩ : syracuseStep 11238749 = 4214531) B4214531
theorem B2809217 : Blo 1478559 2809217 := bstep (se 2 (by rfl) ⟨1053456, by rfl⟩ : syracuseStep 2809217 = 2106913) B2106913
theorem B2219417 : Blo 1478559 2219417 := bstep (se 2 (by rfl) ⟨832281, by rfl⟩ : syracuseStep 2219417 = 1664563) B1664563
theorem B2497945 : Blo 1478559 2497945 := bstep (se 2 (by rfl) ⟨936729, by rfl⟩ : syracuseStep 2497945 = 1873459) B1873459
theorem B7495091 : Blo 1478559 7495091 := bstep (se 1 (by rfl) ⟨5621318, by rfl⟩ : syracuseStep 7495091 = 11242637) B11242637
theorem B2219531 : Blo 1478559 2219531 := bstep (se 1 (by rfl) ⟨1664648, by rfl⟩ : syracuseStep 2219531 = 3329297) B3329297
theorem B2219543 : Blo 1478559 2219543 := bstep (se 1 (by rfl) ⟨1664657, by rfl⟩ : syracuseStep 2219543 = 3329315) B3329315
theorem B4742707 : Blo 1478559 4742707 := bstep (se 1 (by rfl) ⟨3557030, by rfl⟩ : syracuseStep 4742707 = 7114061) B7114061
theorem B4996673 : Blo 1478559 4996673 := bstep (se 2 (by rfl) ⟨1873752, by rfl⟩ : syracuseStep 4996673 = 3747505) B3747505
theorem B2219609 : Blo 1478559 2219609 := bstep (se 2 (by rfl) ⟨832353, by rfl⟩ : syracuseStep 2219609 = 1664707) B1664707
theorem B8421043 : Blo 1478559 8421043 := bstep (se 1 (by rfl) ⟨6315782, by rfl⟩ : syracuseStep 8421043 = 12631565) B12631565
theorem B3743435 : Blo 1478559 3743435 := bstep (se 1 (by rfl) ⟨2807576, by rfl⟩ : syracuseStep 3743435 = 5615153) B5615153
theorem B2219723 : Blo 1478559 2219723 := bstep (se 1 (by rfl) ⟨1664792, by rfl⟩ : syracuseStep 2219723 = 3329585) B3329585
theorem B28458701 : Blo 1478559 28458701 := bstep (se 3 (by rfl) ⟨5336006, by rfl⟩ : syracuseStep 28458701 = 10672013) B10672013
theorem B2219735 : Blo 1478559 2219735 := bstep (se 1 (by rfl) ⟨1664801, by rfl⟩ : syracuseStep 2219735 = 3329603) B3329603
theorem B2809559 : Blo 1478559 2809559 := bstep (se 1 (by rfl) ⟨2107169, by rfl⟩ : syracuseStep 2809559 = 4214339) B4214339
theorem B2531083 : Blo 1478559 2531083 := bstep (se 1 (by rfl) ⟨1898312, by rfl⟩ : syracuseStep 2531083 = 3796625) B3796625
theorem B2219801 : Blo 1478559 2219801 := bstep (se 2 (by rfl) ⟨832425, by rfl⟩ : syracuseStep 2219801 = 1664851) B1664851
theorem B3997529 : Blo 1478559 3997529 := bstep (se 2 (by rfl) ⟨1499073, by rfl⟩ : syracuseStep 3997529 = 2998147) B2998147
theorem B5062493 : Blo 1478559 5062493 := bstep (se 3 (by rfl) ⟨949217, by rfl⟩ : syracuseStep 5062493 = 1898435) B1898435
theorem B2105227 : Blo 1478559 2105227 := bstep (se 1 (by rfl) ⟨1578920, by rfl⟩ : syracuseStep 2105227 = 3157841) B3157841
theorem B2219915 : Blo 1478559 2219915 := bstep (se 1 (by rfl) ⟨1664936, by rfl⟩ : syracuseStep 2219915 = 3329873) B3329873
theorem B2219927 : Blo 1478559 2219927 := bstep (se 1 (by rfl) ⟨1664945, by rfl⟩ : syracuseStep 2219927 = 3329891) B3329891
theorem B15998897 : Blo 1478559 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B40468403 : Blo 1478559 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B2219993 : Blo 1478559 2219993 := bstep (se 2 (by rfl) ⟨832497, by rfl⟩ : syracuseStep 2219993 = 1664995) B1664995
theorem B3743759 : Blo 1478559 3743759 := bstep (se 1 (by rfl) ⟨2807819, by rfl⟩ : syracuseStep 3743759 = 5615639) B5615639
theorem B2220047 : Blo 1478559 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B2310187 : Blo 1478559 2310187 := bstep (se 1 (by rfl) ⟨1732640, by rfl⟩ : syracuseStep 2310187 = 3465281) B3465281
theorem B2220089 : Blo 1478559 2220089 := bstep (se 2 (by rfl) ⟨832533, by rfl⟩ : syracuseStep 2220089 = 1665067) B1665067
theorem B2220167 : Blo 1478559 2220167 := bstep (se 1 (by rfl) ⟨1665125, by rfl⟩ : syracuseStep 2220167 = 3330251) B3330251
theorem B2809991 : Blo 1478559 2809991 := bstep (se 1 (by rfl) ⟨2107493, by rfl⟩ : syracuseStep 2809991 = 4214987) B4214987
theorem B3743891 : Blo 1478559 3743891 := bstep (se 1 (by rfl) ⟨2807918, by rfl⟩ : syracuseStep 3743891 = 5615837) B5615837
theorem B4210841 : Blo 1478559 4210841 := bstep (se 2 (by rfl) ⟨1579065, by rfl⟩ : syracuseStep 4210841 = 3158131) B3158131
theorem B2220203 : Blo 1478559 2220203 := bstep (se 1 (by rfl) ⟨1665152, by rfl⟩ : syracuseStep 2220203 = 3330305) B3330305
theorem B8421569 : Blo 1478559 8421569 := bstep (se 2 (by rfl) ⟨3158088, by rfl⟩ : syracuseStep 8421569 = 6316177) B6316177
theorem B2220233 : Blo 1478559 2220233 := bstep (se 2 (by rfl) ⟨832587, by rfl⟩ : syracuseStep 2220233 = 1665175) B1665175
theorem B2220347 : Blo 1478559 2220347 := bstep (se 1 (by rfl) ⟨1665260, by rfl⟩ : syracuseStep 2220347 = 3330521) B3330521
theorem B4055357 : Blo 1478559 4055357 := bstep (se 3 (by rfl) ⟨760379, by rfl⟩ : syracuseStep 4055357 = 1520759) B1520759
theorem B2220407 : Blo 1478559 2220407 := bstep (se 1 (by rfl) ⟨1665305, by rfl⟩ : syracuseStep 2220407 = 3330611) B3330611
theorem B2220431 : Blo 1478559 2220431 := bstep (se 1 (by rfl) ⟨1665323, by rfl⟩ : syracuseStep 2220431 = 3330647) B3330647
theorem B2105785 : Blo 1478559 2105785 := bstep (se 2 (by rfl) ⟨789669, by rfl⟩ : syracuseStep 2105785 = 1579339) B1579339
theorem B2220473 : Blo 1478559 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B2220551 : Blo 1478559 2220551 := bstep (se 1 (by rfl) ⟨1665413, by rfl⟩ : syracuseStep 2220551 = 3330827) B3330827
theorem B2220587 : Blo 1478559 2220587 := bstep (se 1 (by rfl) ⟨1665440, by rfl⟩ : syracuseStep 2220587 = 3330881) B3330881
theorem B2220617 : Blo 1478559 2220617 := bstep (se 2 (by rfl) ⟨832731, by rfl⟩ : syracuseStep 2220617 = 1665463) B1665463
theorem B2220731 : Blo 1478559 2220731 := bstep (se 1 (by rfl) ⟨1665548, by rfl⟩ : syracuseStep 2220731 = 3331097) B3331097
theorem B8430317 : Blo 1478559 8430317 := bstep (se 3 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 8430317 = 3161369) B3161369
theorem B2220791 : Blo 1478559 2220791 := bstep (se 1 (by rfl) ⟨1665593, by rfl⟩ : syracuseStep 2220791 = 3331187) B3331187
theorem B11240207 : Blo 1478559 11240207 := bstep (se 1 (by rfl) ⟨8430155, by rfl⟩ : syracuseStep 11240207 = 16860311) B16860311
theorem B2220815 : Blo 1478559 2220815 := bstep (se 1 (by rfl) ⟨1665611, by rfl⟩ : syracuseStep 2220815 = 3331223) B3331223
theorem B1663879 : Blo 1478559 1663879 := bstep (se 1 (by rfl) ⟨1247909, by rfl⟩ : syracuseStep 1663879 = 2495819) B2495819
theorem B3326867 : Blo 1478559 3326867 := bstep (se 1 (by rfl) ⟨2495150, by rfl⟩ : syracuseStep 3326867 = 4990301) B4990301
theorem B3326921 : Blo 1478559 3326921 := bstep (se 2 (by rfl) ⟨1247595, by rfl⟩ : syracuseStep 3326921 = 2495191) B2495191
theorem B1664059 : Blo 1478559 1664059 := bstep (se 1 (by rfl) ⟨1248044, by rfl⟩ : syracuseStep 1664059 = 2496089) B2496089
theorem B3745025 : Blo 1478559 3745025 := bstep (se 2 (by rfl) ⟨1404384, by rfl⟩ : syracuseStep 3745025 = 2808769) B2808769
theorem B4621627 : Blo 1478559 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B3556723 : Blo 1478559 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B20243843 : Blo 1478559 20243843 := bstep (se 1 (by rfl) ⟨15182882, by rfl⟩ : syracuseStep 20243843 = 30365765) B30365765
theorem B12633479 : Blo 1478559 12633479 := bstep (se 1 (by rfl) ⟨9475109, by rfl⟩ : syracuseStep 12633479 = 18950219) B18950219
theorem B4990355 : Blo 1478559 4990355 := bstep (se 1 (by rfl) ⟨3742766, by rfl⟩ : syracuseStep 4990355 = 7485533) B7485533
theorem B6317459 : Blo 1478559 6317459 := bstep (se 1 (by rfl) ⟨4738094, by rfl⟩ : syracuseStep 6317459 = 9476189) B9476189
theorem B1664527 : Blo 1478559 1664527 := bstep (se 1 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 1664527 = 2496791) B2496791
theorem B7112215 : Blo 1478559 7112215 := bstep (se 1 (by rfl) ⟨5334161, by rfl⟩ : syracuseStep 7112215 = 10668323) B10668323
theorem B4212253 : Blo 1478559 4212253 := bstep (se 3 (by rfl) ⟨789797, by rfl⟩ : syracuseStep 4212253 = 1579595) B1579595
theorem B3745399 : Blo 1478559 3745399 := bstep (se 1 (by rfl) ⟨2809049, by rfl⟩ : syracuseStep 3745399 = 5618099) B5618099
theorem B3327623 : Blo 1478559 3327623 := bstep (se 1 (by rfl) ⟨2495717, by rfl⟩ : syracuseStep 3327623 = 4991435) B4991435
theorem B4212425 : Blo 1478559 4212425 := bstep (se 2 (by rfl) ⟨1579659, by rfl⟩ : syracuseStep 4212425 = 3159319) B3159319
theorem B4212481 : Blo 1478559 4212481 := bstep (se 2 (by rfl) ⟨1579680, by rfl⟩ : syracuseStep 4212481 = 3159361) B3159361
theorem B5998369 : Blo 1478559 5998369 := bstep (se 2 (by rfl) ⟨2249388, by rfl⟩ : syracuseStep 5998369 = 4498777) B4498777
theorem B3327803 : Blo 1478559 3327803 := bstep (se 1 (by rfl) ⟨2495852, by rfl⟩ : syracuseStep 3327803 = 4991705) B4991705
theorem B3327929 : Blo 1478559 3327929 := bstep (se 2 (by rfl) ⟨1247973, by rfl⟩ : syracuseStep 3327929 = 2495947) B2495947
theorem B7997393 : Blo 1478559 7997393 := bstep (se 2 (by rfl) ⟨2999022, by rfl⟩ : syracuseStep 7997393 = 5998045) B5998045
theorem B1665031 : Blo 1478559 1665031 := bstep (se 1 (by rfl) ⟨1248773, by rfl⟩ : syracuseStep 1665031 = 2497547) B2497547
theorem B8538155 : Blo 1478559 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B3745835 : Blo 1478559 3745835 := bstep (se 1 (by rfl) ⟨2809376, by rfl⟩ : syracuseStep 3745835 = 5618753) B5618753
theorem B4212823 : Blo 1478559 4212823 := bstep (se 1 (by rfl) ⟨3159617, by rfl⟩ : syracuseStep 4212823 = 6319235) B6319235
theorem B1665211 : Blo 1478559 1665211 := bstep (se 1 (by rfl) ⟨1248908, by rfl⟩ : syracuseStep 1665211 = 2497817) B2497817
theorem B3328271 : Blo 1478559 3328271 := bstep (se 1 (by rfl) ⟨2496203, by rfl⟩ : syracuseStep 3328271 = 4992407) B4992407
theorem B3328289 : Blo 1478559 3328289 := bstep (se 2 (by rfl) ⟨1248108, by rfl⟩ : syracuseStep 3328289 = 2496217) B2496217
theorem B7489907 : Blo 1478559 7489907 := bstep (se 1 (by rfl) ⟨5617430, by rfl⟩ : syracuseStep 7489907 = 11234861) B11234861
theorem B8423959 : Blo 1478559 8423959 := bstep (se 1 (by rfl) ⟨6317969, by rfl⟩ : syracuseStep 8423959 = 12635939) B12635939
theorem B2665019 : Blo 1478559 2665019 := bstep (se 1 (by rfl) ⟨1998764, by rfl⟩ : syracuseStep 2665019 = 3997529) B3997529
theorem B26978935 : Blo 1478559 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B3328631 : Blo 1478559 3328631 := bstep (se 1 (by rfl) ⟨2496473, by rfl⟩ : syracuseStep 3328631 = 4992947) B4992947
theorem B3001033 : Blo 1478559 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B4991759 : Blo 1478559 4991759 := bstep (se 1 (by rfl) ⟨3743819, by rfl⟩ : syracuseStep 4991759 = 7487639) B7487639
theorem B3328811 : Blo 1478559 3328811 := bstep (se 1 (by rfl) ⟨2496608, by rfl⟩ : syracuseStep 3328811 = 4993217) B4993217
theorem B7490393 : Blo 1478559 7490393 := bstep (se 2 (by rfl) ⟨2808897, by rfl⟩ : syracuseStep 7490393 = 5617795) B5617795
theorem B3746675 : Blo 1478559 3746675 := bstep (se 1 (by rfl) ⟨2810006, by rfl⟩ : syracuseStep 3746675 = 5620013) B5620013
theorem B3746695 : Blo 1478559 3746695 := bstep (se 1 (by rfl) ⟨2810021, by rfl⟩ : syracuseStep 3746695 = 5620043) B5620043
theorem B16845731 : Blo 1478559 16845731 := bstep (se 1 (by rfl) ⟨12634298, by rfl⟩ : syracuseStep 16845731 = 25268597) B25268597
theorem B4992029 : Blo 1478559 4992029 := bstep (se 3 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 4992029 = 1872011) B1872011
theorem B6319133 : Blo 1478559 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B3329171 : Blo 1478559 3329171 := bstep (se 1 (by rfl) ⟨2496878, by rfl⟩ : syracuseStep 3329171 = 4993757) B4993757
theorem B3746969 : Blo 1478559 3746969 := bstep (se 2 (by rfl) ⟨1405113, by rfl⟩ : syracuseStep 3746969 = 2810227) B2810227
theorem B3329225 : Blo 1478559 3329225 := bstep (se 2 (by rfl) ⟨1248459, by rfl⟩ : syracuseStep 3329225 = 2496919) B2496919
theorem B3747131 : Blo 1478559 3747131 := bstep (se 1 (by rfl) ⟨2810348, by rfl⟩ : syracuseStep 3747131 = 5620697) B5620697
theorem B3747343 : Blo 1478559 3747343 := bstep (se 1 (by rfl) ⟨2810507, by rfl⟩ : syracuseStep 3747343 = 5621015) B5621015
theorem B1871419 : Blo 1478559 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B3747617 : Blo 1478559 3747617 := bstep (se 2 (by rfl) ⟨1405356, by rfl⟩ : syracuseStep 3747617 = 2810713) B2810713
theorem B15986483 : Blo 1478559 15986483 := bstep (se 1 (by rfl) ⟨11989862, by rfl⟩ : syracuseStep 15986483 = 23979725) B23979725
theorem B7409497 : Blo 1478559 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B2666375 : Blo 1478559 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B3329927 : Blo 1478559 3329927 := bstep (se 1 (by rfl) ⟨2497445, by rfl⟩ : syracuseStep 3329927 = 4994891) B4994891
theorem B1478587 : Blo 1478559 1478587 := bstep (se 1 (by rfl) ⟨1108940, by rfl⟩ : syracuseStep 1478587 = 2217881) B2217881
theorem B1478663 : Blo 1478559 1478663 := bstep (se 1 (by rfl) ⟨1108997, by rfl⟩ : syracuseStep 1478663 = 2217995) B2217995
theorem B1478671 : Blo 1478559 1478671 := bstep (se 1 (by rfl) ⟨1109003, by rfl⟩ : syracuseStep 1478671 = 2218007) B2218007
theorem B1478715 : Blo 1478559 1478715 := bstep (se 1 (by rfl) ⟨1109036, by rfl⟩ : syracuseStep 1478715 = 2218073) B2218073
theorem B3330107 : Blo 1478559 3330107 := bstep (se 1 (by rfl) ⟨2497580, by rfl⟩ : syracuseStep 3330107 = 4995161) B4995161
theorem B14217277 : Blo 1478559 14217277 := bstep (se 3 (by rfl) ⟨2665739, by rfl⟩ : syracuseStep 14217277 = 5331479) B5331479
theorem B1478791 : Blo 1478559 1478791 := bstep (se 1 (by rfl) ⟨1109093, by rfl⟩ : syracuseStep 1478791 = 2218187) B2218187
theorem B1478799 : Blo 1478559 1478799 := bstep (se 1 (by rfl) ⟨1109099, by rfl⟩ : syracuseStep 1478799 = 2218199) B2218199
theorem B3330233 : Blo 1478559 3330233 := bstep (se 2 (by rfl) ⟨1248837, by rfl⟩ : syracuseStep 3330233 = 2497675) B2497675
theorem B1478843 : Blo 1478559 1478843 := bstep (se 1 (by rfl) ⟨1109132, by rfl⟩ : syracuseStep 1478843 = 2218265) B2218265
theorem B6410477 : Blo 1478559 6410477 := bstep (se 3 (by rfl) ⟨1201964, by rfl⟩ : syracuseStep 6410477 = 2403929) B2403929
theorem B35983601 : Blo 1478559 35983601 := bstep (se 2 (by rfl) ⟨13493850, by rfl⟩ : syracuseStep 35983601 = 26987701) B26987701
theorem B1478919 : Blo 1478559 1478919 := bstep (se 1 (by rfl) ⟨1109189, by rfl⟩ : syracuseStep 1478919 = 2218379) B2218379
theorem B1478927 : Blo 1478559 1478927 := bstep (se 1 (by rfl) ⟨1109195, by rfl⟩ : syracuseStep 1478927 = 2218391) B2218391
theorem B1478971 : Blo 1478559 1478971 := bstep (se 1 (by rfl) ⟨1109228, by rfl⟩ : syracuseStep 1478971 = 2218457) B2218457
theorem B7999859 : Blo 1478559 7999859 := bstep (se 1 (by rfl) ⟨5999894, by rfl⟩ : syracuseStep 7999859 = 11999789) B11999789
theorem B1479047 : Blo 1478559 1479047 := bstep (se 1 (by rfl) ⟨1109285, by rfl⟩ : syracuseStep 1479047 = 2218571) B2218571
theorem B1479055 : Blo 1478559 1479055 := bstep (se 1 (by rfl) ⟨1109291, by rfl⟩ : syracuseStep 1479055 = 2218583) B2218583
theorem B4993433 : Blo 1478559 4993433 := bstep (se 2 (by rfl) ⟨1872537, by rfl⟩ : syracuseStep 4993433 = 3745075) B3745075
theorem B1479099 : Blo 1478559 1479099 := bstep (se 1 (by rfl) ⟨1109324, by rfl⟩ : syracuseStep 1479099 = 2218649) B2218649
theorem B3158473 : Blo 1478559 3158473 := bstep (se 2 (by rfl) ⟨1184427, by rfl⟩ : syracuseStep 3158473 = 2368855) B2368855
theorem B1479175 : Blo 1478559 1479175 := bstep (se 1 (by rfl) ⟨1109381, by rfl⟩ : syracuseStep 1479175 = 2218763) B2218763
theorem B1872391 : Blo 1478559 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B1479183 : Blo 1478559 1479183 := bstep (se 1 (by rfl) ⟨1109387, by rfl⟩ : syracuseStep 1479183 = 2218775) B2218775
theorem B3330575 : Blo 1478559 3330575 := bstep (se 1 (by rfl) ⟨2497931, by rfl⟩ : syracuseStep 3330575 = 4995863) B4995863
theorem B3330593 : Blo 1478559 3330593 := bstep (se 2 (by rfl) ⟨1248972, by rfl⟩ : syracuseStep 3330593 = 2497945) B2497945
theorem B1479227 : Blo 1478559 1479227 := bstep (se 1 (by rfl) ⟨1109420, by rfl⟩ : syracuseStep 1479227 = 2218841) B2218841
theorem B1479303 : Blo 1478559 1479303 := bstep (se 1 (by rfl) ⟨1109477, by rfl⟩ : syracuseStep 1479303 = 2218955) B2218955
theorem B1479311 : Blo 1478559 1479311 := bstep (se 1 (by rfl) ⟨1109483, by rfl⟩ : syracuseStep 1479311 = 2218967) B2218967
theorem B1479355 : Blo 1478559 1479355 := bstep (se 1 (by rfl) ⟨1109516, by rfl⟩ : syracuseStep 1479355 = 2219033) B2219033
theorem B1479431 : Blo 1478559 1479431 := bstep (se 1 (by rfl) ⟨1109573, by rfl⟩ : syracuseStep 1479431 = 2219147) B2219147
theorem B1479439 : Blo 1478559 1479439 := bstep (se 1 (by rfl) ⟨1109579, by rfl⟩ : syracuseStep 1479439 = 2219159) B2219159
theorem B1479483 : Blo 1478559 1479483 := bstep (se 1 (by rfl) ⟨1109612, by rfl⟩ : syracuseStep 1479483 = 2219225) B2219225
theorem B26997619 : Blo 1478559 26997619 := bstep (se 1 (by rfl) ⟨20248214, by rfl⟩ : syracuseStep 26997619 = 40496429) B40496429
theorem B4215671 : Blo 1478559 4215671 := bstep (se 1 (by rfl) ⟨3161753, by rfl⟩ : syracuseStep 4215671 = 6323507) B6323507
theorem B3330935 : Blo 1478559 3330935 := bstep (se 1 (by rfl) ⟨2498201, by rfl⟩ : syracuseStep 3330935 = 4996403) B4996403
theorem B8426375 : Blo 1478559 8426375 := bstep (se 1 (by rfl) ⟨6319781, by rfl⟩ : syracuseStep 8426375 = 12639563) B12639563
theorem B1479559 : Blo 1478559 1479559 := bstep (se 1 (by rfl) ⟨1109669, by rfl⟩ : syracuseStep 1479559 = 2219339) B2219339
theorem B1479567 : Blo 1478559 1479567 := bstep (se 1 (by rfl) ⟨1109675, by rfl⟩ : syracuseStep 1479567 = 2219351) B2219351
theorem B7492499 : Blo 1478559 7492499 := bstep (se 1 (by rfl) ⟨5619374, by rfl⟩ : syracuseStep 7492499 = 11238749) B11238749
theorem B11228057 : Blo 1478559 11228057 := bstep (se 2 (by rfl) ⟨4210521, by rfl⟩ : syracuseStep 11228057 = 8421043) B8421043
theorem B1872811 : Blo 1478559 1872811 := bstep (se 1 (by rfl) ⟨1404608, by rfl⟩ : syracuseStep 1872811 = 2809217) B2809217
theorem B1479611 : Blo 1478559 1479611 := bstep (se 1 (by rfl) ⟨1109708, by rfl⟩ : syracuseStep 1479611 = 2219417) B2219417
theorem B1479687 : Blo 1478559 1479687 := bstep (se 1 (by rfl) ⟨1109765, by rfl⟩ : syracuseStep 1479687 = 2219531) B2219531
theorem B1479695 : Blo 1478559 1479695 := bstep (se 1 (by rfl) ⟨1109771, by rfl⟩ : syracuseStep 1479695 = 2219543) B2219543
theorem B3331115 : Blo 1478559 3331115 := bstep (se 1 (by rfl) ⟨2498336, by rfl⟩ : syracuseStep 3331115 = 4996673) B4996673
theorem B1479739 : Blo 1478559 1479739 := bstep (se 1 (by rfl) ⟨1109804, by rfl⟩ : syracuseStep 1479739 = 2219609) B2219609
theorem B4994135 : Blo 1478559 4994135 := bstep (se 1 (by rfl) ⟨3745601, by rfl⟩ : syracuseStep 4994135 = 7491203) B7491203
theorem B2495623 : Blo 1478559 2495623 := bstep (se 1 (by rfl) ⟨1871717, by rfl⟩ : syracuseStep 2495623 = 3743435) B3743435
theorem B1733767 : Blo 1478559 1733767 := bstep (se 1 (by rfl) ⟨1300325, by rfl⟩ : syracuseStep 1733767 = 2600651) B2600651
theorem B1479815 : Blo 1478559 1479815 := bstep (se 1 (by rfl) ⟨1109861, by rfl⟩ : syracuseStep 1479815 = 2219723) B2219723
theorem B1479823 : Blo 1478559 1479823 := bstep (se 1 (by rfl) ⟨1109867, by rfl⟩ : syracuseStep 1479823 = 2219735) B2219735
theorem B1873039 : Blo 1478559 1873039 := bstep (se 1 (by rfl) ⟨1404779, by rfl⟩ : syracuseStep 1873039 = 2809559) B2809559
theorem B2806969 : Blo 1478559 2806969 := bstep (se 2 (by rfl) ⟨1052613, by rfl⟩ : syracuseStep 2806969 = 2105227) B2105227
theorem B1479867 : Blo 1478559 1479867 := bstep (se 1 (by rfl) ⟨1109900, by rfl⟩ : syracuseStep 1479867 = 2219801) B2219801
theorem B1479943 : Blo 1478559 1479943 := bstep (se 1 (by rfl) ⟨1109957, by rfl⟩ : syracuseStep 1479943 = 2219915) B2219915
theorem B1479951 : Blo 1478559 1479951 := bstep (se 1 (by rfl) ⟨1109963, by rfl⟩ : syracuseStep 1479951 = 2219927) B2219927
theorem B22771003 : Blo 1478559 22771003 := bstep (se 1 (by rfl) ⟨17078252, by rfl⟩ : syracuseStep 22771003 = 34156505) B34156505
theorem B1479995 : Blo 1478559 1479995 := bstep (se 1 (by rfl) ⟨1109996, by rfl⟩ : syracuseStep 1479995 = 2219993) B2219993
theorem B30365027 : Blo 1478559 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B1480071 : Blo 1478559 1480071 := bstep (se 1 (by rfl) ⟨1110053, by rfl⟩ : syracuseStep 1480071 = 2220107) B2220107
theorem B1480079 : Blo 1478559 1480079 := bstep (se 1 (by rfl) ⟨1110059, by rfl⟩ : syracuseStep 1480079 = 2220119) B2220119
theorem B3159481 : Blo 1478559 3159481 := bstep (se 2 (by rfl) ⟨1184805, by rfl⟩ : syracuseStep 3159481 = 2369611) B2369611
theorem B1480123 : Blo 1478559 1480123 := bstep (se 1 (by rfl) ⟨1110092, by rfl⟩ : syracuseStep 1480123 = 2220185) B2220185
theorem B25286093 : Blo 1478559 25286093 := bstep (se 3 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 25286093 = 9482285) B9482285
theorem B1480199 : Blo 1478559 1480199 := bstep (se 1 (by rfl) ⟨1110149, by rfl⟩ : syracuseStep 1480199 = 2220299) B2220299
theorem B4740619 : Blo 1478559 4740619 := bstep (se 1 (by rfl) ⟨3555464, by rfl⟩ : syracuseStep 4740619 = 7110929) B7110929
theorem B2807311 : Blo 1478559 2807311 := bstep (se 1 (by rfl) ⟨2105483, by rfl⟩ : syracuseStep 2807311 = 4210967) B4210967
theorem B1480207 : Blo 1478559 1480207 := bstep (se 1 (by rfl) ⟨1110155, by rfl⟩ : syracuseStep 1480207 = 2220311) B2220311
theorem B20239901 : Blo 1478559 20239901 := bstep (se 3 (by rfl) ⟨3794981, by rfl⟩ : syracuseStep 20239901 = 7589963) B7589963
theorem B1480251 : Blo 1478559 1480251 := bstep (se 1 (by rfl) ⟨1110188, by rfl⟩ : syracuseStep 1480251 = 2220377) B2220377
theorem B4994621 : Blo 1478559 4994621 := bstep (se 3 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 4994621 = 1872983) B1872983
theorem B9475703 : Blo 1478559 9475703 := bstep (se 1 (by rfl) ⟨7106777, by rfl⟩ : syracuseStep 9475703 = 14213555) B14213555
theorem B1480327 : Blo 1478559 1480327 := bstep (se 1 (by rfl) ⟨1110245, by rfl⟩ : syracuseStep 1480327 = 2220491) B2220491
theorem B1480335 : Blo 1478559 1480335 := bstep (se 1 (by rfl) ⟨1110251, by rfl⟩ : syracuseStep 1480335 = 2220503) B2220503
theorem B3159737 : Blo 1478559 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1480379 : Blo 1478559 1480379 := bstep (se 1 (by rfl) ⟨1110284, by rfl⟩ : syracuseStep 1480379 = 2220569) B2220569
theorem B1480455 : Blo 1478559 1480455 := bstep (se 1 (by rfl) ⟨1110341, by rfl⟩ : syracuseStep 1480455 = 2220683) B2220683
theorem B5691151 : Blo 1478559 5691151 := bstep (se 1 (by rfl) ⟨4268363, by rfl⟩ : syracuseStep 5691151 = 8536727) B8536727
theorem B2496271 : Blo 1478559 2496271 := bstep (se 1 (by rfl) ⟨1872203, by rfl⟩ : syracuseStep 2496271 = 3744407) B3744407
theorem B3159823 : Blo 1478559 3159823 := bstep (se 1 (by rfl) ⟨2369867, by rfl⟩ : syracuseStep 3159823 = 4739735) B4739735
theorem B1480463 : Blo 1478559 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B1480507 : Blo 1478559 1480507 := bstep (se 1 (by rfl) ⟨1110380, by rfl⟩ : syracuseStep 1480507 = 2220761) B2220761
theorem B7591769 : Blo 1478559 7591769 := bstep (se 2 (by rfl) ⟨2846913, by rfl⟩ : syracuseStep 7591769 = 5693827) B5693827
theorem B1873783 : Blo 1478559 1873783 := bstep (se 1 (by rfl) ⟨1405337, by rfl⟩ : syracuseStep 1873783 = 2810675) B2810675
theorem B2217863 : Blo 1478559 2217863 := bstep (se 1 (by rfl) ⟨1663397, by rfl⟩ : syracuseStep 2217863 = 3326795) B3326795
theorem B18003863 : Blo 1478559 18003863 := bstep (se 1 (by rfl) ⟨13502897, by rfl⟩ : syracuseStep 18003863 = 27005795) B27005795
theorem B2217899 : Blo 1478559 2217899 := bstep (se 1 (by rfl) ⟨1663424, by rfl⟩ : syracuseStep 2217899 = 3326849) B3326849
theorem B2217929 : Blo 1478559 2217929 := bstep (se 2 (by rfl) ⟨831723, by rfl⟩ : syracuseStep 2217929 = 1663447) B1663447
theorem B9484235 : Blo 1478559 9484235 := bstep (se 1 (by rfl) ⟨7113176, by rfl⟩ : syracuseStep 9484235 = 14226353) B14226353
theorem B3602465 : Blo 1478559 3602465 := bstep (se 2 (by rfl) ⟨1350924, by rfl⟩ : syracuseStep 3602465 = 2701849) B2701849
theorem B2218043 : Blo 1478559 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B4388951 : Blo 1478559 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B2218103 : Blo 1478559 2218103 := bstep (se 1 (by rfl) ⟨1663577, by rfl⟩ : syracuseStep 2218103 = 3327155) B3327155
theorem B2218127 : Blo 1478559 2218127 := bstep (se 1 (by rfl) ⟨1663595, by rfl⟩ : syracuseStep 2218127 = 3327191) B3327191
theorem B9124013 : Blo 1478559 9124013 := bstep (se 3 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 9124013 = 3421505) B3421505
theorem B2218169 : Blo 1478559 2218169 := bstep (se 2 (by rfl) ⟨831813, by rfl⟩ : syracuseStep 2218169 = 1663627) B1663627
theorem B3553465 : Blo 1478559 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B12646601 : Blo 1478559 12646601 := bstep (se 2 (by rfl) ⟨4742475, by rfl⟩ : syracuseStep 12646601 = 9484951) B9484951
theorem B2218247 : Blo 1478559 2218247 := bstep (se 1 (by rfl) ⟨1663685, by rfl⟩ : syracuseStep 2218247 = 3327371) B3327371
theorem B2218283 : Blo 1478559 2218283 := bstep (se 1 (by rfl) ⟨1663712, by rfl⟩ : syracuseStep 2218283 = 3327425) B3327425
theorem B2496811 : Blo 1478559 2496811 := bstep (se 1 (by rfl) ⟨1872608, by rfl⟩ : syracuseStep 2496811 = 3745217) B3745217
theorem B2218313 : Blo 1478559 2218313 := bstep (se 2 (by rfl) ⟨831867, by rfl⟩ : syracuseStep 2218313 = 1663735) B1663735
theorem B2808199 : Blo 1478559 2808199 := bstep (se 1 (by rfl) ⟨2106149, by rfl⟩ : syracuseStep 2808199 = 4212299) B4212299
theorem B11237777 : Blo 1478559 11237777 := bstep (se 2 (by rfl) ⟨4214166, by rfl⟩ : syracuseStep 11237777 = 8428333) B8428333
theorem B8993177 : Blo 1478559 8993177 := bstep (se 2 (by rfl) ⟨3372441, by rfl⟩ : syracuseStep 8993177 = 6744883) B6744883
theorem B2496953 : Blo 1478559 2496953 := bstep (se 2 (by rfl) ⟨936357, by rfl⟩ : syracuseStep 2496953 = 1872715) B1872715
theorem B2218427 : Blo 1478559 2218427 := bstep (se 1 (by rfl) ⟨1663820, by rfl⟩ : syracuseStep 2218427 = 3327641) B3327641
theorem B2218487 : Blo 1478559 2218487 := bstep (se 1 (by rfl) ⟨1663865, by rfl⟩ : syracuseStep 2218487 = 3327731) B3327731
theorem B2218511 : Blo 1478559 2218511 := bstep (se 1 (by rfl) ⟨1663883, by rfl⟩ : syracuseStep 2218511 = 3327767) B3327767
theorem B2218553 : Blo 1478559 2218553 := bstep (se 2 (by rfl) ⟨831957, by rfl⟩ : syracuseStep 2218553 = 1663915) B1663915
theorem B7486019 : Blo 1478559 7486019 := bstep (se 1 (by rfl) ⟨5614514, by rfl⟩ : syracuseStep 7486019 = 11229029) B11229029
theorem B8428151 : Blo 1478559 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B2218631 : Blo 1478559 2218631 := bstep (se 1 (by rfl) ⟨1663973, by rfl⟩ : syracuseStep 2218631 = 3327947) B3327947
theorem B3160711 : Blo 1478559 3160711 := bstep (se 1 (by rfl) ⟨2370533, by rfl⟩ : syracuseStep 3160711 = 4741067) B4741067
theorem B2218667 : Blo 1478559 2218667 := bstep (se 1 (by rfl) ⟨1664000, by rfl⟩ : syracuseStep 2218667 = 3328001) B3328001
theorem B2218697 : Blo 1478559 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B3554081 : Blo 1478559 3554081 := bstep (se 2 (by rfl) ⟨1332780, by rfl⟩ : syracuseStep 3554081 = 2665561) B2665561
theorem B3160865 : Blo 1478559 3160865 := bstep (se 2 (by rfl) ⟨1185324, by rfl⟩ : syracuseStep 3160865 = 2370649) B2370649
theorem B11230001 : Blo 1478559 11230001 := bstep (se 2 (by rfl) ⟨4211250, by rfl⟩ : syracuseStep 11230001 = 8422501) B8422501
theorem B2218811 : Blo 1478559 2218811 := bstep (se 1 (by rfl) ⟨1664108, by rfl⟩ : syracuseStep 2218811 = 3328217) B3328217
theorem B2218871 : Blo 1478559 2218871 := bstep (se 1 (by rfl) ⟨1664153, by rfl⟩ : syracuseStep 2218871 = 3328307) B3328307
theorem B7486343 : Blo 1478559 7486343 := bstep (se 1 (by rfl) ⟨5614757, by rfl⟩ : syracuseStep 7486343 = 11229515) B11229515
theorem B2218895 : Blo 1478559 2218895 := bstep (se 1 (by rfl) ⟨1664171, by rfl⟩ : syracuseStep 2218895 = 3328343) B3328343
theorem B5618585 : Blo 1478559 5618585 := bstep (se 2 (by rfl) ⟨2106969, by rfl⟩ : syracuseStep 5618585 = 4213939) B4213939
theorem B2218937 : Blo 1478559 2218937 := bstep (se 2 (by rfl) ⟨832101, by rfl⟩ : syracuseStep 2218937 = 1664203) B1664203
theorem B4996025 : Blo 1478559 4996025 := bstep (se 2 (by rfl) ⟨1873509, by rfl⟩ : syracuseStep 4996025 = 3747019) B3747019
theorem B2219015 : Blo 1478559 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B4054045 : Blo 1478559 4054045 := bstep (se 3 (by rfl) ⟨760133, by rfl⟩ : syracuseStep 4054045 = 1520267) B1520267
theorem B2219051 : Blo 1478559 2219051 := bstep (se 1 (by rfl) ⟨1664288, by rfl⟩ : syracuseStep 2219051 = 3328577) B3328577
theorem B2219081 : Blo 1478559 2219081 := bstep (se 2 (by rfl) ⟨832155, by rfl⟩ : syracuseStep 2219081 = 1664311) B1664311
theorem B3742807 : Blo 1478559 3742807 := bstep (se 1 (by rfl) ⟨2807105, by rfl⟩ : syracuseStep 3742807 = 5614211) B5614211
theorem B2497655 : Blo 1478559 2497655 := bstep (se 1 (by rfl) ⟨1873241, by rfl⟩ : syracuseStep 2497655 = 3746483) B3746483
theorem B3161207 : Blo 1478559 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2219195 : Blo 1478559 2219195 := bstep (se 1 (by rfl) ⟨1664396, by rfl⟩ : syracuseStep 2219195 = 3328793) B3328793
theorem B7109869 : Blo 1478559 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B6323437 : Blo 1478559 6323437 := bstep (se 3 (by rfl) ⟨1185644, by rfl⟩ : syracuseStep 6323437 = 2371289) B2371289
theorem B2219255 : Blo 1478559 2219255 := bstep (se 1 (by rfl) ⟨1664441, by rfl⟩ : syracuseStep 2219255 = 3328883) B3328883
theorem B2219279 : Blo 1478559 2219279 := bstep (se 1 (by rfl) ⟨1664459, by rfl⟩ : syracuseStep 2219279 = 3328919) B3328919
theorem B3161377 : Blo 1478559 3161377 := bstep (se 2 (by rfl) ⟨1185516, by rfl⟩ : syracuseStep 3161377 = 2371033) B2371033
theorem B2219321 : Blo 1478559 2219321 := bstep (se 2 (by rfl) ⟨832245, by rfl⟩ : syracuseStep 2219321 = 1664491) B1664491
theorem B1580347 : Blo 1478559 1580347 := bstep (se 1 (by rfl) ⟨1185260, by rfl⟩ : syracuseStep 1580347 = 2370521) B2370521
theorem B8428859 : Blo 1478559 8428859 := bstep (se 1 (by rfl) ⟨6321644, by rfl⟩ : syracuseStep 8428859 = 12643289) B12643289
theorem B8543603 : Blo 1478559 8543603 := bstep (se 1 (by rfl) ⟨6407702, by rfl⟩ : syracuseStep 8543603 = 12815405) B12815405
theorem B3743111 : Blo 1478559 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B3554695 : Blo 1478559 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B2219399 : Blo 1478559 2219399 := bstep (se 1 (by rfl) ⟨1664549, by rfl⟩ : syracuseStep 2219399 = 3329099) B3329099
theorem B6323609 : Blo 1478559 6323609 := bstep (se 2 (by rfl) ⟨2371353, by rfl⟩ : syracuseStep 6323609 = 4742707) B4742707
theorem B2219435 : Blo 1478559 2219435 := bstep (se 1 (by rfl) ⟨1664576, by rfl⟩ : syracuseStep 2219435 = 3329153) B3329153
theorem B2219465 : Blo 1478559 2219465 := bstep (se 2 (by rfl) ⟨832299, by rfl⟩ : syracuseStep 2219465 = 1664599) B1664599
theorem B3743243 : Blo 1478559 3743243 := bstep (se 1 (by rfl) ⟨2807432, by rfl⟩ : syracuseStep 3743243 = 5614865) B5614865
theorem B4996619 : Blo 1478559 4996619 := bstep (se 1 (by rfl) ⟨3747464, by rfl⟩ : syracuseStep 4996619 = 7494929) B7494929
theorem B8994347 : Blo 1478559 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B2219579 : Blo 1478559 2219579 := bstep (se 1 (by rfl) ⟨1664684, by rfl⟩ : syracuseStep 2219579 = 3329369) B3329369
theorem B2498107 : Blo 1478559 2498107 := bstep (se 1 (by rfl) ⟨1873580, by rfl⟩ : syracuseStep 2498107 = 3747161) B3747161
theorem B24010339 : Blo 1478559 24010339 := bstep (se 1 (by rfl) ⟨18007754, by rfl⟩ : syracuseStep 24010339 = 36015509) B36015509
theorem B2219639 : Blo 1478559 2219639 := bstep (se 1 (by rfl) ⟨1664729, by rfl⟩ : syracuseStep 2219639 = 3329459) B3329459
theorem B4996727 : Blo 1478559 4996727 := bstep (se 1 (by rfl) ⟨3747545, by rfl⟩ : syracuseStep 4996727 = 7495091) B7495091
theorem B2219663 : Blo 1478559 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B3038905 : Blo 1478559 3038905 := bstep (se 2 (by rfl) ⟨1139589, by rfl⟩ : syracuseStep 3038905 = 2279179) B2279179
theorem B3374777 : Blo 1478559 3374777 := bstep (se 2 (by rfl) ⟨1265541, by rfl⟩ : syracuseStep 3374777 = 2531083) B2531083
theorem B2219705 : Blo 1478559 2219705 := bstep (se 2 (by rfl) ⟨832389, by rfl⟩ : syracuseStep 2219705 = 1664779) B1664779
theorem B2498249 : Blo 1478559 2498249 := bstep (se 2 (by rfl) ⟨936843, by rfl⟩ : syracuseStep 2498249 = 1873687) B1873687
theorem B16858853 : Blo 1478559 16858853 := bstep (se 4 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 16858853 = 3161035) B3161035
theorem B2219783 : Blo 1478559 2219783 := bstep (se 1 (by rfl) ⟨1664837, by rfl⟩ : syracuseStep 2219783 = 3329675) B3329675
theorem B2219819 : Blo 1478559 2219819 := bstep (se 1 (by rfl) ⟨1664864, by rfl⟩ : syracuseStep 2219819 = 3329729) B3329729
theorem B18972467 : Blo 1478559 18972467 := bstep (se 1 (by rfl) ⟨14229350, by rfl⟩ : syracuseStep 18972467 = 28458701) B28458701
theorem B2219849 : Blo 1478559 2219849 := bstep (se 2 (by rfl) ⟨832443, by rfl⟩ : syracuseStep 2219849 = 1664887) B1664887
theorem B3374995 : Blo 1478559 3374995 := bstep (se 1 (by rfl) ⟨2531246, by rfl⟩ : syracuseStep 3374995 = 5062493) B5062493
theorem B2219963 : Blo 1478559 2219963 := bstep (se 1 (by rfl) ⟨1664972, by rfl⟩ : syracuseStep 2219963 = 3329945) B3329945
theorem B10665931 : Blo 1478559 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B2220023 : Blo 1478559 2220023 := bstep (se 1 (by rfl) ⟨1665017, by rfl⟩ : syracuseStep 2220023 = 3330035) B3330035
theorem B2220041 : Blo 1478559 2220041 := bstep (se 2 (by rfl) ⟨832515, by rfl⟩ : syracuseStep 2220041 = 1665031) B1665031
theorem B2220071 : Blo 1478559 2220071 := bstep (se 1 (by rfl) ⟨1665053, by rfl⟩ : syracuseStep 2220071 = 3330107) B3330107
theorem B3080249 : Blo 1478559 3080249 := bstep (se 2 (by rfl) ⟨1155093, by rfl⟩ : syracuseStep 3080249 = 2310187) B2310187
theorem B18956369 : Blo 1478559 18956369 := bstep (se 2 (by rfl) ⟨7108638, by rfl⟩ : syracuseStep 18956369 = 14217277) B14217277
theorem B2220155 : Blo 1478559 2220155 := bstep (se 1 (by rfl) ⟨1665116, by rfl⟩ : syracuseStep 2220155 = 3330233) B3330233
theorem B5333239 : Blo 1478559 5333239 := bstep (se 1 (by rfl) ⟨3999929, by rfl⟩ : syracuseStep 5333239 = 7999859) B7999859
theorem B2220281 : Blo 1478559 2220281 := bstep (se 2 (by rfl) ⟨832605, by rfl⟩ : syracuseStep 2220281 = 1665211) B1665211
theorem B2220383 : Blo 1478559 2220383 := bstep (se 1 (by rfl) ⟨1665287, by rfl⟩ : syracuseStep 2220383 = 3330575) B3330575
theorem B2220395 : Blo 1478559 2220395 := bstep (se 1 (by rfl) ⟨1665296, by rfl⟩ : syracuseStep 2220395 = 3330593) B3330593
theorem B5620211 : Blo 1478559 5620211 := bstep (se 1 (by rfl) ⟨4215158, by rfl⟩ : syracuseStep 5620211 = 8430317) B8430317
theorem B3744265 : Blo 1478559 3744265 := bstep (se 2 (by rfl) ⟨1404099, by rfl⟩ : syracuseStep 3744265 = 2808199) B2808199
theorem B2810447 : Blo 1478559 2810447 := bstep (se 1 (by rfl) ⟨2107835, by rfl⟩ : syracuseStep 2810447 = 4215671) B4215671
theorem B2220623 : Blo 1478559 2220623 := bstep (se 1 (by rfl) ⟨1665467, by rfl⟩ : syracuseStep 2220623 = 3330935) B3330935
theorem B4211297 : Blo 1478559 4211297 := bstep (se 2 (by rfl) ⟨1579236, by rfl⟩ : syracuseStep 4211297 = 3158473) B3158473
theorem B2220743 : Blo 1478559 2220743 := bstep (se 1 (by rfl) ⟨1665557, by rfl⟩ : syracuseStep 2220743 = 3331115) B3331115
theorem B11231945 : Blo 1478559 11231945 := bstep (se 2 (by rfl) ⟨4211979, by rfl⟩ : syracuseStep 11231945 = 8423959) B8423959
theorem B35971913 : Blo 1478559 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B10814285 : Blo 1478559 10814285 := bstep (se 3 (by rfl) ⟨2027678, by rfl⟩ : syracuseStep 10814285 = 4055357) B4055357
theorem B20243351 : Blo 1478559 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B8422319 : Blo 1478559 8422319 := bstep (se 1 (by rfl) ⟨6316739, by rfl⟩ : syracuseStep 8422319 = 12633479) B12633479
theorem B3326903 : Blo 1478559 3326903 := bstep (se 1 (by rfl) ⟨2495177, by rfl⟩ : syracuseStep 3326903 = 4990355) B4990355
theorem B4211639 : Blo 1478559 4211639 := bstep (se 1 (by rfl) ⟨3158729, by rfl⟩ : syracuseStep 4211639 = 6317459) B6317459
theorem B22782941 : Blo 1478559 22782941 := bstep (se 3 (by rfl) ⟨4271801, by rfl⟩ : syracuseStep 22782941 = 8543603) B8543603
theorem B13493267 : Blo 1478559 13493267 := bstep (se 1 (by rfl) ⟨10119950, by rfl⟩ : syracuseStep 13493267 = 20239901) B20239901
theorem B6317135 : Blo 1478559 6317135 := bstep (se 1 (by rfl) ⟨4737851, by rfl⟩ : syracuseStep 6317135 = 9475703) B9475703
theorem B2106491 : Blo 1478559 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B35996825 : Blo 1478559 35996825 := bstep (se 2 (by rfl) ⟨13498809, by rfl⟩ : syracuseStep 35996825 = 26997619) B26997619
theorem B12002575 : Blo 1478559 12002575 := bstep (se 1 (by rfl) ⟨9001931, by rfl⟩ : syracuseStep 12002575 = 18003863) B18003863
theorem B2401643 : Blo 1478559 2401643 := bstep (se 1 (by rfl) ⟨1801232, by rfl⟩ : syracuseStep 2401643 = 3602465) B3602465
theorem B2925967 : Blo 1478559 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B30352805 : Blo 1478559 30352805 := bstep (se 4 (by rfl) ⟨2845575, by rfl⟩ : syracuseStep 30352805 = 5691151) B5691151
theorem B4990409 : Blo 1478559 4990409 := bstep (se 2 (by rfl) ⟨1871403, by rfl⟩ : syracuseStep 4990409 = 3742807) B3742807
theorem B8431067 : Blo 1478559 8431067 := bstep (se 1 (by rfl) ⟨6323300, by rfl⟩ : syracuseStep 8431067 = 12646601) B12646601
theorem B3327497 : Blo 1478559 3327497 := bstep (se 2 (by rfl) ⟨1247811, by rfl⟩ : syracuseStep 3327497 = 2495623) B2495623
theorem B1664635 : Blo 1478559 1664635 := bstep (se 1 (by rfl) ⟨1248476, by rfl⟩ : syracuseStep 1664635 = 2496953) B2496953
theorem B9479825 : Blo 1478559 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B8431249 : Blo 1478559 8431249 := bstep (se 2 (by rfl) ⟨3161718, by rfl⟩ : syracuseStep 8431249 = 6323437) B6323437
theorem B4990679 : Blo 1478559 4990679 := bstep (se 1 (by rfl) ⟨3743009, by rfl⟩ : syracuseStep 4990679 = 7486019) B7486019
theorem B30361337 : Blo 1478559 30361337 := bstep (se 2 (by rfl) ⟨11385501, by rfl⟩ : syracuseStep 30361337 = 22771003) B22771003
theorem B6162169 : Blo 1478559 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B2107129 : Blo 1478559 2107129 := bstep (se 2 (by rfl) ⟨790173, by rfl⟩ : syracuseStep 2107129 = 1580347) B1580347
theorem B3327839 : Blo 1478559 3327839 := bstep (se 1 (by rfl) ⟨2495879, by rfl⟩ : syracuseStep 3327839 = 4991759) B4991759
theorem B2369387 : Blo 1478559 2369387 := bstep (se 1 (by rfl) ⟨1777040, by rfl⟩ : syracuseStep 2369387 = 3554081) B3554081
theorem B2107243 : Blo 1478559 2107243 := bstep (se 1 (by rfl) ⟨1580432, by rfl⟩ : syracuseStep 2107243 = 3160865) B3160865
theorem B4212641 : Blo 1478559 4212641 := bstep (se 2 (by rfl) ⟨1579740, by rfl⟩ : syracuseStep 4212641 = 3159481) B3159481
theorem B4990895 : Blo 1478559 4990895 := bstep (se 1 (by rfl) ⟨3743171, by rfl⟩ : syracuseStep 4990895 = 7486343) B7486343
theorem B3745723 : Blo 1478559 3745723 := bstep (se 1 (by rfl) ⟨2809292, by rfl⟩ : syracuseStep 3745723 = 5618585) B5618585
theorem B3328019 : Blo 1478559 3328019 := bstep (se 1 (by rfl) ⟨2496014, by rfl⟩ : syracuseStep 3328019 = 4992029) B4992029
theorem B4212755 : Blo 1478559 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B18958373 : Blo 1478559 18958373 := bstep (se 4 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 18958373 = 3554695) B3554695
theorem B1665103 : Blo 1478559 1665103 := bstep (se 1 (by rfl) ⟨1248827, by rfl⟩ : syracuseStep 1665103 = 2497655) B2497655
theorem B2107471 : Blo 1478559 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B3328361 : Blo 1478559 3328361 := bstep (se 2 (by rfl) ⟨1248135, by rfl⟩ : syracuseStep 3328361 = 2496271) B2496271
theorem B4213097 : Blo 1478559 4213097 := bstep (se 2 (by rfl) ⟨1579911, by rfl⟩ : syracuseStep 4213097 = 3159823) B3159823
theorem B7997825 : Blo 1478559 7997825 := bstep (se 2 (by rfl) ⟨2999184, by rfl⟩ : syracuseStep 7997825 = 5998369) B5998369
theorem B1665499 : Blo 1478559 1665499 := bstep (se 1 (by rfl) ⟨1249124, by rfl⟩ : syracuseStep 1665499 = 2498249) B2498249
theorem B4499993 : Blo 1478559 4499993 := bstep (se 2 (by rfl) ⟨1687497, by rfl⟩ : syracuseStep 4499993 = 3374995) B3374995
theorem B5614379 : Blo 1478559 5614379 := bstep (se 1 (by rfl) ⟨4210784, by rfl⟩ : syracuseStep 5614379 = 8421569) B8421569
theorem B23989067 : Blo 1478559 23989067 := bstep (se 1 (by rfl) ⟨17991800, by rfl⟩ : syracuseStep 23989067 = 35983601) B35983601
theorem B4737953 : Blo 1478559 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B3328955 : Blo 1478559 3328955 := bstep (se 1 (by rfl) ⟨2496716, by rfl⟩ : syracuseStep 3328955 = 4993433) B4993433
theorem B3329081 : Blo 1478559 3329081 := bstep (se 2 (by rfl) ⟨1248405, by rfl⟩ : syracuseStep 3329081 = 2496811) B2496811
theorem B3329423 : Blo 1478559 3329423 := bstep (se 1 (by rfl) ⟨2497067, by rfl⟩ : syracuseStep 3329423 = 4994135) B4994135
theorem B4214281 : Blo 1478559 4214281 := bstep (se 2 (by rfl) ⟨1580355, by rfl⟩ : syracuseStep 4214281 = 3160711) B3160711
theorem B13495895 : Blo 1478559 13495895 := bstep (se 1 (by rfl) ⟨10121921, by rfl⟩ : syracuseStep 13495895 = 20243843) B20243843
theorem B3329747 : Blo 1478559 3329747 := bstep (se 1 (by rfl) ⟨2497310, by rfl⟩ : syracuseStep 3329747 = 4994621) B4994621
theorem B1478575 : Blo 1478559 1478575 := bstep (se 1 (by rfl) ⟨1108931, by rfl⟩ : syracuseStep 1478575 = 2217863) B2217863
theorem B1478599 : Blo 1478559 1478599 := bstep (se 1 (by rfl) ⟨1108949, by rfl⟩ : syracuseStep 1478599 = 2217899) B2217899
theorem B1478619 : Blo 1478559 1478619 := bstep (se 1 (by rfl) ⟨1108964, by rfl⟩ : syracuseStep 1478619 = 2217929) B2217929
theorem B1478695 : Blo 1478559 1478695 := bstep (se 1 (by rfl) ⟨1109021, by rfl⟩ : syracuseStep 1478695 = 2218043) B2218043
theorem B1478735 : Blo 1478559 1478735 := bstep (se 1 (by rfl) ⟨1109051, by rfl⟩ : syracuseStep 1478735 = 2218103) B2218103
theorem B1478751 : Blo 1478559 1478751 := bstep (se 1 (by rfl) ⟨1109063, by rfl⟩ : syracuseStep 1478751 = 2218127) B2218127
theorem B6082675 : Blo 1478559 6082675 := bstep (se 1 (by rfl) ⟨4562006, by rfl⟩ : syracuseStep 6082675 = 9124013) B9124013
theorem B1478779 : Blo 1478559 1478779 := bstep (se 1 (by rfl) ⟨1109084, by rfl⟩ : syracuseStep 1478779 = 2218169) B2218169
theorem B7106717 : Blo 1478559 7106717 := bstep (se 3 (by rfl) ⟨1332509, by rfl⟩ : syracuseStep 7106717 = 2665019) B2665019
theorem B1478831 : Blo 1478559 1478831 := bstep (se 1 (by rfl) ⟨1109123, by rfl⟩ : syracuseStep 1478831 = 2218247) B2218247
theorem B1478855 : Blo 1478559 1478855 := bstep (se 1 (by rfl) ⟨1109141, by rfl⟩ : syracuseStep 1478855 = 2218283) B2218283
theorem B1478875 : Blo 1478559 1478875 := bstep (se 1 (by rfl) ⟨1109156, by rfl⟩ : syracuseStep 1478875 = 2218313) B2218313
theorem B4993271 : Blo 1478559 4993271 := bstep (se 1 (by rfl) ⟨3744953, by rfl⟩ : syracuseStep 4993271 = 7489907) B7489907
theorem B7491851 : Blo 1478559 7491851 := bstep (se 1 (by rfl) ⟨5618888, by rfl⟩ : syracuseStep 7491851 = 11237777) B11237777
theorem B1478951 : Blo 1478559 1478951 := bstep (se 1 (by rfl) ⟨1109213, by rfl⟩ : syracuseStep 1478951 = 2218427) B2218427
theorem B1478991 : Blo 1478559 1478991 := bstep (se 1 (by rfl) ⟨1109243, by rfl⟩ : syracuseStep 1478991 = 2218487) B2218487
theorem B1479007 : Blo 1478559 1479007 := bstep (se 1 (by rfl) ⟨1109255, by rfl⟩ : syracuseStep 1479007 = 2218511) B2218511
theorem B1479035 : Blo 1478559 1479035 := bstep (se 1 (by rfl) ⟨1109276, by rfl⟩ : syracuseStep 1479035 = 2218553) B2218553
theorem B4215169 : Blo 1478559 4215169 := bstep (se 2 (by rfl) ⟨1580688, by rfl⟩ : syracuseStep 4215169 = 3161377) B3161377
theorem B1479087 : Blo 1478559 1479087 := bstep (se 1 (by rfl) ⟨1109315, by rfl⟩ : syracuseStep 1479087 = 2218631) B2218631
theorem B1479111 : Blo 1478559 1479111 := bstep (se 1 (by rfl) ⟨1109333, by rfl⟩ : syracuseStep 1479111 = 2218667) B2218667
theorem B1479131 : Blo 1478559 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B1479207 : Blo 1478559 1479207 := bstep (se 1 (by rfl) ⟨1109405, by rfl⟩ : syracuseStep 1479207 = 2218811) B2218811
theorem B4993595 : Blo 1478559 4993595 := bstep (se 1 (by rfl) ⟨3745196, by rfl⟩ : syracuseStep 4993595 = 7490393) B7490393
theorem B1479247 : Blo 1478559 1479247 := bstep (se 1 (by rfl) ⟨1109435, by rfl⟩ : syracuseStep 1479247 = 2218871) B2218871
theorem B1479263 : Blo 1478559 1479263 := bstep (se 1 (by rfl) ⟨1109447, by rfl⟩ : syracuseStep 1479263 = 2218895) B2218895
theorem B1479291 : Blo 1478559 1479291 := bstep (se 1 (by rfl) ⟨1109468, by rfl⟩ : syracuseStep 1479291 = 2218937) B2218937
theorem B3330683 : Blo 1478559 3330683 := bstep (se 1 (by rfl) ⟨2498012, by rfl⟩ : syracuseStep 3330683 = 4996025) B4996025
theorem B1479343 : Blo 1478559 1479343 := bstep (se 1 (by rfl) ⟨1109507, by rfl⟩ : syracuseStep 1479343 = 2219015) B2219015
theorem B6320825 : Blo 1478559 6320825 := bstep (se 2 (by rfl) ⟨2370309, by rfl⟩ : syracuseStep 6320825 = 4740619) B4740619
theorem B1479367 : Blo 1478559 1479367 := bstep (se 1 (by rfl) ⟨1109525, by rfl⟩ : syracuseStep 1479367 = 2219051) B2219051
theorem B9482953 : Blo 1478559 9482953 := bstep (se 2 (by rfl) ⟨3556107, by rfl⟩ : syracuseStep 9482953 = 7112215) B7112215
theorem B5616337 : Blo 1478559 5616337 := bstep (se 2 (by rfl) ⟨2106126, by rfl⟩ : syracuseStep 5616337 = 4212253) B4212253
theorem B1479387 : Blo 1478559 1479387 := bstep (se 1 (by rfl) ⟨1109540, by rfl⟩ : syracuseStep 1479387 = 2219081) B2219081
theorem B2495225 : Blo 1478559 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B3330809 : Blo 1478559 3330809 := bstep (se 2 (by rfl) ⟨1249053, by rfl⟩ : syracuseStep 3330809 = 2498107) B2498107
theorem B1479463 : Blo 1478559 1479463 := bstep (se 1 (by rfl) ⟨1109597, by rfl⟩ : syracuseStep 1479463 = 2219195) B2219195
theorem B4993865 : Blo 1478559 4993865 := bstep (se 2 (by rfl) ⟨1872699, by rfl⟩ : syracuseStep 4993865 = 3745399) B3745399
theorem B1479503 : Blo 1478559 1479503 := bstep (se 1 (by rfl) ⟨1109627, by rfl⟩ : syracuseStep 1479503 = 2219255) B2219255
theorem B1479519 : Blo 1478559 1479519 := bstep (se 1 (by rfl) ⟨1109639, by rfl⟩ : syracuseStep 1479519 = 2219279) B2219279
theorem B1479547 : Blo 1478559 1479547 := bstep (se 1 (by rfl) ⟨1109660, by rfl⟩ : syracuseStep 1479547 = 2219321) B2219321
theorem B4051873 : Blo 1478559 4051873 := bstep (se 2 (by rfl) ⟨1519452, by rfl⟩ : syracuseStep 4051873 = 3038905) B3038905
theorem B2495407 : Blo 1478559 2495407 := bstep (se 1 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 2495407 = 3743111) B3743111
theorem B1479599 : Blo 1478559 1479599 := bstep (se 1 (by rfl) ⟨1109699, by rfl⟩ : syracuseStep 1479599 = 2219399) B2219399
theorem B4215739 : Blo 1478559 4215739 := bstep (se 1 (by rfl) ⟨3161804, by rfl⟩ : syracuseStep 4215739 = 6323609) B6323609
theorem B1479623 : Blo 1478559 1479623 := bstep (se 1 (by rfl) ⟨1109717, by rfl⟩ : syracuseStep 1479623 = 2219435) B2219435
theorem B1479643 : Blo 1478559 1479643 := bstep (se 1 (by rfl) ⟨1109732, by rfl⟩ : syracuseStep 1479643 = 2219465) B2219465
theorem B5616641 : Blo 1478559 5616641 := bstep (se 2 (by rfl) ⟨2106240, by rfl⟩ : syracuseStep 5616641 = 4212481) B4212481
theorem B2495495 : Blo 1478559 2495495 := bstep (se 1 (by rfl) ⟨1871621, by rfl⟩ : syracuseStep 2495495 = 3743243) B3743243
theorem B3331079 : Blo 1478559 3331079 := bstep (se 1 (by rfl) ⟨2498309, by rfl⟩ : syracuseStep 3331079 = 4996619) B4996619
theorem B1479719 : Blo 1478559 1479719 := bstep (se 1 (by rfl) ⟨1109789, by rfl⟩ : syracuseStep 1479719 = 2219579) B2219579
theorem B1479759 : Blo 1478559 1479759 := bstep (se 1 (by rfl) ⟨1109819, by rfl⟩ : syracuseStep 1479759 = 2219639) B2219639
theorem B3331151 : Blo 1478559 3331151 := bstep (se 1 (by rfl) ⟨2498363, by rfl⟩ : syracuseStep 3331151 = 4996727) B4996727
theorem B1479775 : Blo 1478559 1479775 := bstep (se 1 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 1479775 = 2219663) B2219663
theorem B2249851 : Blo 1478559 2249851 := bstep (se 1 (by rfl) ⟨1687388, by rfl⟩ : syracuseStep 2249851 = 3374777) B3374777
theorem B1479803 : Blo 1478559 1479803 := bstep (se 1 (by rfl) ⟨1109852, by rfl⟩ : syracuseStep 1479803 = 2219705) B2219705
theorem B1479855 : Blo 1478559 1479855 := bstep (se 1 (by rfl) ⟨1109891, by rfl⟩ : syracuseStep 1479855 = 2219783) B2219783
theorem B1479879 : Blo 1478559 1479879 := bstep (se 1 (by rfl) ⟨1109909, by rfl⟩ : syracuseStep 1479879 = 2219819) B2219819
theorem B1479899 : Blo 1478559 1479899 := bstep (se 1 (by rfl) ⟨1109924, by rfl⟩ : syracuseStep 1479899 = 2219849) B2219849
theorem B1479975 : Blo 1478559 1479975 := bstep (se 1 (by rfl) ⟨1109981, by rfl⟩ : syracuseStep 1479975 = 2219963) B2219963
theorem B1480015 : Blo 1478559 1480015 := bstep (se 1 (by rfl) ⟨1110011, by rfl⟩ : syracuseStep 1480015 = 2220023) B2220023
theorem B2495839 : Blo 1478559 2495839 := bstep (se 1 (by rfl) ⟨1871879, by rfl⟩ : syracuseStep 2495839 = 3743759) B3743759
theorem B1480031 : Blo 1478559 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B1480059 : Blo 1478559 1480059 := bstep (se 1 (by rfl) ⟨1110044, by rfl⟩ : syracuseStep 1480059 = 2220089) B2220089
theorem B1480111 : Blo 1478559 1480111 := bstep (se 1 (by rfl) ⟨1110083, by rfl⟩ : syracuseStep 1480111 = 2220167) B2220167
theorem B2495927 : Blo 1478559 2495927 := bstep (se 1 (by rfl) ⟨1871945, by rfl⟩ : syracuseStep 2495927 = 3743891) B3743891
theorem B2807227 : Blo 1478559 2807227 := bstep (se 1 (by rfl) ⟨2105420, by rfl⟩ : syracuseStep 2807227 = 4210841) B4210841
theorem B1480135 : Blo 1478559 1480135 := bstep (se 1 (by rfl) ⟨1110101, by rfl⟩ : syracuseStep 1480135 = 2220203) B2220203
theorem B5617097 : Blo 1478559 5617097 := bstep (se 2 (by rfl) ⟨2106411, by rfl⟩ : syracuseStep 5617097 = 4212823) B4212823
theorem B1480155 : Blo 1478559 1480155 := bstep (se 1 (by rfl) ⟨1110116, by rfl⟩ : syracuseStep 1480155 = 2220233) B2220233
theorem B4273651 : Blo 1478559 4273651 := bstep (se 1 (by rfl) ⟨3205238, by rfl⟩ : syracuseStep 4273651 = 6410477) B6410477
theorem B1480231 : Blo 1478559 1480231 := bstep (se 1 (by rfl) ⟨1110173, by rfl⟩ : syracuseStep 1480231 = 2220347) B2220347
theorem B1480271 : Blo 1478559 1480271 := bstep (se 1 (by rfl) ⟨1110203, by rfl⟩ : syracuseStep 1480271 = 2220407) B2220407
theorem B1480287 : Blo 1478559 1480287 := bstep (se 1 (by rfl) ⟨1110215, by rfl⟩ : syracuseStep 1480287 = 2220431) B2220431
theorem B1480315 : Blo 1478559 1480315 := bstep (se 1 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 1480315 = 2220473) B2220473
theorem B1480367 : Blo 1478559 1480367 := bstep (se 1 (by rfl) ⟨1110275, by rfl⟩ : syracuseStep 1480367 = 2220551) B2220551
theorem B7493309 : Blo 1478559 7493309 := bstep (se 3 (by rfl) ⟨1404995, by rfl⟩ : syracuseStep 7493309 = 2809991) B2809991
theorem B1480391 : Blo 1478559 1480391 := bstep (se 1 (by rfl) ⟨1110293, by rfl⟩ : syracuseStep 1480391 = 2220587) B2220587
theorem B1480411 : Blo 1478559 1480411 := bstep (se 1 (by rfl) ⟨1110308, by rfl⟩ : syracuseStep 1480411 = 2220617) B2220617
theorem B1480487 : Blo 1478559 1480487 := bstep (se 1 (by rfl) ⟨1110365, by rfl⟩ : syracuseStep 1480487 = 2220731) B2220731
theorem B1480527 : Blo 1478559 1480527 := bstep (se 1 (by rfl) ⟨1110395, by rfl⟩ : syracuseStep 1480527 = 2220791) B2220791
theorem B7493471 : Blo 1478559 7493471 := bstep (se 1 (by rfl) ⟨5620103, by rfl⟩ : syracuseStep 7493471 = 11240207) B11240207
theorem B1480543 : Blo 1478559 1480543 := bstep (se 1 (by rfl) ⟨1110407, by rfl⟩ : syracuseStep 1480543 = 2220815) B2220815
theorem B2807713 : Blo 1478559 2807713 := bstep (se 2 (by rfl) ⟨1052892, by rfl⟩ : syracuseStep 2807713 = 2105785) B2105785
theorem B5617583 : Blo 1478559 5617583 := bstep (se 1 (by rfl) ⟨4213187, by rfl⟩ : syracuseStep 5617583 = 8426375) B8426375
theorem B2217911 : Blo 1478559 2217911 := bstep (se 1 (by rfl) ⟨1663433, by rfl⟩ : syracuseStep 2217911 = 3326867) B3326867
theorem B4994999 : Blo 1478559 4994999 := bstep (se 1 (by rfl) ⟨3746249, by rfl⟩ : syracuseStep 4994999 = 7492499) B7492499
theorem B7485371 : Blo 1478559 7485371 := bstep (se 1 (by rfl) ⟨5614028, by rfl⟩ : syracuseStep 7485371 = 11228057) B11228057
theorem B2217947 : Blo 1478559 2217947 := bstep (se 1 (by rfl) ⟨1663460, by rfl⟩ : syracuseStep 2217947 = 3326921) B3326921
theorem B2496521 : Blo 1478559 2496521 := bstep (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) B1872391
theorem B9246757 : Blo 1478559 9246757 := bstep (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) B1733767
theorem B2496683 : Blo 1478559 2496683 := bstep (se 1 (by rfl) ⟨1872512, by rfl⟩ : syracuseStep 2496683 = 3745025) B3745025
theorem B16857395 : Blo 1478559 16857395 := bstep (se 1 (by rfl) ⟨12643046, by rfl⟩ : syracuseStep 16857395 = 25286093) B25286093
theorem B16005509 : Blo 1478559 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B2218415 : Blo 1478559 2218415 := bstep (se 1 (by rfl) ⟨1663811, by rfl⟩ : syracuseStep 2218415 = 3327623) B3327623
theorem B2808283 : Blo 1478559 2808283 := bstep (se 1 (by rfl) ⟨2106212, by rfl⟩ : syracuseStep 2808283 = 4212425) B4212425
theorem B2218505 : Blo 1478559 2218505 := bstep (se 2 (by rfl) ⟨831939, by rfl⟩ : syracuseStep 2218505 = 1663879) B1663879
theorem B4995593 : Blo 1478559 4995593 := bstep (se 2 (by rfl) ⟨1873347, by rfl⟩ : syracuseStep 4995593 = 3746695) B3746695
theorem B2218535 : Blo 1478559 2218535 := bstep (se 1 (by rfl) ⟨1663901, by rfl⟩ : syracuseStep 2218535 = 3327803) B3327803
theorem B2497081 : Blo 1478559 2497081 := bstep (se 2 (by rfl) ⟨936405, by rfl⟩ : syracuseStep 2497081 = 1872811) B1872811
theorem B5061179 : Blo 1478559 5061179 := bstep (se 1 (by rfl) ⟨3795884, by rfl⟩ : syracuseStep 5061179 = 7591769) B7591769
theorem B2218619 : Blo 1478559 2218619 := bstep (se 1 (by rfl) ⟨1663964, by rfl⟩ : syracuseStep 2218619 = 3327929) B3327929
theorem B6322823 : Blo 1478559 6322823 := bstep (se 1 (by rfl) ⟨4742117, by rfl⟩ : syracuseStep 6322823 = 9484235) B9484235
theorem B5331595 : Blo 1478559 5331595 := bstep (se 1 (by rfl) ⟨3998696, by rfl⟩ : syracuseStep 5331595 = 7997393) B7997393
theorem B5692103 : Blo 1478559 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B2497223 : Blo 1478559 2497223 := bstep (se 1 (by rfl) ⟨1872917, by rfl⟩ : syracuseStep 2497223 = 3745835) B3745835
theorem B5405393 : Blo 1478559 5405393 := bstep (se 2 (by rfl) ⟨2027022, by rfl⟩ : syracuseStep 5405393 = 4054045) B4054045
theorem B2218745 : Blo 1478559 2218745 := bstep (se 2 (by rfl) ⟨832029, by rfl⟩ : syracuseStep 2218745 = 1664059) B1664059
theorem B2218847 : Blo 1478559 2218847 := bstep (se 1 (by rfl) ⟨1664135, by rfl⟩ : syracuseStep 2218847 = 3328271) B3328271
theorem B2497385 : Blo 1478559 2497385 := bstep (se 2 (by rfl) ⟨936519, by rfl⟩ : syracuseStep 2497385 = 1873039) B1873039
theorem B2218859 : Blo 1478559 2218859 := bstep (se 1 (by rfl) ⟨1664144, by rfl⟩ : syracuseStep 2218859 = 3328289) B3328289
theorem B3742625 : Blo 1478559 3742625 := bstep (se 2 (by rfl) ⟨1403484, by rfl⟩ : syracuseStep 3742625 = 2806969) B2806969
theorem B5995451 : Blo 1478559 5995451 := bstep (se 1 (by rfl) ⟨4496588, by rfl⟩ : syracuseStep 5995451 = 8993177) B8993177
theorem B2219087 : Blo 1478559 2219087 := bstep (se 1 (by rfl) ⟨1664315, by rfl⟩ : syracuseStep 2219087 = 3328631) B3328631
theorem B5618767 : Blo 1478559 5618767 := bstep (se 1 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 5618767 = 8428151) B8428151
theorem B4742297 : Blo 1478559 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B2219207 : Blo 1478559 2219207 := bstep (se 1 (by rfl) ⟨1664405, by rfl⟩ : syracuseStep 2219207 = 3328811) B3328811
theorem B7486667 : Blo 1478559 7486667 := bstep (se 1 (by rfl) ⟨5615000, by rfl⟩ : syracuseStep 7486667 = 11230001) B11230001
theorem B2497783 : Blo 1478559 2497783 := bstep (se 1 (by rfl) ⟨1873337, by rfl⟩ : syracuseStep 2497783 = 3746675) B3746675
theorem B11230487 : Blo 1478559 11230487 := bstep (se 1 (by rfl) ⟨8422865, by rfl⟩ : syracuseStep 11230487 = 16845731) B16845731
theorem B3743081 : Blo 1478559 3743081 := bstep (se 2 (by rfl) ⟨1403655, by rfl⟩ : syracuseStep 3743081 = 2807311) B2807311
theorem B2219369 : Blo 1478559 2219369 := bstep (se 2 (by rfl) ⟨832263, by rfl⟩ : syracuseStep 2219369 = 1664527) B1664527
theorem B4996457 : Blo 1478559 4996457 := bstep (se 2 (by rfl) ⟨1873671, by rfl⟩ : syracuseStep 4996457 = 3747343) B3747343
theorem B2219447 : Blo 1478559 2219447 := bstep (se 1 (by rfl) ⟨1664585, by rfl⟩ : syracuseStep 2219447 = 3329171) B3329171
theorem B2497979 : Blo 1478559 2497979 := bstep (se 1 (by rfl) ⟨1873484, by rfl⟩ : syracuseStep 2497979 = 3746969) B3746969
theorem B32013785 : Blo 1478559 32013785 := bstep (se 2 (by rfl) ⟨12005169, by rfl⟩ : syracuseStep 32013785 = 24010339) B24010339
theorem B2219483 : Blo 1478559 2219483 := bstep (se 1 (by rfl) ⟨1664612, by rfl⟩ : syracuseStep 2219483 = 3329225) B3329225
theorem B5619239 : Blo 1478559 5619239 := bstep (se 1 (by rfl) ⟨4214429, by rfl⟩ : syracuseStep 5619239 = 8428859) B8428859
theorem B2498087 : Blo 1478559 2498087 := bstep (se 1 (by rfl) ⟨1873565, by rfl⟩ : syracuseStep 2498087 = 3747131) B3747131
theorem B5996231 : Blo 1478559 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B9879329 : Blo 1478559 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B11239235 : Blo 1478559 11239235 := bstep (se 1 (by rfl) ⟨8429426, by rfl⟩ : syracuseStep 11239235 = 16858853) B16858853
theorem B2498377 : Blo 1478559 2498377 := bstep (se 2 (by rfl) ⟨936891, by rfl⟩ : syracuseStep 2498377 = 1873783) B1873783
theorem B2498411 : Blo 1478559 2498411 := bstep (se 1 (by rfl) ⟨1873808, by rfl⟩ : syracuseStep 2498411 = 3747617) B3747617
theorem B10657655 : Blo 1478559 10657655 := bstep (se 1 (by rfl) ⟨7993241, by rfl⟩ : syracuseStep 10657655 = 15986483) B15986483
theorem B12648311 : Blo 1478559 12648311 := bstep (se 1 (by rfl) ⟨9486233, by rfl⟩ : syracuseStep 12648311 = 18972467) B18972467
theorem B1777583 : Blo 1478559 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B2219951 : Blo 1478559 2219951 := bstep (se 1 (by rfl) ⟨1664963, by rfl⟩ : syracuseStep 2219951 = 3329927) B3329927
theorem B14221241 : Blo 1478559 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B12329009 : Blo 1478559 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B2220137 : Blo 1478559 2220137 := bstep (se 2 (by rfl) ⟨832551, by rfl⟩ : syracuseStep 2220137 = 1665103) B1665103
theorem B2809961 : Blo 1478559 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B7110985 : Blo 1478559 7110985 := bstep (se 2 (by rfl) ⟨2666619, by rfl⟩ : syracuseStep 7110985 = 5333239) B5333239
theorem B2220455 : Blo 1478559 2220455 := bstep (se 1 (by rfl) ⟨1665341, by rfl⟩ : syracuseStep 2220455 = 3330683) B3330683
theorem B7487963 : Blo 1478559 7487963 := bstep (se 1 (by rfl) ⟨5615972, by rfl⟩ : syracuseStep 7487963 = 11231945) B11231945
theorem B1663483 : Blo 1478559 1663483 := bstep (se 1 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 1663483 = 2495225) B2495225
theorem B2220539 : Blo 1478559 2220539 := bstep (se 1 (by rfl) ⟨1665404, by rfl⟩ : syracuseStep 2220539 = 3330809) B3330809
theorem B5620225 : Blo 1478559 5620225 := bstep (se 2 (by rfl) ⟨2107584, by rfl⟩ : syracuseStep 5620225 = 4215169) B4215169
theorem B7209523 : Blo 1478559 7209523 := bstep (se 1 (by rfl) ⟨5407142, by rfl⟩ : syracuseStep 7209523 = 10814285) B10814285
theorem B32440933 : Blo 1478559 32440933 := bstep (se 4 (by rfl) ⟨3041337, by rfl⟩ : syracuseStep 32440933 = 6082675) B6082675
theorem B3744377 : Blo 1478559 3744377 := bstep (se 2 (by rfl) ⟨1404141, by rfl⟩ : syracuseStep 3744377 = 2808283) B2808283
theorem B2220665 : Blo 1478559 2220665 := bstep (se 2 (by rfl) ⟨832749, by rfl⟩ : syracuseStep 2220665 = 1665499) B1665499
theorem B15188627 : Blo 1478559 15188627 := bstep (se 1 (by rfl) ⟨11391470, by rfl⟩ : syracuseStep 15188627 = 22782941) B22782941
theorem B3744427 : Blo 1478559 3744427 := bstep (se 1 (by rfl) ⟨2808320, by rfl⟩ : syracuseStep 3744427 = 5616641) B5616641
theorem B1663663 : Blo 1478559 1663663 := bstep (se 1 (by rfl) ⟨1247747, by rfl⟩ : syracuseStep 1663663 = 2495495) B2495495
theorem B2220719 : Blo 1478559 2220719 := bstep (se 1 (by rfl) ⟨1665539, by rfl⟩ : syracuseStep 2220719 = 3331079) B3331079
theorem B8995511 : Blo 1478559 8995511 := bstep (se 1 (by rfl) ⟨6746633, by rfl⟩ : syracuseStep 8995511 = 13493267) B13493267
theorem B4211423 : Blo 1478559 4211423 := bstep (se 1 (by rfl) ⟨3158567, by rfl⟩ : syracuseStep 4211423 = 6317135) B6317135
theorem B2220767 : Blo 1478559 2220767 := bstep (se 1 (by rfl) ⟨1665575, by rfl⟩ : syracuseStep 2220767 = 3331151) B3331151
theorem B7488449 : Blo 1478559 7488449 := bstep (se 2 (by rfl) ⟨2808168, by rfl⟩ : syracuseStep 7488449 = 5616337) B5616337
theorem B20235203 : Blo 1478559 20235203 := bstep (se 1 (by rfl) ⟨15176402, by rfl⟩ : syracuseStep 20235203 = 30352805) B30352805
theorem B1663951 : Blo 1478559 1663951 := bstep (se 1 (by rfl) ⟨1247963, by rfl⟩ : syracuseStep 1663951 = 2495927) B2495927
theorem B3326939 : Blo 1478559 3326939 := bstep (se 1 (by rfl) ⟨2495204, by rfl⟩ : syracuseStep 3326939 = 4990409) B4990409
theorem B3744731 : Blo 1478559 3744731 := bstep (se 1 (by rfl) ⟨2808548, by rfl⟩ : syracuseStep 3744731 = 5617097) B5617097
theorem B5620711 : Blo 1478559 5620711 := bstep (se 1 (by rfl) ⟨4215533, by rfl⟩ : syracuseStep 5620711 = 8431067) B8431067
theorem B3327119 : Blo 1478559 3327119 := bstep (se 1 (by rfl) ⟨2495339, by rfl⟩ : syracuseStep 3327119 = 4990679) B4990679
theorem B3327209 : Blo 1478559 3327209 := bstep (se 2 (by rfl) ⟨1247703, by rfl⟩ : syracuseStep 3327209 = 2495407) B2495407
theorem B5620985 : Blo 1478559 5620985 := bstep (se 2 (by rfl) ⟨2107869, by rfl⟩ : syracuseStep 5620985 = 4215739) B4215739
theorem B3327263 : Blo 1478559 3327263 := bstep (se 1 (by rfl) ⟨2495447, by rfl⟩ : syracuseStep 3327263 = 4990895) B4990895
theorem B3745055 : Blo 1478559 3745055 := bstep (se 1 (by rfl) ⟨2808791, by rfl⟩ : syracuseStep 3745055 = 5617583) B5617583
theorem B4990247 : Blo 1478559 4990247 := bstep (se 1 (by rfl) ⟨3742685, by rfl⟩ : syracuseStep 4990247 = 7485371) B7485371
theorem B1664347 : Blo 1478559 1664347 := bstep (se 1 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 1664347 = 2496521) B2496521
theorem B1664455 : Blo 1478559 1664455 := bstep (se 1 (by rfl) ⟨1248341, by rfl⟩ : syracuseStep 1664455 = 2496683) B2496683
theorem B2999801 : Blo 1478559 2999801 := bstep (se 2 (by rfl) ⟨1124925, by rfl⟩ : syracuseStep 2999801 = 2249851) B2249851
theorem B3327785 : Blo 1478559 3327785 := bstep (se 2 (by rfl) ⟨1247919, by rfl⟩ : syracuseStep 3327785 = 2495839) B2495839
theorem B3794735 : Blo 1478559 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B1664815 : Blo 1478559 1664815 := bstep (se 1 (by rfl) ⟨1248611, by rfl⟩ : syracuseStep 1664815 = 2497223) B2497223
theorem B3901289 : Blo 1478559 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B15992711 : Blo 1478559 15992711 := bstep (se 1 (by rfl) ⟨11994533, by rfl⟩ : syracuseStep 15992711 = 23989067) B23989067
theorem B1664923 : Blo 1478559 1664923 := bstep (se 1 (by rfl) ⟨1248692, by rfl⟩ : syracuseStep 1664923 = 2497385) B2497385
theorem B4991111 : Blo 1478559 4991111 := bstep (se 1 (by rfl) ⟨3743333, by rfl⟩ : syracuseStep 4991111 = 7486667) B7486667
theorem B11241665 : Blo 1478559 11241665 := bstep (se 2 (by rfl) ⟨4215624, by rfl⟩ : syracuseStep 11241665 = 8431249) B8431249
theorem B1665319 : Blo 1478559 1665319 := bstep (se 1 (by rfl) ⟨1248989, by rfl⟩ : syracuseStep 1665319 = 2497979) B2497979
theorem B21342523 : Blo 1478559 21342523 := bstep (se 1 (by rfl) ⟨16006892, by rfl⟩ : syracuseStep 21342523 = 32013785) B32013785
theorem B3746159 : Blo 1478559 3746159 := bstep (se 1 (by rfl) ⟨2809619, by rfl⟩ : syracuseStep 3746159 = 5619239) B5619239
theorem B1665391 : Blo 1478559 1665391 := bstep (se 1 (by rfl) ⟨1249043, by rfl⟩ : syracuseStep 1665391 = 2498087) B2498087
theorem B8997263 : Blo 1478559 8997263 := bstep (se 1 (by rfl) ⟨6747947, by rfl⟩ : syracuseStep 8997263 = 13495895) B13495895
theorem B12634541 : Blo 1478559 12634541 := bstep (se 3 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 12634541 = 4737953) B4737953
theorem B1665607 : Blo 1478559 1665607 := bstep (se 1 (by rfl) ⟨1249205, by rfl⟩ : syracuseStep 1665607 = 2498411) B2498411
theorem B7105103 : Blo 1478559 7105103 := bstep (se 1 (by rfl) ⟨5328827, by rfl⟩ : syracuseStep 7105103 = 10657655) B10657655
theorem B8432207 : Blo 1478559 8432207 := bstep (se 1 (by rfl) ⟨6324155, by rfl⟩ : syracuseStep 8432207 = 12648311) B12648311
theorem B9480827 : Blo 1478559 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B3328847 : Blo 1478559 3328847 := bstep (se 1 (by rfl) ⟨2496635, by rfl⟩ : syracuseStep 3328847 = 4993271) B4993271
theorem B3746807 : Blo 1478559 3746807 := bstep (se 1 (by rfl) ⟨2810105, by rfl⟩ : syracuseStep 3746807 = 5620211) B5620211
theorem B3329063 : Blo 1478559 3329063 := bstep (se 1 (by rfl) ⟨2496797, by rfl⟩ : syracuseStep 3329063 = 4993595) B4993595
theorem B18951245 : Blo 1478559 18951245 := bstep (se 3 (by rfl) ⟨3553358, by rfl⟩ : syracuseStep 18951245 = 7106717) B7106717
theorem B4213883 : Blo 1478559 4213883 := bstep (se 1 (by rfl) ⟨3160412, by rfl⟩ : syracuseStep 4213883 = 6320825) B6320825
theorem B23981275 : Blo 1478559 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B3329243 : Blo 1478559 3329243 := bstep (se 1 (by rfl) ⟨2496932, by rfl⟩ : syracuseStep 3329243 = 4993865) B4993865
theorem B13495567 : Blo 1478559 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B5614879 : Blo 1478559 5614879 := bstep (se 1 (by rfl) ⟨4211159, by rfl⟩ : syracuseStep 5614879 = 8422319) B8422319
theorem B4992353 : Blo 1478559 4992353 := bstep (se 2 (by rfl) ⟨1872132, by rfl⟩ : syracuseStep 4992353 = 3744265) B3744265
theorem B3329441 : Blo 1478559 3329441 := bstep (se 2 (by rfl) ⟨1248540, by rfl⟩ : syracuseStep 3329441 = 2497081) B2497081
theorem B23997883 : Blo 1478559 23997883 := bstep (se 1 (by rfl) ⟨17998412, by rfl⟩ : syracuseStep 23997883 = 35996825) B35996825
theorem B1601095 : Blo 1478559 1601095 := bstep (se 1 (by rfl) ⟨1200821, by rfl⟩ : syracuseStep 1601095 = 2401643) B2401643
theorem B12643937 : Blo 1478559 12643937 := bstep (se 2 (by rfl) ⟨4741476, by rfl⟩ : syracuseStep 12643937 = 9482953) B9482953
theorem B21327533 : Blo 1478559 21327533 := bstep (se 3 (by rfl) ⟨3998912, by rfl⟩ : syracuseStep 21327533 = 7997825) B7997825
theorem B6319883 : Blo 1478559 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B5402497 : Blo 1478559 5402497 := bstep (se 2 (by rfl) ⟨2025936, by rfl⟩ : syracuseStep 5402497 = 4051873) B4051873
theorem B1478607 : Blo 1478559 1478607 := bstep (se 1 (by rfl) ⟨1108955, by rfl⟩ : syracuseStep 1478607 = 2217911) B2217911
theorem B3329999 : Blo 1478559 3329999 := bstep (se 1 (by rfl) ⟨2497499, by rfl⟩ : syracuseStep 3329999 = 4994999) B4994999
theorem B1478631 : Blo 1478559 1478631 := bstep (se 1 (by rfl) ⟨1108973, by rfl⟩ : syracuseStep 1478631 = 2217947) B2217947
theorem B7491689 : Blo 1478559 7491689 := bstep (se 2 (by rfl) ⟨2809383, by rfl⟩ : syracuseStep 7491689 = 5618767) B5618767
theorem B10670339 : Blo 1478559 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B1478943 : Blo 1478559 1478943 := bstep (se 1 (by rfl) ⟨1109207, by rfl⟩ : syracuseStep 1478943 = 2218415) B2218415
theorem B3330377 : Blo 1478559 3330377 := bstep (se 2 (by rfl) ⟨1248891, by rfl⟩ : syracuseStep 3330377 = 2497783) B2497783
theorem B1479003 : Blo 1478559 1479003 := bstep (se 1 (by rfl) ⟨1109252, by rfl⟩ : syracuseStep 1479003 = 2218505) B2218505
theorem B3330395 : Blo 1478559 3330395 := bstep (se 1 (by rfl) ⟨2497796, by rfl⟩ : syracuseStep 3330395 = 4995593) B4995593
theorem B16003433 : Blo 1478559 16003433 := bstep (se 2 (by rfl) ⟨6001287, by rfl⟩ : syracuseStep 16003433 = 12002575) B12002575
theorem B1479023 : Blo 1478559 1479023 := bstep (se 1 (by rfl) ⟨1109267, by rfl⟩ : syracuseStep 1479023 = 2218535) B2218535
theorem B1479079 : Blo 1478559 1479079 := bstep (se 1 (by rfl) ⟨1109309, by rfl⟩ : syracuseStep 1479079 = 2218619) B2218619
theorem B4215215 : Blo 1478559 4215215 := bstep (se 1 (by rfl) ⟨3161411, by rfl⟩ : syracuseStep 4215215 = 6322823) B6322823
theorem B1479163 : Blo 1478559 1479163 := bstep (se 1 (by rfl) ⟨1109372, by rfl⟩ : syracuseStep 1479163 = 2218745) B2218745
theorem B14414381 : Blo 1478559 14414381 := bstep (se 3 (by rfl) ⟨2702696, by rfl⟩ : syracuseStep 14414381 = 5405393) B5405393
theorem B1479231 : Blo 1478559 1479231 := bstep (se 1 (by rfl) ⟨1109423, by rfl⟩ : syracuseStep 1479231 = 2218847) B2218847
theorem B1479239 : Blo 1478559 1479239 := bstep (se 1 (by rfl) ⟨1109429, by rfl⟩ : syracuseStep 1479239 = 2218859) B2218859
theorem B2495083 : Blo 1478559 2495083 := bstep (se 1 (by rfl) ⟨1871312, by rfl⟩ : syracuseStep 2495083 = 3742625) B3742625
theorem B5698201 : Blo 1478559 5698201 := bstep (se 2 (by rfl) ⟨2136825, by rfl⟩ : syracuseStep 5698201 = 4273651) B4273651
theorem B1479391 : Blo 1478559 1479391 := bstep (se 1 (by rfl) ⟨1109543, by rfl⟩ : syracuseStep 1479391 = 2219087) B2219087
theorem B1479471 : Blo 1478559 1479471 := bstep (se 1 (by rfl) ⟨1109603, by rfl⟩ : syracuseStep 1479471 = 2219207) B2219207
theorem B2495387 : Blo 1478559 2495387 := bstep (se 1 (by rfl) ⟨1871540, by rfl⟩ : syracuseStep 2495387 = 3743081) B3743081
theorem B1479579 : Blo 1478559 1479579 := bstep (se 1 (by rfl) ⟨1109684, by rfl⟩ : syracuseStep 1479579 = 2219369) B2219369
theorem B3330971 : Blo 1478559 3330971 := bstep (se 1 (by rfl) ⟨2498228, by rfl⟩ : syracuseStep 3330971 = 4996457) B4996457
theorem B1479631 : Blo 1478559 1479631 := bstep (se 1 (by rfl) ⟨1109723, by rfl⟩ : syracuseStep 1479631 = 2219447) B2219447
theorem B1479655 : Blo 1478559 1479655 := bstep (se 1 (by rfl) ⟨1109741, by rfl⟩ : syracuseStep 1479655 = 2219483) B2219483
theorem B3331169 : Blo 1478559 3331169 := bstep (se 2 (by rfl) ⟨1249188, by rfl⟩ : syracuseStep 3331169 = 2498377) B2498377
theorem B4740221 : Blo 1478559 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B7492823 : Blo 1478559 7492823 := bstep (se 1 (by rfl) ⟨5619617, by rfl⟩ : syracuseStep 7492823 = 11239235) B11239235
theorem B4994297 : Blo 1478559 4994297 := bstep (se 2 (by rfl) ⟨1872861, by rfl⟩ : syracuseStep 4994297 = 3745723) B3745723
theorem B1479967 : Blo 1478559 1479967 := bstep (se 1 (by rfl) ⟨1109975, by rfl⟩ : syracuseStep 1479967 = 2219951) B2219951
theorem B1480027 : Blo 1478559 1480027 := bstep (se 1 (by rfl) ⟨1110020, by rfl⟩ : syracuseStep 1480027 = 2220041) B2220041
theorem B1480047 : Blo 1478559 1480047 := bstep (se 1 (by rfl) ⟨1110035, by rfl⟩ : syracuseStep 1480047 = 2220071) B2220071
theorem B2053499 : Blo 1478559 2053499 := bstep (se 1 (by rfl) ⟨1540124, by rfl⟩ : syracuseStep 2053499 = 3080249) B3080249
theorem B12637579 : Blo 1478559 12637579 := bstep (se 1 (by rfl) ⟨9478184, by rfl⟩ : syracuseStep 12637579 = 18956369) B18956369
theorem B1480103 : Blo 1478559 1480103 := bstep (se 1 (by rfl) ⟨1110077, by rfl⟩ : syracuseStep 1480103 = 2220155) B2220155
theorem B1480187 : Blo 1478559 1480187 := bstep (se 1 (by rfl) ⟨1110140, by rfl⟩ : syracuseStep 1480187 = 2220281) B2220281
theorem B4994567 : Blo 1478559 4994567 := bstep (se 1 (by rfl) ⟨3745925, by rfl⟩ : syracuseStep 4994567 = 7491851) B7491851
theorem B1480255 : Blo 1478559 1480255 := bstep (se 1 (by rfl) ⟨1110191, by rfl⟩ : syracuseStep 1480255 = 2220383) B2220383
theorem B1480263 : Blo 1478559 1480263 := bstep (se 1 (by rfl) ⟨1110197, by rfl⟩ : syracuseStep 1480263 = 2220395) B2220395
theorem B5617309 : Blo 1478559 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B1873631 : Blo 1478559 1873631 := bstep (se 1 (by rfl) ⟨1405223, by rfl⟩ : syracuseStep 1873631 = 2810447) B2810447
theorem B1480415 : Blo 1478559 1480415 := bstep (se 1 (by rfl) ⟨1110311, by rfl⟩ : syracuseStep 1480415 = 2220623) B2220623
theorem B2807531 : Blo 1478559 2807531 := bstep (se 1 (by rfl) ⟨2105648, by rfl⟩ : syracuseStep 2807531 = 4211297) B4211297
theorem B1480495 : Blo 1478559 1480495 := bstep (se 1 (by rfl) ⟨1110371, by rfl⟩ : syracuseStep 1480495 = 2220743) B2220743
theorem B2217935 : Blo 1478559 2217935 := bstep (se 1 (by rfl) ⟨1663451, by rfl⟩ : syracuseStep 2217935 = 3326903) B3326903
theorem B2807759 : Blo 1478559 2807759 := bstep (se 1 (by rfl) ⟨2105819, by rfl⟩ : syracuseStep 2807759 = 4211639) B4211639
theorem B7108793 : Blo 1478559 7108793 := bstep (se 2 (by rfl) ⟨2665797, by rfl⟩ : syracuseStep 7108793 = 5331595) B5331595
theorem B2218331 : Blo 1478559 2218331 := bstep (se 1 (by rfl) ⟨1663748, by rfl⟩ : syracuseStep 2218331 = 3327497) B3327497
theorem B4995539 : Blo 1478559 4995539 := bstep (se 1 (by rfl) ⟨3746654, by rfl⟩ : syracuseStep 4995539 = 7493309) B7493309
theorem B20240891 : Blo 1478559 20240891 := bstep (se 1 (by rfl) ⟨15180668, by rfl⟩ : syracuseStep 20240891 = 30361337) B30361337
theorem B2218559 : Blo 1478559 2218559 := bstep (se 1 (by rfl) ⟨1663919, by rfl⟩ : syracuseStep 2218559 = 3327839) B3327839
theorem B4995647 : Blo 1478559 4995647 := bstep (se 1 (by rfl) ⟨3746735, by rfl⟩ : syracuseStep 4995647 = 7493471) B7493471
theorem B1579591 : Blo 1478559 1579591 := bstep (se 1 (by rfl) ⟨1184693, by rfl⟩ : syracuseStep 1579591 = 2369387) B2369387
theorem B2808427 : Blo 1478559 2808427 := bstep (se 1 (by rfl) ⟨2106320, by rfl⟩ : syracuseStep 2808427 = 4212641) B4212641
theorem B2218679 : Blo 1478559 2218679 := bstep (se 1 (by rfl) ⟨1664009, by rfl⟩ : syracuseStep 2218679 = 3328019) B3328019
theorem B2808503 : Blo 1478559 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B12638915 : Blo 1478559 12638915 := bstep (se 1 (by rfl) ⟨9479186, by rfl⟩ : syracuseStep 12638915 = 18958373) B18958373
theorem B11999981 : Blo 1478559 11999981 := bstep (se 3 (by rfl) ⟨2249996, by rfl⟩ : syracuseStep 11999981 = 4499993) B4499993
theorem B11238263 : Blo 1478559 11238263 := bstep (se 1 (by rfl) ⟨8428697, by rfl⟩ : syracuseStep 11238263 = 16857395) B16857395
theorem B2218907 : Blo 1478559 2218907 := bstep (se 1 (by rfl) ⟨1664180, by rfl⟩ : syracuseStep 2218907 = 3328361) B3328361
theorem B2808731 : Blo 1478559 2808731 := bstep (se 1 (by rfl) ⟨2106548, by rfl⟩ : syracuseStep 2808731 = 4213097) B4213097
theorem B3374119 : Blo 1478559 3374119 := bstep (se 1 (by rfl) ⟨2530589, by rfl⟩ : syracuseStep 3374119 = 5061179) B5061179
theorem B3742919 : Blo 1478559 3742919 := bstep (se 1 (by rfl) ⟨2807189, by rfl⟩ : syracuseStep 3742919 = 5614379) B5614379
theorem B3742969 : Blo 1478559 3742969 := bstep (se 2 (by rfl) ⟨1403613, by rfl⟩ : syracuseStep 3742969 = 2807227) B2807227
theorem B3996967 : Blo 1478559 3996967 := bstep (se 1 (by rfl) ⟨2997725, by rfl⟩ : syracuseStep 3996967 = 5995451) B5995451
theorem B2219303 : Blo 1478559 2219303 := bstep (se 1 (by rfl) ⟨1664477, by rfl⟩ : syracuseStep 2219303 = 3328955) B3328955
theorem B5619041 : Blo 1478559 5619041 := bstep (se 2 (by rfl) ⟨2107140, by rfl⟩ : syracuseStep 5619041 = 4214281) B4214281
theorem B2219387 : Blo 1478559 2219387 := bstep (se 1 (by rfl) ⟨1664540, by rfl⟩ : syracuseStep 2219387 = 3329081) B3329081
theorem B3161531 : Blo 1478559 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B2219513 : Blo 1478559 2219513 := bstep (se 2 (by rfl) ⟨832317, by rfl⟩ : syracuseStep 2219513 = 1664635) B1664635
theorem B7486991 : Blo 1478559 7486991 := bstep (se 1 (by rfl) ⟨5615243, by rfl⟩ : syracuseStep 7486991 = 11230487) B11230487
theorem B2219615 : Blo 1478559 2219615 := bstep (se 1 (by rfl) ⟨1664711, by rfl⟩ : syracuseStep 2219615 = 3329423) B3329423
theorem B8216225 : Blo 1478559 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B2809505 : Blo 1478559 2809505 := bstep (se 2 (by rfl) ⟨1053564, by rfl⟩ : syracuseStep 2809505 = 2107129) B2107129
theorem B3997487 : Blo 1478559 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B2219831 : Blo 1478559 2219831 := bstep (se 1 (by rfl) ⟨1664873, by rfl⟩ : syracuseStep 2219831 = 3329747) B3329747
theorem B2809657 : Blo 1478559 2809657 := bstep (se 2 (by rfl) ⟨1053621, by rfl⟩ : syracuseStep 2809657 = 2107243) B2107243
theorem B6586219 : Blo 1478559 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B3743617 : Blo 1478559 3743617 := bstep (se 2 (by rfl) ⟨1403856, by rfl⟩ : syracuseStep 3743617 = 2807713) B2807713
theorem B2220251 : Blo 1478559 2220251 := bstep (se 1 (by rfl) ⟨1665188, by rfl⟩ : syracuseStep 2220251 = 3330377) B3330377
theorem B2220263 : Blo 1478559 2220263 := bstep (se 1 (by rfl) ⟨1665197, by rfl⟩ : syracuseStep 2220263 = 3330395) B3330395
theorem B2810143 : Blo 1478559 2810143 := bstep (se 1 (by rfl) ⟨2107607, by rfl⟩ : syracuseStep 2810143 = 4215215) B4215215
theorem B9609587 : Blo 1478559 9609587 := bstep (se 1 (by rfl) ⟨7207190, by rfl⟩ : syracuseStep 9609587 = 14414381) B14414381
theorem B2220425 : Blo 1478559 2220425 := bstep (se 2 (by rfl) ⟨832659, by rfl⟩ : syracuseStep 2220425 = 1665319) B1665319
theorem B10125751 : Blo 1478559 10125751 := bstep (se 1 (by rfl) ⟨7594313, by rfl⟩ : syracuseStep 10125751 = 15188627) B15188627
theorem B5997007 : Blo 1478559 5997007 := bstep (se 1 (by rfl) ⟨4497755, by rfl⟩ : syracuseStep 5997007 = 8995511) B8995511
theorem B2220521 : Blo 1478559 2220521 := bstep (se 2 (by rfl) ⟨832695, by rfl⟩ : syracuseStep 2220521 = 1665391) B1665391
theorem B1663591 : Blo 1478559 1663591 := bstep (se 1 (by rfl) ⟨1247693, by rfl⟩ : syracuseStep 1663591 = 2495387) B2495387
theorem B2220647 : Blo 1478559 2220647 := bstep (se 1 (by rfl) ⟨1665485, by rfl⟩ : syracuseStep 2220647 = 3330971) B3330971
theorem B2220779 : Blo 1478559 2220779 := bstep (se 1 (by rfl) ⟨1665584, by rfl⟩ : syracuseStep 2220779 = 3331169) B3331169
theorem B2220809 : Blo 1478559 2220809 := bstep (se 2 (by rfl) ⟨832803, by rfl⟩ : syracuseStep 2220809 = 1665607) B1665607
theorem B43254577 : Blo 1478559 43254577 := bstep (se 2 (by rfl) ⟨16220466, by rfl⟩ : syracuseStep 43254577 = 32440933) B32440933
theorem B3326777 : Blo 1478559 3326777 := bstep (se 2 (by rfl) ⟨1247541, by rfl⟩ : syracuseStep 3326777 = 2495083) B2495083
theorem B3744569 : Blo 1478559 3744569 := bstep (se 2 (by rfl) ⟨1404213, by rfl⟩ : syracuseStep 3744569 = 2808427) B2808427
theorem B3326831 : Blo 1478559 3326831 := bstep (se 1 (by rfl) ⟨2495123, by rfl⟩ : syracuseStep 3326831 = 4990247) B4990247
theorem B8430749 : Blo 1478559 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B4498825 : Blo 1478559 4498825 := bstep (se 2 (by rfl) ⟨1687059, by rfl⟩ : syracuseStep 4498825 = 3374119) B3374119
theorem B3327407 : Blo 1478559 3327407 := bstep (se 1 (by rfl) ⟨2495555, by rfl⟩ : syracuseStep 3327407 = 4991111) B4991111
theorem B5998175 : Blo 1478559 5998175 := bstep (se 1 (by rfl) ⟨4498631, by rfl⟩ : syracuseStep 5998175 = 8997263) B8997263
theorem B8423027 : Blo 1478559 8423027 := bstep (se 1 (by rfl) ⟨6317270, by rfl⟩ : syracuseStep 8423027 = 12634541) B12634541
theorem B4990625 : Blo 1478559 4990625 := bstep (se 2 (by rfl) ⟨1871484, by rfl⟩ : syracuseStep 4990625 = 3742969) B3742969
theorem B13493927 : Blo 1478559 13493927 := bstep (se 1 (by rfl) ⟨10120445, by rfl⟩ : syracuseStep 13493927 = 20240891) B20240891
theorem B4736735 : Blo 1478559 4736735 := bstep (se 1 (by rfl) ⟨3552551, by rfl⟩ : syracuseStep 4736735 = 7105103) B7105103
theorem B5621471 : Blo 1478559 5621471 := bstep (se 1 (by rfl) ⟨4216103, by rfl⟩ : syracuseStep 5621471 = 8432207) B8432207
theorem B16853021 : Blo 1478559 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B12634163 : Blo 1478559 12634163 := bstep (se 1 (by rfl) ⟨9475622, by rfl⟩ : syracuseStep 12634163 = 18951245) B18951245
theorem B10119293 : Blo 1478559 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B7489745 : Blo 1478559 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B3328235 : Blo 1478559 3328235 := bstep (se 1 (by rfl) ⟨2496176, by rfl⟩ : syracuseStep 3328235 = 4992353) B4992353
theorem B3746027 : Blo 1478559 3746027 := bstep (se 1 (by rfl) ⟨2809520, by rfl⟩ : syracuseStep 3746027 = 5619041) B5619041
theorem B4991327 : Blo 1478559 4991327 := bstep (se 1 (by rfl) ⟨3743495, by rfl⟩ : syracuseStep 4991327 = 7486991) B7486991
theorem B3746209 : Blo 1478559 3746209 := bstep (se 2 (by rfl) ⟨1404828, by rfl⟩ : syracuseStep 3746209 = 2809657) B2809657
theorem B7203329 : Blo 1478559 7203329 := bstep (se 2 (by rfl) ⟨2701248, by rfl⟩ : syracuseStep 7203329 = 5402497) B5402497
theorem B4991489 : Blo 1478559 4991489 := bstep (se 2 (by rfl) ⟨1871808, by rfl⟩ : syracuseStep 4991489 = 3743617) B3743617
theorem B2664991 : Blo 1478559 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B8219339 : Blo 1478559 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B4991975 : Blo 1478559 4991975 := bstep (se 1 (by rfl) ⟨3743981, by rfl⟩ : syracuseStep 4991975 = 7487963) B7487963
theorem B8424485 : Blo 1478559 8424485 := bstep (se 4 (by rfl) ⟨789795, by rfl⟩ : syracuseStep 8424485 = 1579591) B1579591
theorem B9481313 : Blo 1478559 9481313 := bstep (se 2 (by rfl) ⟨3555492, by rfl⟩ : syracuseStep 9481313 = 7110985) B7110985
theorem B4992299 : Blo 1478559 4992299 := bstep (se 1 (by rfl) ⟨3744224, by rfl⟩ : syracuseStep 4992299 = 7488449) B7488449
theorem B28454237 : Blo 1478559 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B9612697 : Blo 1478559 9612697 := bstep (se 2 (by rfl) ⟨3604761, by rfl⟩ : syracuseStep 9612697 = 7209523) B7209523
theorem B3329531 : Blo 1478559 3329531 := bstep (se 1 (by rfl) ⟨2497148, by rfl⟩ : syracuseStep 3329531 = 4994297) B4994297
theorem B3747323 : Blo 1478559 3747323 := bstep (se 1 (by rfl) ⟨2810492, by rfl⟩ : syracuseStep 3747323 = 5620985) B5620985
theorem B7597601 : Blo 1478559 7597601 := bstep (se 2 (by rfl) ⟨2849100, by rfl⟩ : syracuseStep 7597601 = 5698201) B5698201
theorem B4992569 : Blo 1478559 4992569 := bstep (se 2 (by rfl) ⟨1872213, by rfl⟩ : syracuseStep 4992569 = 3744427) B3744427
theorem B42675821 : Blo 1478559 42675821 := bstep (se 3 (by rfl) ⟨8001716, by rfl⟩ : syracuseStep 42675821 = 16003433) B16003433
theorem B5475997 : Blo 1478559 5475997 := bstep (se 3 (by rfl) ⟨1026749, by rfl⟩ : syracuseStep 5475997 = 2053499) B2053499
theorem B3329711 : Blo 1478559 3329711 := bstep (se 1 (by rfl) ⟨2497283, by rfl⟩ : syracuseStep 3329711 = 4994567) B4994567
theorem B1871687 : Blo 1478559 1871687 := bstep (se 1 (by rfl) ⟨1403765, by rfl⟩ : syracuseStep 1871687 = 2807531) B2807531
theorem B10661807 : Blo 1478559 10661807 := bstep (se 1 (by rfl) ⟨7996355, by rfl⟩ : syracuseStep 10661807 = 15992711) B15992711
theorem B1478623 : Blo 1478559 1478623 := bstep (se 1 (by rfl) ⟨1108967, by rfl⟩ : syracuseStep 1478623 = 2217935) B2217935
theorem B1871839 : Blo 1478559 1871839 := bstep (se 1 (by rfl) ⟨1403879, by rfl⟩ : syracuseStep 1871839 = 2807759) B2807759
theorem B7999469 : Blo 1478559 7999469 := bstep (se 3 (by rfl) ⟨1499900, by rfl⟩ : syracuseStep 7999469 = 2999801) B2999801
theorem B4739195 : Blo 1478559 4739195 := bstep (se 1 (by rfl) ⟨3554396, by rfl⟩ : syracuseStep 4739195 = 7108793) B7108793
theorem B1478887 : Blo 1478559 1478887 := bstep (se 1 (by rfl) ⟨1109165, by rfl⟩ : syracuseStep 1478887 = 2218331) B2218331
theorem B3330359 : Blo 1478559 3330359 := bstep (se 1 (by rfl) ⟨2497769, by rfl⟩ : syracuseStep 3330359 = 4995539) B4995539
theorem B17994089 : Blo 1478559 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B1479039 : Blo 1478559 1479039 := bstep (se 1 (by rfl) ⟨1109279, by rfl⟩ : syracuseStep 1479039 = 2218559) B2218559
theorem B3330431 : Blo 1478559 3330431 := bstep (se 1 (by rfl) ⟨2497823, by rfl⟩ : syracuseStep 3330431 = 4995647) B4995647
theorem B5329289 : Blo 1478559 5329289 := bstep (se 2 (by rfl) ⟨1998483, by rfl⟩ : syracuseStep 5329289 = 3996967) B3996967
theorem B6320551 : Blo 1478559 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B7492013 : Blo 1478559 7492013 := bstep (se 3 (by rfl) ⟨1404752, by rfl⟩ : syracuseStep 7492013 = 2809505) B2809505
theorem B1479119 : Blo 1478559 1479119 := bstep (se 1 (by rfl) ⟨1109339, by rfl⟩ : syracuseStep 1479119 = 2218679) B2218679
theorem B1872335 : Blo 1478559 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B8425943 : Blo 1478559 8425943 := bstep (se 1 (by rfl) ⟨6319457, by rfl⟩ : syracuseStep 8425943 = 12638915) B12638915
theorem B7999987 : Blo 1478559 7999987 := bstep (se 1 (by rfl) ⟨5999990, by rfl⟩ : syracuseStep 7999987 = 11999981) B11999981
theorem B7492175 : Blo 1478559 7492175 := bstep (se 1 (by rfl) ⟨5619131, by rfl⟩ : syracuseStep 7492175 = 11238263) B11238263
theorem B1479271 : Blo 1478559 1479271 := bstep (se 1 (by rfl) ⟨1109453, by rfl⟩ : syracuseStep 1479271 = 2218907) B2218907
theorem B1872487 : Blo 1478559 1872487 := bstep (se 1 (by rfl) ⟨1404365, by rfl⟩ : syracuseStep 1872487 = 2808731) B2808731
theorem B2134793 : Blo 1478559 2134793 := bstep (se 2 (by rfl) ⟨800547, by rfl⟩ : syracuseStep 2134793 = 1601095) B1601095
theorem B2495279 : Blo 1478559 2495279 := bstep (se 1 (by rfl) ⟨1871459, by rfl⟩ : syracuseStep 2495279 = 3742919) B3742919
theorem B1479535 : Blo 1478559 1479535 := bstep (se 1 (by rfl) ⟨1109651, by rfl⟩ : syracuseStep 1479535 = 2219303) B2219303
theorem B1479591 : Blo 1478559 1479591 := bstep (se 1 (by rfl) ⟨1109693, by rfl⟩ : syracuseStep 1479591 = 2219387) B2219387
theorem B1479675 : Blo 1478559 1479675 := bstep (se 1 (by rfl) ⟨1109756, by rfl⟩ : syracuseStep 1479675 = 2219513) B2219513
theorem B1479743 : Blo 1478559 1479743 := bstep (se 1 (by rfl) ⟨1109807, by rfl⟩ : syracuseStep 1479743 = 2219615) B2219615
theorem B5477483 : Blo 1478559 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B14218355 : Blo 1478559 14218355 := bstep (se 1 (by rfl) ⟨10663766, by rfl⟩ : syracuseStep 14218355 = 21327533) B21327533
theorem B1479887 : Blo 1478559 1479887 := bstep (se 1 (by rfl) ⟨1109915, by rfl⟩ : syracuseStep 1479887 = 2219831) B2219831
theorem B4994459 : Blo 1478559 4994459 := bstep (se 1 (by rfl) ⟨3745844, by rfl⟩ : syracuseStep 4994459 = 7491689) B7491689
theorem B1480091 : Blo 1478559 1480091 := bstep (se 1 (by rfl) ⟨1110068, by rfl⟩ : syracuseStep 1480091 = 2220137) B2220137
theorem B1873307 : Blo 1478559 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B1480303 : Blo 1478559 1480303 := bstep (se 1 (by rfl) ⟨1110227, by rfl⟩ : syracuseStep 1480303 = 2220455) B2220455
theorem B1480359 : Blo 1478559 1480359 := bstep (se 1 (by rfl) ⟨1110269, by rfl⟩ : syracuseStep 1480359 = 2220539) B2220539
theorem B28456697 : Blo 1478559 28456697 := bstep (se 2 (by rfl) ⟨10671261, by rfl⟩ : syracuseStep 28456697 = 21342523) B21342523
theorem B2496251 : Blo 1478559 2496251 := bstep (se 1 (by rfl) ⟨1872188, by rfl⟩ : syracuseStep 2496251 = 3744377) B3744377
theorem B1480443 : Blo 1478559 1480443 := bstep (se 1 (by rfl) ⟨1110332, by rfl⟩ : syracuseStep 1480443 = 2220665) B2220665
theorem B1480479 : Blo 1478559 1480479 := bstep (se 1 (by rfl) ⟨1110359, by rfl⟩ : syracuseStep 1480479 = 2220719) B2220719
theorem B2807615 : Blo 1478559 2807615 := bstep (se 1 (by rfl) ⟨2105711, by rfl⟩ : syracuseStep 2807615 = 4211423) B4211423
theorem B1480511 : Blo 1478559 1480511 := bstep (se 1 (by rfl) ⟨1110383, by rfl⟩ : syracuseStep 1480511 = 2220767) B2220767
theorem B13490135 : Blo 1478559 13490135 := bstep (se 1 (by rfl) ⟨10117601, by rfl⟩ : syracuseStep 13490135 = 20235203) B20235203
theorem B2217959 : Blo 1478559 2217959 := bstep (se 1 (by rfl) ⟨1663469, by rfl⟩ : syracuseStep 2217959 = 3326939) B3326939
theorem B2496487 : Blo 1478559 2496487 := bstep (se 1 (by rfl) ⟨1872365, by rfl⟩ : syracuseStep 2496487 = 3744731) B3744731
theorem B2217977 : Blo 1478559 2217977 := bstep (se 2 (by rfl) ⟨831741, by rfl⟩ : syracuseStep 2217977 = 1663483) B1663483
theorem B7493633 : Blo 1478559 7493633 := bstep (se 2 (by rfl) ⟨2810112, by rfl⟩ : syracuseStep 7493633 = 5620225) B5620225
theorem B3160147 : Blo 1478559 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B2218079 : Blo 1478559 2218079 := bstep (se 1 (by rfl) ⟨1663559, by rfl⟩ : syracuseStep 2218079 = 3327119) B3327119
theorem B4995215 : Blo 1478559 4995215 := bstep (se 1 (by rfl) ⟨3746411, by rfl⟩ : syracuseStep 4995215 = 7492823) B7492823
theorem B2218139 : Blo 1478559 2218139 := bstep (se 1 (by rfl) ⟨1663604, by rfl⟩ : syracuseStep 2218139 = 3327209) B3327209
theorem B2218175 : Blo 1478559 2218175 := bstep (se 1 (by rfl) ⟨1663631, by rfl⟩ : syracuseStep 2218175 = 3327263) B3327263
theorem B2496703 : Blo 1478559 2496703 := bstep (se 1 (by rfl) ⟨1872527, by rfl⟩ : syracuseStep 2496703 = 3745055) B3745055
theorem B2218217 : Blo 1478559 2218217 := bstep (se 2 (by rfl) ⟨831831, by rfl⟩ : syracuseStep 2218217 = 1663663) B1663663
theorem B41613749 : Blo 1478559 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B127900133 : Blo 1478559 127900133 := bstep (se 4 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 127900133 = 23981275) B23981275
theorem B2218523 : Blo 1478559 2218523 := bstep (se 1 (by rfl) ⟨1663892, by rfl⟩ : syracuseStep 2218523 = 3327785) B3327785
theorem B2218601 : Blo 1478559 2218601 := bstep (se 2 (by rfl) ⟨831975, by rfl⟩ : syracuseStep 2218601 = 1663951) B1663951
theorem B7494281 : Blo 1478559 7494281 := bstep (se 2 (by rfl) ⟨2810355, by rfl⟩ : syracuseStep 7494281 = 5620711) B5620711
theorem B7494443 : Blo 1478559 7494443 := bstep (se 1 (by rfl) ⟨5620832, by rfl⟩ : syracuseStep 7494443 = 11241665) B11241665
theorem B2497439 : Blo 1478559 2497439 := bstep (se 1 (by rfl) ⟨1873079, by rfl⟩ : syracuseStep 2497439 = 3746159) B3746159
theorem B7486505 : Blo 1478559 7486505 := bstep (se 2 (by rfl) ⟨2807439, by rfl⟩ : syracuseStep 7486505 = 5614879) B5614879
theorem B2219129 : Blo 1478559 2219129 := bstep (se 2 (by rfl) ⟨832173, by rfl⟩ : syracuseStep 2219129 = 1664347) B1664347
theorem B16850105 : Blo 1478559 16850105 := bstep (se 2 (by rfl) ⟨6318789, by rfl⟩ : syracuseStep 16850105 = 12637579) B12637579
theorem B2219231 : Blo 1478559 2219231 := bstep (se 1 (by rfl) ⟨1664423, by rfl⟩ : syracuseStep 2219231 = 3328847) B3328847
theorem B31997177 : Blo 1478559 31997177 := bstep (se 2 (by rfl) ⟨11998941, by rfl⟩ : syracuseStep 31997177 = 23997883) B23997883
theorem B4996349 : Blo 1478559 4996349 := bstep (se 3 (by rfl) ⟨936815, by rfl⟩ : syracuseStep 4996349 = 1873631) B1873631
theorem B2219273 : Blo 1478559 2219273 := bstep (se 2 (by rfl) ⟨832227, by rfl⟩ : syracuseStep 2219273 = 1664455) B1664455
theorem B2497871 : Blo 1478559 2497871 := bstep (se 1 (by rfl) ⟨1873403, by rfl⟩ : syracuseStep 2497871 = 3746807) B3746807
theorem B2219375 : Blo 1478559 2219375 := bstep (se 1 (by rfl) ⟨1664531, by rfl⟩ : syracuseStep 2219375 = 3329063) B3329063
theorem B2809255 : Blo 1478559 2809255 := bstep (se 1 (by rfl) ⟨2106941, by rfl⟩ : syracuseStep 2809255 = 4213883) B4213883
theorem B2219495 : Blo 1478559 2219495 := bstep (se 1 (by rfl) ⟨1664621, by rfl⟩ : syracuseStep 2219495 = 3329243) B3329243
theorem B2219627 : Blo 1478559 2219627 := bstep (se 1 (by rfl) ⟨1664720, by rfl⟩ : syracuseStep 2219627 = 3329441) B3329441
theorem B2219753 : Blo 1478559 2219753 := bstep (se 2 (by rfl) ⟨832407, by rfl⟩ : syracuseStep 2219753 = 1664815) B1664815
theorem B8429291 : Blo 1478559 8429291 := bstep (se 1 (by rfl) ⟨6321968, by rfl⟩ : syracuseStep 8429291 = 12643937) B12643937
theorem B8781625 : Blo 1478559 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B2219897 : Blo 1478559 2219897 := bstep (se 2 (by rfl) ⟨832461, by rfl⟩ : syracuseStep 2219897 = 1664923) B1664923
theorem B2219999 : Blo 1478559 2219999 := bstep (se 1 (by rfl) ⟨1664999, by rfl⟩ : syracuseStep 2219999 = 3329999) B3329999
theorem B2220239 : Blo 1478559 2220239 := bstep (se 1 (by rfl) ⟨1665179, by rfl⟩ : syracuseStep 2220239 = 3330359) B3330359
theorem B6406391 : Blo 1478559 6406391 := bstep (se 1 (by rfl) ⟨4804793, by rfl⟩ : syracuseStep 6406391 = 9609587) B9609587
theorem B2220287 : Blo 1478559 2220287 := bstep (se 1 (by rfl) ⟨1665215, by rfl⟩ : syracuseStep 2220287 = 3330431) B3330431
theorem B1663519 : Blo 1478559 1663519 := bstep (se 1 (by rfl) ⟨1247639, by rfl⟩ : syracuseStep 1663519 = 2495279) B2495279
theorem B13501001 : Blo 1478559 13501001 := bstep (se 2 (by rfl) ⟨5062875, by rfl⟩ : syracuseStep 13501001 = 10125751) B10125751
theorem B7996009 : Blo 1478559 7996009 := bstep (se 2 (by rfl) ⟨2998503, by rfl⟩ : syracuseStep 7996009 = 5997007) B5997007
theorem B10666649 : Blo 1478559 10666649 := bstep (se 2 (by rfl) ⟨3999993, by rfl⟩ : syracuseStep 10666649 = 7999987) B7999987
theorem B9478903 : Blo 1478559 9478903 := bstep (se 1 (by rfl) ⟨7109177, by rfl⟩ : syracuseStep 9478903 = 14218355) B14218355
theorem B5620499 : Blo 1478559 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B3998783 : Blo 1478559 3998783 := bstep (se 1 (by rfl) ⟨2999087, by rfl⟩ : syracuseStep 3998783 = 5998175) B5998175
theorem B57672769 : Blo 1478559 57672769 := bstep (se 2 (by rfl) ⟨21627288, by rfl⟩ : syracuseStep 57672769 = 43254577) B43254577
theorem B3327083 : Blo 1478559 3327083 := bstep (se 1 (by rfl) ⟨2495312, by rfl⟩ : syracuseStep 3327083 = 4990625) B4990625
theorem B8995951 : Blo 1478559 8995951 := bstep (se 1 (by rfl) ⟨6746963, by rfl⟩ : syracuseStep 8995951 = 13493927) B13493927
theorem B1664167 : Blo 1478559 1664167 := bstep (se 1 (by rfl) ⟨1248125, by rfl⟩ : syracuseStep 1664167 = 2496251) B2496251
theorem B8422775 : Blo 1478559 8422775 := bstep (se 1 (by rfl) ⟨6317081, by rfl⟩ : syracuseStep 8422775 = 12634163) B12634163
theorem B3327551 : Blo 1478559 3327551 := bstep (se 1 (by rfl) ⟨2495663, by rfl⟩ : syracuseStep 3327551 = 4991327) B4991327
theorem B4802219 : Blo 1478559 4802219 := bstep (se 1 (by rfl) ⟨3601664, by rfl⟩ : syracuseStep 4802219 = 7203329) B7203329
theorem B3327659 : Blo 1478559 3327659 := bstep (se 1 (by rfl) ⟨2495744, by rfl⟩ : syracuseStep 3327659 = 4991489) B4991489
theorem B5998433 : Blo 1478559 5998433 := bstep (se 2 (by rfl) ⟨2249412, by rfl⟩ : syracuseStep 5998433 = 4498825) B4498825
theorem B3745673 : Blo 1478559 3745673 := bstep (se 2 (by rfl) ⟨1404627, by rfl⟩ : syracuseStep 3745673 = 2809255) B2809255
theorem B1664959 : Blo 1478559 1664959 := bstep (se 1 (by rfl) ⟨1248719, by rfl⟩ : syracuseStep 1664959 = 2497439) B2497439
theorem B3327983 : Blo 1478559 3327983 := bstep (se 1 (by rfl) ⟨2495987, by rfl⟩ : syracuseStep 3327983 = 4991975) B4991975
theorem B4991003 : Blo 1478559 4991003 := bstep (se 1 (by rfl) ⟨3743252, by rfl⟩ : syracuseStep 4991003 = 7486505) B7486505
theorem B11233403 : Blo 1478559 11233403 := bstep (se 1 (by rfl) ⟨8425052, by rfl⟩ : syracuseStep 11233403 = 16850105) B16850105
theorem B4991165 : Blo 1478559 4991165 := bstep (se 3 (by rfl) ⟨935843, by rfl⟩ : syracuseStep 4991165 = 1871687) B1871687
theorem B3328199 : Blo 1478559 3328199 := bstep (se 1 (by rfl) ⟨2496149, by rfl⟩ : syracuseStep 3328199 = 4992299) B4992299
theorem B7301329 : Blo 1478559 7301329 := bstep (se 2 (by rfl) ⟨2737998, by rfl⟩ : syracuseStep 7301329 = 5475997) B5475997
theorem B1665247 : Blo 1478559 1665247 := bstep (se 1 (by rfl) ⟨1248935, by rfl⟩ : syracuseStep 1665247 = 2497871) B2497871
theorem B5065067 : Blo 1478559 5065067 := bstep (se 1 (by rfl) ⟨3798800, by rfl⟩ : syracuseStep 5065067 = 7597601) B7597601
theorem B3328379 : Blo 1478559 3328379 := bstep (se 1 (by rfl) ⟨2496284, by rfl⟩ : syracuseStep 3328379 = 4992569) B4992569
theorem B11708833 : Blo 1478559 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B3328649 : Blo 1478559 3328649 := bstep (se 2 (by rfl) ⟨1248243, by rfl⟩ : syracuseStep 3328649 = 2496487) B2496487
theorem B4213529 : Blo 1478559 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B3328937 : Blo 1478559 3328937 := bstep (se 2 (by rfl) ⟨1248351, by rfl⟩ : syracuseStep 3328937 = 2496703) B2496703
theorem B3746857 : Blo 1478559 3746857 := bstep (se 2 (by rfl) ⟨1405071, by rfl⟩ : syracuseStep 3746857 = 2810143) B2810143
theorem B3329639 : Blo 1478559 3329639 := bstep (se 1 (by rfl) ⟨2497229, by rfl⟩ : syracuseStep 3329639 = 4994459) B4994459
theorem B47984237 : Blo 1478559 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B5615351 : Blo 1478559 5615351 := bstep (se 1 (by rfl) ⟨4211513, by rfl⟩ : syracuseStep 5615351 = 8423027) B8423027
theorem B3157823 : Blo 1478559 3157823 := bstep (se 1 (by rfl) ⟨2368367, by rfl⟩ : syracuseStep 3157823 = 4736735) B4736735
theorem B3747647 : Blo 1478559 3747647 := bstep (se 1 (by rfl) ⟨2810735, by rfl⟩ : syracuseStep 3747647 = 5621471) B5621471
theorem B4992893 : Blo 1478559 4992893 := bstep (se 3 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 4992893 = 1872335) B1872335
theorem B1871743 : Blo 1478559 1871743 := bstep (se 1 (by rfl) ⟨1403807, by rfl⟩ : syracuseStep 1871743 = 2807615) B2807615
theorem B1478639 : Blo 1478559 1478639 := bstep (se 1 (by rfl) ⟨1108979, by rfl⟩ : syracuseStep 1478639 = 2217959) B2217959
theorem B1478651 : Blo 1478559 1478651 := bstep (se 1 (by rfl) ⟨1108988, by rfl⟩ : syracuseStep 1478651 = 2217977) B2217977
theorem B11235347 : Blo 1478559 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B1478719 : Blo 1478559 1478719 := bstep (se 1 (by rfl) ⟨1109039, by rfl⟩ : syracuseStep 1478719 = 2218079) B2218079
theorem B6746195 : Blo 1478559 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B3330143 : Blo 1478559 3330143 := bstep (se 1 (by rfl) ⟨2497607, by rfl⟩ : syracuseStep 3330143 = 4995215) B4995215
theorem B1478759 : Blo 1478559 1478759 := bstep (se 1 (by rfl) ⟨1109069, by rfl⟩ : syracuseStep 1478759 = 2218139) B2218139
theorem B1478783 : Blo 1478559 1478783 := bstep (se 1 (by rfl) ⟨1109087, by rfl⟩ : syracuseStep 1478783 = 2218175) B2218175
theorem B4993163 : Blo 1478559 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B1478811 : Blo 1478559 1478811 := bstep (se 1 (by rfl) ⟨1109108, by rfl⟩ : syracuseStep 1478811 = 2218217) B2218217
theorem B27742499 : Blo 1478559 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B85266755 : Blo 1478559 85266755 := bstep (se 1 (by rfl) ⟨63950066, by rfl⟩ : syracuseStep 85266755 = 127900133) B127900133
theorem B1479015 : Blo 1478559 1479015 := bstep (se 1 (by rfl) ⟨1109261, by rfl⟩ : syracuseStep 1479015 = 2218523) B2218523
theorem B1479067 : Blo 1478559 1479067 := bstep (se 1 (by rfl) ⟨1109300, by rfl⟩ : syracuseStep 1479067 = 2218601) B2218601
theorem B12816929 : Blo 1478559 12816929 := bstep (se 2 (by rfl) ⟨4806348, by rfl⟩ : syracuseStep 12816929 = 9612697) B9612697
theorem B5616323 : Blo 1478559 5616323 := bstep (se 1 (by rfl) ⟨4212242, by rfl⟩ : syracuseStep 5616323 = 8424485) B8424485
theorem B6320875 : Blo 1478559 6320875 := bstep (se 1 (by rfl) ⟨4740656, by rfl⟩ : syracuseStep 6320875 = 9481313) B9481313
theorem B1479419 : Blo 1478559 1479419 := bstep (se 1 (by rfl) ⟨1109564, by rfl⟩ : syracuseStep 1479419 = 2219129) B2219129
theorem B1479487 : Blo 1478559 1479487 := bstep (se 1 (by rfl) ⟨1109615, by rfl⟩ : syracuseStep 1479487 = 2219231) B2219231
theorem B3330899 : Blo 1478559 3330899 := bstep (se 1 (by rfl) ⟨2498174, by rfl⟩ : syracuseStep 3330899 = 4996349) B4996349
theorem B1479515 : Blo 1478559 1479515 := bstep (se 1 (by rfl) ⟨1109636, by rfl⟩ : syracuseStep 1479515 = 2219273) B2219273
theorem B18969491 : Blo 1478559 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B1479583 : Blo 1478559 1479583 := bstep (se 1 (by rfl) ⟨1109687, by rfl⟩ : syracuseStep 1479583 = 2219375) B2219375
theorem B1479663 : Blo 1478559 1479663 := bstep (se 1 (by rfl) ⟨1109747, by rfl⟩ : syracuseStep 1479663 = 2219495) B2219495
theorem B1479751 : Blo 1478559 1479751 := bstep (se 1 (by rfl) ⟨1109813, by rfl⟩ : syracuseStep 1479751 = 2219627) B2219627
theorem B1479835 : Blo 1478559 1479835 := bstep (se 1 (by rfl) ⟨1109876, by rfl⟩ : syracuseStep 1479835 = 2219753) B2219753
theorem B1479931 : Blo 1478559 1479931 := bstep (se 1 (by rfl) ⟨1109948, by rfl⟩ : syracuseStep 1479931 = 2219897) B2219897
theorem B7107871 : Blo 1478559 7107871 := bstep (se 1 (by rfl) ⟨5330903, by rfl⟩ : syracuseStep 7107871 = 10661807) B10661807
theorem B2495785 : Blo 1478559 2495785 := bstep (se 2 (by rfl) ⟨935919, by rfl⟩ : syracuseStep 2495785 = 1871839) B1871839
theorem B1479999 : Blo 1478559 1479999 := bstep (se 1 (by rfl) ⟨1109999, by rfl⟩ : syracuseStep 1479999 = 2219999) B2219999
theorem B1480167 : Blo 1478559 1480167 := bstep (se 1 (by rfl) ⟨1110125, by rfl⟩ : syracuseStep 1480167 = 2220251) B2220251
theorem B1480175 : Blo 1478559 1480175 := bstep (se 1 (by rfl) ⟨1110131, by rfl⟩ : syracuseStep 1480175 = 2220263) B2220263
theorem B3552859 : Blo 1478559 3552859 := bstep (se 1 (by rfl) ⟨2664644, by rfl⟩ : syracuseStep 3552859 = 5329289) B5329289
theorem B1480283 : Blo 1478559 1480283 := bstep (se 1 (by rfl) ⟨1110212, by rfl⟩ : syracuseStep 1480283 = 2220425) B2220425
theorem B4994675 : Blo 1478559 4994675 := bstep (se 1 (by rfl) ⟨3746006, by rfl⟩ : syracuseStep 4994675 = 7492013) B7492013
theorem B5617295 : Blo 1478559 5617295 := bstep (se 1 (by rfl) ⟨4212971, by rfl⟩ : syracuseStep 5617295 = 8425943) B8425943
theorem B1480347 : Blo 1478559 1480347 := bstep (se 1 (by rfl) ⟨1110260, by rfl⟩ : syracuseStep 1480347 = 2220521) B2220521
theorem B12637853 : Blo 1478559 12637853 := bstep (se 3 (by rfl) ⟨2369597, by rfl⟩ : syracuseStep 12637853 = 4739195) B4739195
theorem B4994783 : Blo 1478559 4994783 := bstep (se 1 (by rfl) ⟨3746087, by rfl⟩ : syracuseStep 4994783 = 7492175) B7492175
theorem B1480431 : Blo 1478559 1480431 := bstep (se 1 (by rfl) ⟨1110323, by rfl⟩ : syracuseStep 1480431 = 2220647) B2220647
theorem B1480519 : Blo 1478559 1480519 := bstep (se 1 (by rfl) ⟨1110389, by rfl⟩ : syracuseStep 1480519 = 2220779) B2220779
theorem B1480539 : Blo 1478559 1480539 := bstep (se 1 (by rfl) ⟨1110404, by rfl⟩ : syracuseStep 1480539 = 2220809) B2220809
theorem B2217851 : Blo 1478559 2217851 := bstep (se 1 (by rfl) ⟨1663388, by rfl⟩ : syracuseStep 2217851 = 3326777) B3326777
theorem B2496379 : Blo 1478559 2496379 := bstep (se 1 (by rfl) ⟨1872284, by rfl⟩ : syracuseStep 2496379 = 3744569) B3744569
theorem B4994945 : Blo 1478559 4994945 := bstep (se 2 (by rfl) ⟨1873104, by rfl⟩ : syracuseStep 4994945 = 3746209) B3746209
theorem B8427401 : Blo 1478559 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B2217887 : Blo 1478559 2217887 := bstep (se 1 (by rfl) ⟨1663415, by rfl⟩ : syracuseStep 2217887 = 3326831) B3326831
theorem B3553321 : Blo 1478559 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B3651655 : Blo 1478559 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B2218121 : Blo 1478559 2218121 := bstep (se 2 (by rfl) ⟨831795, by rfl⟩ : syracuseStep 2218121 = 1663591) B1663591
theorem B2496649 : Blo 1478559 2496649 := bstep (se 2 (by rfl) ⟨936243, by rfl⟩ : syracuseStep 2496649 = 1872487) B1872487
theorem B2218271 : Blo 1478559 2218271 := bstep (se 1 (by rfl) ⟨1663703, by rfl⟩ : syracuseStep 2218271 = 3327407) B3327407
theorem B4995485 : Blo 1478559 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B18971131 : Blo 1478559 18971131 := bstep (se 1 (by rfl) ⟨14228348, by rfl⟩ : syracuseStep 18971131 = 28456697) B28456697
theorem B8993423 : Blo 1478559 8993423 := bstep (se 1 (by rfl) ⟨6745067, by rfl⟩ : syracuseStep 8993423 = 13490135) B13490135
theorem B4995755 : Blo 1478559 4995755 := bstep (se 1 (by rfl) ⟨3746816, by rfl⟩ : syracuseStep 4995755 = 7493633) B7493633
theorem B2218823 : Blo 1478559 2218823 := bstep (se 1 (by rfl) ⟨1664117, by rfl⟩ : syracuseStep 2218823 = 3328235) B3328235
theorem B2497351 : Blo 1478559 2497351 := bstep (se 1 (by rfl) ⟨1873013, by rfl⟩ : syracuseStep 2497351 = 3746027) B3746027
theorem B4996187 : Blo 1478559 4996187 := bstep (se 1 (by rfl) ⟨3747140, by rfl⟩ : syracuseStep 4996187 = 7494281) B7494281
theorem B5479559 : Blo 1478559 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B4996295 : Blo 1478559 4996295 := bstep (se 1 (by rfl) ⟨3747221, by rfl⟩ : syracuseStep 4996295 = 7494443) B7494443
theorem B5692781 : Blo 1478559 5692781 := bstep (se 3 (by rfl) ⟨1067396, by rfl⟩ : syracuseStep 5692781 = 2134793) B2134793
theorem B21331451 : Blo 1478559 21331451 := bstep (se 1 (by rfl) ⟨15998588, by rfl⟩ : syracuseStep 21331451 = 31997177) B31997177
theorem B2219687 : Blo 1478559 2219687 := bstep (se 1 (by rfl) ⟨1664765, by rfl⟩ : syracuseStep 2219687 = 3329531) B3329531
theorem B2498215 : Blo 1478559 2498215 := bstep (se 1 (by rfl) ⟨1873661, by rfl⟩ : syracuseStep 2498215 = 3747323) B3747323
theorem B28450547 : Blo 1478559 28450547 := bstep (se 1 (by rfl) ⟨21337910, by rfl⟩ : syracuseStep 28450547 = 42675821) B42675821
theorem B2219807 : Blo 1478559 2219807 := bstep (se 1 (by rfl) ⟨1664855, by rfl⟩ : syracuseStep 2219807 = 3329711) B3329711
theorem B5619527 : Blo 1478559 5619527 := bstep (se 1 (by rfl) ⟨4214645, by rfl⟩ : syracuseStep 5619527 = 8429291) B8429291
theorem B5332979 : Blo 1478559 5332979 := bstep (se 1 (by rfl) ⟨3999734, by rfl⟩ : syracuseStep 5332979 = 7999469) B7999469
theorem B4497463 : Blo 1478559 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B2220095 : Blo 1478559 2220095 := bstep (se 1 (by rfl) ⟨1665071, by rfl⟩ : syracuseStep 2220095 = 3330143) B3330143
theorem B56844503 : Blo 1478559 56844503 := bstep (se 1 (by rfl) ⟨42633377, by rfl⟩ : syracuseStep 56844503 = 85266755) B85266755
theorem B2220329 : Blo 1478559 2220329 := bstep (se 2 (by rfl) ⟨832623, by rfl⟩ : syracuseStep 2220329 = 1665247) B1665247
theorem B8544619 : Blo 1478559 8544619 := bstep (se 1 (by rfl) ⟨6408464, by rfl⟩ : syracuseStep 8544619 = 12816929) B12816929
theorem B7111099 : Blo 1478559 7111099 := bstep (se 1 (by rfl) ⟨5333324, by rfl⟩ : syracuseStep 7111099 = 10666649) B10666649
theorem B3744215 : Blo 1478559 3744215 := bstep (se 1 (by rfl) ⟨2808161, by rfl⟩ : syracuseStep 3744215 = 5616323) B5616323
theorem B2220599 : Blo 1478559 2220599 := bstep (se 1 (by rfl) ⟨1665449, by rfl⟩ : syracuseStep 2220599 = 3330899) B3330899
theorem B3744863 : Blo 1478559 3744863 := bstep (se 1 (by rfl) ⟨2808647, by rfl⟩ : syracuseStep 3744863 = 5617295) B5617295
theorem B3327335 : Blo 1478559 3327335 := bstep (se 1 (by rfl) ⟨2495501, by rfl⟩ : syracuseStep 3327335 = 4991003) B4991003
theorem B7488935 : Blo 1478559 7488935 := bstep (se 1 (by rfl) ⟨5616701, by rfl⟩ : syracuseStep 7488935 = 11233403) B11233403
theorem B3327443 : Blo 1478559 3327443 := bstep (se 1 (by rfl) ⟨2495582, by rfl⟩ : syracuseStep 3327443 = 4991165) B4991165
theorem B11994601 : Blo 1478559 11994601 := bstep (se 2 (by rfl) ⟨4497975, by rfl⟩ : syracuseStep 11994601 = 8995951) B8995951
theorem B3376711 : Blo 1478559 3376711 := bstep (se 1 (by rfl) ⟨2532533, by rfl⟩ : syracuseStep 3376711 = 5065067) B5065067
theorem B3327713 : Blo 1478559 3327713 := bstep (se 2 (by rfl) ⟨1247892, by rfl⟩ : syracuseStep 3327713 = 2495785) B2495785
theorem B4737145 : Blo 1478559 4737145 := bstep (se 2 (by rfl) ⟨1776429, by rfl⟩ : syracuseStep 4737145 = 3552859) B3552859
theorem B3795187 : Blo 1478559 3795187 := bstep (se 1 (by rfl) ⟨2846390, by rfl⟩ : syracuseStep 3795187 = 5692781) B5692781
theorem B18967031 : Blo 1478559 18967031 := bstep (se 1 (by rfl) ⟨14225273, by rfl⟩ : syracuseStep 18967031 = 28450547) B28450547
theorem B3328505 : Blo 1478559 3328505 := bstep (se 2 (by rfl) ⟨1248189, by rfl⟩ : syracuseStep 3328505 = 2496379) B2496379
theorem B3746351 : Blo 1478559 3746351 := bstep (se 1 (by rfl) ⟨2809763, by rfl⟩ : syracuseStep 3746351 = 5619527) B5619527
theorem B3328595 : Blo 1478559 3328595 := bstep (se 1 (by rfl) ⟨2496446, by rfl⟩ : syracuseStep 3328595 = 4992893) B4992893
theorem B7490231 : Blo 1478559 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B4737761 : Blo 1478559 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B3328775 : Blo 1478559 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B4868873 : Blo 1478559 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B4270927 : Blo 1478559 4270927 := bstep (se 1 (by rfl) ⟨3203195, by rfl⟩ : syracuseStep 4270927 = 6406391) B6406391
theorem B3328865 : Blo 1478559 3328865 := bstep (se 2 (by rfl) ⟨1248324, by rfl⟩ : syracuseStep 3328865 = 2496649) B2496649
theorem B3746999 : Blo 1478559 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B2665855 : Blo 1478559 2665855 := bstep (se 1 (by rfl) ⟨1999391, by rfl⟩ : syracuseStep 2665855 = 3998783) B3998783
theorem B10661345 : Blo 1478559 10661345 := bstep (se 2 (by rfl) ⟨3998004, by rfl⟩ : syracuseStep 10661345 = 7996009) B7996009
theorem B5615183 : Blo 1478559 5615183 := bstep (se 1 (by rfl) ⟨4211387, by rfl⟩ : syracuseStep 5615183 = 8422775) B8422775
theorem B3329783 : Blo 1478559 3329783 := bstep (se 1 (by rfl) ⟨2497337, by rfl⟩ : syracuseStep 3329783 = 4994675) B4994675
theorem B38940421 : Blo 1478559 38940421 := bstep (se 4 (by rfl) ⟨3650664, by rfl⟩ : syracuseStep 38940421 = 7301329) B7301329
theorem B3329801 : Blo 1478559 3329801 := bstep (se 2 (by rfl) ⟨1248675, by rfl⟩ : syracuseStep 3329801 = 2497351) B2497351
theorem B8425235 : Blo 1478559 8425235 := bstep (se 1 (by rfl) ⟨6318926, by rfl⟩ : syracuseStep 8425235 = 12637853) B12637853
theorem B3329855 : Blo 1478559 3329855 := bstep (se 1 (by rfl) ⟨2497391, by rfl⟩ : syracuseStep 3329855 = 4994783) B4994783
theorem B1478567 : Blo 1478559 1478567 := bstep (se 1 (by rfl) ⟨1108925, by rfl⟩ : syracuseStep 1478567 = 2217851) B2217851
theorem B3329963 : Blo 1478559 3329963 := bstep (se 1 (by rfl) ⟨2497472, by rfl⟩ : syracuseStep 3329963 = 4994945) B4994945
theorem B1478591 : Blo 1478559 1478591 := bstep (se 1 (by rfl) ⟨1108943, by rfl⟩ : syracuseStep 1478591 = 2217887) B2217887
theorem B1478747 : Blo 1478559 1478747 := bstep (se 1 (by rfl) ⟨1109060, by rfl⟩ : syracuseStep 1478747 = 2218121) B2218121
theorem B1478847 : Blo 1478559 1478847 := bstep (se 1 (by rfl) ⟨1109135, by rfl⟩ : syracuseStep 1478847 = 2218271) B2218271
theorem B3330323 : Blo 1478559 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B3330503 : Blo 1478559 3330503 := bstep (se 1 (by rfl) ⟨2497877, by rfl⟩ : syracuseStep 3330503 = 4995755) B4995755
theorem B1479215 : Blo 1478559 1479215 := bstep (se 1 (by rfl) ⟨1109411, by rfl⟩ : syracuseStep 1479215 = 2218823) B2218823
theorem B3330791 : Blo 1478559 3330791 := bstep (se 1 (by rfl) ⟨2498093, by rfl⟩ : syracuseStep 3330791 = 4996187) B4996187
theorem B3330863 : Blo 1478559 3330863 := bstep (se 1 (by rfl) ⟨2498147, by rfl⟩ : syracuseStep 3330863 = 4996295) B4996295
theorem B3330953 : Blo 1478559 3330953 := bstep (se 2 (by rfl) ⟨1249107, by rfl⟩ : syracuseStep 3330953 = 2498215) B2498215
theorem B15995821 : Blo 1478559 15995821 := bstep (se 3 (by rfl) ⟨2999216, by rfl⟩ : syracuseStep 15995821 = 5998433) B5998433
theorem B1479791 : Blo 1478559 1479791 := bstep (se 1 (by rfl) ⟨1109843, by rfl⟩ : syracuseStep 1479791 = 2219687) B2219687
theorem B2495657 : Blo 1478559 2495657 := bstep (se 2 (by rfl) ⟨935871, by rfl⟩ : syracuseStep 2495657 = 1871743) B1871743
theorem B1479871 : Blo 1478559 1479871 := bstep (se 1 (by rfl) ⟨1109903, by rfl⟩ : syracuseStep 1479871 = 2219807) B2219807
theorem B1480159 : Blo 1478559 1480159 := bstep (se 1 (by rfl) ⟨1110119, by rfl⟩ : syracuseStep 1480159 = 2220239) B2220239
theorem B1480191 : Blo 1478559 1480191 := bstep (se 1 (by rfl) ⟨1110143, by rfl⟩ : syracuseStep 1480191 = 2220287) B2220287
theorem B18494999 : Blo 1478559 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B9000667 : Blo 1478559 9000667 := bstep (se 1 (by rfl) ⟨6750500, by rfl⟩ : syracuseStep 9000667 = 13501001) B13501001
theorem B15611777 : Blo 1478559 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B12646327 : Blo 1478559 12646327 := bstep (se 1 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 12646327 = 18969491) B18969491
theorem B25294841 : Blo 1478559 25294841 := bstep (se 2 (by rfl) ⟨9485565, by rfl⟩ : syracuseStep 25294841 = 18971131) B18971131
theorem B2218025 : Blo 1478559 2218025 := bstep (se 2 (by rfl) ⟨831759, by rfl⟩ : syracuseStep 2218025 = 1663519) B1663519
theorem B2218055 : Blo 1478559 2218055 := bstep (se 1 (by rfl) ⟨1663541, by rfl⟩ : syracuseStep 2218055 = 3327083) B3327083
theorem B8427833 : Blo 1478559 8427833 := bstep (se 2 (by rfl) ⟨3160437, by rfl⟩ : syracuseStep 8427833 = 6320875) B6320875
theorem B12638537 : Blo 1478559 12638537 := bstep (se 2 (by rfl) ⟨4739451, by rfl⟩ : syracuseStep 12638537 = 9478903) B9478903
theorem B2218367 : Blo 1478559 2218367 := bstep (se 1 (by rfl) ⟨1663775, by rfl⟩ : syracuseStep 2218367 = 3327551) B3327551
theorem B3201479 : Blo 1478559 3201479 := bstep (se 1 (by rfl) ⟨2401109, by rfl⟩ : syracuseStep 3201479 = 4802219) B4802219
theorem B2218439 : Blo 1478559 2218439 := bstep (se 1 (by rfl) ⟨1663829, by rfl⟩ : syracuseStep 2218439 = 3327659) B3327659
theorem B5618267 : Blo 1478559 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B2497115 : Blo 1478559 2497115 := bstep (se 1 (by rfl) ⟨1872836, by rfl⟩ : syracuseStep 2497115 = 3745673) B3745673
theorem B56883869 : Blo 1478559 56883869 := bstep (se 3 (by rfl) ⟨10665725, by rfl⟩ : syracuseStep 56883869 = 21331451) B21331451
theorem B2218655 : Blo 1478559 2218655 := bstep (se 1 (by rfl) ⟨1663991, by rfl⟩ : syracuseStep 2218655 = 3327983) B3327983
theorem B4995809 : Blo 1478559 4995809 := bstep (se 2 (by rfl) ⟨1873428, by rfl⟩ : syracuseStep 4995809 = 3746857) B3746857
theorem B76897025 : Blo 1478559 76897025 := bstep (se 2 (by rfl) ⟨28836384, by rfl⟩ : syracuseStep 76897025 = 57672769) B57672769
theorem B2218799 : Blo 1478559 2218799 := bstep (se 1 (by rfl) ⟨1664099, by rfl⟩ : syracuseStep 2218799 = 3328199) B3328199
theorem B2218889 : Blo 1478559 2218889 := bstep (se 2 (by rfl) ⟨832083, by rfl⟩ : syracuseStep 2218889 = 1664167) B1664167
theorem B2218919 : Blo 1478559 2218919 := bstep (se 1 (by rfl) ⟨1664189, by rfl⟩ : syracuseStep 2218919 = 3328379) B3328379
theorem B9477161 : Blo 1478559 9477161 := bstep (se 2 (by rfl) ⟨3553935, by rfl⟩ : syracuseStep 9477161 = 7107871) B7107871
theorem B2219099 : Blo 1478559 2219099 := bstep (se 1 (by rfl) ⟨1664324, by rfl⟩ : syracuseStep 2219099 = 3328649) B3328649
theorem B5995615 : Blo 1478559 5995615 := bstep (se 1 (by rfl) ⟨4496711, by rfl⟩ : syracuseStep 5995615 = 8993423) B8993423
theorem B2809019 : Blo 1478559 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B2219291 : Blo 1478559 2219291 := bstep (se 1 (by rfl) ⟨1664468, by rfl⟩ : syracuseStep 2219291 = 3328937) B3328937
theorem B3653039 : Blo 1478559 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B8420861 : Blo 1478559 8420861 := bstep (se 3 (by rfl) ⟨1578911, by rfl⟩ : syracuseStep 8420861 = 3157823) B3157823
theorem B2219759 : Blo 1478559 2219759 := bstep (se 1 (by rfl) ⟨1664819, by rfl⟩ : syracuseStep 2219759 = 3329639) B3329639
theorem B31989491 : Blo 1478559 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B3743567 : Blo 1478559 3743567 := bstep (se 1 (by rfl) ⟨2807675, by rfl⟩ : syracuseStep 3743567 = 5615351) B5615351
theorem B2498431 : Blo 1478559 2498431 := bstep (se 1 (by rfl) ⟨1873823, by rfl⟩ : syracuseStep 2498431 = 3747647) B3747647
theorem B2219945 : Blo 1478559 2219945 := bstep (se 2 (by rfl) ⟨832479, by rfl⟩ : syracuseStep 2219945 = 1664959) B1664959
theorem B14221277 : Blo 1478559 14221277 := bstep (se 3 (by rfl) ⟨2666489, by rfl⟩ : syracuseStep 14221277 = 5332979) B5332979
theorem B37896335 : Blo 1478559 37896335 := bstep (se 1 (by rfl) ⟨28422251, by rfl⟩ : syracuseStep 37896335 = 56844503) B56844503
theorem B6316193 : Blo 1478559 6316193 := bstep (se 2 (by rfl) ⟨2368572, by rfl⟩ : syracuseStep 6316193 = 4737145) B4737145
theorem B2220215 : Blo 1478559 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B23986469 : Blo 1478559 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B2220335 : Blo 1478559 2220335 := bstep (se 1 (by rfl) ⟨1665251, by rfl⟩ : syracuseStep 2220335 = 3330503) B3330503
theorem B2220527 : Blo 1478559 2220527 := bstep (se 1 (by rfl) ⟨1665395, by rfl⟩ : syracuseStep 2220527 = 3330791) B3330791
theorem B2220575 : Blo 1478559 2220575 := bstep (se 1 (by rfl) ⟨1665431, by rfl⟩ : syracuseStep 2220575 = 3330863) B3330863
theorem B2220635 : Blo 1478559 2220635 := bstep (se 1 (by rfl) ⟨1665476, by rfl⟩ : syracuseStep 2220635 = 3330953) B3330953
theorem B1663771 : Blo 1478559 1663771 := bstep (se 1 (by rfl) ⟨1247828, by rfl⟩ : syracuseStep 1663771 = 2495657) B2495657
theorem B12329999 : Blo 1478559 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B5694569 : Blo 1478559 5694569 := bstep (se 2 (by rfl) ⟨2135463, by rfl⟩ : syracuseStep 5694569 = 4270927) B4270927
theorem B3745511 : Blo 1478559 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B1664743 : Blo 1478559 1664743 := bstep (se 1 (by rfl) ⟨1248557, by rfl⟩ : syracuseStep 1664743 = 2497115) B2497115
theorem B37922579 : Blo 1478559 37922579 := bstep (se 1 (by rfl) ⟨28441934, by rfl⟩ : syracuseStep 37922579 = 56883869) B56883869
theorem B3245915 : Blo 1478559 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B15992801 : Blo 1478559 15992801 := bstep (se 2 (by rfl) ⟨5997300, by rfl⟩ : syracuseStep 15992801 = 11994601) B11994601
theorem B6318107 : Blo 1478559 6318107 := bstep (se 1 (by rfl) ⟨4738580, by rfl⟩ : syracuseStep 6318107 = 9477161) B9477161
theorem B2435359 : Blo 1478559 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B5613907 : Blo 1478559 5613907 := bstep (se 1 (by rfl) ⟨4210430, by rfl⟩ : syracuseStep 5613907 = 8420861) B8420861
theorem B21326327 : Blo 1478559 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B16861769 : Blo 1478559 16861769 := bstep (se 2 (by rfl) ⟨6323163, by rfl⟩ : syracuseStep 16861769 = 12646327) B12646327
theorem B9480851 : Blo 1478559 9480851 := bstep (se 1 (by rfl) ⟨7110638, by rfl⟩ : syracuseStep 9480851 = 14221277) B14221277
theorem B18009125 : Blo 1478559 18009125 := bstep (se 4 (by rfl) ⟨1688355, by rfl⟩ : syracuseStep 18009125 = 3376711) B3376711
theorem B7490717 : Blo 1478559 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B9481465 : Blo 1478559 9481465 := bstep (se 2 (by rfl) ⟨3555549, by rfl⟩ : syracuseStep 9481465 = 7111099) B7111099
theorem B4992623 : Blo 1478559 4992623 := bstep (se 1 (by rfl) ⟨3744467, by rfl⟩ : syracuseStep 4992623 = 7488935) B7488935
theorem B21327761 : Blo 1478559 21327761 := bstep (se 2 (by rfl) ⟨7997910, by rfl⟩ : syracuseStep 21327761 = 15995821) B15995821
theorem B10407851 : Blo 1478559 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B16863227 : Blo 1478559 16863227 := bstep (se 1 (by rfl) ⟨12647420, by rfl⟩ : syracuseStep 16863227 = 25294841) B25294841
theorem B1478683 : Blo 1478559 1478683 := bstep (se 1 (by rfl) ⟨1109012, by rfl⟩ : syracuseStep 1478683 = 2218025) B2218025
theorem B1478703 : Blo 1478559 1478703 := bstep (se 1 (by rfl) ⟨1109027, by rfl⟩ : syracuseStep 1478703 = 2218055) B2218055
theorem B8425691 : Blo 1478559 8425691 := bstep (se 1 (by rfl) ⟨6319268, by rfl⟩ : syracuseStep 8425691 = 12638537) B12638537
theorem B1478911 : Blo 1478559 1478911 := bstep (se 1 (by rfl) ⟨1109183, by rfl⟩ : syracuseStep 1478911 = 2218367) B2218367
theorem B1478959 : Blo 1478559 1478959 := bstep (se 1 (by rfl) ⟨1109219, by rfl⟩ : syracuseStep 1478959 = 2218439) B2218439
theorem B12644687 : Blo 1478559 12644687 := bstep (se 1 (by rfl) ⟨9483515, by rfl⟩ : syracuseStep 12644687 = 18967031) B18967031
theorem B1479103 : Blo 1478559 1479103 := bstep (se 1 (by rfl) ⟨1109327, by rfl⟩ : syracuseStep 1479103 = 2218655) B2218655
theorem B4993487 : Blo 1478559 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B3158507 : Blo 1478559 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B3330539 : Blo 1478559 3330539 := bstep (se 1 (by rfl) ⟨2497904, by rfl⟩ : syracuseStep 3330539 = 4995809) B4995809
theorem B1479199 : Blo 1478559 1479199 := bstep (se 1 (by rfl) ⟨1109399, by rfl⟩ : syracuseStep 1479199 = 2218799) B2218799
theorem B1479259 : Blo 1478559 1479259 := bstep (se 1 (by rfl) ⟨1109444, by rfl⟩ : syracuseStep 1479259 = 2218889) B2218889
theorem B1479279 : Blo 1478559 1479279 := bstep (se 1 (by rfl) ⟨1109459, by rfl⟩ : syracuseStep 1479279 = 2218919) B2218919
theorem B14217893 : Blo 1478559 14217893 := bstep (se 4 (by rfl) ⟨1332927, by rfl⟩ : syracuseStep 14217893 = 2665855) B2665855
theorem B1479399 : Blo 1478559 1479399 := bstep (se 1 (by rfl) ⟨1109549, by rfl⟩ : syracuseStep 1479399 = 2219099) B2219099
theorem B34149109 : Blo 1478559 34149109 := bstep (se 5 (by rfl) ⟨1600739, by rfl⟩ : syracuseStep 34149109 = 3201479) B3201479
theorem B1479527 : Blo 1478559 1479527 := bstep (se 1 (by rfl) ⟨1109645, by rfl⟩ : syracuseStep 1479527 = 2219291) B2219291
theorem B7107563 : Blo 1478559 7107563 := bstep (se 1 (by rfl) ⟨5330672, by rfl⟩ : syracuseStep 7107563 = 10661345) B10661345
theorem B1479839 : Blo 1478559 1479839 := bstep (se 1 (by rfl) ⟨1109879, by rfl⟩ : syracuseStep 1479839 = 2219759) B2219759
theorem B3331241 : Blo 1478559 3331241 := bstep (se 2 (by rfl) ⟨1249215, by rfl⟩ : syracuseStep 3331241 = 2498431) B2498431
theorem B5616823 : Blo 1478559 5616823 := bstep (se 1 (by rfl) ⟨4212617, by rfl⟩ : syracuseStep 5616823 = 8425235) B8425235
theorem B2495711 : Blo 1478559 2495711 := bstep (se 1 (by rfl) ⟨1871783, by rfl⟩ : syracuseStep 2495711 = 3743567) B3743567
theorem B1479963 : Blo 1478559 1479963 := bstep (se 1 (by rfl) ⟨1109972, by rfl⟩ : syracuseStep 1479963 = 2219945) B2219945
theorem B1480063 : Blo 1478559 1480063 := bstep (se 1 (by rfl) ⟨1110047, by rfl⟩ : syracuseStep 1480063 = 2220095) B2220095
theorem B1480219 : Blo 1478559 1480219 := bstep (se 1 (by rfl) ⟨1110164, by rfl⟩ : syracuseStep 1480219 = 2220329) B2220329
theorem B2496143 : Blo 1478559 2496143 := bstep (se 1 (by rfl) ⟨1872107, by rfl⟩ : syracuseStep 2496143 = 3744215) B3744215
theorem B5060249 : Blo 1478559 5060249 := bstep (se 2 (by rfl) ⟨1897593, by rfl⟩ : syracuseStep 5060249 = 3795187) B3795187
theorem B1480399 : Blo 1478559 1480399 := bstep (se 1 (by rfl) ⟨1110299, by rfl⟩ : syracuseStep 1480399 = 2220599) B2220599
theorem B11392825 : Blo 1478559 11392825 := bstep (se 2 (by rfl) ⟨4272309, by rfl⟩ : syracuseStep 11392825 = 8544619) B8544619
theorem B2496575 : Blo 1478559 2496575 := bstep (se 1 (by rfl) ⟨1872431, by rfl⟩ : syracuseStep 2496575 = 3744863) B3744863
theorem B2218223 : Blo 1478559 2218223 := bstep (se 1 (by rfl) ⟨1663667, by rfl⟩ : syracuseStep 2218223 = 3327335) B3327335
theorem B2218295 : Blo 1478559 2218295 := bstep (se 1 (by rfl) ⟨1663721, by rfl⟩ : syracuseStep 2218295 = 3327443) B3327443
theorem B2218475 : Blo 1478559 2218475 := bstep (se 1 (by rfl) ⟨1663856, by rfl⟩ : syracuseStep 2218475 = 3327713) B3327713
theorem B7994153 : Blo 1478559 7994153 := bstep (se 2 (by rfl) ⟨2997807, by rfl⟩ : syracuseStep 7994153 = 5995615) B5995615
theorem B5618555 : Blo 1478559 5618555 := bstep (se 1 (by rfl) ⟨4213916, by rfl⟩ : syracuseStep 5618555 = 8427833) B8427833
theorem B2219003 : Blo 1478559 2219003 := bstep (se 1 (by rfl) ⟨1664252, by rfl⟩ : syracuseStep 2219003 = 3328505) B3328505
theorem B2497567 : Blo 1478559 2497567 := bstep (se 1 (by rfl) ⟨1873175, by rfl⟩ : syracuseStep 2497567 = 3746351) B3746351
theorem B2219063 : Blo 1478559 2219063 := bstep (se 1 (by rfl) ⟨1664297, by rfl⟩ : syracuseStep 2219063 = 3328595) B3328595
theorem B51264683 : Blo 1478559 51264683 := bstep (se 1 (by rfl) ⟨38448512, by rfl⟩ : syracuseStep 51264683 = 76897025) B76897025
theorem B2219183 : Blo 1478559 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B2219243 : Blo 1478559 2219243 := bstep (se 1 (by rfl) ⟨1664432, by rfl⟩ : syracuseStep 2219243 = 3328865) B3328865
theorem B2497999 : Blo 1478559 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B12000889 : Blo 1478559 12000889 := bstep (se 2 (by rfl) ⟨4500333, by rfl⟩ : syracuseStep 12000889 = 9000667) B9000667
theorem B51920561 : Blo 1478559 51920561 := bstep (se 2 (by rfl) ⟨19470210, by rfl⟩ : syracuseStep 51920561 = 38940421) B38940421
theorem B3743455 : Blo 1478559 3743455 := bstep (se 1 (by rfl) ⟨2807591, by rfl⟩ : syracuseStep 3743455 = 5615183) B5615183
theorem B2219855 : Blo 1478559 2219855 := bstep (se 1 (by rfl) ⟨1664891, by rfl⟩ : syracuseStep 2219855 = 3329783) B3329783
theorem B2219867 : Blo 1478559 2219867 := bstep (se 1 (by rfl) ⟨1664900, by rfl⟩ : syracuseStep 2219867 = 3329801) B3329801
theorem B2219903 : Blo 1478559 2219903 := bstep (se 1 (by rfl) ⟨1664927, by rfl⟩ : syracuseStep 2219903 = 3329855) B3329855
theorem B2219975 : Blo 1478559 2219975 := bstep (se 1 (by rfl) ⟨1664981, by rfl⟩ : syracuseStep 2219975 = 3329963) B3329963
theorem B25264223 : Blo 1478559 25264223 := bstep (se 1 (by rfl) ⟨18948167, by rfl⟩ : syracuseStep 25264223 = 37896335) B37896335
theorem B4210795 : Blo 1478559 4210795 := bstep (se 1 (by rfl) ⟨3158096, by rfl⟩ : syracuseStep 4210795 = 6316193) B6316193
theorem B15990979 : Blo 1478559 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B8429791 : Blo 1478559 8429791 := bstep (se 1 (by rfl) ⟨6322343, by rfl⟩ : syracuseStep 8429791 = 12644687) B12644687
theorem B2105671 : Blo 1478559 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B2220359 : Blo 1478559 2220359 := bstep (se 1 (by rfl) ⟨1665269, by rfl⟩ : syracuseStep 2220359 = 3330539) B3330539
theorem B9478595 : Blo 1478559 9478595 := bstep (se 1 (by rfl) ⟨7108946, by rfl⟩ : syracuseStep 9478595 = 14217893) B14217893
theorem B64004741 : Blo 1478559 64004741 := bstep (se 4 (by rfl) ⟨6000444, by rfl⟩ : syracuseStep 64004741 = 12000889) B12000889
theorem B2220827 : Blo 1478559 2220827 := bstep (se 1 (by rfl) ⟨1665620, by rfl⟩ : syracuseStep 2220827 = 3331241) B3331241
theorem B1663807 : Blo 1478559 1663807 := bstep (se 1 (by rfl) ⟨1247855, by rfl⟩ : syracuseStep 1663807 = 2495711) B2495711
theorem B45532145 : Blo 1478559 45532145 := bstep (se 2 (by rfl) ⟨17074554, by rfl⟩ : syracuseStep 45532145 = 34149109) B34149109
theorem B1664095 : Blo 1478559 1664095 := bstep (se 1 (by rfl) ⟨1248071, by rfl⟩ : syracuseStep 1664095 = 2496143) B2496143
theorem B25281719 : Blo 1478559 25281719 := bstep (se 1 (by rfl) ⟨18961289, by rfl⟩ : syracuseStep 25281719 = 37922579) B37922579
theorem B2163943 : Blo 1478559 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B4212071 : Blo 1478559 4212071 := bstep (se 1 (by rfl) ⟨3159053, by rfl⟩ : syracuseStep 4212071 = 6318107) B6318107
theorem B1664383 : Blo 1478559 1664383 := bstep (se 1 (by rfl) ⟨1248287, by rfl⟩ : syracuseStep 1664383 = 2496575) B2496575
theorem B7489097 : Blo 1478559 7489097 := bstep (se 2 (by rfl) ⟨2808411, by rfl⟩ : syracuseStep 7489097 = 5616823) B5616823
theorem B12641953 : Blo 1478559 12641953 := bstep (se 2 (by rfl) ⟨4740732, by rfl⟩ : syracuseStep 12641953 = 9481465) B9481465
theorem B11241179 : Blo 1478559 11241179 := bstep (se 1 (by rfl) ⟨8430884, by rfl⟩ : syracuseStep 11241179 = 16861769) B16861769
theorem B138454829 : Blo 1478559 138454829 := bstep (se 3 (by rfl) ⟨25960280, by rfl⟩ : syracuseStep 138454829 = 51920561) B51920561
theorem B3745703 : Blo 1478559 3745703 := bstep (se 1 (by rfl) ⟨2809277, by rfl⟩ : syracuseStep 3745703 = 5618555) B5618555
theorem B4991273 : Blo 1478559 4991273 := bstep (se 2 (by rfl) ⟨1871727, by rfl⟩ : syracuseStep 4991273 = 3743455) B3743455
theorem B3328415 : Blo 1478559 3328415 := bstep (se 1 (by rfl) ⟨2496311, by rfl⟩ : syracuseStep 3328415 = 4992623) B4992623
theorem B15190433 : Blo 1478559 15190433 := bstep (se 2 (by rfl) ⟨5696412, by rfl⟩ : syracuseStep 15190433 = 11392825) B11392825
theorem B11242151 : Blo 1478559 11242151 := bstep (se 1 (by rfl) ⟨8431613, by rfl⟩ : syracuseStep 11242151 = 16863227) B16863227
theorem B3328991 : Blo 1478559 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B3247145 : Blo 1478559 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B4738375 : Blo 1478559 4738375 := bstep (se 1 (by rfl) ⟨3553781, by rfl⟩ : syracuseStep 4738375 = 7107563) B7107563
theorem B8219999 : Blo 1478559 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B3796379 : Blo 1478559 3796379 := bstep (se 1 (by rfl) ⟨2847284, by rfl⟩ : syracuseStep 3796379 = 5694569) B5694569
theorem B10661867 : Blo 1478559 10661867 := bstep (se 1 (by rfl) ⟨7996400, by rfl⟩ : syracuseStep 10661867 = 15992801) B15992801
theorem B3330089 : Blo 1478559 3330089 := bstep (se 2 (by rfl) ⟨1248783, by rfl⟩ : syracuseStep 3330089 = 2497567) B2497567
theorem B1478815 : Blo 1478559 1478815 := bstep (se 1 (by rfl) ⟨1109111, by rfl⟩ : syracuseStep 1478815 = 2218223) B2218223
theorem B1478863 : Blo 1478559 1478863 := bstep (se 1 (by rfl) ⟨1109147, by rfl⟩ : syracuseStep 1478863 = 2218295) B2218295
theorem B1478983 : Blo 1478559 1478983 := bstep (se 1 (by rfl) ⟨1109237, by rfl⟩ : syracuseStep 1478983 = 2218475) B2218475
theorem B14217551 : Blo 1478559 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B6320567 : Blo 1478559 6320567 := bstep (se 1 (by rfl) ⟨4740425, by rfl⟩ : syracuseStep 6320567 = 9480851) B9480851
theorem B5329435 : Blo 1478559 5329435 := bstep (se 1 (by rfl) ⟨3997076, by rfl⟩ : syracuseStep 5329435 = 7994153) B7994153
theorem B3330665 : Blo 1478559 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B1479335 : Blo 1478559 1479335 := bstep (se 1 (by rfl) ⟨1109501, by rfl⟩ : syracuseStep 1479335 = 2219003) B2219003
theorem B12006083 : Blo 1478559 12006083 := bstep (se 1 (by rfl) ⟨9004562, by rfl⟩ : syracuseStep 12006083 = 18009125) B18009125
theorem B1479375 : Blo 1478559 1479375 := bstep (se 1 (by rfl) ⟨1109531, by rfl⟩ : syracuseStep 1479375 = 2219063) B2219063
theorem B4993811 : Blo 1478559 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B1479455 : Blo 1478559 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1479495 : Blo 1478559 1479495 := bstep (se 1 (by rfl) ⟨1109621, by rfl⟩ : syracuseStep 1479495 = 2219243) B2219243
theorem B1479903 : Blo 1478559 1479903 := bstep (se 1 (by rfl) ⟨1109927, by rfl⟩ : syracuseStep 1479903 = 2219855) B2219855
theorem B1479911 : Blo 1478559 1479911 := bstep (se 1 (by rfl) ⟨1109933, by rfl⟩ : syracuseStep 1479911 = 2219867) B2219867
theorem B1479935 : Blo 1478559 1479935 := bstep (se 1 (by rfl) ⟨1109951, by rfl⟩ : syracuseStep 1479935 = 2219903) B2219903
theorem B14218507 : Blo 1478559 14218507 := bstep (se 1 (by rfl) ⟨10663880, by rfl⟩ : syracuseStep 14218507 = 21327761) B21327761
theorem B1479983 : Blo 1478559 1479983 := bstep (se 1 (by rfl) ⟨1109987, by rfl⟩ : syracuseStep 1479983 = 2219975) B2219975
theorem B1480143 : Blo 1478559 1480143 := bstep (se 1 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 1480143 = 2220215) B2220215
theorem B5617127 : Blo 1478559 5617127 := bstep (se 1 (by rfl) ⟨4212845, by rfl⟩ : syracuseStep 5617127 = 8425691) B8425691
theorem B1480223 : Blo 1478559 1480223 := bstep (se 1 (by rfl) ⟨1110167, by rfl⟩ : syracuseStep 1480223 = 2220335) B2220335
theorem B1480351 : Blo 1478559 1480351 := bstep (se 1 (by rfl) ⟨1110263, by rfl⟩ : syracuseStep 1480351 = 2220527) B2220527
theorem B1480383 : Blo 1478559 1480383 := bstep (se 1 (by rfl) ⟨1110287, by rfl⟩ : syracuseStep 1480383 = 2220575) B2220575
theorem B1480423 : Blo 1478559 1480423 := bstep (se 1 (by rfl) ⟨1110317, by rfl⟩ : syracuseStep 1480423 = 2220635) B2220635
theorem B7485209 : Blo 1478559 7485209 := bstep (se 2 (by rfl) ⟨2806953, by rfl⟩ : syracuseStep 7485209 = 5613907) B5613907
theorem B2218361 : Blo 1478559 2218361 := bstep (se 2 (by rfl) ⟨831885, by rfl⟩ : syracuseStep 2218361 = 1663771) B1663771
theorem B3373499 : Blo 1478559 3373499 := bstep (se 1 (by rfl) ⟨2530124, by rfl⟩ : syracuseStep 3373499 = 5060249) B5060249
theorem B2497007 : Blo 1478559 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B34176455 : Blo 1478559 34176455 := bstep (se 1 (by rfl) ⟨25632341, by rfl⟩ : syracuseStep 34176455 = 51264683) B51264683
theorem B2219657 : Blo 1478559 2219657 := bstep (se 2 (by rfl) ⟨832371, by rfl⟩ : syracuseStep 2219657 = 1664743) B1664743
theorem B6938567 : Blo 1478559 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B2220059 : Blo 1478559 2220059 := bstep (se 1 (by rfl) ⟨1665044, by rfl⟩ : syracuseStep 2220059 = 3330089) B3330089
theorem B16842815 : Blo 1478559 16842815 := bstep (se 1 (by rfl) ⟨12632111, by rfl⟩ : syracuseStep 16842815 = 25264223) B25264223
theorem B9478367 : Blo 1478559 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B11239721 : Blo 1478559 11239721 := bstep (se 2 (by rfl) ⟨4214895, by rfl⟩ : syracuseStep 11239721 = 8429791) B8429791
theorem B2220443 : Blo 1478559 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B8004055 : Blo 1478559 8004055 := bstep (se 1 (by rfl) ⟨6003041, by rfl⟩ : syracuseStep 8004055 = 12006083) B12006083
theorem B3744751 : Blo 1478559 3744751 := bstep (se 1 (by rfl) ⟨2808563, by rfl⟩ : syracuseStep 3744751 = 5617127) B5617127
theorem B8995997 : Blo 1478559 8995997 := bstep (se 3 (by rfl) ⟨1686749, by rfl⟩ : syracuseStep 8995997 = 3373499) B3373499
theorem B4990139 : Blo 1478559 4990139 := bstep (se 1 (by rfl) ⟨3742604, by rfl⟩ : syracuseStep 4990139 = 7485209) B7485209
theorem B3327515 : Blo 1478559 3327515 := bstep (se 1 (by rfl) ⟨2495636, by rfl⟩ : syracuseStep 3327515 = 4991273) B4991273
theorem B10126955 : Blo 1478559 10126955 := bstep (se 1 (by rfl) ⟨7595216, by rfl⟩ : syracuseStep 10126955 = 15190433) B15190433
theorem B2885257 : Blo 1478559 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B1664671 : Blo 1478559 1664671 := bstep (se 1 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 1664671 = 2497007) B2497007
theorem B18958009 : Blo 1478559 18958009 := bstep (se 2 (by rfl) ⟨7109253, by rfl⟩ : syracuseStep 18958009 = 14218507) B14218507
theorem B6317833 : Blo 1478559 6317833 := bstep (se 2 (by rfl) ⟨2369187, by rfl⟩ : syracuseStep 6317833 = 4738375) B4738375
theorem B2164763 : Blo 1478559 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B22784303 : Blo 1478559 22784303 := bstep (se 1 (by rfl) ⟨17088227, by rfl⟩ : syracuseStep 22784303 = 34176455) B34176455
theorem B5614393 : Blo 1478559 5614393 := bstep (se 2 (by rfl) ⟨2105397, by rfl⟩ : syracuseStep 5614393 = 4210795) B4210795
theorem B4213711 : Blo 1478559 4213711 := bstep (se 1 (by rfl) ⟨3160283, by rfl⟩ : syracuseStep 4213711 = 6320567) B6320567
theorem B6319063 : Blo 1478559 6319063 := bstep (se 1 (by rfl) ⟨4739297, by rfl⟩ : syracuseStep 6319063 = 9478595) B9478595
theorem B3329207 : Blo 1478559 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B30354763 : Blo 1478559 30354763 := bstep (se 1 (by rfl) ⟨22766072, by rfl⟩ : syracuseStep 30354763 = 45532145) B45532145
theorem B7105913 : Blo 1478559 7105913 := bstep (se 2 (by rfl) ⟨2664717, by rfl⟩ : syracuseStep 7105913 = 5329435) B5329435
theorem B16854479 : Blo 1478559 16854479 := bstep (se 1 (by rfl) ⟨12640859, by rfl⟩ : syracuseStep 16854479 = 25281719) B25281719
theorem B4992731 : Blo 1478559 4992731 := bstep (se 1 (by rfl) ⟨3744548, by rfl⟩ : syracuseStep 4992731 = 7489097) B7489097
theorem B92303219 : Blo 1478559 92303219 := bstep (se 1 (by rfl) ⟨69227414, by rfl⟩ : syracuseStep 92303219 = 138454829) B138454829
theorem B1478907 : Blo 1478559 1478907 := bstep (se 1 (by rfl) ⟨1109180, by rfl⟩ : syracuseStep 1478907 = 2218361) B2218361
theorem B16855937 : Blo 1478559 16855937 := bstep (se 2 (by rfl) ⟨6320976, by rfl⟩ : syracuseStep 16855937 = 12641953) B12641953
theorem B1479771 : Blo 1478559 1479771 := bstep (se 1 (by rfl) ⟨1109828, by rfl⟩ : syracuseStep 1479771 = 2219657) B2219657
theorem B4625711 : Blo 1478559 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B7107911 : Blo 1478559 7107911 := bstep (se 1 (by rfl) ⟨5330933, by rfl⟩ : syracuseStep 7107911 = 10661867) B10661867
theorem B1480239 : Blo 1478559 1480239 := bstep (se 1 (by rfl) ⟨1110179, by rfl⟩ : syracuseStep 1480239 = 2220359) B2220359
theorem B21321305 : Blo 1478559 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B42669827 : Blo 1478559 42669827 := bstep (se 1 (by rfl) ⟨32002370, by rfl⟩ : syracuseStep 42669827 = 64004741) B64004741
theorem B2807561 : Blo 1478559 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B1480551 : Blo 1478559 1480551 := bstep (se 1 (by rfl) ⟨1110413, by rfl⟩ : syracuseStep 1480551 = 2220827) B2220827
theorem B2808047 : Blo 1478559 2808047 := bstep (se 1 (by rfl) ⟨2106035, by rfl⟩ : syracuseStep 2808047 = 4212071) B4212071
theorem B21919997 : Blo 1478559 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B2218409 : Blo 1478559 2218409 := bstep (se 2 (by rfl) ⟨831903, by rfl⟩ : syracuseStep 2218409 = 1663807) B1663807
theorem B7494119 : Blo 1478559 7494119 := bstep (se 1 (by rfl) ⟨5620589, by rfl⟩ : syracuseStep 7494119 = 11241179) B11241179
theorem B2497135 : Blo 1478559 2497135 := bstep (se 1 (by rfl) ⟨1872851, by rfl⟩ : syracuseStep 2497135 = 3745703) B3745703
theorem B2218793 : Blo 1478559 2218793 := bstep (se 2 (by rfl) ⟨832047, by rfl⟩ : syracuseStep 2218793 = 1664095) B1664095
theorem B2218943 : Blo 1478559 2218943 := bstep (se 1 (by rfl) ⟨1664207, by rfl⟩ : syracuseStep 2218943 = 3328415) B3328415
theorem B7494767 : Blo 1478559 7494767 := bstep (se 1 (by rfl) ⟨5621075, by rfl⟩ : syracuseStep 7494767 = 11242151) B11242151
theorem B2219177 : Blo 1478559 2219177 := bstep (se 2 (by rfl) ⟨832191, by rfl⟩ : syracuseStep 2219177 = 1664383) B1664383
theorem B2219327 : Blo 1478559 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B2530919 : Blo 1478559 2530919 := bstep (se 1 (by rfl) ⟨1898189, by rfl⟩ : syracuseStep 2530919 = 3796379) B3796379
theorem B7488125 : Blo 1478559 7488125 := bstep (se 3 (by rfl) ⟨1404023, by rfl⟩ : syracuseStep 7488125 = 2808047) B2808047
theorem B5997331 : Blo 1478559 5997331 := bstep (se 1 (by rfl) ⟨4497998, by rfl⟩ : syracuseStep 5997331 = 8995997) B8995997
theorem B3326759 : Blo 1478559 3326759 := bstep (se 1 (by rfl) ⟨2495069, by rfl⟩ : syracuseStep 3326759 = 4990139) B4990139
theorem B14214203 : Blo 1478559 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B15189535 : Blo 1478559 15189535 := bstep (se 1 (by rfl) ⟨11392151, by rfl⟩ : syracuseStep 15189535 = 22784303) B22784303
theorem B4737275 : Blo 1478559 4737275 := bstep (se 1 (by rfl) ⟨3552956, by rfl⟩ : syracuseStep 4737275 = 7105913) B7105913
theorem B8423777 : Blo 1478559 8423777 := bstep (se 2 (by rfl) ⟨3158916, by rfl⟩ : syracuseStep 8423777 = 6317833) B6317833
theorem B3328487 : Blo 1478559 3328487 := bstep (se 1 (by rfl) ⟨2496365, by rfl⟩ : syracuseStep 3328487 = 4992731) B4992731
theorem B6318911 : Blo 1478559 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B58453325 : Blo 1478559 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B3329513 : Blo 1478559 3329513 := bstep (se 2 (by rfl) ⟨1248567, by rfl⟩ : syracuseStep 3329513 = 2497135) B2497135
theorem B3083807 : Blo 1478559 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B4738607 : Blo 1478559 4738607 := bstep (se 1 (by rfl) ⟨3553955, by rfl⟩ : syracuseStep 4738607 = 7107911) B7107911
theorem B28446551 : Blo 1478559 28446551 := bstep (se 1 (by rfl) ⟨21334913, by rfl⟩ : syracuseStep 28446551 = 42669827) B42669827
theorem B8425417 : Blo 1478559 8425417 := bstep (se 2 (by rfl) ⟨3159531, by rfl⟩ : syracuseStep 8425417 = 6319063) B6319063
theorem B4993001 : Blo 1478559 4993001 := bstep (se 2 (by rfl) ⟨1872375, by rfl⟩ : syracuseStep 4993001 = 3744751) B3744751
theorem B1478939 : Blo 1478559 1478939 := bstep (se 1 (by rfl) ⟨1109204, by rfl⟩ : syracuseStep 1478939 = 2218409) B2218409
theorem B27005213 : Blo 1478559 27005213 := bstep (se 3 (by rfl) ⟨5063477, by rfl⟩ : syracuseStep 27005213 = 10126955) B10126955
theorem B40473017 : Blo 1478559 40473017 := bstep (se 2 (by rfl) ⟨15177381, by rfl⟩ : syracuseStep 40473017 = 30354763) B30354763
theorem B1479195 : Blo 1478559 1479195 := bstep (se 1 (by rfl) ⟨1109396, by rfl⟩ : syracuseStep 1479195 = 2218793) B2218793
theorem B1479295 : Blo 1478559 1479295 := bstep (se 1 (by rfl) ⟨1109471, by rfl⟩ : syracuseStep 1479295 = 2218943) B2218943
theorem B1479451 : Blo 1478559 1479451 := bstep (se 1 (by rfl) ⟨1109588, by rfl⟩ : syracuseStep 1479451 = 2219177) B2219177
theorem B3847009 : Blo 1478559 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B1479551 : Blo 1478559 1479551 := bstep (se 1 (by rfl) ⟨1109663, by rfl⟩ : syracuseStep 1479551 = 2219327) B2219327
theorem B25277345 : Blo 1478559 25277345 := bstep (se 2 (by rfl) ⟨9479004, by rfl⟩ : syracuseStep 25277345 = 18958009) B18958009
theorem B11236319 : Blo 1478559 11236319 := bstep (se 1 (by rfl) ⟨8427239, by rfl⟩ : syracuseStep 11236319 = 16854479) B16854479
theorem B61535479 : Blo 1478559 61535479 := bstep (se 1 (by rfl) ⟨46151609, by rfl⟩ : syracuseStep 61535479 = 92303219) B92303219
theorem B1480039 : Blo 1478559 1480039 := bstep (se 1 (by rfl) ⟨1110029, by rfl⟩ : syracuseStep 1480039 = 2220059) B2220059
theorem B11228543 : Blo 1478559 11228543 := bstep (se 1 (by rfl) ⟨8421407, by rfl⟩ : syracuseStep 11228543 = 16842815) B16842815
theorem B5772701 : Blo 1478559 5772701 := bstep (se 3 (by rfl) ⟨1082381, by rfl⟩ : syracuseStep 5772701 = 2164763) B2164763
theorem B7493147 : Blo 1478559 7493147 := bstep (se 1 (by rfl) ⟨5619860, by rfl⟩ : syracuseStep 7493147 = 11239721) B11239721
theorem B1480295 : Blo 1478559 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B11237291 : Blo 1478559 11237291 := bstep (se 1 (by rfl) ⟨8427968, by rfl⟩ : syracuseStep 11237291 = 16855937) B16855937
theorem B10672073 : Blo 1478559 10672073 := bstep (se 2 (by rfl) ⟨4002027, by rfl⟩ : syracuseStep 10672073 = 8004055) B8004055
theorem B2218343 : Blo 1478559 2218343 := bstep (se 1 (by rfl) ⟨1663757, by rfl⟩ : syracuseStep 2218343 = 3327515) B3327515
theorem B7485857 : Blo 1478559 7485857 := bstep (se 2 (by rfl) ⟨2807196, by rfl⟩ : syracuseStep 7485857 = 5614393) B5614393
theorem B5618281 : Blo 1478559 5618281 := bstep (se 2 (by rfl) ⟨2106855, by rfl⟩ : syracuseStep 5618281 = 4213711) B4213711
theorem B4996079 : Blo 1478559 4996079 := bstep (se 1 (by rfl) ⟨3747059, by rfl⟩ : syracuseStep 4996079 = 7494119) B7494119
theorem B7486829 : Blo 1478559 7486829 := bstep (se 3 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 7486829 = 2807561) B2807561
theorem B4996511 : Blo 1478559 4996511 := bstep (se 1 (by rfl) ⟨3747383, by rfl⟩ : syracuseStep 4996511 = 7494767) B7494767
theorem B2219471 : Blo 1478559 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B2219561 : Blo 1478559 2219561 := bstep (se 2 (by rfl) ⟨832335, by rfl⟩ : syracuseStep 2219561 = 1664671) B1664671
theorem B1687279 : Blo 1478559 1687279 := bstep (se 1 (by rfl) ⟨1265459, by rfl⟩ : syracuseStep 1687279 = 2530919) B2530919
theorem B81010853 : Blo 1478559 81010853 := bstep (se 4 (by rfl) ⟨7594767, by rfl⟩ : syracuseStep 81010853 = 15189535) B15189535
theorem B16851563 : Blo 1478559 16851563 := bstep (se 1 (by rfl) ⟨12638672, by rfl⟩ : syracuseStep 16851563 = 25277345) B25277345
theorem B5129345 : Blo 1478559 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B4990571 : Blo 1478559 4990571 := bstep (se 1 (by rfl) ⟨3742928, by rfl⟩ : syracuseStep 4990571 = 7485857) B7485857
theorem B4212607 : Blo 1478559 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B4991219 : Blo 1478559 4991219 := bstep (se 1 (by rfl) ⟨3743414, by rfl⟩ : syracuseStep 4991219 = 7486829) B7486829
theorem B11233889 : Blo 1478559 11233889 := bstep (se 2 (by rfl) ⟨4212708, by rfl⟩ : syracuseStep 11233889 = 8425417) B8425417
theorem B3328667 : Blo 1478559 3328667 := bstep (se 1 (by rfl) ⟨2496500, by rfl⟩ : syracuseStep 3328667 = 4993001) B4993001
theorem B4992083 : Blo 1478559 4992083 := bstep (se 1 (by rfl) ⟨3744062, by rfl⟩ : syracuseStep 4992083 = 7488125) B7488125
theorem B7490879 : Blo 1478559 7490879 := bstep (se 1 (by rfl) ⟨5618159, by rfl⟩ : syracuseStep 7490879 = 11236319) B11236319
theorem B7491041 : Blo 1478559 7491041 := bstep (se 2 (by rfl) ⟨2809140, by rfl⟩ : syracuseStep 7491041 = 5618281) B5618281
theorem B7491527 : Blo 1478559 7491527 := bstep (se 1 (by rfl) ⟨5618645, by rfl⟩ : syracuseStep 7491527 = 11237291) B11237291
theorem B7114715 : Blo 1478559 7114715 := bstep (se 1 (by rfl) ⟨5336036, by rfl⟩ : syracuseStep 7114715 = 10672073) B10672073
theorem B31985765 : Blo 1478559 31985765 := bstep (se 4 (by rfl) ⟨2998665, by rfl⟩ : syracuseStep 31985765 = 5997331) B5997331
theorem B3158183 : Blo 1478559 3158183 := bstep (se 1 (by rfl) ⟨2368637, by rfl⟩ : syracuseStep 3158183 = 4737275) B4737275
theorem B5615851 : Blo 1478559 5615851 := bstep (se 1 (by rfl) ⟨4211888, by rfl⟩ : syracuseStep 5615851 = 8423777) B8423777
theorem B1478895 : Blo 1478559 1478895 := bstep (se 1 (by rfl) ⟨1109171, by rfl⟩ : syracuseStep 1478895 = 2218343) B2218343
theorem B82047305 : Blo 1478559 82047305 := bstep (se 2 (by rfl) ⟨30767739, by rfl⟩ : syracuseStep 82047305 = 61535479) B61535479
theorem B3330719 : Blo 1478559 3330719 := bstep (se 1 (by rfl) ⟨2498039, by rfl⟩ : syracuseStep 3330719 = 4996079) B4996079
theorem B3331007 : Blo 1478559 3331007 := bstep (se 1 (by rfl) ⟨2498255, by rfl⟩ : syracuseStep 3331007 = 4996511) B4996511
theorem B1479647 : Blo 1478559 1479647 := bstep (se 1 (by rfl) ⟨1109735, by rfl⟩ : syracuseStep 1479647 = 2219471) B2219471
theorem B2249705 : Blo 1478559 2249705 := bstep (se 2 (by rfl) ⟨843639, by rfl⟩ : syracuseStep 2249705 = 1687279) B1687279
theorem B1479707 : Blo 1478559 1479707 := bstep (se 1 (by rfl) ⟨1109780, by rfl⟩ : syracuseStep 1479707 = 2219561) B2219561
theorem B3159071 : Blo 1478559 3159071 := bstep (se 1 (by rfl) ⟨2369303, by rfl⟩ : syracuseStep 3159071 = 4738607) B4738607
theorem B18003475 : Blo 1478559 18003475 := bstep (se 1 (by rfl) ⟨13502606, by rfl⟩ : syracuseStep 18003475 = 27005213) B27005213
theorem B26982011 : Blo 1478559 26982011 := bstep (se 1 (by rfl) ⟨20236508, by rfl⟩ : syracuseStep 26982011 = 40473017) B40473017
theorem B2217839 : Blo 1478559 2217839 := bstep (se 1 (by rfl) ⟨1663379, by rfl⟩ : syracuseStep 2217839 = 3326759) B3326759
theorem B9476135 : Blo 1478559 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B7485695 : Blo 1478559 7485695 := bstep (se 1 (by rfl) ⟨5614271, by rfl⟩ : syracuseStep 7485695 = 11228543) B11228543
theorem B3848467 : Blo 1478559 3848467 := bstep (se 1 (by rfl) ⟨2886350, by rfl⟩ : syracuseStep 3848467 = 5772701) B5772701
theorem B4995431 : Blo 1478559 4995431 := bstep (se 1 (by rfl) ⟨3746573, by rfl⟩ : syracuseStep 4995431 = 7493147) B7493147
theorem B2218991 : Blo 1478559 2218991 := bstep (se 1 (by rfl) ⟨1664243, by rfl⟩ : syracuseStep 2218991 = 3328487) B3328487
theorem B38968883 : Blo 1478559 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B2219675 : Blo 1478559 2219675 := bstep (se 1 (by rfl) ⟨1664756, by rfl⟩ : syracuseStep 2219675 = 3329513) B3329513
theorem B2055871 : Blo 1478559 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B18964367 : Blo 1478559 18964367 := bstep (se 1 (by rfl) ⟨14223275, by rfl⟩ : syracuseStep 18964367 = 28446551) B28446551
theorem B21323843 : Blo 1478559 21323843 := bstep (se 1 (by rfl) ⟨15992882, by rfl⟩ : syracuseStep 21323843 = 31985765) B31985765
theorem B2105455 : Blo 1478559 2105455 := bstep (se 1 (by rfl) ⟨1579091, by rfl⟩ : syracuseStep 2105455 = 3158183) B3158183
theorem B54698203 : Blo 1478559 54698203 := bstep (se 1 (by rfl) ⟨41023652, by rfl⟩ : syracuseStep 54698203 = 82047305) B82047305
theorem B7487801 : Blo 1478559 7487801 := bstep (se 2 (by rfl) ⟨2807925, by rfl⟩ : syracuseStep 7487801 = 5615851) B5615851
theorem B2220479 : Blo 1478559 2220479 := bstep (se 1 (by rfl) ⟨1665359, by rfl⟩ : syracuseStep 2220479 = 3330719) B3330719
theorem B2220671 : Blo 1478559 2220671 := bstep (se 1 (by rfl) ⟨1665503, by rfl⟩ : syracuseStep 2220671 = 3331007) B3331007
theorem B1499803 : Blo 1478559 1499803 := bstep (se 1 (by rfl) ⟨1124852, by rfl⟩ : syracuseStep 1499803 = 2249705) B2249705
theorem B2106047 : Blo 1478559 2106047 := bstep (se 1 (by rfl) ⟨1579535, by rfl⟩ : syracuseStep 2106047 = 3159071) B3159071
theorem B3327047 : Blo 1478559 3327047 := bstep (se 1 (by rfl) ⟨2495285, by rfl⟩ : syracuseStep 3327047 = 4990571) B4990571
theorem B6317423 : Blo 1478559 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B3327479 : Blo 1478559 3327479 := bstep (se 1 (by rfl) ⟨2495609, by rfl⟩ : syracuseStep 3327479 = 4991219) B4991219
theorem B4990463 : Blo 1478559 4990463 := bstep (se 1 (by rfl) ⟨3742847, by rfl⟩ : syracuseStep 4990463 = 7485695) B7485695
theorem B7489259 : Blo 1478559 7489259 := bstep (se 1 (by rfl) ⟨5616944, by rfl⟩ : syracuseStep 7489259 = 11233889) B11233889
theorem B24004633 : Blo 1478559 24004633 := bstep (se 2 (by rfl) ⟨9001737, by rfl⟩ : syracuseStep 24004633 = 18003475) B18003475
theorem B3328055 : Blo 1478559 3328055 := bstep (se 1 (by rfl) ⟨2496041, by rfl⟩ : syracuseStep 3328055 = 4992083) B4992083
theorem B25979255 : Blo 1478559 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B12642911 : Blo 1478559 12642911 := bstep (se 1 (by rfl) ⟨9482183, by rfl⟩ : syracuseStep 12642911 = 18964367) B18964367
theorem B5131289 : Blo 1478559 5131289 := bstep (se 2 (by rfl) ⟨1924233, by rfl⟩ : syracuseStep 5131289 = 3848467) B3848467
theorem B11234375 : Blo 1478559 11234375 := bstep (se 1 (by rfl) ⟨8425781, by rfl⟩ : syracuseStep 11234375 = 16851563) B16851563
theorem B3419563 : Blo 1478559 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B10964645 : Blo 1478559 10964645 := bstep (se 4 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 10964645 = 2055871) B2055871
theorem B1478559 : Blo 1478559 1478559 := bstep (se 1 (by rfl) ⟨1108919, by rfl⟩ : syracuseStep 1478559 = 2217839) B2217839
theorem B3330287 : Blo 1478559 3330287 := bstep (se 1 (by rfl) ⟨2497715, by rfl⟩ : syracuseStep 3330287 = 4995431) B4995431
theorem B1479327 : Blo 1478559 1479327 := bstep (se 1 (by rfl) ⟨1109495, by rfl⟩ : syracuseStep 1479327 = 2218991) B2218991
theorem B4993919 : Blo 1478559 4993919 := bstep (se 1 (by rfl) ⟨3745439, by rfl⟩ : syracuseStep 4993919 = 7490879) B7490879
theorem B4994027 : Blo 1478559 4994027 := bstep (se 1 (by rfl) ⟨3745520, by rfl⟩ : syracuseStep 4994027 = 7491041) B7491041
theorem B1479783 : Blo 1478559 1479783 := bstep (se 1 (by rfl) ⟨1109837, by rfl⟩ : syracuseStep 1479783 = 2219675) B2219675
theorem B5616809 : Blo 1478559 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B4994351 : Blo 1478559 4994351 := bstep (se 1 (by rfl) ⟨3745763, by rfl⟩ : syracuseStep 4994351 = 7491527) B7491527
theorem B54007235 : Blo 1478559 54007235 := bstep (se 1 (by rfl) ⟨40505426, by rfl⟩ : syracuseStep 54007235 = 81010853) B81010853
theorem B17988007 : Blo 1478559 17988007 := bstep (se 1 (by rfl) ⟨13491005, by rfl⟩ : syracuseStep 17988007 = 26982011) B26982011
theorem B2219111 : Blo 1478559 2219111 := bstep (se 1 (by rfl) ⟨1664333, by rfl⟩ : syracuseStep 2219111 = 3328667) B3328667
theorem B4743143 : Blo 1478559 4743143 := bstep (se 1 (by rfl) ⟨3557357, by rfl⟩ : syracuseStep 4743143 = 7114715) B7114715
theorem B32006177 : Blo 1478559 32006177 := bstep (se 2 (by rfl) ⟨12002316, by rfl⟩ : syracuseStep 32006177 = 24004633) B24004633
theorem B2220191 : Blo 1478559 2220191 := bstep (se 1 (by rfl) ⟨1665143, by rfl⟩ : syracuseStep 2220191 = 3330287) B3330287
theorem B3744539 : Blo 1478559 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B4211615 : Blo 1478559 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B36004823 : Blo 1478559 36004823 := bstep (se 1 (by rfl) ⟨27003617, by rfl⟩ : syracuseStep 36004823 = 54007235) B54007235
theorem B3326975 : Blo 1478559 3326975 := bstep (se 1 (by rfl) ⟨2495231, by rfl⟩ : syracuseStep 3326975 = 4990463) B4990463
theorem B17319503 : Blo 1478559 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B7489583 : Blo 1478559 7489583 := bstep (se 1 (by rfl) ⟨5617187, by rfl⟩ : syracuseStep 7489583 = 11234375) B11234375
theorem B7309763 : Blo 1478559 7309763 := bstep (se 1 (by rfl) ⟨5482322, by rfl⟩ : syracuseStep 7309763 = 10964645) B10964645
theorem B14215895 : Blo 1478559 14215895 := bstep (se 1 (by rfl) ⟨10661921, by rfl⟩ : syracuseStep 14215895 = 21323843) B21323843
theorem B4991867 : Blo 1478559 4991867 := bstep (se 1 (by rfl) ⟨3743900, by rfl⟩ : syracuseStep 4991867 = 7487801) B7487801
theorem B3329279 : Blo 1478559 3329279 := bstep (se 1 (by rfl) ⟨2496959, by rfl⟩ : syracuseStep 3329279 = 4993919) B4993919
theorem B3329351 : Blo 1478559 3329351 := bstep (se 1 (by rfl) ⟨2497013, by rfl⟩ : syracuseStep 3329351 = 4994027) B4994027
theorem B7998949 : Blo 1478559 7998949 := bstep (se 4 (by rfl) ⟨749901, by rfl⟩ : syracuseStep 7998949 = 1499803) B1499803
theorem B3329567 : Blo 1478559 3329567 := bstep (se 1 (by rfl) ⟨2497175, by rfl⟩ : syracuseStep 3329567 = 4994351) B4994351
theorem B4992839 : Blo 1478559 4992839 := bstep (se 1 (by rfl) ⟨3744629, by rfl⟩ : syracuseStep 4992839 = 7489259) B7489259
theorem B5616125 : Blo 1478559 5616125 := bstep (se 3 (by rfl) ⟨1053023, by rfl⟩ : syracuseStep 5616125 = 2106047) B2106047
theorem B4559417 : Blo 1478559 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3420859 : Blo 1478559 3420859 := bstep (se 1 (by rfl) ⟨2565644, by rfl⟩ : syracuseStep 3420859 = 5131289) B5131289
theorem B1479407 : Blo 1478559 1479407 := bstep (se 1 (by rfl) ⟨1109555, by rfl⟩ : syracuseStep 1479407 = 2219111) B2219111
theorem B2807273 : Blo 1478559 2807273 := bstep (se 2 (by rfl) ⟨1052727, by rfl⟩ : syracuseStep 2807273 = 2105455) B2105455
theorem B72930937 : Blo 1478559 72930937 := bstep (se 2 (by rfl) ⟨27349101, by rfl⟩ : syracuseStep 72930937 = 54698203) B54698203
theorem B1480319 : Blo 1478559 1480319 := bstep (se 1 (by rfl) ⟨1110239, by rfl⟩ : syracuseStep 1480319 = 2220479) B2220479
theorem B1480447 : Blo 1478559 1480447 := bstep (se 1 (by rfl) ⟨1110335, by rfl⟩ : syracuseStep 1480447 = 2220671) B2220671
theorem B23984009 : Blo 1478559 23984009 := bstep (se 2 (by rfl) ⟨8994003, by rfl⟩ : syracuseStep 23984009 = 17988007) B17988007
theorem B2218031 : Blo 1478559 2218031 := bstep (se 1 (by rfl) ⟨1663523, by rfl⟩ : syracuseStep 2218031 = 3327047) B3327047
theorem B2218319 : Blo 1478559 2218319 := bstep (se 1 (by rfl) ⟨1663739, by rfl⟩ : syracuseStep 2218319 = 3327479) B3327479
theorem B2218703 : Blo 1478559 2218703 := bstep (se 1 (by rfl) ⟨1664027, by rfl⟩ : syracuseStep 2218703 = 3328055) B3328055
theorem B8428607 : Blo 1478559 8428607 := bstep (se 1 (by rfl) ⟨6321455, by rfl⟩ : syracuseStep 8428607 = 12642911) B12642911
theorem B3162095 : Blo 1478559 3162095 := bstep (se 1 (by rfl) ⟨2371571, by rfl⟩ : syracuseStep 3162095 = 4743143) B4743143
theorem B3744083 : Blo 1478559 3744083 := bstep (se 1 (by rfl) ⟨2808062, by rfl⟩ : syracuseStep 3744083 = 5616125) B5616125
theorem B3039611 : Blo 1478559 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B24003215 : Blo 1478559 24003215 := bstep (se 1 (by rfl) ⟨18002411, by rfl⟩ : syracuseStep 24003215 = 36004823) B36004823
theorem B3327911 : Blo 1478559 3327911 := bstep (se 1 (by rfl) ⟨2495933, by rfl⟩ : syracuseStep 3327911 = 4991867) B4991867
theorem B97241249 : Blo 1478559 97241249 := bstep (se 2 (by rfl) ⟨36465468, by rfl⟩ : syracuseStep 97241249 = 72930937) B72930937
theorem B3328559 : Blo 1478559 3328559 := bstep (se 1 (by rfl) ⟨2496419, by rfl⟩ : syracuseStep 3328559 = 4992839) B4992839
theorem B2108063 : Blo 1478559 2108063 := bstep (se 1 (by rfl) ⟨1581047, by rfl⟩ : syracuseStep 2108063 = 3162095) B3162095
theorem B1871515 : Blo 1478559 1871515 := bstep (se 1 (by rfl) ⟨1403636, by rfl⟩ : syracuseStep 1871515 = 2807273) B2807273
theorem B11546335 : Blo 1478559 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B1478687 : Blo 1478559 1478687 := bstep (se 1 (by rfl) ⟨1109015, by rfl⟩ : syracuseStep 1478687 = 2218031) B2218031
theorem B4993055 : Blo 1478559 4993055 := bstep (se 1 (by rfl) ⟨3744791, by rfl⟩ : syracuseStep 4993055 = 7489583) B7489583
theorem B1478879 : Blo 1478559 1478879 := bstep (se 1 (by rfl) ⟨1109159, by rfl⟩ : syracuseStep 1478879 = 2218319) B2218319
theorem B1479135 : Blo 1478559 1479135 := bstep (se 1 (by rfl) ⟨1109351, by rfl⟩ : syracuseStep 1479135 = 2218703) B2218703
theorem B21337451 : Blo 1478559 21337451 := bstep (se 1 (by rfl) ⟨16003088, by rfl⟩ : syracuseStep 21337451 = 32006177) B32006177
theorem B1480127 : Blo 1478559 1480127 := bstep (se 1 (by rfl) ⟨1110095, by rfl⟩ : syracuseStep 1480127 = 2220191) B2220191
theorem B2496359 : Blo 1478559 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B2217983 : Blo 1478559 2217983 := bstep (se 1 (by rfl) ⟨1663487, by rfl⟩ : syracuseStep 2217983 = 3326975) B3326975
theorem B4561145 : Blo 1478559 4561145 := bstep (se 2 (by rfl) ⟨1710429, by rfl⟩ : syracuseStep 4561145 = 3420859) B3420859
theorem B15989339 : Blo 1478559 15989339 := bstep (se 1 (by rfl) ⟨11992004, by rfl⟩ : syracuseStep 15989339 = 23984009) B23984009
theorem B4873175 : Blo 1478559 4873175 := bstep (se 1 (by rfl) ⟨3654881, by rfl⟩ : syracuseStep 4873175 = 7309763) B7309763
theorem B9477263 : Blo 1478559 9477263 := bstep (se 1 (by rfl) ⟨7107947, by rfl⟩ : syracuseStep 9477263 = 14215895) B14215895
theorem B10665265 : Blo 1478559 10665265 := bstep (se 2 (by rfl) ⟨3999474, by rfl⟩ : syracuseStep 10665265 = 7998949) B7998949
theorem B5619071 : Blo 1478559 5619071 := bstep (se 1 (by rfl) ⟨4214303, by rfl⟩ : syracuseStep 5619071 = 8428607) B8428607
theorem B2219519 : Blo 1478559 2219519 := bstep (se 1 (by rfl) ⟨1664639, by rfl⟩ : syracuseStep 2219519 = 3329279) B3329279
theorem B2219567 : Blo 1478559 2219567 := bstep (se 1 (by rfl) ⟨1664675, by rfl⟩ : syracuseStep 2219567 = 3329351) B3329351
theorem B2219711 : Blo 1478559 2219711 := bstep (se 1 (by rfl) ⟨1664783, by rfl⟩ : syracuseStep 2219711 = 3329567) B3329567
theorem B11230973 : Blo 1478559 11230973 := bstep (se 3 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 11230973 = 4211615) B4211615
theorem B1664239 : Blo 1478559 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B3040763 : Blo 1478559 3040763 := bstep (se 1 (by rfl) ⟨2280572, by rfl⟩ : syracuseStep 3040763 = 4561145) B4561145
theorem B10659559 : Blo 1478559 10659559 := bstep (se 1 (by rfl) ⟨7994669, by rfl⟩ : syracuseStep 10659559 = 15989339) B15989339
theorem B5621501 : Blo 1478559 5621501 := bstep (se 3 (by rfl) ⟨1054031, by rfl⟩ : syracuseStep 5621501 = 2108063) B2108063
theorem B6318175 : Blo 1478559 6318175 := bstep (se 1 (by rfl) ⟨4738631, by rfl⟩ : syracuseStep 6318175 = 9477263) B9477263
theorem B3746047 : Blo 1478559 3746047 := bstep (se 1 (by rfl) ⟨2809535, by rfl⟩ : syracuseStep 3746047 = 5619071) B5619071
theorem B15395113 : Blo 1478559 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B3328703 : Blo 1478559 3328703 := bstep (se 1 (by rfl) ⟨2496527, by rfl⟩ : syracuseStep 3328703 = 4993055) B4993055
theorem B16002143 : Blo 1478559 16002143 := bstep (se 1 (by rfl) ⟨12001607, by rfl⟩ : syracuseStep 16002143 = 24003215) B24003215
theorem B14224967 : Blo 1478559 14224967 := bstep (se 1 (by rfl) ⟨10668725, by rfl⟩ : syracuseStep 14224967 = 21337451) B21337451
theorem B1478655 : Blo 1478559 1478655 := bstep (se 1 (by rfl) ⟨1108991, by rfl⟩ : syracuseStep 1478655 = 2217983) B2217983
theorem B64827499 : Blo 1478559 64827499 := bstep (se 1 (by rfl) ⟨48620624, by rfl⟩ : syracuseStep 64827499 = 97241249) B97241249
theorem B3248783 : Blo 1478559 3248783 := bstep (se 1 (by rfl) ⟨2436587, by rfl⟩ : syracuseStep 3248783 = 4873175) B4873175
theorem B2495353 : Blo 1478559 2495353 := bstep (se 2 (by rfl) ⟨935757, by rfl⟩ : syracuseStep 2495353 = 1871515) B1871515
theorem B1479679 : Blo 1478559 1479679 := bstep (se 1 (by rfl) ⟨1109759, by rfl⟩ : syracuseStep 1479679 = 2219519) B2219519
theorem B1479711 : Blo 1478559 1479711 := bstep (se 1 (by rfl) ⟨1109783, by rfl⟩ : syracuseStep 1479711 = 2219567) B2219567
theorem B1479807 : Blo 1478559 1479807 := bstep (se 1 (by rfl) ⟨1109855, by rfl⟩ : syracuseStep 1479807 = 2219711) B2219711
theorem B2496055 : Blo 1478559 2496055 := bstep (se 1 (by rfl) ⟨1872041, by rfl⟩ : syracuseStep 2496055 = 3744083) B3744083
theorem B2218607 : Blo 1478559 2218607 := bstep (se 1 (by rfl) ⟨1663955, by rfl⟩ : syracuseStep 2218607 = 3327911) B3327911
theorem B32422517 : Blo 1478559 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B2219039 : Blo 1478559 2219039 := bstep (se 1 (by rfl) ⟨1664279, by rfl⟩ : syracuseStep 2219039 = 3328559) B3328559
theorem B14220353 : Blo 1478559 14220353 := bstep (se 2 (by rfl) ⟨5332632, by rfl⟩ : syracuseStep 14220353 = 10665265) B10665265
theorem B7487315 : Blo 1478559 7487315 := bstep (se 1 (by rfl) ⟨5615486, by rfl⟩ : syracuseStep 7487315 = 11230973) B11230973
theorem B3327137 : Blo 1478559 3327137 := bstep (se 2 (by rfl) ⟨1247676, by rfl⟩ : syracuseStep 3327137 = 2495353) B2495353
theorem B9480235 : Blo 1478559 9480235 := bstep (se 1 (by rfl) ⟨7110176, by rfl⟩ : syracuseStep 9480235 = 14220353) B14220353
theorem B10668095 : Blo 1478559 10668095 := bstep (se 1 (by rfl) ⟨8001071, by rfl⟩ : syracuseStep 10668095 = 16002143) B16002143
theorem B3328073 : Blo 1478559 3328073 := bstep (se 2 (by rfl) ⟨1248027, by rfl⟩ : syracuseStep 3328073 = 2496055) B2496055
theorem B4991543 : Blo 1478559 4991543 := bstep (se 1 (by rfl) ⟨3743657, by rfl⟩ : syracuseStep 4991543 = 7487315) B7487315
theorem B32434805 : Blo 1478559 32434805 := bstep (se 5 (by rfl) ⟨1520381, by rfl⟩ : syracuseStep 32434805 = 3040763) B3040763
theorem B8424233 : Blo 1478559 8424233 := bstep (se 2 (by rfl) ⟨3159087, by rfl⟩ : syracuseStep 8424233 = 6318175) B6318175
theorem B86436665 : Blo 1478559 86436665 := bstep (se 2 (by rfl) ⟨32413749, by rfl⟩ : syracuseStep 86436665 = 64827499) B64827499
theorem B2165855 : Blo 1478559 2165855 := bstep (se 1 (by rfl) ⟨1624391, by rfl⟩ : syracuseStep 2165855 = 3248783) B3248783
theorem B3747667 : Blo 1478559 3747667 := bstep (se 1 (by rfl) ⟨2810750, by rfl⟩ : syracuseStep 3747667 = 5621501) B5621501
theorem B1479071 : Blo 1478559 1479071 := bstep (se 1 (by rfl) ⟨1109303, by rfl⟩ : syracuseStep 1479071 = 2218607) B2218607
theorem B21615011 : Blo 1478559 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B1479359 : Blo 1478559 1479359 := bstep (se 1 (by rfl) ⟨1109519, by rfl⟩ : syracuseStep 1479359 = 2219039) B2219039
theorem B9483311 : Blo 1478559 9483311 := bstep (se 1 (by rfl) ⟨7112483, by rfl⟩ : syracuseStep 9483311 = 14224967) B14224967
theorem B4994729 : Blo 1478559 4994729 := bstep (se 2 (by rfl) ⟨1873023, by rfl⟩ : syracuseStep 4994729 = 3746047) B3746047
theorem B20526817 : Blo 1478559 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B2218985 : Blo 1478559 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B2219135 : Blo 1478559 2219135 := bstep (se 1 (by rfl) ⟨1664351, by rfl⟩ : syracuseStep 2219135 = 3328703) B3328703
theorem B14212745 : Blo 1478559 14212745 := bstep (se 2 (by rfl) ⟨5329779, by rfl⟩ : syracuseStep 14212745 = 10659559) B10659559
theorem B12640313 : Blo 1478559 12640313 := bstep (se 2 (by rfl) ⟨4740117, by rfl⟩ : syracuseStep 12640313 = 9480235) B9480235
theorem B14410007 : Blo 1478559 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B23102453 : Blo 1478559 23102453 := bstep (se 5 (by rfl) ⟨1082927, by rfl⟩ : syracuseStep 23102453 = 2165855) B2165855
theorem B7112063 : Blo 1478559 7112063 := bstep (se 1 (by rfl) ⟨5334047, by rfl⟩ : syracuseStep 7112063 = 10668095) B10668095
theorem B3327695 : Blo 1478559 3327695 := bstep (se 1 (by rfl) ⟨2495771, by rfl⟩ : syracuseStep 3327695 = 4991543) B4991543
theorem B57624443 : Blo 1478559 57624443 := bstep (se 1 (by rfl) ⟨43218332, by rfl⟩ : syracuseStep 57624443 = 86436665) B86436665
theorem B3329819 : Blo 1478559 3329819 := bstep (se 1 (by rfl) ⟨2497364, by rfl⟩ : syracuseStep 3329819 = 4994729) B4994729
theorem B21623203 : Blo 1478559 21623203 := bstep (se 1 (by rfl) ⟨16217402, by rfl⟩ : syracuseStep 21623203 = 32434805) B32434805
theorem B5616155 : Blo 1478559 5616155 := bstep (se 1 (by rfl) ⟨4212116, by rfl⟩ : syracuseStep 5616155 = 8424233) B8424233
theorem B1479323 : Blo 1478559 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B1479423 : Blo 1478559 1479423 := bstep (se 1 (by rfl) ⟨1109567, by rfl⟩ : syracuseStep 1479423 = 2219135) B2219135
theorem B9475163 : Blo 1478559 9475163 := bstep (se 1 (by rfl) ⟨7106372, by rfl⟩ : syracuseStep 9475163 = 14212745) B14212745
theorem B6322207 : Blo 1478559 6322207 := bstep (se 1 (by rfl) ⟨4741655, by rfl⟩ : syracuseStep 6322207 = 9483311) B9483311
theorem B2218091 : Blo 1478559 2218091 := bstep (se 1 (by rfl) ⟨1663568, by rfl⟩ : syracuseStep 2218091 = 3327137) B3327137
theorem B2218715 : Blo 1478559 2218715 := bstep (se 1 (by rfl) ⟨1664036, by rfl⟩ : syracuseStep 2218715 = 3328073) B3328073
theorem B27369089 : Blo 1478559 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B4996889 : Blo 1478559 4996889 := bstep (se 2 (by rfl) ⟨1873833, by rfl⟩ : syracuseStep 4996889 = 3747667) B3747667
theorem B8429609 : Blo 1478559 8429609 := bstep (se 2 (by rfl) ⟨3161103, by rfl⟩ : syracuseStep 8429609 = 6322207) B6322207
theorem B3744103 : Blo 1478559 3744103 := bstep (se 1 (by rfl) ⟨2808077, by rfl⟩ : syracuseStep 3744103 = 5616155) B5616155
theorem B6316775 : Blo 1478559 6316775 := bstep (se 1 (by rfl) ⟨4737581, by rfl⟩ : syracuseStep 6316775 = 9475163) B9475163
theorem B18246059 : Blo 1478559 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B61606541 : Blo 1478559 61606541 := bstep (se 3 (by rfl) ⟨11551226, by rfl⟩ : syracuseStep 61606541 = 23102453) B23102453
theorem B28830937 : Blo 1478559 28830937 := bstep (se 2 (by rfl) ⟨10811601, by rfl⟩ : syracuseStep 28830937 = 21623203) B21623203
theorem B38416295 : Blo 1478559 38416295 := bstep (se 1 (by rfl) ⟨28812221, by rfl⟩ : syracuseStep 38416295 = 57624443) B57624443
theorem B1478727 : Blo 1478559 1478727 := bstep (se 1 (by rfl) ⟨1109045, by rfl⟩ : syracuseStep 1478727 = 2218091) B2218091
theorem B1479143 : Blo 1478559 1479143 := bstep (se 1 (by rfl) ⟨1109357, by rfl⟩ : syracuseStep 1479143 = 2218715) B2218715
theorem B3331259 : Blo 1478559 3331259 := bstep (se 1 (by rfl) ⟨2498444, by rfl⟩ : syracuseStep 3331259 = 4996889) B4996889
theorem B8426875 : Blo 1478559 8426875 := bstep (se 1 (by rfl) ⟨6320156, by rfl⟩ : syracuseStep 8426875 = 12640313) B12640313
theorem B9606671 : Blo 1478559 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B4741375 : Blo 1478559 4741375 := bstep (se 1 (by rfl) ⟨3556031, by rfl⟩ : syracuseStep 4741375 = 7112063) B7112063
theorem B2218463 : Blo 1478559 2218463 := bstep (se 1 (by rfl) ⟨1663847, by rfl⟩ : syracuseStep 2218463 = 3327695) B3327695
theorem B2219879 : Blo 1478559 2219879 := bstep (se 1 (by rfl) ⟨1664909, by rfl⟩ : syracuseStep 2219879 = 3329819) B3329819
theorem B5619739 : Blo 1478559 5619739 := bstep (se 1 (by rfl) ⟨4214804, by rfl⟩ : syracuseStep 5619739 = 8429609) B8429609
theorem B4211183 : Blo 1478559 4211183 := bstep (se 1 (by rfl) ⟨3158387, by rfl⟩ : syracuseStep 4211183 = 6316775) B6316775
theorem B2220839 : Blo 1478559 2220839 := bstep (se 1 (by rfl) ⟨1665629, by rfl⟩ : syracuseStep 2220839 = 3331259) B3331259
theorem B164284109 : Blo 1478559 164284109 := bstep (se 3 (by rfl) ⟨30803270, by rfl⟩ : syracuseStep 164284109 = 61606541) B61606541
theorem B102443453 : Blo 1478559 102443453 := bstep (se 3 (by rfl) ⟨19208147, by rfl⟩ : syracuseStep 102443453 = 38416295) B38416295
theorem B4992137 : Blo 1478559 4992137 := bstep (se 2 (by rfl) ⟨1872051, by rfl⟩ : syracuseStep 4992137 = 3744103) B3744103
theorem B38441249 : Blo 1478559 38441249 := bstep (se 2 (by rfl) ⟨14415468, by rfl⟩ : syracuseStep 38441249 = 28830937) B28830937
theorem B1478975 : Blo 1478559 1478975 := bstep (se 1 (by rfl) ⟨1109231, by rfl⟩ : syracuseStep 1478975 = 2218463) B2218463
theorem B11235833 : Blo 1478559 11235833 := bstep (se 2 (by rfl) ⟨4213437, by rfl⟩ : syracuseStep 11235833 = 8426875) B8426875
theorem B1479919 : Blo 1478559 1479919 := bstep (se 1 (by rfl) ⟨1109939, by rfl⟩ : syracuseStep 1479919 = 2219879) B2219879
theorem B6321833 : Blo 1478559 6321833 := bstep (se 2 (by rfl) ⟨2370687, by rfl⟩ : syracuseStep 6321833 = 4741375) B4741375
theorem B6404447 : Blo 1478559 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B12164039 : Blo 1478559 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B3328091 : Blo 1478559 3328091 := bstep (se 1 (by rfl) ⟨2496068, by rfl⟩ : syracuseStep 3328091 = 4992137) B4992137
theorem B25627499 : Blo 1478559 25627499 := bstep (se 1 (by rfl) ⟨19220624, by rfl⟩ : syracuseStep 25627499 = 38441249) B38441249
theorem B7490555 : Blo 1478559 7490555 := bstep (se 1 (by rfl) ⟨5617916, by rfl⟩ : syracuseStep 7490555 = 11235833) B11235833
theorem B4214555 : Blo 1478559 4214555 := bstep (se 1 (by rfl) ⟨3160916, by rfl⟩ : syracuseStep 4214555 = 6321833) B6321833
theorem B109522739 : Blo 1478559 109522739 := bstep (se 1 (by rfl) ⟨82142054, by rfl⟩ : syracuseStep 109522739 = 164284109) B164284109
theorem B7492985 : Blo 1478559 7492985 := bstep (se 2 (by rfl) ⟨2809869, by rfl⟩ : syracuseStep 7492985 = 5619739) B5619739
theorem B2807455 : Blo 1478559 2807455 := bstep (se 1 (by rfl) ⟨2105591, by rfl⟩ : syracuseStep 2807455 = 4211183) B4211183
theorem B1480559 : Blo 1478559 1480559 := bstep (se 1 (by rfl) ⟨1110419, by rfl⟩ : syracuseStep 1480559 = 2220839) B2220839
theorem B17078525 : Blo 1478559 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B68295635 : Blo 1478559 68295635 := bstep (se 1 (by rfl) ⟨51221726, by rfl⟩ : syracuseStep 68295635 = 102443453) B102443453
theorem B8109359 : Blo 1478559 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B17084999 : Blo 1478559 17084999 := bstep (se 1 (by rfl) ⟨12813749, by rfl⟩ : syracuseStep 17084999 = 25627499) B25627499
theorem B4993703 : Blo 1478559 4993703 := bstep (se 1 (by rfl) ⟨3745277, by rfl⟩ : syracuseStep 4993703 = 7490555) B7490555
theorem B4995323 : Blo 1478559 4995323 := bstep (se 1 (by rfl) ⟨3746492, by rfl⟩ : syracuseStep 4995323 = 7492985) B7492985
theorem B2218727 : Blo 1478559 2218727 := bstep (se 1 (by rfl) ⟨1664045, by rfl⟩ : syracuseStep 2218727 = 3328091) B3328091
theorem B11385683 : Blo 1478559 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B45530423 : Blo 1478559 45530423 := bstep (se 1 (by rfl) ⟨34147817, by rfl⟩ : syracuseStep 45530423 = 68295635) B68295635
theorem B292060637 : Blo 1478559 292060637 := bstep (se 3 (by rfl) ⟨54761369, by rfl⟩ : syracuseStep 292060637 = 109522739) B109522739
theorem B5406239 : Blo 1478559 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B3743273 : Blo 1478559 3743273 := bstep (se 2 (by rfl) ⟨1403727, by rfl⟩ : syracuseStep 3743273 = 2807455) B2807455
theorem B2809703 : Blo 1478559 2809703 := bstep (se 1 (by rfl) ⟨2107277, by rfl⟩ : syracuseStep 2809703 = 4214555) B4214555
theorem B30353615 : Blo 1478559 30353615 := bstep (se 1 (by rfl) ⟨22765211, by rfl⟩ : syracuseStep 30353615 = 45530423) B45530423
theorem B11389999 : Blo 1478559 11389999 := bstep (se 1 (by rfl) ⟨8542499, by rfl⟩ : syracuseStep 11389999 = 17084999) B17084999
theorem B3329135 : Blo 1478559 3329135 := bstep (se 1 (by rfl) ⟨2496851, by rfl⟩ : syracuseStep 3329135 = 4993703) B4993703
theorem B3330215 : Blo 1478559 3330215 := bstep (se 1 (by rfl) ⟨2497661, by rfl⟩ : syracuseStep 3330215 = 4995323) B4995323
theorem B1479151 : Blo 1478559 1479151 := bstep (se 1 (by rfl) ⟨1109363, by rfl⟩ : syracuseStep 1479151 = 2218727) B2218727
theorem B7590455 : Blo 1478559 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B2495515 : Blo 1478559 2495515 := bstep (se 1 (by rfl) ⟨1871636, by rfl⟩ : syracuseStep 2495515 = 3743273) B3743273
theorem B1873135 : Blo 1478559 1873135 := bstep (se 1 (by rfl) ⟨1404851, by rfl⟩ : syracuseStep 1873135 = 2809703) B2809703
theorem B194707091 : Blo 1478559 194707091 := bstep (se 1 (by rfl) ⟨146030318, by rfl⟩ : syracuseStep 194707091 = 292060637) B292060637
theorem B3604159 : Blo 1478559 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B2220143 : Blo 1478559 2220143 := bstep (se 1 (by rfl) ⟨1665107, by rfl⟩ : syracuseStep 2220143 = 3330215) B3330215
theorem B3327353 : Blo 1478559 3327353 := bstep (se 2 (by rfl) ⟨1247757, by rfl⟩ : syracuseStep 3327353 = 2495515) B2495515
theorem B20235743 : Blo 1478559 20235743 := bstep (se 1 (by rfl) ⟨15176807, by rfl⟩ : syracuseStep 20235743 = 30353615) B30353615
theorem B129804727 : Blo 1478559 129804727 := bstep (se 1 (by rfl) ⟨97353545, by rfl⟩ : syracuseStep 129804727 = 194707091) B194707091
theorem B19222181 : Blo 1478559 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B5060303 : Blo 1478559 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B15186665 : Blo 1478559 15186665 := bstep (se 2 (by rfl) ⟨5694999, by rfl⟩ : syracuseStep 15186665 = 11389999) B11389999
theorem B2497513 : Blo 1478559 2497513 := bstep (se 2 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 2497513 = 1873135) B1873135
theorem B2219423 : Blo 1478559 2219423 := bstep (se 1 (by rfl) ⟨1664567, by rfl⟩ : syracuseStep 2219423 = 3329135) B3329135
theorem B173072969 : Blo 1478559 173072969 := bstep (se 2 (by rfl) ⟨64902363, by rfl⟩ : syracuseStep 173072969 = 129804727) B129804727
theorem B12814787 : Blo 1478559 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B3330017 : Blo 1478559 3330017 := bstep (se 2 (by rfl) ⟨1248756, by rfl⟩ : syracuseStep 3330017 = 2497513) B2497513
theorem B1479615 : Blo 1478559 1479615 := bstep (se 1 (by rfl) ⟨1109711, by rfl⟩ : syracuseStep 1479615 = 2219423) B2219423
theorem B1480095 : Blo 1478559 1480095 := bstep (se 1 (by rfl) ⟨1110071, by rfl⟩ : syracuseStep 1480095 = 2220143) B2220143
theorem B2218235 : Blo 1478559 2218235 := bstep (se 1 (by rfl) ⟨1663676, by rfl⟩ : syracuseStep 2218235 = 3327353) B3327353
theorem B13490495 : Blo 1478559 13490495 := bstep (se 1 (by rfl) ⟨10117871, by rfl⟩ : syracuseStep 13490495 = 20235743) B20235743
theorem B3373535 : Blo 1478559 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B10124443 : Blo 1478559 10124443 := bstep (se 1 (by rfl) ⟨7593332, by rfl⟩ : syracuseStep 10124443 = 15186665) B15186665
theorem B8996093 : Blo 1478559 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B34172765 : Blo 1478559 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B1478823 : Blo 1478559 1478823 := bstep (se 1 (by rfl) ⟨1109117, by rfl⟩ : syracuseStep 1478823 = 2218235) B2218235
theorem B115381979 : Blo 1478559 115381979 := bstep (se 1 (by rfl) ⟨86536484, by rfl⟩ : syracuseStep 115381979 = 173072969) B173072969
theorem B13499257 : Blo 1478559 13499257 := bstep (se 2 (by rfl) ⟨5062221, by rfl⟩ : syracuseStep 13499257 = 10124443) B10124443
theorem B8993663 : Blo 1478559 8993663 := bstep (se 1 (by rfl) ⟨6745247, by rfl⟩ : syracuseStep 8993663 = 13490495) B13490495
theorem B2220011 : Blo 1478559 2220011 := bstep (se 1 (by rfl) ⟨1665008, by rfl⟩ : syracuseStep 2220011 = 3330017) B3330017
theorem B5997395 : Blo 1478559 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B17999009 : Blo 1478559 17999009 := bstep (se 2 (by rfl) ⟨6749628, by rfl⟩ : syracuseStep 17999009 = 13499257) B13499257
theorem B1480007 : Blo 1478559 1480007 := bstep (se 1 (by rfl) ⟨1110005, by rfl⟩ : syracuseStep 1480007 = 2220011) B2220011
theorem B76921319 : Blo 1478559 76921319 := bstep (se 1 (by rfl) ⟨57690989, by rfl⟩ : syracuseStep 76921319 = 115381979) B115381979
theorem B5995775 : Blo 1478559 5995775 := bstep (se 1 (by rfl) ⟨4496831, by rfl⟩ : syracuseStep 5995775 = 8993663) B8993663
theorem B22781843 : Blo 1478559 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B15993053 : Blo 1478559 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B11999339 : Blo 1478559 11999339 := bstep (se 1 (by rfl) ⟨8999504, by rfl⟩ : syracuseStep 11999339 = 17999009) B17999009
theorem B51280879 : Blo 1478559 51280879 := bstep (se 1 (by rfl) ⟨38460659, by rfl⟩ : syracuseStep 51280879 = 76921319) B76921319
theorem B3997183 : Blo 1478559 3997183 := bstep (se 1 (by rfl) ⟨2997887, by rfl⟩ : syracuseStep 3997183 = 5995775) B5995775
theorem B15187895 : Blo 1478559 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B68374505 : Blo 1478559 68374505 := bstep (se 2 (by rfl) ⟨25640439, by rfl⟩ : syracuseStep 68374505 = 51280879) B51280879
theorem B7999559 : Blo 1478559 7999559 := bstep (se 1 (by rfl) ⟨5999669, by rfl⟩ : syracuseStep 7999559 = 11999339) B11999339
theorem B10662035 : Blo 1478559 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B5329577 : Blo 1478559 5329577 := bstep (se 2 (by rfl) ⟨1998591, by rfl⟩ : syracuseStep 5329577 = 3997183) B3997183
theorem B10125263 : Blo 1478559 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B5333039 : Blo 1478559 5333039 := bstep (se 1 (by rfl) ⟨3999779, by rfl⟩ : syracuseStep 5333039 = 7999559) B7999559
theorem B45583003 : Blo 1478559 45583003 := bstep (se 1 (by rfl) ⟨34187252, by rfl⟩ : syracuseStep 45583003 = 68374505) B68374505
theorem B28432093 : Blo 1478559 28432093 := bstep (se 3 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 28432093 = 10662035) B10662035
theorem B14212205 : Blo 1478559 14212205 := bstep (se 3 (by rfl) ⟨2664788, by rfl⟩ : syracuseStep 14212205 = 5329577) B5329577
theorem B27000701 : Blo 1478559 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B3555359 : Blo 1478559 3555359 := bstep (se 1 (by rfl) ⟨2666519, by rfl⟩ : syracuseStep 3555359 = 5333039) B5333039
theorem B18000467 : Blo 1478559 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B243109349 : Blo 1478559 243109349 := bstep (se 4 (by rfl) ⟨22791501, by rfl⟩ : syracuseStep 243109349 = 45583003) B45583003
theorem B9474803 : Blo 1478559 9474803 := bstep (se 1 (by rfl) ⟨7106102, by rfl⟩ : syracuseStep 9474803 = 14212205) B14212205
theorem B37909457 : Blo 1478559 37909457 := bstep (se 2 (by rfl) ⟨14216046, by rfl⟩ : syracuseStep 37909457 = 28432093) B28432093
theorem B6316535 : Blo 1478559 6316535 := bstep (se 1 (by rfl) ⟨4737401, by rfl⟩ : syracuseStep 6316535 = 9474803) B9474803
theorem B25272971 : Blo 1478559 25272971 := bstep (se 1 (by rfl) ⟨18954728, by rfl⟩ : syracuseStep 25272971 = 37909457) B37909457
theorem B162072899 : Blo 1478559 162072899 := bstep (se 1 (by rfl) ⟨121554674, by rfl⟩ : syracuseStep 162072899 = 243109349) B243109349
theorem B2370239 : Blo 1478559 2370239 := bstep (se 1 (by rfl) ⟨1777679, by rfl⟩ : syracuseStep 2370239 = 3555359) B3555359
theorem B12000311 : Blo 1478559 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B4211023 : Blo 1478559 4211023 := bstep (se 1 (by rfl) ⟨3158267, by rfl⟩ : syracuseStep 4211023 = 6316535) B6316535
theorem B108048599 : Blo 1478559 108048599 := bstep (se 1 (by rfl) ⟨81036449, by rfl⟩ : syracuseStep 108048599 = 162072899) B162072899
theorem B8000207 : Blo 1478559 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B16848647 : Blo 1478559 16848647 := bstep (se 1 (by rfl) ⟨12636485, by rfl⟩ : syracuseStep 16848647 = 25272971) B25272971
theorem B1580159 : Blo 1478559 1580159 := bstep (se 1 (by rfl) ⟨1185119, by rfl⟩ : syracuseStep 1580159 = 2370239) B2370239
theorem B72032399 : Blo 1478559 72032399 := bstep (se 1 (by rfl) ⟨54024299, by rfl⟩ : syracuseStep 72032399 = 108048599) B108048599
theorem B5333471 : Blo 1478559 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B11232431 : Blo 1478559 11232431 := bstep (se 1 (by rfl) ⟨8424323, by rfl⟩ : syracuseStep 11232431 = 16848647) B16848647
theorem B4213757 : Blo 1478559 4213757 := bstep (se 3 (by rfl) ⟨790079, by rfl⟩ : syracuseStep 4213757 = 1580159) B1580159
theorem B5614697 : Blo 1478559 5614697 := bstep (se 2 (by rfl) ⟨2105511, by rfl⟩ : syracuseStep 5614697 = 4211023) B4211023
theorem B48021599 : Blo 1478559 48021599 := bstep (se 1 (by rfl) ⟨36016199, by rfl⟩ : syracuseStep 48021599 = 72032399) B72032399
theorem B3555647 : Blo 1478559 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B7488287 : Blo 1478559 7488287 := bstep (se 1 (by rfl) ⟨5616215, by rfl⟩ : syracuseStep 7488287 = 11232431) B11232431
theorem B2809171 : Blo 1478559 2809171 := bstep (se 1 (by rfl) ⟨2106878, by rfl⟩ : syracuseStep 2809171 = 4213757) B4213757
theorem B3743131 : Blo 1478559 3743131 := bstep (se 1 (by rfl) ⟨2807348, by rfl⟩ : syracuseStep 3743131 = 5614697) B5614697
theorem B32014399 : Blo 1478559 32014399 := bstep (se 1 (by rfl) ⟨24010799, by rfl⟩ : syracuseStep 32014399 = 48021599) B48021599
theorem B3745561 : Blo 1478559 3745561 := bstep (se 2 (by rfl) ⟨1404585, by rfl⟩ : syracuseStep 3745561 = 2809171) B2809171
theorem B4990841 : Blo 1478559 4990841 := bstep (se 2 (by rfl) ⟨1871565, by rfl⟩ : syracuseStep 4990841 = 3743131) B3743131
theorem B2370431 : Blo 1478559 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B4992191 : Blo 1478559 4992191 := bstep (se 1 (by rfl) ⟨3744143, by rfl⟩ : syracuseStep 4992191 = 7488287) B7488287
theorem B3327227 : Blo 1478559 3327227 := bstep (se 1 (by rfl) ⟨2495420, by rfl⟩ : syracuseStep 3327227 = 4990841) B4990841
theorem B3328127 : Blo 1478559 3328127 := bstep (se 1 (by rfl) ⟨2496095, by rfl⟩ : syracuseStep 3328127 = 4992191) B4992191
theorem B6321149 : Blo 1478559 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B4994081 : Blo 1478559 4994081 := bstep (se 2 (by rfl) ⟨1872780, by rfl⟩ : syracuseStep 4994081 = 3745561) B3745561
theorem B42685865 : Blo 1478559 42685865 := bstep (se 2 (by rfl) ⟨16007199, by rfl⟩ : syracuseStep 42685865 = 32014399) B32014399
theorem B4214099 : Blo 1478559 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B3329387 : Blo 1478559 3329387 := bstep (se 1 (by rfl) ⟨2497040, by rfl⟩ : syracuseStep 3329387 = 4994081) B4994081
theorem B2218151 : Blo 1478559 2218151 := bstep (se 1 (by rfl) ⟨1663613, by rfl⟩ : syracuseStep 2218151 = 3327227) B3327227
theorem B28457243 : Blo 1478559 28457243 := bstep (se 1 (by rfl) ⟨21342932, by rfl⟩ : syracuseStep 28457243 = 42685865) B42685865
theorem B2218751 : Blo 1478559 2218751 := bstep (se 1 (by rfl) ⟨1664063, by rfl⟩ : syracuseStep 2218751 = 3328127) B3328127
theorem B1478767 : Blo 1478559 1478767 := bstep (se 1 (by rfl) ⟨1109075, by rfl⟩ : syracuseStep 1478767 = 2218151) B2218151
theorem B1479167 : Blo 1478559 1479167 := bstep (se 1 (by rfl) ⟨1109375, by rfl⟩ : syracuseStep 1479167 = 2218751) B2218751
theorem B18971495 : Blo 1478559 18971495 := bstep (se 1 (by rfl) ⟨14228621, by rfl⟩ : syracuseStep 18971495 = 28457243) B28457243
theorem B2809399 : Blo 1478559 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B2219591 : Blo 1478559 2219591 := bstep (se 1 (by rfl) ⟨1664693, by rfl⟩ : syracuseStep 2219591 = 3329387) B3329387
theorem B3745865 : Blo 1478559 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B1479727 : Blo 1478559 1479727 := bstep (se 1 (by rfl) ⟨1109795, by rfl⟩ : syracuseStep 1479727 = 2219591) B2219591
theorem B12647663 : Blo 1478559 12647663 := bstep (se 1 (by rfl) ⟨9485747, by rfl⟩ : syracuseStep 12647663 = 18971495) B18971495
theorem B8431775 : Blo 1478559 8431775 := bstep (se 1 (by rfl) ⟨6323831, by rfl⟩ : syracuseStep 8431775 = 12647663) B12647663
theorem B2497243 : Blo 1478559 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B5621183 : Blo 1478559 5621183 := bstep (se 1 (by rfl) ⟨4215887, by rfl⟩ : syracuseStep 5621183 = 8431775) B8431775
theorem B3329657 : Blo 1478559 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B3747455 : Blo 1478559 3747455 := bstep (se 1 (by rfl) ⟨2810591, by rfl⟩ : syracuseStep 3747455 = 5621183) B5621183
theorem B2219771 : Blo 1478559 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B1479847 : Blo 1478559 1479847 := bstep (se 1 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 1479847 = 2219771) B2219771
theorem B2498303 : Blo 1478559 2498303 := bstep (se 1 (by rfl) ⟨1873727, by rfl⟩ : syracuseStep 2498303 = 3747455) B3747455
theorem B1665535 : Blo 1478559 1665535 := bstep (se 1 (by rfl) ⟨1249151, by rfl⟩ : syracuseStep 1665535 = 2498303) B2498303
theorem B2220713 : Blo 1478559 2220713 := bstep (se 2 (by rfl) ⟨832767, by rfl⟩ : syracuseStep 2220713 = 1665535) B1665535
theorem B1480475 : Blo 1478559 1480475 := bstep (se 1 (by rfl) ⟨1110356, by rfl⟩ : syracuseStep 1480475 = 2220713) B2220713

theorem C0 (j : ℕ) (h1 : 369639 ≤ j) (h2 : j ≤ 370139) : Blo 1478559 (4 * j + 3) := by
  interval_cases j
  · exact B1478559
  · exact B1478563
  · exact B1478567
  · exact B1478571
  · exact B1478575
  · exact B1478579
  · exact B1478583
  · exact B1478587
  · exact B1478591
  · exact B1478595
  · exact B1478599
  · exact B1478603
  · exact B1478607
  · exact B1478611
  · exact B1478615
  · exact B1478619
  · exact B1478623
  · exact B1478627
  · exact B1478631
  · exact B1478635
  · exact B1478639
  · exact B1478643
  · exact B1478647
  · exact B1478651
  · exact B1478655
  · exact B1478659
  · exact B1478663
  · exact B1478667
  · exact B1478671
  · exact B1478675
  · exact B1478679
  · exact B1478683
  · exact B1478687
  · exact B1478691
  · exact B1478695
  · exact B1478699
  · exact B1478703
  · exact B1478707
  · exact B1478711
  · exact B1478715
  · exact B1478719
  · exact B1478723
  · exact B1478727
  · exact B1478731
  · exact B1478735
  · exact B1478739
  · exact B1478743
  · exact B1478747
  · exact B1478751
  · exact B1478755
  · exact B1478759
  · exact B1478763
  · exact B1478767
  · exact B1478771
  · exact B1478775
  · exact B1478779
  · exact B1478783
  · exact B1478787
  · exact B1478791
  · exact B1478795
  · exact B1478799
  · exact B1478803
  · exact B1478807
  · exact B1478811
  · exact B1478815
  · exact B1478819
  · exact B1478823
  · exact B1478827
  · exact B1478831
  · exact B1478835
  · exact B1478839
  · exact B1478843
  · exact B1478847
  · exact B1478851
  · exact B1478855
  · exact B1478859
  · exact B1478863
  · exact B1478867
  · exact B1478871
  · exact B1478875
  · exact B1478879
  · exact B1478883
  · exact B1478887
  · exact B1478891
  · exact B1478895
  · exact B1478899
  · exact B1478903
  · exact B1478907
  · exact B1478911
  · exact B1478915
  · exact B1478919
  · exact B1478923
  · exact B1478927
  · exact B1478931
  · exact B1478935
  · exact B1478939
  · exact B1478943
  · exact B1478947
  · exact B1478951
  · exact B1478955
  · exact B1478959
  · exact B1478963
  · exact B1478967
  · exact B1478971
  · exact B1478975
  · exact B1478979
  · exact B1478983
  · exact B1478987
  · exact B1478991
  · exact B1478995
  · exact B1478999
  · exact B1479003
  · exact B1479007
  · exact B1479011
  · exact B1479015
  · exact B1479019
  · exact B1479023
  · exact B1479027
  · exact B1479031
  · exact B1479035
  · exact B1479039
  · exact B1479043
  · exact B1479047
  · exact B1479051
  · exact B1479055
  · exact B1479059
  · exact B1479063
  · exact B1479067
  · exact B1479071
  · exact B1479075
  · exact B1479079
  · exact B1479083
  · exact B1479087
  · exact B1479091
  · exact B1479095
  · exact B1479099
  · exact B1479103
  · exact B1479107
  · exact B1479111
  · exact B1479115
  · exact B1479119
  · exact B1479123
  · exact B1479127
  · exact B1479131
  · exact B1479135
  · exact B1479139
  · exact B1479143
  · exact B1479147
  · exact B1479151
  · exact B1479155
  · exact B1479159
  · exact B1479163
  · exact B1479167
  · exact B1479171
  · exact B1479175
  · exact B1479179
  · exact B1479183
  · exact B1479187
  · exact B1479191
  · exact B1479195
  · exact B1479199
  · exact B1479203
  · exact B1479207
  · exact B1479211
  · exact B1479215
  · exact B1479219
  · exact B1479223
  · exact B1479227
  · exact B1479231
  · exact B1479235
  · exact B1479239
  · exact B1479243
  · exact B1479247
  · exact B1479251
  · exact B1479255
  · exact B1479259
  · exact B1479263
  · exact B1479267
  · exact B1479271
  · exact B1479275
  · exact B1479279
  · exact B1479283
  · exact B1479287
  · exact B1479291
  · exact B1479295
  · exact B1479299
  · exact B1479303
  · exact B1479307
  · exact B1479311
  · exact B1479315
  · exact B1479319
  · exact B1479323
  · exact B1479327
  · exact B1479331
  · exact B1479335
  · exact B1479339
  · exact B1479343
  · exact B1479347
  · exact B1479351
  · exact B1479355
  · exact B1479359
  · exact B1479363
  · exact B1479367
  · exact B1479371
  · exact B1479375
  · exact B1479379
  · exact B1479383
  · exact B1479387
  · exact B1479391
  · exact B1479395
  · exact B1479399
  · exact B1479403
  · exact B1479407
  · exact B1479411
  · exact B1479415
  · exact B1479419
  · exact B1479423
  · exact B1479427
  · exact B1479431
  · exact B1479435
  · exact B1479439
  · exact B1479443
  · exact B1479447
  · exact B1479451
  · exact B1479455
  · exact B1479459
  · exact B1479463
  · exact B1479467
  · exact B1479471
  · exact B1479475
  · exact B1479479
  · exact B1479483
  · exact B1479487
  · exact B1479491
  · exact B1479495
  · exact B1479499
  · exact B1479503
  · exact B1479507
  · exact B1479511
  · exact B1479515
  · exact B1479519
  · exact B1479523
  · exact B1479527
  · exact B1479531
  · exact B1479535
  · exact B1479539
  · exact B1479543
  · exact B1479547
  · exact B1479551
  · exact B1479555
  · exact B1479559
  · exact B1479563
  · exact B1479567
  · exact B1479571
  · exact B1479575
  · exact B1479579
  · exact B1479583
  · exact B1479587
  · exact B1479591
  · exact B1479595
  · exact B1479599
  · exact B1479603
  · exact B1479607
  · exact B1479611
  · exact B1479615
  · exact B1479619
  · exact B1479623
  · exact B1479627
  · exact B1479631
  · exact B1479635
  · exact B1479639
  · exact B1479643
  · exact B1479647
  · exact B1479651
  · exact B1479655
  · exact B1479659
  · exact B1479663
  · exact B1479667
  · exact B1479671
  · exact B1479675
  · exact B1479679
  · exact B1479683
  · exact B1479687
  · exact B1479691
  · exact B1479695
  · exact B1479699
  · exact B1479703
  · exact B1479707
  · exact B1479711
  · exact B1479715
  · exact B1479719
  · exact B1479723
  · exact B1479727
  · exact B1479731
  · exact B1479735
  · exact B1479739
  · exact B1479743
  · exact B1479747
  · exact B1479751
  · exact B1479755
  · exact B1479759
  · exact B1479763
  · exact B1479767
  · exact B1479771
  · exact B1479775
  · exact B1479779
  · exact B1479783
  · exact B1479787
  · exact B1479791
  · exact B1479795
  · exact B1479799
  · exact B1479803
  · exact B1479807
  · exact B1479811
  · exact B1479815
  · exact B1479819
  · exact B1479823
  · exact B1479827
  · exact B1479831
  · exact B1479835
  · exact B1479839
  · exact B1479843
  · exact B1479847
  · exact B1479851
  · exact B1479855
  · exact B1479859
  · exact B1479863
  · exact B1479867
  · exact B1479871
  · exact B1479875
  · exact B1479879
  · exact B1479883
  · exact B1479887
  · exact B1479891
  · exact B1479895
  · exact B1479899
  · exact B1479903
  · exact B1479907
  · exact B1479911
  · exact B1479915
  · exact B1479919
  · exact B1479923
  · exact B1479927
  · exact B1479931
  · exact B1479935
  · exact B1479939
  · exact B1479943
  · exact B1479947
  · exact B1479951
  · exact B1479955
  · exact B1479959
  · exact B1479963
  · exact B1479967
  · exact B1479971
  · exact B1479975
  · exact B1479979
  · exact B1479983
  · exact B1479987
  · exact B1479991
  · exact B1479995
  · exact B1479999
  · exact B1480003
  · exact B1480007
  · exact B1480011
  · exact B1480015
  · exact B1480019
  · exact B1480023
  · exact B1480027
  · exact B1480031
  · exact B1480035
  · exact B1480039
  · exact B1480043
  · exact B1480047
  · exact B1480051
  · exact B1480055
  · exact B1480059
  · exact B1480063
  · exact B1480067
  · exact B1480071
  · exact B1480075
  · exact B1480079
  · exact B1480083
  · exact B1480087
  · exact B1480091
  · exact B1480095
  · exact B1480099
  · exact B1480103
  · exact B1480107
  · exact B1480111
  · exact B1480115
  · exact B1480119
  · exact B1480123
  · exact B1480127
  · exact B1480131
  · exact B1480135
  · exact B1480139
  · exact B1480143
  · exact B1480147
  · exact B1480151
  · exact B1480155
  · exact B1480159
  · exact B1480163
  · exact B1480167
  · exact B1480171
  · exact B1480175
  · exact B1480179
  · exact B1480183
  · exact B1480187
  · exact B1480191
  · exact B1480195
  · exact B1480199
  · exact B1480203
  · exact B1480207
  · exact B1480211
  · exact B1480215
  · exact B1480219
  · exact B1480223
  · exact B1480227
  · exact B1480231
  · exact B1480235
  · exact B1480239
  · exact B1480243
  · exact B1480247
  · exact B1480251
  · exact B1480255
  · exact B1480259
  · exact B1480263
  · exact B1480267
  · exact B1480271
  · exact B1480275
  · exact B1480279
  · exact B1480283
  · exact B1480287
  · exact B1480291
  · exact B1480295
  · exact B1480299
  · exact B1480303
  · exact B1480307
  · exact B1480311
  · exact B1480315
  · exact B1480319
  · exact B1480323
  · exact B1480327
  · exact B1480331
  · exact B1480335
  · exact B1480339
  · exact B1480343
  · exact B1480347
  · exact B1480351
  · exact B1480355
  · exact B1480359
  · exact B1480363
  · exact B1480367
  · exact B1480371
  · exact B1480375
  · exact B1480379
  · exact B1480383
  · exact B1480387
  · exact B1480391
  · exact B1480395
  · exact B1480399
  · exact B1480403
  · exact B1480407
  · exact B1480411
  · exact B1480415
  · exact B1480419
  · exact B1480423
  · exact B1480427
  · exact B1480431
  · exact B1480435
  · exact B1480439
  · exact B1480443
  · exact B1480447
  · exact B1480451
  · exact B1480455
  · exact B1480459
  · exact B1480463
  · exact B1480467
  · exact B1480471
  · exact B1480475
  · exact B1480479
  · exact B1480483
  · exact B1480487
  · exact B1480491
  · exact B1480495
  · exact B1480499
  · exact B1480503
  · exact B1480507
  · exact B1480511
  · exact B1480515
  · exact B1480519
  · exact B1480523
  · exact B1480527
  · exact B1480531
  · exact B1480535
  · exact B1480539
  · exact B1480543
  · exact B1480547
  · exact B1480551
  · exact B1480555
  · exact B1480559

theorem solution (m : ℕ) (hlo : 1478559 ≤ m) (hhi : m ≤ 1480559) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 369639 ≤ j := by omega
    have hj2 : j ≤ 370139 := by omega
    have hb : Blo 1478559 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
