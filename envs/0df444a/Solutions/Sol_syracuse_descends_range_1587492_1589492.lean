-- Prove2me | solution 1 for syracuse_descends_range_1587492_1589492
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:08:27.692697+00:00
-- url     : https://prove2.me/submissions/8ab774ec-8c2f-4d39-b0f2-9ac2f94e1ce4

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


theorem B2383877 : Blo 1587492 2383877 := bbase (se 4 (by rfl) ⟨223488, by rfl⟩ : syracuseStep 2383877 = 446977) (by norm_num)
theorem B2383901 : Blo 1587492 2383901 := bbase (se 3 (by rfl) ⟨446981, by rfl⟩ : syracuseStep 2383901 = 893963) (by norm_num)
theorem B2383925 : Blo 1587492 2383925 := bbase (se 5 (by rfl) ⟨111746, by rfl⟩ : syracuseStep 2383925 = 223493) (by norm_num)
theorem B5161013 : Blo 1587492 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B2383949 : Blo 1587492 2383949 := bbase (se 3 (by rfl) ⟨446990, by rfl⟩ : syracuseStep 2383949 = 893981) (by norm_num)
theorem B1785937 : Blo 1587492 1785937 := bbase (se 2 (by rfl) ⟨669726, by rfl⟩ : syracuseStep 1785937 = 1339453) (by norm_num)
theorem B3014749 : Blo 1587492 3014749 := bbase (se 3 (by rfl) ⟨565265, by rfl⟩ : syracuseStep 3014749 = 1130531) (by norm_num)
theorem B2383973 : Blo 1587492 2383973 := bbase (se 4 (by rfl) ⟨223497, by rfl⟩ : syracuseStep 2383973 = 446995) (by norm_num)
theorem B1785973 : Blo 1587492 1785973 := bbase (se 5 (by rfl) ⟨83717, by rfl⟩ : syracuseStep 1785973 = 167435) (by norm_num)
theorem B1695865 : Blo 1587492 1695865 := bbase (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) (by norm_num)
theorem B2383997 : Blo 1587492 2383997 := bbase (se 3 (by rfl) ⟨446999, by rfl⟩ : syracuseStep 2383997 = 893999) (by norm_num)
theorem B2261125 : Blo 1587492 2261125 := bbase (se 4 (by rfl) ⟨211980, by rfl⟩ : syracuseStep 2261125 = 423961) (by norm_num)
theorem B2678933 : Blo 1587492 2678933 := bbase (se 6 (by rfl) ⟨62787, by rfl⟩ : syracuseStep 2678933 = 125575) (by norm_num)
theorem B2384021 : Blo 1587492 2384021 := bbase (se 6 (by rfl) ⟨55875, by rfl⟩ : syracuseStep 2384021 = 111751) (by norm_num)
theorem B1786009 : Blo 1587492 1786009 := bbase (se 2 (by rfl) ⟨669753, by rfl⟩ : syracuseStep 1786009 = 1339507) (by norm_num)
theorem B3391645 : Blo 1587492 3391645 := bbase (se 3 (by rfl) ⟨635933, by rfl⟩ : syracuseStep 3391645 = 1271867) (by norm_num)
theorem B2384045 : Blo 1587492 2384045 := bbase (se 3 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 2384045 = 894017) (by norm_num)
theorem B1695925 : Blo 1587492 1695925 := bbase (se 5 (by rfl) ⟨79496, by rfl⟩ : syracuseStep 1695925 = 158993) (by norm_num)
theorem B3571901 : Blo 1587492 3571901 := bbase (se 3 (by rfl) ⟨669731, by rfl⟩ : syracuseStep 3571901 = 1339463) (by norm_num)
theorem B1786045 : Blo 1587492 1786045 := bbase (se 3 (by rfl) ⟨334883, by rfl⟩ : syracuseStep 1786045 = 669767) (by norm_num)
theorem B5505221 : Blo 1587492 5505221 := bbase (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) (by norm_num)
theorem B3866821 : Blo 1587492 3866821 := bbase (se 4 (by rfl) ⟨362514, by rfl⟩ : syracuseStep 3866821 = 725029) (by norm_num)
theorem B2384069 : Blo 1587492 2384069 := bbase (se 4 (by rfl) ⟨223506, by rfl⟩ : syracuseStep 2384069 = 447013) (by norm_num)
theorem B8044757 : Blo 1587492 8044757 := bbase (se 7 (by rfl) ⟨94274, by rfl⟩ : syracuseStep 8044757 = 188549) (by norm_num)
theorem B2384093 : Blo 1587492 2384093 := bbase (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) (by norm_num)
theorem B1786081 : Blo 1587492 1786081 := bbase (se 2 (by rfl) ⟨669780, by rfl⟩ : syracuseStep 1786081 = 1339561) (by norm_num)
theorem B2384117 : Blo 1587492 2384117 := bbase (se 5 (by rfl) ⟨111755, by rfl⟩ : syracuseStep 2384117 = 223511) (by norm_num)
theorem B3571973 : Blo 1587492 3571973 := bbase (se 4 (by rfl) ⟨334872, by rfl⟩ : syracuseStep 3571973 = 669745) (by norm_num)
theorem B1786117 : Blo 1587492 1786117 := bbase (se 4 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 1786117 = 334897) (by norm_num)
theorem B2384141 : Blo 1587492 2384141 := bbase (se 3 (by rfl) ⟨447026, by rfl⟩ : syracuseStep 2384141 = 894053) (by norm_num)
theorem B2679061 : Blo 1587492 2679061 := bbase (se 6 (by rfl) ⟨62790, by rfl⟩ : syracuseStep 2679061 = 125581) (by norm_num)
theorem B5726485 : Blo 1587492 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B1909021 : Blo 1587492 1909021 := bbase (se 3 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 1909021 = 715883) (by norm_num)
theorem B2384165 : Blo 1587492 2384165 := bbase (se 4 (by rfl) ⟨223515, by rfl⟩ : syracuseStep 2384165 = 447031) (by norm_num)
theorem B1786153 : Blo 1587492 1786153 := bbase (se 2 (by rfl) ⟨669807, by rfl⟩ : syracuseStep 1786153 = 1339615) (by norm_num)
theorem B4022581 : Blo 1587492 4022581 := bbase (se 5 (by rfl) ⟨188558, by rfl⟩ : syracuseStep 4022581 = 377117) (by norm_num)
theorem B2384189 : Blo 1587492 2384189 := bbase (se 3 (by rfl) ⟨447035, by rfl⟩ : syracuseStep 2384189 = 894071) (by norm_num)
theorem B3572045 : Blo 1587492 3572045 := bbase (se 3 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 3572045 = 1339517) (by norm_num)
theorem B1786189 : Blo 1587492 1786189 := bbase (se 3 (by rfl) ⟨334910, by rfl⟩ : syracuseStep 1786189 = 669821) (by norm_num)
theorem B1810765 : Blo 1587492 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B2384213 : Blo 1587492 2384213 := bbase (se 10 (by rfl) ⟨3492, by rfl⟩ : syracuseStep 2384213 = 6985) (by norm_num)
theorem B2679149 : Blo 1587492 2679149 := bbase (se 3 (by rfl) ⟨502340, by rfl⟩ : syracuseStep 2679149 = 1004681) (by norm_num)
theorem B2384237 : Blo 1587492 2384237 := bbase (se 3 (by rfl) ⟨447044, by rfl⟩ : syracuseStep 2384237 = 894089) (by norm_num)
theorem B1786225 : Blo 1587492 1786225 := bbase (se 2 (by rfl) ⟨669834, by rfl⟩ : syracuseStep 1786225 = 1339669) (by norm_num)
theorem B3015053 : Blo 1587492 3015053 := bbase (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) (by norm_num)
theorem B3572117 : Blo 1587492 3572117 := bbase (se 6 (by rfl) ⟨83721, by rfl⟩ : syracuseStep 3572117 = 167443) (by norm_num)
theorem B1786261 : Blo 1587492 1786261 := bbase (se 6 (by rfl) ⟨41865, by rfl⟩ : syracuseStep 1786261 = 83731) (by norm_num)
theorem B4022693 : Blo 1587492 4022693 := bbase (se 4 (by rfl) ⟨377127, by rfl⟩ : syracuseStep 4022693 = 754255) (by norm_num)
theorem B1786297 : Blo 1587492 1786297 := bbase (se 2 (by rfl) ⟨669861, by rfl⟩ : syracuseStep 1786297 = 1339723) (by norm_num)
theorem B2261461 : Blo 1587492 2261461 := bbase (se 7 (by rfl) ⟨26501, by rfl⟩ : syracuseStep 2261461 = 53003) (by norm_num)
theorem B3572189 : Blo 1587492 3572189 := bbase (se 3 (by rfl) ⟨669785, by rfl⟩ : syracuseStep 3572189 = 1339571) (by norm_num)
theorem B1786333 : Blo 1587492 1786333 := bbase (se 3 (by rfl) ⟨334937, by rfl⟩ : syracuseStep 1786333 = 669875) (by norm_num)
theorem B2679277 : Blo 1587492 2679277 := bbase (se 3 (by rfl) ⟨502364, by rfl⟩ : syracuseStep 2679277 = 1004729) (by norm_num)
theorem B1696241 : Blo 1587492 1696241 := bbase (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) (by norm_num)
theorem B1786369 : Blo 1587492 1786369 := bbase (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) (by norm_num)
theorem B4293125 : Blo 1587492 4293125 := bbase (se 4 (by rfl) ⟨402480, by rfl⟩ : syracuseStep 4293125 = 804961) (by norm_num)
theorem B6439445 : Blo 1587492 6439445 := bbase (se 6 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 6439445 = 301849) (by norm_num)
theorem B3219997 : Blo 1587492 3219997 := bbase (se 3 (by rfl) ⟨603749, by rfl⟩ : syracuseStep 3219997 = 1207499) (by norm_num)
theorem B3572261 : Blo 1587492 3572261 := bbase (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) (by norm_num)
theorem B3867173 : Blo 1587492 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1786405 : Blo 1587492 1786405 := bbase (se 4 (by rfl) ⟨167475, by rfl⟩ : syracuseStep 1786405 = 334951) (by norm_num)
theorem B5358149 : Blo 1587492 5358149 := bbase (se 4 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 5358149 = 1004653) (by norm_num)
theorem B2679365 : Blo 1587492 2679365 := bbase (se 4 (by rfl) ⟨251190, by rfl⟩ : syracuseStep 2679365 = 502381) (by norm_num)
theorem B1786441 : Blo 1587492 1786441 := bbase (se 2 (by rfl) ⟨669915, by rfl⟩ : syracuseStep 1786441 = 1339831) (by norm_num)
theorem B6029909 : Blo 1587492 6029909 := bbase (se 8 (by rfl) ⟨35331, by rfl⟩ : syracuseStep 6029909 = 70663) (by norm_num)
theorem B12231253 : Blo 1587492 12231253 := bbase (se 8 (by rfl) ⟨71667, by rfl⟩ : syracuseStep 12231253 = 143335) (by norm_num)
theorem B2482781 : Blo 1587492 2482781 := bbase (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) (by norm_num)
theorem B4022885 : Blo 1587492 4022885 := bbase (se 4 (by rfl) ⟨377145, by rfl⟩ : syracuseStep 4022885 = 754291) (by norm_num)
theorem B3572333 : Blo 1587492 3572333 := bbase (se 3 (by rfl) ⟨669812, by rfl⟩ : syracuseStep 3572333 = 1339625) (by norm_num)
theorem B1786477 : Blo 1587492 1786477 := bbase (se 3 (by rfl) ⟨334964, by rfl⟩ : syracuseStep 1786477 = 669929) (by norm_num)
theorem B8036981 : Blo 1587492 8036981 := bbase (se 5 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 8036981 = 753467) (by norm_num)
theorem B1786513 : Blo 1587492 1786513 := bbase (se 2 (by rfl) ⟨669942, by rfl⟩ : syracuseStep 1786513 = 1339885) (by norm_num)
theorem B1909405 : Blo 1587492 1909405 := bbase (se 3 (by rfl) ⟨358013, by rfl⟩ : syracuseStep 1909405 = 716027) (by norm_num)
theorem B2261677 : Blo 1587492 2261677 := bbase (se 3 (by rfl) ⟨424064, by rfl⟩ : syracuseStep 2261677 = 848129) (by norm_num)
theorem B3572405 : Blo 1587492 3572405 := bbase (se 5 (by rfl) ⟨167456, by rfl⟩ : syracuseStep 3572405 = 334913) (by norm_num)
theorem B1786549 : Blo 1587492 1786549 := bbase (se 5 (by rfl) ⟨83744, by rfl⟩ : syracuseStep 1786549 = 167489) (by norm_num)
theorem B2679493 : Blo 1587492 2679493 := bbase (se 4 (by rfl) ⟨251202, by rfl⟩ : syracuseStep 2679493 = 502405) (by norm_num)
theorem B1786585 : Blo 1587492 1786585 := bbase (se 2 (by rfl) ⟨669969, by rfl⟩ : syracuseStep 1786585 = 1339939) (by norm_num)
theorem B3572477 : Blo 1587492 3572477 := bbase (se 3 (by rfl) ⟨669839, by rfl⟩ : syracuseStep 3572477 = 1339679) (by norm_num)
theorem B1786621 : Blo 1587492 1786621 := bbase (se 3 (by rfl) ⟨334991, by rfl⟩ : syracuseStep 1786621 = 669983) (by norm_num)
theorem B5088005 : Blo 1587492 5088005 := bbase (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) (by norm_num)
theorem B2679581 : Blo 1587492 2679581 := bbase (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) (by norm_num)
theorem B1786657 : Blo 1587492 1786657 := bbase (se 2 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 1786657 = 1339993) (by norm_num)
theorem B3572549 : Blo 1587492 3572549 := bbase (se 4 (by rfl) ⟨334926, by rfl⟩ : syracuseStep 3572549 = 669853) (by norm_num)
theorem B1786693 : Blo 1587492 1786693 := bbase (se 4 (by rfl) ⟨167502, by rfl⟩ : syracuseStep 1786693 = 335005) (by norm_num)
theorem B4522853 : Blo 1587492 4522853 := bbase (se 4 (by rfl) ⟨424017, by rfl⟩ : syracuseStep 4522853 = 848035) (by norm_num)
theorem B1786729 : Blo 1587492 1786729 := bbase (se 2 (by rfl) ⟨670023, by rfl⟩ : syracuseStep 1786729 = 1340047) (by norm_num)
theorem B6030197 : Blo 1587492 6030197 := bbase (se 5 (by rfl) ⟨282665, by rfl⟩ : syracuseStep 6030197 = 565331) (by norm_num)
theorem B4350853 : Blo 1587492 4350853 := bbase (se 4 (by rfl) ⟨407892, by rfl⟩ : syracuseStep 4350853 = 815785) (by norm_num)
theorem B3572621 : Blo 1587492 3572621 := bbase (se 3 (by rfl) ⟨669866, by rfl⟩ : syracuseStep 3572621 = 1339733) (by norm_num)
theorem B1786765 : Blo 1587492 1786765 := bbase (se 3 (by rfl) ⟨335018, by rfl⟩ : syracuseStep 1786765 = 670037) (by norm_num)
theorem B9044885 : Blo 1587492 9044885 := bbase (se 6 (by rfl) ⟨211989, by rfl⟩ : syracuseStep 9044885 = 423979) (by norm_num)
theorem B2679709 : Blo 1587492 2679709 := bbase (se 3 (by rfl) ⟨502445, by rfl⟩ : syracuseStep 2679709 = 1004891) (by norm_num)
theorem B1696685 : Blo 1587492 1696685 := bbase (se 3 (by rfl) ⟨318128, by rfl⟩ : syracuseStep 1696685 = 636257) (by norm_num)
theorem B1786801 : Blo 1587492 1786801 := bbase (se 2 (by rfl) ⟨670050, by rfl⟩ : syracuseStep 1786801 = 1340101) (by norm_num)
theorem B4023229 : Blo 1587492 4023229 := bbase (se 3 (by rfl) ⟨754355, by rfl⟩ : syracuseStep 4023229 = 1508711) (by norm_num)
theorem B3572693 : Blo 1587492 3572693 := bbase (se 7 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 3572693 = 83735) (by norm_num)
theorem B1786837 : Blo 1587492 1786837 := bbase (se 7 (by rfl) ⟨20939, by rfl⟩ : syracuseStep 1786837 = 41879) (by norm_num)
theorem B1696745 : Blo 1587492 1696745 := bbase (se 2 (by rfl) ⟨636279, by rfl⟩ : syracuseStep 1696745 = 1272559) (by norm_num)
theorem B5358581 : Blo 1587492 5358581 := bbase (se 5 (by rfl) ⟨251183, by rfl⟩ : syracuseStep 5358581 = 502367) (by norm_num)
theorem B2679797 : Blo 1587492 2679797 := bbase (se 5 (by rfl) ⟨125615, by rfl⟩ : syracuseStep 2679797 = 251231) (by norm_num)
theorem B1786873 : Blo 1587492 1786873 := bbase (se 2 (by rfl) ⟨670077, by rfl⟩ : syracuseStep 1786873 = 1340155) (by norm_num)
theorem B3392533 : Blo 1587492 3392533 := bbase (se 6 (by rfl) ⟨79512, by rfl⟩ : syracuseStep 3392533 = 159025) (by norm_num)
theorem B1811477 : Blo 1587492 1811477 := bbase (se 6 (by rfl) ⟨42456, by rfl⟩ : syracuseStep 1811477 = 84913) (by norm_num)
theorem B3572765 : Blo 1587492 3572765 := bbase (se 3 (by rfl) ⟨669893, by rfl⟩ : syracuseStep 3572765 = 1339787) (by norm_num)
theorem B1786909 : Blo 1587492 1786909 := bbase (se 3 (by rfl) ⟨335045, by rfl⟩ : syracuseStep 1786909 = 670091) (by norm_num)
theorem B2147357 : Blo 1587492 2147357 := bbase (se 3 (by rfl) ⟨402629, by rfl⟩ : syracuseStep 2147357 = 805259) (by norm_num)
theorem B2262053 : Blo 1587492 2262053 := bbase (se 4 (by rfl) ⟨212067, by rfl⟩ : syracuseStep 2262053 = 424135) (by norm_num)
theorem B4023341 : Blo 1587492 4023341 := bbase (se 3 (by rfl) ⟨754376, by rfl⟩ : syracuseStep 4023341 = 1508753) (by norm_num)
theorem B1786945 : Blo 1587492 1786945 := bbase (se 2 (by rfl) ⟨670104, by rfl⟩ : syracuseStep 1786945 = 1340209) (by norm_num)
theorem B3572837 : Blo 1587492 3572837 := bbase (se 4 (by rfl) ⟨334953, by rfl⟩ : syracuseStep 3572837 = 669907) (by norm_num)
theorem B1786981 : Blo 1587492 1786981 := bbase (se 4 (by rfl) ⟨167529, by rfl⟩ : syracuseStep 1786981 = 335059) (by norm_num)
theorem B1696873 : Blo 1587492 1696873 := bbase (se 2 (by rfl) ⟨636327, by rfl⟩ : syracuseStep 1696873 = 1272655) (by norm_num)
theorem B2679925 : Blo 1587492 2679925 := bbase (se 5 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 2679925 = 251243) (by norm_num)
theorem B3671165 : Blo 1587492 3671165 := bbase (se 3 (by rfl) ⟨688343, by rfl⟩ : syracuseStep 3671165 = 1376687) (by norm_num)
theorem B3015805 : Blo 1587492 3015805 := bbase (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) (by norm_num)
theorem B1787017 : Blo 1587492 1787017 := bbase (se 2 (by rfl) ⟨670131, by rfl⟩ : syracuseStep 1787017 = 1340263) (by norm_num)
theorem B3572909 : Blo 1587492 3572909 := bbase (se 3 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 3572909 = 1339841) (by norm_num)
theorem B1787053 : Blo 1587492 1787053 := bbase (se 3 (by rfl) ⟨335072, by rfl⟩ : syracuseStep 1787053 = 670145) (by norm_num)
theorem B3818677 : Blo 1587492 3818677 := bbase (se 5 (by rfl) ⟨179000, by rfl⟩ : syracuseStep 3818677 = 358001) (by norm_num)
theorem B1811641 : Blo 1587492 1811641 := bbase (se 2 (by rfl) ⟨679365, by rfl⟩ : syracuseStep 1811641 = 1358731) (by norm_num)
theorem B2680013 : Blo 1587492 2680013 := bbase (se 3 (by rfl) ⟨502502, by rfl⟩ : syracuseStep 2680013 = 1005005) (by norm_num)
theorem B1787089 : Blo 1587492 1787089 := bbase (se 2 (by rfl) ⟨670158, by rfl⟩ : syracuseStep 1787089 = 1340317) (by norm_num)
theorem B10175701 : Blo 1587492 10175701 := bbase (se 7 (by rfl) ⟨119246, by rfl⟩ : syracuseStep 10175701 = 238493) (by norm_num)
theorem B3572981 : Blo 1587492 3572981 := bbase (se 5 (by rfl) ⟨167483, by rfl⟩ : syracuseStep 3572981 = 334967) (by norm_num)
theorem B1787125 : Blo 1587492 1787125 := bbase (se 5 (by rfl) ⟨83771, by rfl⟩ : syracuseStep 1787125 = 167543) (by norm_num)
theorem B3015949 : Blo 1587492 3015949 := bbase (se 3 (by rfl) ⟨565490, by rfl⟩ : syracuseStep 3015949 = 1130981) (by norm_num)
theorem B1787161 : Blo 1587492 1787161 := bbase (se 2 (by rfl) ⟨670185, by rfl⟩ : syracuseStep 1787161 = 1340371) (by norm_num)
theorem B3573053 : Blo 1587492 3573053 := bbase (se 3 (by rfl) ⟨669947, by rfl⟩ : syracuseStep 3573053 = 1339895) (by norm_num)
theorem B1787197 : Blo 1587492 1787197 := bbase (se 3 (by rfl) ⟨335099, by rfl⟩ : syracuseStep 1787197 = 670199) (by norm_num)
theorem B2680141 : Blo 1587492 2680141 := bbase (se 3 (by rfl) ⟨502526, by rfl⟩ : syracuseStep 2680141 = 1005053) (by norm_num)
theorem B30532949 : Blo 1587492 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B1787233 : Blo 1587492 1787233 := bbase (se 2 (by rfl) ⟨670212, by rfl⟩ : syracuseStep 1787233 = 1340425) (by norm_num)
theorem B3573125 : Blo 1587492 3573125 := bbase (se 4 (by rfl) ⟨334980, by rfl⟩ : syracuseStep 3573125 = 669961) (by norm_num)
theorem B4294021 : Blo 1587492 4294021 := bbase (se 4 (by rfl) ⟨402564, by rfl⟩ : syracuseStep 4294021 = 805129) (by norm_num)
theorem B1787269 : Blo 1587492 1787269 := bbase (se 4 (by rfl) ⟨167556, by rfl⟩ : syracuseStep 1787269 = 335113) (by norm_num)
theorem B5359013 : Blo 1587492 5359013 := bbase (se 4 (by rfl) ⟨502407, by rfl⟩ : syracuseStep 5359013 = 1004815) (by norm_num)
theorem B2680229 : Blo 1587492 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B1787305 : Blo 1587492 1787305 := bbase (se 2 (by rfl) ⟨670239, by rfl⟩ : syracuseStep 1787305 = 1340479) (by norm_num)
theorem B3016109 : Blo 1587492 3016109 := bbase (se 3 (by rfl) ⟨565520, by rfl⟩ : syracuseStep 3016109 = 1131041) (by norm_num)
theorem B3622333 : Blo 1587492 3622333 := bbase (se 3 (by rfl) ⟨679187, by rfl⟩ : syracuseStep 3622333 = 1358375) (by norm_num)
theorem B3573197 : Blo 1587492 3573197 := bbase (se 3 (by rfl) ⟨669974, by rfl⟩ : syracuseStep 3573197 = 1339949) (by norm_num)
theorem B1787341 : Blo 1587492 1787341 := bbase (se 3 (by rfl) ⟨335126, by rfl⟩ : syracuseStep 1787341 = 670253) (by norm_num)
theorem B6784469 : Blo 1587492 6784469 := bbase (se 7 (by rfl) ⟨79505, by rfl⟩ : syracuseStep 6784469 = 159011) (by norm_num)
theorem B8046053 : Blo 1587492 8046053 := bbase (se 4 (by rfl) ⟨754317, by rfl⟩ : syracuseStep 8046053 = 1508635) (by norm_num)
theorem B1787377 : Blo 1587492 1787377 := bbase (se 2 (by rfl) ⟨670266, by rfl⟩ : syracuseStep 1787377 = 1340533) (by norm_num)
theorem B2754037 : Blo 1587492 2754037 := bbase (se 5 (by rfl) ⟨129095, by rfl⟩ : syracuseStep 2754037 = 258191) (by norm_num)
theorem B3393029 : Blo 1587492 3393029 := bbase (se 4 (by rfl) ⟨318096, by rfl⟩ : syracuseStep 3393029 = 636193) (by norm_num)
theorem B3573269 : Blo 1587492 3573269 := bbase (se 6 (by rfl) ⟨83748, by rfl⟩ : syracuseStep 3573269 = 167497) (by norm_num)
theorem B1787413 : Blo 1587492 1787413 := bbase (se 6 (by rfl) ⟨41892, by rfl⟩ : syracuseStep 1787413 = 83785) (by norm_num)
theorem B2680357 : Blo 1587492 2680357 := bbase (se 4 (by rfl) ⟨251283, by rfl⟩ : syracuseStep 2680357 = 502567) (by norm_num)
theorem B1812005 : Blo 1587492 1812005 := bbase (se 4 (by rfl) ⟨169875, by rfl⟩ : syracuseStep 1812005 = 339751) (by norm_num)
theorem B1697317 : Blo 1587492 1697317 := bbase (se 4 (by rfl) ⟨159123, by rfl⟩ : syracuseStep 1697317 = 318247) (by norm_num)
theorem B1787449 : Blo 1587492 1787449 := bbase (se 2 (by rfl) ⟨670293, by rfl⟩ : syracuseStep 1787449 = 1340587) (by norm_num)
theorem B3016253 : Blo 1587492 3016253 := bbase (se 3 (by rfl) ⟨565547, by rfl⟩ : syracuseStep 3016253 = 1131095) (by norm_num)
theorem B3573341 : Blo 1587492 3573341 := bbase (se 3 (by rfl) ⟨670001, by rfl⟩ : syracuseStep 3573341 = 1340003) (by norm_num)
theorem B1787485 : Blo 1587492 1787485 := bbase (se 3 (by rfl) ⟨335153, by rfl⟩ : syracuseStep 1787485 = 670307) (by norm_num)
theorem B2680445 : Blo 1587492 2680445 := bbase (se 3 (by rfl) ⟨502583, by rfl⟩ : syracuseStep 2680445 = 1005167) (by norm_num)
theorem B1787521 : Blo 1587492 1787521 := bbase (se 2 (by rfl) ⟨670320, by rfl⟩ : syracuseStep 1787521 = 1340641) (by norm_num)
theorem B8152709 : Blo 1587492 8152709 := bbase (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) (by norm_num)
theorem B6440597 : Blo 1587492 6440597 := bbase (se 6 (by rfl) ⟨150951, by rfl⟩ : syracuseStep 6440597 = 301903) (by norm_num)
theorem B3573413 : Blo 1587492 3573413 := bbase (se 4 (by rfl) ⟨335007, by rfl⟩ : syracuseStep 3573413 = 670015) (by norm_num)
theorem B1787557 : Blo 1587492 1787557 := bbase (se 4 (by rfl) ⟨167583, by rfl⟩ : syracuseStep 1787557 = 335167) (by norm_num)
theorem B1787593 : Blo 1587492 1787593 := bbase (se 2 (by rfl) ⟨670347, by rfl⟩ : syracuseStep 1787593 = 1340695) (by norm_num)
theorem B3221213 : Blo 1587492 3221213 := bbase (se 3 (by rfl) ⟨603977, by rfl⟩ : syracuseStep 3221213 = 1207955) (by norm_num)
theorem B3573485 : Blo 1587492 3573485 := bbase (se 3 (by rfl) ⟨670028, by rfl⟩ : syracuseStep 3573485 = 1340057) (by norm_num)
theorem B1787629 : Blo 1587492 1787629 := bbase (se 3 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 1787629 = 670361) (by norm_num)
theorem B2680573 : Blo 1587492 2680573 := bbase (se 3 (by rfl) ⟨502607, by rfl⟩ : syracuseStep 2680573 = 1005215) (by norm_num)
theorem B1787665 : Blo 1587492 1787665 := bbase (se 2 (by rfl) ⟨670374, by rfl⟩ : syracuseStep 1787665 = 1340749) (by norm_num)
theorem B4073237 : Blo 1587492 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B28968725 : Blo 1587492 28968725 := bbase (se 6 (by rfl) ⟨678954, by rfl⟩ : syracuseStep 28968725 = 1357909) (by norm_num)
theorem B3573557 : Blo 1587492 3573557 := bbase (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) (by norm_num)
theorem B1787701 : Blo 1587492 1787701 := bbase (se 5 (by rfl) ⟨83798, by rfl⟩ : syracuseStep 1787701 = 167597) (by norm_num)
theorem B5359445 : Blo 1587492 5359445 := bbase (se 9 (by rfl) ⟨15701, by rfl⟩ : syracuseStep 5359445 = 31403) (by norm_num)
theorem B2680661 : Blo 1587492 2680661 := bbase (se 9 (by rfl) ⟨7853, by rfl⟩ : syracuseStep 2680661 = 15707) (by norm_num)
theorem B1787737 : Blo 1587492 1787737 := bbase (se 2 (by rfl) ⟨670401, by rfl⟩ : syracuseStep 1787737 = 1340803) (by norm_num)
theorem B3016541 : Blo 1587492 3016541 := bbase (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) (by norm_num)
theorem B3868517 : Blo 1587492 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B3573629 : Blo 1587492 3573629 := bbase (se 3 (by rfl) ⟨670055, by rfl⟩ : syracuseStep 3573629 = 1340111) (by norm_num)
theorem B1787773 : Blo 1587492 1787773 := bbase (se 3 (by rfl) ⟨335207, by rfl⟩ : syracuseStep 1787773 = 670415) (by norm_num)
theorem B8038277 : Blo 1587492 8038277 := bbase (se 4 (by rfl) ⟨753588, by rfl⟩ : syracuseStep 8038277 = 1507177) (by norm_num)
theorem B1787809 : Blo 1587492 1787809 := bbase (se 2 (by rfl) ⟨670428, by rfl⟩ : syracuseStep 1787809 = 1340857) (by norm_num)
theorem B3573701 : Blo 1587492 3573701 := bbase (se 4 (by rfl) ⟨335034, by rfl⟩ : syracuseStep 3573701 = 670069) (by norm_num)
theorem B1787845 : Blo 1587492 1787845 := bbase (se 4 (by rfl) ⟨167610, by rfl⟩ : syracuseStep 1787845 = 335221) (by norm_num)
theorem B1812425 : Blo 1587492 1812425 := bbase (se 2 (by rfl) ⟨679659, by rfl⟩ : syracuseStep 1812425 = 1359319) (by norm_num)
theorem B2680789 : Blo 1587492 2680789 := bbase (se 7 (by rfl) ⟨31415, by rfl⟩ : syracuseStep 2680789 = 62831) (by norm_num)
theorem B1787881 : Blo 1587492 1787881 := bbase (se 2 (by rfl) ⟨670455, by rfl⟩ : syracuseStep 1787881 = 1340911) (by norm_num)
theorem B15468533 : Blo 1587492 15468533 := bbase (se 5 (by rfl) ⟨725087, by rfl⟩ : syracuseStep 15468533 = 1450175) (by norm_num)
theorem B3016693 : Blo 1587492 3016693 := bbase (se 5 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 3016693 = 282815) (by norm_num)
theorem B3573773 : Blo 1587492 3573773 := bbase (se 3 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 3573773 = 1340165) (by norm_num)
theorem B1787917 : Blo 1587492 1787917 := bbase (se 3 (by rfl) ⟨335234, by rfl⟩ : syracuseStep 1787917 = 670469) (by norm_num)
theorem B6031381 : Blo 1587492 6031381 := bbase (se 6 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 6031381 = 282721) (by norm_num)
theorem B2680877 : Blo 1587492 2680877 := bbase (se 3 (by rfl) ⟨502664, by rfl⟩ : syracuseStep 2680877 = 1005329) (by norm_num)
theorem B1787953 : Blo 1587492 1787953 := bbase (se 2 (by rfl) ⟨670482, by rfl⟩ : syracuseStep 1787953 = 1340965) (by norm_num)
theorem B3672125 : Blo 1587492 3672125 := bbase (se 3 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 3672125 = 1377047) (by norm_num)
theorem B3573845 : Blo 1587492 3573845 := bbase (se 8 (by rfl) ⟨20940, by rfl⟩ : syracuseStep 3573845 = 41881) (by norm_num)
theorem B1787989 : Blo 1587492 1787989 := bbase (se 8 (by rfl) ⟨10476, by rfl⟩ : syracuseStep 1787989 = 20953) (by norm_num)
theorem B1788025 : Blo 1587492 1788025 := bbase (se 2 (by rfl) ⟨670509, by rfl⟩ : syracuseStep 1788025 = 1341019) (by norm_num)
theorem B2009225 : Blo 1587492 2009225 := bbase (se 2 (by rfl) ⟨753459, by rfl⟩ : syracuseStep 2009225 = 1506919) (by norm_num)
theorem B7637141 : Blo 1587492 7637141 := bbase (se 6 (by rfl) ⟨178995, by rfl⟩ : syracuseStep 7637141 = 357991) (by norm_num)
theorem B3573917 : Blo 1587492 3573917 := bbase (se 3 (by rfl) ⟨670109, by rfl⟩ : syracuseStep 3573917 = 1340219) (by norm_num)
theorem B1788061 : Blo 1587492 1788061 := bbase (se 3 (by rfl) ⟨335261, by rfl⟩ : syracuseStep 1788061 = 670523) (by norm_num)
theorem B2681005 : Blo 1587492 2681005 := bbase (se 3 (by rfl) ⟨502688, by rfl⟩ : syracuseStep 2681005 = 1005377) (by norm_num)
theorem B2009281 : Blo 1587492 2009281 := bbase (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) (by norm_num)
theorem B1788097 : Blo 1587492 1788097 := bbase (se 2 (by rfl) ⟨670536, by rfl⟩ : syracuseStep 1788097 = 1341073) (by norm_num)
theorem B3573989 : Blo 1587492 3573989 := bbase (se 4 (by rfl) ⟨335061, by rfl⟩ : syracuseStep 3573989 = 670123) (by norm_num)
theorem B1788133 : Blo 1587492 1788133 := bbase (se 4 (by rfl) ⟨167637, by rfl⟩ : syracuseStep 1788133 = 335275) (by norm_num)
theorem B7637237 : Blo 1587492 7637237 := bbase (se 5 (by rfl) ⟨357995, by rfl⟩ : syracuseStep 7637237 = 715991) (by norm_num)
theorem B5359877 : Blo 1587492 5359877 := bbase (se 4 (by rfl) ⟨502488, by rfl⟩ : syracuseStep 5359877 = 1004977) (by norm_num)
theorem B2681093 : Blo 1587492 2681093 := bbase (se 4 (by rfl) ⟨251352, by rfl⟩ : syracuseStep 2681093 = 502705) (by norm_num)
theorem B1788169 : Blo 1587492 1788169 := bbase (se 2 (by rfl) ⟨670563, by rfl⟩ : syracuseStep 1788169 = 1341127) (by norm_num)
theorem B2009377 : Blo 1587492 2009377 := bbase (se 2 (by rfl) ⟨753516, by rfl⟩ : syracuseStep 2009377 = 1507033) (by norm_num)
theorem B3016997 : Blo 1587492 3016997 := bbase (se 4 (by rfl) ⟨282843, by rfl⟩ : syracuseStep 3016997 = 565687) (by norm_num)
theorem B3574061 : Blo 1587492 3574061 := bbase (se 3 (by rfl) ⟨670136, by rfl⟩ : syracuseStep 3574061 = 1340273) (by norm_num)
theorem B6031685 : Blo 1587492 6031685 := bbase (se 4 (by rfl) ⟨565470, by rfl⟩ : syracuseStep 6031685 = 1130941) (by norm_num)
theorem B3574133 : Blo 1587492 3574133 := bbase (se 5 (by rfl) ⟨167537, by rfl⟩ : syracuseStep 3574133 = 335075) (by norm_num)
theorem B2902397 : Blo 1587492 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B3393917 : Blo 1587492 3393917 := bbase (se 3 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 3393917 = 1272719) (by norm_num)
theorem B2681221 : Blo 1587492 2681221 := bbase (se 4 (by rfl) ⟨251364, by rfl⟩ : syracuseStep 2681221 = 502729) (by norm_num)
theorem B4524437 : Blo 1587492 4524437 := bbase (se 6 (by rfl) ⟨106041, by rfl⟩ : syracuseStep 4524437 = 212083) (by norm_num)
theorem B3574205 : Blo 1587492 3574205 := bbase (se 3 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 3574205 = 1340327) (by norm_num)
theorem B6785477 : Blo 1587492 6785477 := bbase (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) (by norm_num)
theorem B2009549 : Blo 1587492 2009549 := bbase (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) (by norm_num)
theorem B2681309 : Blo 1587492 2681309 := bbase (se 3 (by rfl) ⟨502745, by rfl⟩ : syracuseStep 2681309 = 1005491) (by norm_num)
theorem B3394037 : Blo 1587492 3394037 := bbase (se 5 (by rfl) ⟨159095, by rfl⟩ : syracuseStep 3394037 = 318191) (by norm_num)
theorem B2009605 : Blo 1587492 2009605 := bbase (se 4 (by rfl) ⟨188400, by rfl⟩ : syracuseStep 2009605 = 376801) (by norm_num)
theorem B3574277 : Blo 1587492 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B2066965 : Blo 1587492 2066965 := bbase (se 6 (by rfl) ⟨48444, by rfl⟩ : syracuseStep 2066965 = 96889) (by norm_num)
theorem B3574349 : Blo 1587492 3574349 := bbase (se 3 (by rfl) ⟨670190, by rfl⟩ : syracuseStep 3574349 = 1340381) (by norm_num)
theorem B3623501 : Blo 1587492 3623501 := bbase (se 3 (by rfl) ⟨679406, by rfl⟩ : syracuseStep 3623501 = 1358813) (by norm_num)
theorem B2681437 : Blo 1587492 2681437 := bbase (se 3 (by rfl) ⟨502769, by rfl⟩ : syracuseStep 2681437 = 1005539) (by norm_num)
theorem B2009701 : Blo 1587492 2009701 := bbase (se 4 (by rfl) ⟨188409, by rfl⟩ : syracuseStep 2009701 = 376819) (by norm_num)
theorem B3574421 : Blo 1587492 3574421 := bbase (se 6 (by rfl) ⟨83775, by rfl⟩ : syracuseStep 3574421 = 167551) (by norm_num)
theorem B5360309 : Blo 1587492 5360309 := bbase (se 5 (by rfl) ⟨251264, by rfl⟩ : syracuseStep 5360309 = 502529) (by norm_num)
theorem B2681525 : Blo 1587492 2681525 := bbase (se 5 (by rfl) ⟨125696, by rfl⟩ : syracuseStep 2681525 = 251393) (by norm_num)
theorem B3574493 : Blo 1587492 3574493 := bbase (se 3 (by rfl) ⟨670217, by rfl⟩ : syracuseStep 3574493 = 1340435) (by norm_num)
theorem B2009873 : Blo 1587492 2009873 := bbase (se 2 (by rfl) ⟨753702, by rfl⟩ : syracuseStep 2009873 = 1507405) (by norm_num)
theorem B3574565 : Blo 1587492 3574565 := bbase (se 4 (by rfl) ⟨335115, by rfl⟩ : syracuseStep 3574565 = 670231) (by norm_num)
theorem B3222317 : Blo 1587492 3222317 := bbase (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) (by norm_num)
theorem B2681653 : Blo 1587492 2681653 := bbase (se 5 (by rfl) ⟨125702, by rfl⟩ : syracuseStep 2681653 = 251405) (by norm_num)
theorem B2009929 : Blo 1587492 2009929 := bbase (se 2 (by rfl) ⟨753723, by rfl⟩ : syracuseStep 2009929 = 1507447) (by norm_num)
theorem B3574637 : Blo 1587492 3574637 := bbase (se 3 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 3574637 = 1340489) (by norm_num)
theorem B2681741 : Blo 1587492 2681741 := bbase (se 3 (by rfl) ⟨502826, by rfl⟩ : syracuseStep 2681741 = 1005653) (by norm_num)
theorem B5090197 : Blo 1587492 5090197 := bbase (se 6 (by rfl) ⟨119301, by rfl⟩ : syracuseStep 5090197 = 238603) (by norm_num)
theorem B2010025 : Blo 1587492 2010025 := bbase (se 2 (by rfl) ⟨753759, by rfl⟩ : syracuseStep 2010025 = 1507519) (by norm_num)
theorem B3574709 : Blo 1587492 3574709 := bbase (se 5 (by rfl) ⟨167564, by rfl⟩ : syracuseStep 3574709 = 335129) (by norm_num)
theorem B3574781 : Blo 1587492 3574781 := bbase (se 3 (by rfl) ⟨670271, by rfl⟩ : syracuseStep 3574781 = 1340543) (by norm_num)
theorem B2681869 : Blo 1587492 2681869 := bbase (se 3 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 2681869 = 1005701) (by norm_num)
theorem B4525109 : Blo 1587492 4525109 := bbase (se 5 (by rfl) ⟨212114, by rfl⟩ : syracuseStep 4525109 = 424229) (by norm_num)
theorem B3574853 : Blo 1587492 3574853 := bbase (se 4 (by rfl) ⟨335142, by rfl⟩ : syracuseStep 3574853 = 670285) (by norm_num)
theorem B2010197 : Blo 1587492 2010197 := bbase (se 8 (by rfl) ⟨11778, by rfl⟩ : syracuseStep 2010197 = 23557) (by norm_num)
theorem B5360741 : Blo 1587492 5360741 := bbase (se 4 (by rfl) ⟨502569, by rfl⟩ : syracuseStep 5360741 = 1005139) (by norm_num)
theorem B2681957 : Blo 1587492 2681957 := bbase (se 4 (by rfl) ⟨251433, by rfl⟩ : syracuseStep 2681957 = 502867) (by norm_num)
theorem B3394669 : Blo 1587492 3394669 := bbase (se 3 (by rfl) ⟨636500, by rfl⟩ : syracuseStep 3394669 = 1273001) (by norm_num)
theorem B2010253 : Blo 1587492 2010253 := bbase (se 3 (by rfl) ⟨376922, by rfl⟩ : syracuseStep 2010253 = 753845) (by norm_num)
theorem B3574925 : Blo 1587492 3574925 := bbase (se 3 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 3574925 = 1340597) (by norm_num)
theorem B8039573 : Blo 1587492 8039573 := bbase (se 6 (by rfl) ⟨188427, by rfl⟩ : syracuseStep 8039573 = 376855) (by norm_num)
theorem B3574997 : Blo 1587492 3574997 := bbase (se 7 (by rfl) ⟨41894, by rfl⟩ : syracuseStep 3574997 = 83789) (by norm_num)
theorem B2682085 : Blo 1587492 2682085 := bbase (se 4 (by rfl) ⟨251445, by rfl⟩ : syracuseStep 2682085 = 502891) (by norm_num)
theorem B2010349 : Blo 1587492 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B3575069 : Blo 1587492 3575069 := bbase (se 3 (by rfl) ⟨670325, by rfl⟩ : syracuseStep 3575069 = 1340651) (by norm_num)
theorem B2682173 : Blo 1587492 2682173 := bbase (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) (by norm_num)
theorem B3575141 : Blo 1587492 3575141 := bbase (se 4 (by rfl) ⟨335169, by rfl⟩ : syracuseStep 3575141 = 670339) (by norm_num)
theorem B2010521 : Blo 1587492 2010521 := bbase (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) (by norm_num)
theorem B3575213 : Blo 1587492 3575213 := bbase (se 3 (by rfl) ⟨670352, by rfl⟩ : syracuseStep 3575213 = 1340705) (by norm_num)
theorem B2010577 : Blo 1587492 2010577 := bbase (se 2 (by rfl) ⟨753966, by rfl⟩ : syracuseStep 2010577 = 1507933) (by norm_num)
theorem B4525541 : Blo 1587492 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B3575285 : Blo 1587492 3575285 := bbase (se 5 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 3575285 = 335183) (by norm_num)
theorem B5361173 : Blo 1587492 5361173 := bbase (se 6 (by rfl) ⟨125652, by rfl⟩ : syracuseStep 5361173 = 251305) (by norm_num)
theorem B2010673 : Blo 1587492 2010673 := bbase (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) (by norm_num)
theorem B3575357 : Blo 1587492 3575357 := bbase (se 3 (by rfl) ⟨670379, by rfl⟩ : syracuseStep 3575357 = 1340759) (by norm_num)
theorem B15265397 : Blo 1587492 15265397 := bbase (se 5 (by rfl) ⟨715565, by rfl⟩ : syracuseStep 15265397 = 1431131) (by norm_num)
theorem B3575429 : Blo 1587492 3575429 := bbase (se 4 (by rfl) ⟨335196, by rfl⟩ : syracuseStep 3575429 = 670393) (by norm_num)
theorem B2543285 : Blo 1587492 2543285 := bbase (se 5 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 2543285 = 238433) (by norm_num)
theorem B3575501 : Blo 1587492 3575501 := bbase (se 3 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 3575501 = 1340813) (by norm_num)
theorem B5091029 : Blo 1587492 5091029 := bbase (se 7 (by rfl) ⟨59660, by rfl⟩ : syracuseStep 5091029 = 119321) (by norm_num)
theorem B2010845 : Blo 1587492 2010845 := bbase (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) (by norm_num)
theorem B2010901 : Blo 1587492 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B3575573 : Blo 1587492 3575573 := bbase (se 6 (by rfl) ⟨83802, by rfl⟩ : syracuseStep 3575573 = 167605) (by norm_num)
theorem B3575645 : Blo 1587492 3575645 := bbase (se 3 (by rfl) ⟨670433, by rfl⟩ : syracuseStep 3575645 = 1340867) (by norm_num)
theorem B2010997 : Blo 1587492 2010997 := bbase (se 5 (by rfl) ⟨94265, by rfl⟩ : syracuseStep 2010997 = 188531) (by norm_num)
theorem B3575717 : Blo 1587492 3575717 := bbase (se 4 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 3575717 = 670447) (by norm_num)
theorem B5361605 : Blo 1587492 5361605 := bbase (se 4 (by rfl) ⟨502650, by rfl⟩ : syracuseStep 5361605 = 1005301) (by norm_num)
theorem B3575789 : Blo 1587492 3575789 := bbase (se 3 (by rfl) ⟨670460, by rfl⟩ : syracuseStep 3575789 = 1340921) (by norm_num)
theorem B7630853 : Blo 1587492 7630853 := bbase (se 4 (by rfl) ⟨715392, by rfl⟩ : syracuseStep 7630853 = 1430785) (by norm_num)
theorem B2011169 : Blo 1587492 2011169 := bbase (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) (by norm_num)
theorem B3575861 : Blo 1587492 3575861 := bbase (se 5 (by rfl) ⟨167618, by rfl⟩ : syracuseStep 3575861 = 335237) (by norm_num)
theorem B2715709 : Blo 1587492 2715709 := bbase (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) (by norm_num)
theorem B2011225 : Blo 1587492 2011225 := bbase (se 2 (by rfl) ⟨754209, by rfl⟩ : syracuseStep 2011225 = 1508419) (by norm_num)
theorem B3575933 : Blo 1587492 3575933 := bbase (se 3 (by rfl) ⟨670487, by rfl⟩ : syracuseStep 3575933 = 1340975) (by norm_num)
theorem B4018349 : Blo 1587492 4018349 := bbase (se 3 (by rfl) ⟨753440, by rfl⟩ : syracuseStep 4018349 = 1506881) (by norm_num)
theorem B9662645 : Blo 1587492 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B6787253 : Blo 1587492 6787253 := bbase (se 5 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 6787253 = 636305) (by norm_num)
theorem B2011321 : Blo 1587492 2011321 := bbase (se 2 (by rfl) ⟨754245, by rfl⟩ : syracuseStep 2011321 = 1508491) (by norm_num)
theorem B3576005 : Blo 1587492 3576005 := bbase (se 4 (by rfl) ⟨335250, by rfl⟩ : syracuseStep 3576005 = 670501) (by norm_num)
theorem B4526293 : Blo 1587492 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B3576077 : Blo 1587492 3576077 := bbase (se 3 (by rfl) ⟨670514, by rfl⟩ : syracuseStep 3576077 = 1341029) (by norm_num)
theorem B13758805 : Blo 1587492 13758805 := bbase (se 10 (by rfl) ⟨20154, by rfl⟩ : syracuseStep 13758805 = 40309) (by norm_num)
theorem B3576149 : Blo 1587492 3576149 := bbase (se 10 (by rfl) ⟨5238, by rfl⟩ : syracuseStep 3576149 = 10477) (by norm_num)
theorem B2011493 : Blo 1587492 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B5362037 : Blo 1587492 5362037 := bbase (se 5 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 5362037 = 502691) (by norm_num)
theorem B6033797 : Blo 1587492 6033797 := bbase (se 4 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 6033797 = 1131337) (by norm_num)
theorem B2011549 : Blo 1587492 2011549 := bbase (se 3 (by rfl) ⟨377165, by rfl⟩ : syracuseStep 2011549 = 754331) (by norm_num)
theorem B3576221 : Blo 1587492 3576221 := bbase (se 3 (by rfl) ⟨670541, by rfl⟩ : syracuseStep 3576221 = 1341083) (by norm_num)
theorem B8040869 : Blo 1587492 8040869 := bbase (se 4 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 8040869 = 1507663) (by norm_num)
theorem B3576293 : Blo 1587492 3576293 := bbase (se 4 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 3576293 = 670555) (by norm_num)
theorem B2011645 : Blo 1587492 2011645 := bbase (se 3 (by rfl) ⟨377183, by rfl⟩ : syracuseStep 2011645 = 754367) (by norm_num)
theorem B4018693 : Blo 1587492 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B4018805 : Blo 1587492 4018805 := bbase (se 5 (by rfl) ⟨188381, by rfl⟩ : syracuseStep 4018805 = 376763) (by norm_num)
theorem B6034085 : Blo 1587492 6034085 := bbase (se 4 (by rfl) ⟨565695, by rfl⟩ : syracuseStep 6034085 = 1131391) (by norm_num)
theorem B1635005 : Blo 1587492 1635005 := bbase (se 3 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 1635005 = 613127) (by norm_num)
theorem B5362469 : Blo 1587492 5362469 := bbase (se 4 (by rfl) ⟨502731, by rfl⟩ : syracuseStep 5362469 = 1005463) (by norm_num)
theorem B4018997 : Blo 1587492 4018997 := bbase (se 5 (by rfl) ⟨188390, by rfl⟩ : syracuseStep 4018997 = 376781) (by norm_num)
theorem B2036701 : Blo 1587492 2036701 := bbase (se 3 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 2036701 = 763763) (by norm_num)
theorem B4584421 : Blo 1587492 4584421 := bbase (se 4 (by rfl) ⟨429789, by rfl⟩ : syracuseStep 4584421 = 859579) (by norm_num)
theorem B13063157 : Blo 1587492 13063157 := bbase (se 5 (by rfl) ⟨612335, by rfl⟩ : syracuseStep 13063157 = 1224671) (by norm_num)
theorem B2864165 : Blo 1587492 2864165 := bbase (se 4 (by rfl) ⟨268515, by rfl⟩ : syracuseStep 2864165 = 537031) (by norm_num)
theorem B10179701 : Blo 1587492 10179701 := bbase (se 5 (by rfl) ⟨477173, by rfl⟩ : syracuseStep 10179701 = 954347) (by norm_num)
theorem B4019341 : Blo 1587492 4019341 := bbase (se 3 (by rfl) ⟨753626, by rfl⟩ : syracuseStep 4019341 = 1507253) (by norm_num)
theorem B2544797 : Blo 1587492 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B3814573 : Blo 1587492 3814573 := bbase (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) (by norm_num)
theorem B5362901 : Blo 1587492 5362901 := bbase (se 7 (by rfl) ⟨62846, by rfl⟩ : syracuseStep 5362901 = 125693) (by norm_num)
theorem B4019453 : Blo 1587492 4019453 := bbase (se 3 (by rfl) ⟨753647, by rfl⟩ : syracuseStep 4019453 = 1507295) (by norm_num)
theorem B3265813 : Blo 1587492 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B1611037 : Blo 1587492 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B3265885 : Blo 1587492 3265885 := bbase (se 3 (by rfl) ⟨612353, by rfl⟩ : syracuseStep 3265885 = 1224707) (by norm_num)
theorem B4019645 : Blo 1587492 4019645 := bbase (se 3 (by rfl) ⟨753683, by rfl⟩ : syracuseStep 4019645 = 1507367) (by norm_num)
theorem B2381261 : Blo 1587492 2381261 := bbase (se 3 (by rfl) ⟨446486, by rfl⟩ : syracuseStep 2381261 = 892973) (by norm_num)
theorem B2381285 : Blo 1587492 2381285 := bbase (se 4 (by rfl) ⟨223245, by rfl⟩ : syracuseStep 2381285 = 446491) (by norm_num)
theorem B2381309 : Blo 1587492 2381309 := bbase (se 3 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 2381309 = 892991) (by norm_num)
theorem B2381333 : Blo 1587492 2381333 := bbase (se 6 (by rfl) ⟨55812, by rfl⟩ : syracuseStep 2381333 = 111625) (by norm_num)
theorem B2381357 : Blo 1587492 2381357 := bbase (se 3 (by rfl) ⟨446504, by rfl⟩ : syracuseStep 2381357 = 893009) (by norm_num)
theorem B2381381 : Blo 1587492 2381381 := bbase (se 4 (by rfl) ⟨223254, by rfl⟩ : syracuseStep 2381381 = 446509) (by norm_num)
theorem B2381405 : Blo 1587492 2381405 := bbase (se 3 (by rfl) ⟨446513, by rfl⟩ : syracuseStep 2381405 = 893027) (by norm_num)
theorem B2545253 : Blo 1587492 2545253 := bbase (se 4 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 2545253 = 477235) (by norm_num)
theorem B2381429 : Blo 1587492 2381429 := bbase (se 5 (by rfl) ⟨111629, by rfl⟩ : syracuseStep 2381429 = 223259) (by norm_num)
theorem B3266165 : Blo 1587492 3266165 := bbase (se 5 (by rfl) ⟨153101, by rfl⟩ : syracuseStep 3266165 = 306203) (by norm_num)
theorem B5363333 : Blo 1587492 5363333 := bbase (se 4 (by rfl) ⟨502812, by rfl⟩ : syracuseStep 5363333 = 1005625) (by norm_num)
theorem B2381453 : Blo 1587492 2381453 := bbase (se 3 (by rfl) ⟨446522, by rfl⟩ : syracuseStep 2381453 = 893045) (by norm_num)
theorem B2381477 : Blo 1587492 2381477 := bbase (se 4 (by rfl) ⟨223263, by rfl⟩ : syracuseStep 2381477 = 446527) (by norm_num)
theorem B8042165 : Blo 1587492 8042165 := bbase (se 5 (by rfl) ⟨376976, by rfl⟩ : syracuseStep 8042165 = 753953) (by norm_num)
theorem B2381501 : Blo 1587492 2381501 := bbase (se 3 (by rfl) ⟨446531, by rfl⟩ : syracuseStep 2381501 = 893063) (by norm_num)
theorem B2381525 : Blo 1587492 2381525 := bbase (se 7 (by rfl) ⟨27908, by rfl⟩ : syracuseStep 2381525 = 55817) (by norm_num)
theorem B19314389 : Blo 1587492 19314389 := bbase (se 7 (by rfl) ⟨226340, by rfl⟩ : syracuseStep 19314389 = 452681) (by norm_num)
theorem B2381549 : Blo 1587492 2381549 := bbase (se 3 (by rfl) ⟨446540, by rfl⟩ : syracuseStep 2381549 = 893081) (by norm_num)
theorem B2381573 : Blo 1587492 2381573 := bbase (se 4 (by rfl) ⟨223272, by rfl⟩ : syracuseStep 2381573 = 446545) (by norm_num)
theorem B4019989 : Blo 1587492 4019989 := bbase (se 6 (by rfl) ⟨94218, by rfl⟩ : syracuseStep 4019989 = 188437) (by norm_num)
theorem B2381597 : Blo 1587492 2381597 := bbase (se 3 (by rfl) ⟨446549, by rfl⟩ : syracuseStep 2381597 = 893099) (by norm_num)
theorem B2381621 : Blo 1587492 2381621 := bbase (se 5 (by rfl) ⟨111638, by rfl⟩ : syracuseStep 2381621 = 223277) (by norm_num)
theorem B2381645 : Blo 1587492 2381645 := bbase (se 3 (by rfl) ⟨446558, by rfl⟩ : syracuseStep 2381645 = 893117) (by norm_num)
theorem B2381669 : Blo 1587492 2381669 := bbase (se 4 (by rfl) ⟨223281, by rfl⟩ : syracuseStep 2381669 = 446563) (by norm_num)
theorem B2381693 : Blo 1587492 2381693 := bbase (se 3 (by rfl) ⟨446567, by rfl⟩ : syracuseStep 2381693 = 893135) (by norm_num)
theorem B4020101 : Blo 1587492 4020101 := bbase (se 4 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 4020101 = 753769) (by norm_num)
theorem B4585349 : Blo 1587492 4585349 := bbase (se 4 (by rfl) ⟨429876, by rfl⟩ : syracuseStep 4585349 = 859753) (by norm_num)
theorem B2381717 : Blo 1587492 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B5724053 : Blo 1587492 5724053 := bbase (se 6 (by rfl) ⟨134157, by rfl⟩ : syracuseStep 5724053 = 268315) (by norm_num)
theorem B2381741 : Blo 1587492 2381741 := bbase (se 3 (by rfl) ⟨446576, by rfl⟩ : syracuseStep 2381741 = 893153) (by norm_num)
theorem B8591285 : Blo 1587492 8591285 := bbase (se 5 (by rfl) ⟨402716, by rfl⟩ : syracuseStep 8591285 = 805433) (by norm_num)
theorem B2381765 : Blo 1587492 2381765 := bbase (se 4 (by rfl) ⟨223290, by rfl⟩ : syracuseStep 2381765 = 446581) (by norm_num)
theorem B2381789 : Blo 1587492 2381789 := bbase (se 3 (by rfl) ⟨446585, by rfl⟩ : syracuseStep 2381789 = 893171) (by norm_num)
theorem B2381813 : Blo 1587492 2381813 := bbase (se 5 (by rfl) ⟨111647, by rfl⟩ : syracuseStep 2381813 = 223295) (by norm_num)
theorem B2381837 : Blo 1587492 2381837 := bbase (se 3 (by rfl) ⟨446594, by rfl⟩ : syracuseStep 2381837 = 893189) (by norm_num)
theorem B2381861 : Blo 1587492 2381861 := bbase (se 4 (by rfl) ⟨223299, by rfl⟩ : syracuseStep 2381861 = 446599) (by norm_num)
theorem B2414645 : Blo 1587492 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B5363765 : Blo 1587492 5363765 := bbase (se 5 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 5363765 = 502853) (by norm_num)
theorem B2381885 : Blo 1587492 2381885 := bbase (se 3 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 2381885 = 893207) (by norm_num)
theorem B4020293 : Blo 1587492 4020293 := bbase (se 4 (by rfl) ⟨376902, by rfl⟩ : syracuseStep 4020293 = 753805) (by norm_num)
theorem B2381909 : Blo 1587492 2381909 := bbase (se 8 (by rfl) ⟨13956, by rfl⟩ : syracuseStep 2381909 = 27913) (by norm_num)
theorem B2381933 : Blo 1587492 2381933 := bbase (se 3 (by rfl) ⟨446612, by rfl⟩ : syracuseStep 2381933 = 893225) (by norm_num)
theorem B2381957 : Blo 1587492 2381957 := bbase (se 4 (by rfl) ⟨223308, by rfl⟩ : syracuseStep 2381957 = 446617) (by norm_num)
theorem B9664661 : Blo 1587492 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B2381981 : Blo 1587492 2381981 := bbase (se 3 (by rfl) ⟨446621, by rfl⟩ : syracuseStep 2381981 = 893243) (by norm_num)
theorem B3815581 : Blo 1587492 3815581 := bbase (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) (by norm_num)
theorem B2382005 : Blo 1587492 2382005 := bbase (se 5 (by rfl) ⟨111656, by rfl⟩ : syracuseStep 2382005 = 223313) (by norm_num)
theorem B12064949 : Blo 1587492 12064949 := bbase (se 5 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 12064949 = 1131089) (by norm_num)
theorem B2382029 : Blo 1587492 2382029 := bbase (se 3 (by rfl) ⟨446630, by rfl⟩ : syracuseStep 2382029 = 893261) (by norm_num)
theorem B13760725 : Blo 1587492 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B2382053 : Blo 1587492 2382053 := bbase (se 4 (by rfl) ⟨223317, by rfl⟩ : syracuseStep 2382053 = 446635) (by norm_num)
theorem B2382077 : Blo 1587492 2382077 := bbase (se 3 (by rfl) ⟨446639, by rfl⟩ : syracuseStep 2382077 = 893279) (by norm_num)
theorem B3815677 : Blo 1587492 3815677 := bbase (se 3 (by rfl) ⟨715439, by rfl⟩ : syracuseStep 3815677 = 1430879) (by norm_num)
theorem B2382101 : Blo 1587492 2382101 := bbase (se 6 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 2382101 = 111661) (by norm_num)
theorem B2382125 : Blo 1587492 2382125 := bbase (se 3 (by rfl) ⟨446648, by rfl⟩ : syracuseStep 2382125 = 893297) (by norm_num)
theorem B2382149 : Blo 1587492 2382149 := bbase (se 4 (by rfl) ⟨223326, by rfl⟩ : syracuseStep 2382149 = 446653) (by norm_num)
theorem B2382173 : Blo 1587492 2382173 := bbase (se 3 (by rfl) ⟨446657, by rfl⟩ : syracuseStep 2382173 = 893315) (by norm_num)
theorem B2382197 : Blo 1587492 2382197 := bbase (se 5 (by rfl) ⟨111665, by rfl⟩ : syracuseStep 2382197 = 223331) (by norm_num)
theorem B2382221 : Blo 1587492 2382221 := bbase (se 3 (by rfl) ⟨446666, by rfl⟩ : syracuseStep 2382221 = 893333) (by norm_num)
theorem B4020637 : Blo 1587492 4020637 := bbase (se 3 (by rfl) ⟨753869, by rfl⟩ : syracuseStep 4020637 = 1507739) (by norm_num)
theorem B2685349 : Blo 1587492 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B2382245 : Blo 1587492 2382245 := bbase (se 4 (by rfl) ⟨223335, by rfl⟩ : syracuseStep 2382245 = 446671) (by norm_num)
theorem B2382269 : Blo 1587492 2382269 := bbase (se 3 (by rfl) ⟨446675, by rfl⟩ : syracuseStep 2382269 = 893351) (by norm_num)
theorem B2382293 : Blo 1587492 2382293 := bbase (se 7 (by rfl) ⟨27917, by rfl⟩ : syracuseStep 2382293 = 55835) (by norm_num)
theorem B5364197 : Blo 1587492 5364197 := bbase (se 4 (by rfl) ⟨502893, by rfl⟩ : syracuseStep 5364197 = 1005787) (by norm_num)
theorem B2382317 : Blo 1587492 2382317 := bbase (se 3 (by rfl) ⟨446684, by rfl⟩ : syracuseStep 2382317 = 893369) (by norm_num)
theorem B2382341 : Blo 1587492 2382341 := bbase (se 4 (by rfl) ⟨223344, by rfl⟩ : syracuseStep 2382341 = 446689) (by norm_num)
theorem B4020749 : Blo 1587492 4020749 := bbase (se 3 (by rfl) ⟨753890, by rfl⟩ : syracuseStep 4020749 = 1507781) (by norm_num)
theorem B6027797 : Blo 1587492 6027797 := bbase (se 6 (by rfl) ⟨141276, by rfl⟩ : syracuseStep 6027797 = 282553) (by norm_num)
theorem B2382365 : Blo 1587492 2382365 := bbase (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) (by norm_num)
theorem B6781477 : Blo 1587492 6781477 := bbase (se 4 (by rfl) ⟨635763, by rfl⟩ : syracuseStep 6781477 = 1271527) (by norm_num)
theorem B2382389 : Blo 1587492 2382389 := bbase (se 5 (by rfl) ⟨111674, by rfl⟩ : syracuseStep 2382389 = 223349) (by norm_num)
theorem B2382413 : Blo 1587492 2382413 := bbase (se 3 (by rfl) ⟨446702, by rfl⟩ : syracuseStep 2382413 = 893405) (by norm_num)
theorem B12057173 : Blo 1587492 12057173 := bbase (se 8 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 12057173 = 141295) (by norm_num)
theorem B2382437 : Blo 1587492 2382437 := bbase (se 4 (by rfl) ⟨223353, by rfl⟩ : syracuseStep 2382437 = 446707) (by norm_num)
theorem B2382461 : Blo 1587492 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B2382485 : Blo 1587492 2382485 := bbase (se 6 (by rfl) ⟨55839, by rfl⟩ : syracuseStep 2382485 = 111679) (by norm_num)
theorem B2292373 : Blo 1587492 2292373 := bbase (se 6 (by rfl) ⟨53727, by rfl⟩ : syracuseStep 2292373 = 107455) (by norm_num)
theorem B2382509 : Blo 1587492 2382509 := bbase (se 3 (by rfl) ⟨446720, by rfl⟩ : syracuseStep 2382509 = 893441) (by norm_num)
theorem B2382533 : Blo 1587492 2382533 := bbase (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) (by norm_num)
theorem B4020941 : Blo 1587492 4020941 := bbase (se 3 (by rfl) ⟨753926, by rfl⟩ : syracuseStep 4020941 = 1507853) (by norm_num)
theorem B8583893 : Blo 1587492 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B2382557 : Blo 1587492 2382557 := bbase (se 3 (by rfl) ⟨446729, by rfl⟩ : syracuseStep 2382557 = 893459) (by norm_num)
theorem B9042677 : Blo 1587492 9042677 := bbase (se 5 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 9042677 = 847751) (by norm_num)
theorem B2382581 : Blo 1587492 2382581 := bbase (se 5 (by rfl) ⟨111683, by rfl⟩ : syracuseStep 2382581 = 223367) (by norm_num)
theorem B11451125 : Blo 1587492 11451125 := bbase (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) (by norm_num)
theorem B3816197 : Blo 1587492 3816197 := bbase (se 4 (by rfl) ⟨357768, by rfl⟩ : syracuseStep 3816197 = 715537) (by norm_num)
theorem B2382605 : Blo 1587492 2382605 := bbase (se 3 (by rfl) ⟨446738, by rfl⟩ : syracuseStep 2382605 = 893477) (by norm_num)
theorem B2382629 : Blo 1587492 2382629 := bbase (se 4 (by rfl) ⟨223371, by rfl⟩ : syracuseStep 2382629 = 446743) (by norm_num)
theorem B2382653 : Blo 1587492 2382653 := bbase (se 3 (by rfl) ⟨446747, by rfl⟩ : syracuseStep 2382653 = 893495) (by norm_num)
theorem B2382677 : Blo 1587492 2382677 := bbase (se 9 (by rfl) ⟨6980, by rfl⟩ : syracuseStep 2382677 = 13961) (by norm_num)
theorem B2292581 : Blo 1587492 2292581 := bbase (se 4 (by rfl) ⟨214929, by rfl⟩ : syracuseStep 2292581 = 429859) (by norm_num)
theorem B2382701 : Blo 1587492 2382701 := bbase (se 3 (by rfl) ⟨446756, by rfl⟩ : syracuseStep 2382701 = 893513) (by norm_num)
theorem B2382725 : Blo 1587492 2382725 := bbase (se 4 (by rfl) ⟨223380, by rfl⟩ : syracuseStep 2382725 = 446761) (by norm_num)
theorem B2718605 : Blo 1587492 2718605 := bbase (se 3 (by rfl) ⟨509738, by rfl⟩ : syracuseStep 2718605 = 1019477) (by norm_num)
theorem B2382749 : Blo 1587492 2382749 := bbase (se 3 (by rfl) ⟨446765, by rfl⟩ : syracuseStep 2382749 = 893531) (by norm_num)
theorem B9657269 : Blo 1587492 9657269 := bbase (se 5 (by rfl) ⟨452684, by rfl⟩ : syracuseStep 9657269 = 905369) (by norm_num)
theorem B2382773 : Blo 1587492 2382773 := bbase (se 5 (by rfl) ⟨111692, by rfl⟩ : syracuseStep 2382773 = 223385) (by norm_num)
theorem B8043461 : Blo 1587492 8043461 := bbase (se 4 (by rfl) ⟨754074, by rfl⟩ : syracuseStep 8043461 = 1508149) (by norm_num)
theorem B2382797 : Blo 1587492 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B2382821 : Blo 1587492 2382821 := bbase (se 4 (by rfl) ⟨223389, by rfl⟩ : syracuseStep 2382821 = 446779) (by norm_num)
theorem B2382845 : Blo 1587492 2382845 := bbase (se 3 (by rfl) ⟨446783, by rfl⟩ : syracuseStep 2382845 = 893567) (by norm_num)
theorem B2382869 : Blo 1587492 2382869 := bbase (se 6 (by rfl) ⟨55848, by rfl⟩ : syracuseStep 2382869 = 111697) (by norm_num)
theorem B4021285 : Blo 1587492 4021285 := bbase (se 4 (by rfl) ⟨376995, by rfl⟩ : syracuseStep 4021285 = 753991) (by norm_num)
theorem B2382893 : Blo 1587492 2382893 := bbase (se 3 (by rfl) ⟨446792, by rfl⟩ : syracuseStep 2382893 = 893585) (by norm_num)
theorem B2382917 : Blo 1587492 2382917 := bbase (se 4 (by rfl) ⟨223398, by rfl⟩ : syracuseStep 2382917 = 446797) (by norm_num)
theorem B2382941 : Blo 1587492 2382941 := bbase (se 3 (by rfl) ⟨446801, by rfl⟩ : syracuseStep 2382941 = 893603) (by norm_num)
theorem B2382965 : Blo 1587492 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B2382989 : Blo 1587492 2382989 := bbase (se 3 (by rfl) ⟨446810, by rfl⟩ : syracuseStep 2382989 = 893621) (by norm_num)
theorem B4021397 : Blo 1587492 4021397 := bbase (se 6 (by rfl) ⟨94251, by rfl⟩ : syracuseStep 4021397 = 188503) (by norm_num)
theorem B4832405 : Blo 1587492 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B2383013 : Blo 1587492 2383013 := bbase (se 4 (by rfl) ⟨223407, by rfl⟩ : syracuseStep 2383013 = 446815) (by norm_num)
theorem B15465653 : Blo 1587492 15465653 := bbase (se 5 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 15465653 = 1449905) (by norm_num)
theorem B2383037 : Blo 1587492 2383037 := bbase (se 3 (by rfl) ⟨446819, by rfl⟩ : syracuseStep 2383037 = 893639) (by norm_num)
theorem B13565141 : Blo 1587492 13565141 := bbase (se 7 (by rfl) ⟨158966, by rfl⟩ : syracuseStep 13565141 = 317933) (by norm_num)
theorem B2383061 : Blo 1587492 2383061 := bbase (se 7 (by rfl) ⟨27926, by rfl⟩ : syracuseStep 2383061 = 55853) (by norm_num)
theorem B3013861 : Blo 1587492 3013861 := bbase (se 4 (by rfl) ⟨282549, by rfl⟩ : syracuseStep 3013861 = 565099) (by norm_num)
theorem B2383085 : Blo 1587492 2383085 := bbase (se 3 (by rfl) ⟨446828, by rfl⟩ : syracuseStep 2383085 = 893657) (by norm_num)
theorem B2383109 : Blo 1587492 2383109 := bbase (se 4 (by rfl) ⟨223416, by rfl⟩ : syracuseStep 2383109 = 446833) (by norm_num)
theorem B3816725 : Blo 1587492 3816725 := bbase (se 6 (by rfl) ⟨89454, by rfl⟩ : syracuseStep 3816725 = 178909) (by norm_num)
theorem B2383133 : Blo 1587492 2383133 := bbase (se 3 (by rfl) ⟨446837, by rfl⟩ : syracuseStep 2383133 = 893675) (by norm_num)
theorem B2383157 : Blo 1587492 2383157 := bbase (se 5 (by rfl) ⟨111710, by rfl⟩ : syracuseStep 2383157 = 223421) (by norm_num)
theorem B2383181 : Blo 1587492 2383181 := bbase (se 3 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 2383181 = 893693) (by norm_num)
theorem B4021589 : Blo 1587492 4021589 := bbase (se 11 (by rfl) ⟨2945, by rfl⟩ : syracuseStep 4021589 = 5891) (by norm_num)
theorem B2383205 : Blo 1587492 2383205 := bbase (se 4 (by rfl) ⟨223425, by rfl⟩ : syracuseStep 2383205 = 446851) (by norm_num)
theorem B2260333 : Blo 1587492 2260333 := bbase (se 3 (by rfl) ⟨423812, by rfl⟩ : syracuseStep 2260333 = 847625) (by norm_num)
theorem B3014005 : Blo 1587492 3014005 := bbase (se 5 (by rfl) ⟨141281, by rfl⟩ : syracuseStep 3014005 = 282563) (by norm_num)
theorem B2383229 : Blo 1587492 2383229 := bbase (se 3 (by rfl) ⟨446855, by rfl⟩ : syracuseStep 2383229 = 893711) (by norm_num)
theorem B4521349 : Blo 1587492 4521349 := bbase (se 4 (by rfl) ⟨423876, by rfl⟩ : syracuseStep 4521349 = 847753) (by norm_num)
theorem B2383253 : Blo 1587492 2383253 := bbase (se 6 (by rfl) ⟨55857, by rfl⟩ : syracuseStep 2383253 = 111715) (by norm_num)
theorem B3390893 : Blo 1587492 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B2383277 : Blo 1587492 2383277 := bbase (se 3 (by rfl) ⟨446864, by rfl⟩ : syracuseStep 2383277 = 893729) (by norm_num)
theorem B6438341 : Blo 1587492 6438341 := bbase (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) (by norm_num)
theorem B2383301 : Blo 1587492 2383301 := bbase (se 4 (by rfl) ⟨223434, by rfl⟩ : syracuseStep 2383301 = 446869) (by norm_num)
theorem B2383325 : Blo 1587492 2383325 := bbase (se 3 (by rfl) ⟨446873, by rfl⟩ : syracuseStep 2383325 = 893747) (by norm_num)
theorem B1908209 : Blo 1587492 1908209 := bbase (se 2 (by rfl) ⟨715578, by rfl⟩ : syracuseStep 1908209 = 1431157) (by norm_num)
theorem B2383349 : Blo 1587492 2383349 := bbase (se 5 (by rfl) ⟨111719, by rfl⟩ : syracuseStep 2383349 = 223439) (by norm_num)
theorem B3816965 : Blo 1587492 3816965 := bbase (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) (by norm_num)
theorem B2383373 : Blo 1587492 2383373 := bbase (se 3 (by rfl) ⟨446882, by rfl⟩ : syracuseStep 2383373 = 893765) (by norm_num)
theorem B3014165 : Blo 1587492 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B2383397 : Blo 1587492 2383397 := bbase (se 4 (by rfl) ⟨223443, by rfl⟩ : syracuseStep 2383397 = 446887) (by norm_num)
theorem B2383421 : Blo 1587492 2383421 := bbase (se 3 (by rfl) ⟨446891, by rfl⟩ : syracuseStep 2383421 = 893783) (by norm_num)
theorem B5226053 : Blo 1587492 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B6438469 : Blo 1587492 6438469 := bbase (se 4 (by rfl) ⟨603606, by rfl⟩ : syracuseStep 6438469 = 1207213) (by norm_num)
theorem B2383445 : Blo 1587492 2383445 := bbase (se 8 (by rfl) ⟨13965, by rfl⟩ : syracuseStep 2383445 = 27931) (by norm_num)
theorem B2383469 : Blo 1587492 2383469 := bbase (se 3 (by rfl) ⟨446900, by rfl⟩ : syracuseStep 2383469 = 893801) (by norm_num)
theorem B2383493 : Blo 1587492 2383493 := bbase (se 4 (by rfl) ⟨223452, by rfl⟩ : syracuseStep 2383493 = 446905) (by norm_num)
theorem B2383517 : Blo 1587492 2383517 := bbase (se 3 (by rfl) ⟨446909, by rfl⟩ : syracuseStep 2383517 = 893819) (by norm_num)
theorem B3014309 : Blo 1587492 3014309 := bbase (se 4 (by rfl) ⟨282591, by rfl⟩ : syracuseStep 3014309 = 565183) (by norm_num)
theorem B3391141 : Blo 1587492 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B1719973 : Blo 1587492 1719973 := bbase (se 4 (by rfl) ⟨161247, by rfl⟩ : syracuseStep 1719973 = 322495) (by norm_num)
theorem B4021933 : Blo 1587492 4021933 := bbase (se 3 (by rfl) ⟨754112, by rfl⟩ : syracuseStep 4021933 = 1508225) (by norm_num)
theorem B2383541 : Blo 1587492 2383541 := bbase (se 5 (by rfl) ⟨111728, by rfl⟩ : syracuseStep 2383541 = 223457) (by norm_num)
theorem B1695421 : Blo 1587492 1695421 := bbase (se 3 (by rfl) ⟨317891, by rfl⟩ : syracuseStep 1695421 = 635783) (by norm_num)
theorem B2383565 : Blo 1587492 2383565 := bbase (se 3 (by rfl) ⟨446918, by rfl⟩ : syracuseStep 2383565 = 893837) (by norm_num)
theorem B2383589 : Blo 1587492 2383589 := bbase (se 4 (by rfl) ⟨223461, by rfl⟩ : syracuseStep 2383589 = 446923) (by norm_num)
theorem B2383613 : Blo 1587492 2383613 := bbase (se 3 (by rfl) ⟨446927, by rfl⟩ : syracuseStep 2383613 = 893855) (by norm_num)
theorem B2383637 : Blo 1587492 2383637 := bbase (se 6 (by rfl) ⟨55866, by rfl⟩ : syracuseStep 2383637 = 111733) (by norm_num)
theorem B4022045 : Blo 1587492 4022045 := bbase (se 3 (by rfl) ⟨754133, by rfl⟩ : syracuseStep 4022045 = 1508267) (by norm_num)
theorem B1908517 : Blo 1587492 1908517 := bbase (se 4 (by rfl) ⟨178923, by rfl⟩ : syracuseStep 1908517 = 357847) (by norm_num)
theorem B2383661 : Blo 1587492 2383661 := bbase (se 3 (by rfl) ⟨446936, by rfl⟩ : syracuseStep 2383661 = 893873) (by norm_num)
theorem B2383685 : Blo 1587492 2383685 := bbase (se 4 (by rfl) ⟨223470, by rfl⟩ : syracuseStep 2383685 = 446941) (by norm_num)
theorem B3923797 : Blo 1587492 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B2383709 : Blo 1587492 2383709 := bbase (se 3 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 2383709 = 893891) (by norm_num)
theorem B2383733 : Blo 1587492 2383733 := bbase (se 5 (by rfl) ⟨111737, by rfl⟩ : syracuseStep 2383733 = 223475) (by norm_num)
theorem B1908617 : Blo 1587492 1908617 := bbase (se 2 (by rfl) ⟨715731, by rfl⟩ : syracuseStep 1908617 = 1431463) (by norm_num)
theorem B2383757 : Blo 1587492 2383757 := bbase (se 3 (by rfl) ⟨446954, by rfl⟩ : syracuseStep 2383757 = 893909) (by norm_num)
theorem B2383781 : Blo 1587492 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B2383805 : Blo 1587492 2383805 := bbase (se 3 (by rfl) ⟨446963, by rfl⟩ : syracuseStep 2383805 = 893927) (by norm_num)
theorem B3014597 : Blo 1587492 3014597 := bbase (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) (by norm_num)
theorem B2383829 : Blo 1587492 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B4022237 : Blo 1587492 4022237 := bbase (se 3 (by rfl) ⟨754169, by rfl⟩ : syracuseStep 4022237 = 1508339) (by norm_num)
theorem B2383853 : Blo 1587492 2383853 := bbase (se 3 (by rfl) ⟨446972, by rfl⟩ : syracuseStep 2383853 = 893945) (by norm_num)
theorem B1589251 : Blo 1587492 1589251 := bstep (se 1 (by rfl) ⟨1191938, by rfl⟩ : syracuseStep 1589251 = 2383877) B2383877
theorem B20348941 : Blo 1587492 20348941 := bstep (se 3 (by rfl) ⟨3815426, by rfl⟩ : syracuseStep 20348941 = 7630853) B7630853
theorem B2383889 : Blo 1587492 2383889 := bstep (se 2 (by rfl) ⟨893958, by rfl⟩ : syracuseStep 2383889 = 1787917) B1787917
theorem B1589267 : Blo 1587492 1589267 := bstep (se 1 (by rfl) ⟨1191950, by rfl⟩ : syracuseStep 1589267 = 2383901) B2383901
theorem B2383907 : Blo 1587492 2383907 := bstep (se 1 (by rfl) ⟨1787930, by rfl⟩ : syracuseStep 2383907 = 3575861) B3575861
theorem B1589283 : Blo 1587492 1589283 := bstep (se 1 (by rfl) ⟨1191962, by rfl⟩ : syracuseStep 1589283 = 2383925) B2383925
theorem B3440675 : Blo 1587492 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B1589299 : Blo 1587492 1589299 := bstep (se 1 (by rfl) ⟨1191974, by rfl⟩ : syracuseStep 1589299 = 2383949) B2383949
theorem B2383937 : Blo 1587492 2383937 := bstep (se 2 (by rfl) ⟨893976, by rfl⟩ : syracuseStep 2383937 = 1787953) B1787953
theorem B1589315 : Blo 1587492 1589315 := bstep (se 1 (by rfl) ⟨1191986, by rfl⟩ : syracuseStep 1589315 = 2383973) B2383973
theorem B5726285 : Blo 1587492 5726285 := bstep (se 3 (by rfl) ⟨1073678, by rfl⟩ : syracuseStep 5726285 = 2147357) B2147357
theorem B3620945 : Blo 1587492 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B2383955 : Blo 1587492 2383955 := bstep (se 1 (by rfl) ⟨1787966, by rfl⟩ : syracuseStep 2383955 = 3575933) B3575933
theorem B1589331 : Blo 1587492 1589331 := bstep (se 1 (by rfl) ⟨1191998, by rfl⟩ : syracuseStep 1589331 = 2383997) B2383997
theorem B1785955 : Blo 1587492 1785955 := bstep (se 1 (by rfl) ⟨1339466, by rfl⟩ : syracuseStep 1785955 = 2678933) B2678933
theorem B1589347 : Blo 1587492 1589347 := bstep (se 1 (by rfl) ⟨1192010, by rfl⟩ : syracuseStep 1589347 = 2384021) B2384021
theorem B2383985 : Blo 1587492 2383985 := bstep (se 2 (by rfl) ⟨893994, by rfl⟩ : syracuseStep 2383985 = 1787989) B1787989
theorem B2678899 : Blo 1587492 2678899 := bstep (se 1 (by rfl) ⟨2009174, by rfl⟩ : syracuseStep 2678899 = 4018349) B4018349
theorem B1589363 : Blo 1587492 1589363 := bstep (se 1 (by rfl) ⟨1192022, by rfl⟩ : syracuseStep 1589363 = 2384045) B2384045
theorem B3670147 : Blo 1587492 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B2384003 : Blo 1587492 2384003 := bstep (se 1 (by rfl) ⟨1788002, by rfl⟩ : syracuseStep 2384003 = 3576005) B3576005
theorem B1589379 : Blo 1587492 1589379 := bstep (se 1 (by rfl) ⟨1192034, by rfl⟩ : syracuseStep 1589379 = 2384069) B2384069
theorem B1589395 : Blo 1587492 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B2261153 : Blo 1587492 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B2384033 : Blo 1587492 2384033 := bstep (se 2 (by rfl) ⟨894012, by rfl⟩ : syracuseStep 2384033 = 1788025) B1788025
theorem B1589411 : Blo 1587492 1589411 := bstep (se 1 (by rfl) ⟨1192058, by rfl⟩ : syracuseStep 1589411 = 2384117) B2384117
theorem B3014833 : Blo 1587492 3014833 := bstep (se 2 (by rfl) ⟨1130562, by rfl⟩ : syracuseStep 3014833 = 2261125) B2261125
theorem B2384051 : Blo 1587492 2384051 := bstep (se 1 (by rfl) ⟨1788038, by rfl⟩ : syracuseStep 2384051 = 3576077) B3576077
theorem B1589427 : Blo 1587492 1589427 := bstep (se 1 (by rfl) ⟨1192070, by rfl⟩ : syracuseStep 1589427 = 2384141) B2384141
theorem B1589443 : Blo 1587492 1589443 := bstep (se 1 (by rfl) ⟨1192082, by rfl⟩ : syracuseStep 1589443 = 2384165) B2384165
theorem B9052357 : Blo 1587492 9052357 := bstep (se 4 (by rfl) ⟨848658, by rfl⟩ : syracuseStep 9052357 = 1697317) B1697317
theorem B5087441 : Blo 1587492 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B4522193 : Blo 1587492 4522193 := bstep (se 2 (by rfl) ⟨1695822, by rfl⟩ : syracuseStep 4522193 = 3391645) B3391645
theorem B2384081 : Blo 1587492 2384081 := bstep (se 2 (by rfl) ⟨894030, by rfl⟩ : syracuseStep 2384081 = 1788061) B1788061
theorem B1589459 : Blo 1587492 1589459 := bstep (se 1 (by rfl) ⟨1192094, by rfl⟩ : syracuseStep 1589459 = 2384189) B2384189
theorem B2384099 : Blo 1587492 2384099 := bstep (se 1 (by rfl) ⟨1788074, by rfl⟩ : syracuseStep 2384099 = 3576149) B3576149
theorem B1589475 : Blo 1587492 1589475 := bstep (se 1 (by rfl) ⟨1192106, by rfl⟩ : syracuseStep 1589475 = 2384213) B2384213
theorem B2261233 : Blo 1587492 2261233 := bstep (se 2 (by rfl) ⟨847962, by rfl⟩ : syracuseStep 2261233 = 1695925) B1695925
theorem B1786099 : Blo 1587492 1786099 := bstep (se 1 (by rfl) ⟨1339574, by rfl⟩ : syracuseStep 1786099 = 2679149) B2679149
theorem B1589491 : Blo 1587492 1589491 := bstep (se 1 (by rfl) ⟨1192118, by rfl⟩ : syracuseStep 1589491 = 2384237) B2384237
theorem B2679041 : Blo 1587492 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B4022531 : Blo 1587492 4022531 := bstep (se 1 (by rfl) ⟨3016898, by rfl⟩ : syracuseStep 4022531 = 6033797) B6033797
theorem B2384129 : Blo 1587492 2384129 := bstep (se 2 (by rfl) ⟨894048, by rfl⟩ : syracuseStep 2384129 = 1788097) B1788097
theorem B2384147 : Blo 1587492 2384147 := bstep (se 1 (by rfl) ⟨1788110, by rfl⟩ : syracuseStep 2384147 = 3576221) B3576221
theorem B2384177 : Blo 1587492 2384177 := bstep (se 2 (by rfl) ⟨894066, by rfl⟩ : syracuseStep 2384177 = 1788133) B1788133
theorem B2384195 : Blo 1587492 2384195 := bstep (se 1 (by rfl) ⟨1788146, by rfl⟩ : syracuseStep 2384195 = 3576293) B3576293
theorem B2384225 : Blo 1587492 2384225 := bstep (se 2 (by rfl) ⟨894084, by rfl⟩ : syracuseStep 2384225 = 1788169) B1788169
theorem B4292963 : Blo 1587492 4292963 := bstep (se 1 (by rfl) ⟨3219722, by rfl⟩ : syracuseStep 4292963 = 6439445) B6439445
theorem B5357933 : Blo 1587492 5357933 := bstep (se 3 (by rfl) ⟨1004612, by rfl⟩ : syracuseStep 5357933 = 2009225) B2009225
theorem B3572081 : Blo 1587492 3572081 := bstep (se 2 (by rfl) ⟨1339530, by rfl⟩ : syracuseStep 3572081 = 2679061) B2679061
theorem B7635313 : Blo 1587492 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B2679169 : Blo 1587492 2679169 := bstep (se 2 (by rfl) ⟨1004688, by rfl⟩ : syracuseStep 2679169 = 2009377) B2009377
theorem B3572099 : Blo 1587492 3572099 := bstep (se 1 (by rfl) ⟨2679074, by rfl⟩ : syracuseStep 3572099 = 5358149) B5358149
theorem B1786243 : Blo 1587492 1786243 := bstep (se 1 (by rfl) ⟨1339682, by rfl⟩ : syracuseStep 1786243 = 2679365) B2679365
theorem B5357987 : Blo 1587492 5357987 := bstep (se 1 (by rfl) ⟨4018490, by rfl⟩ : syracuseStep 5357987 = 8036981) B8036981
theorem B2679203 : Blo 1587492 2679203 := bstep (se 1 (by rfl) ⟨2009402, by rfl⟩ : syracuseStep 2679203 = 4018805) B4018805
theorem B4022723 : Blo 1587492 4022723 := bstep (se 1 (by rfl) ⟨3017042, by rfl⟩ : syracuseStep 4022723 = 6034085) B6034085
theorem B65233349 : Blo 1587492 65233349 := bstep (se 4 (by rfl) ⟨6115626, by rfl⟩ : syracuseStep 65233349 = 12231253) B12231253
theorem B3392003 : Blo 1587492 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B1786387 : Blo 1587492 1786387 := bstep (se 1 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 1786387 = 2679581) B2679581
theorem B2679331 : Blo 1587492 2679331 := bstep (se 1 (by rfl) ⟨2009498, by rfl⟩ : syracuseStep 2679331 = 4018997) B4018997
theorem B3580465 : Blo 1587492 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B3015235 : Blo 1587492 3015235 := bstep (se 1 (by rfl) ⟨2261426, by rfl⟩ : syracuseStep 3015235 = 4522853) B4522853
theorem B6029923 : Blo 1587492 6029923 := bstep (se 1 (by rfl) ⟨4522442, by rfl⟩ : syracuseStep 6029923 = 9044885) B9044885
theorem B3015281 : Blo 1587492 3015281 := bstep (se 2 (by rfl) ⟨1130730, by rfl⟩ : syracuseStep 3015281 = 2261461) B2261461
theorem B3572369 : Blo 1587492 3572369 := bstep (se 2 (by rfl) ⟨1339638, by rfl⟩ : syracuseStep 3572369 = 2679277) B2679277
theorem B3572387 : Blo 1587492 3572387 := bstep (se 1 (by rfl) ⟨2679290, by rfl⟩ : syracuseStep 3572387 = 5358581) B5358581
theorem B1786531 : Blo 1587492 1786531 := bstep (se 1 (by rfl) ⟨1339898, by rfl⟩ : syracuseStep 1786531 = 2679797) B2679797
theorem B8708771 : Blo 1587492 8708771 := bstep (se 1 (by rfl) ⟨6531578, by rfl⟩ : syracuseStep 8708771 = 13063157) B13063157
theorem B5358257 : Blo 1587492 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B2679473 : Blo 1587492 2679473 := bstep (se 2 (by rfl) ⟨1004802, by rfl⟩ : syracuseStep 2679473 = 2009605) B2009605
theorem B4293329 : Blo 1587492 4293329 := bstep (se 2 (by rfl) ⟨1609998, by rfl⟩ : syracuseStep 4293329 = 3219997) B3219997
theorem B2679601 : Blo 1587492 2679601 := bstep (se 2 (by rfl) ⟨1004850, by rfl⟩ : syracuseStep 2679601 = 2009701) B2009701
theorem B1786675 : Blo 1587492 1786675 := bstep (se 1 (by rfl) ⟨1340006, by rfl⟩ : syracuseStep 1786675 = 2680013) B2680013
theorem B2679635 : Blo 1587492 2679635 := bstep (se 1 (by rfl) ⟨2009726, by rfl⟩ : syracuseStep 2679635 = 4019453) B4019453
theorem B3056497 : Blo 1587492 3056497 := bstep (se 2 (by rfl) ⟨1146186, by rfl⟩ : syracuseStep 3056497 = 2292373) B2292373
theorem B3015569 : Blo 1587492 3015569 := bstep (se 2 (by rfl) ⟨1130838, by rfl⟩ : syracuseStep 3015569 = 2261677) B2261677
theorem B3572657 : Blo 1587492 3572657 := bstep (se 2 (by rfl) ⟨1339746, by rfl⟩ : syracuseStep 3572657 = 2679493) B2679493
theorem B3572675 : Blo 1587492 3572675 := bstep (se 1 (by rfl) ⟨2679506, by rfl⟩ : syracuseStep 3572675 = 5359013) B5359013
theorem B1786819 : Blo 1587492 1786819 := bstep (se 1 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 1786819 = 2680229) B2680229
theorem B2679763 : Blo 1587492 2679763 := bstep (se 1 (by rfl) ⟨2009822, by rfl⟩ : syracuseStep 2679763 = 4019645) B4019645
theorem B4522979 : Blo 1587492 4522979 := bstep (se 1 (by rfl) ⟨3392234, by rfl⟩ : syracuseStep 4522979 = 6784469) B6784469
theorem B2262019 : Blo 1587492 2262019 := bstep (se 1 (by rfl) ⟨1696514, by rfl⟩ : syracuseStep 2262019 = 3393029) B3393029
theorem B1696835 : Blo 1587492 1696835 := bstep (se 1 (by rfl) ⟨1272626, by rfl⟩ : syracuseStep 1696835 = 2545253) B2545253
theorem B1786963 : Blo 1587492 1786963 := bstep (se 1 (by rfl) ⟨1340222, by rfl⟩ : syracuseStep 1786963 = 2680445) B2680445
theorem B2679905 : Blo 1587492 2679905 := bstep (se 2 (by rfl) ⟨1004964, by rfl⟩ : syracuseStep 2679905 = 2009929) B2009929
theorem B4293731 : Blo 1587492 4293731 := bstep (se 1 (by rfl) ⟨3220298, by rfl⟩ : syracuseStep 4293731 = 6440597) B6440597
theorem B5358797 : Blo 1587492 5358797 := bstep (se 3 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 5358797 = 2009549) B2009549
theorem B3572945 : Blo 1587492 3572945 := bstep (se 2 (by rfl) ⟨1339854, by rfl⟩ : syracuseStep 3572945 = 2679709) B2679709
theorem B2680033 : Blo 1587492 2680033 := bstep (se 2 (by rfl) ⟨1005012, by rfl⟩ : syracuseStep 2680033 = 2010025) B2010025
theorem B3572963 : Blo 1587492 3572963 := bstep (se 1 (by rfl) ⟨2679722, by rfl⟩ : syracuseStep 3572963 = 5359445) B5359445
theorem B1787107 : Blo 1587492 1787107 := bstep (se 1 (by rfl) ⟨1340330, by rfl⟩ : syracuseStep 1787107 = 2680661) B2680661
theorem B5358851 : Blo 1587492 5358851 := bstep (se 1 (by rfl) ⟨4019138, by rfl⟩ : syracuseStep 5358851 = 8038277) B8038277
theorem B2680067 : Blo 1587492 2680067 := bstep (se 1 (by rfl) ⟨2010050, by rfl⟩ : syracuseStep 2680067 = 4020101) B4020101
theorem B3056899 : Blo 1587492 3056899 := bstep (se 1 (by rfl) ⟨2292674, by rfl⟩ : syracuseStep 3056899 = 4585349) B4585349
theorem B5727523 : Blo 1587492 5727523 := bstep (se 1 (by rfl) ⟨4295642, by rfl⟩ : syracuseStep 5727523 = 8591285) B8591285
theorem B5088557 : Blo 1587492 5088557 := bstep (se 3 (by rfl) ⟨954104, by rfl⟩ : syracuseStep 5088557 = 1908209) B1908209
theorem B4523309 : Blo 1587492 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B20350277 : Blo 1587492 20350277 := bstep (se 4 (by rfl) ⟨1907838, by rfl⟩ : syracuseStep 20350277 = 3815677) B3815677
theorem B4523377 : Blo 1587492 4523377 := bstep (se 2 (by rfl) ⟨1696266, by rfl⟩ : syracuseStep 4523377 = 3392533) B3392533
theorem B1787251 : Blo 1587492 1787251 := bstep (se 1 (by rfl) ⟨1340438, by rfl⟩ : syracuseStep 1787251 = 2680877) B2680877
theorem B2680195 : Blo 1587492 2680195 := bstep (se 1 (by rfl) ⟨2010146, by rfl⟩ : syracuseStep 2680195 = 4020293) B4020293
theorem B2262497 : Blo 1587492 2262497 := bstep (se 2 (by rfl) ⟨848436, by rfl⟩ : syracuseStep 2262497 = 1696873) B1696873
theorem B3573233 : Blo 1587492 3573233 := bstep (se 2 (by rfl) ⟨1339962, by rfl⟩ : syracuseStep 3573233 = 2679925) B2679925
theorem B3573251 : Blo 1587492 3573251 := bstep (se 1 (by rfl) ⟨2679938, by rfl⟩ : syracuseStep 3573251 = 5359877) B5359877
theorem B1787395 : Blo 1587492 1787395 := bstep (se 1 (by rfl) ⟨1340546, by rfl⟩ : syracuseStep 1787395 = 2681093) B2681093
theorem B13936141 : Blo 1587492 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B5359121 : Blo 1587492 5359121 := bstep (se 2 (by rfl) ⟨2009670, by rfl⟩ : syracuseStep 5359121 = 4019341) B4019341
theorem B2680337 : Blo 1587492 2680337 := bstep (se 2 (by rfl) ⟨1005126, by rfl⟩ : syracuseStep 2680337 = 2010253) B2010253
theorem B2262611 : Blo 1587492 2262611 := bstep (se 1 (by rfl) ⟨1696958, by rfl⟩ : syracuseStep 2262611 = 3393917) B3393917
theorem B3016291 : Blo 1587492 3016291 := bstep (se 1 (by rfl) ⟨2262218, by rfl⟩ : syracuseStep 3016291 = 4524437) B4524437
theorem B13567601 : Blo 1587492 13567601 := bstep (se 2 (by rfl) ⟨5087850, by rfl⟩ : syracuseStep 13567601 = 10175701) B10175701
theorem B4523651 : Blo 1587492 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B8709773 : Blo 1587492 8709773 := bstep (se 3 (by rfl) ⟨1633082, by rfl⟩ : syracuseStep 8709773 = 3266165) B3266165
theorem B2680465 : Blo 1587492 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B1787539 : Blo 1587492 1787539 := bstep (se 1 (by rfl) ⟨1340654, by rfl⟩ : syracuseStep 1787539 = 2681309) B2681309
theorem B2262691 : Blo 1587492 2262691 := bstep (se 1 (by rfl) ⟨1697018, by rfl⟩ : syracuseStep 2262691 = 3394037) B3394037
theorem B2680499 : Blo 1587492 2680499 := bstep (se 1 (by rfl) ⟨2010374, by rfl⟩ : syracuseStep 2680499 = 4020749) B4020749
theorem B2148049 : Blo 1587492 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B8038115 : Blo 1587492 8038115 := bstep (se 1 (by rfl) ⟨6028586, by rfl⟩ : syracuseStep 8038115 = 12057173) B12057173
theorem B3573521 : Blo 1587492 3573521 := bstep (se 2 (by rfl) ⟨1340070, by rfl⟩ : syracuseStep 3573521 = 2680141) B2680141
theorem B3573539 : Blo 1587492 3573539 := bstep (se 1 (by rfl) ⟨2680154, by rfl⟩ : syracuseStep 3573539 = 5360309) B5360309
theorem B1787683 : Blo 1587492 1787683 := bstep (se 1 (by rfl) ⟨1340762, by rfl⟩ : syracuseStep 1787683 = 2681525) B2681525
theorem B2680627 : Blo 1587492 2680627 := bstep (se 1 (by rfl) ⟨2010470, by rfl⟩ : syracuseStep 2680627 = 4020941) B4020941
theorem B17418053 : Blo 1587492 17418053 := bstep (se 4 (by rfl) ⟨1632942, by rfl⟩ : syracuseStep 17418053 = 3265885) B3265885
theorem B4360013 : Blo 1587492 4360013 := bstep (se 3 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 4360013 = 1635005) B1635005
theorem B2148211 : Blo 1587492 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1787827 : Blo 1587492 1787827 := bstep (se 1 (by rfl) ⟨1340870, by rfl⟩ : syracuseStep 1787827 = 2681741) B2681741
theorem B1812403 : Blo 1587492 1812403 := bstep (se 1 (by rfl) ⟨1359302, by rfl⟩ : syracuseStep 1812403 = 2718605) B2718605
theorem B2680769 : Blo 1587492 2680769 := bstep (se 2 (by rfl) ⟨1005288, by rfl⟩ : syracuseStep 2680769 = 2010577) B2010577
theorem B3672049 : Blo 1587492 3672049 := bstep (se 2 (by rfl) ⟨1377018, by rfl⟩ : syracuseStep 3672049 = 2754037) B2754037
theorem B3016739 : Blo 1587492 3016739 := bstep (se 1 (by rfl) ⟨2262554, by rfl⟩ : syracuseStep 3016739 = 4525109) B4525109
theorem B5359661 : Blo 1587492 5359661 := bstep (se 3 (by rfl) ⟨1004936, by rfl⟩ : syracuseStep 5359661 = 2009873) B2009873
theorem B3573809 : Blo 1587492 3573809 := bstep (se 2 (by rfl) ⟨1340178, by rfl⟩ : syracuseStep 3573809 = 2680357) B2680357
theorem B2680897 : Blo 1587492 2680897 := bstep (se 2 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 2680897 = 2010673) B2010673
theorem B3573827 : Blo 1587492 3573827 := bstep (se 1 (by rfl) ⟨2680370, by rfl⟩ : syracuseStep 3573827 = 5360741) B5360741
theorem B1787971 : Blo 1587492 1787971 := bstep (se 1 (by rfl) ⟨1340978, by rfl⟩ : syracuseStep 1787971 = 2681957) B2681957
theorem B5359715 : Blo 1587492 5359715 := bstep (se 1 (by rfl) ⟨4019786, by rfl⟩ : syracuseStep 5359715 = 8039573) B8039573
theorem B2680931 : Blo 1587492 2680931 := bstep (se 1 (by rfl) ⟨2010698, by rfl⟩ : syracuseStep 2680931 = 4021397) B4021397
theorem B3221603 : Blo 1587492 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B1788115 : Blo 1587492 1788115 := bstep (se 1 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 1788115 = 2682173) B2682173
theorem B2681059 : Blo 1587492 2681059 := bstep (se 1 (by rfl) ⟨2010794, by rfl⟩ : syracuseStep 2681059 = 4021589) B4021589
theorem B10316045 : Blo 1587492 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B6113549 : Blo 1587492 6113549 := bstep (se 3 (by rfl) ⟨1146290, by rfl⟩ : syracuseStep 6113549 = 2292581) B2292581
theorem B3017027 : Blo 1587492 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B3574097 : Blo 1587492 3574097 := bstep (se 2 (by rfl) ⟨1340286, by rfl⟩ : syracuseStep 3574097 = 2680573) B2680573
theorem B2009443 : Blo 1587492 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B3574115 : Blo 1587492 3574115 := bstep (se 1 (by rfl) ⟨2680586, by rfl⟩ : syracuseStep 3574115 = 5361173) B5361173
theorem B5089645 : Blo 1587492 5089645 := bstep (se 3 (by rfl) ⟨954308, by rfl⟩ : syracuseStep 5089645 = 1908617) B1908617
theorem B5359985 : Blo 1587492 5359985 := bstep (se 2 (by rfl) ⟨2009994, by rfl⟩ : syracuseStep 5359985 = 4019989) B4019989
theorem B2681201 : Blo 1587492 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B10176931 : Blo 1587492 10176931 := bstep (se 1 (by rfl) ⟨7632698, by rfl⟩ : syracuseStep 10176931 = 15265397) B15265397
theorem B2009539 : Blo 1587492 2009539 := bstep (se 1 (by rfl) ⟨1507154, by rfl⟩ : syracuseStep 2009539 = 3014309) B3014309
theorem B4524493 : Blo 1587492 4524493 := bstep (se 3 (by rfl) ⟨848342, by rfl⟩ : syracuseStep 4524493 = 1696685) B1696685
theorem B3394019 : Blo 1587492 3394019 := bstep (se 1 (by rfl) ⟨2545514, by rfl⟩ : syracuseStep 3394019 = 5091029) B5091029
theorem B2681329 : Blo 1587492 2681329 := bstep (se 2 (by rfl) ⟨1005498, by rfl⟩ : syracuseStep 2681329 = 2010997) B2010997
theorem B8038925 : Blo 1587492 8038925 := bstep (se 3 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 8038925 = 3014597) B3014597
theorem B2681363 : Blo 1587492 2681363 := bstep (se 1 (by rfl) ⟨2011022, by rfl⟩ : syracuseStep 2681363 = 4022045) B4022045
theorem B4524653 : Blo 1587492 4524653 := bstep (se 3 (by rfl) ⟨848372, by rfl⟩ : syracuseStep 4524653 = 1696745) B1696745
theorem B3574385 : Blo 1587492 3574385 := bstep (se 2 (by rfl) ⟨1340394, by rfl⟩ : syracuseStep 3574385 = 2680789) B2680789
theorem B3574403 : Blo 1587492 3574403 := bstep (se 1 (by rfl) ⟨2680802, by rfl⟩ : syracuseStep 3574403 = 5361605) B5361605
theorem B2681491 : Blo 1587492 2681491 := bstep (se 1 (by rfl) ⟨2011118, by rfl⟩ : syracuseStep 2681491 = 4022237) B4022237
theorem B6032141 : Blo 1587492 6032141 := bstep (se 3 (by rfl) ⟨1131026, by rfl⟩ : syracuseStep 6032141 = 2262053) B2262053
theorem B2681633 : Blo 1587492 2681633 := bstep (se 2 (by rfl) ⟨1005612, by rfl⟩ : syracuseStep 2681633 = 2011225) B2011225
theorem B6441763 : Blo 1587492 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B4524835 : Blo 1587492 4524835 := bstep (se 1 (by rfl) ⟨3393626, by rfl⟩ : syracuseStep 4524835 = 6787253) B6787253
theorem B5360525 : Blo 1587492 5360525 := bstep (se 3 (by rfl) ⟨1005098, by rfl⟩ : syracuseStep 5360525 = 2010197) B2010197
theorem B3574673 : Blo 1587492 3574673 := bstep (se 2 (by rfl) ⟨1340502, by rfl⟩ : syracuseStep 3574673 = 2681005) B2681005
theorem B2681761 : Blo 1587492 2681761 := bstep (se 2 (by rfl) ⟨1005660, by rfl⟩ : syracuseStep 2681761 = 2011321) B2011321
theorem B3574691 : Blo 1587492 3574691 := bstep (se 1 (by rfl) ⟨2681018, by rfl⟩ : syracuseStep 3574691 = 5362037) B5362037
theorem B2010035 : Blo 1587492 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B5360579 : Blo 1587492 5360579 := bstep (se 1 (by rfl) ⟨4020434, by rfl⟩ : syracuseStep 5360579 = 8040869) B8040869
theorem B2681795 : Blo 1587492 2681795 := bstep (se 1 (by rfl) ⟨2011346, by rfl⟩ : syracuseStep 2681795 = 4022693) B4022693
theorem B2862083 : Blo 1587492 2862083 := bstep (se 1 (by rfl) ⟨2146562, by rfl⟩ : syracuseStep 2862083 = 4293125) B4293125
theorem B19328053 : Blo 1587492 19328053 := bstep (se 5 (by rfl) ⟨906002, by rfl⟩ : syracuseStep 19328053 = 1812005) B1812005
theorem B30551093 : Blo 1587492 30551093 := bstep (se 5 (by rfl) ⟨1432082, by rfl⟩ : syracuseStep 30551093 = 2864165) B2864165
theorem B2681923 : Blo 1587492 2681923 := bstep (se 1 (by rfl) ⟨2011442, by rfl⟩ : syracuseStep 2681923 = 4022885) B4022885
theorem B6786125 : Blo 1587492 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B3574961 : Blo 1587492 3574961 := bstep (se 2 (by rfl) ⟨1340610, by rfl⟩ : syracuseStep 3574961 = 2681221) B2681221
theorem B3574979 : Blo 1587492 3574979 := bstep (se 1 (by rfl) ⟨2681234, by rfl⟩ : syracuseStep 3574979 = 5362469) B5362469
theorem B5360849 : Blo 1587492 5360849 := bstep (se 2 (by rfl) ⟨2010318, by rfl⟩ : syracuseStep 5360849 = 4020637) B4020637
theorem B2682065 : Blo 1587492 2682065 := bstep (se 2 (by rfl) ⟨1005774, by rfl⟩ : syracuseStep 2682065 = 2011549) B2011549
theorem B2682193 : Blo 1587492 2682193 := bstep (se 2 (by rfl) ⟨1005822, by rfl⟩ : syracuseStep 2682193 = 2011645) B2011645
theorem B2682227 : Blo 1587492 2682227 := bstep (se 1 (by rfl) ⟨2011670, by rfl⟩ : syracuseStep 2682227 = 4023341) B4023341
theorem B10177933 : Blo 1587492 10177933 := bstep (se 3 (by rfl) ⟨1908362, by rfl⟩ : syracuseStep 10177933 = 3816725) B3816725
theorem B6786467 : Blo 1587492 6786467 := bstep (se 1 (by rfl) ⟨5089850, by rfl⟩ : syracuseStep 6786467 = 10179701) B10179701
theorem B3575249 : Blo 1587492 3575249 := bstep (se 2 (by rfl) ⟨1340718, by rfl⟩ : syracuseStep 3575249 = 2681437) B2681437
theorem B3575267 : Blo 1587492 3575267 := bstep (se 1 (by rfl) ⟨2681450, by rfl⟩ : syracuseStep 3575267 = 5362901) B5362901
theorem B2010739 : Blo 1587492 2010739 := bstep (se 1 (by rfl) ⟨1508054, by rfl⟩ : syracuseStep 2010739 = 3016109) B3016109
theorem B20623045 : Blo 1587492 20623045 := bstep (se 4 (by rfl) ⟨1933410, by rfl⟩ : syracuseStep 20623045 = 3866821) B3866821
theorem B2010835 : Blo 1587492 2010835 := bstep (se 1 (by rfl) ⟨1508126, by rfl⟩ : syracuseStep 2010835 = 3016253) B3016253
theorem B5361389 : Blo 1587492 5361389 := bstep (se 3 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 5361389 = 2010521) B2010521
theorem B3575537 : Blo 1587492 3575537 := bstep (se 2 (by rfl) ⟨1340826, by rfl⟩ : syracuseStep 3575537 = 2681653) B2681653
theorem B3575555 : Blo 1587492 3575555 := bstep (se 1 (by rfl) ⟨2681666, by rfl⟩ : syracuseStep 3575555 = 5363333) B5363333
theorem B5361443 : Blo 1587492 5361443 := bstep (se 1 (by rfl) ⟨4021082, by rfl⟩ : syracuseStep 5361443 = 8042165) B8042165
theorem B2715491 : Blo 1587492 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B6786929 : Blo 1587492 6786929 := bstep (se 2 (by rfl) ⟨2545098, by rfl⟩ : syracuseStep 6786929 = 5090197) B5090197
theorem B2715601 : Blo 1587492 2715601 := bstep (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) B2036701
theorem B3575825 : Blo 1587492 3575825 := bstep (se 2 (by rfl) ⟨1340934, by rfl⟩ : syracuseStep 3575825 = 2681869) B2681869
theorem B1609763 : Blo 1587492 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B3575843 : Blo 1587492 3575843 := bstep (se 1 (by rfl) ⟨2681882, by rfl⟩ : syracuseStep 3575843 = 5363765) B5363765
theorem B5361713 : Blo 1587492 5361713 := bstep (se 2 (by rfl) ⟨2010642, by rfl⟩ : syracuseStep 5361713 = 4021285) B4021285
theorem B6443107 : Blo 1587492 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B5091427 : Blo 1587492 5091427 := bstep (se 1 (by rfl) ⟨3818570, by rfl⟩ : syracuseStep 5091427 = 7637141) B7637141
theorem B4526225 : Blo 1587492 4526225 := bstep (se 2 (by rfl) ⟨1697334, by rfl⟩ : syracuseStep 4526225 = 3394669) B3394669
theorem B5091491 : Blo 1587492 5091491 := bstep (se 1 (by rfl) ⟨3818618, by rfl⟩ : syracuseStep 5091491 = 7637237) B7637237
theorem B2011331 : Blo 1587492 2011331 := bstep (se 1 (by rfl) ⟨1508498, by rfl⟩ : syracuseStep 2011331 = 3016997) B3016997
theorem B5091569 : Blo 1587492 5091569 := bstep (se 2 (by rfl) ⟨1909338, by rfl⟩ : syracuseStep 5091569 = 3818677) B3818677
theorem B4018481 : Blo 1587492 4018481 := bstep (se 2 (by rfl) ⟨1506930, by rfl⟩ : syracuseStep 4018481 = 3013861) B3013861
theorem B3576113 : Blo 1587492 3576113 := bstep (se 2 (by rfl) ⟨1341042, by rfl⟩ : syracuseStep 3576113 = 2682085) B2682085
theorem B3576131 : Blo 1587492 3576131 := bstep (se 1 (by rfl) ⟨2682098, by rfl⟩ : syracuseStep 3576131 = 5364197) B5364197
theorem B4018531 : Blo 1587492 4018531 := bstep (se 1 (by rfl) ⟨3013898, by rfl⟩ : syracuseStep 4018531 = 6027797) B6027797
theorem B4354417 : Blo 1587492 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B73380293 : Blo 1587492 73380293 := bstep (se 4 (by rfl) ⟨6879402, by rfl⟩ : syracuseStep 73380293 = 13758805) B13758805
theorem B5722595 : Blo 1587492 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B4018673 : Blo 1587492 4018673 := bstep (se 2 (by rfl) ⟨1507002, by rfl⟩ : syracuseStep 4018673 = 3014005) B3014005
theorem B2544131 : Blo 1587492 2544131 := bstep (se 1 (by rfl) ⟨1908098, by rfl⟩ : syracuseStep 2544131 = 3816197) B3816197
theorem B5362253 : Blo 1587492 5362253 := bstep (se 3 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 5362253 = 2010845) B2010845
theorem B8589901 : Blo 1587492 8589901 := bstep (se 3 (by rfl) ⟨1610606, by rfl⟩ : syracuseStep 8589901 = 3221213) B3221213
theorem B4829777 : Blo 1587492 4829777 := bstep (se 2 (by rfl) ⟨1811166, by rfl⟩ : syracuseStep 4829777 = 3622333) B3622333
theorem B5362307 : Blo 1587492 5362307 := bstep (se 1 (by rfl) ⟨4021730, by rfl⟩ : syracuseStep 5362307 = 8043461) B8043461
theorem B23204549 : Blo 1587492 23204549 := bstep (se 4 (by rfl) ⟨2175426, by rfl⟩ : syracuseStep 23204549 = 4350853) B4350853
theorem B10310435 : Blo 1587492 10310435 := bstep (se 1 (by rfl) ⟨7732826, by rfl⟩ : syracuseStep 10310435 = 15465653) B15465653
theorem B5362577 : Blo 1587492 5362577 := bstep (se 2 (by rfl) ⟨2010966, by rfl⟩ : syracuseStep 5362577 = 4021933) B4021933
theorem B2544643 : Blo 1587492 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B2544689 : Blo 1587492 2544689 := bstep (se 2 (by rfl) ⟨954258, by rfl⟩ : syracuseStep 2544689 = 1908517) B1908517
theorem B5231729 : Blo 1587492 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B24450245 : Blo 1587492 24450245 := bstep (se 4 (by rfl) ⟨2292210, by rfl⟩ : syracuseStep 24450245 = 4584421) B4584421
theorem B8041841 : Blo 1587492 8041841 := bstep (se 2 (by rfl) ⟨3015690, by rfl⟩ : syracuseStep 8041841 = 6031381) B6031381
theorem B4830605 : Blo 1587492 4830605 := bstep (se 3 (by rfl) ⟨905738, by rfl⟩ : syracuseStep 4830605 = 1811477) B1811477
theorem B5363117 : Blo 1587492 5363117 := bstep (se 3 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 5363117 = 2011169) B2011169
theorem B2381249 : Blo 1587492 2381249 := bstep (se 2 (by rfl) ⟨892968, by rfl⟩ : syracuseStep 2381249 = 1785937) B1785937
theorem B11023813 : Blo 1587492 11023813 := bstep (se 4 (by rfl) ⟨1033482, by rfl⟩ : syracuseStep 11023813 = 2066965) B2066965
theorem B4019665 : Blo 1587492 4019665 := bstep (se 2 (by rfl) ⟨1507374, by rfl⟩ : syracuseStep 4019665 = 3014749) B3014749
theorem B2381267 : Blo 1587492 2381267 := bstep (se 1 (by rfl) ⟨1785950, by rfl⟩ : syracuseStep 2381267 = 3571901) B3571901
theorem B5363171 : Blo 1587492 5363171 := bstep (se 1 (by rfl) ⟨4022378, by rfl⟩ : syracuseStep 5363171 = 8044757) B8044757
theorem B2381297 : Blo 1587492 2381297 := bstep (se 2 (by rfl) ⟨892986, by rfl⟩ : syracuseStep 2381297 = 1785973) B1785973
theorem B2381315 : Blo 1587492 2381315 := bstep (se 1 (by rfl) ⟨1785986, by rfl⟩ : syracuseStep 2381315 = 3571973) B3571973
theorem B2381345 : Blo 1587492 2381345 := bstep (se 2 (by rfl) ⟨893004, by rfl⟩ : syracuseStep 2381345 = 1786009) B1786009
theorem B2381363 : Blo 1587492 2381363 := bstep (se 1 (by rfl) ⟨1786022, by rfl⟩ : syracuseStep 2381363 = 3572045) B3572045
theorem B2381393 : Blo 1587492 2381393 := bstep (se 2 (by rfl) ⟨893022, by rfl⟩ : syracuseStep 2381393 = 1786045) B1786045
theorem B2381411 : Blo 1587492 2381411 := bstep (se 1 (by rfl) ⟨1786058, by rfl⟩ : syracuseStep 2381411 = 3572117) B3572117
theorem B18347633 : Blo 1587492 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B6035057 : Blo 1587492 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B2381441 : Blo 1587492 2381441 := bstep (se 2 (by rfl) ⟨893040, by rfl⟩ : syracuseStep 2381441 = 1786081) B1786081
theorem B2381459 : Blo 1587492 2381459 := bstep (se 1 (by rfl) ⟨1786094, by rfl⟩ : syracuseStep 2381459 = 3572189) B3572189
theorem B2381489 : Blo 1587492 2381489 := bstep (se 2 (by rfl) ⟨893058, by rfl⟩ : syracuseStep 2381489 = 1786117) B1786117
theorem B2381507 : Blo 1587492 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B2578115 : Blo 1587492 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B2545361 : Blo 1587492 2545361 := bstep (se 2 (by rfl) ⟨954510, by rfl⟩ : syracuseStep 2545361 = 1909021) B1909021
theorem B2381537 : Blo 1587492 2381537 := bstep (se 2 (by rfl) ⟨893076, by rfl⟩ : syracuseStep 2381537 = 1786153) B1786153
theorem B4019939 : Blo 1587492 4019939 := bstep (se 1 (by rfl) ⟨3014954, by rfl⟩ : syracuseStep 4019939 = 6029909) B6029909
theorem B5363441 : Blo 1587492 5363441 := bstep (se 2 (by rfl) ⟨2011290, by rfl⟩ : syracuseStep 5363441 = 4022581) B4022581
theorem B2381555 : Blo 1587492 2381555 := bstep (se 1 (by rfl) ⟨1786166, by rfl⟩ : syracuseStep 2381555 = 3572333) B3572333
theorem B2381585 : Blo 1587492 2381585 := bstep (se 2 (by rfl) ⟨893094, by rfl⟩ : syracuseStep 2381585 = 1786189) B1786189
theorem B2381603 : Blo 1587492 2381603 := bstep (se 1 (by rfl) ⟨1786202, by rfl⟩ : syracuseStep 2381603 = 3572405) B3572405
theorem B2381633 : Blo 1587492 2381633 := bstep (se 2 (by rfl) ⟨893112, by rfl⟩ : syracuseStep 2381633 = 1786225) B1786225
theorem B2381651 : Blo 1587492 2381651 := bstep (se 1 (by rfl) ⟨1786238, by rfl⟩ : syracuseStep 2381651 = 3572477) B3572477
theorem B2381681 : Blo 1587492 2381681 := bstep (se 2 (by rfl) ⟨893130, by rfl⟩ : syracuseStep 2381681 = 1786261) B1786261
theorem B2381699 : Blo 1587492 2381699 := bstep (se 1 (by rfl) ⟨1786274, by rfl⟩ : syracuseStep 2381699 = 3572549) B3572549
theorem B2381729 : Blo 1587492 2381729 := bstep (se 2 (by rfl) ⟨893148, by rfl⟩ : syracuseStep 2381729 = 1786297) B1786297
theorem B4020131 : Blo 1587492 4020131 := bstep (se 1 (by rfl) ⟨3015098, by rfl⟩ : syracuseStep 4020131 = 6030197) B6030197
theorem B2381747 : Blo 1587492 2381747 := bstep (se 1 (by rfl) ⟨1786310, by rfl⟩ : syracuseStep 2381747 = 3572621) B3572621
theorem B2381777 : Blo 1587492 2381777 := bstep (se 2 (by rfl) ⟨893166, by rfl⟩ : syracuseStep 2381777 = 1786333) B1786333
theorem B2381795 : Blo 1587492 2381795 := bstep (se 1 (by rfl) ⟨1786346, by rfl⟩ : syracuseStep 2381795 = 3572693) B3572693
theorem B2381825 : Blo 1587492 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B2381843 : Blo 1587492 2381843 := bstep (se 1 (by rfl) ⟨1786382, by rfl⟩ : syracuseStep 2381843 = 3572765) B3572765
theorem B9041969 : Blo 1587492 9041969 := bstep (se 2 (by rfl) ⟨3390738, by rfl⟩ : syracuseStep 9041969 = 6781477) B6781477
theorem B2381873 : Blo 1587492 2381873 := bstep (se 2 (by rfl) ⟨893202, by rfl⟩ : syracuseStep 2381873 = 1786405) B1786405
theorem B2381891 : Blo 1587492 2381891 := bstep (se 1 (by rfl) ⟨1786418, by rfl⟩ : syracuseStep 2381891 = 3572837) B3572837
theorem B2447443 : Blo 1587492 2447443 := bstep (se 1 (by rfl) ⟨1835582, by rfl⟩ : syracuseStep 2447443 = 3671165) B3671165
theorem B2381921 : Blo 1587492 2381921 := bstep (se 2 (by rfl) ⟨893220, by rfl⟩ : syracuseStep 2381921 = 1786441) B1786441
theorem B2381939 : Blo 1587492 2381939 := bstep (se 1 (by rfl) ⟨1786454, by rfl⟩ : syracuseStep 2381939 = 3572909) B3572909
theorem B2381969 : Blo 1587492 2381969 := bstep (se 2 (by rfl) ⟨893238, by rfl⟩ : syracuseStep 2381969 = 1786477) B1786477
theorem B2381987 : Blo 1587492 2381987 := bstep (se 1 (by rfl) ⟨1786490, by rfl⟩ : syracuseStep 2381987 = 3572981) B3572981
theorem B2382017 : Blo 1587492 2382017 := bstep (se 2 (by rfl) ⟨893256, by rfl⟩ : syracuseStep 2382017 = 1786513) B1786513
theorem B9173189 : Blo 1587492 9173189 := bstep (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) B1719973
theorem B2545873 : Blo 1587492 2545873 := bstep (se 2 (by rfl) ⟨954702, by rfl⟩ : syracuseStep 2545873 = 1909405) B1909405
theorem B2382035 : Blo 1587492 2382035 := bstep (se 1 (by rfl) ⟨1786526, by rfl⟩ : syracuseStep 2382035 = 3573053) B3573053
theorem B20355299 : Blo 1587492 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B2382065 : Blo 1587492 2382065 := bstep (se 2 (by rfl) ⟨893274, by rfl⟩ : syracuseStep 2382065 = 1786549) B1786549
theorem B2382083 : Blo 1587492 2382083 := bstep (se 1 (by rfl) ⟨1786562, by rfl⟩ : syracuseStep 2382083 = 3573125) B3573125
theorem B5363981 : Blo 1587492 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B2382113 : Blo 1587492 2382113 := bstep (se 2 (by rfl) ⟨893292, by rfl⟩ : syracuseStep 2382113 = 1786585) B1786585
theorem B1587507 : Blo 1587492 1587507 := bstep (se 1 (by rfl) ⟨1190630, by rfl⟩ : syracuseStep 1587507 = 2381261) B2381261
theorem B2382131 : Blo 1587492 2382131 := bstep (se 1 (by rfl) ⟨1786598, by rfl⟩ : syracuseStep 2382131 = 3573197) B3573197
theorem B26482997 : Blo 1587492 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B1587523 : Blo 1587492 1587523 := bstep (se 1 (by rfl) ⟨1190642, by rfl⟩ : syracuseStep 1587523 = 2381285) B2381285
theorem B5364035 : Blo 1587492 5364035 := bstep (se 1 (by rfl) ⟨4023026, by rfl⟩ : syracuseStep 5364035 = 8046053) B8046053
theorem B7739725 : Blo 1587492 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B2382161 : Blo 1587492 2382161 := bstep (se 2 (by rfl) ⟨893310, by rfl⟩ : syracuseStep 2382161 = 1786621) B1786621
theorem B1587539 : Blo 1587492 1587539 := bstep (se 1 (by rfl) ⟨1190654, by rfl⟩ : syracuseStep 1587539 = 2381309) B2381309
theorem B1587555 : Blo 1587492 1587555 := bstep (se 1 (by rfl) ⟨1190666, by rfl⟩ : syracuseStep 1587555 = 2381333) B2381333
theorem B2382179 : Blo 1587492 2382179 := bstep (se 1 (by rfl) ⟨1786634, by rfl⟩ : syracuseStep 2382179 = 3573269) B3573269
theorem B1587571 : Blo 1587492 1587571 := bstep (se 1 (by rfl) ⟨1190678, by rfl⟩ : syracuseStep 1587571 = 2381357) B2381357
theorem B2382209 : Blo 1587492 2382209 := bstep (se 2 (by rfl) ⟨893328, by rfl⟩ : syracuseStep 2382209 = 1786657) B1786657
theorem B1587587 : Blo 1587492 1587587 := bstep (se 1 (by rfl) ⟨1190690, by rfl⟩ : syracuseStep 1587587 = 2381381) B2381381
theorem B1587603 : Blo 1587492 1587603 := bstep (se 1 (by rfl) ⟨1190702, by rfl⟩ : syracuseStep 1587603 = 2381405) B2381405
theorem B2382227 : Blo 1587492 2382227 := bstep (se 1 (by rfl) ⟨1786670, by rfl⟩ : syracuseStep 2382227 = 3573341) B3573341
theorem B1587619 : Blo 1587492 1587619 := bstep (se 1 (by rfl) ⟨1190714, by rfl⟩ : syracuseStep 1587619 = 2381429) B2381429
theorem B2382257 : Blo 1587492 2382257 := bstep (se 2 (by rfl) ⟨893346, by rfl⟩ : syracuseStep 2382257 = 1786693) B1786693
theorem B1587635 : Blo 1587492 1587635 := bstep (se 1 (by rfl) ⟨1190726, by rfl⟩ : syracuseStep 1587635 = 2381453) B2381453
theorem B1587651 : Blo 1587492 1587651 := bstep (se 1 (by rfl) ⟨1190738, by rfl⟩ : syracuseStep 1587651 = 2381477) B2381477
theorem B2382275 : Blo 1587492 2382275 := bstep (se 1 (by rfl) ⟨1786706, by rfl⟩ : syracuseStep 2382275 = 3573413) B3573413
theorem B1587667 : Blo 1587492 1587667 := bstep (se 1 (by rfl) ⟨1190750, by rfl⟩ : syracuseStep 1587667 = 2381501) B2381501
theorem B2382305 : Blo 1587492 2382305 := bstep (se 2 (by rfl) ⟨893364, by rfl⟩ : syracuseStep 2382305 = 1786729) B1786729
theorem B1587683 : Blo 1587492 1587683 := bstep (se 1 (by rfl) ⟨1190762, by rfl⟩ : syracuseStep 1587683 = 2381525) B2381525
theorem B12876259 : Blo 1587492 12876259 := bstep (se 1 (by rfl) ⟨9657194, by rfl⟩ : syracuseStep 12876259 = 19314389) B19314389
theorem B1587699 : Blo 1587492 1587699 := bstep (se 1 (by rfl) ⟨1190774, by rfl⟩ : syracuseStep 1587699 = 2381549) B2381549
theorem B2382323 : Blo 1587492 2382323 := bstep (se 1 (by rfl) ⟨1786742, by rfl⟩ : syracuseStep 2382323 = 3573485) B3573485
theorem B1587715 : Blo 1587492 1587715 := bstep (se 1 (by rfl) ⟨1190786, by rfl⟩ : syracuseStep 1587715 = 2381573) B2381573
theorem B2382353 : Blo 1587492 2382353 := bstep (se 2 (by rfl) ⟨893382, by rfl⟩ : syracuseStep 2382353 = 1786765) B1786765
theorem B1587731 : Blo 1587492 1587731 := bstep (se 1 (by rfl) ⟨1190798, by rfl⟩ : syracuseStep 1587731 = 2381597) B2381597
theorem B1587747 : Blo 1587492 1587747 := bstep (se 1 (by rfl) ⟨1190810, by rfl⟩ : syracuseStep 1587747 = 2381621) B2381621
theorem B2382371 : Blo 1587492 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B1587763 : Blo 1587492 1587763 := bstep (se 1 (by rfl) ⟨1190822, by rfl⟩ : syracuseStep 1587763 = 2381645) B2381645
theorem B2382401 : Blo 1587492 2382401 := bstep (se 2 (by rfl) ⟨893400, by rfl⟩ : syracuseStep 2382401 = 1786801) B1786801
theorem B1587779 : Blo 1587492 1587779 := bstep (se 1 (by rfl) ⟨1190834, by rfl⟩ : syracuseStep 1587779 = 2381669) B2381669
theorem B5364305 : Blo 1587492 5364305 := bstep (se 2 (by rfl) ⟨2011614, by rfl⟩ : syracuseStep 5364305 = 4023229) B4023229
theorem B1587795 : Blo 1587492 1587795 := bstep (se 1 (by rfl) ⟨1190846, by rfl⟩ : syracuseStep 1587795 = 2381693) B2381693
theorem B2382419 : Blo 1587492 2382419 := bstep (se 1 (by rfl) ⟨1786814, by rfl⟩ : syracuseStep 2382419 = 3573629) B3573629
theorem B1587811 : Blo 1587492 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B3816035 : Blo 1587492 3816035 := bstep (se 1 (by rfl) ⟨2862026, by rfl⟩ : syracuseStep 3816035 = 5724053) B5724053
theorem B2382449 : Blo 1587492 2382449 := bstep (se 2 (by rfl) ⟨893418, by rfl⟩ : syracuseStep 2382449 = 1786837) B1786837
theorem B1587827 : Blo 1587492 1587827 := bstep (se 1 (by rfl) ⟨1190870, by rfl⟩ : syracuseStep 1587827 = 2381741) B2381741
theorem B1587843 : Blo 1587492 1587843 := bstep (se 1 (by rfl) ⟨1190882, by rfl⟩ : syracuseStep 1587843 = 2381765) B2381765
theorem B2382467 : Blo 1587492 2382467 := bstep (se 1 (by rfl) ⟨1786850, by rfl⟩ : syracuseStep 2382467 = 3573701) B3573701
theorem B1587859 : Blo 1587492 1587859 := bstep (se 1 (by rfl) ⟨1190894, by rfl⟩ : syracuseStep 1587859 = 2381789) B2381789
theorem B2382497 : Blo 1587492 2382497 := bstep (se 2 (by rfl) ⟨893436, by rfl⟩ : syracuseStep 2382497 = 1786873) B1786873
theorem B10312355 : Blo 1587492 10312355 := bstep (se 1 (by rfl) ⟨7734266, by rfl⟩ : syracuseStep 10312355 = 15468533) B15468533
theorem B1587875 : Blo 1587492 1587875 := bstep (se 1 (by rfl) ⟨1190906, by rfl⟩ : syracuseStep 1587875 = 2381813) B2381813
theorem B1587891 : Blo 1587492 1587891 := bstep (se 1 (by rfl) ⟨1190918, by rfl⟩ : syracuseStep 1587891 = 2381837) B2381837
theorem B2382515 : Blo 1587492 2382515 := bstep (se 1 (by rfl) ⟨1786886, by rfl⟩ : syracuseStep 2382515 = 3573773) B3573773
theorem B1587907 : Blo 1587492 1587907 := bstep (se 1 (by rfl) ⟨1190930, by rfl⟩ : syracuseStep 1587907 = 2381861) B2381861
theorem B2382545 : Blo 1587492 2382545 := bstep (se 2 (by rfl) ⟨893454, by rfl⟩ : syracuseStep 2382545 = 1786909) B1786909
theorem B1587923 : Blo 1587492 1587923 := bstep (se 1 (by rfl) ⟨1190942, by rfl⟩ : syracuseStep 1587923 = 2381885) B2381885
theorem B2448083 : Blo 1587492 2448083 := bstep (se 1 (by rfl) ⟨1836062, by rfl⟩ : syracuseStep 2448083 = 3672125) B3672125
theorem B1587939 : Blo 1587492 1587939 := bstep (se 1 (by rfl) ⟨1190954, by rfl⟩ : syracuseStep 1587939 = 2381909) B2381909
theorem B2382563 : Blo 1587492 2382563 := bstep (se 1 (by rfl) ⟨1786922, by rfl⟩ : syracuseStep 2382563 = 3573845) B3573845
theorem B1587955 : Blo 1587492 1587955 := bstep (se 1 (by rfl) ⟨1190966, by rfl⟩ : syracuseStep 1587955 = 2381933) B2381933
theorem B2382593 : Blo 1587492 2382593 := bstep (se 2 (by rfl) ⟨893472, by rfl⟩ : syracuseStep 2382593 = 1786945) B1786945
theorem B1587971 : Blo 1587492 1587971 := bstep (se 1 (by rfl) ⟨1190978, by rfl⟩ : syracuseStep 1587971 = 2381957) B2381957
theorem B1587987 : Blo 1587492 1587987 := bstep (se 1 (by rfl) ⟨1190990, by rfl⟩ : syracuseStep 1587987 = 2381981) B2381981
theorem B2382611 : Blo 1587492 2382611 := bstep (se 1 (by rfl) ⟨1786958, by rfl⟩ : syracuseStep 2382611 = 3573917) B3573917
theorem B1588003 : Blo 1587492 1588003 := bstep (se 1 (by rfl) ⟨1191002, by rfl⟩ : syracuseStep 1588003 = 2382005) B2382005
theorem B8043299 : Blo 1587492 8043299 := bstep (se 1 (by rfl) ⟨6032474, by rfl⟩ : syracuseStep 8043299 = 12064949) B12064949
theorem B2382641 : Blo 1587492 2382641 := bstep (se 2 (by rfl) ⟨893490, by rfl⟩ : syracuseStep 2382641 = 1786981) B1786981
theorem B1588019 : Blo 1587492 1588019 := bstep (se 1 (by rfl) ⟨1191014, by rfl⟩ : syracuseStep 1588019 = 2382029) B2382029
theorem B1588035 : Blo 1587492 1588035 := bstep (se 1 (by rfl) ⟨1191026, by rfl⟩ : syracuseStep 1588035 = 2382053) B2382053
theorem B2382659 : Blo 1587492 2382659 := bstep (se 1 (by rfl) ⟨1786994, by rfl⟩ : syracuseStep 2382659 = 3573989) B3573989
theorem B4021073 : Blo 1587492 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B1588051 : Blo 1587492 1588051 := bstep (se 1 (by rfl) ⟨1191038, by rfl⟩ : syracuseStep 1588051 = 2382077) B2382077
theorem B2382689 : Blo 1587492 2382689 := bstep (se 2 (by rfl) ⟨893508, by rfl⟩ : syracuseStep 2382689 = 1787017) B1787017
theorem B1588067 : Blo 1587492 1588067 := bstep (se 1 (by rfl) ⟨1191050, by rfl⟩ : syracuseStep 1588067 = 2382101) B2382101
theorem B1588083 : Blo 1587492 1588083 := bstep (se 1 (by rfl) ⟨1191062, by rfl⟩ : syracuseStep 1588083 = 2382125) B2382125
theorem B2382707 : Blo 1587492 2382707 := bstep (se 1 (by rfl) ⟨1787030, by rfl⟩ : syracuseStep 2382707 = 3574061) B3574061
theorem B1588099 : Blo 1587492 1588099 := bstep (se 1 (by rfl) ⟨1191074, by rfl⟩ : syracuseStep 1588099 = 2382149) B2382149
theorem B4021123 : Blo 1587492 4021123 := bstep (se 1 (by rfl) ⟨3015842, by rfl⟩ : syracuseStep 4021123 = 6031685) B6031685
theorem B5086097 : Blo 1587492 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B2382737 : Blo 1587492 2382737 := bstep (se 2 (by rfl) ⟨893526, by rfl⟩ : syracuseStep 2382737 = 1787053) B1787053
theorem B1588115 : Blo 1587492 1588115 := bstep (se 1 (by rfl) ⟨1191086, by rfl⟩ : syracuseStep 1588115 = 2382173) B2382173
theorem B2415521 : Blo 1587492 2415521 := bstep (se 2 (by rfl) ⟨905820, by rfl⟩ : syracuseStep 2415521 = 1811641) B1811641
theorem B1588131 : Blo 1587492 1588131 := bstep (se 1 (by rfl) ⟨1191098, by rfl⟩ : syracuseStep 1588131 = 2382197) B2382197
theorem B2382755 : Blo 1587492 2382755 := bstep (se 1 (by rfl) ⟨1787066, by rfl⟩ : syracuseStep 2382755 = 3574133) B3574133
theorem B1588147 : Blo 1587492 1588147 := bstep (se 1 (by rfl) ⟨1191110, by rfl⟩ : syracuseStep 1588147 = 2382221) B2382221
theorem B2382785 : Blo 1587492 2382785 := bstep (se 2 (by rfl) ⟨893544, by rfl⟩ : syracuseStep 2382785 = 1787089) B1787089
theorem B1588163 : Blo 1587492 1588163 := bstep (se 1 (by rfl) ⟨1191122, by rfl⟩ : syracuseStep 1588163 = 2382245) B2382245
theorem B1588179 : Blo 1587492 1588179 := bstep (se 1 (by rfl) ⟨1191134, by rfl⟩ : syracuseStep 1588179 = 2382269) B2382269
theorem B2382803 : Blo 1587492 2382803 := bstep (se 1 (by rfl) ⟨1787102, by rfl⟩ : syracuseStep 2382803 = 3574205) B3574205
theorem B1588195 : Blo 1587492 1588195 := bstep (se 1 (by rfl) ⟨1191146, by rfl⟩ : syracuseStep 1588195 = 2382293) B2382293
theorem B2382833 : Blo 1587492 2382833 := bstep (se 2 (by rfl) ⟨893562, by rfl⟩ : syracuseStep 2382833 = 1787125) B1787125
theorem B1588211 : Blo 1587492 1588211 := bstep (se 1 (by rfl) ⟨1191158, by rfl⟩ : syracuseStep 1588211 = 2382317) B2382317
theorem B1588227 : Blo 1587492 1588227 := bstep (se 1 (by rfl) ⟨1191170, by rfl⟩ : syracuseStep 1588227 = 2382341) B2382341
theorem B2382851 : Blo 1587492 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B21740557 : Blo 1587492 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B4021265 : Blo 1587492 4021265 := bstep (se 2 (by rfl) ⟨1507974, by rfl⟩ : syracuseStep 4021265 = 3015949) B3015949
theorem B1588243 : Blo 1587492 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B2382881 : Blo 1587492 2382881 := bstep (se 2 (by rfl) ⟨893580, by rfl⟩ : syracuseStep 2382881 = 1787161) B1787161
theorem B1588259 : Blo 1587492 1588259 := bstep (se 1 (by rfl) ⟨1191194, by rfl⟩ : syracuseStep 1588259 = 2382389) B2382389
theorem B1588275 : Blo 1587492 1588275 := bstep (se 1 (by rfl) ⟨1191206, by rfl⟩ : syracuseStep 1588275 = 2382413) B2382413
theorem B2382899 : Blo 1587492 2382899 := bstep (se 1 (by rfl) ⟨1787174, by rfl⟩ : syracuseStep 2382899 = 3574349) B3574349
theorem B2415667 : Blo 1587492 2415667 := bstep (se 1 (by rfl) ⟨1811750, by rfl⟩ : syracuseStep 2415667 = 3623501) B3623501
theorem B1588291 : Blo 1587492 1588291 := bstep (se 1 (by rfl) ⟨1191218, by rfl⟩ : syracuseStep 1588291 = 2382437) B2382437
theorem B9657413 : Blo 1587492 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B2382929 : Blo 1587492 2382929 := bstep (se 2 (by rfl) ⟨893598, by rfl⟩ : syracuseStep 2382929 = 1787197) B1787197
theorem B1588307 : Blo 1587492 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B1588323 : Blo 1587492 1588323 := bstep (se 1 (by rfl) ⟨1191242, by rfl⟩ : syracuseStep 1588323 = 2382485) B2382485
theorem B2382947 : Blo 1587492 2382947 := bstep (se 1 (by rfl) ⟨1787210, by rfl⟩ : syracuseStep 2382947 = 3574421) B3574421
theorem B1588339 : Blo 1587492 1588339 := bstep (se 1 (by rfl) ⟨1191254, by rfl⟩ : syracuseStep 1588339 = 2382509) B2382509
theorem B2382977 : Blo 1587492 2382977 := bstep (se 2 (by rfl) ⟨893616, by rfl⟩ : syracuseStep 2382977 = 1787233) B1787233
theorem B1588355 : Blo 1587492 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B6782093 : Blo 1587492 6782093 := bstep (se 3 (by rfl) ⟨1271642, by rfl⟩ : syracuseStep 6782093 = 2543285) B2543285
theorem B3013777 : Blo 1587492 3013777 := bstep (se 2 (by rfl) ⟨1130166, by rfl⟩ : syracuseStep 3013777 = 2260333) B2260333
theorem B1588371 : Blo 1587492 1588371 := bstep (se 1 (by rfl) ⟨1191278, by rfl⟩ : syracuseStep 1588371 = 2382557) B2382557
theorem B2382995 : Blo 1587492 2382995 := bstep (se 1 (by rfl) ⟨1787246, by rfl⟩ : syracuseStep 2382995 = 3574493) B3574493
theorem B6028451 : Blo 1587492 6028451 := bstep (se 1 (by rfl) ⟨4521338, by rfl⟩ : syracuseStep 6028451 = 9042677) B9042677
theorem B1588387 : Blo 1587492 1588387 := bstep (se 1 (by rfl) ⟨1191290, by rfl⟩ : syracuseStep 1588387 = 2382581) B2382581
theorem B7634083 : Blo 1587492 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B6028465 : Blo 1587492 6028465 := bstep (se 2 (by rfl) ⟨2260674, by rfl⟩ : syracuseStep 6028465 = 4521349) B4521349
theorem B5725361 : Blo 1587492 5725361 := bstep (se 2 (by rfl) ⟨2147010, by rfl⟩ : syracuseStep 5725361 = 4294021) B4294021
theorem B1588403 : Blo 1587492 1588403 := bstep (se 1 (by rfl) ⟨1191302, by rfl⟩ : syracuseStep 1588403 = 2382605) B2382605
theorem B2383025 : Blo 1587492 2383025 := bstep (se 2 (by rfl) ⟨893634, by rfl⟩ : syracuseStep 2383025 = 1787269) B1787269
theorem B1588419 : Blo 1587492 1588419 := bstep (se 1 (by rfl) ⟨1191314, by rfl⟩ : syracuseStep 1588419 = 2382629) B2382629
theorem B2383043 : Blo 1587492 2383043 := bstep (se 1 (by rfl) ⟨1787282, by rfl⟩ : syracuseStep 2383043 = 3574565) B3574565
theorem B1588435 : Blo 1587492 1588435 := bstep (se 1 (by rfl) ⟨1191326, by rfl⟩ : syracuseStep 1588435 = 2382653) B2382653
theorem B2383073 : Blo 1587492 2383073 := bstep (se 2 (by rfl) ⟨893652, by rfl⟩ : syracuseStep 2383073 = 1787305) B1787305
theorem B1588451 : Blo 1587492 1588451 := bstep (se 1 (by rfl) ⟨1191338, by rfl⟩ : syracuseStep 1588451 = 2382677) B2382677
theorem B1588467 : Blo 1587492 1588467 := bstep (se 1 (by rfl) ⟨1191350, by rfl⟩ : syracuseStep 1588467 = 2382701) B2382701
theorem B2383091 : Blo 1587492 2383091 := bstep (se 1 (by rfl) ⟨1787318, by rfl⟩ : syracuseStep 2383091 = 3574637) B3574637
theorem B1588483 : Blo 1587492 1588483 := bstep (se 1 (by rfl) ⟨1191362, by rfl⟩ : syracuseStep 1588483 = 2382725) B2382725
theorem B2383121 : Blo 1587492 2383121 := bstep (se 2 (by rfl) ⟨893670, by rfl⟩ : syracuseStep 2383121 = 1787341) B1787341
theorem B1588499 : Blo 1587492 1588499 := bstep (se 1 (by rfl) ⟨1191374, by rfl⟩ : syracuseStep 1588499 = 2382749) B2382749
theorem B6438179 : Blo 1587492 6438179 := bstep (se 1 (by rfl) ⟨4828634, by rfl⟩ : syracuseStep 6438179 = 9657269) B9657269
theorem B1588515 : Blo 1587492 1588515 := bstep (se 1 (by rfl) ⟨1191386, by rfl⟩ : syracuseStep 1588515 = 2382773) B2382773
theorem B2383139 : Blo 1587492 2383139 := bstep (se 1 (by rfl) ⟨1787354, by rfl⟩ : syracuseStep 2383139 = 3574709) B3574709
theorem B1588531 : Blo 1587492 1588531 := bstep (se 1 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 1588531 = 2382797) B2382797
theorem B2383169 : Blo 1587492 2383169 := bstep (se 2 (by rfl) ⟨893688, by rfl⟩ : syracuseStep 2383169 = 1787377) B1787377
theorem B1588547 : Blo 1587492 1588547 := bstep (se 1 (by rfl) ⟨1191410, by rfl⟩ : syracuseStep 1588547 = 2382821) B2382821
theorem B1588563 : Blo 1587492 1588563 := bstep (se 1 (by rfl) ⟨1191422, by rfl⟩ : syracuseStep 1588563 = 2382845) B2382845
theorem B2383187 : Blo 1587492 2383187 := bstep (se 1 (by rfl) ⟨1787390, by rfl⟩ : syracuseStep 2383187 = 3574781) B3574781
theorem B1588579 : Blo 1587492 1588579 := bstep (se 1 (by rfl) ⟨1191434, by rfl⟩ : syracuseStep 1588579 = 2382869) B2382869
theorem B2383217 : Blo 1587492 2383217 := bstep (se 2 (by rfl) ⟨893706, by rfl⟩ : syracuseStep 2383217 = 1787413) B1787413
theorem B1588595 : Blo 1587492 1588595 := bstep (se 1 (by rfl) ⟨1191446, by rfl⟩ : syracuseStep 1588595 = 2382893) B2382893
theorem B1588611 : Blo 1587492 1588611 := bstep (se 1 (by rfl) ⟨1191458, by rfl⟩ : syracuseStep 1588611 = 2382917) B2382917
theorem B2383235 : Blo 1587492 2383235 := bstep (se 1 (by rfl) ⟨1787426, by rfl⟩ : syracuseStep 2383235 = 3574853) B3574853
theorem B77249933 : Blo 1587492 77249933 := bstep (se 3 (by rfl) ⟨14484362, by rfl⟩ : syracuseStep 77249933 = 28968725) B28968725
theorem B1588627 : Blo 1587492 1588627 := bstep (se 1 (by rfl) ⟨1191470, by rfl⟩ : syracuseStep 1588627 = 2382941) B2382941
theorem B2383265 : Blo 1587492 2383265 := bstep (se 2 (by rfl) ⟨893724, by rfl⟩ : syracuseStep 2383265 = 1787449) B1787449
theorem B1588643 : Blo 1587492 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B8584625 : Blo 1587492 8584625 := bstep (se 2 (by rfl) ⟨3219234, by rfl⟩ : syracuseStep 8584625 = 6438469) B6438469
theorem B1588659 : Blo 1587492 1588659 := bstep (se 1 (by rfl) ⟨1191494, by rfl⟩ : syracuseStep 1588659 = 2382989) B2382989
theorem B2383283 : Blo 1587492 2383283 := bstep (se 1 (by rfl) ⟨1787462, by rfl⟩ : syracuseStep 2383283 = 3574925) B3574925
theorem B19332533 : Blo 1587492 19332533 := bstep (se 5 (by rfl) ⟨906212, by rfl⟩ : syracuseStep 19332533 = 1812425) B1812425
theorem B1588675 : Blo 1587492 1588675 := bstep (se 1 (by rfl) ⟨1191506, by rfl⟩ : syracuseStep 1588675 = 2383013) B2383013
theorem B2383313 : Blo 1587492 2383313 := bstep (se 2 (by rfl) ⟨893742, by rfl⟩ : syracuseStep 2383313 = 1787485) B1787485
theorem B1588691 : Blo 1587492 1588691 := bstep (se 1 (by rfl) ⟨1191518, by rfl⟩ : syracuseStep 1588691 = 2383037) B2383037
theorem B9043427 : Blo 1587492 9043427 := bstep (se 1 (by rfl) ⟨6782570, by rfl⟩ : syracuseStep 9043427 = 13565141) B13565141
theorem B1588707 : Blo 1587492 1588707 := bstep (se 1 (by rfl) ⟨1191530, by rfl⟩ : syracuseStep 1588707 = 2383061) B2383061
theorem B2383331 : Blo 1587492 2383331 := bstep (se 1 (by rfl) ⟨1787498, by rfl⟩ : syracuseStep 2383331 = 3574997) B3574997
theorem B1588723 : Blo 1587492 1588723 := bstep (se 1 (by rfl) ⟨1191542, by rfl⟩ : syracuseStep 1588723 = 2383085) B2383085
theorem B2383361 : Blo 1587492 2383361 := bstep (se 2 (by rfl) ⟨893760, by rfl⟩ : syracuseStep 2383361 = 1787521) B1787521
theorem B1588739 : Blo 1587492 1588739 := bstep (se 1 (by rfl) ⟨1191554, by rfl⟩ : syracuseStep 1588739 = 2383109) B2383109
theorem B1588755 : Blo 1587492 1588755 := bstep (se 1 (by rfl) ⟨1191566, by rfl⟩ : syracuseStep 1588755 = 2383133) B2383133
theorem B2383379 : Blo 1587492 2383379 := bstep (se 1 (by rfl) ⟨1787534, by rfl⟩ : syracuseStep 2383379 = 3575069) B3575069
theorem B1588771 : Blo 1587492 1588771 := bstep (se 1 (by rfl) ⟨1191578, by rfl⟩ : syracuseStep 1588771 = 2383157) B2383157
theorem B4521521 : Blo 1587492 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B2383409 : Blo 1587492 2383409 := bstep (se 2 (by rfl) ⟨893778, by rfl⟩ : syracuseStep 2383409 = 1787557) B1787557
theorem B1588787 : Blo 1587492 1588787 := bstep (se 1 (by rfl) ⟨1191590, by rfl⟩ : syracuseStep 1588787 = 2383181) B2383181
theorem B1588803 : Blo 1587492 1588803 := bstep (se 1 (by rfl) ⟨1191602, by rfl⟩ : syracuseStep 1588803 = 2383205) B2383205
theorem B2383427 : Blo 1587492 2383427 := bstep (se 1 (by rfl) ⟨1787570, by rfl⟩ : syracuseStep 2383427 = 3575141) B3575141
theorem B8044109 : Blo 1587492 8044109 := bstep (se 3 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 8044109 = 3016541) B3016541
theorem B2260561 : Blo 1587492 2260561 := bstep (se 2 (by rfl) ⟨847710, by rfl⟩ : syracuseStep 2260561 = 1695421) B1695421
theorem B1588819 : Blo 1587492 1588819 := bstep (se 1 (by rfl) ⟨1191614, by rfl⟩ : syracuseStep 1588819 = 2383229) B2383229
theorem B2383457 : Blo 1587492 2383457 := bstep (se 2 (by rfl) ⟨893796, by rfl⟩ : syracuseStep 2383457 = 1787593) B1787593
theorem B1588835 : Blo 1587492 1588835 := bstep (se 1 (by rfl) ⟨1191626, by rfl⟩ : syracuseStep 1588835 = 2383253) B2383253
theorem B2260595 : Blo 1587492 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B1588851 : Blo 1587492 1588851 := bstep (se 1 (by rfl) ⟨1191638, by rfl⟩ : syracuseStep 1588851 = 2383277) B2383277
theorem B2383475 : Blo 1587492 2383475 := bstep (se 1 (by rfl) ⟨1787606, by rfl⟩ : syracuseStep 2383475 = 3575213) B3575213
theorem B4292227 : Blo 1587492 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B1588867 : Blo 1587492 1588867 := bstep (se 1 (by rfl) ⟨1191650, by rfl⟩ : syracuseStep 1588867 = 2383301) B2383301
theorem B1588883 : Blo 1587492 1588883 := bstep (se 1 (by rfl) ⟨1191662, by rfl⟩ : syracuseStep 1588883 = 2383325) B2383325
theorem B2383505 : Blo 1587492 2383505 := bstep (se 2 (by rfl) ⟨893814, by rfl⟩ : syracuseStep 2383505 = 1787629) B1787629
theorem B1588899 : Blo 1587492 1588899 := bstep (se 1 (by rfl) ⟨1191674, by rfl⟩ : syracuseStep 1588899 = 2383349) B2383349
theorem B2383523 : Blo 1587492 2383523 := bstep (se 1 (by rfl) ⟨1787642, by rfl⟩ : syracuseStep 2383523 = 3575285) B3575285
theorem B1588915 : Blo 1587492 1588915 := bstep (se 1 (by rfl) ⟨1191686, by rfl⟩ : syracuseStep 1588915 = 2383373) B2383373
theorem B2383553 : Blo 1587492 2383553 := bstep (se 2 (by rfl) ⟨893832, by rfl⟩ : syracuseStep 2383553 = 1787665) B1787665
theorem B1588931 : Blo 1587492 1588931 := bstep (se 1 (by rfl) ⟨1191698, by rfl⟩ : syracuseStep 1588931 = 2383397) B2383397
theorem B1588947 : Blo 1587492 1588947 := bstep (se 1 (by rfl) ⟨1191710, by rfl⟩ : syracuseStep 1588947 = 2383421) B2383421
theorem B2383571 : Blo 1587492 2383571 := bstep (se 1 (by rfl) ⟨1787678, by rfl⟩ : syracuseStep 2383571 = 3575357) B3575357
theorem B1588963 : Blo 1587492 1588963 := bstep (se 1 (by rfl) ⟨1191722, by rfl⟩ : syracuseStep 1588963 = 2383445) B2383445
theorem B2383601 : Blo 1587492 2383601 := bstep (se 2 (by rfl) ⟨893850, by rfl⟩ : syracuseStep 2383601 = 1787701) B1787701
theorem B1588979 : Blo 1587492 1588979 := bstep (se 1 (by rfl) ⟨1191734, by rfl⟩ : syracuseStep 1588979 = 2383469) B2383469
theorem B1588995 : Blo 1587492 1588995 := bstep (se 1 (by rfl) ⟨1191746, by rfl⟩ : syracuseStep 1588995 = 2383493) B2383493
theorem B2383619 : Blo 1587492 2383619 := bstep (se 1 (by rfl) ⟨1787714, by rfl⟩ : syracuseStep 2383619 = 3575429) B3575429
theorem B1589011 : Blo 1587492 1589011 := bstep (se 1 (by rfl) ⟨1191758, by rfl⟩ : syracuseStep 1589011 = 2383517) B2383517
theorem B2383649 : Blo 1587492 2383649 := bstep (se 2 (by rfl) ⟨893868, by rfl⟩ : syracuseStep 2383649 = 1787737) B1787737
theorem B1589027 : Blo 1587492 1589027 := bstep (se 1 (by rfl) ⟨1191770, by rfl⟩ : syracuseStep 1589027 = 2383541) B2383541
theorem B1589043 : Blo 1587492 1589043 := bstep (se 1 (by rfl) ⟨1191782, by rfl⟩ : syracuseStep 1589043 = 2383565) B2383565
theorem B2383667 : Blo 1587492 2383667 := bstep (se 1 (by rfl) ⟨1787750, by rfl⟩ : syracuseStep 2383667 = 3575501) B3575501
theorem B1589059 : Blo 1587492 1589059 := bstep (se 1 (by rfl) ⟨1191794, by rfl⟩ : syracuseStep 1589059 = 2383589) B2383589
theorem B2383697 : Blo 1587492 2383697 := bstep (se 2 (by rfl) ⟨893886, by rfl⟩ : syracuseStep 2383697 = 1787773) B1787773
theorem B1589075 : Blo 1587492 1589075 := bstep (se 1 (by rfl) ⟨1191806, by rfl⟩ : syracuseStep 1589075 = 2383613) B2383613
theorem B1589091 : Blo 1587492 1589091 := bstep (se 1 (by rfl) ⟨1191818, by rfl⟩ : syracuseStep 1589091 = 2383637) B2383637
theorem B2383715 : Blo 1587492 2383715 := bstep (se 1 (by rfl) ⟨1787786, by rfl⟩ : syracuseStep 2383715 = 3575573) B3575573
theorem B1589107 : Blo 1587492 1589107 := bstep (se 1 (by rfl) ⟨1191830, by rfl⟩ : syracuseStep 1589107 = 2383661) B2383661
theorem B2383745 : Blo 1587492 2383745 := bstep (se 2 (by rfl) ⟨893904, by rfl⟩ : syracuseStep 2383745 = 1787809) B1787809
theorem B1589123 : Blo 1587492 1589123 := bstep (se 1 (by rfl) ⟨1191842, by rfl⟩ : syracuseStep 1589123 = 2383685) B2383685
theorem B1589139 : Blo 1587492 1589139 := bstep (se 1 (by rfl) ⟨1191854, by rfl⟩ : syracuseStep 1589139 = 2383709) B2383709
theorem B2383763 : Blo 1587492 2383763 := bstep (se 1 (by rfl) ⟨1787822, by rfl⟩ : syracuseStep 2383763 = 3575645) B3575645
theorem B1589155 : Blo 1587492 1589155 := bstep (se 1 (by rfl) ⟨1191866, by rfl⟩ : syracuseStep 1589155 = 2383733) B2383733
theorem B2383793 : Blo 1587492 2383793 := bstep (se 2 (by rfl) ⟨893922, by rfl⟩ : syracuseStep 2383793 = 1787845) B1787845
theorem B1589171 : Blo 1587492 1589171 := bstep (se 1 (by rfl) ⟨1191878, by rfl⟩ : syracuseStep 1589171 = 2383757) B2383757
theorem B1589187 : Blo 1587492 1589187 := bstep (se 1 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 1589187 = 2383781) B2383781
theorem B2383811 : Blo 1587492 2383811 := bstep (se 1 (by rfl) ⟨1787858, by rfl⟩ : syracuseStep 2383811 = 3575717) B3575717
theorem B1589203 : Blo 1587492 1589203 := bstep (se 1 (by rfl) ⟨1191902, by rfl⟩ : syracuseStep 1589203 = 2383805) B2383805
theorem B2383841 : Blo 1587492 2383841 := bstep (se 2 (by rfl) ⟨893940, by rfl⟩ : syracuseStep 2383841 = 1787881) B1787881
theorem B1589219 : Blo 1587492 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B4022257 : Blo 1587492 4022257 := bstep (se 2 (by rfl) ⟨1508346, by rfl⟩ : syracuseStep 4022257 = 3016693) B3016693
theorem B1589235 : Blo 1587492 1589235 := bstep (se 1 (by rfl) ⟨1191926, by rfl⟩ : syracuseStep 1589235 = 2383853) B2383853
theorem B2383859 : Blo 1587492 2383859 := bstep (se 1 (by rfl) ⟨1787894, by rfl⟩ : syracuseStep 2383859 = 3575789) B3575789
theorem B2383883 : Blo 1587492 2383883 := bstep (se 1 (by rfl) ⟨1787912, by rfl⟩ : syracuseStep 2383883 = 3575825) B3575825
theorem B1589259 : Blo 1587492 1589259 := bstep (se 1 (by rfl) ⟨1191944, by rfl⟩ : syracuseStep 1589259 = 2383889) B2383889
theorem B27131921 : Blo 1587492 27131921 := bstep (se 2 (by rfl) ⟨10174470, by rfl⟩ : syracuseStep 27131921 = 20348941) B20348941
theorem B2383895 : Blo 1587492 2383895 := bstep (se 1 (by rfl) ⟨1787921, by rfl⟩ : syracuseStep 2383895 = 3575843) B3575843
theorem B1589271 : Blo 1587492 1589271 := bstep (se 1 (by rfl) ⟨1191953, by rfl⟩ : syracuseStep 1589271 = 2383907) B2383907
theorem B1589291 : Blo 1587492 1589291 := bstep (se 1 (by rfl) ⟨1191968, by rfl⟩ : syracuseStep 1589291 = 2383937) B2383937
theorem B3817523 : Blo 1587492 3817523 := bstep (se 1 (by rfl) ⟨2863142, by rfl⟩ : syracuseStep 3817523 = 5726285) B5726285
theorem B1589303 : Blo 1587492 1589303 := bstep (se 1 (by rfl) ⟨1191977, by rfl⟩ : syracuseStep 1589303 = 2383955) B2383955
theorem B74326085 : Blo 1587492 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B1589323 : Blo 1587492 1589323 := bstep (se 1 (by rfl) ⟨1191992, by rfl⟩ : syracuseStep 1589323 = 2383985) B2383985
theorem B1589335 : Blo 1587492 1589335 := bstep (se 1 (by rfl) ⟨1192001, by rfl⟩ : syracuseStep 1589335 = 2384003) B2384003
theorem B2383961 : Blo 1587492 2383961 := bstep (se 2 (by rfl) ⟨893985, by rfl⟩ : syracuseStep 2383961 = 1787971) B1787971
theorem B9175133 : Blo 1587492 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B1589355 : Blo 1587492 1589355 := bstep (se 1 (by rfl) ⟨1192016, by rfl⟩ : syracuseStep 1589355 = 2384033) B2384033
theorem B1589367 : Blo 1587492 1589367 := bstep (se 1 (by rfl) ⟨1192025, by rfl⟩ : syracuseStep 1589367 = 2384051) B2384051
theorem B3391627 : Blo 1587492 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B3014795 : Blo 1587492 3014795 := bstep (se 1 (by rfl) ⟨2261096, by rfl⟩ : syracuseStep 3014795 = 4522193) B4522193
theorem B1589387 : Blo 1587492 1589387 := bstep (se 1 (by rfl) ⟨1192040, by rfl⟩ : syracuseStep 1589387 = 2384081) B2384081
theorem B1589399 : Blo 1587492 1589399 := bstep (se 1 (by rfl) ⟨1192049, by rfl⟩ : syracuseStep 1589399 = 2384099) B2384099
theorem B3571865 : Blo 1587492 3571865 := bstep (se 2 (by rfl) ⟨1339449, by rfl⟩ : syracuseStep 3571865 = 2678899) B2678899
theorem B1786027 : Blo 1587492 1786027 := bstep (se 1 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 1786027 = 2679041) B2679041
theorem B1589419 : Blo 1587492 1589419 := bstep (se 1 (by rfl) ⟨1192064, by rfl⟩ : syracuseStep 1589419 = 2384129) B2384129
theorem B1589431 : Blo 1587492 1589431 := bstep (se 1 (by rfl) ⟨1192073, by rfl⟩ : syracuseStep 1589431 = 2384147) B2384147
theorem B2678987 : Blo 1587492 2678987 := bstep (se 1 (by rfl) ⟨2009240, by rfl⟩ : syracuseStep 2678987 = 4018481) B4018481
theorem B2384075 : Blo 1587492 2384075 := bstep (se 1 (by rfl) ⟨1788056, by rfl⟩ : syracuseStep 2384075 = 3576113) B3576113
theorem B1589451 : Blo 1587492 1589451 := bstep (se 1 (by rfl) ⟨1192088, by rfl⟩ : syracuseStep 1589451 = 2384177) B2384177
theorem B2384087 : Blo 1587492 2384087 := bstep (se 1 (by rfl) ⟨1788065, by rfl⟩ : syracuseStep 2384087 = 3576131) B3576131
theorem B1589463 : Blo 1587492 1589463 := bstep (se 1 (by rfl) ⟨1192097, by rfl⟩ : syracuseStep 1589463 = 2384195) B2384195
theorem B1589483 : Blo 1587492 1589483 := bstep (se 1 (by rfl) ⟨1192112, by rfl⟩ : syracuseStep 1589483 = 2384225) B2384225
theorem B3571955 : Blo 1587492 3571955 := bstep (se 1 (by rfl) ⟨2678966, by rfl⟩ : syracuseStep 3571955 = 5357933) B5357933
theorem B3571991 : Blo 1587492 3571991 := bstep (se 1 (by rfl) ⟨2678993, by rfl⟩ : syracuseStep 3571991 = 5357987) B5357987
theorem B1786135 : Blo 1587492 1786135 := bstep (se 1 (by rfl) ⟨1339601, by rfl⟩ : syracuseStep 1786135 = 2679203) B2679203
theorem B2384153 : Blo 1587492 2384153 := bstep (se 2 (by rfl) ⟨894057, by rfl⟩ : syracuseStep 2384153 = 1788115) B1788115
theorem B13951277 : Blo 1587492 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B3014977 : Blo 1587492 3014977 := bstep (se 2 (by rfl) ⟨1130616, by rfl⟩ : syracuseStep 3014977 = 2261233) B2261233
theorem B2679115 : Blo 1587492 2679115 := bstep (se 1 (by rfl) ⟨2009336, by rfl⟩ : syracuseStep 2679115 = 4018673) B4018673
theorem B1696087 : Blo 1587492 1696087 := bstep (se 1 (by rfl) ⟨1272065, by rfl⟩ : syracuseStep 1696087 = 2544131) B2544131
theorem B17170805 : Blo 1587492 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B3219851 : Blo 1587492 3219851 := bstep (se 1 (by rfl) ⟨2414888, by rfl⟩ : syracuseStep 3219851 = 4829777) B4829777
theorem B6029741 : Blo 1587492 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B3572171 : Blo 1587492 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B1786315 : Blo 1587492 1786315 := bstep (se 1 (by rfl) ⟨1339736, by rfl⟩ : syracuseStep 1786315 = 2679473) B2679473
theorem B5358041 : Blo 1587492 5358041 := bstep (se 2 (by rfl) ⟨2009265, by rfl⟩ : syracuseStep 5358041 = 4018531) B4018531
theorem B2679257 : Blo 1587492 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B3572225 : Blo 1587492 3572225 := bstep (se 2 (by rfl) ⟨1339584, by rfl⟩ : syracuseStep 3572225 = 2679169) B2679169
theorem B24461837 : Blo 1587492 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B6873623 : Blo 1587492 6873623 := bstep (se 1 (by rfl) ⟨5155217, by rfl⟩ : syracuseStep 6873623 = 10310435) B10310435
theorem B1786423 : Blo 1587492 1786423 := bstep (se 1 (by rfl) ⟨1339817, by rfl⟩ : syracuseStep 1786423 = 2679635) B2679635
theorem B2679385 : Blo 1587492 2679385 := bstep (se 2 (by rfl) ⟨1004769, by rfl⟩ : syracuseStep 2679385 = 2009539) B2009539
theorem B3015319 : Blo 1587492 3015319 := bstep (se 1 (by rfl) ⟨2261489, by rfl⟩ : syracuseStep 3015319 = 4522979) B4522979
theorem B1696459 : Blo 1587492 1696459 := bstep (se 1 (by rfl) ⟨1272344, by rfl⟩ : syracuseStep 1696459 = 2544689) B2544689
theorem B27509453 : Blo 1587492 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B3572441 : Blo 1587492 3572441 := bstep (se 2 (by rfl) ⟨1339665, by rfl⟩ : syracuseStep 3572441 = 2679331) B2679331
theorem B1786603 : Blo 1587492 1786603 := bstep (se 1 (by rfl) ⟨1339952, by rfl⟩ : syracuseStep 1786603 = 2679905) B2679905
theorem B11453201 : Blo 1587492 11453201 := bstep (se 2 (by rfl) ⟨4294950, by rfl⟩ : syracuseStep 11453201 = 8589901) B8589901
theorem B3572531 : Blo 1587492 3572531 := bstep (se 1 (by rfl) ⟨2679398, by rfl⟩ : syracuseStep 3572531 = 5358797) B5358797
theorem B3572567 : Blo 1587492 3572567 := bstep (se 1 (by rfl) ⟨2679425, by rfl⟩ : syracuseStep 3572567 = 5358851) B5358851
theorem B1786711 : Blo 1587492 1786711 := bstep (se 1 (by rfl) ⟨1340033, by rfl⟩ : syracuseStep 1786711 = 2680067) B2680067
theorem B8045405 : Blo 1587492 8045405 := bstep (se 3 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 8045405 = 3017027) B3017027
theorem B3392371 : Blo 1587492 3392371 := bstep (se 1 (by rfl) ⟨2544278, by rfl⟩ : syracuseStep 3392371 = 5088557) B5088557
theorem B3015539 : Blo 1587492 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B13566851 : Blo 1587492 13566851 := bstep (se 1 (by rfl) ⟨10175138, by rfl⟩ : syracuseStep 13566851 = 20350277) B20350277
theorem B3220403 : Blo 1587492 3220403 := bstep (se 1 (by rfl) ⟨2415302, by rfl⟩ : syracuseStep 3220403 = 4830605) B4830605
theorem B3572747 : Blo 1587492 3572747 := bstep (se 1 (by rfl) ⟨2679560, by rfl⟩ : syracuseStep 3572747 = 5359121) B5359121
theorem B1786891 : Blo 1587492 1786891 := bstep (se 1 (by rfl) ⟨1340168, by rfl⟩ : syracuseStep 1786891 = 2680337) B2680337
theorem B3572801 : Blo 1587492 3572801 := bstep (se 2 (by rfl) ⟨1339800, by rfl⟩ : syracuseStep 3572801 = 2679601) B2679601
theorem B9045067 : Blo 1587492 9045067 := bstep (se 1 (by rfl) ⟨6783800, by rfl⟩ : syracuseStep 9045067 = 13567601) B13567601
theorem B12231755 : Blo 1587492 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B4023371 : Blo 1587492 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B3015767 : Blo 1587492 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B1786999 : Blo 1587492 1786999 := bstep (se 1 (by rfl) ⟨1340249, by rfl⟩ : syracuseStep 1786999 = 2680499) B2680499
theorem B1696907 : Blo 1587492 1696907 := bstep (se 1 (by rfl) ⟨1272680, by rfl⟩ : syracuseStep 1696907 = 2545361) B2545361
theorem B51553421 : Blo 1587492 51553421 := bstep (se 3 (by rfl) ⟨9666266, by rfl⟩ : syracuseStep 51553421 = 19332533) B19332533
theorem B5358743 : Blo 1587492 5358743 := bstep (se 1 (by rfl) ⟨4019057, by rfl⟩ : syracuseStep 5358743 = 8038115) B8038115
theorem B2679959 : Blo 1587492 2679959 := bstep (se 1 (by rfl) ⟨2009969, by rfl⟩ : syracuseStep 2679959 = 4019939) B4019939
theorem B2680087 : Blo 1587492 2680087 := bstep (se 1 (by rfl) ⟨2010065, by rfl⟩ : syracuseStep 2680087 = 4020131) B4020131
theorem B3573017 : Blo 1587492 3573017 := bstep (se 2 (by rfl) ⟨1339881, by rfl⟩ : syracuseStep 3573017 = 2679763) B2679763
theorem B1787179 : Blo 1587492 1787179 := bstep (se 1 (by rfl) ⟨1340384, by rfl⟩ : syracuseStep 1787179 = 2680769) B2680769
theorem B3392857 : Blo 1587492 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B3016025 : Blo 1587492 3016025 := bstep (se 2 (by rfl) ⟨1131009, by rfl⟩ : syracuseStep 3016025 = 2262019) B2262019
theorem B9045341 : Blo 1587492 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B3573107 : Blo 1587492 3573107 := bstep (se 1 (by rfl) ⟨2679830, by rfl⟩ : syracuseStep 3573107 = 5359661) B5359661
theorem B3573143 : Blo 1587492 3573143 := bstep (se 1 (by rfl) ⟨2679857, by rfl⟩ : syracuseStep 3573143 = 5359715) B5359715
theorem B1787287 : Blo 1587492 1787287 := bstep (se 1 (by rfl) ⟨1340465, by rfl⟩ : syracuseStep 1787287 = 2680931) B2680931
theorem B3220889 : Blo 1587492 3220889 := bstep (se 2 (by rfl) ⟨1207833, by rfl⟩ : syracuseStep 3220889 = 2415667) B2415667
theorem B2147735 : Blo 1587492 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B17655331 : Blo 1587492 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B8037953 : Blo 1587492 8037953 := bstep (se 2 (by rfl) ⟨3014232, by rfl⟩ : syracuseStep 8037953 = 6028465) B6028465
theorem B3573323 : Blo 1587492 3573323 := bstep (se 1 (by rfl) ⟨2679992, by rfl⟩ : syracuseStep 3573323 = 5359985) B5359985
theorem B1787467 : Blo 1587492 1787467 := bstep (se 1 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 1787467 = 2681201) B2681201
theorem B3573377 : Blo 1587492 3573377 := bstep (se 2 (by rfl) ⟨1340016, by rfl⟩ : syracuseStep 3573377 = 2680033) B2680033
theorem B5359283 : Blo 1587492 5359283 := bstep (se 1 (by rfl) ⟨4019462, by rfl⟩ : syracuseStep 5359283 = 8038925) B8038925
theorem B1787575 : Blo 1587492 1787575 := bstep (se 1 (by rfl) ⟨1340681, by rfl⟩ : syracuseStep 1787575 = 2681363) B2681363
theorem B23226061 : Blo 1587492 23226061 := bstep (se 3 (by rfl) ⟨4354886, by rfl⟩ : syracuseStep 23226061 = 8709773) B8709773
theorem B7636697 : Blo 1587492 7636697 := bstep (se 2 (by rfl) ⟨2863761, by rfl⟩ : syracuseStep 7636697 = 5727523) B5727523
theorem B3016435 : Blo 1587492 3016435 := bstep (se 1 (by rfl) ⟨2262326, by rfl⟩ : syracuseStep 3016435 = 4524653) B4524653
theorem B6874903 : Blo 1587492 6874903 := bstep (se 1 (by rfl) ⟨5156177, by rfl⟩ : syracuseStep 6874903 = 10312355) B10312355
theorem B6031169 : Blo 1587492 6031169 := bstep (se 2 (by rfl) ⟨2261688, by rfl⟩ : syracuseStep 6031169 = 4523377) B4523377
theorem B3573593 : Blo 1587492 3573593 := bstep (se 2 (by rfl) ⟨1340097, by rfl⟩ : syracuseStep 3573593 = 2680195) B2680195
theorem B1787755 : Blo 1587492 1787755 := bstep (se 1 (by rfl) ⟨1340816, by rfl⟩ : syracuseStep 1787755 = 2681633) B2681633
theorem B2680715 : Blo 1587492 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B14698417 : Blo 1587492 14698417 := bstep (se 2 (by rfl) ⟨5511906, by rfl⟩ : syracuseStep 14698417 = 11023813) B11023813
theorem B3573683 : Blo 1587492 3573683 := bstep (se 1 (by rfl) ⟨2680262, by rfl⟩ : syracuseStep 3573683 = 5360525) B5360525
theorem B5359553 : Blo 1587492 5359553 := bstep (se 2 (by rfl) ⟨2009832, by rfl⟩ : syracuseStep 5359553 = 4019665) B4019665
theorem B3573719 : Blo 1587492 3573719 := bstep (se 1 (by rfl) ⟨2680289, by rfl⟩ : syracuseStep 3573719 = 5360579) B5360579
theorem B1787863 : Blo 1587492 1787863 := bstep (se 1 (by rfl) ⟨1340897, by rfl⟩ : syracuseStep 1787863 = 2681795) B2681795
theorem B2680843 : Blo 1587492 2680843 := bstep (se 1 (by rfl) ⟨2010632, by rfl⟩ : syracuseStep 2680843 = 4021265) B4021265
theorem B20367395 : Blo 1587492 20367395 := bstep (se 1 (by rfl) ⟨15275546, by rfl⟩ : syracuseStep 20367395 = 30551093) B30551093
theorem B4524083 : Blo 1587492 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B3573899 : Blo 1587492 3573899 := bstep (se 1 (by rfl) ⟨2680424, by rfl⟩ : syracuseStep 3573899 = 5360849) B5360849
theorem B1788043 : Blo 1587492 1788043 := bstep (se 1 (by rfl) ⟨1341032, by rfl⟩ : syracuseStep 1788043 = 2682065) B2682065
theorem B2680985 : Blo 1587492 2680985 := bstep (se 2 (by rfl) ⟨1005369, by rfl⟩ : syracuseStep 2680985 = 2010739) B2010739
theorem B3573953 : Blo 1587492 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B3016921 : Blo 1587492 3016921 := bstep (se 2 (by rfl) ⟨1131345, by rfl⟩ : syracuseStep 3016921 = 2262691) B2262691
theorem B1788151 : Blo 1587492 1788151 := bstep (se 1 (by rfl) ⟨1341113, by rfl⟩ : syracuseStep 1788151 = 2682227) B2682227
theorem B4524311 : Blo 1587492 4524311 := bstep (se 1 (by rfl) ⟨3393233, by rfl⟩ : syracuseStep 4524311 = 6786467) B6786467
theorem B2681113 : Blo 1587492 2681113 := bstep (se 2 (by rfl) ⟨1005417, by rfl⟩ : syracuseStep 2681113 = 2010835) B2010835
theorem B3574169 : Blo 1587492 3574169 := bstep (se 2 (by rfl) ⟨1340313, by rfl⟩ : syracuseStep 3574169 = 2680627) B2680627
theorem B5360093 : Blo 1587492 5360093 := bstep (se 3 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 5360093 = 2010035) B2010035
theorem B3574259 : Blo 1587492 3574259 := bstep (se 1 (by rfl) ⟨2680694, by rfl⟩ : syracuseStep 3574259 = 5361389) B5361389
theorem B3574295 : Blo 1587492 3574295 := bstep (se 1 (by rfl) ⟨2680721, by rfl⟩ : syracuseStep 3574295 = 5361443) B5361443
theorem B4524619 : Blo 1587492 4524619 := bstep (se 1 (by rfl) ⟨3393464, by rfl⟩ : syracuseStep 4524619 = 6786929) B6786929
theorem B3574475 : Blo 1587492 3574475 := bstep (se 1 (by rfl) ⟨2680856, by rfl⟩ : syracuseStep 3574475 = 5361713) B5361713
theorem B3574529 : Blo 1587492 3574529 := bstep (se 2 (by rfl) ⟨1340448, by rfl⟩ : syracuseStep 3574529 = 2680897) B2680897
theorem B3017483 : Blo 1587492 3017483 := bstep (se 1 (by rfl) ⟨2263112, by rfl⟩ : syracuseStep 3017483 = 4526225) B4526225
theorem B3394327 : Blo 1587492 3394327 := bstep (se 1 (by rfl) ⟨2545745, by rfl⟩ : syracuseStep 3394327 = 5091491) B5091491
theorem B3263257 : Blo 1587492 3263257 := bstep (se 2 (by rfl) ⟨1223721, by rfl⟩ : syracuseStep 3263257 = 2447443) B2447443
theorem B3394379 : Blo 1587492 3394379 := bstep (se 1 (by rfl) ⟨2545784, by rfl⟩ : syracuseStep 3394379 = 5091569) B5091569
theorem B4893529 : Blo 1587492 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B2681687 : Blo 1587492 2681687 := bstep (se 1 (by rfl) ⟨2011265, by rfl⟩ : syracuseStep 2681687 = 4022531) B4022531
theorem B4524893 : Blo 1587492 4524893 := bstep (se 3 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 4524893 = 1696835) B1696835
theorem B2861975 : Blo 1587492 2861975 := bstep (se 1 (by rfl) ⟨2146481, by rfl⟩ : syracuseStep 2861975 = 4292963) B4292963
theorem B12069809 : Blo 1587492 12069809 := bstep (se 2 (by rfl) ⟨4526178, by rfl⟩ : syracuseStep 12069809 = 9052357) B9052357
theorem B2681815 : Blo 1587492 2681815 := bstep (se 1 (by rfl) ⟨2011361, by rfl⟩ : syracuseStep 2681815 = 4022723) B4022723
theorem B3574745 : Blo 1587492 3574745 := bstep (se 2 (by rfl) ⟨1340529, by rfl⟩ : syracuseStep 3574745 = 2681059) B2681059
theorem B3574835 : Blo 1587492 3574835 := bstep (se 1 (by rfl) ⟨2681126, by rfl⟩ : syracuseStep 3574835 = 5362253) B5362253
theorem B2010187 : Blo 1587492 2010187 := bstep (se 1 (by rfl) ⟨1507640, by rfl⟩ : syracuseStep 2010187 = 3015281) B3015281
theorem B3574871 : Blo 1587492 3574871 := bstep (se 1 (by rfl) ⟨2681153, by rfl⟩ : syracuseStep 3574871 = 5362307) B5362307
theorem B15469699 : Blo 1587492 15469699 := bstep (se 1 (by rfl) ⟨11602274, by rfl⟩ : syracuseStep 15469699 = 23204549) B23204549
theorem B6786193 : Blo 1587492 6786193 := bstep (se 2 (by rfl) ⟨2544822, by rfl⟩ : syracuseStep 6786193 = 5089645) B5089645
theorem B13569241 : Blo 1587492 13569241 := bstep (se 2 (by rfl) ⟨5088465, by rfl⟩ : syracuseStep 13569241 = 10176931) B10176931
theorem B3575051 : Blo 1587492 3575051 := bstep (se 1 (by rfl) ⟨2681288, by rfl⟩ : syracuseStep 3575051 = 5362577) B5362577
theorem B6032657 : Blo 1587492 6032657 := bstep (se 2 (by rfl) ⟨2262246, by rfl⟩ : syracuseStep 6032657 = 4524493) B4524493
theorem B3575105 : Blo 1587492 3575105 := bstep (se 2 (by rfl) ⟨1340664, by rfl⟩ : syracuseStep 3575105 = 2681329) B2681329
theorem B2862487 : Blo 1587492 2862487 := bstep (se 1 (by rfl) ⟨2146865, by rfl⟩ : syracuseStep 2862487 = 4293731) B4293731
theorem B8039897 : Blo 1587492 8039897 := bstep (se 2 (by rfl) ⟨3014961, by rfl⟩ : syracuseStep 8039897 = 6029923) B6029923
theorem B3575321 : Blo 1587492 3575321 := bstep (se 2 (by rfl) ⟨1340745, by rfl⟩ : syracuseStep 3575321 = 2681491) B2681491
theorem B5361227 : Blo 1587492 5361227 := bstep (se 1 (by rfl) ⟨4020920, by rfl⟩ : syracuseStep 5361227 = 8041841) B8041841
theorem B3575411 : Blo 1587492 3575411 := bstep (se 1 (by rfl) ⟨2681558, by rfl⟩ : syracuseStep 3575411 = 5363117) B5363117
theorem B3575447 : Blo 1587492 3575447 := bstep (se 1 (by rfl) ⟨2681585, by rfl⟩ : syracuseStep 3575447 = 5363171) B5363171
theorem B8589017 : Blo 1587492 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B6033113 : Blo 1587492 6033113 := bstep (se 2 (by rfl) ⟨2262417, by rfl⟩ : syracuseStep 6033113 = 4524835) B4524835
theorem B13577989 : Blo 1587492 13577989 := bstep (se 4 (by rfl) ⟨1272936, by rfl⟩ : syracuseStep 13577989 = 2545873) B2545873
theorem B3575627 : Blo 1587492 3575627 := bstep (se 1 (by rfl) ⟨2681720, by rfl⟩ : syracuseStep 3575627 = 5363441) B5363441
theorem B5361497 : Blo 1587492 5361497 := bstep (se 2 (by rfl) ⟨2010561, by rfl⟩ : syracuseStep 5361497 = 4021123) B4021123
theorem B3575681 : Blo 1587492 3575681 := bstep (se 2 (by rfl) ⟨1340880, by rfl⟩ : syracuseStep 3575681 = 2681761) B2681761
theorem B11612035 : Blo 1587492 11612035 := bstep (se 1 (by rfl) ⟨8709026, by rfl⟩ : syracuseStep 11612035 = 17418053) B17418053
theorem B6033325 : Blo 1587492 6033325 := bstep (se 3 (by rfl) ⟨1131248, by rfl⟩ : syracuseStep 6033325 = 2262497) B2262497
theorem B28987409 : Blo 1587492 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B2011159 : Blo 1587492 2011159 := bstep (se 1 (by rfl) ⟨1508369, by rfl⟩ : syracuseStep 2011159 = 3016739) B3016739
theorem B3575897 : Blo 1587492 3575897 := bstep (se 2 (by rfl) ⟨1340961, by rfl⟩ : syracuseStep 3575897 = 2681923) B2681923
theorem B13570199 : Blo 1587492 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B4075699 : Blo 1587492 4075699 := bstep (se 1 (by rfl) ⟨3056774, by rfl⟩ : syracuseStep 4075699 = 6113549) B6113549
theorem B3575987 : Blo 1587492 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B4018369 : Blo 1587492 4018369 := bstep (se 2 (by rfl) ⟨1506888, by rfl⟩ : syracuseStep 4018369 = 3013777) B3013777
theorem B3576023 : Blo 1587492 3576023 := bstep (se 1 (by rfl) ⟨2682017, by rfl⟩ : syracuseStep 3576023 = 5364035) B5364035
theorem B10178777 : Blo 1587492 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B6033629 : Blo 1587492 6033629 := bstep (se 3 (by rfl) ⟨1131305, by rfl⟩ : syracuseStep 6033629 = 2262611) B2262611
theorem B4075865 : Blo 1587492 4075865 := bstep (se 2 (by rfl) ⟨1528449, by rfl⟩ : syracuseStep 4075865 = 3056899) B3056899
theorem B3576203 : Blo 1587492 3576203 := bstep (se 1 (by rfl) ⟨2682152, by rfl⟩ : syracuseStep 3576203 = 5364305) B5364305
theorem B2544023 : Blo 1587492 2544023 := bstep (se 1 (by rfl) ⟨1908017, by rfl⟩ : syracuseStep 2544023 = 3816035) B3816035
theorem B3576257 : Blo 1587492 3576257 := bstep (se 2 (by rfl) ⟨1341096, by rfl⟩ : syracuseStep 3576257 = 2682193) B2682193
theorem B13570577 : Blo 1587492 13570577 := bstep (se 2 (by rfl) ⟨5088966, by rfl⟩ : syracuseStep 13570577 = 10177933) B10177933
theorem B5362199 : Blo 1587492 5362199 := bstep (se 1 (by rfl) ⟨4021649, by rfl⟩ : syracuseStep 5362199 = 8043299) B8043299
theorem B11448877 : Blo 1587492 11448877 := bstep (se 3 (by rfl) ⟨2146664, by rfl⟩ : syracuseStep 11448877 = 4293329) B4293329
theorem B11457125 : Blo 1587492 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B1610347 : Blo 1587492 1610347 := bstep (se 1 (by rfl) ⟨1207760, by rfl⟩ : syracuseStep 1610347 = 2415521) B2415521
theorem B4018967 : Blo 1587492 4018967 := bstep (se 1 (by rfl) ⟨3014225, by rfl⟩ : syracuseStep 4018967 = 6028451) B6028451
theorem B5722969 : Blo 1587492 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B27497393 : Blo 1587492 27497393 := bstep (se 2 (by rfl) ⟨10311522, by rfl⟩ : syracuseStep 27497393 = 20623045) B20623045
theorem B51499955 : Blo 1587492 51499955 := bstep (se 1 (by rfl) ⟨38624966, by rfl⟩ : syracuseStep 51499955 = 77249933) B77249933
theorem B2864065 : Blo 1587492 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B5723083 : Blo 1587492 5723083 := bstep (se 1 (by rfl) ⟨4292312, by rfl⟩ : syracuseStep 5723083 = 8584625) B8584625
theorem B65205269 : Blo 1587492 65205269 := bstep (se 6 (by rfl) ⟨1528248, by rfl⟩ : syracuseStep 65205269 = 3056497) B3056497
theorem B8041517 : Blo 1587492 8041517 := bstep (se 3 (by rfl) ⟨1507784, by rfl⟩ : syracuseStep 8041517 = 3015569) B3015569
theorem B5362739 : Blo 1587492 5362739 := bstep (se 1 (by rfl) ⟨4022054, by rfl⟩ : syracuseStep 5362739 = 8044109) B8044109
theorem B4896065 : Blo 1587492 4896065 := bstep (se 2 (by rfl) ⟨1836024, by rfl⟩ : syracuseStep 4896065 = 3672049) B3672049
theorem B5363009 : Blo 1587492 5363009 := bstep (se 2 (by rfl) ⟨2011128, by rfl⟩ : syracuseStep 5363009 = 4022257) B4022257
theorem B2381273 : Blo 1587492 2381273 := bstep (se 2 (by rfl) ⟨892977, by rfl⟩ : syracuseStep 2381273 = 1785955) B1785955
theorem B6788569 : Blo 1587492 6788569 := bstep (se 2 (by rfl) ⟨2545713, by rfl⟩ : syracuseStep 6788569 = 5091427) B5091427
theorem B9655853 : Blo 1587492 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B4019777 : Blo 1587492 4019777 := bstep (se 2 (by rfl) ⟨1507416, by rfl⟩ : syracuseStep 4019777 = 3014833) B3014833
theorem B2381387 : Blo 1587492 2381387 := bstep (se 1 (by rfl) ⟨1786040, by rfl⟩ : syracuseStep 2381387 = 3572081) B3572081
theorem B2381399 : Blo 1587492 2381399 := bstep (se 1 (by rfl) ⟨1786049, by rfl⟩ : syracuseStep 2381399 = 3572099) B3572099
theorem B48920195 : Blo 1587492 48920195 := bstep (se 1 (by rfl) ⟨36690146, by rfl⟩ : syracuseStep 48920195 = 73380293) B73380293
theorem B43488899 : Blo 1587492 43488899 := bstep (se 1 (by rfl) ⟨32616674, by rfl⟩ : syracuseStep 43488899 = 65233349) B65233349
theorem B3815063 : Blo 1587492 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B2381465 : Blo 1587492 2381465 := bstep (se 2 (by rfl) ⟨893049, by rfl⟩ : syracuseStep 2381465 = 1786099) B1786099
theorem B2381579 : Blo 1587492 2381579 := bstep (se 1 (by rfl) ⟨1786184, by rfl⟩ : syracuseStep 2381579 = 3572369) B3572369
theorem B10319633 : Blo 1587492 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B2381591 : Blo 1587492 2381591 := bstep (se 1 (by rfl) ⟨1786193, by rfl⟩ : syracuseStep 2381591 = 3572387) B3572387
theorem B5805847 : Blo 1587492 5805847 := bstep (se 1 (by rfl) ⟨4354385, by rfl⟩ : syracuseStep 5805847 = 8708771) B8708771
theorem B15267629 : Blo 1587492 15267629 := bstep (se 3 (by rfl) ⟨2862680, by rfl⟩ : syracuseStep 15267629 = 5725361) B5725361
theorem B10180417 : Blo 1587492 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B2381657 : Blo 1587492 2381657 := bstep (se 2 (by rfl) ⟨893121, by rfl⟩ : syracuseStep 2381657 = 1786243) B1786243
theorem B5363549 : Blo 1587492 5363549 := bstep (se 3 (by rfl) ⟨1005665, by rfl⟩ : syracuseStep 5363549 = 2011331) B2011331
theorem B34363237 : Blo 1587492 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B2381771 : Blo 1587492 2381771 := bstep (se 1 (by rfl) ⟨1786328, by rfl⟩ : syracuseStep 2381771 = 3572657) B3572657
theorem B2381783 : Blo 1587492 2381783 := bstep (se 1 (by rfl) ⟨1786337, by rfl⟩ : syracuseStep 2381783 = 3572675) B3572675
theorem B17168345 : Blo 1587492 17168345 := bstep (se 2 (by rfl) ⟨6438129, by rfl⟩ : syracuseStep 17168345 = 12876259) B12876259
theorem B2381849 : Blo 1587492 2381849 := bstep (se 2 (by rfl) ⟨893193, by rfl⟩ : syracuseStep 2381849 = 1786387) B1786387
theorem B4773953 : Blo 1587492 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B4020313 : Blo 1587492 4020313 := bstep (se 2 (by rfl) ⟨1507617, by rfl⟩ : syracuseStep 4020313 = 3015235) B3015235
theorem B16300163 : Blo 1587492 16300163 := bstep (se 1 (by rfl) ⟨12225122, by rfl⟩ : syracuseStep 16300163 = 24450245) B24450245
theorem B2381963 : Blo 1587492 2381963 := bstep (se 1 (by rfl) ⟨1786472, by rfl⟩ : syracuseStep 2381963 = 3572945) B3572945
theorem B2381975 : Blo 1587492 2381975 := bstep (se 1 (by rfl) ⟨1786481, by rfl⟩ : syracuseStep 2381975 = 3572963) B3572963
theorem B2382041 : Blo 1587492 2382041 := bstep (se 2 (by rfl) ⟨893265, by rfl⟩ : syracuseStep 2382041 = 1786531) B1786531
theorem B1587499 : Blo 1587492 1587499 := bstep (se 1 (by rfl) ⟨1190624, by rfl⟩ : syracuseStep 1587499 = 2381249) B2381249
theorem B1587511 : Blo 1587492 1587511 := bstep (se 1 (by rfl) ⟨1190633, by rfl⟩ : syracuseStep 1587511 = 2381267) B2381267
theorem B2382155 : Blo 1587492 2382155 := bstep (se 1 (by rfl) ⟨1786616, by rfl⟩ : syracuseStep 2382155 = 3573233) B3573233
theorem B1587531 : Blo 1587492 1587531 := bstep (se 1 (by rfl) ⟨1190648, by rfl⟩ : syracuseStep 1587531 = 2381297) B2381297
theorem B1587543 : Blo 1587492 1587543 := bstep (se 1 (by rfl) ⟨1190657, by rfl⟩ : syracuseStep 1587543 = 2381315) B2381315
theorem B2382167 : Blo 1587492 2382167 := bstep (se 1 (by rfl) ⟨1786625, by rfl⟩ : syracuseStep 2382167 = 3573251) B3573251
theorem B1587563 : Blo 1587492 1587563 := bstep (se 1 (by rfl) ⟨1190672, by rfl⟩ : syracuseStep 1587563 = 2381345) B2381345
theorem B1587575 : Blo 1587492 1587575 := bstep (se 1 (by rfl) ⟨1190681, by rfl⟩ : syracuseStep 1587575 = 2381363) B2381363
theorem B1587595 : Blo 1587492 1587595 := bstep (se 1 (by rfl) ⟨1190696, by rfl⟩ : syracuseStep 1587595 = 2381393) B2381393
theorem B1587607 : Blo 1587492 1587607 := bstep (se 1 (by rfl) ⟨1190705, by rfl⟩ : syracuseStep 1587607 = 2381411) B2381411
theorem B2382233 : Blo 1587492 2382233 := bstep (se 2 (by rfl) ⟨893337, by rfl⟩ : syracuseStep 2382233 = 1786675) B1786675
theorem B1587627 : Blo 1587492 1587627 := bstep (se 1 (by rfl) ⟨1190720, by rfl⟩ : syracuseStep 1587627 = 2381441) B2381441
theorem B1587639 : Blo 1587492 1587639 := bstep (se 1 (by rfl) ⟨1190729, by rfl⟩ : syracuseStep 1587639 = 2381459) B2381459
theorem B1587659 : Blo 1587492 1587659 := bstep (se 1 (by rfl) ⟨1190744, by rfl⟩ : syracuseStep 1587659 = 2381489) B2381489
theorem B1587671 : Blo 1587492 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B1718743 : Blo 1587492 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B1587691 : Blo 1587492 1587691 := bstep (se 1 (by rfl) ⟨1190768, by rfl⟩ : syracuseStep 1587691 = 2381537) B2381537
theorem B1587703 : Blo 1587492 1587703 := bstep (se 1 (by rfl) ⟨1190777, by rfl⟩ : syracuseStep 1587703 = 2381555) B2381555
theorem B1587723 : Blo 1587492 1587723 := bstep (se 1 (by rfl) ⟨1190792, by rfl⟩ : syracuseStep 1587723 = 2381585) B2381585
theorem B2382347 : Blo 1587492 2382347 := bstep (se 1 (by rfl) ⟨1786760, by rfl⟩ : syracuseStep 2382347 = 3573521) B3573521
theorem B1587735 : Blo 1587492 1587735 := bstep (se 1 (by rfl) ⟨1190801, by rfl⟩ : syracuseStep 1587735 = 2381603) B2381603
theorem B2382359 : Blo 1587492 2382359 := bstep (se 1 (by rfl) ⟨1786769, by rfl⟩ : syracuseStep 2382359 = 3573539) B3573539
theorem B1587755 : Blo 1587492 1587755 := bstep (se 1 (by rfl) ⟨1190816, by rfl⟩ : syracuseStep 1587755 = 2381633) B2381633
theorem B2906675 : Blo 1587492 2906675 := bstep (se 1 (by rfl) ⟨2180006, by rfl⟩ : syracuseStep 2906675 = 4360013) B4360013
theorem B1587767 : Blo 1587492 1587767 := bstep (se 1 (by rfl) ⟨1190825, by rfl⟩ : syracuseStep 1587767 = 2381651) B2381651
theorem B1587787 : Blo 1587492 1587787 := bstep (se 1 (by rfl) ⟨1190840, by rfl⟩ : syracuseStep 1587787 = 2381681) B2381681
theorem B1587799 : Blo 1587492 1587799 := bstep (se 1 (by rfl) ⟨1190849, by rfl⟩ : syracuseStep 1587799 = 2381699) B2381699
theorem B2382425 : Blo 1587492 2382425 := bstep (se 2 (by rfl) ⟨893409, by rfl⟩ : syracuseStep 2382425 = 1786819) B1786819
theorem B9050717 : Blo 1587492 9050717 := bstep (se 3 (by rfl) ⟨1697009, by rfl⟩ : syracuseStep 9050717 = 3394019) B3394019
theorem B1587819 : Blo 1587492 1587819 := bstep (se 1 (by rfl) ⟨1190864, by rfl⟩ : syracuseStep 1587819 = 2381729) B2381729
theorem B1587831 : Blo 1587492 1587831 := bstep (se 1 (by rfl) ⟨1190873, by rfl⟩ : syracuseStep 1587831 = 2381747) B2381747
theorem B1587851 : Blo 1587492 1587851 := bstep (se 1 (by rfl) ⟨1190888, by rfl⟩ : syracuseStep 1587851 = 2381777) B2381777
theorem B1587863 : Blo 1587492 1587863 := bstep (se 1 (by rfl) ⟨1190897, by rfl⟩ : syracuseStep 1587863 = 2381795) B2381795
theorem B1587883 : Blo 1587492 1587883 := bstep (se 1 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 1587883 = 2381825) B2381825
theorem B1587895 : Blo 1587492 1587895 := bstep (se 1 (by rfl) ⟨1190921, by rfl⟩ : syracuseStep 1587895 = 2381843) B2381843
theorem B6027979 : Blo 1587492 6027979 := bstep (se 1 (by rfl) ⟨4520984, by rfl⟩ : syracuseStep 6027979 = 9041969) B9041969
theorem B1587915 : Blo 1587492 1587915 := bstep (se 1 (by rfl) ⟨1190936, by rfl⟩ : syracuseStep 1587915 = 2381873) B2381873
theorem B2382539 : Blo 1587492 2382539 := bstep (se 1 (by rfl) ⟨1786904, by rfl⟩ : syracuseStep 2382539 = 3573809) B3573809
theorem B1587927 : Blo 1587492 1587927 := bstep (se 1 (by rfl) ⟨1190945, by rfl⟩ : syracuseStep 1587927 = 2381891) B2381891
theorem B2382551 : Blo 1587492 2382551 := bstep (se 1 (by rfl) ⟨1786913, by rfl⟩ : syracuseStep 2382551 = 3573827) B3573827
theorem B1587947 : Blo 1587492 1587947 := bstep (se 1 (by rfl) ⟨1190960, by rfl⟩ : syracuseStep 1587947 = 2381921) B2381921
theorem B25770737 : Blo 1587492 25770737 := bstep (se 2 (by rfl) ⟨9664026, by rfl⟩ : syracuseStep 25770737 = 19328053) B19328053
theorem B1587959 : Blo 1587492 1587959 := bstep (se 1 (by rfl) ⟨1190969, by rfl⟩ : syracuseStep 1587959 = 2381939) B2381939
theorem B1587979 : Blo 1587492 1587979 := bstep (se 1 (by rfl) ⟨1190984, by rfl⟩ : syracuseStep 1587979 = 2381969) B2381969
theorem B1587991 : Blo 1587492 1587991 := bstep (se 1 (by rfl) ⟨1190993, by rfl⟩ : syracuseStep 1587991 = 2381987) B2381987
theorem B2382617 : Blo 1587492 2382617 := bstep (se 2 (by rfl) ⟨893481, by rfl⟩ : syracuseStep 2382617 = 1786963) B1786963
theorem B1588011 : Blo 1587492 1588011 := bstep (se 1 (by rfl) ⟨1191008, by rfl⟩ : syracuseStep 1588011 = 2382017) B2382017
theorem B1588023 : Blo 1587492 1588023 := bstep (se 1 (by rfl) ⟨1191017, by rfl⟩ : syracuseStep 1588023 = 2382035) B2382035
theorem B1588043 : Blo 1587492 1588043 := bstep (se 1 (by rfl) ⟨1191032, by rfl⟩ : syracuseStep 1588043 = 2382065) B2382065
theorem B1588055 : Blo 1587492 1588055 := bstep (se 1 (by rfl) ⟨1191041, by rfl⟩ : syracuseStep 1588055 = 2382083) B2382083
theorem B1588075 : Blo 1587492 1588075 := bstep (se 1 (by rfl) ⟨1191056, by rfl⟩ : syracuseStep 1588075 = 2382113) B2382113
theorem B1588087 : Blo 1587492 1588087 := bstep (se 1 (by rfl) ⟨1191065, by rfl⟩ : syracuseStep 1588087 = 2382131) B2382131
theorem B1588107 : Blo 1587492 1588107 := bstep (se 1 (by rfl) ⟨1191080, by rfl⟩ : syracuseStep 1588107 = 2382161) B2382161
theorem B2382731 : Blo 1587492 2382731 := bstep (se 1 (by rfl) ⟨1787048, by rfl⟩ : syracuseStep 2382731 = 3574097) B3574097
theorem B1588119 : Blo 1587492 1588119 := bstep (se 1 (by rfl) ⟨1191089, by rfl⟩ : syracuseStep 1588119 = 2382179) B2382179
theorem B2382743 : Blo 1587492 2382743 := bstep (se 1 (by rfl) ⟨1787057, by rfl⟩ : syracuseStep 2382743 = 3574115) B3574115
theorem B1588139 : Blo 1587492 1588139 := bstep (se 1 (by rfl) ⟨1191104, by rfl⟩ : syracuseStep 1588139 = 2382209) B2382209
theorem B1588151 : Blo 1587492 1588151 := bstep (se 1 (by rfl) ⟨1191113, by rfl⟩ : syracuseStep 1588151 = 2382227) B2382227
theorem B1588171 : Blo 1587492 1588171 := bstep (se 1 (by rfl) ⟨1191128, by rfl⟩ : syracuseStep 1588171 = 2382257) B2382257
theorem B1588183 : Blo 1587492 1588183 := bstep (se 1 (by rfl) ⟨1191137, by rfl⟩ : syracuseStep 1588183 = 2382275) B2382275
theorem B2382809 : Blo 1587492 2382809 := bstep (se 2 (by rfl) ⟨893553, by rfl⟩ : syracuseStep 2382809 = 1787107) B1787107
theorem B6028253 : Blo 1587492 6028253 := bstep (se 3 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 6028253 = 2260595) B2260595
theorem B1588203 : Blo 1587492 1588203 := bstep (se 1 (by rfl) ⟨1191152, by rfl⟩ : syracuseStep 1588203 = 2382305) B2382305
theorem B1588215 : Blo 1587492 1588215 := bstep (se 1 (by rfl) ⟨1191161, by rfl⟩ : syracuseStep 1588215 = 2382323) B2382323
theorem B1588235 : Blo 1587492 1588235 := bstep (se 1 (by rfl) ⟨1191176, by rfl⟩ : syracuseStep 1588235 = 2382353) B2382353
theorem B1588247 : Blo 1587492 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B1588267 : Blo 1587492 1588267 := bstep (se 1 (by rfl) ⟨1191200, by rfl⟩ : syracuseStep 1588267 = 2382401) B2382401
theorem B1588279 : Blo 1587492 1588279 := bstep (se 1 (by rfl) ⟨1191209, by rfl⟩ : syracuseStep 1588279 = 2382419) B2382419
theorem B1588299 : Blo 1587492 1588299 := bstep (se 1 (by rfl) ⟨1191224, by rfl⟩ : syracuseStep 1588299 = 2382449) B2382449
theorem B2382923 : Blo 1587492 2382923 := bstep (se 1 (by rfl) ⟨1787192, by rfl⟩ : syracuseStep 2382923 = 3574385) B3574385
theorem B1588311 : Blo 1587492 1588311 := bstep (se 1 (by rfl) ⟨1191233, by rfl⟩ : syracuseStep 1588311 = 2382467) B2382467
theorem B2382935 : Blo 1587492 2382935 := bstep (se 1 (by rfl) ⟨1787201, by rfl⟩ : syracuseStep 2382935 = 3574403) B3574403
theorem B1588331 : Blo 1587492 1588331 := bstep (se 1 (by rfl) ⟨1191248, by rfl⟩ : syracuseStep 1588331 = 2382497) B2382497
theorem B1588343 : Blo 1587492 1588343 := bstep (se 1 (by rfl) ⟨1191257, by rfl⟩ : syracuseStep 1588343 = 2382515) B2382515
theorem B1588363 : Blo 1587492 1588363 := bstep (se 1 (by rfl) ⟨1191272, by rfl⟩ : syracuseStep 1588363 = 2382545) B2382545
theorem B1588375 : Blo 1587492 1588375 := bstep (se 1 (by rfl) ⟨1191281, by rfl⟩ : syracuseStep 1588375 = 2382563) B2382563
theorem B2383001 : Blo 1587492 2383001 := bstep (se 2 (by rfl) ⟨893625, by rfl⟩ : syracuseStep 2383001 = 1787251) B1787251
theorem B1588395 : Blo 1587492 1588395 := bstep (se 1 (by rfl) ⟨1191296, by rfl⟩ : syracuseStep 1588395 = 2382593) B2382593
theorem B4021427 : Blo 1587492 4021427 := bstep (se 1 (by rfl) ⟨3016070, by rfl⟩ : syracuseStep 4021427 = 6032141) B6032141
theorem B1588407 : Blo 1587492 1588407 := bstep (se 1 (by rfl) ⟨1191305, by rfl⟩ : syracuseStep 1588407 = 2382611) B2382611
theorem B1588427 : Blo 1587492 1588427 := bstep (se 1 (by rfl) ⟨1191320, by rfl⟩ : syracuseStep 1588427 = 2382641) B2382641
theorem B1588439 : Blo 1587492 1588439 := bstep (se 1 (by rfl) ⟨1191329, by rfl⟩ : syracuseStep 1588439 = 2382659) B2382659
theorem B6528221 : Blo 1587492 6528221 := bstep (se 3 (by rfl) ⟨1224041, by rfl⟩ : syracuseStep 6528221 = 2448083) B2448083
theorem B1588459 : Blo 1587492 1588459 := bstep (se 1 (by rfl) ⟨1191344, by rfl⟩ : syracuseStep 1588459 = 2382689) B2382689
theorem B1588471 : Blo 1587492 1588471 := bstep (se 1 (by rfl) ⟨1191353, by rfl⟩ : syracuseStep 1588471 = 2382707) B2382707
theorem B23223557 : Blo 1587492 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B3390731 : Blo 1587492 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B1588491 : Blo 1587492 1588491 := bstep (se 1 (by rfl) ⟨1191368, by rfl⟩ : syracuseStep 1588491 = 2382737) B2382737
theorem B2383115 : Blo 1587492 2383115 := bstep (se 1 (by rfl) ⟨1787336, by rfl⟩ : syracuseStep 2383115 = 3574673) B3574673
theorem B1588503 : Blo 1587492 1588503 := bstep (se 1 (by rfl) ⟨1191377, by rfl⟩ : syracuseStep 1588503 = 2382755) B2382755
theorem B2383127 : Blo 1587492 2383127 := bstep (se 1 (by rfl) ⟨1787345, by rfl⟩ : syracuseStep 2383127 = 3574691) B3574691
theorem B1588523 : Blo 1587492 1588523 := bstep (se 1 (by rfl) ⟨1191392, by rfl⟩ : syracuseStep 1588523 = 2382785) B2382785
theorem B1588535 : Blo 1587492 1588535 := bstep (se 1 (by rfl) ⟨1191401, by rfl⟩ : syracuseStep 1588535 = 2382803) B2382803
theorem B1588555 : Blo 1587492 1588555 := bstep (se 1 (by rfl) ⟨1191416, by rfl⟩ : syracuseStep 1588555 = 2382833) B2382833
theorem B1908055 : Blo 1587492 1908055 := bstep (se 1 (by rfl) ⟨1431041, by rfl⟩ : syracuseStep 1908055 = 2862083) B2862083
theorem B1588567 : Blo 1587492 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B2383193 : Blo 1587492 2383193 := bstep (se 2 (by rfl) ⟨893697, by rfl⟩ : syracuseStep 2383193 = 1787395) B1787395
theorem B1588587 : Blo 1587492 1588587 := bstep (se 1 (by rfl) ⟨1191440, by rfl⟩ : syracuseStep 1588587 = 2382881) B2382881
theorem B1588599 : Blo 1587492 1588599 := bstep (se 1 (by rfl) ⟨1191449, by rfl⟩ : syracuseStep 1588599 = 2382899) B2382899
theorem B6438275 : Blo 1587492 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B1588619 : Blo 1587492 1588619 := bstep (se 1 (by rfl) ⟨1191464, by rfl⟩ : syracuseStep 1588619 = 2382929) B2382929
theorem B1588631 : Blo 1587492 1588631 := bstep (se 1 (by rfl) ⟨1191473, by rfl⟩ : syracuseStep 1588631 = 2382947) B2382947
theorem B1588651 : Blo 1587492 1588651 := bstep (se 1 (by rfl) ⟨1191488, by rfl⟩ : syracuseStep 1588651 = 2382977) B2382977
theorem B4521395 : Blo 1587492 4521395 := bstep (se 1 (by rfl) ⟨3391046, by rfl⟩ : syracuseStep 4521395 = 6782093) B6782093
theorem B1588663 : Blo 1587492 1588663 := bstep (se 1 (by rfl) ⟨1191497, by rfl⟩ : syracuseStep 1588663 = 2382995) B2382995
theorem B3014081 : Blo 1587492 3014081 := bstep (se 2 (by rfl) ⟨1130280, by rfl⟩ : syracuseStep 3014081 = 2260561) B2260561
theorem B1588683 : Blo 1587492 1588683 := bstep (se 1 (by rfl) ⟨1191512, by rfl⟩ : syracuseStep 1588683 = 2383025) B2383025
theorem B2383307 : Blo 1587492 2383307 := bstep (se 1 (by rfl) ⟨1787480, by rfl⟩ : syracuseStep 2383307 = 3574961) B3574961
theorem B1588695 : Blo 1587492 1588695 := bstep (se 1 (by rfl) ⟨1191521, by rfl⟩ : syracuseStep 1588695 = 2383043) B2383043
theorem B2383319 : Blo 1587492 2383319 := bstep (se 1 (by rfl) ⟨1787489, by rfl⟩ : syracuseStep 2383319 = 3574979) B3574979
theorem B4021721 : Blo 1587492 4021721 := bstep (se 2 (by rfl) ⟨1508145, by rfl⟩ : syracuseStep 4021721 = 3016291) B3016291
theorem B1588715 : Blo 1587492 1588715 := bstep (se 1 (by rfl) ⟨1191536, by rfl⟩ : syracuseStep 1588715 = 2383073) B2383073
theorem B1588727 : Blo 1587492 1588727 := bstep (se 1 (by rfl) ⟨1191545, by rfl⟩ : syracuseStep 1588727 = 2383091) B2383091
theorem B1588747 : Blo 1587492 1588747 := bstep (se 1 (by rfl) ⟨1191560, by rfl⟩ : syracuseStep 1588747 = 2383121) B2383121
theorem B4292119 : Blo 1587492 4292119 := bstep (se 1 (by rfl) ⟨3219089, by rfl⟩ : syracuseStep 4292119 = 6438179) B6438179
theorem B1588759 : Blo 1587492 1588759 := bstep (se 1 (by rfl) ⟨1191569, by rfl⟩ : syracuseStep 1588759 = 2383139) B2383139
theorem B2383385 : Blo 1587492 2383385 := bstep (se 2 (by rfl) ⟨893769, by rfl⟩ : syracuseStep 2383385 = 1787539) B1787539
theorem B1588779 : Blo 1587492 1588779 := bstep (se 1 (by rfl) ⟨1191584, by rfl⟩ : syracuseStep 1588779 = 2383169) B2383169
theorem B1588791 : Blo 1587492 1588791 := bstep (se 1 (by rfl) ⟨1191593, by rfl⟩ : syracuseStep 1588791 = 2383187) B2383187
theorem B1588811 : Blo 1587492 1588811 := bstep (se 1 (by rfl) ⟨1191608, by rfl⟩ : syracuseStep 1588811 = 2383217) B2383217
theorem B1588823 : Blo 1587492 1588823 := bstep (se 1 (by rfl) ⟨1191617, by rfl⟩ : syracuseStep 1588823 = 2383235) B2383235
theorem B7241309 : Blo 1587492 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B1588843 : Blo 1587492 1588843 := bstep (se 1 (by rfl) ⟨1191632, by rfl⟩ : syracuseStep 1588843 = 2383265) B2383265
theorem B1588855 : Blo 1587492 1588855 := bstep (se 1 (by rfl) ⟨1191641, by rfl⟩ : syracuseStep 1588855 = 2383283) B2383283
theorem B1588875 : Blo 1587492 1588875 := bstep (se 1 (by rfl) ⟨1191656, by rfl⟩ : syracuseStep 1588875 = 2383313) B2383313
theorem B2383499 : Blo 1587492 2383499 := bstep (se 1 (by rfl) ⟨1787624, by rfl⟩ : syracuseStep 2383499 = 3575249) B3575249
theorem B6028951 : Blo 1587492 6028951 := bstep (se 1 (by rfl) ⟨4521713, by rfl⟩ : syracuseStep 6028951 = 9043427) B9043427
theorem B1588887 : Blo 1587492 1588887 := bstep (se 1 (by rfl) ⟨1191665, by rfl⟩ : syracuseStep 1588887 = 2383331) B2383331
theorem B2383511 : Blo 1587492 2383511 := bstep (se 1 (by rfl) ⟨1787633, by rfl⟩ : syracuseStep 2383511 = 3575267) B3575267
theorem B1588907 : Blo 1587492 1588907 := bstep (se 1 (by rfl) ⟨1191680, by rfl⟩ : syracuseStep 1588907 = 2383361) B2383361
theorem B1588919 : Blo 1587492 1588919 := bstep (se 1 (by rfl) ⟨1191689, by rfl⟩ : syracuseStep 1588919 = 2383379) B2383379
theorem B3014347 : Blo 1587492 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B1588939 : Blo 1587492 1588939 := bstep (se 1 (by rfl) ⟨1191704, by rfl⟩ : syracuseStep 1588939 = 2383409) B2383409
theorem B1588951 : Blo 1587492 1588951 := bstep (se 1 (by rfl) ⟨1191713, by rfl⟩ : syracuseStep 1588951 = 2383427) B2383427
theorem B2383577 : Blo 1587492 2383577 := bstep (se 2 (by rfl) ⟨893841, by rfl⟩ : syracuseStep 2383577 = 1787683) B1787683
theorem B1588971 : Blo 1587492 1588971 := bstep (se 1 (by rfl) ⟨1191728, by rfl⟩ : syracuseStep 1588971 = 2383457) B2383457
theorem B1588983 : Blo 1587492 1588983 := bstep (se 1 (by rfl) ⟨1191737, by rfl⟩ : syracuseStep 1588983 = 2383475) B2383475
theorem B1589003 : Blo 1587492 1589003 := bstep (se 1 (by rfl) ⟨1191752, by rfl⟩ : syracuseStep 1589003 = 2383505) B2383505
theorem B1589015 : Blo 1587492 1589015 := bstep (se 1 (by rfl) ⟨1191761, by rfl⟩ : syracuseStep 1589015 = 2383523) B2383523
theorem B1589035 : Blo 1587492 1589035 := bstep (se 1 (by rfl) ⟨1191776, by rfl⟩ : syracuseStep 1589035 = 2383553) B2383553
theorem B1589047 : Blo 1587492 1589047 := bstep (se 1 (by rfl) ⟨1191785, by rfl⟩ : syracuseStep 1589047 = 2383571) B2383571
theorem B1589067 : Blo 1587492 1589067 := bstep (se 1 (by rfl) ⟨1191800, by rfl⟩ : syracuseStep 1589067 = 2383601) B2383601
theorem B2383691 : Blo 1587492 2383691 := bstep (se 1 (by rfl) ⟨1787768, by rfl⟩ : syracuseStep 2383691 = 3575537) B3575537
theorem B1589079 : Blo 1587492 1589079 := bstep (se 1 (by rfl) ⟨1191809, by rfl⟩ : syracuseStep 1589079 = 2383619) B2383619
theorem B2383703 : Blo 1587492 2383703 := bstep (se 1 (by rfl) ⟨1787777, by rfl⟩ : syracuseStep 2383703 = 3575555) B3575555
theorem B1589099 : Blo 1587492 1589099 := bstep (se 1 (by rfl) ⟨1191824, by rfl⟩ : syracuseStep 1589099 = 2383649) B2383649
theorem B1589111 : Blo 1587492 1589111 := bstep (se 1 (by rfl) ⟨1191833, by rfl⟩ : syracuseStep 1589111 = 2383667) B2383667
theorem B1589131 : Blo 1587492 1589131 := bstep (se 1 (by rfl) ⟨1191848, by rfl⟩ : syracuseStep 1589131 = 2383697) B2383697
theorem B1589143 : Blo 1587492 1589143 := bstep (se 1 (by rfl) ⟨1191857, by rfl⟩ : syracuseStep 1589143 = 2383715) B2383715
theorem B2383769 : Blo 1587492 2383769 := bstep (se 2 (by rfl) ⟨893913, by rfl⟩ : syracuseStep 2383769 = 1787827) B1787827
theorem B2416537 : Blo 1587492 2416537 := bstep (se 2 (by rfl) ⟨906201, by rfl⟩ : syracuseStep 2416537 = 1812403) B1812403
theorem B1589163 : Blo 1587492 1589163 := bstep (se 1 (by rfl) ⟨1191872, by rfl⟩ : syracuseStep 1589163 = 2383745) B2383745
theorem B1589175 : Blo 1587492 1589175 := bstep (se 1 (by rfl) ⟨1191881, by rfl⟩ : syracuseStep 1589175 = 2383763) B2383763
theorem B3620801 : Blo 1587492 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B1589195 : Blo 1587492 1589195 := bstep (se 1 (by rfl) ⟨1191896, by rfl⟩ : syracuseStep 1589195 = 2383793) B2383793
theorem B1589207 : Blo 1587492 1589207 := bstep (se 1 (by rfl) ⟨1191905, by rfl⟩ : syracuseStep 1589207 = 2383811) B2383811
theorem B1589227 : Blo 1587492 1589227 := bstep (se 1 (by rfl) ⟨1191920, by rfl⟩ : syracuseStep 1589227 = 2383841) B2383841
theorem B1589239 : Blo 1587492 1589239 := bstep (se 1 (by rfl) ⟨1191929, by rfl⟩ : syracuseStep 1589239 = 2383859) B2383859
theorem B1589255 : Blo 1587492 1589255 := bstep (se 1 (by rfl) ⟨1191941, by rfl⟩ : syracuseStep 1589255 = 2383883) B2383883
theorem B18087947 : Blo 1587492 18087947 := bstep (se 1 (by rfl) ⟨13565960, by rfl⟩ : syracuseStep 18087947 = 27131921) B27131921
theorem B1589263 : Blo 1587492 1589263 := bstep (se 1 (by rfl) ⟨1191947, by rfl⟩ : syracuseStep 1589263 = 2383895) B2383895
theorem B77299757 : Blo 1587492 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B2383931 : Blo 1587492 2383931 := bstep (se 1 (by rfl) ⟨1787948, by rfl⟩ : syracuseStep 2383931 = 3575897) B3575897
theorem B1589307 : Blo 1587492 1589307 := bstep (se 1 (by rfl) ⟨1191980, by rfl⟩ : syracuseStep 1589307 = 2383961) B2383961
theorem B2383991 : Blo 1587492 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B1785991 : Blo 1587492 1785991 := bstep (se 1 (by rfl) ⟨1339493, by rfl⟩ : syracuseStep 1785991 = 2678987) B2678987
theorem B1589383 : Blo 1587492 1589383 := bstep (se 1 (by rfl) ⟨1192037, by rfl⟩ : syracuseStep 1589383 = 2384075) B2384075
theorem B2384015 : Blo 1587492 2384015 := bstep (se 1 (by rfl) ⟨1788011, by rfl⟩ : syracuseStep 2384015 = 3576023) B3576023
theorem B1589391 : Blo 1587492 1589391 := bstep (se 1 (by rfl) ⟨1192043, by rfl⟩ : syracuseStep 1589391 = 2384087) B2384087
theorem B4022419 : Blo 1587492 4022419 := bstep (se 1 (by rfl) ⟨3016814, by rfl⟩ : syracuseStep 4022419 = 6033629) B6033629
theorem B4522169 : Blo 1587492 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B2384057 : Blo 1587492 2384057 := bstep (se 2 (by rfl) ⟨894021, by rfl⟩ : syracuseStep 2384057 = 1788043) B1788043
theorem B1589435 : Blo 1587492 1589435 := bstep (se 1 (by rfl) ⟨1192076, by rfl⟩ : syracuseStep 1589435 = 2384153) B2384153
theorem B5357825 : Blo 1587492 5357825 := bstep (se 2 (by rfl) ⟨2009184, by rfl⟩ : syracuseStep 5357825 = 4018369) B4018369
theorem B2384135 : Blo 1587492 2384135 := bstep (se 1 (by rfl) ⟨1788101, by rfl⟩ : syracuseStep 2384135 = 3576203) B3576203
theorem B1696015 : Blo 1587492 1696015 := bstep (se 1 (by rfl) ⟨1272011, by rfl⟩ : syracuseStep 1696015 = 2544023) B2544023
theorem B4022561 : Blo 1587492 4022561 := bstep (se 2 (by rfl) ⟨1508460, by rfl⟩ : syracuseStep 4022561 = 3016921) B3016921
theorem B2384171 : Blo 1587492 2384171 := bstep (se 1 (by rfl) ⟨1788128, by rfl⟩ : syracuseStep 2384171 = 3576257) B3576257
theorem B3572027 : Blo 1587492 3572027 := bstep (se 1 (by rfl) ⟨2679020, by rfl⟩ : syracuseStep 3572027 = 5358041) B5358041
theorem B1786171 : Blo 1587492 1786171 := bstep (se 1 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 1786171 = 2679257) B2679257
theorem B2384201 : Blo 1587492 2384201 := bstep (se 2 (by rfl) ⟨894075, by rfl⟩ : syracuseStep 2384201 = 1788151) B1788151
theorem B43467101 : Blo 1587492 43467101 := bstep (se 3 (by rfl) ⟨8150081, by rfl⟩ : syracuseStep 43467101 = 16300163) B16300163
theorem B3572153 : Blo 1587492 3572153 := bstep (se 2 (by rfl) ⟨1339557, by rfl⟩ : syracuseStep 3572153 = 2679115) B2679115
theorem B2261449 : Blo 1587492 2261449 := bstep (se 2 (by rfl) ⟨848043, by rfl⟩ : syracuseStep 2261449 = 1696087) B1696087
theorem B7635467 : Blo 1587492 7635467 := bstep (se 1 (by rfl) ⟨5726600, by rfl⟩ : syracuseStep 7635467 = 11453201) B11453201
theorem B2679311 : Blo 1587492 2679311 := bstep (se 1 (by rfl) ⟨2009483, by rfl⟩ : syracuseStep 2679311 = 4018967) B4018967
theorem B9044567 : Blo 1587492 9044567 := bstep (se 1 (by rfl) ⟨6783425, by rfl⟩ : syracuseStep 9044567 = 13566851) B13566851
theorem B34333303 : Blo 1587492 34333303 := bstep (se 1 (by rfl) ⟨25749977, by rfl⟩ : syracuseStep 34333303 = 51499955) B51499955
theorem B3572495 : Blo 1587492 3572495 := bstep (se 1 (by rfl) ⟨2679371, by rfl⟩ : syracuseStep 3572495 = 5358743) B5358743
theorem B1786639 : Blo 1587492 1786639 := bstep (se 1 (by rfl) ⟨1339979, by rfl⟩ : syracuseStep 1786639 = 2679959) B2679959
theorem B3572513 : Blo 1587492 3572513 := bstep (se 2 (by rfl) ⟨1339692, by rfl⟩ : syracuseStep 3572513 = 2679385) B2679385
theorem B2147129 : Blo 1587492 2147129 := bstep (se 2 (by rfl) ⟨805173, by rfl⟩ : syracuseStep 2147129 = 1610347) B1610347
theorem B6030227 : Blo 1587492 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B8037305 : Blo 1587492 8037305 := bstep (se 2 (by rfl) ⟨3013989, by rfl⟩ : syracuseStep 8037305 = 6027979) B6027979
theorem B2261945 : Blo 1587492 2261945 := bstep (se 2 (by rfl) ⟨848229, by rfl⟩ : syracuseStep 2261945 = 1696459) B1696459
theorem B8586269 : Blo 1587492 8586269 := bstep (se 3 (by rfl) ⟨1609925, by rfl⟩ : syracuseStep 8586269 = 3219851) B3219851
theorem B4351009 : Blo 1587492 4351009 := bstep (se 2 (by rfl) ⟨1631628, by rfl⟩ : syracuseStep 4351009 = 3263257) B3263257
theorem B5358635 : Blo 1587492 5358635 := bstep (se 1 (by rfl) ⟨4018976, by rfl⟩ : syracuseStep 5358635 = 8037953) B8037953
theorem B2679851 : Blo 1587492 2679851 := bstep (se 1 (by rfl) ⟨2009888, by rfl⟩ : syracuseStep 2679851 = 4019777) B4019777
theorem B5727293 : Blo 1587492 5727293 := bstep (se 3 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 5727293 = 2147735) B2147735
theorem B32613463 : Blo 1587492 32613463 := bstep (se 1 (by rfl) ⟨24460097, by rfl⟩ : syracuseStep 32613463 = 48920195) B48920195
theorem B28992599 : Blo 1587492 28992599 := bstep (se 1 (by rfl) ⟨21744449, by rfl⟩ : syracuseStep 28992599 = 43488899) B43488899
theorem B3572855 : Blo 1587492 3572855 := bstep (se 1 (by rfl) ⟨2679641, by rfl⟩ : syracuseStep 3572855 = 5359283) B5359283
theorem B4523161 : Blo 1587492 4523161 := bstep (se 2 (by rfl) ⟨1696185, by rfl⟩ : syracuseStep 4523161 = 3392371) B3392371
theorem B3818753 : Blo 1587492 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1787143 : Blo 1587492 1787143 := bstep (se 1 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 1787143 = 2680715) B2680715
theorem B3573035 : Blo 1587492 3573035 := bstep (se 1 (by rfl) ⟨2679776, by rfl⟩ : syracuseStep 3573035 = 5359553) B5359553
theorem B11445563 : Blo 1587492 11445563 := bstep (se 1 (by rfl) ⟨8584172, by rfl⟩ : syracuseStep 11445563 = 17168345) B17168345
theorem B3016055 : Blo 1587492 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B12060089 : Blo 1587492 12060089 := bstep (se 2 (by rfl) ⟨4522533, by rfl⟩ : syracuseStep 12060089 = 9045067) B9045067
theorem B2680249 : Blo 1587492 2680249 := bstep (se 2 (by rfl) ⟨1005093, by rfl⟩ : syracuseStep 2680249 = 2010187) B2010187
theorem B1787323 : Blo 1587492 1787323 := bstep (se 1 (by rfl) ⟨1340492, by rfl⟩ : syracuseStep 1787323 = 2680985) B2680985
theorem B25748941 : Blo 1587492 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B3016207 : Blo 1587492 3016207 := bstep (se 1 (by rfl) ⟨2262155, by rfl⟩ : syracuseStep 3016207 = 4524311) B4524311
theorem B3573395 : Blo 1587492 3573395 := bstep (se 1 (by rfl) ⟨2680046, by rfl⟩ : syracuseStep 3573395 = 5360093) B5360093
theorem B3573449 : Blo 1587492 3573449 := bstep (se 2 (by rfl) ⟨1340043, by rfl⟩ : syracuseStep 3573449 = 2680087) B2680087
theorem B10176293 : Blo 1587492 10176293 := bstep (se 4 (by rfl) ⟨954027, by rfl⟩ : syracuseStep 10176293 = 1908055) B1908055
theorem B2262919 : Blo 1587492 2262919 := bstep (se 1 (by rfl) ⟨1697189, by rfl⟩ : syracuseStep 2262919 = 3394379) B3394379
theorem B1787791 : Blo 1587492 1787791 := bstep (se 1 (by rfl) ⟨1340843, by rfl⟩ : syracuseStep 1787791 = 2681687) B2681687
theorem B3016595 : Blo 1587492 3016595 := bstep (se 1 (by rfl) ⟨2262446, by rfl⟩ : syracuseStep 3016595 = 4524893) B4524893
theorem B8046539 : Blo 1587492 8046539 := bstep (se 1 (by rfl) ⟨6034904, by rfl⟩ : syracuseStep 8046539 = 12069809) B12069809
theorem B2680951 : Blo 1587492 2680951 := bstep (se 1 (by rfl) ⟨2010713, by rfl⟩ : syracuseStep 2680951 = 4021427) B4021427
theorem B12888197 : Blo 1587492 12888197 := bstep (se 4 (by rfl) ⟨1208268, by rfl⟩ : syracuseStep 12888197 = 2416537) B2416537
theorem B4352147 : Blo 1587492 4352147 := bstep (se 1 (by rfl) ⟨3264110, by rfl⟩ : syracuseStep 4352147 = 6528221) B6528221
theorem B8038601 : Blo 1587492 8038601 := bstep (se 2 (by rfl) ⟨3014475, by rfl⟩ : syracuseStep 8038601 = 6028951) B6028951
theorem B30968081 : Blo 1587492 30968081 := bstep (se 2 (by rfl) ⟨11613030, by rfl⟩ : syracuseStep 30968081 = 23226061) B23226061
theorem B2009387 : Blo 1587492 2009387 := bstep (se 1 (by rfl) ⟨1507040, by rfl⟩ : syracuseStep 2009387 = 3014081) B3014081
theorem B5359931 : Blo 1587492 5359931 := bstep (se 1 (by rfl) ⟨4019948, by rfl⟩ : syracuseStep 5359931 = 8039897) B8039897
theorem B2681147 : Blo 1587492 2681147 := bstep (se 1 (by rfl) ⟨2010860, by rfl⟩ : syracuseStep 2681147 = 4021721) B4021721
theorem B3574151 : Blo 1587492 3574151 := bstep (se 1 (by rfl) ⟨2680613, by rfl⟩ : syracuseStep 3574151 = 5361227) B5361227
theorem B4827539 : Blo 1587492 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B8587741 : Blo 1587492 8587741 := bstep (se 3 (by rfl) ⟨1610201, by rfl⟩ : syracuseStep 8587741 = 3220403) B3220403
theorem B3574331 : Blo 1587492 3574331 := bstep (se 1 (by rfl) ⟨2680748, by rfl⟩ : syracuseStep 3574331 = 5361497) B5361497
theorem B19597889 : Blo 1587492 19597889 := bstep (se 2 (by rfl) ⟨7349208, by rfl⟩ : syracuseStep 19597889 = 14698417) B14698417
theorem B3574457 : Blo 1587492 3574457 := bstep (se 2 (by rfl) ⟨1340421, by rfl⟩ : syracuseStep 3574457 = 2680843) B2680843
theorem B2681545 : Blo 1587492 2681545 := bstep (se 2 (by rfl) ⟨1005579, by rfl⟩ : syracuseStep 2681545 = 2011159) B2011159
theorem B2009863 : Blo 1587492 2009863 := bstep (se 1 (by rfl) ⟨1507397, by rfl⟩ : syracuseStep 2009863 = 3014795) B3014795
theorem B9046799 : Blo 1587492 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B5360417 : Blo 1587492 5360417 := bstep (se 2 (by rfl) ⟨2010156, by rfl⟩ : syracuseStep 5360417 = 4020313) B4020313
theorem B6785851 : Blo 1587492 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B9300851 : Blo 1587492 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B5434265 : Blo 1587492 5434265 := bstep (se 2 (by rfl) ⟨2037849, by rfl⟩ : syracuseStep 5434265 = 4075699) B4075699
theorem B11447203 : Blo 1587492 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B9047051 : Blo 1587492 9047051 := bstep (se 1 (by rfl) ⟨6785288, by rfl⟩ : syracuseStep 9047051 = 13570577) B13570577
theorem B4582415 : Blo 1587492 4582415 := bstep (se 1 (by rfl) ⟨3436811, by rfl⟩ : syracuseStep 4582415 = 6873623) B6873623
theorem B3574799 : Blo 1587492 3574799 := bstep (se 1 (by rfl) ⟨2681099, by rfl⟩ : syracuseStep 3574799 = 5362199) B5362199
theorem B4525085 : Blo 1587492 4525085 := bstep (se 3 (by rfl) ⟨848453, by rfl⟩ : syracuseStep 4525085 = 1696907) B1696907
theorem B3574817 : Blo 1587492 3574817 := bstep (se 2 (by rfl) ⟨1340556, by rfl⟩ : syracuseStep 3574817 = 2681113) B2681113
theorem B7638083 : Blo 1587492 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B2010359 : Blo 1587492 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B43470179 : Blo 1587492 43470179 := bstep (se 1 (by rfl) ⟨32602634, by rfl⟩ : syracuseStep 43470179 = 65205269) B65205269
theorem B5361011 : Blo 1587492 5361011 := bstep (se 1 (by rfl) ⟨4020758, by rfl⟩ : syracuseStep 5361011 = 8041517) B8041517
theorem B3575159 : Blo 1587492 3575159 := bstep (se 1 (by rfl) ⟨2681369, by rfl⟩ : syracuseStep 3575159 = 5362739) B5362739
theorem B8154503 : Blo 1587492 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B2682247 : Blo 1587492 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B2010511 : Blo 1587492 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B15265169 : Blo 1587492 15265169 := bstep (se 2 (by rfl) ⟨5724438, by rfl⟩ : syracuseStep 15265169 = 11448877) B11448877
theorem B34368947 : Blo 1587492 34368947 := bstep (se 1 (by rfl) ⟨25776710, by rfl⟩ : syracuseStep 34368947 = 51553421) B51553421
theorem B6032825 : Blo 1587492 6032825 := bstep (se 2 (by rfl) ⟨2262309, by rfl⟩ : syracuseStep 6032825 = 4524619) B4524619
theorem B3575339 : Blo 1587492 3575339 := bstep (se 1 (by rfl) ⟨2681504, by rfl⟩ : syracuseStep 3575339 = 5363009) B5363009
theorem B2010683 : Blo 1587492 2010683 := bstep (se 1 (by rfl) ⟨1508012, by rfl⟩ : syracuseStep 2010683 = 3016025) B3016025
theorem B4525769 : Blo 1587492 4525769 := bstep (se 2 (by rfl) ⟨1697163, by rfl⟩ : syracuseStep 4525769 = 3394327) B3394327
theorem B8589037 : Blo 1587492 8589037 := bstep (se 3 (by rfl) ⟨1610444, by rfl⟩ : syracuseStep 8589037 = 3220889) B3220889
theorem B2543375 : Blo 1587492 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B6524705 : Blo 1587492 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B7630625 : Blo 1587492 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B5091131 : Blo 1587492 5091131 := bstep (se 1 (by rfl) ⟨3818348, by rfl⟩ : syracuseStep 5091131 = 7636697) B7636697
theorem B10178419 : Blo 1587492 10178419 := bstep (se 1 (by rfl) ⟨7633814, by rfl⟩ : syracuseStep 10178419 = 15267629) B15267629
theorem B3575699 : Blo 1587492 3575699 := bstep (se 1 (by rfl) ⟨2681774, by rfl⟩ : syracuseStep 3575699 = 5363549) B5363549
theorem B7630777 : Blo 1587492 7630777 := bstep (se 2 (by rfl) ⟨2861541, by rfl⟩ : syracuseStep 7630777 = 5723083) B5723083
theorem B3575753 : Blo 1587492 3575753 := bstep (se 2 (by rfl) ⟨1340907, by rfl⟩ : syracuseStep 3575753 = 2681815) B2681815
theorem B13578263 : Blo 1587492 13578263 := bstep (se 1 (by rfl) ⟨10183697, by rfl⟩ : syracuseStep 13578263 = 20367395) B20367395
theorem B3182635 : Blo 1587492 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B9048257 : Blo 1587492 9048257 := bstep (se 2 (by rfl) ⟨3393096, by rfl⟩ : syracuseStep 9048257 = 6786193) B6786193
theorem B18092321 : Blo 1587492 18092321 := bstep (se 2 (by rfl) ⟨6784620, by rfl⟩ : syracuseStep 18092321 = 13569241) B13569241
theorem B1937783 : Blo 1587492 1937783 := bstep (se 1 (by rfl) ⟨1453337, by rfl⟩ : syracuseStep 1937783 = 2906675) B2906675
theorem B6033811 : Blo 1587492 6033811 := bstep (se 1 (by rfl) ⟨4525358, by rfl⟩ : syracuseStep 6033811 = 9050717) B9050717
theorem B2011655 : Blo 1587492 2011655 := bstep (se 1 (by rfl) ⟨1508741, by rfl⟩ : syracuseStep 2011655 = 3017483) B3017483
theorem B4018835 : Blo 1587492 4018835 := bstep (se 1 (by rfl) ⟨3014126, by rfl⟩ : syracuseStep 4018835 = 6028253) B6028253
theorem B5722825 : Blo 1587492 5722825 := bstep (se 2 (by rfl) ⟨2146059, by rfl⟩ : syracuseStep 5722825 = 4292119) B4292119
theorem B23540441 : Blo 1587492 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B4019129 : Blo 1587492 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B9655469 : Blo 1587492 9655469 := bstep (se 3 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 9655469 = 3620801) B3620801
theorem B2545015 : Blo 1587492 2545015 := bstep (se 1 (by rfl) ⟨1908761, by rfl⟩ : syracuseStep 2545015 = 3817523) B3817523
theorem B49550723 : Blo 1587492 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B6116755 : Blo 1587492 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B2381243 : Blo 1587492 2381243 := bstep (se 1 (by rfl) ⟨1785932, by rfl⟩ : syracuseStep 2381243 = 3571865) B3571865
theorem B2381303 : Blo 1587492 2381303 := bstep (se 1 (by rfl) ⟨1785977, by rfl⟩ : syracuseStep 2381303 = 3571955) B3571955
theorem B2381327 : Blo 1587492 2381327 := bstep (se 1 (by rfl) ⟨1785995, by rfl⟩ : syracuseStep 2381327 = 3571991) B3571991
theorem B2381369 : Blo 1587492 2381369 := bstep (se 2 (by rfl) ⟨893013, by rfl⟩ : syracuseStep 2381369 = 1786027) B1786027
theorem B2717243 : Blo 1587492 2717243 := bstep (se 1 (by rfl) ⟨2037932, by rfl⟩ : syracuseStep 2717243 = 4075865) B4075865
theorem B4019827 : Blo 1587492 4019827 := bstep (se 1 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 4019827 = 6029741) B6029741
theorem B2381447 : Blo 1587492 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B2381483 : Blo 1587492 2381483 := bstep (se 1 (by rfl) ⟨1786112, by rfl⟩ : syracuseStep 2381483 = 3572225) B3572225
theorem B16307891 : Blo 1587492 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B2381513 : Blo 1587492 2381513 := bstep (se 2 (by rfl) ⟨893067, by rfl⟩ : syracuseStep 2381513 = 1786135) B1786135
theorem B4019969 : Blo 1587492 4019969 := bstep (se 2 (by rfl) ⟨1507488, by rfl⟩ : syracuseStep 4019969 = 3014977) B3014977
theorem B18339635 : Blo 1587492 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B2381627 : Blo 1587492 2381627 := bstep (se 1 (by rfl) ⟨1786220, by rfl⟩ : syracuseStep 2381627 = 3572441) B3572441
theorem B2381687 : Blo 1587492 2381687 := bstep (se 1 (by rfl) ⟨1786265, by rfl⟩ : syracuseStep 2381687 = 3572531) B3572531
theorem B2381711 : Blo 1587492 2381711 := bstep (se 1 (by rfl) ⟨1786283, by rfl⟩ : syracuseStep 2381711 = 3572567) B3572567
theorem B5363603 : Blo 1587492 5363603 := bstep (se 1 (by rfl) ⟨4022702, by rfl⟩ : syracuseStep 5363603 = 8045405) B8045405
theorem B2381753 : Blo 1587492 2381753 := bstep (se 2 (by rfl) ⟨893157, by rfl⟩ : syracuseStep 2381753 = 1786315) B1786315
theorem B2291657 : Blo 1587492 2291657 := bstep (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) B1718743
theorem B18331595 : Blo 1587492 18331595 := bstep (se 1 (by rfl) ⟨13748696, by rfl⟩ : syracuseStep 18331595 = 27497393) B27497393
theorem B2381831 : Blo 1587492 2381831 := bstep (se 1 (by rfl) ⟨1786373, by rfl⟩ : syracuseStep 2381831 = 3572747) B3572747
theorem B61929485 : Blo 1587492 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B2381867 : Blo 1587492 2381867 := bstep (se 1 (by rfl) ⟨1786400, by rfl⟩ : syracuseStep 2381867 = 3572801) B3572801
theorem B2381897 : Blo 1587492 2381897 := bstep (se 2 (by rfl) ⟨893211, by rfl⟩ : syracuseStep 2381897 = 1786423) B1786423
theorem B13056173 : Blo 1587492 13056173 := bstep (se 3 (by rfl) ⟨2448032, by rfl⟩ : syracuseStep 13056173 = 4896065) B4896065
theorem B2382011 : Blo 1587492 2382011 := bstep (se 1 (by rfl) ⟨1786508, by rfl⟩ : syracuseStep 2382011 = 3573017) B3573017
theorem B4020425 : Blo 1587492 4020425 := bstep (se 2 (by rfl) ⟨1507659, by rfl⟩ : syracuseStep 4020425 = 3015319) B3015319
theorem B2382071 : Blo 1587492 2382071 := bstep (se 1 (by rfl) ⟨1786553, by rfl⟩ : syracuseStep 2382071 = 3573107) B3573107
theorem B2382095 : Blo 1587492 2382095 := bstep (se 1 (by rfl) ⟨1786571, by rfl⟩ : syracuseStep 2382095 = 3573143) B3573143
theorem B2382137 : Blo 1587492 2382137 := bstep (se 2 (by rfl) ⟨893301, by rfl⟩ : syracuseStep 2382137 = 1786603) B1786603
theorem B1587515 : Blo 1587492 1587515 := bstep (se 1 (by rfl) ⟨1190636, by rfl⟩ : syracuseStep 1587515 = 2381273) B2381273
theorem B1587591 : Blo 1587492 1587591 := bstep (se 1 (by rfl) ⟨1190693, by rfl⟩ : syracuseStep 1587591 = 2381387) B2381387
theorem B2382215 : Blo 1587492 2382215 := bstep (se 1 (by rfl) ⟨1786661, by rfl⟩ : syracuseStep 2382215 = 3573323) B3573323
theorem B1587599 : Blo 1587492 1587599 := bstep (se 1 (by rfl) ⟨1190699, by rfl⟩ : syracuseStep 1587599 = 2381399) B2381399
theorem B2382251 : Blo 1587492 2382251 := bstep (se 1 (by rfl) ⟨1786688, by rfl⟩ : syracuseStep 2382251 = 3573377) B3573377
theorem B1587643 : Blo 1587492 1587643 := bstep (se 1 (by rfl) ⟨1190732, by rfl⟩ : syracuseStep 1587643 = 2381465) B2381465
theorem B2382281 : Blo 1587492 2382281 := bstep (se 2 (by rfl) ⟨893355, by rfl⟩ : syracuseStep 2382281 = 1786711) B1786711
theorem B1587719 : Blo 1587492 1587719 := bstep (se 1 (by rfl) ⟨1190789, by rfl⟩ : syracuseStep 1587719 = 2381579) B2381579
theorem B6879755 : Blo 1587492 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B1587727 : Blo 1587492 1587727 := bstep (se 1 (by rfl) ⟨1190795, by rfl⟩ : syracuseStep 1587727 = 2381591) B2381591
theorem B4020779 : Blo 1587492 4020779 := bstep (se 1 (by rfl) ⟨3015584, by rfl⟩ : syracuseStep 4020779 = 6031169) B6031169
theorem B1587771 : Blo 1587492 1587771 := bstep (se 1 (by rfl) ⟨1190828, by rfl⟩ : syracuseStep 1587771 = 2381657) B2381657
theorem B2382395 : Blo 1587492 2382395 := bstep (se 1 (by rfl) ⟨1786796, by rfl⟩ : syracuseStep 2382395 = 3573593) B3573593
theorem B2382455 : Blo 1587492 2382455 := bstep (se 1 (by rfl) ⟨1786841, by rfl⟩ : syracuseStep 2382455 = 3573683) B3573683
theorem B1587847 : Blo 1587492 1587847 := bstep (se 1 (by rfl) ⟨1190885, by rfl⟩ : syracuseStep 1587847 = 2381771) B2381771
theorem B1587855 : Blo 1587492 1587855 := bstep (se 1 (by rfl) ⟨1190891, by rfl⟩ : syracuseStep 1587855 = 2381783) B2381783
theorem B2382479 : Blo 1587492 2382479 := bstep (se 1 (by rfl) ⟨1786859, by rfl⟩ : syracuseStep 2382479 = 3573719) B3573719
theorem B2382521 : Blo 1587492 2382521 := bstep (se 2 (by rfl) ⟨893445, by rfl⟩ : syracuseStep 2382521 = 1786891) B1786891
theorem B1587899 : Blo 1587492 1587899 := bstep (se 1 (by rfl) ⟨1190924, by rfl⟩ : syracuseStep 1587899 = 2381849) B2381849
theorem B1587975 : Blo 1587492 1587975 := bstep (se 1 (by rfl) ⟨1190981, by rfl⟩ : syracuseStep 1587975 = 2381963) B2381963
theorem B2382599 : Blo 1587492 2382599 := bstep (se 1 (by rfl) ⟨1786949, by rfl⟩ : syracuseStep 2382599 = 3573899) B3573899
theorem B1587983 : Blo 1587492 1587983 := bstep (se 1 (by rfl) ⟨1190987, by rfl⟩ : syracuseStep 1587983 = 2381975) B2381975
theorem B30964517 : Blo 1587492 30964517 := bstep (se 4 (by rfl) ⟨2902923, by rfl⟩ : syracuseStep 30964517 = 5805847) B5805847
theorem B2382635 : Blo 1587492 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B1588027 : Blo 1587492 1588027 := bstep (se 1 (by rfl) ⟨1191020, by rfl⟩ : syracuseStep 1588027 = 2382041) B2382041
theorem B2382665 : Blo 1587492 2382665 := bstep (se 2 (by rfl) ⟨893499, by rfl⟩ : syracuseStep 2382665 = 1786999) B1786999
theorem B20626265 : Blo 1587492 20626265 := bstep (se 2 (by rfl) ⟨7734849, by rfl⟩ : syracuseStep 20626265 = 15469699) B15469699
theorem B1588103 : Blo 1587492 1588103 := bstep (se 1 (by rfl) ⟨1191077, by rfl⟩ : syracuseStep 1588103 = 2382155) B2382155
theorem B1588111 : Blo 1587492 1588111 := bstep (se 1 (by rfl) ⟨1191083, by rfl⟩ : syracuseStep 1588111 = 2382167) B2382167
theorem B1588155 : Blo 1587492 1588155 := bstep (se 1 (by rfl) ⟨1191116, by rfl⟩ : syracuseStep 1588155 = 2382233) B2382233
theorem B2382779 : Blo 1587492 2382779 := bstep (se 1 (by rfl) ⟨1787084, by rfl⟩ : syracuseStep 2382779 = 3574169) B3574169
theorem B2382839 : Blo 1587492 2382839 := bstep (se 1 (by rfl) ⟨1787129, by rfl⟩ : syracuseStep 2382839 = 3574259) B3574259
theorem B1588231 : Blo 1587492 1588231 := bstep (se 1 (by rfl) ⟨1191173, by rfl⟩ : syracuseStep 1588231 = 2382347) B2382347
theorem B1588239 : Blo 1587492 1588239 := bstep (se 1 (by rfl) ⟨1191179, by rfl⟩ : syracuseStep 1588239 = 2382359) B2382359
theorem B2382863 : Blo 1587492 2382863 := bstep (se 1 (by rfl) ⟨1787147, by rfl⟩ : syracuseStep 2382863 = 3574295) B3574295
theorem B2382905 : Blo 1587492 2382905 := bstep (se 2 (by rfl) ⟨893589, by rfl⟩ : syracuseStep 2382905 = 1787179) B1787179
theorem B1588283 : Blo 1587492 1588283 := bstep (se 1 (by rfl) ⟨1191212, by rfl⟩ : syracuseStep 1588283 = 2382425) B2382425
theorem B18095237 : Blo 1587492 18095237 := bstep (se 4 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 18095237 = 3392857) B3392857
theorem B1588359 : Blo 1587492 1588359 := bstep (se 1 (by rfl) ⟨1191269, by rfl⟩ : syracuseStep 1588359 = 2382539) B2382539
theorem B2382983 : Blo 1587492 2382983 := bstep (se 1 (by rfl) ⟨1787237, by rfl⟩ : syracuseStep 2382983 = 3574475) B3574475
theorem B1588367 : Blo 1587492 1588367 := bstep (se 1 (by rfl) ⟨1191275, by rfl⟩ : syracuseStep 1588367 = 2382551) B2382551
theorem B2383019 : Blo 1587492 2383019 := bstep (se 1 (by rfl) ⟨1787264, by rfl⟩ : syracuseStep 2383019 = 3574529) B3574529
theorem B1588411 : Blo 1587492 1588411 := bstep (se 1 (by rfl) ⟨1191308, by rfl⟩ : syracuseStep 1588411 = 2382617) B2382617
theorem B3816649 : Blo 1587492 3816649 := bstep (se 2 (by rfl) ⟨1431243, by rfl⟩ : syracuseStep 3816649 = 2862487) B2862487
theorem B2383049 : Blo 1587492 2383049 := bstep (se 2 (by rfl) ⟨893643, by rfl⟩ : syracuseStep 2383049 = 1787287) B1787287
theorem B1588487 : Blo 1587492 1588487 := bstep (se 1 (by rfl) ⟨1191365, by rfl⟩ : syracuseStep 1588487 = 2382731) B2382731
theorem B1907983 : Blo 1587492 1907983 := bstep (se 1 (by rfl) ⟨1430987, by rfl⟩ : syracuseStep 1907983 = 2861975) B2861975
theorem B1588495 : Blo 1587492 1588495 := bstep (se 1 (by rfl) ⟨1191371, by rfl⟩ : syracuseStep 1588495 = 2382743) B2382743
theorem B9051425 : Blo 1587492 9051425 := bstep (se 2 (by rfl) ⟨3394284, by rfl⟩ : syracuseStep 9051425 = 6788569) B6788569
theorem B68721965 : Blo 1587492 68721965 := bstep (se 3 (by rfl) ⟨12885368, by rfl⟩ : syracuseStep 68721965 = 25770737) B25770737
theorem B1588539 : Blo 1587492 1588539 := bstep (se 1 (by rfl) ⟨1191404, by rfl⟩ : syracuseStep 1588539 = 2382809) B2382809
theorem B2383163 : Blo 1587492 2383163 := bstep (se 1 (by rfl) ⟨1787372, by rfl⟩ : syracuseStep 2383163 = 3574745) B3574745
theorem B2383223 : Blo 1587492 2383223 := bstep (se 1 (by rfl) ⟨1787417, by rfl⟩ : syracuseStep 2383223 = 3574835) B3574835
theorem B1588615 : Blo 1587492 1588615 := bstep (se 1 (by rfl) ⟨1191461, by rfl⟩ : syracuseStep 1588615 = 2382923) B2382923
theorem B1588623 : Blo 1587492 1588623 := bstep (se 1 (by rfl) ⟨1191467, by rfl⟩ : syracuseStep 1588623 = 2382935) B2382935
theorem B2383247 : Blo 1587492 2383247 := bstep (se 1 (by rfl) ⟨1787435, by rfl⟩ : syracuseStep 2383247 = 3574871) B3574871
theorem B2383289 : Blo 1587492 2383289 := bstep (se 2 (by rfl) ⟨893733, by rfl⟩ : syracuseStep 2383289 = 1787467) B1787467
theorem B1588667 : Blo 1587492 1588667 := bstep (se 1 (by rfl) ⟨1191500, by rfl⟩ : syracuseStep 1588667 = 2383001) B2383001
theorem B2260487 : Blo 1587492 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B1588743 : Blo 1587492 1588743 := bstep (se 1 (by rfl) ⟨1191557, by rfl⟩ : syracuseStep 1588743 = 2383115) B2383115
theorem B2383367 : Blo 1587492 2383367 := bstep (se 1 (by rfl) ⟨1787525, by rfl⟩ : syracuseStep 2383367 = 3575051) B3575051
theorem B4021771 : Blo 1587492 4021771 := bstep (se 1 (by rfl) ⟨3016328, by rfl⟩ : syracuseStep 4021771 = 6032657) B6032657
theorem B1588751 : Blo 1587492 1588751 := bstep (se 1 (by rfl) ⟨1191563, by rfl⟩ : syracuseStep 1588751 = 2383127) B2383127
theorem B2383403 : Blo 1587492 2383403 := bstep (se 1 (by rfl) ⟨1787552, by rfl⟩ : syracuseStep 2383403 = 3575105) B3575105
theorem B1588795 : Blo 1587492 1588795 := bstep (se 1 (by rfl) ⟨1191596, by rfl⟩ : syracuseStep 1588795 = 2383193) B2383193
theorem B2383433 : Blo 1587492 2383433 := bstep (se 2 (by rfl) ⟨893787, by rfl⟩ : syracuseStep 2383433 = 1787575) B1787575
theorem B4292183 : Blo 1587492 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B3014263 : Blo 1587492 3014263 := bstep (se 1 (by rfl) ⟨2260697, by rfl⟩ : syracuseStep 3014263 = 4521395) B4521395
theorem B1588871 : Blo 1587492 1588871 := bstep (se 1 (by rfl) ⟨1191653, by rfl⟩ : syracuseStep 1588871 = 2383307) B2383307
theorem B1588879 : Blo 1587492 1588879 := bstep (se 1 (by rfl) ⟨1191659, by rfl⟩ : syracuseStep 1588879 = 2383319) B2383319
theorem B4021913 : Blo 1587492 4021913 := bstep (se 2 (by rfl) ⟨1508217, by rfl⟩ : syracuseStep 4021913 = 3016435) B3016435
theorem B18103985 : Blo 1587492 18103985 := bstep (se 2 (by rfl) ⟨6788994, by rfl⟩ : syracuseStep 18103985 = 13577989) B13577989
theorem B1588923 : Blo 1587492 1588923 := bstep (se 1 (by rfl) ⟨1191692, by rfl⟩ : syracuseStep 1588923 = 2383385) B2383385
theorem B2383547 : Blo 1587492 2383547 := bstep (se 1 (by rfl) ⟨1787660, by rfl⟩ : syracuseStep 2383547 = 3575321) B3575321
theorem B9166537 : Blo 1587492 9166537 := bstep (se 2 (by rfl) ⟨3437451, by rfl⟩ : syracuseStep 9166537 = 6874903) B6874903
theorem B2383607 : Blo 1587492 2383607 := bstep (se 1 (by rfl) ⟨1787705, by rfl⟩ : syracuseStep 2383607 = 3575411) B3575411
theorem B13573889 : Blo 1587492 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B1588999 : Blo 1587492 1588999 := bstep (se 1 (by rfl) ⟨1191749, by rfl⟩ : syracuseStep 1588999 = 2383499) B2383499
theorem B1589007 : Blo 1587492 1589007 := bstep (se 1 (by rfl) ⟨1191755, by rfl⟩ : syracuseStep 1589007 = 2383511) B2383511
theorem B2383631 : Blo 1587492 2383631 := bstep (se 1 (by rfl) ⟨1787723, by rfl⟩ : syracuseStep 2383631 = 3575447) B3575447
theorem B45817649 : Blo 1587492 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B5726011 : Blo 1587492 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B4022075 : Blo 1587492 4022075 := bstep (se 1 (by rfl) ⟨3016556, by rfl⟩ : syracuseStep 4022075 = 6033113) B6033113
theorem B1589051 : Blo 1587492 1589051 := bstep (se 1 (by rfl) ⟨1191788, by rfl⟩ : syracuseStep 1589051 = 2383577) B2383577
theorem B2383673 : Blo 1587492 2383673 := bstep (se 2 (by rfl) ⟨893877, by rfl⟩ : syracuseStep 2383673 = 1787755) B1787755
theorem B15482713 : Blo 1587492 15482713 := bstep (se 2 (by rfl) ⟨5806017, by rfl⟩ : syracuseStep 15482713 = 11612035) B11612035
theorem B1589127 : Blo 1587492 1589127 := bstep (se 1 (by rfl) ⟨1191845, by rfl⟩ : syracuseStep 1589127 = 2383691) B2383691
theorem B2383751 : Blo 1587492 2383751 := bstep (se 1 (by rfl) ⟨1787813, by rfl⟩ : syracuseStep 2383751 = 3575627) B3575627
theorem B1589135 : Blo 1587492 1589135 := bstep (se 1 (by rfl) ⟨1191851, by rfl⟩ : syracuseStep 1589135 = 2383703) B2383703
theorem B8044433 : Blo 1587492 8044433 := bstep (se 2 (by rfl) ⟨3016662, by rfl⟩ : syracuseStep 8044433 = 6033325) B6033325
theorem B2383787 : Blo 1587492 2383787 := bstep (se 1 (by rfl) ⟨1787840, by rfl⟩ : syracuseStep 2383787 = 3575681) B3575681
theorem B1589179 : Blo 1587492 1589179 := bstep (se 1 (by rfl) ⟨1191884, by rfl⟩ : syracuseStep 1589179 = 2383769) B2383769
theorem B2383817 : Blo 1587492 2383817 := bstep (se 2 (by rfl) ⟨893931, by rfl⟩ : syracuseStep 2383817 = 1787863) B1787863
theorem B12058631 : Blo 1587492 12058631 := bstep (se 1 (by rfl) ⟨9043973, by rfl⟩ : syracuseStep 12058631 = 18087947) B18087947
theorem B9052175 : Blo 1587492 9052175 := bstep (se 1 (by rfl) ⟨6789131, by rfl⟩ : syracuseStep 9052175 = 13578263) B13578263
theorem B1589287 : Blo 1587492 1589287 := bstep (se 1 (by rfl) ⟨1191965, by rfl⟩ : syracuseStep 1589287 = 2383931) B2383931
theorem B4243513 : Blo 1587492 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B12066893 : Blo 1587492 12066893 := bstep (se 3 (by rfl) ⟨2262542, by rfl⟩ : syracuseStep 12066893 = 4525085) B4525085
theorem B1589327 : Blo 1587492 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B1589343 : Blo 1587492 1589343 := bstep (se 1 (by rfl) ⟨1192007, by rfl⟩ : syracuseStep 1589343 = 2384015) B2384015
theorem B1589371 : Blo 1587492 1589371 := bstep (se 1 (by rfl) ⟨1192028, by rfl⟩ : syracuseStep 1589371 = 2384057) B2384057
theorem B3571883 : Blo 1587492 3571883 := bstep (se 1 (by rfl) ⟨2678912, by rfl⟩ : syracuseStep 3571883 = 5357825) B5357825
theorem B1589423 : Blo 1587492 1589423 := bstep (se 1 (by rfl) ⟨1192067, by rfl⟩ : syracuseStep 1589423 = 2384135) B2384135
theorem B1589447 : Blo 1587492 1589447 := bstep (se 1 (by rfl) ⟨1192085, by rfl⟩ : syracuseStep 1589447 = 2384171) B2384171
theorem B1589467 : Blo 1587492 1589467 := bstep (se 1 (by rfl) ⟨1192100, by rfl⟩ : syracuseStep 1589467 = 2384201) B2384201
theorem B1786207 : Blo 1587492 1786207 := bstep (se 1 (by rfl) ⟨1339655, by rfl⟩ : syracuseStep 1786207 = 2679311) B2679311
theorem B2261353 : Blo 1587492 2261353 := bstep (se 2 (by rfl) ⟨848007, by rfl⟩ : syracuseStep 2261353 = 1696015) B1696015
theorem B6029711 : Blo 1587492 6029711 := bstep (se 1 (by rfl) ⟨4522283, by rfl⟩ : syracuseStep 6029711 = 9044567) B9044567
theorem B2679223 : Blo 1587492 2679223 := bstep (se 1 (by rfl) ⟨2009417, by rfl⟩ : syracuseStep 2679223 = 4018835) B4018835
theorem B12059117 : Blo 1587492 12059117 := bstep (se 3 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 12059117 = 4522169) B4522169
theorem B8045081 : Blo 1587492 8045081 := bstep (se 2 (by rfl) ⟨3016905, by rfl⟩ : syracuseStep 8045081 = 6033811) B6033811
theorem B5358203 : Blo 1587492 5358203 := bstep (se 1 (by rfl) ⟨4018652, by rfl⟩ : syracuseStep 5358203 = 8037305) B8037305
theorem B2679419 : Blo 1587492 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B3572423 : Blo 1587492 3572423 := bstep (se 1 (by rfl) ⟨2679317, by rfl⟩ : syracuseStep 3572423 = 5358635) B5358635
theorem B1786567 : Blo 1587492 1786567 := bstep (se 1 (by rfl) ⟨1339925, by rfl⟩ : syracuseStep 1786567 = 2679851) B2679851
theorem B3818195 : Blo 1587492 3818195 := bstep (se 1 (by rfl) ⟨2863646, by rfl⟩ : syracuseStep 3818195 = 5727293) B5727293
theorem B5358365 : Blo 1587492 5358365 := bstep (se 3 (by rfl) ⟨1004693, by rfl⟩ : syracuseStep 5358365 = 2009387) B2009387
theorem B45777737 : Blo 1587492 45777737 := bstep (se 2 (by rfl) ⟨17166651, by rfl⟩ : syracuseStep 45777737 = 34333303) B34333303
theorem B2679817 : Blo 1587492 2679817 := bstep (se 2 (by rfl) ⟨1004931, by rfl⟩ : syracuseStep 2679817 = 2009863) B2009863
theorem B1811495 : Blo 1587492 1811495 := bstep (se 1 (by rfl) ⟨1358621, by rfl⟩ : syracuseStep 1811495 = 2717243) B2717243
theorem B10871927 : Blo 1587492 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B2679979 : Blo 1587492 2679979 := bstep (se 1 (by rfl) ⟨2009984, by rfl⟩ : syracuseStep 2679979 = 4019969) B4019969
theorem B6784195 : Blo 1587492 6784195 := bstep (se 1 (by rfl) ⟨5088146, by rfl⟩ : syracuseStep 6784195 = 10176293) B10176293
theorem B15262937 : Blo 1587492 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B5801345 : Blo 1587492 5801345 := bstep (se 2 (by rfl) ⟨2175504, by rfl⟩ : syracuseStep 5801345 = 4351009) B4351009
theorem B2901431 : Blo 1587492 2901431 := bstep (se 1 (by rfl) ⟨2176073, by rfl⟩ : syracuseStep 2901431 = 4352147) B4352147
theorem B43484617 : Blo 1587492 43484617 := bstep (se 2 (by rfl) ⟨16306731, by rfl⟩ : syracuseStep 43484617 = 32613463) B32613463
theorem B5359067 : Blo 1587492 5359067 := bstep (se 1 (by rfl) ⟨4019300, by rfl⟩ : syracuseStep 5359067 = 8038601) B8038601
theorem B2680283 : Blo 1587492 2680283 := bstep (se 1 (by rfl) ⟨2010212, by rfl⟩ : syracuseStep 2680283 = 4020425) B4020425
theorem B20645387 : Blo 1587492 20645387 := bstep (se 1 (by rfl) ⟨15484040, by rfl⟩ : syracuseStep 20645387 = 30968081) B30968081
theorem B6030881 : Blo 1587492 6030881 := bstep (se 2 (by rfl) ⟨2261580, by rfl⟩ : syracuseStep 6030881 = 4523161) B4523161
theorem B3573287 : Blo 1587492 3573287 := bstep (se 1 (by rfl) ⟨2679965, by rfl⟩ : syracuseStep 3573287 = 5359931) B5359931
theorem B1787431 : Blo 1587492 1787431 := bstep (se 1 (by rfl) ⟨1340573, by rfl⟩ : syracuseStep 1787431 = 2681147) B2681147
theorem B5088865 : Blo 1587492 5088865 := bstep (se 2 (by rfl) ⟨1908324, by rfl⟩ : syracuseStep 5088865 = 3816649) B3816649
theorem B2680519 : Blo 1587492 2680519 := bstep (se 1 (by rfl) ⟨2010389, by rfl⟩ : syracuseStep 2680519 = 4020779) B4020779
theorem B3393353 : Blo 1587492 3393353 := bstep (se 2 (by rfl) ⟨1272507, by rfl⟩ : syracuseStep 3393353 = 2545015) B2545015
theorem B6031199 : Blo 1587492 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B2680681 : Blo 1587492 2680681 := bstep (se 2 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 2680681 = 2010511) B2010511
theorem B3573611 : Blo 1587492 3573611 := bstep (se 1 (by rfl) ⟨2680208, by rfl⟩ : syracuseStep 3573611 = 5360417) B5360417
theorem B3573665 : Blo 1587492 3573665 := bstep (se 2 (by rfl) ⟨1340124, by rfl⟩ : syracuseStep 3573665 = 2680249) B2680249
theorem B3622843 : Blo 1587492 3622843 := bstep (se 1 (by rfl) ⟨2717132, by rfl⟩ : syracuseStep 3622843 = 5434265) B5434265
theorem B6031367 : Blo 1587492 6031367 := bstep (se 1 (by rfl) ⟨4523525, by rfl⟩ : syracuseStep 6031367 = 9047051) B9047051
theorem B5359769 : Blo 1587492 5359769 := bstep (se 2 (by rfl) ⟨2009913, by rfl⟩ : syracuseStep 5359769 = 4019827) B4019827
theorem B13576349 : Blo 1587492 13576349 := bstep (se 3 (by rfl) ⟨2545565, by rfl⟩ : syracuseStep 13576349 = 5091131) B5091131
theorem B3574007 : Blo 1587492 3574007 := bstep (se 1 (by rfl) ⟨2680505, by rfl⟩ : syracuseStep 3574007 = 5361011) B5361011
theorem B10176779 : Blo 1587492 10176779 := bstep (se 1 (by rfl) ⟨7632584, by rfl⟩ : syracuseStep 10176779 = 15265169) B15265169
theorem B12061061 : Blo 1587492 12061061 := bstep (se 4 (by rfl) ⟨1130724, by rfl⟩ : syracuseStep 12061061 = 2261449) B2261449
theorem B2861455 : Blo 1587492 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B2681275 : Blo 1587492 2681275 := bstep (se 1 (by rfl) ⟨2010956, by rfl⟩ : syracuseStep 2681275 = 4021913) B4021913
theorem B12069323 : Blo 1587492 12069323 := bstep (se 1 (by rfl) ⟨9051992, by rfl⟩ : syracuseStep 12069323 = 18103985) B18103985
theorem B3017179 : Blo 1587492 3017179 := bstep (se 1 (by rfl) ⟨2262884, by rfl⟩ : syracuseStep 3017179 = 4525769) B4525769
theorem B6031853 : Blo 1587492 6031853 := bstep (se 3 (by rfl) ⟨1130972, by rfl⟩ : syracuseStep 6031853 = 2261945) B2261945
theorem B3017225 : Blo 1587492 3017225 := bstep (se 2 (by rfl) ⟨1131459, by rfl⟩ : syracuseStep 3017225 = 2262919) B2262919
theorem B2681383 : Blo 1587492 2681383 := bstep (se 1 (by rfl) ⟨2011037, by rfl⟩ : syracuseStep 2681383 = 4022075) B4022075
theorem B6032171 : Blo 1587492 6032171 := bstep (se 1 (by rfl) ⟨4524128, by rfl⟩ : syracuseStep 6032171 = 9048257) B9048257
theorem B3574601 : Blo 1587492 3574601 := bstep (se 2 (by rfl) ⟨1340475, by rfl⟩ : syracuseStep 3574601 = 2680951) B2680951
theorem B12061547 : Blo 1587492 12061547 := bstep (se 1 (by rfl) ⟨9046160, by rfl⟩ : syracuseStep 12061547 = 18092321) B18092321
theorem B2681707 : Blo 1587492 2681707 := bstep (se 1 (by rfl) ⟨2011280, by rfl⟩ : syracuseStep 2681707 = 4022561) B4022561
theorem B28978067 : Blo 1587492 28978067 := bstep (se 1 (by rfl) ⟨21733550, by rfl⟩ : syracuseStep 28978067 = 43467101) B43467101
theorem B5090311 : Blo 1587492 5090311 := bstep (se 1 (by rfl) ⟨3817733, by rfl⟩ : syracuseStep 5090311 = 7635467) B7635467
theorem B5360957 : Blo 1587492 5360957 := bstep (se 3 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 5360957 = 2010359) B2010359
theorem B19328399 : Blo 1587492 19328399 := bstep (se 1 (by rfl) ⟨14496299, by rfl⟩ : syracuseStep 19328399 = 28992599) B28992599
theorem B7630375 : Blo 1587492 7630375 := bstep (se 1 (by rfl) ⟨5722781, by rfl⟩ : syracuseStep 7630375 = 11445563) B11445563
theorem B33033815 : Blo 1587492 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B7630433 : Blo 1587492 7630433 := bstep (se 2 (by rfl) ⟨2861412, by rfl⟩ : syracuseStep 7630433 = 5722825) B5722825
theorem B3575393 : Blo 1587492 3575393 := bstep (se 2 (by rfl) ⟨1340772, by rfl⟩ : syracuseStep 3575393 = 2681545) B2681545
theorem B8040059 : Blo 1587492 8040059 := bstep (se 1 (by rfl) ⟨6030044, by rfl⟩ : syracuseStep 8040059 = 12060089) B12060089
theorem B9047801 : Blo 1587492 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B2011063 : Blo 1587492 2011063 := bstep (se 1 (by rfl) ⟨1508297, by rfl⟩ : syracuseStep 2011063 = 3016595) B3016595
theorem B3575735 : Blo 1587492 3575735 := bstep (se 1 (by rfl) ⟨2681801, by rfl⟩ : syracuseStep 3575735 = 5363603) B5363603
theorem B18346013 : Blo 1587492 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B8704115 : Blo 1587492 8704115 := bstep (se 1 (by rfl) ⟨6528086, by rfl⟩ : syracuseStep 8704115 = 13056173) B13056173
theorem B5361821 : Blo 1587492 5361821 := bstep (se 3 (by rfl) ⟨1005341, by rfl⟩ : syracuseStep 5361821 = 2010683) B2010683
theorem B2543977 : Blo 1587492 2543977 := bstep (se 2 (by rfl) ⟨953991, by rfl⟩ : syracuseStep 2543977 = 1907983) B1907983
theorem B3576329 : Blo 1587492 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B8155673 : Blo 1587492 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B13750843 : Blo 1587492 13750843 := bstep (se 1 (by rfl) ⟨10313132, by rfl⟩ : syracuseStep 13750843 = 20626265) B20626265
theorem B5362361 : Blo 1587492 5362361 := bstep (se 2 (by rfl) ⟨2010885, by rfl⟩ : syracuseStep 5362361 = 4021771) B4021771
theorem B5092055 : Blo 1587492 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B12063491 : Blo 1587492 12063491 := bstep (se 1 (by rfl) ⟨9047618, by rfl⟩ : syracuseStep 12063491 = 18095237) B18095237
theorem B4019017 : Blo 1587492 4019017 := bstep (se 2 (by rfl) ⟨1507131, by rfl⟩ : syracuseStep 4019017 = 3014263) B3014263
theorem B6034283 : Blo 1587492 6034283 := bstep (se 1 (by rfl) ⟨4525712, by rfl⟩ : syracuseStep 6034283 = 9051425) B9051425
theorem B45814643 : Blo 1587492 45814643 := bstep (se 1 (by rfl) ⟨34360982, by rfl⟩ : syracuseStep 45814643 = 68721965) B68721965
theorem B28980119 : Blo 1587492 28980119 := bstep (se 1 (by rfl) ⟨21735089, by rfl⟩ : syracuseStep 28980119 = 43470179) B43470179
theorem B5436335 : Blo 1587492 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B13571225 : Blo 1587492 13571225 := bstep (se 2 (by rfl) ⟨5089209, by rfl⟩ : syracuseStep 13571225 = 10178419) B10178419
theorem B9049259 : Blo 1587492 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B30545099 : Blo 1587492 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B5362955 : Blo 1587492 5362955 := bstep (se 1 (by rfl) ⟨4022216, by rfl⟩ : syracuseStep 5362955 = 8044433) B8044433
theorem B51533171 : Blo 1587492 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B2381321 : Blo 1587492 2381321 := bstep (se 2 (by rfl) ⟨892995, by rfl⟩ : syracuseStep 2381321 = 1785991) B1785991
theorem B5363225 : Blo 1587492 5363225 := bstep (se 2 (by rfl) ⟨2011209, by rfl⟩ : syracuseStep 5363225 = 4022419) B4022419
theorem B2381351 : Blo 1587492 2381351 := bstep (se 1 (by rfl) ⟨1786013, by rfl⟩ : syracuseStep 2381351 = 3572027) B3572027
theorem B2381435 : Blo 1587492 2381435 := bstep (se 1 (by rfl) ⟨1786076, by rfl⟩ : syracuseStep 2381435 = 3572153) B3572153
theorem B2381561 : Blo 1587492 2381561 := bstep (se 2 (by rfl) ⟨893085, by rfl⟩ : syracuseStep 2381561 = 1786171) B1786171
theorem B2381663 : Blo 1587492 2381663 := bstep (se 1 (by rfl) ⟨1786247, by rfl⟩ : syracuseStep 2381663 = 3572495) B3572495
theorem B2381675 : Blo 1587492 2381675 := bstep (se 1 (by rfl) ⟨1786256, by rfl⟩ : syracuseStep 2381675 = 3572513) B3572513
theorem B22902709 : Blo 1587492 22902709 := bstep (se 5 (by rfl) ⟨1073564, by rfl⟩ : syracuseStep 22902709 = 2147129) B2147129
theorem B4020151 : Blo 1587492 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B11450321 : Blo 1587492 11450321 := bstep (se 2 (by rfl) ⟨4293870, by rfl⟩ : syracuseStep 11450321 = 8587741) B8587741
theorem B5724179 : Blo 1587492 5724179 := bstep (se 1 (by rfl) ⟨4293134, by rfl⟩ : syracuseStep 5724179 = 8586269) B8586269
theorem B2381903 : Blo 1587492 2381903 := bstep (se 1 (by rfl) ⟨1786427, by rfl⟩ : syracuseStep 2381903 = 3572855) B3572855
theorem B6436979 : Blo 1587492 6436979 := bstep (se 1 (by rfl) ⟨4827734, by rfl⟩ : syracuseStep 6436979 = 9655469) B9655469
theorem B2545835 : Blo 1587492 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B2382023 : Blo 1587492 2382023 := bstep (se 1 (by rfl) ⟨1786517, by rfl⟩ : syracuseStep 2382023 = 3573035) B3573035
theorem B1587495 : Blo 1587492 1587495 := bstep (se 1 (by rfl) ⟨1190621, by rfl⟩ : syracuseStep 1587495 = 2381243) B2381243
theorem B5167421 : Blo 1587492 5167421 := bstep (se 3 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 5167421 = 1937783) B1937783
theorem B8042813 : Blo 1587492 8042813 := bstep (se 3 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 8042813 = 3016055) B3016055
theorem B1587535 : Blo 1587492 1587535 := bstep (se 1 (by rfl) ⟨1190651, by rfl⟩ : syracuseStep 1587535 = 2381303) B2381303
theorem B1587551 : Blo 1587492 1587551 := bstep (se 1 (by rfl) ⟨1190663, by rfl⟩ : syracuseStep 1587551 = 2381327) B2381327
theorem B2382185 : Blo 1587492 2382185 := bstep (se 2 (by rfl) ⟨893319, by rfl⟩ : syracuseStep 2382185 = 1786639) B1786639
theorem B1587579 : Blo 1587492 1587579 := bstep (se 1 (by rfl) ⟨1190684, by rfl⟩ : syracuseStep 1587579 = 2381369) B2381369
theorem B48888197 : Blo 1587492 48888197 := bstep (se 4 (by rfl) ⟨4583268, by rfl⟩ : syracuseStep 48888197 = 9166537) B9166537
theorem B1587631 : Blo 1587492 1587631 := bstep (se 1 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 1587631 = 2381447) B2381447
theorem B2382263 : Blo 1587492 2382263 := bstep (se 1 (by rfl) ⟨1786697, by rfl⟩ : syracuseStep 2382263 = 3573395) B3573395
theorem B1587655 : Blo 1587492 1587655 := bstep (se 1 (by rfl) ⟨1190741, by rfl⟩ : syracuseStep 1587655 = 2381483) B2381483
theorem B1587675 : Blo 1587492 1587675 := bstep (se 1 (by rfl) ⟨1190756, by rfl⟩ : syracuseStep 1587675 = 2381513) B2381513
theorem B2382299 : Blo 1587492 2382299 := bstep (se 1 (by rfl) ⟨1786724, by rfl⟩ : syracuseStep 2382299 = 3573449) B3573449
theorem B1587751 : Blo 1587492 1587751 := bstep (se 1 (by rfl) ⟨1190813, by rfl⟩ : syracuseStep 1587751 = 2381627) B2381627
theorem B1587791 : Blo 1587492 1587791 := bstep (se 1 (by rfl) ⟨1190843, by rfl⟩ : syracuseStep 1587791 = 2381687) B2381687
theorem B1587807 : Blo 1587492 1587807 := bstep (se 1 (by rfl) ⟨1190855, by rfl⟩ : syracuseStep 1587807 = 2381711) B2381711
theorem B1587835 : Blo 1587492 1587835 := bstep (se 1 (by rfl) ⟨1190876, by rfl⟩ : syracuseStep 1587835 = 2381753) B2381753
theorem B12221063 : Blo 1587492 12221063 := bstep (se 1 (by rfl) ⟨9165797, by rfl⟩ : syracuseStep 12221063 = 18331595) B18331595
theorem B5364359 : Blo 1587492 5364359 := bstep (se 1 (by rfl) ⟨4023269, by rfl⟩ : syracuseStep 5364359 = 8046539) B8046539
theorem B1587887 : Blo 1587492 1587887 := bstep (se 1 (by rfl) ⟨1190915, by rfl⟩ : syracuseStep 1587887 = 2381831) B2381831
theorem B41286323 : Blo 1587492 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B6027965 : Blo 1587492 6027965 := bstep (se 3 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 6027965 = 2260487) B2260487
theorem B5364413 : Blo 1587492 5364413 := bstep (se 3 (by rfl) ⟨1005827, by rfl⟩ : syracuseStep 5364413 = 2011655) B2011655
theorem B1587911 : Blo 1587492 1587911 := bstep (se 1 (by rfl) ⟨1190933, by rfl⟩ : syracuseStep 1587911 = 2381867) B2381867
theorem B1587931 : Blo 1587492 1587931 := bstep (se 1 (by rfl) ⟨1190948, by rfl⟩ : syracuseStep 1587931 = 2381897) B2381897
theorem B8592131 : Blo 1587492 8592131 := bstep (se 1 (by rfl) ⟨6444098, by rfl⟩ : syracuseStep 8592131 = 12888197) B12888197
theorem B1588007 : Blo 1587492 1588007 := bstep (se 1 (by rfl) ⟨1191005, by rfl⟩ : syracuseStep 1588007 = 2382011) B2382011
theorem B1588047 : Blo 1587492 1588047 := bstep (se 1 (by rfl) ⟨1191035, by rfl⟩ : syracuseStep 1588047 = 2382071) B2382071
theorem B1588063 : Blo 1587492 1588063 := bstep (se 1 (by rfl) ⟨1191047, by rfl⟩ : syracuseStep 1588063 = 2382095) B2382095
theorem B1588091 : Blo 1587492 1588091 := bstep (se 1 (by rfl) ⟨1191068, by rfl⟩ : syracuseStep 1588091 = 2382137) B2382137
theorem B1588143 : Blo 1587492 1588143 := bstep (se 1 (by rfl) ⟨1191107, by rfl⟩ : syracuseStep 1588143 = 2382215) B2382215
theorem B2382767 : Blo 1587492 2382767 := bstep (se 1 (by rfl) ⟨1787075, by rfl⟩ : syracuseStep 2382767 = 3574151) B3574151
theorem B3218359 : Blo 1587492 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B1588167 : Blo 1587492 1588167 := bstep (se 1 (by rfl) ⟨1191125, by rfl⟩ : syracuseStep 1588167 = 2382251) B2382251
theorem B1588187 : Blo 1587492 1588187 := bstep (se 1 (by rfl) ⟨1191140, by rfl⟩ : syracuseStep 1588187 = 2382281) B2382281
theorem B2382857 : Blo 1587492 2382857 := bstep (se 2 (by rfl) ⟨893571, by rfl⟩ : syracuseStep 2382857 = 1787143) B1787143
theorem B1588263 : Blo 1587492 1588263 := bstep (se 1 (by rfl) ⟨1191197, by rfl⟩ : syracuseStep 1588263 = 2382395) B2382395
theorem B2382887 : Blo 1587492 2382887 := bstep (se 1 (by rfl) ⟨1787165, by rfl⟩ : syracuseStep 2382887 = 3574331) B3574331
theorem B13065259 : Blo 1587492 13065259 := bstep (se 1 (by rfl) ⟨9798944, by rfl⟩ : syracuseStep 13065259 = 19597889) B19597889
theorem B1588303 : Blo 1587492 1588303 := bstep (se 1 (by rfl) ⟨1191227, by rfl⟩ : syracuseStep 1588303 = 2382455) B2382455
theorem B1588319 : Blo 1587492 1588319 := bstep (se 1 (by rfl) ⟨1191239, by rfl⟩ : syracuseStep 1588319 = 2382479) B2382479
theorem B1588347 : Blo 1587492 1588347 := bstep (se 1 (by rfl) ⟨1191260, by rfl⟩ : syracuseStep 1588347 = 2382521) B2382521
theorem B2382971 : Blo 1587492 2382971 := bstep (se 1 (by rfl) ⟨1787228, by rfl⟩ : syracuseStep 2382971 = 3574457) B3574457
theorem B1588399 : Blo 1587492 1588399 := bstep (se 1 (by rfl) ⟨1191299, by rfl⟩ : syracuseStep 1588399 = 2382599) B2382599
theorem B20643011 : Blo 1587492 20643011 := bstep (se 1 (by rfl) ⟨15482258, by rfl⟩ : syracuseStep 20643011 = 30964517) B30964517
theorem B1588423 : Blo 1587492 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B1588443 : Blo 1587492 1588443 := bstep (se 1 (by rfl) ⟨1191332, by rfl⟩ : syracuseStep 1588443 = 2382665) B2382665
theorem B62774509 : Blo 1587492 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B6200567 : Blo 1587492 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B2383097 : Blo 1587492 2383097 := bstep (se 2 (by rfl) ⟨893661, by rfl⟩ : syracuseStep 2383097 = 1787323) B1787323
theorem B34331921 : Blo 1587492 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B1588519 : Blo 1587492 1588519 := bstep (se 1 (by rfl) ⟨1191389, by rfl⟩ : syracuseStep 1588519 = 2382779) B2382779
theorem B1588559 : Blo 1587492 1588559 := bstep (se 1 (by rfl) ⟨1191419, by rfl⟩ : syracuseStep 1588559 = 2382839) B2382839
theorem B3054943 : Blo 1587492 3054943 := bstep (se 1 (by rfl) ⟨2291207, by rfl⟩ : syracuseStep 3054943 = 4582415) B4582415
theorem B1588575 : Blo 1587492 1588575 := bstep (se 1 (by rfl) ⟨1191431, by rfl⟩ : syracuseStep 1588575 = 2382863) B2382863
theorem B2383199 : Blo 1587492 2383199 := bstep (se 1 (by rfl) ⟨1787399, by rfl⟩ : syracuseStep 2383199 = 3574799) B3574799
theorem B4021609 : Blo 1587492 4021609 := bstep (se 2 (by rfl) ⟨1508103, by rfl⟩ : syracuseStep 4021609 = 3016207) B3016207
theorem B2383211 : Blo 1587492 2383211 := bstep (se 1 (by rfl) ⟨1787408, by rfl⟩ : syracuseStep 2383211 = 3574817) B3574817
theorem B1588603 : Blo 1587492 1588603 := bstep (se 1 (by rfl) ⟨1191452, by rfl⟩ : syracuseStep 1588603 = 2382905) B2382905
theorem B1588655 : Blo 1587492 1588655 := bstep (se 1 (by rfl) ⟨1191491, by rfl⟩ : syracuseStep 1588655 = 2382983) B2382983
theorem B24444341 : Blo 1587492 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B1588679 : Blo 1587492 1588679 := bstep (se 1 (by rfl) ⟨1191509, by rfl⟩ : syracuseStep 1588679 = 2383019) B2383019
theorem B1588699 : Blo 1587492 1588699 := bstep (se 1 (by rfl) ⟨1191524, by rfl⟩ : syracuseStep 1588699 = 2383049) B2383049
theorem B48905693 : Blo 1587492 48905693 := bstep (se 3 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 48905693 = 18339635) B18339635
theorem B1588775 : Blo 1587492 1588775 := bstep (se 1 (by rfl) ⟨1191581, by rfl⟩ : syracuseStep 1588775 = 2383163) B2383163
theorem B1588815 : Blo 1587492 1588815 := bstep (se 1 (by rfl) ⟨1191611, by rfl⟩ : syracuseStep 1588815 = 2383223) B2383223
theorem B2383439 : Blo 1587492 2383439 := bstep (se 1 (by rfl) ⟨1787579, by rfl⟩ : syracuseStep 2383439 = 3575159) B3575159
theorem B1588831 : Blo 1587492 1588831 := bstep (se 1 (by rfl) ⟨1191623, by rfl⟩ : syracuseStep 1588831 = 2383247) B2383247
theorem B1588859 : Blo 1587492 1588859 := bstep (se 1 (by rfl) ⟨1191644, by rfl⟩ : syracuseStep 1588859 = 2383289) B2383289
theorem B4021883 : Blo 1587492 4021883 := bstep (se 1 (by rfl) ⟨3016412, by rfl⟩ : syracuseStep 4021883 = 6032825) B6032825
theorem B22912631 : Blo 1587492 22912631 := bstep (se 1 (by rfl) ⟨17184473, by rfl⟩ : syracuseStep 22912631 = 34368947) B34368947
theorem B11452049 : Blo 1587492 11452049 := bstep (se 2 (by rfl) ⟨4294518, by rfl⟩ : syracuseStep 11452049 = 8589037) B8589037
theorem B1588911 : Blo 1587492 1588911 := bstep (se 1 (by rfl) ⟨1191683, by rfl⟩ : syracuseStep 1588911 = 2383367) B2383367
theorem B1588935 : Blo 1587492 1588935 := bstep (se 1 (by rfl) ⟨1191701, by rfl⟩ : syracuseStep 1588935 = 2383403) B2383403
theorem B2383559 : Blo 1587492 2383559 := bstep (se 1 (by rfl) ⟨1787669, by rfl⟩ : syracuseStep 2383559 = 3575339) B3575339
theorem B1588955 : Blo 1587492 1588955 := bstep (se 1 (by rfl) ⟨1191716, by rfl⟩ : syracuseStep 1588955 = 2383433) B2383433
theorem B7634681 : Blo 1587492 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B20643617 : Blo 1587492 20643617 := bstep (se 2 (by rfl) ⟨7741356, by rfl⟩ : syracuseStep 20643617 = 15482713) B15482713
theorem B1589031 : Blo 1587492 1589031 := bstep (se 1 (by rfl) ⟨1191773, by rfl⟩ : syracuseStep 1589031 = 2383547) B2383547
theorem B1589071 : Blo 1587492 1589071 := bstep (se 1 (by rfl) ⟨1191803, by rfl⟩ : syracuseStep 1589071 = 2383607) B2383607
theorem B1695583 : Blo 1587492 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B1589087 : Blo 1587492 1589087 := bstep (se 1 (by rfl) ⟨1191815, by rfl⟩ : syracuseStep 1589087 = 2383631) B2383631
theorem B2383721 : Blo 1587492 2383721 := bstep (se 2 (by rfl) ⟨893895, by rfl⟩ : syracuseStep 2383721 = 1787791) B1787791
theorem B4349803 : Blo 1587492 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B5087083 : Blo 1587492 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B1589115 : Blo 1587492 1589115 := bstep (se 1 (by rfl) ⟨1191836, by rfl⟩ : syracuseStep 1589115 = 2383673) B2383673
theorem B10174369 : Blo 1587492 10174369 := bstep (se 2 (by rfl) ⟨3815388, by rfl⟩ : syracuseStep 10174369 = 7630777) B7630777
theorem B1589167 : Blo 1587492 1589167 := bstep (se 1 (by rfl) ⟨1191875, by rfl⟩ : syracuseStep 1589167 = 2383751) B2383751
theorem B2383799 : Blo 1587492 2383799 := bstep (se 1 (by rfl) ⟨1787849, by rfl⟩ : syracuseStep 2383799 = 3575699) B3575699
theorem B1589191 : Blo 1587492 1589191 := bstep (se 1 (by rfl) ⟨1191893, by rfl⟩ : syracuseStep 1589191 = 2383787) B2383787
theorem B1589211 : Blo 1587492 1589211 := bstep (se 1 (by rfl) ⟨1191908, by rfl⟩ : syracuseStep 1589211 = 2383817) B2383817
theorem B2383835 : Blo 1587492 2383835 := bstep (se 1 (by rfl) ⟨1787876, by rfl⟩ : syracuseStep 2383835 = 3575753) B3575753
theorem B12230675 : Blo 1587492 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B8044595 : Blo 1587492 8044595 := bstep (se 1 (by rfl) ⟨6033446, by rfl⟩ : syracuseStep 8044595 = 12066893) B12066893
theorem B2384219 : Blo 1587492 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B3572135 : Blo 1587492 3572135 := bstep (se 1 (by rfl) ⟨2679101, by rfl⟩ : syracuseStep 3572135 = 5358203) B5358203
theorem B1786279 : Blo 1587492 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B3391969 : Blo 1587492 3391969 := bstep (se 2 (by rfl) ⟨1271988, by rfl⟩ : syracuseStep 3391969 = 2543977) B2543977
theorem B3015137 : Blo 1587492 3015137 := bstep (se 2 (by rfl) ⟨1130676, by rfl⟩ : syracuseStep 3015137 = 2261353) B2261353
theorem B3572243 : Blo 1587492 3572243 := bstep (se 1 (by rfl) ⟨2679182, by rfl⟩ : syracuseStep 3572243 = 5358365) B5358365
theorem B4022855 : Blo 1587492 4022855 := bstep (se 1 (by rfl) ⟨3017141, by rfl⟩ : syracuseStep 4022855 = 6034283) B6034283
theorem B3572297 : Blo 1587492 3572297 := bstep (se 2 (by rfl) ⟨1339611, by rfl⟩ : syracuseStep 3572297 = 2679223) B2679223
theorem B4022905 : Blo 1587492 4022905 := bstep (se 2 (by rfl) ⟨1508589, by rfl⟩ : syracuseStep 4022905 = 3017179) B3017179
theorem B18334457 : Blo 1587492 18334457 := bstep (se 2 (by rfl) ⟨6875421, by rfl⟩ : syracuseStep 18334457 = 13750843) B13750843
theorem B10175291 : Blo 1587492 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B3867563 : Blo 1587492 3867563 := bstep (se 1 (by rfl) ⟨2900672, by rfl⟩ : syracuseStep 3867563 = 5801345) B5801345
theorem B1934287 : Blo 1587492 1934287 := bstep (se 1 (by rfl) ⟨1450715, by rfl⟩ : syracuseStep 1934287 = 2901431) B2901431
theorem B3572711 : Blo 1587492 3572711 := bstep (se 1 (by rfl) ⟨2679533, by rfl⟩ : syracuseStep 3572711 = 5359067) B5359067
theorem B1786855 : Blo 1587492 1786855 := bstep (se 1 (by rfl) ⟨1340141, by rfl⟩ : syracuseStep 1786855 = 2680283) B2680283
theorem B13763591 : Blo 1587492 13763591 := bstep (se 1 (by rfl) ⟨10322693, by rfl⟩ : syracuseStep 13763591 = 20645387) B20645387
theorem B5358689 : Blo 1587492 5358689 := bstep (se 2 (by rfl) ⟨2009508, by rfl⟩ : syracuseStep 5358689 = 4019017) B4019017
theorem B3573089 : Blo 1587492 3573089 := bstep (se 2 (by rfl) ⟨1339908, by rfl⟩ : syracuseStep 3573089 = 2679817) B2679817
theorem B3573179 : Blo 1587492 3573179 := bstep (se 1 (by rfl) ⟨2679884, by rfl⟩ : syracuseStep 3573179 = 5359769) B5359769
theorem B6784519 : Blo 1587492 6784519 := bstep (se 1 (by rfl) ⟨5088389, by rfl⟩ : syracuseStep 6784519 = 10176779) B10176779
theorem B3573305 : Blo 1587492 3573305 := bstep (se 2 (by rfl) ⟨1339989, by rfl⟩ : syracuseStep 3573305 = 2679979) B2679979
theorem B9045593 : Blo 1587492 9045593 := bstep (se 2 (by rfl) ⟨3392097, by rfl⟩ : syracuseStep 9045593 = 6784195) B6784195
theorem B8046215 : Blo 1587492 8046215 := bstep (se 1 (by rfl) ⟨6034661, by rfl⟩ : syracuseStep 8046215 = 12069323) B12069323
theorem B83699345 : Blo 1587492 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B4073257 : Blo 1587492 4073257 := bstep (se 2 (by rfl) ⟨1527471, by rfl⟩ : syracuseStep 4073257 = 3054943) B3054943
theorem B5728087 : Blo 1587492 5728087 := bstep (se 1 (by rfl) ⟨4296065, by rfl⟩ : syracuseStep 5728087 = 8592131) B8592131
theorem B19318711 : Blo 1587492 19318711 := bstep (se 1 (by rfl) ⟨14489033, by rfl⟩ : syracuseStep 19318711 = 28978067) B28978067
theorem B6785153 : Blo 1587492 6785153 := bstep (se 2 (by rfl) ⟨2544432, by rfl⟩ : syracuseStep 6785153 = 5088865) B5088865
theorem B3573971 : Blo 1587492 3573971 := bstep (se 1 (by rfl) ⟨2680478, by rfl⟩ : syracuseStep 3573971 = 5360957) B5360957
theorem B3574025 : Blo 1587492 3574025 := bstep (se 2 (by rfl) ⟨1340259, by rfl⟩ : syracuseStep 3574025 = 2680519) B2680519
theorem B16296227 : Blo 1587492 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B22022543 : Blo 1587492 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B5360039 : Blo 1587492 5360039 := bstep (se 1 (by rfl) ⟨4020029, by rfl⟩ : syracuseStep 5360039 = 8040059) B8040059
theorem B2681255 : Blo 1587492 2681255 := bstep (se 1 (by rfl) ⟨2010941, by rfl⟩ : syracuseStep 2681255 = 4021883) B4021883
theorem B3574241 : Blo 1587492 3574241 := bstep (se 2 (by rfl) ⟨1340340, by rfl⟩ : syracuseStep 3574241 = 2680681) B2680681
theorem B6031867 : Blo 1587492 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B5089787 : Blo 1587492 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B5360201 : Blo 1587492 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B2681417 : Blo 1587492 2681417 := bstep (se 2 (by rfl) ⟨1005531, by rfl⟩ : syracuseStep 2681417 = 2011063) B2011063
theorem B8039087 : Blo 1587492 8039087 := bstep (se 1 (by rfl) ⟨6029315, by rfl⟩ : syracuseStep 8039087 = 12058631) B12058631
theorem B5802743 : Blo 1587492 5802743 := bstep (se 1 (by rfl) ⟨4352057, by rfl⟩ : syracuseStep 5802743 = 8704115) B8704115
theorem B3574547 : Blo 1587492 3574547 := bstep (se 1 (by rfl) ⟨2680910, by rfl⟩ : syracuseStep 3574547 = 5361821) B5361821
theorem B8039411 : Blo 1587492 8039411 := bstep (se 1 (by rfl) ⟨6029558, by rfl⟩ : syracuseStep 8039411 = 12059117) B12059117
theorem B3574907 : Blo 1587492 3574907 := bstep (se 1 (by rfl) ⟨2681180, by rfl⟩ : syracuseStep 3574907 = 5362361) B5362361
theorem B3394703 : Blo 1587492 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B30518491 : Blo 1587492 30518491 := bstep (se 1 (by rfl) ⟨22888868, by rfl⟩ : syracuseStep 30518491 = 45777737) B45777737
theorem B30543095 : Blo 1587492 30543095 := bstep (se 1 (by rfl) ⟨22907321, by rfl⟩ : syracuseStep 30543095 = 45814643) B45814643
theorem B3575033 : Blo 1587492 3575033 := bstep (se 2 (by rfl) ⟨1340637, by rfl⟩ : syracuseStep 3575033 = 2681275) B2681275
theorem B19320079 : Blo 1587492 19320079 := bstep (se 1 (by rfl) ⟨14490059, by rfl⟩ : syracuseStep 19320079 = 28980119) B28980119
theorem B3575177 : Blo 1587492 3575177 := bstep (se 2 (by rfl) ⟨1340691, by rfl⟩ : syracuseStep 3575177 = 2681383) B2681383
theorem B9047483 : Blo 1587492 9047483 := bstep (se 1 (by rfl) ⟨6785612, by rfl⟩ : syracuseStep 9047483 = 13571225) B13571225
theorem B6032839 : Blo 1587492 6032839 := bstep (se 1 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 6032839 = 9049259) B9049259
theorem B3575303 : Blo 1587492 3575303 := bstep (se 1 (by rfl) ⟨2681477, by rfl⟩ : syracuseStep 3575303 = 5362955) B5362955
theorem B3575483 : Blo 1587492 3575483 := bstep (se 1 (by rfl) ⟨2681612, by rfl⟩ : syracuseStep 3575483 = 5363225) B5363225
theorem B3575609 : Blo 1587492 3575609 := bstep (se 2 (by rfl) ⟨1340853, by rfl⟩ : syracuseStep 3575609 = 2681707) B2681707
theorem B6787081 : Blo 1587492 6787081 := bstep (se 2 (by rfl) ⟨2545155, by rfl⟩ : syracuseStep 6787081 = 5090311) B5090311
theorem B17420345 : Blo 1587492 17420345 := bstep (se 2 (by rfl) ⟨6532629, by rfl⟩ : syracuseStep 17420345 = 13065259) B13065259
theorem B3444947 : Blo 1587492 3444947 := bstep (se 1 (by rfl) ⟨2583710, by rfl⟩ : syracuseStep 3444947 = 5167421) B5167421
theorem B5361875 : Blo 1587492 5361875 := bstep (se 1 (by rfl) ⟨4021406, by rfl⟩ : syracuseStep 5361875 = 8042813) B8042813
theorem B32592131 : Blo 1587492 32592131 := bstep (se 1 (by rfl) ⟨24444098, by rfl⟩ : syracuseStep 32592131 = 48888197) B48888197
theorem B8040707 : Blo 1587492 8040707 := bstep (se 1 (by rfl) ⟨6030530, by rfl⟩ : syracuseStep 8040707 = 12061061) B12061061
theorem B2011483 : Blo 1587492 2011483 := bstep (se 1 (by rfl) ⟨1508612, by rfl⟩ : syracuseStep 2011483 = 3017225) B3017225
theorem B8147375 : Blo 1587492 8147375 := bstep (se 1 (by rfl) ⟨6110531, by rfl⟩ : syracuseStep 8147375 = 12221063) B12221063
theorem B3576239 : Blo 1587492 3576239 := bstep (se 1 (by rfl) ⟨2682179, by rfl⟩ : syracuseStep 3576239 = 5364359) B5364359
theorem B4018643 : Blo 1587492 4018643 := bstep (se 1 (by rfl) ⟨3013982, by rfl⟩ : syracuseStep 4018643 = 6027965) B6027965
theorem B3576275 : Blo 1587492 3576275 := bstep (se 1 (by rfl) ⟨2682206, by rfl⟩ : syracuseStep 3576275 = 5364413) B5364413
theorem B5362145 : Blo 1587492 5362145 := bstep (se 2 (by rfl) ⟨2010804, by rfl⟩ : syracuseStep 5362145 = 4021609) B4021609
theorem B8041031 : Blo 1587492 8041031 := bstep (se 1 (by rfl) ⟨6030773, by rfl⟩ : syracuseStep 8041031 = 12061547) B12061547
theorem B57979489 : Blo 1587492 57979489 := bstep (se 2 (by rfl) ⟨21742308, by rfl⟩ : syracuseStep 57979489 = 43484617) B43484617
theorem B4133711 : Blo 1587492 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B9048941 : Blo 1587492 9048941 := bstep (se 3 (by rfl) ⟨1696676, by rfl⟩ : syracuseStep 9048941 = 3393353) B3393353
theorem B15275087 : Blo 1587492 15275087 := bstep (se 1 (by rfl) ⟨11456315, by rfl⟩ : syracuseStep 15275087 = 22912631) B22912631
theorem B14496893 : Blo 1587492 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B30536945 : Blo 1587492 30536945 := bstep (se 2 (by rfl) ⟨11451354, by rfl⟩ : syracuseStep 30536945 = 22902709) B22902709
theorem B4830457 : Blo 1587492 4830457 := bstep (se 2 (by rfl) ⟨1811421, by rfl⟩ : syracuseStep 4830457 = 3622843) B3622843
theorem B6034783 : Blo 1587492 6034783 := bstep (se 1 (by rfl) ⟨4526087, by rfl⟩ : syracuseStep 6034783 = 9052175) B9052175
theorem B5658017 : Blo 1587492 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B4830653 : Blo 1587492 4830653 := bstep (se 3 (by rfl) ⟨905747, by rfl⟩ : syracuseStep 4830653 = 1811495) B1811495
theorem B2381255 : Blo 1587492 2381255 := bstep (se 1 (by rfl) ⟨1785941, by rfl⟩ : syracuseStep 2381255 = 3571883) B3571883
theorem B4019807 : Blo 1587492 4019807 := bstep (se 1 (by rfl) ⟨3014855, by rfl⟩ : syracuseStep 4019807 = 6029711) B6029711
theorem B5363387 : Blo 1587492 5363387 := bstep (se 1 (by rfl) ⟨4022540, by rfl⟩ : syracuseStep 5363387 = 8045081) B8045081
theorem B5437115 : Blo 1587492 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B6788893 : Blo 1587492 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B2381609 : Blo 1587492 2381609 := bstep (se 2 (by rfl) ⟨893103, by rfl⟩ : syracuseStep 2381609 = 1786207) B1786207
theorem B2381615 : Blo 1587492 2381615 := bstep (se 1 (by rfl) ⟨1786211, by rfl⟩ : syracuseStep 2381615 = 3572423) B3572423
theorem B2545463 : Blo 1587492 2545463 := bstep (se 1 (by rfl) ⟨1909097, by rfl⟩ : syracuseStep 2545463 = 3818195) B3818195
theorem B8042327 : Blo 1587492 8042327 := bstep (se 1 (by rfl) ⟨6031745, by rfl⟩ : syracuseStep 8042327 = 12063491) B12063491
theorem B3815273 : Blo 1587492 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B7247951 : Blo 1587492 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B20363399 : Blo 1587492 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B34355447 : Blo 1587492 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B2382089 : Blo 1587492 2382089 := bstep (se 2 (by rfl) ⟨893283, by rfl⟩ : syracuseStep 2382089 = 1786567) B1786567
theorem B1587547 : Blo 1587492 1587547 := bstep (se 1 (by rfl) ⟨1190660, by rfl⟩ : syracuseStep 1587547 = 2381321) B2381321
theorem B4020587 : Blo 1587492 4020587 := bstep (se 1 (by rfl) ⟨3015440, by rfl⟩ : syracuseStep 4020587 = 6030881) B6030881
theorem B1587567 : Blo 1587492 1587567 := bstep (se 1 (by rfl) ⟨1190675, by rfl⟩ : syracuseStep 1587567 = 2381351) B2381351
theorem B2382191 : Blo 1587492 2382191 := bstep (se 1 (by rfl) ⟨1786643, by rfl⟩ : syracuseStep 2382191 = 3573287) B3573287
theorem B1587623 : Blo 1587492 1587623 := bstep (se 1 (by rfl) ⟨1190717, by rfl⟩ : syracuseStep 1587623 = 2381435) B2381435
theorem B1587707 : Blo 1587492 1587707 := bstep (se 1 (by rfl) ⟨1190780, by rfl⟩ : syracuseStep 1587707 = 2381561) B2381561
theorem B1587775 : Blo 1587492 1587775 := bstep (se 1 (by rfl) ⟨1190831, by rfl⟩ : syracuseStep 1587775 = 2381663) B2381663
theorem B4020799 : Blo 1587492 4020799 := bstep (se 1 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 4020799 = 6031199) B6031199
theorem B1587783 : Blo 1587492 1587783 := bstep (se 1 (by rfl) ⟨1190837, by rfl⟩ : syracuseStep 1587783 = 2381675) B2381675
theorem B2382407 : Blo 1587492 2382407 := bstep (se 1 (by rfl) ⟨1786805, by rfl⟩ : syracuseStep 2382407 = 3573611) B3573611
theorem B4291145 : Blo 1587492 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B2382443 : Blo 1587492 2382443 := bstep (se 1 (by rfl) ⟨1786832, by rfl⟩ : syracuseStep 2382443 = 3573665) B3573665
theorem B7633547 : Blo 1587492 7633547 := bstep (se 1 (by rfl) ⟨5725160, by rfl⟩ : syracuseStep 7633547 = 11450321) B11450321
theorem B4020911 : Blo 1587492 4020911 := bstep (se 1 (by rfl) ⟨3015683, by rfl⟩ : syracuseStep 4020911 = 6031367) B6031367
theorem B3816119 : Blo 1587492 3816119 := bstep (se 1 (by rfl) ⟨2862089, by rfl⟩ : syracuseStep 3816119 = 5724179) B5724179
theorem B1587935 : Blo 1587492 1587935 := bstep (se 1 (by rfl) ⟨1190951, by rfl⟩ : syracuseStep 1587935 = 2381903) B2381903
theorem B4291319 : Blo 1587492 4291319 := bstep (se 1 (by rfl) ⟨3218489, by rfl⟩ : syracuseStep 4291319 = 6436979) B6436979
theorem B9050899 : Blo 1587492 9050899 := bstep (se 1 (by rfl) ⟨6788174, by rfl⟩ : syracuseStep 9050899 = 13576349) B13576349
theorem B1588015 : Blo 1587492 1588015 := bstep (se 1 (by rfl) ⟨1191011, by rfl⟩ : syracuseStep 1588015 = 2382023) B2382023
theorem B2382671 : Blo 1587492 2382671 := bstep (se 1 (by rfl) ⟨1787003, by rfl⟩ : syracuseStep 2382671 = 3574007) B3574007
theorem B1588123 : Blo 1587492 1588123 := bstep (se 1 (by rfl) ⟨1191092, by rfl⟩ : syracuseStep 1588123 = 2382185) B2382185
theorem B1588175 : Blo 1587492 1588175 := bstep (se 1 (by rfl) ⟨1191131, by rfl⟩ : syracuseStep 1588175 = 2382263) B2382263
theorem B1588199 : Blo 1587492 1588199 := bstep (se 1 (by rfl) ⟨1191149, by rfl⟩ : syracuseStep 1588199 = 2382299) B2382299
theorem B4021235 : Blo 1587492 4021235 := bstep (se 1 (by rfl) ⟨3015926, by rfl⟩ : syracuseStep 4021235 = 6031853) B6031853
theorem B27524215 : Blo 1587492 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B9043109 : Blo 1587492 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B4021447 : Blo 1587492 4021447 := bstep (se 1 (by rfl) ⟨3016085, by rfl⟩ : syracuseStep 4021447 = 6032171) B6032171
theorem B2383067 : Blo 1587492 2383067 := bstep (se 1 (by rfl) ⟨1787300, by rfl⟩ : syracuseStep 2383067 = 3574601) B3574601
theorem B1588511 : Blo 1587492 1588511 := bstep (se 1 (by rfl) ⟨1191383, by rfl⟩ : syracuseStep 1588511 = 2382767) B2382767
theorem B1588571 : Blo 1587492 1588571 := bstep (se 1 (by rfl) ⟨1191428, by rfl⟩ : syracuseStep 1588571 = 2382857) B2382857
theorem B1588591 : Blo 1587492 1588591 := bstep (se 1 (by rfl) ⟨1191443, by rfl⟩ : syracuseStep 1588591 = 2382887) B2382887
theorem B10173833 : Blo 1587492 10173833 := bstep (se 2 (by rfl) ⟨3815187, by rfl⟩ : syracuseStep 10173833 = 7630375) B7630375
theorem B2383241 : Blo 1587492 2383241 := bstep (se 2 (by rfl) ⟨893715, by rfl⟩ : syracuseStep 2383241 = 1787431) B1787431
theorem B1588647 : Blo 1587492 1588647 := bstep (se 1 (by rfl) ⟨1191485, by rfl⟩ : syracuseStep 1588647 = 2382971) B2382971
theorem B55049645 : Blo 1587492 55049645 := bstep (se 3 (by rfl) ⟨10321808, by rfl⟩ : syracuseStep 55049645 = 20643617) B20643617
theorem B13762007 : Blo 1587492 13762007 := bstep (se 1 (by rfl) ⟨10321505, by rfl⟩ : syracuseStep 13762007 = 20643011) B20643011
theorem B1588731 : Blo 1587492 1588731 := bstep (se 1 (by rfl) ⟨1191548, by rfl⟩ : syracuseStep 1588731 = 2383097) B2383097
theorem B22887947 : Blo 1587492 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B1588799 : Blo 1587492 1588799 := bstep (se 1 (by rfl) ⟨1191599, by rfl⟩ : syracuseStep 1588799 = 2383199) B2383199
theorem B1588807 : Blo 1587492 1588807 := bstep (se 1 (by rfl) ⟨1191605, by rfl⟩ : syracuseStep 1588807 = 2383211) B2383211
theorem B12885599 : Blo 1587492 12885599 := bstep (se 1 (by rfl) ⟨9664199, by rfl⟩ : syracuseStep 12885599 = 19328399) B19328399
theorem B32603795 : Blo 1587492 32603795 := bstep (se 1 (by rfl) ⟨24452846, by rfl⟩ : syracuseStep 32603795 = 48905693) B48905693
theorem B1588959 : Blo 1587492 1588959 := bstep (se 1 (by rfl) ⟨1191719, by rfl⟩ : syracuseStep 1588959 = 2383439) B2383439
theorem B5086955 : Blo 1587492 5086955 := bstep (se 1 (by rfl) ⟨3815216, by rfl⟩ : syracuseStep 5086955 = 7630433) B7630433
theorem B2383595 : Blo 1587492 2383595 := bstep (se 1 (by rfl) ⟨1787696, by rfl⟩ : syracuseStep 2383595 = 3575393) B3575393
theorem B7634699 : Blo 1587492 7634699 := bstep (se 1 (by rfl) ⟨5726024, by rfl⟩ : syracuseStep 7634699 = 11452049) B11452049
theorem B1589039 : Blo 1587492 1589039 := bstep (se 1 (by rfl) ⟨1191779, by rfl⟩ : syracuseStep 1589039 = 2383559) B2383559
theorem B5799737 : Blo 1587492 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B6782777 : Blo 1587492 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B13565825 : Blo 1587492 13565825 := bstep (se 2 (by rfl) ⟨5087184, by rfl⟩ : syracuseStep 13565825 = 10174369) B10174369
theorem B1589147 : Blo 1587492 1589147 := bstep (se 1 (by rfl) ⟨1191860, by rfl⟩ : syracuseStep 1589147 = 2383721) B2383721
theorem B1589199 : Blo 1587492 1589199 := bstep (se 1 (by rfl) ⟨1191899, by rfl⟩ : syracuseStep 1589199 = 2383799) B2383799
theorem B2383823 : Blo 1587492 2383823 := bstep (se 1 (by rfl) ⟨1787867, by rfl⟩ : syracuseStep 2383823 = 3575735) B3575735
theorem B1589223 : Blo 1587492 1589223 := bstep (se 1 (by rfl) ⟨1191917, by rfl⟩ : syracuseStep 1589223 = 2383835) B2383835
theorem B1589479 : Blo 1587492 1589479 := bstep (se 1 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 1589479 = 2384219) B2384219
theorem B5431583 : Blo 1587492 5431583 := bstep (se 1 (by rfl) ⟨4073687, by rfl⟩ : syracuseStep 5431583 = 8147375) B8147375
theorem B2384159 : Blo 1587492 2384159 := bstep (se 1 (by rfl) ⟨1788119, by rfl⟩ : syracuseStep 2384159 = 3576239) B3576239
theorem B2679095 : Blo 1587492 2679095 := bstep (se 1 (by rfl) ⟨2009321, by rfl⟩ : syracuseStep 2679095 = 4018643) B4018643
theorem B2384183 : Blo 1587492 2384183 := bstep (se 1 (by rfl) ⟨1788137, by rfl⟩ : syracuseStep 2384183 = 3576275) B3576275
theorem B12222971 : Blo 1587492 12222971 := bstep (se 1 (by rfl) ⟨9167228, by rfl⟩ : syracuseStep 12222971 = 18334457) B18334457
theorem B6783527 : Blo 1587492 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B4522625 : Blo 1587492 4522625 := bstep (se 2 (by rfl) ⟨1695984, by rfl⟩ : syracuseStep 4522625 = 3391969) B3391969
theorem B9175727 : Blo 1587492 9175727 := bstep (se 1 (by rfl) ⟨6881795, by rfl⟩ : syracuseStep 9175727 = 13763591) B13763591
theorem B10183391 : Blo 1587492 10183391 := bstep (se 1 (by rfl) ⟨7637543, by rfl⟩ : syracuseStep 10183391 = 15275087) B15275087
theorem B3572459 : Blo 1587492 3572459 := bstep (se 1 (by rfl) ⟨2679344, by rfl⟩ : syracuseStep 3572459 = 5358689) B5358689
theorem B20357963 : Blo 1587492 20357963 := bstep (se 1 (by rfl) ⟨15268472, by rfl⟩ : syracuseStep 20357963 = 30536945) B30536945
theorem B3220435 : Blo 1587492 3220435 := bstep (se 1 (by rfl) ⟨2415326, by rfl⟩ : syracuseStep 3220435 = 4830653) B4830653
theorem B12067865 : Blo 1587492 12067865 := bstep (se 2 (by rfl) ⟨4525449, by rfl⟩ : syracuseStep 12067865 = 9050899) B9050899
theorem B6030395 : Blo 1587492 6030395 := bstep (se 1 (by rfl) ⟨4522796, by rfl⟩ : syracuseStep 6030395 = 9045593) B9045593
theorem B2679871 : Blo 1587492 2679871 := bstep (se 1 (by rfl) ⟨2009903, by rfl⟩ : syracuseStep 2679871 = 4019807) B4019807
theorem B4523435 : Blo 1587492 4523435 := bstep (se 1 (by rfl) ⟨3392576, by rfl⟩ : syracuseStep 4523435 = 6785153) B6785153
theorem B13575599 : Blo 1587492 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B10864151 : Blo 1587492 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B2680391 : Blo 1587492 2680391 := bstep (se 1 (by rfl) ⟨2010293, by rfl⟩ : syracuseStep 2680391 = 4020587) B4020587
theorem B14681695 : Blo 1587492 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B3573359 : Blo 1587492 3573359 := bstep (se 1 (by rfl) ⟨2680019, by rfl⟩ : syracuseStep 3573359 = 5360039) B5360039
theorem B1787503 : Blo 1587492 1787503 := bstep (se 1 (by rfl) ⟨1340627, by rfl⟩ : syracuseStep 1787503 = 2681255) B2681255
theorem B40691321 : Blo 1587492 40691321 := bstep (se 2 (by rfl) ⟨15259245, by rfl⟩ : syracuseStep 40691321 = 30518491) B30518491
theorem B6440609 : Blo 1587492 6440609 := bstep (se 2 (by rfl) ⟨2415228, by rfl⟩ : syracuseStep 6440609 = 4830457) B4830457
theorem B3393191 : Blo 1587492 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B2860763 : Blo 1587492 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B3573467 : Blo 1587492 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B1787611 : Blo 1587492 1787611 := bstep (se 1 (by rfl) ⟨1340708, by rfl⟩ : syracuseStep 1787611 = 2681417) B2681417
theorem B5089031 : Blo 1587492 5089031 := bstep (se 1 (by rfl) ⟨3816773, by rfl⟩ : syracuseStep 5089031 = 7633547) B7633547
theorem B5359391 : Blo 1587492 5359391 := bstep (se 1 (by rfl) ⟨4019543, by rfl⟩ : syracuseStep 5359391 = 8039087) B8039087
theorem B2680607 : Blo 1587492 2680607 := bstep (se 1 (by rfl) ⟨2010455, by rfl⟩ : syracuseStep 2680607 = 4020911) B4020911
theorem B8046377 : Blo 1587492 8046377 := bstep (se 2 (by rfl) ⟨3017391, by rfl⟩ : syracuseStep 8046377 = 6034783) B6034783
theorem B10176317 : Blo 1587492 10176317 := bstep (se 3 (by rfl) ⟨1908059, by rfl⟩ : syracuseStep 10176317 = 3816119) B3816119
theorem B2860879 : Blo 1587492 2860879 := bstep (se 1 (by rfl) ⟨2145659, by rfl⟩ : syracuseStep 2860879 = 4291319) B4291319
theorem B5359607 : Blo 1587492 5359607 := bstep (se 1 (by rfl) ⟨4019705, by rfl⟩ : syracuseStep 5359607 = 8039411) B8039411
theorem B2680823 : Blo 1587492 2680823 := bstep (se 1 (by rfl) ⟨2010617, by rfl⟩ : syracuseStep 2680823 = 4021235) B4021235
theorem B9046025 : Blo 1587492 9046025 := bstep (se 2 (by rfl) ⟨3392259, by rfl⟩ : syracuseStep 9046025 = 6784519) B6784519
theorem B2263135 : Blo 1587492 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B6031655 : Blo 1587492 6031655 := bstep (se 1 (by rfl) ⟨4523741, by rfl⟩ : syracuseStep 6031655 = 9047483) B9047483
theorem B10316197 : Blo 1587492 10316197 := bstep (se 4 (by rfl) ⟨967143, by rfl⟩ : syracuseStep 10316197 = 1934287) B1934287
theorem B21735863 : Blo 1587492 21735863 := bstep (se 1 (by rfl) ⟨16301897, by rfl⟩ : syracuseStep 21735863 = 32603795) B32603795
theorem B7637449 : Blo 1587492 7637449 := bstep (se 2 (by rfl) ⟨2864043, by rfl⟩ : syracuseStep 7637449 = 5728087) B5728087
theorem B5089799 : Blo 1587492 5089799 := bstep (se 1 (by rfl) ⟨3817349, by rfl⟩ : syracuseStep 5089799 = 7634699) B7634699
theorem B25758281 : Blo 1587492 25758281 := bstep (se 2 (by rfl) ⟨9659355, by rfl⟩ : syracuseStep 25758281 = 19318711) B19318711
theorem B8153783 : Blo 1587492 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B2296631 : Blo 1587492 2296631 := bstep (se 1 (by rfl) ⟨1722473, by rfl⟩ : syracuseStep 2296631 = 3444947) B3444947
theorem B3574583 : Blo 1587492 3574583 := bstep (se 1 (by rfl) ⟨2680937, by rfl⟩ : syracuseStep 3574583 = 5361875) B5361875
theorem B21728087 : Blo 1587492 21728087 := bstep (se 1 (by rfl) ⟨16296065, by rfl⟩ : syracuseStep 21728087 = 32592131) B32592131
theorem B5360471 : Blo 1587492 5360471 := bstep (se 1 (by rfl) ⟨4020353, by rfl⟩ : syracuseStep 5360471 = 8040707) B8040707
theorem B2010091 : Blo 1587492 2010091 := bstep (se 1 (by rfl) ⟨1507568, by rfl⟩ : syracuseStep 2010091 = 3015137) B3015137
theorem B3574763 : Blo 1587492 3574763 := bstep (se 1 (by rfl) ⟨2681072, by rfl⟩ : syracuseStep 3574763 = 5362145) B5362145
theorem B5360687 : Blo 1587492 5360687 := bstep (se 1 (by rfl) ⟨4020515, by rfl⟩ : syracuseStep 5360687 = 8041031) B8041031
theorem B2681903 : Blo 1587492 2681903 := bstep (se 1 (by rfl) ⟨2011427, by rfl⟩ : syracuseStep 2681903 = 4022855) B4022855
theorem B2681977 : Blo 1587492 2681977 := bstep (se 2 (by rfl) ⟨1005741, by rfl⟩ : syracuseStep 2681977 = 2011483) B2011483
theorem B6032627 : Blo 1587492 6032627 := bstep (se 1 (by rfl) ⟨4524470, by rfl⟩ : syracuseStep 6032627 = 9048941) B9048941
theorem B146795813 : Blo 1587492 146795813 := bstep (se 4 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 146795813 = 27524215) B27524215
theorem B5361065 : Blo 1587492 5361065 := bstep (se 2 (by rfl) ⟨2010399, by rfl⟩ : syracuseStep 5361065 = 4020799) B4020799
theorem B55799563 : Blo 1587492 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B3575591 : Blo 1587492 3575591 := bstep (se 1 (by rfl) ⟨2681693, by rfl⟩ : syracuseStep 3575591 = 5363387) B5363387
theorem B3624743 : Blo 1587492 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B5361551 : Blo 1587492 5361551 := bstep (se 1 (by rfl) ⟨4021163, by rfl⟩ : syracuseStep 5361551 = 8042327) B8042327
theorem B34361597 : Blo 1587492 34361597 := bstep (se 3 (by rfl) ⟨6442799, by rfl⟩ : syracuseStep 34361597 = 12885599) B12885599
theorem B5361929 : Blo 1587492 5361929 := bstep (se 2 (by rfl) ⟨2010723, by rfl⟩ : syracuseStep 5361929 = 4021447) B4021447
theorem B25760105 : Blo 1587492 25760105 := bstep (se 2 (by rfl) ⟨9660039, by rfl⟩ : syracuseStep 25760105 = 19320079) B19320079
theorem B6787901 : Blo 1587492 6787901 := bstep (se 3 (by rfl) ⟨1272731, by rfl⟩ : syracuseStep 6787901 = 2545463) B2545463
theorem B20362063 : Blo 1587492 20362063 := bstep (se 1 (by rfl) ⟨15271547, by rfl⟩ : syracuseStep 20362063 = 30543095) B30543095
theorem B11023229 : Blo 1587492 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B15258631 : Blo 1587492 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B9049441 : Blo 1587492 9049441 := bstep (se 2 (by rfl) ⟨3393540, by rfl⟩ : syracuseStep 9049441 = 6787081) B6787081
theorem B5363063 : Blo 1587492 5363063 := bstep (se 1 (by rfl) ⟨4022297, by rfl⟩ : syracuseStep 5363063 = 8044595) B8044595
theorem B11613563 : Blo 1587492 11613563 := bstep (se 1 (by rfl) ⟨8710172, by rfl⟩ : syracuseStep 11613563 = 17420345) B17420345
theorem B2381423 : Blo 1587492 2381423 := bstep (se 1 (by rfl) ⟨1786067, by rfl⟩ : syracuseStep 2381423 = 3572135) B3572135
theorem B2381495 : Blo 1587492 2381495 := bstep (se 1 (by rfl) ⟨1786121, by rfl⟩ : syracuseStep 2381495 = 3572243) B3572243
theorem B2381531 : Blo 1587492 2381531 := bstep (se 1 (by rfl) ⟨1786148, by rfl⟩ : syracuseStep 2381531 = 3572297) B3572297
theorem B2381705 : Blo 1587492 2381705 := bstep (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) B1786279
theorem B2578375 : Blo 1587492 2578375 := bstep (se 1 (by rfl) ⟨1933781, by rfl⟩ : syracuseStep 2578375 = 3867563) B3867563
theorem B2381807 : Blo 1587492 2381807 := bstep (se 1 (by rfl) ⟨1786355, by rfl⟩ : syracuseStep 2381807 = 3572711) B3572711
theorem B8042489 : Blo 1587492 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B9664595 : Blo 1587492 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B77305985 : Blo 1587492 77305985 := bstep (se 2 (by rfl) ⟨28989744, by rfl⟩ : syracuseStep 77305985 = 57979489) B57979489
theorem B5363873 : Blo 1587492 5363873 := bstep (se 2 (by rfl) ⟨2011452, by rfl⟩ : syracuseStep 5363873 = 4022905) B4022905
theorem B2382059 : Blo 1587492 2382059 := bstep (se 1 (by rfl) ⟨1786544, by rfl⟩ : syracuseStep 2382059 = 3573089) B3573089
theorem B2382119 : Blo 1587492 2382119 := bstep (se 1 (by rfl) ⟨1786589, by rfl⟩ : syracuseStep 2382119 = 3573179) B3573179
theorem B1587503 : Blo 1587492 1587503 := bstep (se 1 (by rfl) ⟨1190627, by rfl⟩ : syracuseStep 1587503 = 2381255) B2381255
theorem B2382203 : Blo 1587492 2382203 := bstep (se 1 (by rfl) ⟨1786652, by rfl⟩ : syracuseStep 2382203 = 3573305) B3573305
theorem B15088045 : Blo 1587492 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B5364143 : Blo 1587492 5364143 := bstep (se 1 (by rfl) ⟨4023107, by rfl⟩ : syracuseStep 5364143 = 8046215) B8046215
theorem B1587739 : Blo 1587492 1587739 := bstep (se 1 (by rfl) ⟨1190804, by rfl⟩ : syracuseStep 1587739 = 2381609) B2381609
theorem B1587743 : Blo 1587492 1587743 := bstep (se 1 (by rfl) ⟨1190807, by rfl⟩ : syracuseStep 1587743 = 2381615) B2381615
theorem B2382473 : Blo 1587492 2382473 := bstep (se 2 (by rfl) ⟨893427, by rfl⟩ : syracuseStep 2382473 = 1786855) B1786855
theorem B4831967 : Blo 1587492 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B2382647 : Blo 1587492 2382647 := bstep (se 1 (by rfl) ⟨1786985, by rfl⟩ : syracuseStep 2382647 = 3573971) B3573971
theorem B22903631 : Blo 1587492 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B1588059 : Blo 1587492 1588059 := bstep (se 1 (by rfl) ⟨1191044, by rfl⟩ : syracuseStep 1588059 = 2382089) B2382089
theorem B2382683 : Blo 1587492 2382683 := bstep (se 1 (by rfl) ⟨1787012, by rfl⟩ : syracuseStep 2382683 = 3574025) B3574025
theorem B21724037 : Blo 1587492 21724037 := bstep (se 4 (by rfl) ⟨2036628, by rfl⟩ : syracuseStep 21724037 = 4073257) B4073257
theorem B1588127 : Blo 1587492 1588127 := bstep (se 1 (by rfl) ⟨1191095, by rfl⟩ : syracuseStep 1588127 = 2382191) B2382191
theorem B2382827 : Blo 1587492 2382827 := bstep (se 1 (by rfl) ⟨1787120, by rfl⟩ : syracuseStep 2382827 = 3574241) B3574241
theorem B1588271 : Blo 1587492 1588271 := bstep (se 1 (by rfl) ⟨1191203, by rfl⟩ : syracuseStep 1588271 = 2382407) B2382407
theorem B1588295 : Blo 1587492 1588295 := bstep (se 1 (by rfl) ⟨1191221, by rfl⟩ : syracuseStep 1588295 = 2382443) B2382443
theorem B2383031 : Blo 1587492 2383031 := bstep (se 1 (by rfl) ⟨1787273, by rfl⟩ : syracuseStep 2383031 = 3574547) B3574547
theorem B1588447 : Blo 1587492 1588447 := bstep (se 1 (by rfl) ⟨1191335, by rfl⟩ : syracuseStep 1588447 = 2382671) B2382671
theorem B8043785 : Blo 1587492 8043785 := bstep (se 2 (by rfl) ⟨3016419, by rfl⟩ : syracuseStep 8043785 = 6032839) B6032839
theorem B15473981 : Blo 1587492 15473981 := bstep (se 3 (by rfl) ⟨2901371, by rfl⟩ : syracuseStep 15473981 = 5802743) B5802743
theorem B2383271 : Blo 1587492 2383271 := bstep (se 1 (by rfl) ⟨1787453, by rfl⟩ : syracuseStep 2383271 = 3574907) B3574907
theorem B6028739 : Blo 1587492 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B1588711 : Blo 1587492 1588711 := bstep (se 1 (by rfl) ⟨1191533, by rfl⟩ : syracuseStep 1588711 = 2383067) B2383067
theorem B2383355 : Blo 1587492 2383355 := bstep (se 1 (by rfl) ⟨1787516, by rfl⟩ : syracuseStep 2383355 = 3575033) B3575033
theorem B6782555 : Blo 1587492 6782555 := bstep (se 1 (by rfl) ⟨5086916, by rfl⟩ : syracuseStep 6782555 = 10173833) B10173833
theorem B1588827 : Blo 1587492 1588827 := bstep (se 1 (by rfl) ⟨1191620, by rfl⟩ : syracuseStep 1588827 = 2383241) B2383241
theorem B2383451 : Blo 1587492 2383451 := bstep (se 1 (by rfl) ⟨1787588, by rfl⟩ : syracuseStep 2383451 = 3575177) B3575177
theorem B10174061 : Blo 1587492 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B36699763 : Blo 1587492 36699763 := bstep (se 1 (by rfl) ⟨27524822, by rfl⟩ : syracuseStep 36699763 = 55049645) B55049645
theorem B9174671 : Blo 1587492 9174671 := bstep (se 1 (by rfl) ⟨6881003, by rfl⟩ : syracuseStep 9174671 = 13762007) B13762007
theorem B2383535 : Blo 1587492 2383535 := bstep (se 1 (by rfl) ⟨1787651, by rfl⟩ : syracuseStep 2383535 = 3575303) B3575303
theorem B9051857 : Blo 1587492 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B2383655 : Blo 1587492 2383655 := bstep (se 1 (by rfl) ⟨1787741, by rfl⟩ : syracuseStep 2383655 = 3575483) B3575483
theorem B3391303 : Blo 1587492 3391303 := bstep (se 1 (by rfl) ⟨2543477, by rfl⟩ : syracuseStep 3391303 = 5086955) B5086955
theorem B1589063 : Blo 1587492 1589063 := bstep (se 1 (by rfl) ⟨1191797, by rfl⟩ : syracuseStep 1589063 = 2383595) B2383595
theorem B3866491 : Blo 1587492 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B4521851 : Blo 1587492 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B2383739 : Blo 1587492 2383739 := bstep (se 1 (by rfl) ⟨1787804, by rfl⟩ : syracuseStep 2383739 = 3575609) B3575609
theorem B9043883 : Blo 1587492 9043883 := bstep (se 1 (by rfl) ⟨6782912, by rfl⟩ : syracuseStep 9043883 = 13565825) B13565825
theorem B1589215 : Blo 1587492 1589215 := bstep (se 1 (by rfl) ⟨1191911, by rfl⟩ : syracuseStep 1589215 = 2383823) B2383823
theorem B1589439 : Blo 1587492 1589439 := bstep (se 1 (by rfl) ⟨1192079, by rfl⟩ : syracuseStep 1589439 = 2384159) B2384159
theorem B1786063 : Blo 1587492 1786063 := bstep (se 1 (by rfl) ⟨1339547, by rfl⟩ : syracuseStep 1786063 = 2679095) B2679095
theorem B1589455 : Blo 1587492 1589455 := bstep (se 1 (by rfl) ⟨1192091, by rfl⟩ : syracuseStep 1589455 = 2384183) B2384183
theorem B3015083 : Blo 1587492 3015083 := bstep (se 1 (by rfl) ⟨2261312, by rfl⟩ : syracuseStep 3015083 = 4522625) B4522625
theorem B13754929 : Blo 1587492 13754929 := bstep (se 2 (by rfl) ⟨5158098, by rfl⟩ : syracuseStep 13754929 = 10316197) B10316197
theorem B7348819 : Blo 1587492 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B10183265 : Blo 1587492 10183265 := bstep (se 2 (by rfl) ⟨3818724, by rfl⟩ : syracuseStep 10183265 = 7637449) B7637449
theorem B8045243 : Blo 1587492 8045243 := bstep (se 1 (by rfl) ⟨6033932, by rfl⟩ : syracuseStep 8045243 = 12067865) B12067865
theorem B14484221 : Blo 1587492 14484221 := bstep (se 3 (by rfl) ⟨2715791, by rfl⟩ : syracuseStep 14484221 = 5431583) B5431583
theorem B41263949 : Blo 1587492 41263949 := bstep (se 3 (by rfl) ⟨7736990, by rfl⟩ : syracuseStep 41263949 = 15473981) B15473981
theorem B7742375 : Blo 1587492 7742375 := bstep (se 1 (by rfl) ⟨5806781, by rfl⟩ : syracuseStep 7742375 = 11613563) B11613563
theorem B3015623 : Blo 1587492 3015623 := bstep (se 1 (by rfl) ⟨2261717, by rfl⟩ : syracuseStep 3015623 = 4523435) B4523435
theorem B7242767 : Blo 1587492 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B1786927 : Blo 1587492 1786927 := bstep (se 1 (by rfl) ⟨1340195, by rfl⟩ : syracuseStep 1786927 = 2680391) B2680391
theorem B27149417 : Blo 1587492 27149417 := bstep (se 2 (by rfl) ⟨10181031, by rfl⟩ : syracuseStep 27149417 = 20362063) B20362063
theorem B4293739 : Blo 1587492 4293739 := bstep (se 1 (by rfl) ⟨3220304, by rfl⟩ : syracuseStep 4293739 = 6440609) B6440609
theorem B3392687 : Blo 1587492 3392687 := bstep (se 1 (by rfl) ⟨2544515, by rfl⟩ : syracuseStep 3392687 = 5089031) B5089031
theorem B3572927 : Blo 1587492 3572927 := bstep (se 1 (by rfl) ⟨2679695, by rfl⟩ : syracuseStep 3572927 = 5359391) B5359391
theorem B1787071 : Blo 1587492 1787071 := bstep (se 1 (by rfl) ⟨1340303, by rfl⟩ : syracuseStep 1787071 = 2680607) B2680607
theorem B6784211 : Blo 1587492 6784211 := bstep (se 1 (by rfl) ⟨5088158, by rfl⟩ : syracuseStep 6784211 = 10176317) B10176317
theorem B4293913 : Blo 1587492 4293913 := bstep (se 2 (by rfl) ⟨1610217, by rfl⟩ : syracuseStep 4293913 = 3220435) B3220435
theorem B2680121 : Blo 1587492 2680121 := bstep (se 2 (by rfl) ⟨1005045, by rfl⟩ : syracuseStep 2680121 = 2010091) B2010091
theorem B3573071 : Blo 1587492 3573071 := bstep (se 1 (by rfl) ⟨2679803, by rfl⟩ : syracuseStep 3573071 = 5359607) B5359607
theorem B1787215 : Blo 1587492 1787215 := bstep (se 1 (by rfl) ⟨1340411, by rfl⟩ : syracuseStep 1787215 = 2680823) B2680823
theorem B6030683 : Blo 1587492 6030683 := bstep (se 1 (by rfl) ⟨4523012, by rfl⟩ : syracuseStep 6030683 = 9046025) B9046025
theorem B3573161 : Blo 1587492 3573161 := bstep (se 2 (by rfl) ⟨1339935, by rfl⟩ : syracuseStep 3573161 = 2679871) B2679871
theorem B51537323 : Blo 1587492 51537323 := bstep (se 1 (by rfl) ⟨38652992, by rfl⟩ : syracuseStep 51537323 = 77305985) B77305985
theorem B18089405 : Blo 1587492 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B3393199 : Blo 1587492 3393199 := bstep (se 1 (by rfl) ⟨2544899, by rfl⟩ : syracuseStep 3393199 = 5089799) B5089799
theorem B3221311 : Blo 1587492 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B14485391 : Blo 1587492 14485391 := bstep (se 1 (by rfl) ⟨10864043, by rfl⟩ : syracuseStep 14485391 = 21728087) B21728087
theorem B3573647 : Blo 1587492 3573647 := bstep (se 1 (by rfl) ⟨2680235, by rfl⟩ : syracuseStep 3573647 = 5360471) B5360471
theorem B7628701 : Blo 1587492 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B3573791 : Blo 1587492 3573791 := bstep (se 1 (by rfl) ⟨2680343, by rfl⟩ : syracuseStep 3573791 = 5360687) B5360687
theorem B1787935 : Blo 1587492 1787935 := bstep (se 1 (by rfl) ⟨1340951, by rfl⟩ : syracuseStep 1787935 = 2681903) B2681903
theorem B48933017 : Blo 1587492 48933017 := bstep (se 2 (by rfl) ⟨18349881, by rfl⟩ : syracuseStep 48933017 = 36699763) B36699763
theorem B97863875 : Blo 1587492 97863875 := bstep (se 1 (by rfl) ⟨73397906, by rfl⟩ : syracuseStep 97863875 = 146795813) B146795813
theorem B3574043 : Blo 1587492 3574043 := bstep (se 1 (by rfl) ⟨2680532, by rfl⟩ : syracuseStep 3574043 = 5361065) B5361065
theorem B5155321 : Blo 1587492 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B3574367 : Blo 1587492 3574367 := bstep (se 1 (by rfl) ⟨2680775, by rfl⟩ : syracuseStep 3574367 = 5361551) B5361551
theorem B3017513 : Blo 1587492 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B22907731 : Blo 1587492 22907731 := bstep (se 1 (by rfl) ⟨17180798, by rfl⟩ : syracuseStep 22907731 = 34361597) B34361597
theorem B3574619 : Blo 1587492 3574619 := bstep (se 1 (by rfl) ⟨2680964, by rfl⟩ : syracuseStep 3574619 = 5361929) B5361929
theorem B17173403 : Blo 1587492 17173403 := bstep (se 1 (by rfl) ⟨12880052, by rfl⟩ : syracuseStep 17173403 = 25760105) B25760105
theorem B3575375 : Blo 1587492 3575375 := bstep (se 1 (by rfl) ⟨2681531, by rfl⟩ : syracuseStep 3575375 = 5363063) B5363063
theorem B27127547 : Blo 1587492 27127547 := bstep (se 1 (by rfl) ⟨20345660, by rfl⟩ : syracuseStep 27127547 = 40691321) B40691321
theorem B5361659 : Blo 1587492 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B20344841 : Blo 1587492 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B6443063 : Blo 1587492 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B3575915 : Blo 1587492 3575915 := bstep (se 1 (by rfl) ⟨2681936, by rfl⟩ : syracuseStep 3575915 = 5363873) B5363873
theorem B3575969 : Blo 1587492 3575969 := bstep (se 2 (by rfl) ⟨1340988, by rfl⟩ : syracuseStep 3575969 = 2681977) B2681977
theorem B3576095 : Blo 1587492 3576095 := bstep (se 1 (by rfl) ⟨2682071, by rfl⟩ : syracuseStep 3576095 = 5364143) B5364143
theorem B9048509 : Blo 1587492 9048509 := bstep (se 3 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 9048509 = 3393191) B3393191
theorem B5435855 : Blo 1587492 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B19575593 : Blo 1587492 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B6124349 : Blo 1587492 6124349 := bstep (se 3 (by rfl) ⟨1148315, by rfl⟩ : syracuseStep 6124349 = 2296631) B2296631
theorem B18101069 : Blo 1587492 18101069 := bstep (se 3 (by rfl) ⟨3393950, by rfl⟩ : syracuseStep 18101069 = 6787901) B6787901
theorem B5362523 : Blo 1587492 5362523 := bstep (se 1 (by rfl) ⟨4021892, by rfl⟩ : syracuseStep 5362523 = 8043785) B8043785
theorem B4019159 : Blo 1587492 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B13751333 : Blo 1587492 13751333 := bstep (se 4 (by rfl) ⟨1289187, by rfl⟩ : syracuseStep 13751333 = 2578375) B2578375
theorem B6116447 : Blo 1587492 6116447 := bstep (se 1 (by rfl) ⟨4587335, by rfl⟩ : syracuseStep 6116447 = 9174671) B9174671
theorem B3814505 : Blo 1587492 3814505 := bstep (se 2 (by rfl) ⟨1430439, by rfl⟩ : syracuseStep 3814505 = 2860879) B2860879
theorem B6034571 : Blo 1587492 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B8148647 : Blo 1587492 8148647 := bstep (se 1 (by rfl) ⟨6111485, by rfl⟩ : syracuseStep 8148647 = 12222971) B12222971
theorem B6788927 : Blo 1587492 6788927 := bstep (se 1 (by rfl) ⟨5091695, by rfl⟩ : syracuseStep 6788927 = 10183391) B10183391
theorem B2381639 : Blo 1587492 2381639 := bstep (se 1 (by rfl) ⟨1786229, by rfl⟩ : syracuseStep 2381639 = 3572459) B3572459
theorem B13571975 : Blo 1587492 13571975 := bstep (se 1 (by rfl) ⟨10178981, by rfl⟩ : syracuseStep 13571975 = 20357963) B20357963
theorem B20117393 : Blo 1587492 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B4020263 : Blo 1587492 4020263 := bstep (se 1 (by rfl) ⟨3015197, by rfl⟩ : syracuseStep 4020263 = 6030395) B6030395
theorem B9050399 : Blo 1587492 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B1587615 : Blo 1587492 1587615 := bstep (se 1 (by rfl) ⟨1190711, by rfl⟩ : syracuseStep 1587615 = 2381423) B2381423
theorem B2382239 : Blo 1587492 2382239 := bstep (se 1 (by rfl) ⟨1786679, by rfl⟩ : syracuseStep 2382239 = 3573359) B3573359
theorem B1587663 : Blo 1587492 1587663 := bstep (se 1 (by rfl) ⟨1190747, by rfl⟩ : syracuseStep 1587663 = 2381495) B2381495
theorem B1587687 : Blo 1587492 1587687 := bstep (se 1 (by rfl) ⟨1190765, by rfl⟩ : syracuseStep 1587687 = 2381531) B2381531
theorem B2382311 : Blo 1587492 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B5364251 : Blo 1587492 5364251 := bstep (se 1 (by rfl) ⟨4023188, by rfl⟩ : syracuseStep 5364251 = 8046377) B8046377
theorem B1587803 : Blo 1587492 1587803 := bstep (se 1 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 1587803 = 2381705) B2381705
theorem B1587871 : Blo 1587492 1587871 := bstep (se 1 (by rfl) ⟨1190903, by rfl⟩ : syracuseStep 1587871 = 2381807) B2381807
theorem B1588039 : Blo 1587492 1588039 := bstep (se 1 (by rfl) ⟨1191029, by rfl⟩ : syracuseStep 1588039 = 2382059) B2382059
theorem B68688749 : Blo 1587492 68688749 := bstep (se 3 (by rfl) ⟨12879140, by rfl⟩ : syracuseStep 68688749 = 25758281) B25758281
theorem B1588079 : Blo 1587492 1588079 := bstep (se 1 (by rfl) ⟨1191059, by rfl⟩ : syracuseStep 1588079 = 2382119) B2382119
theorem B4021103 : Blo 1587492 4021103 := bstep (se 1 (by rfl) ⟨3015827, by rfl⟩ : syracuseStep 4021103 = 6031655) B6031655
theorem B1588135 : Blo 1587492 1588135 := bstep (se 1 (by rfl) ⟨1191101, by rfl⟩ : syracuseStep 1588135 = 2382203) B2382203
theorem B14490575 : Blo 1587492 14490575 := bstep (se 1 (by rfl) ⟨10867931, by rfl⟩ : syracuseStep 14490575 = 21735863) B21735863
theorem B1588315 : Blo 1587492 1588315 := bstep (se 1 (by rfl) ⟨1191236, by rfl⟩ : syracuseStep 1588315 = 2382473) B2382473
theorem B24468605 : Blo 1587492 24468605 := bstep (se 3 (by rfl) ⟨4587863, by rfl⟩ : syracuseStep 24468605 = 9175727) B9175727
theorem B12065921 : Blo 1587492 12065921 := bstep (se 2 (by rfl) ⟨4524720, by rfl⟩ : syracuseStep 12065921 = 9049441) B9049441
theorem B1588431 : Blo 1587492 1588431 := bstep (se 1 (by rfl) ⟨1191323, by rfl⟩ : syracuseStep 1588431 = 2382647) B2382647
theorem B2383055 : Blo 1587492 2383055 := bstep (se 1 (by rfl) ⟨1787291, by rfl⟩ : syracuseStep 2383055 = 3574583) B3574583
theorem B15269087 : Blo 1587492 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B1588455 : Blo 1587492 1588455 := bstep (se 1 (by rfl) ⟨1191341, by rfl⟩ : syracuseStep 1588455 = 2382683) B2382683
theorem B14482691 : Blo 1587492 14482691 := bstep (se 1 (by rfl) ⟨10862018, by rfl⟩ : syracuseStep 14482691 = 21724037) B21724037
theorem B1588551 : Blo 1587492 1588551 := bstep (se 1 (by rfl) ⟨1191413, by rfl⟩ : syracuseStep 1588551 = 2382827) B2382827
theorem B2383175 : Blo 1587492 2383175 := bstep (se 1 (by rfl) ⟨1787381, by rfl⟩ : syracuseStep 2383175 = 3574763) B3574763
theorem B1588687 : Blo 1587492 1588687 := bstep (se 1 (by rfl) ⟨1191515, by rfl⟩ : syracuseStep 1588687 = 2383031) B2383031
theorem B2383337 : Blo 1587492 2383337 := bstep (se 2 (by rfl) ⟨893751, by rfl⟩ : syracuseStep 2383337 = 1787503) B1787503
theorem B4021751 : Blo 1587492 4021751 := bstep (se 1 (by rfl) ⟨3016313, by rfl⟩ : syracuseStep 4021751 = 6032627) B6032627
theorem B1588847 : Blo 1587492 1588847 := bstep (se 1 (by rfl) ⟨1191635, by rfl⟩ : syracuseStep 1588847 = 2383271) B2383271
theorem B2383481 : Blo 1587492 2383481 := bstep (se 2 (by rfl) ⟨893805, by rfl⟩ : syracuseStep 2383481 = 1787611) B1787611
theorem B1588903 : Blo 1587492 1588903 := bstep (se 1 (by rfl) ⟨1191677, by rfl⟩ : syracuseStep 1588903 = 2383355) B2383355
theorem B74399417 : Blo 1587492 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B4521703 : Blo 1587492 4521703 := bstep (se 1 (by rfl) ⟨3391277, by rfl⟩ : syracuseStep 4521703 = 6782555) B6782555
theorem B1588967 : Blo 1587492 1588967 := bstep (se 1 (by rfl) ⟨1191725, by rfl⟩ : syracuseStep 1588967 = 2383451) B2383451
theorem B6782707 : Blo 1587492 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B4521737 : Blo 1587492 4521737 := bstep (se 2 (by rfl) ⟨1695651, by rfl⟩ : syracuseStep 4521737 = 3391303) B3391303
theorem B1589023 : Blo 1587492 1589023 := bstep (se 1 (by rfl) ⟨1191767, by rfl⟩ : syracuseStep 1589023 = 2383535) B2383535
theorem B1589103 : Blo 1587492 1589103 := bstep (se 1 (by rfl) ⟨1191827, by rfl⟩ : syracuseStep 1589103 = 2383655) B2383655
theorem B2383727 : Blo 1587492 2383727 := bstep (se 1 (by rfl) ⟨1787795, by rfl⟩ : syracuseStep 2383727 = 3575591) B3575591
theorem B2416495 : Blo 1587492 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B3014567 : Blo 1587492 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B1589159 : Blo 1587492 1589159 := bstep (se 1 (by rfl) ⟨1191869, by rfl⟩ : syracuseStep 1589159 = 2383739) B2383739
theorem B6029255 : Blo 1587492 6029255 := bstep (se 1 (by rfl) ⟨4521941, by rfl⟩ : syracuseStep 6029255 = 9043883) B9043883
theorem B2383913 : Blo 1587492 2383913 := bstep (se 2 (by rfl) ⟨893967, by rfl⟩ : syracuseStep 2383913 = 1787935) B1787935
theorem B2383943 : Blo 1587492 2383943 := bstep (se 1 (by rfl) ⟨1787957, by rfl⟩ : syracuseStep 2383943 = 3575915) B3575915
theorem B2383979 : Blo 1587492 2383979 := bstep (se 1 (by rfl) ⟨1787984, by rfl⟩ : syracuseStep 2383979 = 3575969) B3575969
theorem B2384063 : Blo 1587492 2384063 := bstep (se 1 (by rfl) ⟨1788047, by rfl⟩ : syracuseStep 2384063 = 3576095) B3576095
theorem B13050395 : Blo 1587492 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B12067379 : Blo 1587492 12067379 := bstep (se 1 (by rfl) ⟨9050534, by rfl⟩ : syracuseStep 12067379 = 18101069) B18101069
theorem B5161583 : Blo 1587492 5161583 := bstep (se 1 (by rfl) ⟨3871187, by rfl⟩ : syracuseStep 5161583 = 7742375) B7742375
theorem B2679439 : Blo 1587492 2679439 := bstep (se 1 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 2679439 = 4019159) B4019159
theorem B6873761 : Blo 1587492 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B9167555 : Blo 1587492 9167555 := bstep (se 1 (by rfl) ⟨6875666, by rfl⟩ : syracuseStep 9167555 = 13751333) B13751333
theorem B4023047 : Blo 1587492 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B9798425 : Blo 1587492 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B2261791 : Blo 1587492 2261791 := bstep (se 1 (by rfl) ⟨1696343, by rfl⟩ : syracuseStep 2261791 = 3392687) B3392687
theorem B4522807 : Blo 1587492 4522807 := bstep (se 1 (by rfl) ⟨3392105, by rfl⟩ : syracuseStep 4522807 = 6784211) B6784211
theorem B1786747 : Blo 1587492 1786747 := bstep (se 1 (by rfl) ⟨1340060, by rfl⟩ : syracuseStep 1786747 = 2680121) B2680121
theorem B34358215 : Blo 1587492 34358215 := bstep (se 1 (by rfl) ⟨25768661, by rfl⟩ : syracuseStep 34358215 = 51537323) B51537323
theorem B12059603 : Blo 1587492 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B13411595 : Blo 1587492 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B2680175 : Blo 1587492 2680175 := bstep (se 1 (by rfl) ⟨2010131, by rfl⟩ : syracuseStep 2680175 = 4020263) B4020263
theorem B32622011 : Blo 1587492 32622011 := bstep (se 1 (by rfl) ⟨24466508, by rfl⟩ : syracuseStep 32622011 = 48933017) B48933017
theorem B65242583 : Blo 1587492 65242583 := bstep (se 1 (by rfl) ⟨48931937, by rfl⟩ : syracuseStep 65242583 = 97863875) B97863875
theorem B2680735 : Blo 1587492 2680735 := bstep (se 1 (by rfl) ⟨2010551, by rfl⟩ : syracuseStep 2680735 = 4021103) B4021103
theorem B9660383 : Blo 1587492 9660383 := bstep (se 1 (by rfl) ⟨7245287, by rfl⟩ : syracuseStep 9660383 = 14490575) B14490575
theorem B16312403 : Blo 1587492 16312403 := bstep (se 1 (by rfl) ⟨12234302, by rfl⟩ : syracuseStep 16312403 = 24468605) B24468605
theorem B8046701 : Blo 1587492 8046701 := bstep (se 3 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 8046701 = 3017513) B3017513
theorem B110037197 : Blo 1587492 110037197 := bstep (se 3 (by rfl) ⟨20631974, by rfl⟩ : syracuseStep 110037197 = 41263949) B41263949
theorem B4524265 : Blo 1587492 4524265 := bstep (se 2 (by rfl) ⟨1696599, by rfl⟩ : syracuseStep 4524265 = 3393199) B3393199
theorem B2681167 : Blo 1587492 2681167 := bstep (se 1 (by rfl) ⟨2010875, by rfl⟩ : syracuseStep 2681167 = 4021751) B4021751
theorem B4295081 : Blo 1587492 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B3221993 : Blo 1587492 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B2009711 : Blo 1587492 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B3574439 : Blo 1587492 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B4295375 : Blo 1587492 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B6032339 : Blo 1587492 6032339 := bstep (se 1 (by rfl) ⟨4524254, by rfl⟩ : syracuseStep 6032339 = 9048509) B9048509
theorem B3623903 : Blo 1587492 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B4082899 : Blo 1587492 4082899 := bstep (se 1 (by rfl) ⟨3062174, by rfl⟩ : syracuseStep 4082899 = 6124349) B6124349
theorem B22899941 : Blo 1587492 22899941 := bstep (se 4 (by rfl) ⟨2146869, by rfl⟩ : syracuseStep 22899941 = 4293739) B4293739
theorem B3575015 : Blo 1587492 3575015 := bstep (se 1 (by rfl) ⟨2681261, by rfl⟩ : syracuseStep 3575015 = 5362523) B5362523
theorem B40717565 : Blo 1587492 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B2010415 : Blo 1587492 2010415 := bstep (se 1 (by rfl) ⟨1507811, by rfl⟩ : syracuseStep 2010415 = 3015623) B3015623
theorem B4828511 : Blo 1587492 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B2543003 : Blo 1587492 2543003 := bstep (se 1 (by rfl) ⟨1907252, by rfl⟩ : syracuseStep 2543003 = 3814505) B3814505
theorem B18099611 : Blo 1587492 18099611 := bstep (se 1 (by rfl) ⟨13574708, by rfl⟩ : syracuseStep 18099611 = 27149417) B27149417
theorem B30543641 : Blo 1587492 30543641 := bstep (se 2 (by rfl) ⟨11453865, by rfl⟩ : syracuseStep 30543641 = 22907731) B22907731
theorem B8040221 : Blo 1587492 8040221 := bstep (se 3 (by rfl) ⟨1507541, by rfl⟩ : syracuseStep 8040221 = 3015083) B3015083
theorem B4525951 : Blo 1587492 4525951 := bstep (se 1 (by rfl) ⟨3394463, by rfl⟩ : syracuseStep 4525951 = 6788927) B6788927
theorem B9047983 : Blo 1587492 9047983 := bstep (se 1 (by rfl) ⟨6785987, by rfl⟩ : syracuseStep 9047983 = 13571975) B13571975
theorem B6033599 : Blo 1587492 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B3576167 : Blo 1587492 3576167 := bstep (se 1 (by rfl) ⟨2682125, by rfl⟩ : syracuseStep 3576167 = 5364251) B5364251
theorem B21729725 : Blo 1587492 21729725 := bstep (se 3 (by rfl) ⟨4074323, by rfl⟩ : syracuseStep 21729725 = 8148647) B8148647
theorem B11448935 : Blo 1587492 11448935 := bstep (se 1 (by rfl) ⟨8586701, by rfl⟩ : syracuseStep 11448935 = 17173403) B17173403
theorem B9655127 : Blo 1587492 9655127 := bstep (se 1 (by rfl) ⟨7241345, by rfl⟩ : syracuseStep 9655127 = 14482691) B14482691
theorem B49599611 : Blo 1587492 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B18085031 : Blo 1587492 18085031 := bstep (se 1 (by rfl) ⟨13563773, by rfl⟩ : syracuseStep 18085031 = 27127547) B27127547
theorem B10171601 : Blo 1587492 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B4019503 : Blo 1587492 4019503 := bstep (se 1 (by rfl) ⟨3014627, by rfl⟩ : syracuseStep 4019503 = 6029255) B6029255
theorem B13563227 : Blo 1587492 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B2381417 : Blo 1587492 2381417 := bstep (se 2 (by rfl) ⟨893031, by rfl⟩ : syracuseStep 2381417 = 1786063) B1786063
theorem B6788843 : Blo 1587492 6788843 := bstep (se 1 (by rfl) ⟨5091632, by rfl⟩ : syracuseStep 6788843 = 10183265) B10183265
theorem B5363495 : Blo 1587492 5363495 := bstep (se 1 (by rfl) ⟨4022621, by rfl⟩ : syracuseStep 5363495 = 8045243) B8045243
theorem B9656147 : Blo 1587492 9656147 := bstep (se 1 (by rfl) ⟨7242110, by rfl⟩ : syracuseStep 9656147 = 14484221) B14484221
theorem B4077631 : Blo 1587492 4077631 := bstep (se 1 (by rfl) ⟨3058223, by rfl⟩ : syracuseStep 4077631 = 6116447) B6116447
theorem B18339905 : Blo 1587492 18339905 := bstep (se 2 (by rfl) ⟨6877464, by rfl⟩ : syracuseStep 18339905 = 13754929) B13754929
theorem B2381951 : Blo 1587492 2381951 := bstep (se 1 (by rfl) ⟨1786463, by rfl⟩ : syracuseStep 2381951 = 3572927) B3572927
theorem B2382047 : Blo 1587492 2382047 := bstep (se 1 (by rfl) ⟨1786535, by rfl⟩ : syracuseStep 2382047 = 3573071) B3573071
theorem B4020455 : Blo 1587492 4020455 := bstep (se 1 (by rfl) ⟨3015341, by rfl⟩ : syracuseStep 4020455 = 6030683) B6030683
theorem B2382107 : Blo 1587492 2382107 := bstep (se 1 (by rfl) ⟨1786580, by rfl⟩ : syracuseStep 2382107 = 3573161) B3573161
theorem B1587759 : Blo 1587492 1587759 := bstep (se 1 (by rfl) ⟨1190819, by rfl⟩ : syracuseStep 1587759 = 2381639) B2381639
theorem B9656927 : Blo 1587492 9656927 := bstep (se 1 (by rfl) ⟨7242695, by rfl⟩ : syracuseStep 9656927 = 14485391) B14485391
theorem B2382431 : Blo 1587492 2382431 := bstep (se 1 (by rfl) ⟨1786823, by rfl⟩ : syracuseStep 2382431 = 3573647) B3573647
theorem B2382527 : Blo 1587492 2382527 := bstep (se 1 (by rfl) ⟨1786895, by rfl⟩ : syracuseStep 2382527 = 3573791) B3573791
theorem B2382569 : Blo 1587492 2382569 := bstep (se 2 (by rfl) ⟨893463, by rfl⟩ : syracuseStep 2382569 = 1786927) B1786927
theorem B2382695 : Blo 1587492 2382695 := bstep (se 1 (by rfl) ⟨1787021, by rfl⟩ : syracuseStep 2382695 = 3574043) B3574043
theorem B2382761 : Blo 1587492 2382761 := bstep (se 2 (by rfl) ⟨893535, by rfl⟩ : syracuseStep 2382761 = 1787071) B1787071
theorem B1588159 : Blo 1587492 1588159 := bstep (se 1 (by rfl) ⟨1191119, by rfl⟩ : syracuseStep 1588159 = 2382239) B2382239
theorem B1588207 : Blo 1587492 1588207 := bstep (se 1 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 1588207 = 2382311) B2382311
theorem B5725217 : Blo 1587492 5725217 := bstep (se 2 (by rfl) ⟨2146956, by rfl⟩ : syracuseStep 5725217 = 4293913) B4293913
theorem B2382911 : Blo 1587492 2382911 := bstep (se 1 (by rfl) ⟨1787183, by rfl⟩ : syracuseStep 2382911 = 3574367) B3574367
theorem B2382953 : Blo 1587492 2382953 := bstep (se 2 (by rfl) ⟨893607, by rfl⟩ : syracuseStep 2382953 = 1787215) B1787215
theorem B2383079 : Blo 1587492 2383079 := bstep (se 1 (by rfl) ⟨1787309, by rfl⟩ : syracuseStep 2383079 = 3574619) B3574619
theorem B45792499 : Blo 1587492 45792499 := bstep (se 1 (by rfl) ⟨34344374, by rfl⟩ : syracuseStep 45792499 = 68688749) B68688749
theorem B8043947 : Blo 1587492 8043947 := bstep (se 1 (by rfl) ⟨6032960, by rfl⟩ : syracuseStep 8043947 = 12065921) B12065921
theorem B1588703 : Blo 1587492 1588703 := bstep (se 1 (by rfl) ⟨1191527, by rfl⟩ : syracuseStep 1588703 = 2383055) B2383055
theorem B1588783 : Blo 1587492 1588783 := bstep (se 1 (by rfl) ⟨1191587, by rfl⟩ : syracuseStep 1588783 = 2383175) B2383175
theorem B6028937 : Blo 1587492 6028937 := bstep (se 2 (by rfl) ⟨2260851, by rfl⟩ : syracuseStep 6028937 = 4521703) B4521703
theorem B9043609 : Blo 1587492 9043609 := bstep (se 2 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 9043609 = 6782707) B6782707
theorem B1588891 : Blo 1587492 1588891 := bstep (se 1 (by rfl) ⟨1191668, by rfl⟩ : syracuseStep 1588891 = 2383337) B2383337
theorem B2383583 : Blo 1587492 2383583 := bstep (se 1 (by rfl) ⟨1787687, by rfl⟩ : syracuseStep 2383583 = 3575375) B3575375
theorem B1588987 : Blo 1587492 1588987 := bstep (se 1 (by rfl) ⟨1191740, by rfl⟩ : syracuseStep 1588987 = 2383481) B2383481
theorem B3014491 : Blo 1587492 3014491 := bstep (se 1 (by rfl) ⟨2260868, by rfl⟩ : syracuseStep 3014491 = 4521737) B4521737
theorem B1589151 : Blo 1587492 1589151 := bstep (se 1 (by rfl) ⟨1191863, by rfl⟩ : syracuseStep 1589151 = 2383727) B2383727
theorem B1589275 : Blo 1587492 1589275 := bstep (se 1 (by rfl) ⟨1191956, by rfl⟩ : syracuseStep 1589275 = 2383913) B2383913
theorem B1589295 : Blo 1587492 1589295 := bstep (se 1 (by rfl) ⟨1191971, by rfl⟩ : syracuseStep 1589295 = 2383943) B2383943
theorem B1589319 : Blo 1587492 1589319 := bstep (se 1 (by rfl) ⟨1191989, by rfl⟩ : syracuseStep 1589319 = 2383979) B2383979
theorem B4022399 : Blo 1587492 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B1589375 : Blo 1587492 1589375 := bstep (se 1 (by rfl) ⟨1192031, by rfl⟩ : syracuseStep 1589375 = 2384063) B2384063
theorem B48906413 : Blo 1587492 48906413 := bstep (se 3 (by rfl) ⟨9169952, by rfl⟩ : syracuseStep 48906413 = 18339905) B18339905
theorem B2384111 : Blo 1587492 2384111 := bstep (se 1 (by rfl) ⟨1788083, by rfl⟩ : syracuseStep 2384111 = 3576167) B3576167
theorem B8700263 : Blo 1587492 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B8044919 : Blo 1587492 8044919 := bstep (se 1 (by rfl) ⟨6033689, by rfl⟩ : syracuseStep 8044919 = 12067379) B12067379
theorem B3441055 : Blo 1587492 3441055 := bstep (se 1 (by rfl) ⟨2580791, by rfl⟩ : syracuseStep 3441055 = 5161583) B5161583
theorem B6111703 : Blo 1587492 6111703 := bstep (se 1 (by rfl) ⟨4583777, by rfl⟩ : syracuseStep 6111703 = 9167555) B9167555
theorem B3572585 : Blo 1587492 3572585 := bstep (se 2 (by rfl) ⟨1339719, by rfl⟩ : syracuseStep 3572585 = 2679439) B2679439
theorem B1786783 : Blo 1587492 1786783 := bstep (se 1 (by rfl) ⟨1340087, by rfl⟩ : syracuseStep 1786783 = 2680175) B2680175
theorem B3015721 : Blo 1587492 3015721 := bstep (se 2 (by rfl) ⟨1130895, by rfl⟩ : syracuseStep 3015721 = 2261791) B2261791
theorem B6030409 : Blo 1587492 6030409 := bstep (se 2 (by rfl) ⟨2261403, by rfl⟩ : syracuseStep 6030409 = 4522807) B4522807
theorem B45810953 : Blo 1587492 45810953 := bstep (se 2 (by rfl) ⟨17179107, by rfl⟩ : syracuseStep 45810953 = 34358215) B34358215
theorem B6440255 : Blo 1587492 6440255 := bstep (se 1 (by rfl) ⟨4830191, by rfl⟩ : syracuseStep 6440255 = 9660383) B9660383
theorem B2680303 : Blo 1587492 2680303 := bstep (se 1 (by rfl) ⟨2010227, by rfl⟩ : syracuseStep 2680303 = 4020455) B4020455
theorem B5359229 : Blo 1587492 5359229 := bstep (se 3 (by rfl) ⟨1004855, by rfl⟩ : syracuseStep 5359229 = 2009711) B2009711
theorem B61056665 : Blo 1587492 61056665 := bstep (se 2 (by rfl) ⟨22896249, by rfl⟩ : syracuseStep 61056665 = 45792499) B45792499
theorem B2147995 : Blo 1587492 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B5359337 : Blo 1587492 5359337 := bstep (se 2 (by rfl) ⟨2009751, by rfl⟩ : syracuseStep 5359337 = 4019503) B4019503
theorem B2680553 : Blo 1587492 2680553 := bstep (se 2 (by rfl) ⟨1005207, by rfl⟩ : syracuseStep 2680553 = 2010415) B2010415
theorem B5360147 : Blo 1587492 5360147 := bstep (se 1 (by rfl) ⟨4020110, by rfl⟩ : syracuseStep 5360147 = 8040221) B8040221
theorem B3574313 : Blo 1587492 3574313 := bstep (se 2 (by rfl) ⟨1340367, by rfl⟩ : syracuseStep 3574313 = 2680735) B2680735
theorem B14486483 : Blo 1587492 14486483 := bstep (se 1 (by rfl) ⟨10864862, by rfl⟩ : syracuseStep 14486483 = 21729725) B21729725
theorem B6032353 : Blo 1587492 6032353 := bstep (se 2 (by rfl) ⟨2262132, by rfl⟩ : syracuseStep 6032353 = 4524265) B4524265
theorem B3574889 : Blo 1587492 3574889 := bstep (se 2 (by rfl) ⟨1340583, by rfl⟩ : syracuseStep 3574889 = 2681167) B2681167
theorem B4582507 : Blo 1587492 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B2682031 : Blo 1587492 2682031 := bstep (se 1 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 2682031 = 4023047) B4023047
theorem B6532283 : Blo 1587492 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B8039735 : Blo 1587492 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B33066407 : Blo 1587492 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B43495055 : Blo 1587492 43495055 := bstep (se 1 (by rfl) ⟨32621291, by rfl⟩ : syracuseStep 43495055 = 65242583) B65242583
theorem B4525895 : Blo 1587492 4525895 := bstep (se 1 (by rfl) ⟨3394421, by rfl⟩ : syracuseStep 4525895 = 6788843) B6788843
theorem B3575663 : Blo 1587492 3575663 := bstep (se 1 (by rfl) ⟨2681747, by rfl⟩ : syracuseStep 3575663 = 5363495) B5363495
theorem B10874935 : Blo 1587492 10874935 := bstep (se 1 (by rfl) ⟨8156201, by rfl⟩ : syracuseStep 10874935 = 16312403) B16312403
theorem B5443865 : Blo 1587492 5443865 := bstep (se 2 (by rfl) ⟨2041449, by rfl⟩ : syracuseStep 5443865 = 4082899) B4082899
theorem B2863387 : Blo 1587492 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B2863583 : Blo 1587492 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B15266627 : Blo 1587492 15266627 := bstep (se 1 (by rfl) ⟨11449970, by rfl⟩ : syracuseStep 15266627 = 22899941) B22899941
theorem B27145043 : Blo 1587492 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B5362631 : Blo 1587492 5362631 := bstep (se 1 (by rfl) ⟨4021973, by rfl⟩ : syracuseStep 5362631 = 8043947) B8043947
theorem B4019291 : Blo 1587492 4019291 := bstep (se 1 (by rfl) ⟨3014468, by rfl⟩ : syracuseStep 4019291 = 6028937) B6028937
theorem B4019321 : Blo 1587492 4019321 := bstep (se 2 (by rfl) ⟨1507245, by rfl⟩ : syracuseStep 4019321 = 3014491) B3014491
theorem B6034601 : Blo 1587492 6034601 := bstep (se 2 (by rfl) ⟨2262975, by rfl⟩ : syracuseStep 6034601 = 4525951) B4525951
theorem B20362427 : Blo 1587492 20362427 := bstep (se 1 (by rfl) ⟨15271820, by rfl⟩ : syracuseStep 20362427 = 30543641) B30543641
theorem B12063977 : Blo 1587492 12063977 := bstep (se 2 (by rfl) ⟨4523991, by rfl⟩ : syracuseStep 12063977 = 9047983) B9047983
theorem B5436841 : Blo 1587492 5436841 := bstep (se 2 (by rfl) ⟨2038815, by rfl⟩ : syracuseStep 5436841 = 4077631) B4077631
theorem B7632623 : Blo 1587492 7632623 := bstep (se 1 (by rfl) ⟨5724467, by rfl⟩ : syracuseStep 7632623 = 11448935) B11448935
theorem B6436751 : Blo 1587492 6436751 := bstep (se 1 (by rfl) ⟨4827563, by rfl⟩ : syracuseStep 6436751 = 9655127) B9655127
theorem B35764253 : Blo 1587492 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B12056687 : Blo 1587492 12056687 := bstep (se 1 (by rfl) ⟨9042515, by rfl⟩ : syracuseStep 12056687 = 18085031) B18085031
theorem B6781067 : Blo 1587492 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B9042151 : Blo 1587492 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B12876029 : Blo 1587492 12876029 := bstep (se 3 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 12876029 = 4828511) B4828511
theorem B21748007 : Blo 1587492 21748007 := bstep (se 1 (by rfl) ⟨16311005, by rfl⟩ : syracuseStep 21748007 = 32622011) B32622011
theorem B1587611 : Blo 1587492 1587611 := bstep (se 1 (by rfl) ⟨1190708, by rfl⟩ : syracuseStep 1587611 = 2381417) B2381417
theorem B2382329 : Blo 1587492 2382329 := bstep (se 2 (by rfl) ⟨893373, by rfl⟩ : syracuseStep 2382329 = 1786747) B1786747
theorem B6437431 : Blo 1587492 6437431 := bstep (se 1 (by rfl) ⟨4828073, by rfl⟩ : syracuseStep 6437431 = 9656147) B9656147
theorem B5364467 : Blo 1587492 5364467 := bstep (se 1 (by rfl) ⟨4023350, by rfl⟩ : syracuseStep 5364467 = 8046701) B8046701
theorem B1587967 : Blo 1587492 1587967 := bstep (se 1 (by rfl) ⟨1190975, by rfl⟩ : syracuseStep 1587967 = 2381951) B2381951
theorem B73358131 : Blo 1587492 73358131 := bstep (se 1 (by rfl) ⟨55018598, by rfl⟩ : syracuseStep 73358131 = 110037197) B110037197
theorem B1588031 : Blo 1587492 1588031 := bstep (se 1 (by rfl) ⟨1191023, by rfl⟩ : syracuseStep 1588031 = 2382047) B2382047
theorem B1588071 : Blo 1587492 1588071 := bstep (se 1 (by rfl) ⟨1191053, by rfl⟩ : syracuseStep 1588071 = 2382107) B2382107
theorem B6437951 : Blo 1587492 6437951 := bstep (se 1 (by rfl) ⟨4828463, by rfl⟩ : syracuseStep 6437951 = 9656927) B9656927
theorem B1588287 : Blo 1587492 1588287 := bstep (se 1 (by rfl) ⟨1191215, by rfl⟩ : syracuseStep 1588287 = 2382431) B2382431
theorem B2382959 : Blo 1587492 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B1588351 : Blo 1587492 1588351 := bstep (se 1 (by rfl) ⟨1191263, by rfl⟩ : syracuseStep 1588351 = 2382527) B2382527
theorem B1588379 : Blo 1587492 1588379 := bstep (se 1 (by rfl) ⟨1191284, by rfl⟩ : syracuseStep 1588379 = 2382569) B2382569
theorem B1588463 : Blo 1587492 1588463 := bstep (se 1 (by rfl) ⟨1191347, by rfl⟩ : syracuseStep 1588463 = 2382695) B2382695
theorem B1588507 : Blo 1587492 1588507 := bstep (se 1 (by rfl) ⟨1191380, by rfl⟩ : syracuseStep 1588507 = 2382761) B2382761
theorem B4021559 : Blo 1587492 4021559 := bstep (se 1 (by rfl) ⟨3016169, by rfl⟩ : syracuseStep 4021559 = 6032339) B6032339
theorem B2415935 : Blo 1587492 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B3816811 : Blo 1587492 3816811 := bstep (se 1 (by rfl) ⟨2862608, by rfl⟩ : syracuseStep 3816811 = 5725217) B5725217
theorem B1588607 : Blo 1587492 1588607 := bstep (se 1 (by rfl) ⟨1191455, by rfl⟩ : syracuseStep 1588607 = 2382911) B2382911
theorem B1588635 : Blo 1587492 1588635 := bstep (se 1 (by rfl) ⟨1191476, by rfl⟩ : syracuseStep 1588635 = 2382953) B2382953
theorem B1588719 : Blo 1587492 1588719 := bstep (se 1 (by rfl) ⟨1191539, by rfl⟩ : syracuseStep 1588719 = 2383079) B2383079
theorem B2383343 : Blo 1587492 2383343 := bstep (se 1 (by rfl) ⟨1787507, by rfl⟩ : syracuseStep 2383343 = 3575015) B3575015
theorem B12058145 : Blo 1587492 12058145 := bstep (se 2 (by rfl) ⟨4521804, by rfl⟩ : syracuseStep 12058145 = 9043609) B9043609
theorem B1695335 : Blo 1587492 1695335 := bstep (se 1 (by rfl) ⟨1271501, by rfl⟩ : syracuseStep 1695335 = 2543003) B2543003
theorem B12066407 : Blo 1587492 12066407 := bstep (se 1 (by rfl) ⟨9049805, by rfl⟩ : syracuseStep 12066407 = 18099611) B18099611
theorem B1589055 : Blo 1587492 1589055 := bstep (se 1 (by rfl) ⟨1191791, by rfl⟩ : syracuseStep 1589055 = 2383583) B2383583
theorem B14499913 : Blo 1587492 14499913 := bstep (se 2 (by rfl) ⟨5437467, by rfl⟩ : syracuseStep 14499913 = 10874935) B10874935
theorem B32604275 : Blo 1587492 32604275 := bstep (se 1 (by rfl) ⟨24453206, by rfl⟩ : syracuseStep 32604275 = 48906413) B48906413
theorem B1589407 : Blo 1587492 1589407 := bstep (se 1 (by rfl) ⟨1192055, by rfl⟩ : syracuseStep 1589407 = 2384111) B2384111
theorem B3629243 : Blo 1587492 3629243 := bstep (se 1 (by rfl) ⟨2721932, by rfl⟩ : syracuseStep 3629243 = 5443865) B5443865
theorem B5800175 : Blo 1587492 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B1909055 : Blo 1587492 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B3817849 : Blo 1587492 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B4588073 : Blo 1587492 4588073 := bstep (se 2 (by rfl) ⟨1720527, by rfl⟩ : syracuseStep 4588073 = 3441055) B3441055
theorem B18096695 : Blo 1587492 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B2679527 : Blo 1587492 2679527 := bstep (se 1 (by rfl) ⟨2009645, by rfl⟩ : syracuseStep 2679527 = 4019291) B4019291
theorem B2679547 : Blo 1587492 2679547 := bstep (se 1 (by rfl) ⟨2009660, by rfl⟩ : syracuseStep 2679547 = 4019321) B4019321
theorem B4023067 : Blo 1587492 4023067 := bstep (se 1 (by rfl) ⟨3017300, by rfl⟩ : syracuseStep 4023067 = 6034601) B6034601
theorem B13574951 : Blo 1587492 13574951 := bstep (se 1 (by rfl) ⟨10181213, by rfl⟩ : syracuseStep 13574951 = 20362427) B20362427
theorem B30540635 : Blo 1587492 30540635 := bstep (se 1 (by rfl) ⟨22905476, by rfl⟩ : syracuseStep 30540635 = 45810953) B45810953
theorem B4293503 : Blo 1587492 4293503 := bstep (se 1 (by rfl) ⟨3220127, by rfl⟩ : syracuseStep 4293503 = 6440255) B6440255
theorem B3572819 : Blo 1587492 3572819 := bstep (se 1 (by rfl) ⟨2679614, by rfl⟩ : syracuseStep 3572819 = 5359229) B5359229
theorem B3572891 : Blo 1587492 3572891 := bstep (se 1 (by rfl) ⟨2679668, by rfl⟩ : syracuseStep 3572891 = 5359337) B5359337
theorem B1787035 : Blo 1587492 1787035 := bstep (se 1 (by rfl) ⟨1340276, by rfl⟩ : syracuseStep 1787035 = 2680553) B2680553
theorem B5088415 : Blo 1587492 5088415 := bstep (se 1 (by rfl) ⟨3816311, by rfl⟩ : syracuseStep 5088415 = 7632623) B7632623
theorem B8037791 : Blo 1587492 8037791 := bstep (se 1 (by rfl) ⟨6028343, by rfl⟩ : syracuseStep 8037791 = 12056687) B12056687
theorem B3573431 : Blo 1587492 3573431 := bstep (se 1 (by rfl) ⟨2680073, by rfl⟩ : syracuseStep 3573431 = 5360147) B5360147
theorem B5089081 : Blo 1587492 5089081 := bstep (se 2 (by rfl) ⟨1908405, by rfl⟩ : syracuseStep 5089081 = 3816811) B3816811
theorem B3573737 : Blo 1587492 3573737 := bstep (se 2 (by rfl) ⟨1340151, by rfl⟩ : syracuseStep 3573737 = 2680303) B2680303
theorem B5359823 : Blo 1587492 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B2681039 : Blo 1587492 2681039 := bstep (se 1 (by rfl) ⟨2010779, by rfl⟩ : syracuseStep 2681039 = 4021559) B4021559
theorem B8038763 : Blo 1587492 8038763 := bstep (se 1 (by rfl) ⟨6029072, by rfl⟩ : syracuseStep 8038763 = 12058145) B12058145
theorem B17164669 : Blo 1587492 17164669 := bstep (se 3 (by rfl) ⟨3218375, by rfl⟩ : syracuseStep 17164669 = 6436751) B6436751
theorem B3017263 : Blo 1587492 3017263 := bstep (se 1 (by rfl) ⟨2262947, by rfl⟩ : syracuseStep 3017263 = 4525895) B4525895
theorem B2681599 : Blo 1587492 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B17419421 : Blo 1587492 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B10177751 : Blo 1587492 10177751 := bstep (se 1 (by rfl) ⟨7633313, by rfl⟩ : syracuseStep 10177751 = 15266627) B15266627
theorem B3575087 : Blo 1587492 3575087 := bstep (se 1 (by rfl) ⟨2681315, by rfl⟩ : syracuseStep 3575087 = 5362631) B5362631
theorem B18083573 : Blo 1587492 18083573 := bstep (se 5 (by rfl) ⟨847667, by rfl⟩ : syracuseStep 18083573 = 1695335) B1695335
theorem B23842835 : Blo 1587492 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B8040545 : Blo 1587492 8040545 := bstep (se 2 (by rfl) ⟨3015204, by rfl⟩ : syracuseStep 8040545 = 6030409) B6030409
theorem B3576041 : Blo 1587492 3576041 := bstep (se 2 (by rfl) ⟨1341015, by rfl⟩ : syracuseStep 3576041 = 2682031) B2682031
theorem B3576311 : Blo 1587492 3576311 := bstep (se 1 (by rfl) ⟨2682233, by rfl⟩ : syracuseStep 3576311 = 5364467) B5364467
theorem B2863993 : Blo 1587492 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B1610623 : Blo 1587492 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B28996703 : Blo 1587492 28996703 := bstep (se 1 (by rfl) ⟨21747527, by rfl⟩ : syracuseStep 28996703 = 43495055) B43495055
theorem B38630621 : Blo 1587492 38630621 := bstep (se 3 (by rfl) ⟨7243241, by rfl⟩ : syracuseStep 38630621 = 14486483) B14486483
theorem B5363279 : Blo 1587492 5363279 := bstep (se 1 (by rfl) ⟨4022459, by rfl⟩ : syracuseStep 5363279 = 8044919) B8044919
theorem B12056201 : Blo 1587492 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B2381723 : Blo 1587492 2381723 := bstep (se 1 (by rfl) ⟨1786292, by rfl⟩ : syracuseStep 2381723 = 3572585) B3572585
theorem B8148937 : Blo 1587492 8148937 := bstep (se 2 (by rfl) ⟨3055851, by rfl⟩ : syracuseStep 8148937 = 6111703) B6111703
theorem B8583241 : Blo 1587492 8583241 := bstep (se 2 (by rfl) ⟨3218715, by rfl⟩ : syracuseStep 8583241 = 6437431) B6437431
theorem B8042651 : Blo 1587492 8042651 := bstep (se 1 (by rfl) ⟨6031988, by rfl⟩ : syracuseStep 8042651 = 12063977) B12063977
theorem B97810841 : Blo 1587492 97810841 := bstep (se 2 (by rfl) ⟨36679065, by rfl⟩ : syracuseStep 97810841 = 73358131) B73358131
theorem B40704443 : Blo 1587492 40704443 := bstep (se 1 (by rfl) ⟨30528332, by rfl⟩ : syracuseStep 40704443 = 61056665) B61056665
theorem B88177085 : Blo 1587492 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B2382377 : Blo 1587492 2382377 := bstep (se 2 (by rfl) ⟨893391, by rfl⟩ : syracuseStep 2382377 = 1786783) B1786783
theorem B8043137 : Blo 1587492 8043137 := bstep (se 2 (by rfl) ⟨3016176, by rfl⟩ : syracuseStep 8043137 = 6032353) B6032353
theorem B4020961 : Blo 1587492 4020961 := bstep (se 2 (by rfl) ⟨1507860, by rfl⟩ : syracuseStep 4020961 = 3015721) B3015721
theorem B4520711 : Blo 1587492 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B6110009 : Blo 1587492 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B8584019 : Blo 1587492 8584019 := bstep (se 1 (by rfl) ⟨6438014, by rfl⟩ : syracuseStep 8584019 = 12876029) B12876029
theorem B14498671 : Blo 1587492 14498671 := bstep (se 1 (by rfl) ⟨10874003, by rfl⟩ : syracuseStep 14498671 = 21748007) B21748007
theorem B1588219 : Blo 1587492 1588219 := bstep (se 1 (by rfl) ⟨1191164, by rfl⟩ : syracuseStep 1588219 = 2382329) B2382329
theorem B2382875 : Blo 1587492 2382875 := bstep (se 1 (by rfl) ⟨1787156, by rfl⟩ : syracuseStep 2382875 = 3574313) B3574313
theorem B7249121 : Blo 1587492 7249121 := bstep (se 2 (by rfl) ⟨2718420, by rfl⟩ : syracuseStep 7249121 = 5436841) B5436841
theorem B4291967 : Blo 1587492 4291967 := bstep (se 1 (by rfl) ⟨3218975, by rfl⟩ : syracuseStep 4291967 = 6437951) B6437951
theorem B2383259 : Blo 1587492 2383259 := bstep (se 1 (by rfl) ⟨1787444, by rfl⟩ : syracuseStep 2383259 = 3574889) B3574889
theorem B1588639 : Blo 1587492 1588639 := bstep (se 1 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 1588639 = 2382959) B2382959
theorem B1588895 : Blo 1587492 1588895 := bstep (se 1 (by rfl) ⟨1191671, by rfl⟩ : syracuseStep 1588895 = 2383343) B2383343
theorem B8044271 : Blo 1587492 8044271 := bstep (se 1 (by rfl) ⟨6033203, by rfl⟩ : syracuseStep 8044271 = 12066407) B12066407
theorem B2383775 : Blo 1587492 2383775 := bstep (se 1 (by rfl) ⟨1787831, by rfl⟩ : syracuseStep 2383775 = 3575663) B3575663
theorem B11444321 : Blo 1587492 11444321 := bstep (se 2 (by rfl) ⟨4291620, by rfl⟩ : syracuseStep 11444321 = 8583241) B8583241
theorem B19333217 : Blo 1587492 19333217 := bstep (se 2 (by rfl) ⟨7249956, by rfl⟩ : syracuseStep 19333217 = 14499913) B14499913
theorem B2384027 : Blo 1587492 2384027 := bstep (se 1 (by rfl) ⟨1788020, by rfl⟩ : syracuseStep 2384027 = 3576041) B3576041
theorem B3866783 : Blo 1587492 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B2384207 : Blo 1587492 2384207 := bstep (se 1 (by rfl) ⟨1788155, by rfl⟩ : syracuseStep 2384207 = 3576311) B3576311
theorem B1786351 : Blo 1587492 1786351 := bstep (se 1 (by rfl) ⟨1339763, by rfl⟩ : syracuseStep 1786351 = 2679527) B2679527
theorem B27140669 : Blo 1587492 27140669 := bstep (se 3 (by rfl) ⟨5088875, by rfl⟩ : syracuseStep 27140669 = 10177751) B10177751
theorem B4023017 : Blo 1587492 4023017 := bstep (se 2 (by rfl) ⟨1508631, by rfl⟩ : syracuseStep 4023017 = 3017263) B3017263
theorem B5358527 : Blo 1587492 5358527 := bstep (se 1 (by rfl) ⟨4018895, by rfl⟩ : syracuseStep 5358527 = 8037791) B8037791
theorem B3572729 : Blo 1587492 3572729 := bstep (se 2 (by rfl) ⟨1339773, by rfl⟩ : syracuseStep 3572729 = 2679547) B2679547
theorem B11445245 : Blo 1587492 11445245 := bstep (se 3 (by rfl) ⟨2145983, by rfl⟩ : syracuseStep 11445245 = 4291967) B4291967
theorem B8037467 : Blo 1587492 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B3818657 : Blo 1587492 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B3573215 : Blo 1587492 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1787359 : Blo 1587492 1787359 := bstep (se 1 (by rfl) ⟨1340519, by rfl⟩ : syracuseStep 1787359 = 2681039) B2681039
theorem B6784553 : Blo 1587492 6784553 := bstep (se 2 (by rfl) ⟨2544207, by rfl⟩ : syracuseStep 6784553 = 5088415) B5088415
theorem B5359175 : Blo 1587492 5359175 := bstep (se 1 (by rfl) ⟨4019381, by rfl⟩ : syracuseStep 5359175 = 8038763) B8038763
theorem B4073339 : Blo 1587492 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B6785441 : Blo 1587492 6785441 := bstep (se 2 (by rfl) ⟨2544540, by rfl⟩ : syracuseStep 6785441 = 5089081) B5089081
theorem B10865249 : Blo 1587492 10865249 := bstep (se 2 (by rfl) ⟨4074468, by rfl⟩ : syracuseStep 10865249 = 8148937) B8148937
theorem B15895223 : Blo 1587492 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B5360363 : Blo 1587492 5360363 := bstep (se 1 (by rfl) ⟨4020272, by rfl⟩ : syracuseStep 5360363 = 8040545) B8040545
theorem B21736183 : Blo 1587492 21736183 := bstep (se 1 (by rfl) ⟨16302137, by rfl⟩ : syracuseStep 21736183 = 32604275) B32604275
theorem B3058715 : Blo 1587492 3058715 := bstep (se 1 (by rfl) ⟨2294036, by rfl⟩ : syracuseStep 3058715 = 4588073) B4588073
theorem B46451789 : Blo 1587492 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B9677981 : Blo 1587492 9677981 := bstep (se 3 (by rfl) ⟨1814621, by rfl⟩ : syracuseStep 9677981 = 3629243) B3629243
theorem B5090465 : Blo 1587492 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B20360423 : Blo 1587492 20360423 := bstep (se 1 (by rfl) ⟨15270317, by rfl⟩ : syracuseStep 20360423 = 30540635) B30540635
theorem B2862335 : Blo 1587492 2862335 := bstep (se 1 (by rfl) ⟨2146751, by rfl⟩ : syracuseStep 2862335 = 4293503) B4293503
theorem B5090813 : Blo 1587492 5090813 := bstep (se 3 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 5090813 = 1909055) B1909055
theorem B5361281 : Blo 1587492 5361281 := bstep (se 2 (by rfl) ⟨2010480, by rfl⟩ : syracuseStep 5361281 = 4020961) B4020961
theorem B3575465 : Blo 1587492 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B3575519 : Blo 1587492 3575519 := bstep (se 1 (by rfl) ⟨2681639, by rfl⟩ : syracuseStep 3575519 = 5363279) B5363279
theorem B5361767 : Blo 1587492 5361767 := bstep (se 1 (by rfl) ⟨4021325, by rfl⟩ : syracuseStep 5361767 = 8042651) B8042651
theorem B27136295 : Blo 1587492 27136295 := bstep (se 1 (by rfl) ⟨20352221, by rfl⟩ : syracuseStep 27136295 = 40704443) B40704443
theorem B5362091 : Blo 1587492 5362091 := bstep (se 1 (by rfl) ⟨4021568, by rfl⟩ : syracuseStep 5362091 = 8043137) B8043137
theorem B5722679 : Blo 1587492 5722679 := bstep (se 1 (by rfl) ⟨4292009, by rfl⟩ : syracuseStep 5722679 = 8584019) B8584019
theorem B8589989 : Blo 1587492 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B12055229 : Blo 1587492 12055229 := bstep (se 3 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 12055229 = 4520711) B4520711
theorem B5362847 : Blo 1587492 5362847 := bstep (se 1 (by rfl) ⟨4022135, by rfl⟩ : syracuseStep 5362847 = 8044271) B8044271
theorem B12055715 : Blo 1587492 12055715 := bstep (se 1 (by rfl) ⟨9041786, by rfl⟩ : syracuseStep 12055715 = 18083573) B18083573
theorem B12064463 : Blo 1587492 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B22886225 : Blo 1587492 22886225 := bstep (se 2 (by rfl) ⟨8582334, by rfl⟩ : syracuseStep 22886225 = 17164669) B17164669
theorem B9049967 : Blo 1587492 9049967 := bstep (se 1 (by rfl) ⟨6787475, by rfl⟩ : syracuseStep 9049967 = 13574951) B13574951
theorem B2381879 : Blo 1587492 2381879 := bstep (se 1 (by rfl) ⟨1786409, by rfl⟩ : syracuseStep 2381879 = 3572819) B3572819
theorem B19331135 : Blo 1587492 19331135 := bstep (se 1 (by rfl) ⟨14498351, by rfl⟩ : syracuseStep 19331135 = 28996703) B28996703
theorem B2381927 : Blo 1587492 2381927 := bstep (se 1 (by rfl) ⟨1786445, by rfl⟩ : syracuseStep 2381927 = 3572891) B3572891
theorem B25753747 : Blo 1587492 25753747 := bstep (se 1 (by rfl) ⟨19315310, by rfl⟩ : syracuseStep 25753747 = 38630621) B38630621
theorem B5364089 : Blo 1587492 5364089 := bstep (se 2 (by rfl) ⟨2011533, by rfl⟩ : syracuseStep 5364089 = 4023067) B4023067
theorem B2382287 : Blo 1587492 2382287 := bstep (se 1 (by rfl) ⟨1786715, by rfl⟩ : syracuseStep 2382287 = 3573431) B3573431
theorem B19331561 : Blo 1587492 19331561 := bstep (se 2 (by rfl) ⟨7249335, by rfl⟩ : syracuseStep 19331561 = 14498671) B14498671
theorem B1587815 : Blo 1587492 1587815 := bstep (se 1 (by rfl) ⟨1190861, by rfl⟩ : syracuseStep 1587815 = 2381723) B2381723
theorem B2382491 : Blo 1587492 2382491 := bstep (se 1 (by rfl) ⟨1786868, by rfl⟩ : syracuseStep 2382491 = 3573737) B3573737
theorem B2382713 : Blo 1587492 2382713 := bstep (se 2 (by rfl) ⟨893517, by rfl⟩ : syracuseStep 2382713 = 1787035) B1787035
theorem B65207227 : Blo 1587492 65207227 := bstep (se 1 (by rfl) ⟨48905420, by rfl⟩ : syracuseStep 65207227 = 97810841) B97810841
theorem B58784723 : Blo 1587492 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B1588251 : Blo 1587492 1588251 := bstep (se 1 (by rfl) ⟨1191188, by rfl⟩ : syracuseStep 1588251 = 2382377) B2382377
theorem B1588583 : Blo 1587492 1588583 := bstep (se 1 (by rfl) ⟨1191437, by rfl⟩ : syracuseStep 1588583 = 2382875) B2382875
theorem B4832747 : Blo 1587492 4832747 := bstep (se 1 (by rfl) ⟨3624560, by rfl⟩ : syracuseStep 4832747 = 7249121) B7249121
theorem B2383391 : Blo 1587492 2383391 := bstep (se 1 (by rfl) ⟨1787543, by rfl⟩ : syracuseStep 2383391 = 3575087) B3575087
theorem B1588839 : Blo 1587492 1588839 := bstep (se 1 (by rfl) ⟨1191629, by rfl⟩ : syracuseStep 1588839 = 2383259) B2383259
theorem B1589183 : Blo 1587492 1589183 := bstep (se 1 (by rfl) ⟨1191887, by rfl⟩ : syracuseStep 1589183 = 2383775) B2383775
theorem B1589351 : Blo 1587492 1589351 := bstep (se 1 (by rfl) ⟨1192013, by rfl⟩ : syracuseStep 1589351 = 2384027) B2384027
theorem B1589471 : Blo 1587492 1589471 := bstep (se 1 (by rfl) ⟨1192103, by rfl⟩ : syracuseStep 1589471 = 2384207) B2384207
theorem B13574573 : Blo 1587492 13574573 := bstep (se 3 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 13574573 = 5090465) B5090465
theorem B8036819 : Blo 1587492 8036819 := bstep (se 1 (by rfl) ⟨6027614, by rfl⟩ : syracuseStep 8036819 = 12055229) B12055229
theorem B3572351 : Blo 1587492 3572351 := bstep (se 1 (by rfl) ⟨2679263, by rfl⟩ : syracuseStep 3572351 = 5358527) B5358527
theorem B5358311 : Blo 1587492 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B8037143 : Blo 1587492 8037143 := bstep (se 1 (by rfl) ⟨6027857, by rfl⟩ : syracuseStep 8037143 = 12055715) B12055715
theorem B4523035 : Blo 1587492 4523035 := bstep (se 1 (by rfl) ⟨3392276, by rfl⟩ : syracuseStep 4523035 = 6784553) B6784553
theorem B3572783 : Blo 1587492 3572783 := bstep (se 1 (by rfl) ⟨2679587, by rfl⟩ : syracuseStep 3572783 = 5359175) B5359175
theorem B86942969 : Blo 1587492 86942969 := bstep (se 2 (by rfl) ⟨32603613, by rfl⟩ : syracuseStep 86942969 = 65207227) B65207227
theorem B12887423 : Blo 1587492 12887423 := bstep (se 1 (by rfl) ⟨9665567, by rfl⟩ : syracuseStep 12887423 = 19331135) B19331135
theorem B4523627 : Blo 1587492 4523627 := bstep (se 1 (by rfl) ⟨3392720, by rfl⟩ : syracuseStep 4523627 = 6785441) B6785441
theorem B12887707 : Blo 1587492 12887707 := bstep (se 1 (by rfl) ⟨9665780, by rfl⟩ : syracuseStep 12887707 = 19331561) B19331561
theorem B7243499 : Blo 1587492 7243499 := bstep (se 1 (by rfl) ⟨5432624, by rfl⟩ : syracuseStep 7243499 = 10865249) B10865249
theorem B22906637 : Blo 1587492 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B3573575 : Blo 1587492 3573575 := bstep (se 1 (by rfl) ⟨2680181, by rfl⟩ : syracuseStep 3573575 = 5360363) B5360363
theorem B30967859 : Blo 1587492 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B3221831 : Blo 1587492 3221831 := bstep (se 1 (by rfl) ⟨2416373, by rfl⟩ : syracuseStep 3221831 = 4832747) B4832747
theorem B3393875 : Blo 1587492 3393875 := bstep (se 1 (by rfl) ⟨2545406, by rfl⟩ : syracuseStep 3393875 = 5090813) B5090813
theorem B3574187 : Blo 1587492 3574187 := bstep (se 1 (by rfl) ⟨2680640, by rfl⟩ : syracuseStep 3574187 = 5361281) B5361281
theorem B7629547 : Blo 1587492 7629547 := bstep (se 1 (by rfl) ⟨5722160, by rfl⟩ : syracuseStep 7629547 = 11444321) B11444321
theorem B12888811 : Blo 1587492 12888811 := bstep (se 1 (by rfl) ⟨9666608, by rfl⟩ : syracuseStep 12888811 = 19333217) B19333217
theorem B3574511 : Blo 1587492 3574511 := bstep (se 1 (by rfl) ⟨2680883, by rfl⟩ : syracuseStep 3574511 = 5361767) B5361767
theorem B18090863 : Blo 1587492 18090863 := bstep (se 1 (by rfl) ⟨13568147, by rfl⟩ : syracuseStep 18090863 = 27136295) B27136295
theorem B3574727 : Blo 1587492 3574727 := bstep (se 1 (by rfl) ⟨2681045, by rfl⟩ : syracuseStep 3574727 = 5362091) B5362091
theorem B2682011 : Blo 1587492 2682011 := bstep (se 1 (by rfl) ⟨2011508, by rfl⟩ : syracuseStep 2682011 = 4023017) B4023017
theorem B7630163 : Blo 1587492 7630163 := bstep (se 1 (by rfl) ⟨5722622, by rfl⟩ : syracuseStep 7630163 = 11445245) B11445245
theorem B3575231 : Blo 1587492 3575231 := bstep (se 1 (by rfl) ⟨2681423, by rfl⟩ : syracuseStep 3575231 = 5362847) B5362847
theorem B15257483 : Blo 1587492 15257483 := bstep (se 1 (by rfl) ⟨11443112, by rfl⟩ : syracuseStep 15257483 = 22886225) B22886225
theorem B6033311 : Blo 1587492 6033311 := bstep (se 1 (by rfl) ⟨4524983, by rfl⟩ : syracuseStep 6033311 = 9049967) B9049967
theorem B3576059 : Blo 1587492 3576059 := bstep (se 1 (by rfl) ⟨2682044, by rfl⟩ : syracuseStep 3576059 = 5364089) B5364089
theorem B10596815 : Blo 1587492 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B6451987 : Blo 1587492 6451987 := bstep (se 1 (by rfl) ⟨4838990, by rfl⟩ : syracuseStep 6451987 = 9677981) B9677981
theorem B34338329 : Blo 1587492 34338329 := bstep (se 2 (by rfl) ⟨12876873, by rfl⟩ : syracuseStep 34338329 = 25753747) B25753747
theorem B3815119 : Blo 1587492 3815119 := bstep (se 1 (by rfl) ⟨2861339, by rfl⟩ : syracuseStep 3815119 = 5722679) B5722679
theorem B18093779 : Blo 1587492 18093779 := bstep (se 1 (by rfl) ⟨13570334, by rfl⟩ : syracuseStep 18093779 = 27140669) B27140669
theorem B10311421 : Blo 1587492 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B2381801 : Blo 1587492 2381801 := bstep (se 2 (by rfl) ⟨893175, by rfl⟩ : syracuseStep 2381801 = 1786351) B1786351
theorem B2381819 : Blo 1587492 2381819 := bstep (se 1 (by rfl) ⟨1786364, by rfl⟩ : syracuseStep 2381819 = 3572729) B3572729
theorem B7632893 : Blo 1587492 7632893 := bstep (se 3 (by rfl) ⟨1431167, by rfl⟩ : syracuseStep 7632893 = 2862335) B2862335
theorem B2545771 : Blo 1587492 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B2382143 : Blo 1587492 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B28981577 : Blo 1587492 28981577 := bstep (se 2 (by rfl) ⟨10868091, by rfl⟩ : syracuseStep 28981577 = 21736183) B21736183
theorem B8042975 : Blo 1587492 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B1587919 : Blo 1587492 1587919 := bstep (se 1 (by rfl) ⟨1190939, by rfl⟩ : syracuseStep 1587919 = 2381879) B2381879
theorem B1587951 : Blo 1587492 1587951 := bstep (se 1 (by rfl) ⟨1190963, by rfl⟩ : syracuseStep 1587951 = 2381927) B2381927
theorem B1588191 : Blo 1587492 1588191 := bstep (se 1 (by rfl) ⟨1191143, by rfl⟩ : syracuseStep 1588191 = 2382287) B2382287
theorem B1588327 : Blo 1587492 1588327 := bstep (se 1 (by rfl) ⟨1191245, by rfl⟩ : syracuseStep 1588327 = 2382491) B2382491
theorem B1588475 : Blo 1587492 1588475 := bstep (se 1 (by rfl) ⟨1191356, by rfl⟩ : syracuseStep 1588475 = 2382713) B2382713
theorem B2383145 : Blo 1587492 2383145 := bstep (se 2 (by rfl) ⟨893679, by rfl⟩ : syracuseStep 2383145 = 1787359) B1787359
theorem B39189815 : Blo 1587492 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B2039143 : Blo 1587492 2039143 := bstep (se 1 (by rfl) ⟨1529357, by rfl⟩ : syracuseStep 2039143 = 3058715) B3058715
theorem B13573615 : Blo 1587492 13573615 := bstep (se 1 (by rfl) ⟨10180211, by rfl⟩ : syracuseStep 13573615 = 20360423) B20360423
theorem B10862237 : Blo 1587492 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B1588927 : Blo 1587492 1588927 := bstep (se 1 (by rfl) ⟨1191695, by rfl⟩ : syracuseStep 1588927 = 2383391) B2383391
theorem B2383643 : Blo 1587492 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B2383679 : Blo 1587492 2383679 := bstep (se 1 (by rfl) ⟨1787759, by rfl⟩ : syracuseStep 2383679 = 3575519) B3575519
theorem B2384039 : Blo 1587492 2384039 := bstep (se 1 (by rfl) ⟨1788029, by rfl⟩ : syracuseStep 2384039 = 3576059) B3576059
theorem B5357879 : Blo 1587492 5357879 := bstep (se 1 (by rfl) ⟨4018409, by rfl⟩ : syracuseStep 5357879 = 8036819) B8036819
theorem B3572207 : Blo 1587492 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B5358095 : Blo 1587492 5358095 := bstep (se 1 (by rfl) ⟨4018571, by rfl⟩ : syracuseStep 5358095 = 8037143) B8037143
theorem B8602649 : Blo 1587492 8602649 := bstep (se 2 (by rfl) ⟨3225993, by rfl⟩ : syracuseStep 8602649 = 6451987) B6451987
theorem B15271091 : Blo 1587492 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B5088595 : Blo 1587492 5088595 := bstep (se 1 (by rfl) ⟨3816446, by rfl⟩ : syracuseStep 5088595 = 7632893) B7632893
theorem B20645239 : Blo 1587492 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B6030713 : Blo 1587492 6030713 := bstep (se 2 (by rfl) ⟨2261517, by rfl⟩ : syracuseStep 6030713 = 4523035) B4523035
theorem B2147887 : Blo 1587492 2147887 := bstep (se 1 (by rfl) ⟨1610915, by rfl⟩ : syracuseStep 2147887 = 3221831) B3221831
theorem B2262583 : Blo 1587492 2262583 := bstep (se 1 (by rfl) ⟨1696937, by rfl⟩ : syracuseStep 2262583 = 3393875) B3393875
theorem B12060575 : Blo 1587492 12060575 := bstep (se 1 (by rfl) ⟨9045431, by rfl⟩ : syracuseStep 12060575 = 18090863) B18090863
theorem B18098153 : Blo 1587492 18098153 := bstep (se 2 (by rfl) ⟨6786807, by rfl⟩ : syracuseStep 18098153 = 13573615) B13573615
theorem B1788007 : Blo 1587492 1788007 := bstep (se 1 (by rfl) ⟨1341005, by rfl⟩ : syracuseStep 1788007 = 2682011) B2682011
theorem B26126543 : Blo 1587492 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B13748561 : Blo 1587492 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B3394361 : Blo 1587492 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B7064543 : Blo 1587492 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B57961979 : Blo 1587492 57961979 := bstep (se 1 (by rfl) ⟨43471484, by rfl⟩ : syracuseStep 57961979 = 86942969) B86942969
theorem B22892219 : Blo 1587492 22892219 := bstep (se 1 (by rfl) ⟨17169164, by rfl⟩ : syracuseStep 22892219 = 34338329) B34338329
theorem B12062519 : Blo 1587492 12062519 := bstep (se 1 (by rfl) ⟨9046889, by rfl⟩ : syracuseStep 12062519 = 18093779) B18093779
theorem B4828999 : Blo 1587492 4828999 := bstep (se 1 (by rfl) ⟨3621749, by rfl⟩ : syracuseStep 4828999 = 7243499) B7243499
theorem B19321051 : Blo 1587492 19321051 := bstep (se 1 (by rfl) ⟨14490788, by rfl⟩ : syracuseStep 19321051 = 28981577) B28981577
theorem B12063005 : Blo 1587492 12063005 := bstep (se 3 (by rfl) ⟨2261813, by rfl⟩ : syracuseStep 12063005 = 4523627) B4523627
theorem B5361983 : Blo 1587492 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B17183609 : Blo 1587492 17183609 := bstep (se 2 (by rfl) ⟨6443853, by rfl⟩ : syracuseStep 17183609 = 12887707) B12887707
theorem B10171655 : Blo 1587492 10171655 := bstep (se 1 (by rfl) ⟨7628741, by rfl⟩ : syracuseStep 10171655 = 15257483) B15257483
theorem B9049715 : Blo 1587492 9049715 := bstep (se 1 (by rfl) ⟨6787286, by rfl⟩ : syracuseStep 9049715 = 13574573) B13574573
theorem B2381567 : Blo 1587492 2381567 := bstep (se 1 (by rfl) ⟨1786175, by rfl⟩ : syracuseStep 2381567 = 3572351) B3572351
theorem B2381855 : Blo 1587492 2381855 := bstep (se 1 (by rfl) ⟨1786391, by rfl⟩ : syracuseStep 2381855 = 3572783) B3572783
theorem B8591615 : Blo 1587492 8591615 := bstep (se 1 (by rfl) ⟨6443711, by rfl⟩ : syracuseStep 8591615 = 12887423) B12887423
theorem B10172729 : Blo 1587492 10172729 := bstep (se 2 (by rfl) ⟨3814773, by rfl⟩ : syracuseStep 10172729 = 7629547) B7629547
theorem B17185081 : Blo 1587492 17185081 := bstep (se 2 (by rfl) ⟨6444405, by rfl⟩ : syracuseStep 17185081 = 12888811) B12888811
theorem B20347301 : Blo 1587492 20347301 := bstep (se 4 (by rfl) ⟨1907559, by rfl⟩ : syracuseStep 20347301 = 3815119) B3815119
theorem B2382383 : Blo 1587492 2382383 := bstep (se 1 (by rfl) ⟨1786787, by rfl⟩ : syracuseStep 2382383 = 3573575) B3573575
theorem B1587867 : Blo 1587492 1587867 := bstep (se 1 (by rfl) ⟨1190900, by rfl⟩ : syracuseStep 1587867 = 2381801) B2381801
theorem B1587879 : Blo 1587492 1587879 := bstep (se 1 (by rfl) ⟨1190909, by rfl⟩ : syracuseStep 1587879 = 2381819) B2381819
theorem B1588095 : Blo 1587492 1588095 := bstep (se 1 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 1588095 = 2382143) B2382143
theorem B2382791 : Blo 1587492 2382791 := bstep (se 1 (by rfl) ⟨1787093, by rfl⟩ : syracuseStep 2382791 = 3574187) B3574187
theorem B2718857 : Blo 1587492 2718857 := bstep (se 2 (by rfl) ⟨1019571, by rfl⟩ : syracuseStep 2718857 = 2039143) B2039143
theorem B2383007 : Blo 1587492 2383007 := bstep (se 1 (by rfl) ⟨1787255, by rfl⟩ : syracuseStep 2383007 = 3574511) B3574511
theorem B2383151 : Blo 1587492 2383151 := bstep (se 1 (by rfl) ⟨1787363, by rfl⟩ : syracuseStep 2383151 = 3574727) B3574727
theorem B1588763 : Blo 1587492 1588763 := bstep (se 1 (by rfl) ⟨1191572, by rfl⟩ : syracuseStep 1588763 = 2383145) B2383145
theorem B5086775 : Blo 1587492 5086775 := bstep (se 1 (by rfl) ⟨3815081, by rfl⟩ : syracuseStep 5086775 = 7630163) B7630163
theorem B2383487 : Blo 1587492 2383487 := bstep (se 1 (by rfl) ⟨1787615, by rfl⟩ : syracuseStep 2383487 = 3575231) B3575231
theorem B7241491 : Blo 1587492 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B1589095 : Blo 1587492 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B1589119 : Blo 1587492 1589119 := bstep (se 1 (by rfl) ⟨1191839, by rfl⟩ : syracuseStep 1589119 = 2383679) B2383679
theorem B4022207 : Blo 1587492 4022207 := bstep (se 1 (by rfl) ⟨3016655, by rfl⟩ : syracuseStep 4022207 = 6033311) B6033311
theorem B1589359 : Blo 1587492 1589359 := bstep (se 1 (by rfl) ⟨1192019, by rfl⟩ : syracuseStep 1589359 = 2384039) B2384039
theorem B2384009 : Blo 1587492 2384009 := bstep (se 2 (by rfl) ⟨894003, by rfl⟩ : syracuseStep 2384009 = 1788007) B1788007
theorem B3571919 : Blo 1587492 3571919 := bstep (se 1 (by rfl) ⟨2678939, by rfl⟩ : syracuseStep 3571919 = 5357879) B5357879
theorem B3572063 : Blo 1587492 3572063 := bstep (se 1 (by rfl) ⟨2679047, by rfl⟩ : syracuseStep 3572063 = 5358095) B5358095
theorem B7250285 : Blo 1587492 7250285 := bstep (se 3 (by rfl) ⟨1359428, by rfl⟩ : syracuseStep 7250285 = 2718857) B2718857
theorem B22913441 : Blo 1587492 22913441 := bstep (se 2 (by rfl) ⟨8592540, by rfl⟩ : syracuseStep 22913441 = 17185081) B17185081
theorem B5735099 : Blo 1587492 5735099 := bstep (se 1 (by rfl) ⟨4301324, by rfl⟩ : syracuseStep 5735099 = 8602649) B8602649
theorem B5727743 : Blo 1587492 5727743 := bstep (se 1 (by rfl) ⟨4295807, by rfl⟩ : syracuseStep 5727743 = 8591615) B8591615
theorem B6784793 : Blo 1587492 6784793 := bstep (se 2 (by rfl) ⟨2544297, by rfl⟩ : syracuseStep 6784793 = 5088595) B5088595
theorem B27526985 : Blo 1587492 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B2262907 : Blo 1587492 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B3016777 : Blo 1587492 3016777 := bstep (se 2 (by rfl) ⟨1131291, by rfl⟩ : syracuseStep 3016777 = 2262583) B2262583
theorem B2681471 : Blo 1587492 2681471 := bstep (se 1 (by rfl) ⟨2011103, by rfl⟩ : syracuseStep 2681471 = 4022207) B4022207
theorem B3574655 : Blo 1587492 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B11455739 : Blo 1587492 11455739 := bstep (se 1 (by rfl) ⟨8591804, by rfl⟩ : syracuseStep 11455739 = 17183609) B17183609
theorem B6033143 : Blo 1587492 6033143 := bstep (se 1 (by rfl) ⟨4524857, by rfl⟩ : syracuseStep 6033143 = 9049715) B9049715
theorem B8040383 : Blo 1587492 8040383 := bstep (se 1 (by rfl) ⟨6030287, by rfl⟩ : syracuseStep 8040383 = 12060575) B12060575
theorem B2863849 : Blo 1587492 2863849 := bstep (se 2 (by rfl) ⟨1073943, by rfl⟩ : syracuseStep 2863849 = 2147887) B2147887
theorem B9655321 : Blo 1587492 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B8041679 : Blo 1587492 8041679 := bstep (se 1 (by rfl) ⟨6031259, by rfl⟩ : syracuseStep 8041679 = 12062519) B12062519
theorem B18838781 : Blo 1587492 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B8042003 : Blo 1587492 8042003 := bstep (se 1 (by rfl) ⟨6031502, by rfl⟩ : syracuseStep 8042003 = 12063005) B12063005
theorem B25761401 : Blo 1587492 25761401 := bstep (se 2 (by rfl) ⟨9660525, by rfl⟩ : syracuseStep 25761401 = 19321051) B19321051
theorem B2381471 : Blo 1587492 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B69670781 : Blo 1587492 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B10180727 : Blo 1587492 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B6781103 : Blo 1587492 6781103 := bstep (se 1 (by rfl) ⟨5085827, by rfl⟩ : syracuseStep 6781103 = 10171655) B10171655
theorem B4020475 : Blo 1587492 4020475 := bstep (se 1 (by rfl) ⟨3015356, by rfl⟩ : syracuseStep 4020475 = 6030713) B6030713
theorem B1587711 : Blo 1587492 1587711 := bstep (se 1 (by rfl) ⟨1190783, by rfl⟩ : syracuseStep 1587711 = 2381567) B2381567
theorem B12065435 : Blo 1587492 12065435 := bstep (se 1 (by rfl) ⟨9049076, by rfl⟩ : syracuseStep 12065435 = 18098153) B18098153
theorem B1587903 : Blo 1587492 1587903 := bstep (se 1 (by rfl) ⟨1190927, by rfl⟩ : syracuseStep 1587903 = 2381855) B2381855
theorem B6781819 : Blo 1587492 6781819 := bstep (se 1 (by rfl) ⟨5086364, by rfl⟩ : syracuseStep 6781819 = 10172729) B10172729
theorem B9165707 : Blo 1587492 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B13564867 : Blo 1587492 13564867 := bstep (se 1 (by rfl) ⟨10173650, by rfl⟩ : syracuseStep 13564867 = 20347301) B20347301
theorem B1588255 : Blo 1587492 1588255 := bstep (se 1 (by rfl) ⟨1191191, by rfl⟩ : syracuseStep 1588255 = 2382383) B2382383
theorem B1588527 : Blo 1587492 1588527 := bstep (se 1 (by rfl) ⟨1191395, by rfl⟩ : syracuseStep 1588527 = 2382791) B2382791
theorem B1588671 : Blo 1587492 1588671 := bstep (se 1 (by rfl) ⟨1191503, by rfl⟩ : syracuseStep 1588671 = 2383007) B2383007
theorem B1588767 : Blo 1587492 1588767 := bstep (se 1 (by rfl) ⟨1191575, by rfl⟩ : syracuseStep 1588767 = 2383151) B2383151
theorem B38641319 : Blo 1587492 38641319 := bstep (se 1 (by rfl) ⟨28980989, by rfl⟩ : syracuseStep 38641319 = 57961979) B57961979
theorem B3391183 : Blo 1587492 3391183 := bstep (se 1 (by rfl) ⟨2543387, by rfl⟩ : syracuseStep 3391183 = 5086775) B5086775
theorem B1588991 : Blo 1587492 1588991 := bstep (se 1 (by rfl) ⟨1191743, by rfl⟩ : syracuseStep 1588991 = 2383487) B2383487
theorem B6438665 : Blo 1587492 6438665 := bstep (se 2 (by rfl) ⟨2414499, by rfl⟩ : syracuseStep 6438665 = 4828999) B4828999
theorem B15261479 : Blo 1587492 15261479 := bstep (se 1 (by rfl) ⟨11446109, by rfl⟩ : syracuseStep 15261479 = 22892219) B22892219
theorem B1589339 : Blo 1587492 1589339 := bstep (se 1 (by rfl) ⟨1192004, by rfl⟩ : syracuseStep 1589339 = 2384009) B2384009
theorem B4022369 : Blo 1587492 4022369 := bstep (se 2 (by rfl) ⟨1508388, by rfl⟩ : syracuseStep 4022369 = 3016777) B3016777
theorem B4833523 : Blo 1587492 4833523 := bstep (se 1 (by rfl) ⟨3625142, by rfl⟩ : syracuseStep 4833523 = 7250285) B7250285
theorem B12559187 : Blo 1587492 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B3818465 : Blo 1587492 3818465 := bstep (se 2 (by rfl) ⟨1431924, by rfl⟩ : syracuseStep 3818465 = 2863849) B2863849
theorem B3818495 : Blo 1587492 3818495 := bstep (se 1 (by rfl) ⟨2863871, by rfl⟩ : syracuseStep 3818495 = 5727743) B5727743
theorem B4523195 : Blo 1587492 4523195 := bstep (se 1 (by rfl) ⟨3392396, by rfl⟩ : syracuseStep 4523195 = 6784793) B6784793
theorem B18351323 : Blo 1587492 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B1787647 : Blo 1587492 1787647 := bstep (se 1 (by rfl) ⟨1340735, by rfl⟩ : syracuseStep 1787647 = 2681471) B2681471
theorem B12068837 : Blo 1587492 12068837 := bstep (se 4 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 12068837 = 2262907) B2262907
theorem B7637159 : Blo 1587492 7637159 := bstep (se 1 (by rfl) ⟨5727869, by rfl⟩ : syracuseStep 7637159 = 11455739) B11455739
theorem B5360255 : Blo 1587492 5360255 := bstep (se 1 (by rfl) ⟨4020191, by rfl⟩ : syracuseStep 5360255 = 8040383) B8040383
theorem B5360633 : Blo 1587492 5360633 := bstep (se 2 (by rfl) ⟨2010237, by rfl⟩ : syracuseStep 5360633 = 4020475) B4020475
theorem B5361119 : Blo 1587492 5361119 := bstep (se 1 (by rfl) ⟨4020839, by rfl⟩ : syracuseStep 5361119 = 8041679) B8041679
theorem B5361335 : Blo 1587492 5361335 := bstep (se 1 (by rfl) ⟨4021001, by rfl⟩ : syracuseStep 5361335 = 8042003) B8042003
theorem B17174267 : Blo 1587492 17174267 := bstep (se 1 (by rfl) ⟨12880700, by rfl⟩ : syracuseStep 17174267 = 25761401) B25761401
theorem B12873761 : Blo 1587492 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B6787151 : Blo 1587492 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B25760879 : Blo 1587492 25760879 := bstep (se 1 (by rfl) ⟨19320659, by rfl⟩ : syracuseStep 25760879 = 38641319) B38641319
theorem B2381279 : Blo 1587492 2381279 := bstep (se 1 (by rfl) ⟨1785959, by rfl⟩ : syracuseStep 2381279 = 3571919) B3571919
theorem B2381375 : Blo 1587492 2381375 := bstep (se 1 (by rfl) ⟨1786031, by rfl⟩ : syracuseStep 2381375 = 3572063) B3572063
theorem B15275627 : Blo 1587492 15275627 := bstep (se 1 (by rfl) ⟨11456720, by rfl⟩ : syracuseStep 15275627 = 22913441) B22913441
theorem B3823399 : Blo 1587492 3823399 := bstep (se 1 (by rfl) ⟨2867549, by rfl⟩ : syracuseStep 3823399 = 5735099) B5735099
theorem B1587647 : Blo 1587492 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B9042425 : Blo 1587492 9042425 := bstep (se 2 (by rfl) ⟨3390909, by rfl⟩ : syracuseStep 9042425 = 6781819) B6781819
theorem B46447187 : Blo 1587492 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B18086489 : Blo 1587492 18086489 := bstep (se 2 (by rfl) ⟨6782433, by rfl⟩ : syracuseStep 18086489 = 13564867) B13564867
theorem B4520735 : Blo 1587492 4520735 := bstep (se 1 (by rfl) ⟨3390551, by rfl⟩ : syracuseStep 4520735 = 6781103) B6781103
theorem B8043623 : Blo 1587492 8043623 := bstep (se 1 (by rfl) ⟨6032717, by rfl⟩ : syracuseStep 8043623 = 12065435) B12065435
theorem B2383103 : Blo 1587492 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B6110471 : Blo 1587492 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B4521577 : Blo 1587492 4521577 := bstep (se 2 (by rfl) ⟨1695591, by rfl⟩ : syracuseStep 4521577 = 3391183) B3391183
theorem B4022095 : Blo 1587492 4022095 := bstep (se 1 (by rfl) ⟨3016571, by rfl⟩ : syracuseStep 4022095 = 6033143) B6033143
theorem B4292443 : Blo 1587492 4292443 := bstep (se 1 (by rfl) ⟨3219332, by rfl⟩ : syracuseStep 4292443 = 6438665) B6438665
theorem B10174319 : Blo 1587492 10174319 := bstep (se 1 (by rfl) ⟨7630739, by rfl⟩ : syracuseStep 10174319 = 15261479) B15261479
theorem B8372791 : Blo 1587492 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B3015463 : Blo 1587492 3015463 := bstep (se 1 (by rfl) ⟨2261597, by rfl⟩ : syracuseStep 3015463 = 4523195) B4523195
theorem B495436661 : Blo 1587492 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B10183751 : Blo 1587492 10183751 := bstep (se 1 (by rfl) ⟨7637813, by rfl⟩ : syracuseStep 10183751 = 15275627) B15275627
theorem B8045891 : Blo 1587492 8045891 := bstep (se 1 (by rfl) ⟨6034418, by rfl⟩ : syracuseStep 8045891 = 12068837) B12068837
theorem B3573503 : Blo 1587492 3573503 := bstep (se 1 (by rfl) ⟨2680127, by rfl⟩ : syracuseStep 3573503 = 5360255) B5360255
theorem B3573755 : Blo 1587492 3573755 := bstep (se 1 (by rfl) ⟨2680316, by rfl⟩ : syracuseStep 3573755 = 5360633) B5360633
theorem B4073647 : Blo 1587492 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B3574079 : Blo 1587492 3574079 := bstep (se 1 (by rfl) ⟨2680559, by rfl⟩ : syracuseStep 3574079 = 5361119) B5361119
theorem B5097865 : Blo 1587492 5097865 := bstep (se 2 (by rfl) ⟨1911699, by rfl⟩ : syracuseStep 5097865 = 3823399) B3823399
theorem B3574223 : Blo 1587492 3574223 := bstep (se 1 (by rfl) ⟨2680667, by rfl⟩ : syracuseStep 3574223 = 5361335) B5361335
theorem B4524767 : Blo 1587492 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B2681579 : Blo 1587492 2681579 := bstep (se 1 (by rfl) ⟨2011184, by rfl⟩ : syracuseStep 2681579 = 4022369) B4022369
theorem B17173919 : Blo 1587492 17173919 := bstep (se 1 (by rfl) ⟨12880439, by rfl⟩ : syracuseStep 17173919 = 25760879) B25760879
theorem B12234215 : Blo 1587492 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B5091439 : Blo 1587492 5091439 := bstep (se 1 (by rfl) ⟨3818579, by rfl⟩ : syracuseStep 5091439 = 7637159) B7637159
theorem B5362415 : Blo 1587492 5362415 := bstep (se 1 (by rfl) ⟨4021811, by rfl⟩ : syracuseStep 5362415 = 8043623) B8043623
theorem B5362793 : Blo 1587492 5362793 := bstep (se 2 (by rfl) ⟨2011047, by rfl⟩ : syracuseStep 5362793 = 4022095) B4022095
theorem B5723257 : Blo 1587492 5723257 := bstep (se 2 (by rfl) ⟨2146221, by rfl⟩ : syracuseStep 5723257 = 4292443) B4292443
theorem B11449511 : Blo 1587492 11449511 := bstep (se 1 (by rfl) ⟨8587133, by rfl⟩ : syracuseStep 11449511 = 17174267) B17174267
theorem B8582507 : Blo 1587492 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B6444697 : Blo 1587492 6444697 := bstep (se 2 (by rfl) ⟨2416761, by rfl⟩ : syracuseStep 6444697 = 4833523) B4833523
theorem B2545643 : Blo 1587492 2545643 := bstep (se 1 (by rfl) ⟨1909232, by rfl⟩ : syracuseStep 2545643 = 3818465) B3818465
theorem B2545663 : Blo 1587492 2545663 := bstep (se 1 (by rfl) ⟨1909247, by rfl⟩ : syracuseStep 2545663 = 3818495) B3818495
theorem B1587519 : Blo 1587492 1587519 := bstep (se 1 (by rfl) ⟨1190639, by rfl⟩ : syracuseStep 1587519 = 2381279) B2381279
theorem B1587583 : Blo 1587492 1587583 := bstep (se 1 (by rfl) ⟨1190687, by rfl⟩ : syracuseStep 1587583 = 2381375) B2381375
theorem B6028283 : Blo 1587492 6028283 := bstep (se 1 (by rfl) ⟨4521212, by rfl⟩ : syracuseStep 6028283 = 9042425) B9042425
theorem B12057659 : Blo 1587492 12057659 := bstep (se 1 (by rfl) ⟨9043244, by rfl⟩ : syracuseStep 12057659 = 18086489) B18086489
theorem B3013823 : Blo 1587492 3013823 := bstep (se 1 (by rfl) ⟨2260367, by rfl⟩ : syracuseStep 3013823 = 4520735) B4520735
theorem B6028769 : Blo 1587492 6028769 := bstep (se 2 (by rfl) ⟨2260788, by rfl⟩ : syracuseStep 6028769 = 4521577) B4521577
theorem B1588735 : Blo 1587492 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B2383529 : Blo 1587492 2383529 := bstep (se 2 (by rfl) ⟨893823, by rfl⟩ : syracuseStep 2383529 = 1787647) B1787647
theorem B6782879 : Blo 1587492 6782879 := bstep (se 1 (by rfl) ⟨5087159, by rfl⟩ : syracuseStep 6782879 = 10174319) B10174319
theorem B5431529 : Blo 1587492 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B44654885 : Blo 1587492 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B1697095 : Blo 1587492 1697095 := bstep (se 1 (by rfl) ⟨1272821, by rfl⟩ : syracuseStep 1697095 = 2545643) B2545643
theorem B3016511 : Blo 1587492 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B1787719 : Blo 1587492 1787719 := bstep (se 1 (by rfl) ⟨1340789, by rfl⟩ : syracuseStep 1787719 = 2681579) B2681579
theorem B8038439 : Blo 1587492 8038439 := bstep (se 1 (by rfl) ⟨6028829, by rfl⟩ : syracuseStep 8038439 = 12057659) B12057659
theorem B2009215 : Blo 1587492 2009215 := bstep (se 1 (by rfl) ⟨1506911, by rfl⟩ : syracuseStep 2009215 = 3013823) B3013823
theorem B3394217 : Blo 1587492 3394217 := bstep (se 2 (by rfl) ⟨1272831, by rfl⟩ : syracuseStep 3394217 = 2545663) B2545663
theorem B3574943 : Blo 1587492 3574943 := bstep (se 1 (by rfl) ⟨2681207, by rfl⟩ : syracuseStep 3574943 = 5362415) B5362415
theorem B3575195 : Blo 1587492 3575195 := bstep (se 1 (by rfl) ⟨2681396, by rfl⟩ : syracuseStep 3575195 = 5362793) B5362793
theorem B5721671 : Blo 1587492 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B7631009 : Blo 1587492 7631009 := bstep (se 2 (by rfl) ⟨2861628, by rfl⟩ : syracuseStep 7631009 = 5723257) B5723257
theorem B4018855 : Blo 1587492 4018855 := bstep (se 1 (by rfl) ⟨3014141, by rfl⟩ : syracuseStep 4018855 = 6028283) B6028283
theorem B11449279 : Blo 1587492 11449279 := bstep (se 1 (by rfl) ⟨8586959, by rfl⟩ : syracuseStep 11449279 = 17173919) B17173919
theorem B4019179 : Blo 1587492 4019179 := bstep (se 1 (by rfl) ⟨3014384, by rfl⟩ : syracuseStep 4019179 = 6028769) B6028769
theorem B8156143 : Blo 1587492 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B6788585 : Blo 1587492 6788585 := bstep (se 2 (by rfl) ⟨2545719, by rfl⟩ : syracuseStep 6788585 = 5091439) B5091439
theorem B6797153 : Blo 1587492 6797153 := bstep (se 2 (by rfl) ⟨2548932, by rfl⟩ : syracuseStep 6797153 = 5097865) B5097865
theorem B330291107 : Blo 1587492 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B6789167 : Blo 1587492 6789167 := bstep (se 1 (by rfl) ⟨5091875, by rfl⟩ : syracuseStep 6789167 = 10183751) B10183751
theorem B7633007 : Blo 1587492 7633007 := bstep (se 1 (by rfl) ⟨5724755, by rfl⟩ : syracuseStep 7633007 = 11449511) B11449511
theorem B5363927 : Blo 1587492 5363927 := bstep (se 1 (by rfl) ⟨4022945, by rfl⟩ : syracuseStep 5363927 = 8045891) B8045891
theorem B4020617 : Blo 1587492 4020617 := bstep (se 2 (by rfl) ⟨1507731, by rfl⟩ : syracuseStep 4020617 = 3015463) B3015463
theorem B2382335 : Blo 1587492 2382335 := bstep (se 1 (by rfl) ⟨1786751, by rfl⟩ : syracuseStep 2382335 = 3573503) B3573503
theorem B2382503 : Blo 1587492 2382503 := bstep (se 1 (by rfl) ⟨1786877, by rfl⟩ : syracuseStep 2382503 = 3573755) B3573755
theorem B2382719 : Blo 1587492 2382719 := bstep (se 1 (by rfl) ⟨1787039, by rfl⟩ : syracuseStep 2382719 = 3574079) B3574079
theorem B2382815 : Blo 1587492 2382815 := bstep (se 1 (by rfl) ⟨1787111, by rfl⟩ : syracuseStep 2382815 = 3574223) B3574223
theorem B8592929 : Blo 1587492 8592929 := bstep (se 2 (by rfl) ⟨3222348, by rfl⟩ : syracuseStep 8592929 = 6444697) B6444697
theorem B1589019 : Blo 1587492 1589019 := bstep (se 1 (by rfl) ⟨1191764, by rfl⟩ : syracuseStep 1589019 = 2383529) B2383529
theorem B4521919 : Blo 1587492 4521919 := bstep (se 1 (by rfl) ⟨3391439, by rfl⟩ : syracuseStep 4521919 = 6782879) B6782879
theorem B5087339 : Blo 1587492 5087339 := bstep (se 1 (by rfl) ⟨3815504, by rfl⟩ : syracuseStep 5087339 = 7631009) B7631009
theorem B3621019 : Blo 1587492 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B2678953 : Blo 1587492 2678953 := bstep (se 2 (by rfl) ⟨1004607, by rfl⟩ : syracuseStep 2678953 = 2009215) B2009215
theorem B29769923 : Blo 1587492 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B5358473 : Blo 1587492 5358473 := bstep (se 2 (by rfl) ⟨2009427, by rfl⟩ : syracuseStep 5358473 = 4018855) B4018855
theorem B220194071 : Blo 1587492 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B5358905 : Blo 1587492 5358905 := bstep (se 2 (by rfl) ⟨2009589, by rfl⟩ : syracuseStep 5358905 = 4019179) B4019179
theorem B5358959 : Blo 1587492 5358959 := bstep (se 1 (by rfl) ⟨4019219, by rfl⟩ : syracuseStep 5358959 = 8038439) B8038439
theorem B5088671 : Blo 1587492 5088671 := bstep (se 1 (by rfl) ⟨3816503, by rfl⟩ : syracuseStep 5088671 = 7633007) B7633007
theorem B2680411 : Blo 1587492 2680411 := bstep (se 1 (by rfl) ⟨2010308, by rfl⟩ : syracuseStep 2680411 = 4020617) B4020617
theorem B2262811 : Blo 1587492 2262811 := bstep (se 1 (by rfl) ⟨1697108, by rfl⟩ : syracuseStep 2262811 = 3394217) B3394217
theorem B5728619 : Blo 1587492 5728619 := bstep (se 1 (by rfl) ⟨4296464, by rfl⟩ : syracuseStep 5728619 = 8592929) B8592929
theorem B4525723 : Blo 1587492 4525723 := bstep (se 1 (by rfl) ⟨3394292, by rfl⟩ : syracuseStep 4525723 = 6788585) B6788585
theorem B2011007 : Blo 1587492 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B15265705 : Blo 1587492 15265705 := bstep (se 2 (by rfl) ⟨5724639, by rfl⟩ : syracuseStep 15265705 = 11449279) B11449279
theorem B4526111 : Blo 1587492 4526111 := bstep (se 1 (by rfl) ⟨3394583, by rfl⟩ : syracuseStep 4526111 = 6789167) B6789167
theorem B3575951 : Blo 1587492 3575951 := bstep (se 1 (by rfl) ⟨2681963, by rfl⟩ : syracuseStep 3575951 = 5363927) B5363927
theorem B18125741 : Blo 1587492 18125741 := bstep (se 3 (by rfl) ⟨3398576, by rfl⟩ : syracuseStep 18125741 = 6797153) B6797153
theorem B3814447 : Blo 1587492 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B1588223 : Blo 1587492 1588223 := bstep (se 1 (by rfl) ⟨1191167, by rfl⟩ : syracuseStep 1588223 = 2382335) B2382335
theorem B9051173 : Blo 1587492 9051173 := bstep (se 4 (by rfl) ⟨848547, by rfl⟩ : syracuseStep 9051173 = 1697095) B1697095
theorem B1588335 : Blo 1587492 1588335 := bstep (se 1 (by rfl) ⟨1191251, by rfl⟩ : syracuseStep 1588335 = 2382503) B2382503
theorem B1588479 : Blo 1587492 1588479 := bstep (se 1 (by rfl) ⟨1191359, by rfl⟩ : syracuseStep 1588479 = 2382719) B2382719
theorem B1588543 : Blo 1587492 1588543 := bstep (se 1 (by rfl) ⟨1191407, by rfl⟩ : syracuseStep 1588543 = 2382815) B2382815
theorem B2383295 : Blo 1587492 2383295 := bstep (se 1 (by rfl) ⟨1787471, by rfl⟩ : syracuseStep 2383295 = 3574943) B3574943
theorem B2383463 : Blo 1587492 2383463 := bstep (se 1 (by rfl) ⟨1787597, by rfl⟩ : syracuseStep 2383463 = 3575195) B3575195
theorem B2383625 : Blo 1587492 2383625 := bstep (se 2 (by rfl) ⟨893859, by rfl⟩ : syracuseStep 2383625 = 1787719) B1787719
theorem B43499429 : Blo 1587492 43499429 := bstep (se 4 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 43499429 = 8156143) B8156143
theorem B6029225 : Blo 1587492 6029225 := bstep (se 2 (by rfl) ⟨2260959, by rfl⟩ : syracuseStep 6029225 = 4521919) B4521919
theorem B3391559 : Blo 1587492 3391559 := bstep (se 1 (by rfl) ⟨2543669, by rfl⟩ : syracuseStep 3391559 = 5087339) B5087339
theorem B2383967 : Blo 1587492 2383967 := bstep (se 1 (by rfl) ⟨1787975, by rfl⟩ : syracuseStep 2383967 = 3575951) B3575951
theorem B3571937 : Blo 1587492 3571937 := bstep (se 2 (by rfl) ⟨1339476, by rfl⟩ : syracuseStep 3571937 = 2678953) B2678953
theorem B3572315 : Blo 1587492 3572315 := bstep (se 1 (by rfl) ⟨2679236, by rfl⟩ : syracuseStep 3572315 = 5358473) B5358473
theorem B12083827 : Blo 1587492 12083827 := bstep (se 1 (by rfl) ⟨9062870, by rfl⟩ : syracuseStep 12083827 = 18125741) B18125741
theorem B3572603 : Blo 1587492 3572603 := bstep (se 1 (by rfl) ⟨2679452, by rfl⟩ : syracuseStep 3572603 = 5358905) B5358905
theorem B3572639 : Blo 1587492 3572639 := bstep (se 1 (by rfl) ⟨2679479, by rfl⟩ : syracuseStep 3572639 = 5358959) B5358959
theorem B3392447 : Blo 1587492 3392447 := bstep (se 1 (by rfl) ⟨2544335, by rfl⟩ : syracuseStep 3392447 = 5088671) B5088671
theorem B3819079 : Blo 1587492 3819079 := bstep (se 1 (by rfl) ⟨2864309, by rfl⟩ : syracuseStep 3819079 = 5728619) B5728619
theorem B3573881 : Blo 1587492 3573881 := bstep (se 2 (by rfl) ⟨1340205, by rfl⟩ : syracuseStep 3573881 = 2680411) B2680411
theorem B3017081 : Blo 1587492 3017081 := bstep (se 2 (by rfl) ⟨1131405, by rfl⟩ : syracuseStep 3017081 = 2262811) B2262811
theorem B3017407 : Blo 1587492 3017407 := bstep (se 1 (by rfl) ⟨2263055, by rfl⟩ : syracuseStep 3017407 = 4526111) B4526111
theorem B4828025 : Blo 1587492 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B146796047 : Blo 1587492 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B6034115 : Blo 1587492 6034115 := bstep (se 1 (by rfl) ⟨4525586, by rfl⟩ : syracuseStep 6034115 = 9051173) B9051173
theorem B6034297 : Blo 1587492 6034297 := bstep (se 2 (by rfl) ⟨2262861, by rfl⟩ : syracuseStep 6034297 = 4525723) B4525723
theorem B5362685 : Blo 1587492 5362685 := bstep (se 3 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 5362685 = 2011007) B2011007
theorem B20354273 : Blo 1587492 20354273 := bstep (se 2 (by rfl) ⟨7632852, by rfl⟩ : syracuseStep 20354273 = 15265705) B15265705
theorem B4019483 : Blo 1587492 4019483 := bstep (se 1 (by rfl) ⟨3014612, by rfl⟩ : syracuseStep 4019483 = 6029225) B6029225
theorem B19846615 : Blo 1587492 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B5085929 : Blo 1587492 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B1588863 : Blo 1587492 1588863 := bstep (se 1 (by rfl) ⟨1191647, by rfl⟩ : syracuseStep 1588863 = 2383295) B2383295
theorem B1588975 : Blo 1587492 1588975 := bstep (se 1 (by rfl) ⟨1191731, by rfl⟩ : syracuseStep 1588975 = 2383463) B2383463
theorem B1589083 : Blo 1587492 1589083 := bstep (se 1 (by rfl) ⟨1191812, by rfl⟩ : syracuseStep 1589083 = 2383625) B2383625
theorem B28999619 : Blo 1587492 28999619 := bstep (se 1 (by rfl) ⟨21749714, by rfl⟩ : syracuseStep 28999619 = 43499429) B43499429
theorem B2261039 : Blo 1587492 2261039 := bstep (se 1 (by rfl) ⟨1695779, by rfl⟩ : syracuseStep 2261039 = 3391559) B3391559
theorem B1589311 : Blo 1587492 1589311 := bstep (se 1 (by rfl) ⟨1191983, by rfl⟩ : syracuseStep 1589311 = 2383967) B2383967
theorem B4022743 : Blo 1587492 4022743 := bstep (se 1 (by rfl) ⟨3017057, by rfl⟩ : syracuseStep 4022743 = 6034115) B6034115
theorem B2679655 : Blo 1587492 2679655 := bstep (se 1 (by rfl) ⟨2009741, by rfl⟩ : syracuseStep 2679655 = 4019483) B4019483
theorem B4023209 : Blo 1587492 4023209 := bstep (se 2 (by rfl) ⟨1508703, by rfl⟩ : syracuseStep 4023209 = 3017407) B3017407
theorem B8045729 : Blo 1587492 8045729 := bstep (se 2 (by rfl) ⟨3017148, by rfl⟩ : syracuseStep 8045729 = 6034297) B6034297
theorem B26462153 : Blo 1587492 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B97864031 : Blo 1587492 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B9046525 : Blo 1587492 9046525 := bstep (se 3 (by rfl) ⟨1696223, by rfl⟩ : syracuseStep 9046525 = 3392447) B3392447
theorem B20368421 : Blo 1587492 20368421 := bstep (se 4 (by rfl) ⟨1909539, by rfl⟩ : syracuseStep 20368421 = 3819079) B3819079
theorem B3575123 : Blo 1587492 3575123 := bstep (se 1 (by rfl) ⟨2681342, by rfl⟩ : syracuseStep 3575123 = 5362685) B5362685
theorem B13569515 : Blo 1587492 13569515 := bstep (se 1 (by rfl) ⟨10177136, by rfl⟩ : syracuseStep 13569515 = 20354273) B20354273
theorem B2011387 : Blo 1587492 2011387 := bstep (se 1 (by rfl) ⟨1508540, by rfl⟩ : syracuseStep 2011387 = 3017081) B3017081
theorem B13562477 : Blo 1587492 13562477 := bstep (se 3 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 13562477 = 5085929) B5085929
theorem B12874733 : Blo 1587492 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B2381291 : Blo 1587492 2381291 := bstep (se 1 (by rfl) ⟨1785968, by rfl⟩ : syracuseStep 2381291 = 3571937) B3571937
theorem B2381543 : Blo 1587492 2381543 := bstep (se 1 (by rfl) ⟨1786157, by rfl⟩ : syracuseStep 2381543 = 3572315) B3572315
theorem B2381735 : Blo 1587492 2381735 := bstep (se 1 (by rfl) ⟨1786301, by rfl⟩ : syracuseStep 2381735 = 3572603) B3572603
theorem B2381759 : Blo 1587492 2381759 := bstep (se 1 (by rfl) ⟨1786319, by rfl⟩ : syracuseStep 2381759 = 3572639) B3572639
theorem B16111769 : Blo 1587492 16111769 := bstep (se 2 (by rfl) ⟨6041913, by rfl⟩ : syracuseStep 16111769 = 12083827) B12083827
theorem B2382587 : Blo 1587492 2382587 := bstep (se 1 (by rfl) ⟨1786940, by rfl⟩ : syracuseStep 2382587 = 3573881) B3573881
theorem B19333079 : Blo 1587492 19333079 := bstep (se 1 (by rfl) ⟨14499809, by rfl⟩ : syracuseStep 19333079 = 28999619) B28999619
theorem B6029437 : Blo 1587492 6029437 := bstep (se 3 (by rfl) ⟨1130519, by rfl⟩ : syracuseStep 6029437 = 2261039) B2261039
theorem B3572873 : Blo 1587492 3572873 := bstep (se 2 (by rfl) ⟨1339827, by rfl⟩ : syracuseStep 3572873 = 2679655) B2679655
theorem B65242687 : Blo 1587492 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B9046343 : Blo 1587492 9046343 := bstep (se 1 (by rfl) ⟨6784757, by rfl⟩ : syracuseStep 9046343 = 13569515) B13569515
theorem B12888719 : Blo 1587492 12888719 := bstep (se 1 (by rfl) ⟨9666539, by rfl⟩ : syracuseStep 12888719 = 19333079) B19333079
theorem B2681849 : Blo 1587492 2681849 := bstep (se 2 (by rfl) ⟨1005693, by rfl⟩ : syracuseStep 2681849 = 2011387) B2011387
theorem B2682139 : Blo 1587492 2682139 := bstep (se 1 (by rfl) ⟨2011604, by rfl⟩ : syracuseStep 2682139 = 4023209) B4023209
theorem B12062033 : Blo 1587492 12062033 := bstep (se 2 (by rfl) ⟨4523262, by rfl⟩ : syracuseStep 12062033 = 9046525) B9046525
theorem B13578947 : Blo 1587492 13578947 := bstep (se 1 (by rfl) ⟨10184210, by rfl⟩ : syracuseStep 13578947 = 20368421) B20368421
theorem B42964717 : Blo 1587492 42964717 := bstep (se 3 (by rfl) ⟨8055884, by rfl⟩ : syracuseStep 42964717 = 16111769) B16111769
theorem B9041651 : Blo 1587492 9041651 := bstep (se 1 (by rfl) ⟨6781238, by rfl⟩ : syracuseStep 9041651 = 13562477) B13562477
theorem B5363657 : Blo 1587492 5363657 := bstep (se 2 (by rfl) ⟨2011371, by rfl⟩ : syracuseStep 5363657 = 4022743) B4022743
theorem B8583155 : Blo 1587492 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B5363819 : Blo 1587492 5363819 := bstep (se 1 (by rfl) ⟨4022864, by rfl⟩ : syracuseStep 5363819 = 8045729) B8045729
theorem B1587527 : Blo 1587492 1587527 := bstep (se 1 (by rfl) ⟨1190645, by rfl⟩ : syracuseStep 1587527 = 2381291) B2381291
theorem B1587695 : Blo 1587492 1587695 := bstep (se 1 (by rfl) ⟨1190771, by rfl⟩ : syracuseStep 1587695 = 2381543) B2381543
theorem B1587823 : Blo 1587492 1587823 := bstep (se 1 (by rfl) ⟨1190867, by rfl⟩ : syracuseStep 1587823 = 2381735) B2381735
theorem B1587839 : Blo 1587492 1587839 := bstep (se 1 (by rfl) ⟨1190879, by rfl⟩ : syracuseStep 1587839 = 2381759) B2381759
theorem B1588391 : Blo 1587492 1588391 := bstep (se 1 (by rfl) ⟨1191293, by rfl⟩ : syracuseStep 1588391 = 2382587) B2382587
theorem B2383415 : Blo 1587492 2383415 := bstep (se 1 (by rfl) ⟨1787561, by rfl⟩ : syracuseStep 2383415 = 3575123) B3575123
theorem B70565741 : Blo 1587492 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B9052631 : Blo 1587492 9052631 := bstep (se 1 (by rfl) ⟨6789473, by rfl⟩ : syracuseStep 9052631 = 13578947) B13578947
theorem B6030895 : Blo 1587492 6030895 := bstep (se 1 (by rfl) ⟨4523171, by rfl⟩ : syracuseStep 6030895 = 9046343) B9046343
theorem B1787899 : Blo 1587492 1787899 := bstep (se 1 (by rfl) ⟨1340924, by rfl⟩ : syracuseStep 1787899 = 2681849) B2681849
theorem B8039249 : Blo 1587492 8039249 := bstep (se 2 (by rfl) ⟨3014718, by rfl⟩ : syracuseStep 8039249 = 6029437) B6029437
theorem B3575771 : Blo 1587492 3575771 := bstep (se 1 (by rfl) ⟨2681828, by rfl⟩ : syracuseStep 3575771 = 5363657) B5363657
theorem B5722103 : Blo 1587492 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B3575879 : Blo 1587492 3575879 := bstep (se 1 (by rfl) ⟨2681909, by rfl⟩ : syracuseStep 3575879 = 5363819) B5363819
theorem B3576185 : Blo 1587492 3576185 := bstep (se 2 (by rfl) ⟨1341069, by rfl⟩ : syracuseStep 3576185 = 2682139) B2682139
theorem B8041355 : Blo 1587492 8041355 := bstep (se 1 (by rfl) ⟨6031016, by rfl⟩ : syracuseStep 8041355 = 12062033) B12062033
theorem B47043827 : Blo 1587492 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B2381915 : Blo 1587492 2381915 := bstep (se 1 (by rfl) ⟨1786436, by rfl⟩ : syracuseStep 2381915 = 3572873) B3572873
theorem B6027767 : Blo 1587492 6027767 := bstep (se 1 (by rfl) ⟨4520825, by rfl⟩ : syracuseStep 6027767 = 9041651) B9041651
theorem B8592479 : Blo 1587492 8592479 := bstep (se 1 (by rfl) ⟨6444359, by rfl⟩ : syracuseStep 8592479 = 12888719) B12888719
theorem B86990249 : Blo 1587492 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B57286289 : Blo 1587492 57286289 := bstep (se 2 (by rfl) ⟨21482358, by rfl⟩ : syracuseStep 57286289 = 42964717) B42964717
theorem B1588943 : Blo 1587492 1588943 := bstep (se 1 (by rfl) ⟨1191707, by rfl⟩ : syracuseStep 1588943 = 2383415) B2383415
theorem B2383919 : Blo 1587492 2383919 := bstep (se 1 (by rfl) ⟨1787939, by rfl⟩ : syracuseStep 2383919 = 3575879) B3575879
theorem B2384123 : Blo 1587492 2384123 := bstep (se 1 (by rfl) ⟨1788092, by rfl⟩ : syracuseStep 2384123 = 3576185) B3576185
theorem B2383865 : Blo 1587492 2383865 := bstep (se 2 (by rfl) ⟨893949, by rfl⟩ : syracuseStep 2383865 = 1787899) B1787899
theorem B5359499 : Blo 1587492 5359499 := bstep (se 1 (by rfl) ⟨4019624, by rfl⟩ : syracuseStep 5359499 = 8039249) B8039249
theorem B5728319 : Blo 1587492 5728319 := bstep (se 1 (by rfl) ⟨4296239, by rfl⟩ : syracuseStep 5728319 = 8592479) B8592479
theorem B57993499 : Blo 1587492 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B5360903 : Blo 1587492 5360903 := bstep (se 1 (by rfl) ⟨4020677, by rfl⟩ : syracuseStep 5360903 = 8041355) B8041355
theorem B31362551 : Blo 1587492 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B4018511 : Blo 1587492 4018511 := bstep (se 1 (by rfl) ⟨3013883, by rfl⟩ : syracuseStep 4018511 = 6027767) B6027767
theorem B8041193 : Blo 1587492 8041193 := bstep (se 2 (by rfl) ⟨3015447, by rfl⟩ : syracuseStep 8041193 = 6030895) B6030895
theorem B15258941 : Blo 1587492 15258941 := bstep (se 3 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 15258941 = 5722103) B5722103
theorem B6035087 : Blo 1587492 6035087 := bstep (se 1 (by rfl) ⟨4526315, by rfl⟩ : syracuseStep 6035087 = 9052631) B9052631
theorem B1587943 : Blo 1587492 1587943 := bstep (se 1 (by rfl) ⟨1190957, by rfl⟩ : syracuseStep 1587943 = 2381915) B2381915
theorem B152763437 : Blo 1587492 152763437 := bstep (se 3 (by rfl) ⟨28643144, by rfl⟩ : syracuseStep 152763437 = 57286289) B57286289
theorem B2383847 : Blo 1587492 2383847 := bstep (se 1 (by rfl) ⟨1787885, by rfl⟩ : syracuseStep 2383847 = 3575771) B3575771
theorem B1589279 : Blo 1587492 1589279 := bstep (se 1 (by rfl) ⟨1191959, by rfl⟩ : syracuseStep 1589279 = 2383919) B2383919
theorem B1589415 : Blo 1587492 1589415 := bstep (se 1 (by rfl) ⟨1192061, by rfl⟩ : syracuseStep 1589415 = 2384123) B2384123
theorem B2679007 : Blo 1587492 2679007 := bstep (se 1 (by rfl) ⟨2009255, by rfl⟩ : syracuseStep 2679007 = 4018511) B4018511
theorem B1589243 : Blo 1587492 1589243 := bstep (se 1 (by rfl) ⟨1191932, by rfl⟩ : syracuseStep 1589243 = 2383865) B2383865
theorem B4023391 : Blo 1587492 4023391 := bstep (se 1 (by rfl) ⟨3017543, by rfl⟩ : syracuseStep 4023391 = 6035087) B6035087
theorem B3572999 : Blo 1587492 3572999 := bstep (se 1 (by rfl) ⟨2679749, by rfl⟩ : syracuseStep 3572999 = 5359499) B5359499
theorem B3818879 : Blo 1587492 3818879 := bstep (se 1 (by rfl) ⟨2864159, by rfl⟩ : syracuseStep 3818879 = 5728319) B5728319
theorem B309298661 : Blo 1587492 309298661 := bstep (se 4 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 309298661 = 57993499) B57993499
theorem B3573935 : Blo 1587492 3573935 := bstep (se 1 (by rfl) ⟨2680451, by rfl⟩ : syracuseStep 3573935 = 5360903) B5360903
theorem B20908367 : Blo 1587492 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B5360795 : Blo 1587492 5360795 := bstep (se 1 (by rfl) ⟨4020596, by rfl⟩ : syracuseStep 5360795 = 8041193) B8041193
theorem B10172627 : Blo 1587492 10172627 := bstep (se 1 (by rfl) ⟨7629470, by rfl⟩ : syracuseStep 10172627 = 15258941) B15258941
theorem B101842291 : Blo 1587492 101842291 := bstep (se 1 (by rfl) ⟨76381718, by rfl⟩ : syracuseStep 101842291 = 152763437) B152763437
theorem B1589231 : Blo 1587492 1589231 := bstep (se 1 (by rfl) ⟨1191923, by rfl⟩ : syracuseStep 1589231 = 2383847) B2383847
theorem B3572009 : Blo 1587492 3572009 := bstep (se 2 (by rfl) ⟨1339503, by rfl⟩ : syracuseStep 3572009 = 2679007) B2679007
theorem B3573863 : Blo 1587492 3573863 := bstep (se 1 (by rfl) ⟨2680397, by rfl⟩ : syracuseStep 3573863 = 5360795) B5360795
theorem B13938911 : Blo 1587492 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B543158885 : Blo 1587492 543158885 := bstep (se 4 (by rfl) ⟨50921145, by rfl⟩ : syracuseStep 543158885 = 101842291) B101842291
theorem B2381999 : Blo 1587492 2381999 := bstep (se 1 (by rfl) ⟨1786499, by rfl⟩ : syracuseStep 2381999 = 3572999) B3572999
theorem B2545919 : Blo 1587492 2545919 := bstep (se 1 (by rfl) ⟨1909439, by rfl⟩ : syracuseStep 2545919 = 3818879) B3818879
theorem B206199107 : Blo 1587492 206199107 := bstep (se 1 (by rfl) ⟨154649330, by rfl⟩ : syracuseStep 206199107 = 309298661) B309298661
theorem B2382623 : Blo 1587492 2382623 := bstep (se 1 (by rfl) ⟨1786967, by rfl⟩ : syracuseStep 2382623 = 3573935) B3573935
theorem B5364521 : Blo 1587492 5364521 := bstep (se 2 (by rfl) ⟨2011695, by rfl⟩ : syracuseStep 5364521 = 4023391) B4023391
theorem B6781751 : Blo 1587492 6781751 := bstep (se 1 (by rfl) ⟨5086313, by rfl⟩ : syracuseStep 6781751 = 10172627) B10172627
theorem B1697279 : Blo 1587492 1697279 := bstep (se 1 (by rfl) ⟨1272959, by rfl⟩ : syracuseStep 1697279 = 2545919) B2545919
theorem B9292607 : Blo 1587492 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B362105923 : Blo 1587492 362105923 := bstep (se 1 (by rfl) ⟨271579442, by rfl⟩ : syracuseStep 362105923 = 543158885) B543158885
theorem B137466071 : Blo 1587492 137466071 := bstep (se 1 (by rfl) ⟨103099553, by rfl⟩ : syracuseStep 137466071 = 206199107) B206199107
theorem B3576347 : Blo 1587492 3576347 := bstep (se 1 (by rfl) ⟨2682260, by rfl⟩ : syracuseStep 3576347 = 5364521) B5364521
theorem B2381339 : Blo 1587492 2381339 := bstep (se 1 (by rfl) ⟨1786004, by rfl⟩ : syracuseStep 2381339 = 3572009) B3572009
theorem B2382575 : Blo 1587492 2382575 := bstep (se 1 (by rfl) ⟨1786931, by rfl⟩ : syracuseStep 2382575 = 3573863) B3573863
theorem B1587999 : Blo 1587492 1587999 := bstep (se 1 (by rfl) ⟨1190999, by rfl⟩ : syracuseStep 1587999 = 2381999) B2381999
theorem B1588415 : Blo 1587492 1588415 := bstep (se 1 (by rfl) ⟨1191311, by rfl⟩ : syracuseStep 1588415 = 2382623) B2382623
theorem B4521167 : Blo 1587492 4521167 := bstep (se 1 (by rfl) ⟨3390875, by rfl⟩ : syracuseStep 4521167 = 6781751) B6781751
theorem B91644047 : Blo 1587492 91644047 := bstep (se 1 (by rfl) ⟨68733035, by rfl⟩ : syracuseStep 91644047 = 137466071) B137466071
theorem B2384231 : Blo 1587492 2384231 := bstep (se 1 (by rfl) ⟨1788173, by rfl⟩ : syracuseStep 2384231 = 3576347) B3576347
theorem B6195071 : Blo 1587492 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B4526077 : Blo 1587492 4526077 := bstep (se 3 (by rfl) ⟨848639, by rfl⟩ : syracuseStep 4526077 = 1697279) B1697279
theorem B482807897 : Blo 1587492 482807897 := bstep (se 2 (by rfl) ⟨181052961, by rfl⟩ : syracuseStep 482807897 = 362105923) B362105923
theorem B1587559 : Blo 1587492 1587559 := bstep (se 1 (by rfl) ⟨1190669, by rfl⟩ : syracuseStep 1587559 = 2381339) B2381339
theorem B1588383 : Blo 1587492 1588383 := bstep (se 1 (by rfl) ⟨1191287, by rfl⟩ : syracuseStep 1588383 = 2382575) B2382575
theorem B3014111 : Blo 1587492 3014111 := bstep (se 1 (by rfl) ⟨2260583, by rfl⟩ : syracuseStep 3014111 = 4521167) B4521167
theorem B321871931 : Blo 1587492 321871931 := bstep (se 1 (by rfl) ⟨241403948, by rfl⟩ : syracuseStep 321871931 = 482807897) B482807897
theorem B61096031 : Blo 1587492 61096031 := bstep (se 1 (by rfl) ⟨45822023, by rfl⟩ : syracuseStep 61096031 = 91644047) B91644047
theorem B1589487 : Blo 1587492 1589487 := bstep (se 1 (by rfl) ⟨1192115, by rfl⟩ : syracuseStep 1589487 = 2384231) B2384231
theorem B8037629 : Blo 1587492 8037629 := bstep (se 3 (by rfl) ⟨1507055, by rfl⟩ : syracuseStep 8037629 = 3014111) B3014111
theorem B4130047 : Blo 1587492 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B6034769 : Blo 1587492 6034769 := bstep (se 2 (by rfl) ⟨2263038, by rfl⟩ : syracuseStep 6034769 = 4526077) B4526077
theorem B214581287 : Blo 1587492 214581287 := bstep (se 1 (by rfl) ⟨160935965, by rfl⟩ : syracuseStep 214581287 = 321871931) B321871931
theorem B40730687 : Blo 1587492 40730687 := bstep (se 1 (by rfl) ⟨30548015, by rfl⟩ : syracuseStep 40730687 = 61096031) B61096031
theorem B5358419 : Blo 1587492 5358419 := bstep (se 1 (by rfl) ⟨4018814, by rfl⟩ : syracuseStep 5358419 = 8037629) B8037629
theorem B4023179 : Blo 1587492 4023179 := bstep (se 1 (by rfl) ⟨3017384, by rfl⟩ : syracuseStep 4023179 = 6034769) B6034769
theorem B22026917 : Blo 1587492 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B3572279 : Blo 1587492 3572279 := bstep (se 1 (by rfl) ⟨2679209, by rfl⟩ : syracuseStep 3572279 = 5358419) B5358419
theorem B2682119 : Blo 1587492 2682119 := bstep (se 1 (by rfl) ⟨2011589, by rfl⟩ : syracuseStep 2682119 = 4023179) B4023179
theorem B14684611 : Blo 1587492 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B143054191 : Blo 1587492 143054191 := bstep (se 1 (by rfl) ⟨107290643, by rfl⟩ : syracuseStep 143054191 = 214581287) B214581287
theorem B27153791 : Blo 1587492 27153791 := bstep (se 1 (by rfl) ⟨20365343, by rfl⟩ : syracuseStep 27153791 = 40730687) B40730687
theorem B19579481 : Blo 1587492 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B1788079 : Blo 1587492 1788079 := bstep (se 1 (by rfl) ⟨1341059, by rfl⟩ : syracuseStep 1788079 = 2682119) B2682119
theorem B190738921 : Blo 1587492 190738921 := bstep (se 2 (by rfl) ⟨71527095, by rfl⟩ : syracuseStep 190738921 = 143054191) B143054191
theorem B2381519 : Blo 1587492 2381519 := bstep (se 1 (by rfl) ⟨1786139, by rfl⟩ : syracuseStep 2381519 = 3572279) B3572279
theorem B18102527 : Blo 1587492 18102527 := bstep (se 1 (by rfl) ⟨13576895, by rfl⟩ : syracuseStep 18102527 = 27153791) B27153791
theorem B2384105 : Blo 1587492 2384105 := bstep (se 2 (by rfl) ⟨894039, by rfl⟩ : syracuseStep 2384105 = 1788079) B1788079
theorem B12068351 : Blo 1587492 12068351 := bstep (se 1 (by rfl) ⟨9051263, by rfl⟩ : syracuseStep 12068351 = 18102527) B18102527
theorem B13052987 : Blo 1587492 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B254318561 : Blo 1587492 254318561 := bstep (se 2 (by rfl) ⟨95369460, by rfl⟩ : syracuseStep 254318561 = 190738921) B190738921
theorem B1587679 : Blo 1587492 1587679 := bstep (se 1 (by rfl) ⟨1190759, by rfl⟩ : syracuseStep 1587679 = 2381519) B2381519
theorem B1589403 : Blo 1587492 1589403 := bstep (se 1 (by rfl) ⟨1192052, by rfl⟩ : syracuseStep 1589403 = 2384105) B2384105
theorem B8045567 : Blo 1587492 8045567 := bstep (se 1 (by rfl) ⟨6034175, by rfl⟩ : syracuseStep 8045567 = 12068351) B12068351
theorem B8701991 : Blo 1587492 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B169545707 : Blo 1587492 169545707 := bstep (se 1 (by rfl) ⟨127159280, by rfl⟩ : syracuseStep 169545707 = 254318561) B254318561
theorem B5801327 : Blo 1587492 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B113030471 : Blo 1587492 113030471 := bstep (se 1 (by rfl) ⟨84772853, by rfl⟩ : syracuseStep 113030471 = 169545707) B169545707
theorem B5363711 : Blo 1587492 5363711 := bstep (se 1 (by rfl) ⟨4022783, by rfl⟩ : syracuseStep 5363711 = 8045567) B8045567
theorem B3867551 : Blo 1587492 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B75353647 : Blo 1587492 75353647 := bstep (se 1 (by rfl) ⟨56515235, by rfl⟩ : syracuseStep 75353647 = 113030471) B113030471
theorem B3575807 : Blo 1587492 3575807 := bstep (se 1 (by rfl) ⟨2681855, by rfl⟩ : syracuseStep 3575807 = 5363711) B5363711
theorem B2383871 : Blo 1587492 2383871 := bstep (se 1 (by rfl) ⟨1787903, by rfl⟩ : syracuseStep 2383871 = 3575807) B3575807
theorem B100471529 : Blo 1587492 100471529 := bstep (se 2 (by rfl) ⟨37676823, by rfl⟩ : syracuseStep 100471529 = 75353647) B75353647
theorem B41253877 : Blo 1587492 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B66981019 : Blo 1587492 66981019 := bstep (se 1 (by rfl) ⟨50235764, by rfl⟩ : syracuseStep 66981019 = 100471529) B100471529
theorem B55005169 : Blo 1587492 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B1589247 : Blo 1587492 1589247 := bstep (se 1 (by rfl) ⟨1191935, by rfl⟩ : syracuseStep 1589247 = 2383871) B2383871
theorem B73340225 : Blo 1587492 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B89308025 : Blo 1587492 89308025 := bstep (se 2 (by rfl) ⟨33490509, by rfl⟩ : syracuseStep 89308025 = 66981019) B66981019
theorem B48893483 : Blo 1587492 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B59538683 : Blo 1587492 59538683 := bstep (se 1 (by rfl) ⟨44654012, by rfl⟩ : syracuseStep 59538683 = 89308025) B89308025
theorem B158769821 : Blo 1587492 158769821 := bstep (se 3 (by rfl) ⟨29769341, by rfl⟩ : syracuseStep 158769821 = 59538683) B59538683
theorem B130382621 : Blo 1587492 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B86921747 : Blo 1587492 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B105846547 : Blo 1587492 105846547 := bstep (se 1 (by rfl) ⟨79384910, by rfl⟩ : syracuseStep 105846547 = 158769821) B158769821
theorem B141128729 : Blo 1587492 141128729 := bstep (se 2 (by rfl) ⟨52923273, by rfl⟩ : syracuseStep 141128729 = 105846547) B105846547
theorem B57947831 : Blo 1587492 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B94085819 : Blo 1587492 94085819 := bstep (se 1 (by rfl) ⟨70564364, by rfl⟩ : syracuseStep 94085819 = 141128729) B141128729
theorem B38631887 : Blo 1587492 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B62723879 : Blo 1587492 62723879 := bstep (se 1 (by rfl) ⟨47042909, by rfl⟩ : syracuseStep 62723879 = 94085819) B94085819
theorem B25754591 : Blo 1587492 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B41815919 : Blo 1587492 41815919 := bstep (se 1 (by rfl) ⟨31361939, by rfl⟩ : syracuseStep 41815919 = 62723879) B62723879
theorem B17169727 : Blo 1587492 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B22892969 : Blo 1587492 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B27877279 : Blo 1587492 27877279 := bstep (se 1 (by rfl) ⟨20907959, by rfl⟩ : syracuseStep 27877279 = 41815919) B41815919
theorem B15261979 : Blo 1587492 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B37169705 : Blo 1587492 37169705 := bstep (se 2 (by rfl) ⟨13938639, by rfl⟩ : syracuseStep 37169705 = 27877279) B27877279
theorem B20349305 : Blo 1587492 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B99119213 : Blo 1587492 99119213 := bstep (se 3 (by rfl) ⟨18584852, by rfl⟩ : syracuseStep 99119213 = 37169705) B37169705
theorem B13566203 : Blo 1587492 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B66079475 : Blo 1587492 66079475 := bstep (se 1 (by rfl) ⟨49559606, by rfl⟩ : syracuseStep 66079475 = 99119213) B99119213
theorem B9044135 : Blo 1587492 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B44052983 : Blo 1587492 44052983 := bstep (se 1 (by rfl) ⟨33039737, by rfl⟩ : syracuseStep 44052983 = 66079475) B66079475
theorem B6029423 : Blo 1587492 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B29368655 : Blo 1587492 29368655 := bstep (se 1 (by rfl) ⟨22026491, by rfl⟩ : syracuseStep 29368655 = 44052983) B44052983
theorem B19579103 : Blo 1587492 19579103 := bstep (se 1 (by rfl) ⟨14684327, by rfl⟩ : syracuseStep 19579103 = 29368655) B29368655
theorem B4019615 : Blo 1587492 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B2679743 : Blo 1587492 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B13052735 : Blo 1587492 13052735 := bstep (se 1 (by rfl) ⟨9789551, by rfl⟩ : syracuseStep 13052735 = 19579103) B19579103
theorem B1786495 : Blo 1587492 1786495 := bstep (se 1 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 1786495 = 2679743) B2679743
theorem B8701823 : Blo 1587492 8701823 := bstep (se 1 (by rfl) ⟨6526367, by rfl⟩ : syracuseStep 8701823 = 13052735) B13052735
theorem B5801215 : Blo 1587492 5801215 := bstep (se 1 (by rfl) ⟨4350911, by rfl⟩ : syracuseStep 5801215 = 8701823) B8701823
theorem B2381993 : Blo 1587492 2381993 := bstep (se 2 (by rfl) ⟨893247, by rfl⟩ : syracuseStep 2381993 = 1786495) B1786495
theorem B7734953 : Blo 1587492 7734953 := bstep (se 2 (by rfl) ⟨2900607, by rfl⟩ : syracuseStep 7734953 = 5801215) B5801215
theorem B1587995 : Blo 1587492 1587995 := bstep (se 1 (by rfl) ⟨1190996, by rfl⟩ : syracuseStep 1587995 = 2381993) B2381993
theorem B5156635 : Blo 1587492 5156635 := bstep (se 1 (by rfl) ⟨3867476, by rfl⟩ : syracuseStep 5156635 = 7734953) B7734953
theorem B6875513 : Blo 1587492 6875513 := bstep (se 2 (by rfl) ⟨2578317, by rfl⟩ : syracuseStep 6875513 = 5156635) B5156635
theorem B4583675 : Blo 1587492 4583675 := bstep (se 1 (by rfl) ⟨3437756, by rfl⟩ : syracuseStep 4583675 = 6875513) B6875513
theorem B12223133 : Blo 1587492 12223133 := bstep (se 3 (by rfl) ⟨2291837, by rfl⟩ : syracuseStep 12223133 = 4583675) B4583675
theorem B8148755 : Blo 1587492 8148755 := bstep (se 1 (by rfl) ⟨6111566, by rfl⟩ : syracuseStep 8148755 = 12223133) B12223133
theorem B5432503 : Blo 1587492 5432503 := bstep (se 1 (by rfl) ⟨4074377, by rfl⟩ : syracuseStep 5432503 = 8148755) B8148755
theorem B7243337 : Blo 1587492 7243337 := bstep (se 2 (by rfl) ⟨2716251, by rfl⟩ : syracuseStep 7243337 = 5432503) B5432503
theorem B4828891 : Blo 1587492 4828891 := bstep (se 1 (by rfl) ⟨3621668, by rfl⟩ : syracuseStep 4828891 = 7243337) B7243337
theorem B6438521 : Blo 1587492 6438521 := bstep (se 2 (by rfl) ⟨2414445, by rfl⟩ : syracuseStep 6438521 = 4828891) B4828891
theorem B4292347 : Blo 1587492 4292347 := bstep (se 1 (by rfl) ⟨3219260, by rfl⟩ : syracuseStep 4292347 = 6438521) B6438521
theorem B5723129 : Blo 1587492 5723129 := bstep (se 2 (by rfl) ⟨2146173, by rfl⟩ : syracuseStep 5723129 = 4292347) B4292347
theorem B3815419 : Blo 1587492 3815419 := bstep (se 1 (by rfl) ⟨2861564, by rfl⟩ : syracuseStep 3815419 = 5723129) B5723129
theorem B5087225 : Blo 1587492 5087225 := bstep (se 2 (by rfl) ⟨1907709, by rfl⟩ : syracuseStep 5087225 = 3815419) B3815419
theorem B3391483 : Blo 1587492 3391483 := bstep (se 1 (by rfl) ⟨2543612, by rfl⟩ : syracuseStep 3391483 = 5087225) B5087225
theorem B4521977 : Blo 1587492 4521977 := bstep (se 2 (by rfl) ⟨1695741, by rfl⟩ : syracuseStep 4521977 = 3391483) B3391483
theorem B3014651 : Blo 1587492 3014651 := bstep (se 1 (by rfl) ⟨2260988, by rfl⟩ : syracuseStep 3014651 = 4521977) B4521977
theorem B2009767 : Blo 1587492 2009767 := bstep (se 1 (by rfl) ⟨1507325, by rfl⟩ : syracuseStep 2009767 = 3014651) B3014651
theorem B2679689 : Blo 1587492 2679689 := bstep (se 2 (by rfl) ⟨1004883, by rfl⟩ : syracuseStep 2679689 = 2009767) B2009767
theorem B1786459 : Blo 1587492 1786459 := bstep (se 1 (by rfl) ⟨1339844, by rfl⟩ : syracuseStep 1786459 = 2679689) B2679689
theorem B2381945 : Blo 1587492 2381945 := bstep (se 2 (by rfl) ⟨893229, by rfl⟩ : syracuseStep 2381945 = 1786459) B1786459
theorem B1587963 : Blo 1587492 1587963 := bstep (se 1 (by rfl) ⟨1190972, by rfl⟩ : syracuseStep 1587963 = 2381945) B2381945

theorem C0 (j : ℕ) (h1 : 396873 ≤ j) (h2 : j ≤ 397372) : Blo 1587492 (4 * j + 3) := by
  interval_cases j
  · exact B1587495
  · exact B1587499
  · exact B1587503
  · exact B1587507
  · exact B1587511
  · exact B1587515
  · exact B1587519
  · exact B1587523
  · exact B1587527
  · exact B1587531
  · exact B1587535
  · exact B1587539
  · exact B1587543
  · exact B1587547
  · exact B1587551
  · exact B1587555
  · exact B1587559
  · exact B1587563
  · exact B1587567
  · exact B1587571
  · exact B1587575
  · exact B1587579
  · exact B1587583
  · exact B1587587
  · exact B1587591
  · exact B1587595
  · exact B1587599
  · exact B1587603
  · exact B1587607
  · exact B1587611
  · exact B1587615
  · exact B1587619
  · exact B1587623
  · exact B1587627
  · exact B1587631
  · exact B1587635
  · exact B1587639
  · exact B1587643
  · exact B1587647
  · exact B1587651
  · exact B1587655
  · exact B1587659
  · exact B1587663
  · exact B1587667
  · exact B1587671
  · exact B1587675
  · exact B1587679
  · exact B1587683
  · exact B1587687
  · exact B1587691
  · exact B1587695
  · exact B1587699
  · exact B1587703
  · exact B1587707
  · exact B1587711
  · exact B1587715
  · exact B1587719
  · exact B1587723
  · exact B1587727
  · exact B1587731
  · exact B1587735
  · exact B1587739
  · exact B1587743
  · exact B1587747
  · exact B1587751
  · exact B1587755
  · exact B1587759
  · exact B1587763
  · exact B1587767
  · exact B1587771
  · exact B1587775
  · exact B1587779
  · exact B1587783
  · exact B1587787
  · exact B1587791
  · exact B1587795
  · exact B1587799
  · exact B1587803
  · exact B1587807
  · exact B1587811
  · exact B1587815
  · exact B1587819
  · exact B1587823
  · exact B1587827
  · exact B1587831
  · exact B1587835
  · exact B1587839
  · exact B1587843
  · exact B1587847
  · exact B1587851
  · exact B1587855
  · exact B1587859
  · exact B1587863
  · exact B1587867
  · exact B1587871
  · exact B1587875
  · exact B1587879
  · exact B1587883
  · exact B1587887
  · exact B1587891
  · exact B1587895
  · exact B1587899
  · exact B1587903
  · exact B1587907
  · exact B1587911
  · exact B1587915
  · exact B1587919
  · exact B1587923
  · exact B1587927
  · exact B1587931
  · exact B1587935
  · exact B1587939
  · exact B1587943
  · exact B1587947
  · exact B1587951
  · exact B1587955
  · exact B1587959
  · exact B1587963
  · exact B1587967
  · exact B1587971
  · exact B1587975
  · exact B1587979
  · exact B1587983
  · exact B1587987
  · exact B1587991
  · exact B1587995
  · exact B1587999
  · exact B1588003
  · exact B1588007
  · exact B1588011
  · exact B1588015
  · exact B1588019
  · exact B1588023
  · exact B1588027
  · exact B1588031
  · exact B1588035
  · exact B1588039
  · exact B1588043
  · exact B1588047
  · exact B1588051
  · exact B1588055
  · exact B1588059
  · exact B1588063
  · exact B1588067
  · exact B1588071
  · exact B1588075
  · exact B1588079
  · exact B1588083
  · exact B1588087
  · exact B1588091
  · exact B1588095
  · exact B1588099
  · exact B1588103
  · exact B1588107
  · exact B1588111
  · exact B1588115
  · exact B1588119
  · exact B1588123
  · exact B1588127
  · exact B1588131
  · exact B1588135
  · exact B1588139
  · exact B1588143
  · exact B1588147
  · exact B1588151
  · exact B1588155
  · exact B1588159
  · exact B1588163
  · exact B1588167
  · exact B1588171
  · exact B1588175
  · exact B1588179
  · exact B1588183
  · exact B1588187
  · exact B1588191
  · exact B1588195
  · exact B1588199
  · exact B1588203
  · exact B1588207
  · exact B1588211
  · exact B1588215
  · exact B1588219
  · exact B1588223
  · exact B1588227
  · exact B1588231
  · exact B1588235
  · exact B1588239
  · exact B1588243
  · exact B1588247
  · exact B1588251
  · exact B1588255
  · exact B1588259
  · exact B1588263
  · exact B1588267
  · exact B1588271
  · exact B1588275
  · exact B1588279
  · exact B1588283
  · exact B1588287
  · exact B1588291
  · exact B1588295
  · exact B1588299
  · exact B1588303
  · exact B1588307
  · exact B1588311
  · exact B1588315
  · exact B1588319
  · exact B1588323
  · exact B1588327
  · exact B1588331
  · exact B1588335
  · exact B1588339
  · exact B1588343
  · exact B1588347
  · exact B1588351
  · exact B1588355
  · exact B1588359
  · exact B1588363
  · exact B1588367
  · exact B1588371
  · exact B1588375
  · exact B1588379
  · exact B1588383
  · exact B1588387
  · exact B1588391
  · exact B1588395
  · exact B1588399
  · exact B1588403
  · exact B1588407
  · exact B1588411
  · exact B1588415
  · exact B1588419
  · exact B1588423
  · exact B1588427
  · exact B1588431
  · exact B1588435
  · exact B1588439
  · exact B1588443
  · exact B1588447
  · exact B1588451
  · exact B1588455
  · exact B1588459
  · exact B1588463
  · exact B1588467
  · exact B1588471
  · exact B1588475
  · exact B1588479
  · exact B1588483
  · exact B1588487
  · exact B1588491
  · exact B1588495
  · exact B1588499
  · exact B1588503
  · exact B1588507
  · exact B1588511
  · exact B1588515
  · exact B1588519
  · exact B1588523
  · exact B1588527
  · exact B1588531
  · exact B1588535
  · exact B1588539
  · exact B1588543
  · exact B1588547
  · exact B1588551
  · exact B1588555
  · exact B1588559
  · exact B1588563
  · exact B1588567
  · exact B1588571
  · exact B1588575
  · exact B1588579
  · exact B1588583
  · exact B1588587
  · exact B1588591
  · exact B1588595
  · exact B1588599
  · exact B1588603
  · exact B1588607
  · exact B1588611
  · exact B1588615
  · exact B1588619
  · exact B1588623
  · exact B1588627
  · exact B1588631
  · exact B1588635
  · exact B1588639
  · exact B1588643
  · exact B1588647
  · exact B1588651
  · exact B1588655
  · exact B1588659
  · exact B1588663
  · exact B1588667
  · exact B1588671
  · exact B1588675
  · exact B1588679
  · exact B1588683
  · exact B1588687
  · exact B1588691
  · exact B1588695
  · exact B1588699
  · exact B1588703
  · exact B1588707
  · exact B1588711
  · exact B1588715
  · exact B1588719
  · exact B1588723
  · exact B1588727
  · exact B1588731
  · exact B1588735
  · exact B1588739
  · exact B1588743
  · exact B1588747
  · exact B1588751
  · exact B1588755
  · exact B1588759
  · exact B1588763
  · exact B1588767
  · exact B1588771
  · exact B1588775
  · exact B1588779
  · exact B1588783
  · exact B1588787
  · exact B1588791
  · exact B1588795
  · exact B1588799
  · exact B1588803
  · exact B1588807
  · exact B1588811
  · exact B1588815
  · exact B1588819
  · exact B1588823
  · exact B1588827
  · exact B1588831
  · exact B1588835
  · exact B1588839
  · exact B1588843
  · exact B1588847
  · exact B1588851
  · exact B1588855
  · exact B1588859
  · exact B1588863
  · exact B1588867
  · exact B1588871
  · exact B1588875
  · exact B1588879
  · exact B1588883
  · exact B1588887
  · exact B1588891
  · exact B1588895
  · exact B1588899
  · exact B1588903
  · exact B1588907
  · exact B1588911
  · exact B1588915
  · exact B1588919
  · exact B1588923
  · exact B1588927
  · exact B1588931
  · exact B1588935
  · exact B1588939
  · exact B1588943
  · exact B1588947
  · exact B1588951
  · exact B1588955
  · exact B1588959
  · exact B1588963
  · exact B1588967
  · exact B1588971
  · exact B1588975
  · exact B1588979
  · exact B1588983
  · exact B1588987
  · exact B1588991
  · exact B1588995
  · exact B1588999
  · exact B1589003
  · exact B1589007
  · exact B1589011
  · exact B1589015
  · exact B1589019
  · exact B1589023
  · exact B1589027
  · exact B1589031
  · exact B1589035
  · exact B1589039
  · exact B1589043
  · exact B1589047
  · exact B1589051
  · exact B1589055
  · exact B1589059
  · exact B1589063
  · exact B1589067
  · exact B1589071
  · exact B1589075
  · exact B1589079
  · exact B1589083
  · exact B1589087
  · exact B1589091
  · exact B1589095
  · exact B1589099
  · exact B1589103
  · exact B1589107
  · exact B1589111
  · exact B1589115
  · exact B1589119
  · exact B1589123
  · exact B1589127
  · exact B1589131
  · exact B1589135
  · exact B1589139
  · exact B1589143
  · exact B1589147
  · exact B1589151
  · exact B1589155
  · exact B1589159
  · exact B1589163
  · exact B1589167
  · exact B1589171
  · exact B1589175
  · exact B1589179
  · exact B1589183
  · exact B1589187
  · exact B1589191
  · exact B1589195
  · exact B1589199
  · exact B1589203
  · exact B1589207
  · exact B1589211
  · exact B1589215
  · exact B1589219
  · exact B1589223
  · exact B1589227
  · exact B1589231
  · exact B1589235
  · exact B1589239
  · exact B1589243
  · exact B1589247
  · exact B1589251
  · exact B1589255
  · exact B1589259
  · exact B1589263
  · exact B1589267
  · exact B1589271
  · exact B1589275
  · exact B1589279
  · exact B1589283
  · exact B1589287
  · exact B1589291
  · exact B1589295
  · exact B1589299
  · exact B1589303
  · exact B1589307
  · exact B1589311
  · exact B1589315
  · exact B1589319
  · exact B1589323
  · exact B1589327
  · exact B1589331
  · exact B1589335
  · exact B1589339
  · exact B1589343
  · exact B1589347
  · exact B1589351
  · exact B1589355
  · exact B1589359
  · exact B1589363
  · exact B1589367
  · exact B1589371
  · exact B1589375
  · exact B1589379
  · exact B1589383
  · exact B1589387
  · exact B1589391
  · exact B1589395
  · exact B1589399
  · exact B1589403
  · exact B1589407
  · exact B1589411
  · exact B1589415
  · exact B1589419
  · exact B1589423
  · exact B1589427
  · exact B1589431
  · exact B1589435
  · exact B1589439
  · exact B1589443
  · exact B1589447
  · exact B1589451
  · exact B1589455
  · exact B1589459
  · exact B1589463
  · exact B1589467
  · exact B1589471
  · exact B1589475
  · exact B1589479
  · exact B1589483
  · exact B1589487
  · exact B1589491

theorem solution (m : ℕ) (hlo : 1587492 ≤ m) (hhi : m ≤ 1589492) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 396873 ≤ j := by omega
    have hj2 : j ≤ 397372 := by omega
    have hb : Blo 1587492 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
