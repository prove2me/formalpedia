-- Prove2me | solution 1 for syracuse_descends_range_1638018_1640018
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:15:48.491763+00:00
-- url     : https://prove2.me/submissions/826a7b08-5326-440f-86c1-5567a7a517a7

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


theorem B2457605 : Blo 1638018 2457605 := bbase (se 4 (by rfl) ⟨230400, by rfl⟩ : syracuseStep 2457605 = 460801) (by norm_num)
theorem B1843213 : Blo 1638018 1843213 := bbase (se 3 (by rfl) ⟨345602, by rfl⟩ : syracuseStep 1843213 = 691205) (by norm_num)
theorem B2457629 : Blo 1638018 2457629 := bbase (se 3 (by rfl) ⟨460805, by rfl⟩ : syracuseStep 2457629 = 921611) (by norm_num)
theorem B3113005 : Blo 1638018 3113005 := bbase (se 3 (by rfl) ⟨583688, by rfl⟩ : syracuseStep 3113005 = 1167377) (by norm_num)
theorem B1843249 : Blo 1638018 1843249 := bbase (se 2 (by rfl) ⟨691218, by rfl⟩ : syracuseStep 1843249 = 1382437) (by norm_num)
theorem B5529653 : Blo 1638018 5529653 := bbase (se 5 (by rfl) ⟨259202, by rfl⟩ : syracuseStep 5529653 = 518405) (by norm_num)
theorem B3686453 : Blo 1638018 3686453 := bbase (se 5 (by rfl) ⟨172802, by rfl⟩ : syracuseStep 3686453 = 345605) (by norm_num)
theorem B2457653 : Blo 1638018 2457653 := bbase (se 5 (by rfl) ⟨115202, by rfl⟩ : syracuseStep 2457653 = 230405) (by norm_num)
theorem B2457677 : Blo 1638018 2457677 := bbase (se 3 (by rfl) ⟨460814, by rfl⟩ : syracuseStep 2457677 = 921629) (by norm_num)
theorem B1843285 : Blo 1638018 1843285 := bbase (se 8 (by rfl) ⟨10800, by rfl⟩ : syracuseStep 1843285 = 21601) (by norm_num)
theorem B2457701 : Blo 1638018 2457701 := bbase (se 4 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 2457701 = 460819) (by norm_num)
theorem B1843321 : Blo 1638018 1843321 := bbase (se 2 (by rfl) ⟨691245, by rfl⟩ : syracuseStep 1843321 = 1382491) (by norm_num)
theorem B3686525 : Blo 1638018 3686525 := bbase (se 3 (by rfl) ⟨691223, by rfl⟩ : syracuseStep 3686525 = 1382447) (by norm_num)
theorem B2457725 : Blo 1638018 2457725 := bbase (se 3 (by rfl) ⟨460823, by rfl⟩ : syracuseStep 2457725 = 921647) (by norm_num)
theorem B2334845 : Blo 1638018 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B2457749 : Blo 1638018 2457749 := bbase (se 6 (by rfl) ⟨57603, by rfl⟩ : syracuseStep 2457749 = 115207) (by norm_num)
theorem B1843357 : Blo 1638018 1843357 := bbase (se 3 (by rfl) ⟨345629, by rfl⟩ : syracuseStep 1843357 = 691259) (by norm_num)
theorem B6226085 : Blo 1638018 6226085 := bbase (se 4 (by rfl) ⟨583695, by rfl⟩ : syracuseStep 6226085 = 1167391) (by norm_num)
theorem B2457773 : Blo 1638018 2457773 := bbase (se 3 (by rfl) ⟨460832, by rfl⟩ : syracuseStep 2457773 = 921665) (by norm_num)
theorem B3113149 : Blo 1638018 3113149 := bbase (se 3 (by rfl) ⟨583715, by rfl⟩ : syracuseStep 3113149 = 1167431) (by norm_num)
theorem B1843393 : Blo 1638018 1843393 := bbase (se 2 (by rfl) ⟨691272, by rfl⟩ : syracuseStep 1843393 = 1382545) (by norm_num)
theorem B3686597 : Blo 1638018 3686597 := bbase (se 4 (by rfl) ⟨345618, by rfl⟩ : syracuseStep 3686597 = 691237) (by norm_num)
theorem B2457797 : Blo 1638018 2457797 := bbase (se 4 (by rfl) ⟨230418, by rfl⟩ : syracuseStep 2457797 = 460837) (by norm_num)
theorem B2457821 : Blo 1638018 2457821 := bbase (se 3 (by rfl) ⟨460841, by rfl⟩ : syracuseStep 2457821 = 921683) (by norm_num)
theorem B1843429 : Blo 1638018 1843429 := bbase (se 4 (by rfl) ⟨172821, by rfl⟩ : syracuseStep 1843429 = 345643) (by norm_num)
theorem B2457845 : Blo 1638018 2457845 := bbase (se 5 (by rfl) ⟨115211, by rfl⟩ : syracuseStep 2457845 = 230423) (by norm_num)
theorem B1843465 : Blo 1638018 1843465 := bbase (se 2 (by rfl) ⟨691299, by rfl⟩ : syracuseStep 1843465 = 1382599) (by norm_num)
theorem B3686669 : Blo 1638018 3686669 := bbase (se 3 (by rfl) ⟨691250, by rfl⟩ : syracuseStep 3686669 = 1382501) (by norm_num)
theorem B2457869 : Blo 1638018 2457869 := bbase (se 3 (by rfl) ⟨460850, by rfl⟩ : syracuseStep 2457869 = 921701) (by norm_num)
theorem B8298773 : Blo 1638018 8298773 := bbase (se 6 (by rfl) ⟨194502, by rfl⟩ : syracuseStep 8298773 = 389005) (by norm_num)
theorem B2457893 : Blo 1638018 2457893 := bbase (se 4 (by rfl) ⟨230427, by rfl⟩ : syracuseStep 2457893 = 460855) (by norm_num)
theorem B1843501 : Blo 1638018 1843501 := bbase (se 3 (by rfl) ⟨345656, by rfl⟩ : syracuseStep 1843501 = 691313) (by norm_num)
theorem B2457917 : Blo 1638018 2457917 := bbase (se 3 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 2457917 = 921719) (by norm_num)
theorem B1843537 : Blo 1638018 1843537 := bbase (se 2 (by rfl) ⟨691326, by rfl⟩ : syracuseStep 1843537 = 1382653) (by norm_num)
theorem B3686741 : Blo 1638018 3686741 := bbase (se 10 (by rfl) ⟨5400, by rfl⟩ : syracuseStep 3686741 = 10801) (by norm_num)
theorem B2457941 : Blo 1638018 2457941 := bbase (se 10 (by rfl) ⟨3600, by rfl⟩ : syracuseStep 2457941 = 7201) (by norm_num)
theorem B3113309 : Blo 1638018 3113309 := bbase (se 3 (by rfl) ⟨583745, by rfl⟩ : syracuseStep 3113309 = 1167491) (by norm_num)
theorem B2457965 : Blo 1638018 2457965 := bbase (se 3 (by rfl) ⟨460868, by rfl⟩ : syracuseStep 2457965 = 921737) (by norm_num)
theorem B1843573 : Blo 1638018 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B2457989 : Blo 1638018 2457989 := bbase (se 4 (by rfl) ⟨230436, by rfl⟩ : syracuseStep 2457989 = 460873) (by norm_num)
theorem B1843609 : Blo 1638018 1843609 := bbase (se 2 (by rfl) ⟨691353, by rfl⟩ : syracuseStep 1843609 = 1382707) (by norm_num)
theorem B3686813 : Blo 1638018 3686813 := bbase (se 3 (by rfl) ⟨691277, by rfl⟩ : syracuseStep 3686813 = 1382555) (by norm_num)
theorem B2458013 : Blo 1638018 2458013 := bbase (se 3 (by rfl) ⟨460877, by rfl⟩ : syracuseStep 2458013 = 921755) (by norm_num)
theorem B5251493 : Blo 1638018 5251493 := bbase (se 4 (by rfl) ⟨492327, by rfl⟩ : syracuseStep 5251493 = 984655) (by norm_num)
theorem B2458037 : Blo 1638018 2458037 := bbase (se 5 (by rfl) ⟨115220, by rfl⟩ : syracuseStep 2458037 = 230441) (by norm_num)
theorem B1843645 : Blo 1638018 1843645 := bbase (se 3 (by rfl) ⟨345683, by rfl⟩ : syracuseStep 1843645 = 691367) (by norm_num)
theorem B2458061 : Blo 1638018 2458061 := bbase (se 3 (by rfl) ⟨460886, by rfl⟩ : syracuseStep 2458061 = 921773) (by norm_num)
theorem B1843681 : Blo 1638018 1843681 := bbase (se 2 (by rfl) ⟨691380, by rfl⟩ : syracuseStep 1843681 = 1382761) (by norm_num)
theorem B5530085 : Blo 1638018 5530085 := bbase (se 4 (by rfl) ⟨518445, by rfl⟩ : syracuseStep 5530085 = 1036891) (by norm_num)
theorem B3686885 : Blo 1638018 3686885 := bbase (se 4 (by rfl) ⟨345645, by rfl⟩ : syracuseStep 3686885 = 691291) (by norm_num)
theorem B2458085 : Blo 1638018 2458085 := bbase (se 4 (by rfl) ⟨230445, by rfl⟩ : syracuseStep 2458085 = 460891) (by norm_num)
theorem B3113453 : Blo 1638018 3113453 := bbase (se 3 (by rfl) ⟨583772, by rfl⟩ : syracuseStep 3113453 = 1167545) (by norm_num)
theorem B2458109 : Blo 1638018 2458109 := bbase (se 3 (by rfl) ⟨460895, by rfl⟩ : syracuseStep 2458109 = 921791) (by norm_num)
theorem B1843717 : Blo 1638018 1843717 := bbase (se 4 (by rfl) ⟨172848, by rfl⟩ : syracuseStep 1843717 = 345697) (by norm_num)
theorem B2458133 : Blo 1638018 2458133 := bbase (se 6 (by rfl) ⟨57612, by rfl⟩ : syracuseStep 2458133 = 115225) (by norm_num)
theorem B1843753 : Blo 1638018 1843753 := bbase (se 2 (by rfl) ⟨691407, by rfl⟩ : syracuseStep 1843753 = 1382815) (by norm_num)
theorem B3686957 : Blo 1638018 3686957 := bbase (se 3 (by rfl) ⟨691304, by rfl⟩ : syracuseStep 3686957 = 1382609) (by norm_num)
theorem B2458157 : Blo 1638018 2458157 := bbase (se 3 (by rfl) ⟨460904, by rfl⟩ : syracuseStep 2458157 = 921809) (by norm_num)
theorem B15753781 : Blo 1638018 15753781 := bbase (se 5 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 15753781 = 1476917) (by norm_num)
theorem B2458181 : Blo 1638018 2458181 := bbase (se 4 (by rfl) ⟨230454, by rfl⟩ : syracuseStep 2458181 = 460909) (by norm_num)
theorem B1843789 : Blo 1638018 1843789 := bbase (se 3 (by rfl) ⟨345710, by rfl⟩ : syracuseStep 1843789 = 691421) (by norm_num)
theorem B2458205 : Blo 1638018 2458205 := bbase (se 3 (by rfl) ⟨460913, by rfl⟩ : syracuseStep 2458205 = 921827) (by norm_num)
theorem B1843825 : Blo 1638018 1843825 := bbase (se 2 (by rfl) ⟨691434, by rfl⟩ : syracuseStep 1843825 = 1382869) (by norm_num)
theorem B2073205 : Blo 1638018 2073205 := bbase (se 5 (by rfl) ⟨97181, by rfl⟩ : syracuseStep 2073205 = 194363) (by norm_num)
theorem B3687029 : Blo 1638018 3687029 := bbase (se 5 (by rfl) ⟨172829, by rfl⟩ : syracuseStep 3687029 = 345659) (by norm_num)
theorem B2458229 : Blo 1638018 2458229 := bbase (se 5 (by rfl) ⟨115229, by rfl⟩ : syracuseStep 2458229 = 230459) (by norm_num)
theorem B2458253 : Blo 1638018 2458253 := bbase (se 3 (by rfl) ⟨460922, by rfl⟩ : syracuseStep 2458253 = 921845) (by norm_num)
theorem B1843861 : Blo 1638018 1843861 := bbase (se 6 (by rfl) ⟨43215, by rfl⟩ : syracuseStep 1843861 = 86431) (by norm_num)
theorem B2458277 : Blo 1638018 2458277 := bbase (se 4 (by rfl) ⟨230463, by rfl⟩ : syracuseStep 2458277 = 460927) (by norm_num)
theorem B1843897 : Blo 1638018 1843897 := bbase (se 2 (by rfl) ⟨691461, by rfl⟩ : syracuseStep 1843897 = 1382923) (by norm_num)
theorem B3687101 : Blo 1638018 3687101 := bbase (se 3 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 3687101 = 1382663) (by norm_num)
theorem B2458301 : Blo 1638018 2458301 := bbase (se 3 (by rfl) ⟨460931, by rfl⟩ : syracuseStep 2458301 = 921863) (by norm_num)
theorem B2458325 : Blo 1638018 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B1843933 : Blo 1638018 1843933 := bbase (se 3 (by rfl) ⟨345737, by rfl⟩ : syracuseStep 1843933 = 691475) (by norm_num)
theorem B2802413 : Blo 1638018 2802413 := bbase (se 3 (by rfl) ⟨525452, by rfl⟩ : syracuseStep 2802413 = 1050905) (by norm_num)
theorem B2458349 : Blo 1638018 2458349 := bbase (se 3 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 2458349 = 921881) (by norm_num)
theorem B1843969 : Blo 1638018 1843969 := bbase (se 2 (by rfl) ⟨691488, by rfl⟩ : syracuseStep 1843969 = 1382977) (by norm_num)
theorem B3687173 : Blo 1638018 3687173 := bbase (se 4 (by rfl) ⟨345672, by rfl⟩ : syracuseStep 3687173 = 691345) (by norm_num)
theorem B2458373 : Blo 1638018 2458373 := bbase (se 4 (by rfl) ⟨230472, by rfl⟩ : syracuseStep 2458373 = 460945) (by norm_num)
theorem B2458397 : Blo 1638018 2458397 := bbase (se 3 (by rfl) ⟨460949, by rfl⟩ : syracuseStep 2458397 = 921899) (by norm_num)
theorem B2073377 : Blo 1638018 2073377 := bbase (se 2 (by rfl) ⟨777516, by rfl⟩ : syracuseStep 2073377 = 1555033) (by norm_num)
theorem B1844005 : Blo 1638018 1844005 := bbase (se 4 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 1844005 = 345751) (by norm_num)
theorem B2458421 : Blo 1638018 2458421 := bbase (se 5 (by rfl) ⟨115238, by rfl⟩ : syracuseStep 2458421 = 230477) (by norm_num)
theorem B1844041 : Blo 1638018 1844041 := bbase (se 2 (by rfl) ⟨691515, by rfl⟩ : syracuseStep 1844041 = 1383031) (by norm_num)
theorem B3687245 : Blo 1638018 3687245 := bbase (se 3 (by rfl) ⟨691358, by rfl⟩ : syracuseStep 3687245 = 1382717) (by norm_num)
theorem B2458445 : Blo 1638018 2458445 := bbase (se 3 (by rfl) ⟨460958, by rfl⟩ : syracuseStep 2458445 = 921917) (by norm_num)
theorem B23634773 : Blo 1638018 23634773 := bbase (se 9 (by rfl) ⟨69242, by rfl⟩ : syracuseStep 23634773 = 138485) (by norm_num)
theorem B2073433 : Blo 1638018 2073433 := bbase (se 2 (by rfl) ⟨777537, by rfl⟩ : syracuseStep 2073433 = 1555075) (by norm_num)
theorem B2491229 : Blo 1638018 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B2458469 : Blo 1638018 2458469 := bbase (se 4 (by rfl) ⟨230481, by rfl⟩ : syracuseStep 2458469 = 460963) (by norm_num)
theorem B1844077 : Blo 1638018 1844077 := bbase (se 3 (by rfl) ⟨345764, by rfl⟩ : syracuseStep 1844077 = 691529) (by norm_num)
theorem B2458493 : Blo 1638018 2458493 := bbase (se 3 (by rfl) ⟨460967, by rfl⟩ : syracuseStep 2458493 = 921935) (by norm_num)
theorem B3498893 : Blo 1638018 3498893 := bbase (se 3 (by rfl) ⟨656042, by rfl⟩ : syracuseStep 3498893 = 1312085) (by norm_num)
theorem B1844113 : Blo 1638018 1844113 := bbase (se 2 (by rfl) ⟨691542, by rfl⟩ : syracuseStep 1844113 = 1383085) (by norm_num)
theorem B5530517 : Blo 1638018 5530517 := bbase (se 6 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 5530517 = 259243) (by norm_num)
theorem B3687317 : Blo 1638018 3687317 := bbase (se 6 (by rfl) ⟨86421, by rfl⟩ : syracuseStep 3687317 = 172843) (by norm_num)
theorem B2458517 : Blo 1638018 2458517 := bbase (se 6 (by rfl) ⟨57621, by rfl⟩ : syracuseStep 2458517 = 115243) (by norm_num)
theorem B2491301 : Blo 1638018 2491301 := bbase (se 4 (by rfl) ⟨233559, by rfl⟩ : syracuseStep 2491301 = 467119) (by norm_num)
theorem B2458541 : Blo 1638018 2458541 := bbase (se 3 (by rfl) ⟨460976, by rfl⟩ : syracuseStep 2458541 = 921953) (by norm_num)
theorem B1844149 : Blo 1638018 1844149 := bbase (se 5 (by rfl) ⟨86444, by rfl⟩ : syracuseStep 1844149 = 172889) (by norm_num)
theorem B2073529 : Blo 1638018 2073529 := bbase (se 2 (by rfl) ⟨777573, by rfl⟩ : syracuseStep 2073529 = 1555147) (by norm_num)
theorem B2458565 : Blo 1638018 2458565 := bbase (se 4 (by rfl) ⟨230490, by rfl⟩ : syracuseStep 2458565 = 460981) (by norm_num)
theorem B1844185 : Blo 1638018 1844185 := bbase (se 2 (by rfl) ⟨691569, by rfl⟩ : syracuseStep 1844185 = 1383139) (by norm_num)
theorem B3687389 : Blo 1638018 3687389 := bbase (se 3 (by rfl) ⟨691385, by rfl⟩ : syracuseStep 3687389 = 1382771) (by norm_num)
theorem B2458589 : Blo 1638018 2458589 := bbase (se 3 (by rfl) ⟨460985, by rfl⟩ : syracuseStep 2458589 = 921971) (by norm_num)
theorem B2458613 : Blo 1638018 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B1844221 : Blo 1638018 1844221 := bbase (se 3 (by rfl) ⟨345791, by rfl⟩ : syracuseStep 1844221 = 691583) (by norm_num)
theorem B3499013 : Blo 1638018 3499013 := bbase (se 4 (by rfl) ⟨328032, by rfl⟩ : syracuseStep 3499013 = 656065) (by norm_num)
theorem B2802701 : Blo 1638018 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B2458637 : Blo 1638018 2458637 := bbase (se 3 (by rfl) ⟨460994, by rfl⟩ : syracuseStep 2458637 = 921989) (by norm_num)
theorem B1844257 : Blo 1638018 1844257 := bbase (se 2 (by rfl) ⟨691596, by rfl⟩ : syracuseStep 1844257 = 1383193) (by norm_num)
theorem B3687461 : Blo 1638018 3687461 := bbase (se 4 (by rfl) ⟨345699, by rfl⟩ : syracuseStep 3687461 = 691399) (by norm_num)
theorem B2458661 : Blo 1638018 2458661 := bbase (se 4 (by rfl) ⟨230499, by rfl⟩ : syracuseStep 2458661 = 460999) (by norm_num)
theorem B2458685 : Blo 1638018 2458685 := bbase (se 3 (by rfl) ⟨461003, by rfl⟩ : syracuseStep 2458685 = 922007) (by norm_num)
theorem B1844293 : Blo 1638018 1844293 := bbase (se 4 (by rfl) ⟨172902, by rfl⟩ : syracuseStep 1844293 = 345805) (by norm_num)
theorem B2458709 : Blo 1638018 2458709 := bbase (se 8 (by rfl) ⟨14406, by rfl⟩ : syracuseStep 2458709 = 28813) (by norm_num)
theorem B2073701 : Blo 1638018 2073701 := bbase (se 4 (by rfl) ⟨194409, by rfl⟩ : syracuseStep 2073701 = 388819) (by norm_num)
theorem B1844329 : Blo 1638018 1844329 := bbase (se 2 (by rfl) ⟨691623, by rfl⟩ : syracuseStep 1844329 = 1383247) (by norm_num)
theorem B3687533 : Blo 1638018 3687533 := bbase (se 3 (by rfl) ⟨691412, by rfl⟩ : syracuseStep 3687533 = 1382825) (by norm_num)
theorem B2458733 : Blo 1638018 2458733 := bbase (se 3 (by rfl) ⟨461012, by rfl⟩ : syracuseStep 2458733 = 922025) (by norm_num)
theorem B2458757 : Blo 1638018 2458757 := bbase (se 4 (by rfl) ⟨230508, by rfl⟩ : syracuseStep 2458757 = 461017) (by norm_num)
theorem B1844365 : Blo 1638018 1844365 := bbase (se 3 (by rfl) ⟨345818, by rfl⟩ : syracuseStep 1844365 = 691637) (by norm_num)
theorem B2073757 : Blo 1638018 2073757 := bbase (se 3 (by rfl) ⟨388829, by rfl⟩ : syracuseStep 2073757 = 777659) (by norm_num)
theorem B2458781 : Blo 1638018 2458781 := bbase (se 3 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 2458781 = 922043) (by norm_num)
theorem B4146349 : Blo 1638018 4146349 := bbase (se 3 (by rfl) ⟨777440, by rfl⟩ : syracuseStep 4146349 = 1554881) (by norm_num)
theorem B1844401 : Blo 1638018 1844401 := bbase (se 2 (by rfl) ⟨691650, by rfl⟩ : syracuseStep 1844401 = 1383301) (by norm_num)
theorem B3687605 : Blo 1638018 3687605 := bbase (se 5 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 3687605 = 345713) (by norm_num)
theorem B2458805 : Blo 1638018 2458805 := bbase (se 5 (by rfl) ⟨115256, by rfl⟩ : syracuseStep 2458805 = 230513) (by norm_num)
theorem B2458829 : Blo 1638018 2458829 := bbase (se 3 (by rfl) ⟨461030, by rfl⟩ : syracuseStep 2458829 = 922061) (by norm_num)
theorem B6997205 : Blo 1638018 6997205 := bbase (se 7 (by rfl) ⟨81998, by rfl⟩ : syracuseStep 6997205 = 163997) (by norm_num)
theorem B1844437 : Blo 1638018 1844437 := bbase (se 7 (by rfl) ⟨21614, by rfl⟩ : syracuseStep 1844437 = 43229) (by norm_num)
theorem B56796373 : Blo 1638018 56796373 := bbase (se 7 (by rfl) ⟨665582, by rfl⟩ : syracuseStep 56796373 = 1331165) (by norm_num)
theorem B3548389 : Blo 1638018 3548389 := bbase (se 4 (by rfl) ⟨332661, by rfl⟩ : syracuseStep 3548389 = 665323) (by norm_num)
theorem B2458853 : Blo 1638018 2458853 := bbase (se 4 (by rfl) ⟨230517, by rfl⟩ : syracuseStep 2458853 = 461035) (by norm_num)
theorem B1844473 : Blo 1638018 1844473 := bbase (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) (by norm_num)
theorem B2073853 : Blo 1638018 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B3687677 : Blo 1638018 3687677 := bbase (se 3 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 3687677 = 1382879) (by norm_num)
theorem B2458877 : Blo 1638018 2458877 := bbase (se 3 (by rfl) ⟨461039, by rfl⟩ : syracuseStep 2458877 = 922079) (by norm_num)
theorem B2458901 : Blo 1638018 2458901 := bbase (se 6 (by rfl) ⟨57630, by rfl⟩ : syracuseStep 2458901 = 115261) (by norm_num)
theorem B4146461 : Blo 1638018 4146461 := bbase (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) (by norm_num)
theorem B1844509 : Blo 1638018 1844509 := bbase (se 3 (by rfl) ⟨345845, by rfl⟩ : syracuseStep 1844509 = 691691) (by norm_num)
theorem B2458925 : Blo 1638018 2458925 := bbase (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) (by norm_num)
theorem B1844545 : Blo 1638018 1844545 := bbase (se 2 (by rfl) ⟨691704, by rfl⟩ : syracuseStep 1844545 = 1383409) (by norm_num)
theorem B5530949 : Blo 1638018 5530949 := bbase (se 4 (by rfl) ⟨518526, by rfl⟩ : syracuseStep 5530949 = 1037053) (by norm_num)
theorem B3687749 : Blo 1638018 3687749 := bbase (se 4 (by rfl) ⟨345726, by rfl⟩ : syracuseStep 3687749 = 691453) (by norm_num)
theorem B2458949 : Blo 1638018 2458949 := bbase (se 4 (by rfl) ⟨230526, by rfl⟩ : syracuseStep 2458949 = 461053) (by norm_num)
theorem B2458973 : Blo 1638018 2458973 := bbase (se 3 (by rfl) ⟨461057, by rfl⟩ : syracuseStep 2458973 = 922115) (by norm_num)
theorem B1844581 : Blo 1638018 1844581 := bbase (se 4 (by rfl) ⟨172929, by rfl⟩ : syracuseStep 1844581 = 345859) (by norm_num)
theorem B12608885 : Blo 1638018 12608885 := bbase (se 5 (by rfl) ⟨591041, by rfl⟩ : syracuseStep 12608885 = 1182083) (by norm_num)
theorem B2458997 : Blo 1638018 2458997 := bbase (se 5 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 2458997 = 230531) (by norm_num)
theorem B1844617 : Blo 1638018 1844617 := bbase (se 2 (by rfl) ⟨691731, by rfl⟩ : syracuseStep 1844617 = 1383463) (by norm_num)
theorem B3687821 : Blo 1638018 3687821 := bbase (se 3 (by rfl) ⟨691466, by rfl⟩ : syracuseStep 3687821 = 1382933) (by norm_num)
theorem B2459021 : Blo 1638018 2459021 := bbase (se 3 (by rfl) ⟨461066, by rfl⟩ : syracuseStep 2459021 = 922133) (by norm_num)
theorem B2459045 : Blo 1638018 2459045 := bbase (se 4 (by rfl) ⟨230535, by rfl⟩ : syracuseStep 2459045 = 461071) (by norm_num)
theorem B2074025 : Blo 1638018 2074025 := bbase (se 2 (by rfl) ⟨777759, by rfl⟩ : syracuseStep 2074025 = 1555519) (by norm_num)
theorem B1844653 : Blo 1638018 1844653 := bbase (se 3 (by rfl) ⟨345872, by rfl⟩ : syracuseStep 1844653 = 691745) (by norm_num)
theorem B2459069 : Blo 1638018 2459069 := bbase (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) (by norm_num)
theorem B1844689 : Blo 1638018 1844689 := bbase (se 2 (by rfl) ⟨691758, by rfl⟩ : syracuseStep 1844689 = 1383517) (by norm_num)
theorem B13469141 : Blo 1638018 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B3687893 : Blo 1638018 3687893 := bbase (se 7 (by rfl) ⟨43217, by rfl⟩ : syracuseStep 3687893 = 86435) (by norm_num)
theorem B2459093 : Blo 1638018 2459093 := bbase (se 7 (by rfl) ⟨28817, by rfl⟩ : syracuseStep 2459093 = 57635) (by norm_num)
theorem B4146653 : Blo 1638018 4146653 := bbase (se 3 (by rfl) ⟨777497, by rfl⟩ : syracuseStep 4146653 = 1554995) (by norm_num)
theorem B2074081 : Blo 1638018 2074081 := bbase (se 2 (by rfl) ⟨777780, by rfl⟩ : syracuseStep 2074081 = 1555561) (by norm_num)
theorem B2459117 : Blo 1638018 2459117 := bbase (se 3 (by rfl) ⟨461084, by rfl⟩ : syracuseStep 2459117 = 922169) (by norm_num)
theorem B1844725 : Blo 1638018 1844725 := bbase (se 5 (by rfl) ⟨86471, by rfl⟩ : syracuseStep 1844725 = 172943) (by norm_num)
theorem B2459141 : Blo 1638018 2459141 := bbase (se 4 (by rfl) ⟨230544, by rfl⟩ : syracuseStep 2459141 = 461089) (by norm_num)
theorem B1844761 : Blo 1638018 1844761 := bbase (se 2 (by rfl) ⟨691785, by rfl⟩ : syracuseStep 1844761 = 1383571) (by norm_num)
theorem B3687965 : Blo 1638018 3687965 := bbase (se 3 (by rfl) ⟨691493, by rfl⟩ : syracuseStep 3687965 = 1382987) (by norm_num)
theorem B2459165 : Blo 1638018 2459165 := bbase (se 3 (by rfl) ⟨461093, by rfl⟩ : syracuseStep 2459165 = 922187) (by norm_num)
theorem B8300069 : Blo 1638018 8300069 := bbase (se 4 (by rfl) ⟨778131, by rfl⟩ : syracuseStep 8300069 = 1556263) (by norm_num)
theorem B2459189 : Blo 1638018 2459189 := bbase (se 5 (by rfl) ⟨115274, by rfl⟩ : syracuseStep 2459189 = 230549) (by norm_num)
theorem B1844797 : Blo 1638018 1844797 := bbase (se 3 (by rfl) ⟨345899, by rfl⟩ : syracuseStep 1844797 = 691799) (by norm_num)
theorem B2074177 : Blo 1638018 2074177 := bbase (se 2 (by rfl) ⟨777816, by rfl⟩ : syracuseStep 2074177 = 1555633) (by norm_num)
theorem B2459213 : Blo 1638018 2459213 := bbase (se 3 (by rfl) ⟨461102, by rfl⟩ : syracuseStep 2459213 = 922205) (by norm_num)
theorem B1844833 : Blo 1638018 1844833 := bbase (se 2 (by rfl) ⟨691812, by rfl⟩ : syracuseStep 1844833 = 1383625) (by norm_num)
theorem B3688037 : Blo 1638018 3688037 := bbase (se 4 (by rfl) ⟨345753, by rfl⟩ : syracuseStep 3688037 = 691507) (by norm_num)
theorem B2459237 : Blo 1638018 2459237 := bbase (se 4 (by rfl) ⟨230553, by rfl⟩ : syracuseStep 2459237 = 461107) (by norm_num)
theorem B3499645 : Blo 1638018 3499645 := bbase (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) (by norm_num)
theorem B2459261 : Blo 1638018 2459261 := bbase (se 3 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 2459261 = 922223) (by norm_num)
theorem B1844869 : Blo 1638018 1844869 := bbase (se 4 (by rfl) ⟨172956, by rfl⟩ : syracuseStep 1844869 = 345913) (by norm_num)
theorem B2459285 : Blo 1638018 2459285 := bbase (se 6 (by rfl) ⟨57639, by rfl⟩ : syracuseStep 2459285 = 115279) (by norm_num)
theorem B1844905 : Blo 1638018 1844905 := bbase (se 2 (by rfl) ⟨691839, by rfl⟩ : syracuseStep 1844905 = 1383679) (by norm_num)
theorem B3688109 : Blo 1638018 3688109 := bbase (se 3 (by rfl) ⟨691520, by rfl⟩ : syracuseStep 3688109 = 1383041) (by norm_num)
theorem B2459309 : Blo 1638018 2459309 := bbase (se 3 (by rfl) ⟨461120, by rfl⟩ : syracuseStep 2459309 = 922241) (by norm_num)
theorem B2459333 : Blo 1638018 2459333 := bbase (se 4 (by rfl) ⟨230562, by rfl⟩ : syracuseStep 2459333 = 461125) (by norm_num)
theorem B1844941 : Blo 1638018 1844941 := bbase (se 3 (by rfl) ⟨345926, by rfl⟩ : syracuseStep 1844941 = 691853) (by norm_num)
theorem B1754833 : Blo 1638018 1754833 := bbase (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) (by norm_num)
theorem B2459357 : Blo 1638018 2459357 := bbase (se 3 (by rfl) ⟨461129, by rfl⟩ : syracuseStep 2459357 = 922259) (by norm_num)
theorem B2074349 : Blo 1638018 2074349 := bbase (se 3 (by rfl) ⟨388940, by rfl⟩ : syracuseStep 2074349 = 777881) (by norm_num)
theorem B1844977 : Blo 1638018 1844977 := bbase (se 2 (by rfl) ⟨691866, by rfl⟩ : syracuseStep 1844977 = 1383733) (by norm_num)
theorem B5531381 : Blo 1638018 5531381 := bbase (se 5 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 5531381 = 518567) (by norm_num)
theorem B3688181 : Blo 1638018 3688181 := bbase (se 5 (by rfl) ⟨172883, by rfl⟩ : syracuseStep 3688181 = 345767) (by norm_num)
theorem B2459381 : Blo 1638018 2459381 := bbase (se 5 (by rfl) ⟨115283, by rfl⟩ : syracuseStep 2459381 = 230567) (by norm_num)
theorem B1967873 : Blo 1638018 1967873 := bbase (se 2 (by rfl) ⟨737952, by rfl⟩ : syracuseStep 1967873 = 1475905) (by norm_num)
theorem B2459405 : Blo 1638018 2459405 := bbase (se 3 (by rfl) ⟨461138, by rfl⟩ : syracuseStep 2459405 = 922277) (by norm_num)
theorem B5605141 : Blo 1638018 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B1845013 : Blo 1638018 1845013 := bbase (se 6 (by rfl) ⟨43242, by rfl⟩ : syracuseStep 1845013 = 86485) (by norm_num)
theorem B2074405 : Blo 1638018 2074405 := bbase (se 4 (by rfl) ⟨194475, by rfl⟩ : syracuseStep 2074405 = 388951) (by norm_num)
theorem B2459429 : Blo 1638018 2459429 := bbase (se 4 (by rfl) ⟨230571, by rfl⟩ : syracuseStep 2459429 = 461143) (by norm_num)
theorem B4146997 : Blo 1638018 4146997 := bbase (se 5 (by rfl) ⟨194390, by rfl⟩ : syracuseStep 4146997 = 388781) (by norm_num)
theorem B3688253 : Blo 1638018 3688253 := bbase (se 3 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 3688253 = 1383095) (by norm_num)
theorem B2459453 : Blo 1638018 2459453 := bbase (se 3 (by rfl) ⟨461147, by rfl⟩ : syracuseStep 2459453 = 922295) (by norm_num)
theorem B2459477 : Blo 1638018 2459477 := bbase (se 9 (by rfl) ⟨7205, by rfl⟩ : syracuseStep 2459477 = 14411) (by norm_num)
theorem B2459501 : Blo 1638018 2459501 := bbase (se 3 (by rfl) ⟨461156, by rfl⟩ : syracuseStep 2459501 = 922313) (by norm_num)
theorem B1967989 : Blo 1638018 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B12453749 : Blo 1638018 12453749 := bbase (se 5 (by rfl) ⟨583769, by rfl⟩ : syracuseStep 12453749 = 1167539) (by norm_num)
theorem B2074501 : Blo 1638018 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B3688325 : Blo 1638018 3688325 := bbase (se 4 (by rfl) ⟨345780, by rfl⟩ : syracuseStep 3688325 = 691561) (by norm_num)
theorem B2459525 : Blo 1638018 2459525 := bbase (se 4 (by rfl) ⟨230580, by rfl⟩ : syracuseStep 2459525 = 461161) (by norm_num)
theorem B2459549 : Blo 1638018 2459549 := bbase (se 3 (by rfl) ⟨461165, by rfl⟩ : syracuseStep 2459549 = 922331) (by norm_num)
theorem B4147109 : Blo 1638018 4147109 := bbase (se 4 (by rfl) ⟨388791, by rfl⟩ : syracuseStep 4147109 = 777583) (by norm_num)
theorem B8857525 : Blo 1638018 8857525 := bbase (se 5 (by rfl) ⟨415196, by rfl⟩ : syracuseStep 8857525 = 830393) (by norm_num)
theorem B2459573 : Blo 1638018 2459573 := bbase (se 5 (by rfl) ⟨115292, by rfl⟩ : syracuseStep 2459573 = 230585) (by norm_num)
theorem B2525117 : Blo 1638018 2525117 := bbase (se 3 (by rfl) ⟨473459, by rfl⟩ : syracuseStep 2525117 = 946919) (by norm_num)
theorem B3688397 : Blo 1638018 3688397 := bbase (se 3 (by rfl) ⟨691574, by rfl⟩ : syracuseStep 3688397 = 1383149) (by norm_num)
theorem B2459597 : Blo 1638018 2459597 := bbase (se 3 (by rfl) ⟨461174, by rfl⟩ : syracuseStep 2459597 = 922349) (by norm_num)
theorem B1894357 : Blo 1638018 1894357 := bbase (se 7 (by rfl) ⟨22199, by rfl⟩ : syracuseStep 1894357 = 44399) (by norm_num)
theorem B2459621 : Blo 1638018 2459621 := bbase (se 4 (by rfl) ⟨230589, by rfl⟩ : syracuseStep 2459621 = 461179) (by norm_num)
theorem B2459645 : Blo 1638018 2459645 := bbase (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) (by norm_num)
theorem B3688469 : Blo 1638018 3688469 := bbase (se 6 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 3688469 = 172897) (by norm_num)
theorem B2459669 : Blo 1638018 2459669 := bbase (se 6 (by rfl) ⟨57648, by rfl⟩ : syracuseStep 2459669 = 115297) (by norm_num)
theorem B29919253 : Blo 1638018 29919253 := bbase (se 6 (by rfl) ⟨701232, by rfl⟩ : syracuseStep 29919253 = 1402465) (by norm_num)
theorem B2459693 : Blo 1638018 2459693 := bbase (se 3 (by rfl) ⟨461192, by rfl⟩ : syracuseStep 2459693 = 922385) (by norm_num)
theorem B2074673 : Blo 1638018 2074673 := bbase (se 2 (by rfl) ⟨778002, by rfl⟩ : syracuseStep 2074673 = 1556005) (by norm_num)
theorem B1968185 : Blo 1638018 1968185 := bbase (se 2 (by rfl) ⟨738069, by rfl⟩ : syracuseStep 1968185 = 1476139) (by norm_num)
theorem B2459717 : Blo 1638018 2459717 := bbase (se 4 (by rfl) ⟨230598, by rfl⟩ : syracuseStep 2459717 = 461197) (by norm_num)
theorem B3688541 : Blo 1638018 3688541 := bbase (se 3 (by rfl) ⟨691601, by rfl⟩ : syracuseStep 3688541 = 1383203) (by norm_num)
theorem B2459741 : Blo 1638018 2459741 := bbase (se 3 (by rfl) ⟨461201, by rfl⟩ : syracuseStep 2459741 = 922403) (by norm_num)
theorem B4147301 : Blo 1638018 4147301 := bbase (se 4 (by rfl) ⟨388809, by rfl⟩ : syracuseStep 4147301 = 777619) (by norm_num)
theorem B2074729 : Blo 1638018 2074729 := bbase (se 2 (by rfl) ⟨778023, by rfl⟩ : syracuseStep 2074729 = 1556047) (by norm_num)
theorem B2459765 : Blo 1638018 2459765 := bbase (se 5 (by rfl) ⟨115301, by rfl⟩ : syracuseStep 2459765 = 230603) (by norm_num)
theorem B2459789 : Blo 1638018 2459789 := bbase (se 3 (by rfl) ⟨461210, by rfl⟩ : syracuseStep 2459789 = 922421) (by norm_num)
theorem B5531813 : Blo 1638018 5531813 := bbase (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) (by norm_num)
theorem B3688613 : Blo 1638018 3688613 := bbase (se 4 (by rfl) ⟨345807, by rfl⟩ : syracuseStep 3688613 = 691615) (by norm_num)
theorem B2459813 : Blo 1638018 2459813 := bbase (se 4 (by rfl) ⟨230607, by rfl⟩ : syracuseStep 2459813 = 461215) (by norm_num)
theorem B2459837 : Blo 1638018 2459837 := bbase (se 3 (by rfl) ⟨461219, by rfl⟩ : syracuseStep 2459837 = 922439) (by norm_num)
theorem B2074825 : Blo 1638018 2074825 := bbase (se 2 (by rfl) ⟨778059, by rfl⟩ : syracuseStep 2074825 = 1556119) (by norm_num)
theorem B2459861 : Blo 1638018 2459861 := bbase (se 7 (by rfl) ⟨28826, by rfl⟩ : syracuseStep 2459861 = 57653) (by norm_num)
theorem B3688685 : Blo 1638018 3688685 := bbase (se 3 (by rfl) ⟨691628, by rfl⟩ : syracuseStep 3688685 = 1383257) (by norm_num)
theorem B2459885 : Blo 1638018 2459885 := bbase (se 3 (by rfl) ⟨461228, by rfl⟩ : syracuseStep 2459885 = 922457) (by norm_num)
theorem B4983029 : Blo 1638018 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B9464053 : Blo 1638018 9464053 := bbase (se 5 (by rfl) ⟨443627, by rfl⟩ : syracuseStep 9464053 = 887255) (by norm_num)
theorem B2459909 : Blo 1638018 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B12445973 : Blo 1638018 12445973 := bbase (se 6 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 12445973 = 583405) (by norm_num)
theorem B2459933 : Blo 1638018 2459933 := bbase (se 3 (by rfl) ⟨461237, by rfl⟩ : syracuseStep 2459933 = 922475) (by norm_num)
theorem B3688757 : Blo 1638018 3688757 := bbase (se 5 (by rfl) ⟨172910, by rfl⟩ : syracuseStep 3688757 = 345821) (by norm_num)
theorem B2459957 : Blo 1638018 2459957 := bbase (se 5 (by rfl) ⟨115310, by rfl⟩ : syracuseStep 2459957 = 230621) (by norm_num)
theorem B2459981 : Blo 1638018 2459981 := bbase (se 3 (by rfl) ⟨461246, by rfl⟩ : syracuseStep 2459981 = 922493) (by norm_num)
theorem B4983125 : Blo 1638018 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B2460005 : Blo 1638018 2460005 := bbase (se 4 (by rfl) ⟨230625, by rfl⟩ : syracuseStep 2460005 = 461251) (by norm_num)
theorem B2074997 : Blo 1638018 2074997 := bbase (se 5 (by rfl) ⟨97265, by rfl⟩ : syracuseStep 2074997 = 194531) (by norm_num)
theorem B3688829 : Blo 1638018 3688829 := bbase (se 3 (by rfl) ⟨691655, by rfl⟩ : syracuseStep 3688829 = 1383311) (by norm_num)
theorem B2214317 : Blo 1638018 2214317 := bbase (se 3 (by rfl) ⟨415184, by rfl⟩ : syracuseStep 2214317 = 830369) (by norm_num)
theorem B2075053 : Blo 1638018 2075053 := bbase (se 3 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 2075053 = 778145) (by norm_num)
theorem B4147645 : Blo 1638018 4147645 := bbase (se 3 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 4147645 = 1555367) (by norm_num)
theorem B2697661 : Blo 1638018 2697661 := bbase (se 3 (by rfl) ⟨505811, by rfl⟩ : syracuseStep 2697661 = 1011623) (by norm_num)
theorem B3688901 : Blo 1638018 3688901 := bbase (se 4 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 3688901 = 691669) (by norm_num)
theorem B3369421 : Blo 1638018 3369421 := bbase (se 3 (by rfl) ⟨631766, by rfl⟩ : syracuseStep 3369421 = 1263533) (by norm_num)
theorem B3500533 : Blo 1638018 3500533 := bbase (se 5 (by rfl) ⟨164087, by rfl⟩ : syracuseStep 3500533 = 328175) (by norm_num)
theorem B3688973 : Blo 1638018 3688973 := bbase (se 3 (by rfl) ⟨691682, by rfl⟩ : syracuseStep 3688973 = 1383365) (by norm_num)
theorem B2075149 : Blo 1638018 2075149 := bbase (se 3 (by rfl) ⟨389090, by rfl⟩ : syracuseStep 2075149 = 778181) (by norm_num)
theorem B4147757 : Blo 1638018 4147757 := bbase (se 3 (by rfl) ⟨777704, by rfl⟩ : syracuseStep 4147757 = 1555409) (by norm_num)
theorem B5532245 : Blo 1638018 5532245 := bbase (se 8 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 5532245 = 64831) (by norm_num)
theorem B3689045 : Blo 1638018 3689045 := bbase (se 8 (by rfl) ⟨21615, by rfl⟩ : syracuseStep 3689045 = 43231) (by norm_num)
theorem B2624093 : Blo 1638018 2624093 := bbase (se 3 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 2624093 = 984035) (by norm_num)
theorem B1968733 : Blo 1638018 1968733 := bbase (se 3 (by rfl) ⟨369137, by rfl⟩ : syracuseStep 1968733 = 738275) (by norm_num)
theorem B3500653 : Blo 1638018 3500653 := bbase (se 3 (by rfl) ⟨656372, by rfl⟩ : syracuseStep 3500653 = 1312745) (by norm_num)
theorem B11815541 : Blo 1638018 11815541 := bbase (se 5 (by rfl) ⟨553853, by rfl⟩ : syracuseStep 11815541 = 1107707) (by norm_num)
theorem B6220421 : Blo 1638018 6220421 := bbase (se 4 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 6220421 = 1166329) (by norm_num)
theorem B8858261 : Blo 1638018 8858261 := bbase (se 6 (by rfl) ⟨207615, by rfl⟩ : syracuseStep 8858261 = 415231) (by norm_num)
theorem B3689117 : Blo 1638018 3689117 := bbase (se 3 (by rfl) ⟨691709, by rfl⟩ : syracuseStep 3689117 = 1383419) (by norm_num)
theorem B2075321 : Blo 1638018 2075321 := bbase (se 2 (by rfl) ⟨778245, by rfl⟩ : syracuseStep 2075321 = 1556491) (by norm_num)
theorem B3689189 : Blo 1638018 3689189 := bbase (se 4 (by rfl) ⟨345861, by rfl⟩ : syracuseStep 3689189 = 691723) (by norm_num)
theorem B4147949 : Blo 1638018 4147949 := bbase (se 3 (by rfl) ⟨777740, by rfl⟩ : syracuseStep 4147949 = 1555481) (by norm_num)
theorem B1968877 : Blo 1638018 1968877 := bbase (se 3 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 1968877 = 738329) (by norm_num)
theorem B2075377 : Blo 1638018 2075377 := bbase (se 2 (by rfl) ⟨778266, by rfl⟩ : syracuseStep 2075377 = 1556533) (by norm_num)
theorem B10504981 : Blo 1638018 10504981 := bbase (se 6 (by rfl) ⟨246210, by rfl⟩ : syracuseStep 10504981 = 492421) (by norm_num)
theorem B3689261 : Blo 1638018 3689261 := bbase (se 3 (by rfl) ⟨691736, by rfl⟩ : syracuseStep 3689261 = 1383473) (by norm_num)
theorem B8301365 : Blo 1638018 8301365 := bbase (se 5 (by rfl) ⟨389126, by rfl⟩ : syracuseStep 8301365 = 778253) (by norm_num)
theorem B2075473 : Blo 1638018 2075473 := bbase (se 2 (by rfl) ⟨778302, by rfl⟩ : syracuseStep 2075473 = 1556605) (by norm_num)
theorem B3500909 : Blo 1638018 3500909 := bbase (se 3 (by rfl) ⟨656420, by rfl⟩ : syracuseStep 3500909 = 1312841) (by norm_num)
theorem B3689333 : Blo 1638018 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B6220709 : Blo 1638018 6220709 := bbase (se 4 (by rfl) ⟨583191, by rfl⟩ : syracuseStep 6220709 = 1166383) (by norm_num)
theorem B5909429 : Blo 1638018 5909429 := bbase (se 5 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 5909429 = 554009) (by norm_num)
theorem B3689405 : Blo 1638018 3689405 := bbase (se 3 (by rfl) ⟨691763, by rfl⟩ : syracuseStep 3689405 = 1383527) (by norm_num)
theorem B2075645 : Blo 1638018 2075645 := bbase (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) (by norm_num)
theorem B5532677 : Blo 1638018 5532677 := bbase (se 4 (by rfl) ⟨518688, by rfl⟩ : syracuseStep 5532677 = 1037377) (by norm_num)
theorem B3689477 : Blo 1638018 3689477 := bbase (se 4 (by rfl) ⟨345888, by rfl⟩ : syracuseStep 3689477 = 691777) (by norm_num)
theorem B4148293 : Blo 1638018 4148293 := bbase (se 4 (by rfl) ⟨388902, by rfl⟩ : syracuseStep 4148293 = 777805) (by norm_num)
theorem B3689549 : Blo 1638018 3689549 := bbase (se 3 (by rfl) ⟨691790, by rfl⟩ : syracuseStep 3689549 = 1383581) (by norm_num)
theorem B2624605 : Blo 1638018 2624605 := bbase (se 3 (by rfl) ⟨492113, by rfl⟩ : syracuseStep 2624605 = 984227) (by norm_num)
theorem B3689621 : Blo 1638018 3689621 := bbase (se 6 (by rfl) ⟨86475, by rfl⟩ : syracuseStep 3689621 = 172951) (by norm_num)
theorem B4148405 : Blo 1638018 4148405 := bbase (se 5 (by rfl) ⟨194456, by rfl⟩ : syracuseStep 4148405 = 388913) (by norm_num)
theorem B8293589 : Blo 1638018 8293589 := bbase (se 7 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 8293589 = 194381) (by norm_num)
theorem B3689693 : Blo 1638018 3689693 := bbase (se 3 (by rfl) ⟨691817, by rfl⟩ : syracuseStep 3689693 = 1383635) (by norm_num)
theorem B2952445 : Blo 1638018 2952445 := bbase (se 3 (by rfl) ⟨553583, by rfl⟩ : syracuseStep 2952445 = 1107167) (by norm_num)
theorem B3689765 : Blo 1638018 3689765 := bbase (se 4 (by rfl) ⟨345915, by rfl⟩ : syracuseStep 3689765 = 691831) (by norm_num)
theorem B7875893 : Blo 1638018 7875893 := bbase (se 5 (by rfl) ⟨369182, by rfl⟩ : syracuseStep 7875893 = 738365) (by norm_num)
theorem B5606741 : Blo 1638018 5606741 := bbase (se 11 (by rfl) ⟨4106, by rfl⟩ : syracuseStep 5606741 = 8213) (by norm_num)
theorem B3689837 : Blo 1638018 3689837 := bbase (se 3 (by rfl) ⟨691844, by rfl⟩ : syracuseStep 3689837 = 1383689) (by norm_num)
theorem B4148597 : Blo 1638018 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B2764165 : Blo 1638018 2764165 := bbase (se 4 (by rfl) ⟨259140, by rfl⟩ : syracuseStep 2764165 = 518281) (by norm_num)
theorem B5533109 : Blo 1638018 5533109 := bbase (se 5 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 5533109 = 518729) (by norm_num)
theorem B3689909 : Blo 1638018 3689909 := bbase (se 5 (by rfl) ⟨172964, by rfl⟩ : syracuseStep 3689909 = 345929) (by norm_num)
theorem B2764253 : Blo 1638018 2764253 := bbase (se 3 (by rfl) ⟨518297, by rfl⟩ : syracuseStep 2764253 = 1036595) (by norm_num)
theorem B3689981 : Blo 1638018 3689981 := bbase (se 3 (by rfl) ⟨691871, by rfl⟩ : syracuseStep 3689981 = 1383743) (by norm_num)
theorem B2993669 : Blo 1638018 2993669 := bbase (se 4 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 2993669 = 561313) (by norm_num)
theorem B29888021 : Blo 1638018 29888021 := bbase (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) (by norm_num)
theorem B2952733 : Blo 1638018 2952733 := bbase (se 3 (by rfl) ⟨553637, by rfl⟩ : syracuseStep 2952733 = 1107275) (by norm_num)
theorem B2625061 : Blo 1638018 2625061 := bbase (se 4 (by rfl) ⟨246099, by rfl⟩ : syracuseStep 2625061 = 492199) (by norm_num)
theorem B2764381 : Blo 1638018 2764381 := bbase (se 3 (by rfl) ⟨518321, by rfl⟩ : syracuseStep 2764381 = 1036643) (by norm_num)
theorem B2215549 : Blo 1638018 2215549 := bbase (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) (by norm_num)
theorem B2764469 : Blo 1638018 2764469 := bbase (se 5 (by rfl) ⟨129584, by rfl⟩ : syracuseStep 2764469 = 259169) (by norm_num)
theorem B1683149 : Blo 1638018 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B4148941 : Blo 1638018 4148941 := bbase (se 3 (by rfl) ⟨777926, by rfl⟩ : syracuseStep 4148941 = 1555853) (by norm_num)
theorem B3501797 : Blo 1638018 3501797 := bbase (se 4 (by rfl) ⟨328293, by rfl⟩ : syracuseStep 3501797 = 656587) (by norm_num)
theorem B4665077 : Blo 1638018 4665077 := bbase (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) (by norm_num)
theorem B3321605 : Blo 1638018 3321605 := bbase (se 4 (by rfl) ⟨311400, by rfl⟩ : syracuseStep 3321605 = 622801) (by norm_num)
theorem B1969925 : Blo 1638018 1969925 := bbase (se 4 (by rfl) ⟨184680, by rfl⟩ : syracuseStep 1969925 = 369361) (by norm_num)
theorem B2764597 : Blo 1638018 2764597 := bbase (se 5 (by rfl) ⟨129590, by rfl⟩ : syracuseStep 2764597 = 259181) (by norm_num)
theorem B4149053 : Blo 1638018 4149053 := bbase (se 3 (by rfl) ⟨777947, by rfl⟩ : syracuseStep 4149053 = 1555895) (by norm_num)
theorem B5533541 : Blo 1638018 5533541 := bbase (se 4 (by rfl) ⟨518769, by rfl⟩ : syracuseStep 5533541 = 1037539) (by norm_num)
theorem B2764685 : Blo 1638018 2764685 := bbase (se 3 (by rfl) ⟨518378, by rfl⟩ : syracuseStep 2764685 = 1036757) (by norm_num)
theorem B9334709 : Blo 1638018 9334709 := bbase (se 5 (by rfl) ⟨437564, by rfl⟩ : syracuseStep 9334709 = 875129) (by norm_num)
theorem B3502037 : Blo 1638018 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B4149245 : Blo 1638018 4149245 := bbase (se 3 (by rfl) ⟨777983, by rfl⟩ : syracuseStep 4149245 = 1555967) (by norm_num)
theorem B2764813 : Blo 1638018 2764813 := bbase (se 3 (by rfl) ⟨518402, by rfl⟩ : syracuseStep 2764813 = 1036805) (by norm_num)
theorem B3936293 : Blo 1638018 3936293 := bbase (se 4 (by rfl) ⟨369027, by rfl⟩ : syracuseStep 3936293 = 738055) (by norm_num)
theorem B6221893 : Blo 1638018 6221893 := bbase (se 4 (by rfl) ⟨583302, by rfl⟩ : syracuseStep 6221893 = 1166605) (by norm_num)
theorem B2764901 : Blo 1638018 2764901 := bbase (se 4 (by rfl) ⟨259209, by rfl⟩ : syracuseStep 2764901 = 518419) (by norm_num)
theorem B4427941 : Blo 1638018 4427941 := bbase (se 4 (by rfl) ⟨415119, by rfl⟩ : syracuseStep 4427941 = 830239) (by norm_num)
theorem B4665509 : Blo 1638018 4665509 := bbase (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) (by norm_num)
theorem B2625733 : Blo 1638018 2625733 := bbase (se 4 (by rfl) ⟨246162, by rfl⟩ : syracuseStep 2625733 = 492325) (by norm_num)
theorem B2765029 : Blo 1638018 2765029 := bbase (se 4 (by rfl) ⟨259221, by rfl⟩ : syracuseStep 2765029 = 518443) (by norm_num)
theorem B1749233 : Blo 1638018 1749233 := bbase (se 2 (by rfl) ⟨655962, by rfl⟩ : syracuseStep 1749233 = 1311925) (by norm_num)
theorem B5533973 : Blo 1638018 5533973 := bbase (se 6 (by rfl) ⟨129702, by rfl⟩ : syracuseStep 5533973 = 259405) (by norm_num)
theorem B2765117 : Blo 1638018 2765117 := bbase (se 3 (by rfl) ⟨518459, by rfl⟩ : syracuseStep 2765117 = 1036919) (by norm_num)
theorem B75657557 : Blo 1638018 75657557 := bbase (se 10 (by rfl) ⟨110826, by rfl⟩ : syracuseStep 75657557 = 221653) (by norm_num)
theorem B4149589 : Blo 1638018 4149589 := bbase (se 10 (by rfl) ⟨6078, by rfl⟩ : syracuseStep 4149589 = 12157) (by norm_num)
theorem B1749361 : Blo 1638018 1749361 := bbase (se 2 (by rfl) ⟨656010, by rfl⟩ : syracuseStep 1749361 = 1312021) (by norm_num)
theorem B6222197 : Blo 1638018 6222197 := bbase (se 5 (by rfl) ⟨291665, by rfl⟩ : syracuseStep 6222197 = 583331) (by norm_num)
theorem B2765245 : Blo 1638018 2765245 := bbase (se 3 (by rfl) ⟨518483, by rfl⟩ : syracuseStep 2765245 = 1036967) (by norm_num)
theorem B4149701 : Blo 1638018 4149701 := bbase (se 4 (by rfl) ⟨389034, by rfl⟩ : syracuseStep 4149701 = 778069) (by norm_num)
theorem B3502541 : Blo 1638018 3502541 := bbase (se 3 (by rfl) ⟨656726, by rfl⟩ : syracuseStep 3502541 = 1313453) (by norm_num)
theorem B3502549 : Blo 1638018 3502549 := bbase (se 7 (by rfl) ⟨41045, by rfl⟩ : syracuseStep 3502549 = 82091) (by norm_num)
theorem B8294885 : Blo 1638018 8294885 := bbase (se 4 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 8294885 = 1555291) (by norm_num)
theorem B2765333 : Blo 1638018 2765333 := bbase (se 6 (by rfl) ⟨64812, by rfl⟩ : syracuseStep 2765333 = 129625) (by norm_num)
theorem B1684069 : Blo 1638018 1684069 := bbase (se 4 (by rfl) ⟨157881, by rfl⟩ : syracuseStep 1684069 = 315763) (by norm_num)
theorem B2953829 : Blo 1638018 2953829 := bbase (se 4 (by rfl) ⟨276921, by rfl⟩ : syracuseStep 2953829 = 553843) (by norm_num)
theorem B2626157 : Blo 1638018 2626157 := bbase (se 3 (by rfl) ⟨492404, by rfl⟩ : syracuseStep 2626157 = 984809) (by norm_num)
theorem B4149893 : Blo 1638018 4149893 := bbase (se 4 (by rfl) ⟨389052, by rfl⟩ : syracuseStep 4149893 = 778105) (by norm_num)
theorem B2765461 : Blo 1638018 2765461 := bbase (se 6 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 2765461 = 129631) (by norm_num)
theorem B5534405 : Blo 1638018 5534405 := bbase (se 4 (by rfl) ⟨518850, by rfl⟩ : syracuseStep 5534405 = 1037701) (by norm_num)
theorem B1774285 : Blo 1638018 1774285 := bbase (se 3 (by rfl) ⟨332678, by rfl⟩ : syracuseStep 1774285 = 665357) (by norm_num)
theorem B2765549 : Blo 1638018 2765549 := bbase (se 3 (by rfl) ⟨518540, by rfl⟩ : syracuseStep 2765549 = 1037081) (by norm_num)
theorem B1749805 : Blo 1638018 1749805 := bbase (se 3 (by rfl) ⟨328088, by rfl⟩ : syracuseStep 1749805 = 656177) (by norm_num)
theorem B2765677 : Blo 1638018 2765677 := bbase (se 3 (by rfl) ⟨518564, by rfl⟩ : syracuseStep 2765677 = 1037129) (by norm_num)
theorem B2626445 : Blo 1638018 2626445 := bbase (se 3 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 2626445 = 984917) (by norm_num)
theorem B4666261 : Blo 1638018 4666261 := bbase (se 6 (by rfl) ⟨109365, by rfl⟩ : syracuseStep 4666261 = 218731) (by norm_num)
theorem B1749925 : Blo 1638018 1749925 := bbase (se 4 (by rfl) ⟨164055, by rfl⟩ : syracuseStep 1749925 = 328111) (by norm_num)
theorem B14193589 : Blo 1638018 14193589 := bbase (se 5 (by rfl) ⟨665324, by rfl⟩ : syracuseStep 14193589 = 1330649) (by norm_num)
theorem B2765765 : Blo 1638018 2765765 := bbase (se 4 (by rfl) ⟨259290, by rfl⟩ : syracuseStep 2765765 = 518581) (by norm_num)
theorem B3109853 : Blo 1638018 3109853 := bbase (se 3 (by rfl) ⟨583097, by rfl⟩ : syracuseStep 3109853 = 1166195) (by norm_num)
theorem B4150237 : Blo 1638018 4150237 := bbase (se 3 (by rfl) ⟨778169, by rfl⟩ : syracuseStep 4150237 = 1556339) (by norm_num)
theorem B2765893 : Blo 1638018 2765893 := bbase (se 4 (by rfl) ⟨259302, by rfl⟩ : syracuseStep 2765893 = 518605) (by norm_num)
theorem B4150349 : Blo 1638018 4150349 := bbase (se 3 (by rfl) ⟨778190, by rfl⟩ : syracuseStep 4150349 = 1556381) (by norm_num)
theorem B8983637 : Blo 1638018 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B3110005 : Blo 1638018 3110005 := bbase (se 5 (by rfl) ⟨145781, by rfl⟩ : syracuseStep 3110005 = 291563) (by norm_num)
theorem B5534837 : Blo 1638018 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B2765981 : Blo 1638018 2765981 := bbase (se 3 (by rfl) ⟨518621, by rfl⟩ : syracuseStep 2765981 = 1037243) (by norm_num)
theorem B1750177 : Blo 1638018 1750177 := bbase (se 2 (by rfl) ⟨656316, by rfl⟩ : syracuseStep 1750177 = 1312633) (by norm_num)
theorem B1750181 : Blo 1638018 1750181 := bbase (se 4 (by rfl) ⟨164079, by rfl⟩ : syracuseStep 1750181 = 328159) (by norm_num)
theorem B4150541 : Blo 1638018 4150541 := bbase (se 3 (by rfl) ⟨778226, by rfl⟩ : syracuseStep 4150541 = 1556453) (by norm_num)
theorem B5248277 : Blo 1638018 5248277 := bbase (se 6 (by rfl) ⟨123006, by rfl⟩ : syracuseStep 5248277 = 246013) (by norm_num)
theorem B18666773 : Blo 1638018 18666773 := bbase (se 6 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 18666773 = 875005) (by norm_num)
theorem B1996061 : Blo 1638018 1996061 := bbase (se 3 (by rfl) ⟨374261, by rfl⟩ : syracuseStep 1996061 = 748523) (by norm_num)
theorem B2766109 : Blo 1638018 2766109 := bbase (se 3 (by rfl) ⟨518645, by rfl⟩ : syracuseStep 2766109 = 1037291) (by norm_num)
theorem B2766197 : Blo 1638018 2766197 := bbase (se 5 (by rfl) ⟨129665, by rfl⟩ : syracuseStep 2766197 = 259331) (by norm_num)
theorem B7001477 : Blo 1638018 7001477 := bbase (se 4 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 7001477 = 1312777) (by norm_num)
theorem B3110309 : Blo 1638018 3110309 := bbase (se 4 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 3110309 = 583183) (by norm_num)
theorem B2766325 : Blo 1638018 2766325 := bbase (se 5 (by rfl) ⟨129671, by rfl⟩ : syracuseStep 2766325 = 259343) (by norm_num)
theorem B2766413 : Blo 1638018 2766413 := bbase (se 3 (by rfl) ⟨518702, by rfl⟩ : syracuseStep 2766413 = 1037405) (by norm_num)
theorem B4150885 : Blo 1638018 4150885 := bbase (se 4 (by rfl) ⟨389145, by rfl⟩ : syracuseStep 4150885 = 778291) (by norm_num)
theorem B2766541 : Blo 1638018 2766541 := bbase (se 3 (by rfl) ⟨518726, by rfl⟩ : syracuseStep 2766541 = 1037453) (by norm_num)
theorem B4150997 : Blo 1638018 4150997 := bbase (se 7 (by rfl) ⟨48644, by rfl⟩ : syracuseStep 4150997 = 97289) (by norm_num)
theorem B1750745 : Blo 1638018 1750745 := bbase (se 2 (by rfl) ⟨656529, by rfl⟩ : syracuseStep 1750745 = 1313059) (by norm_num)
theorem B4429541 : Blo 1638018 4429541 := bbase (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) (by norm_num)
theorem B1996529 : Blo 1638018 1996529 := bbase (se 2 (by rfl) ⟨748698, by rfl⟩ : syracuseStep 1996529 = 1497397) (by norm_num)
theorem B8296181 : Blo 1638018 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B3938053 : Blo 1638018 3938053 := bbase (se 4 (by rfl) ⟨369192, by rfl⟩ : syracuseStep 3938053 = 738385) (by norm_num)
theorem B27997973 : Blo 1638018 27997973 := bbase (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) (by norm_num)
theorem B2766629 : Blo 1638018 2766629 := bbase (se 4 (by rfl) ⟨259371, by rfl⟩ : syracuseStep 2766629 = 518743) (by norm_num)
theorem B2955133 : Blo 1638018 2955133 := bbase (se 3 (by rfl) ⟨554087, by rfl⟩ : syracuseStep 2955133 = 1108175) (by norm_num)
theorem B1750933 : Blo 1638018 1750933 := bbase (se 6 (by rfl) ⟨41037, by rfl⟩ : syracuseStep 1750933 = 82075) (by norm_num)
theorem B4151189 : Blo 1638018 4151189 := bbase (se 6 (by rfl) ⟨97293, by rfl⟩ : syracuseStep 4151189 = 194587) (by norm_num)
theorem B2766757 : Blo 1638018 2766757 := bbase (se 4 (by rfl) ⟨259383, by rfl⟩ : syracuseStep 2766757 = 518767) (by norm_num)
theorem B16816085 : Blo 1638018 16816085 := bbase (se 7 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 16816085 = 394127) (by norm_num)
theorem B13293557 : Blo 1638018 13293557 := bbase (se 5 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 13293557 = 1246271) (by norm_num)
theorem B2766845 : Blo 1638018 2766845 := bbase (se 3 (by rfl) ⟨518783, by rfl⟩ : syracuseStep 2766845 = 1037567) (by norm_num)
theorem B1660997 : Blo 1638018 1660997 := bbase (se 4 (by rfl) ⟨155718, by rfl⟩ : syracuseStep 1660997 = 311437) (by norm_num)
theorem B2766973 : Blo 1638018 2766973 := bbase (se 3 (by rfl) ⟨518807, by rfl⟩ : syracuseStep 2766973 = 1037615) (by norm_num)
theorem B3111061 : Blo 1638018 3111061 := bbase (se 6 (by rfl) ⟨72915, by rfl⟩ : syracuseStep 3111061 = 145831) (by norm_num)
theorem B6305957 : Blo 1638018 6305957 := bbase (se 4 (by rfl) ⟨591183, by rfl⟩ : syracuseStep 6305957 = 1182367) (by norm_num)
theorem B2767061 : Blo 1638018 2767061 := bbase (se 7 (by rfl) ⟨32426, by rfl⟩ : syracuseStep 2767061 = 64853) (by norm_num)
theorem B12613877 : Blo 1638018 12613877 := bbase (se 5 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 12613877 = 1182551) (by norm_num)
theorem B3111205 : Blo 1638018 3111205 := bbase (se 4 (by rfl) ⟨291675, by rfl⟩ : syracuseStep 3111205 = 583351) (by norm_num)
theorem B1661249 : Blo 1638018 1661249 := bbase (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) (by norm_num)
theorem B2103617 : Blo 1638018 2103617 := bbase (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) (by norm_num)
theorem B2767189 : Blo 1638018 2767189 := bbase (se 10 (by rfl) ⟨4053, by rfl⟩ : syracuseStep 2767189 = 8107) (by norm_num)
theorem B3938669 : Blo 1638018 3938669 := bbase (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) (by norm_num)
theorem B2767277 : Blo 1638018 2767277 := bbase (se 3 (by rfl) ⟨518864, by rfl⟩ : syracuseStep 2767277 = 1037729) (by norm_num)
theorem B6224309 : Blo 1638018 6224309 := bbase (se 5 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 6224309 = 583529) (by norm_num)
theorem B3111365 : Blo 1638018 3111365 := bbase (se 4 (by rfl) ⟨291690, by rfl⟩ : syracuseStep 3111365 = 583381) (by norm_num)
theorem B2103833 : Blo 1638018 2103833 := bbase (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) (by norm_num)
theorem B2767405 : Blo 1638018 2767405 := bbase (se 3 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 2767405 = 1037777) (by norm_num)
theorem B3111509 : Blo 1638018 3111509 := bbase (se 8 (by rfl) ⟨18231, by rfl⟩ : syracuseStep 3111509 = 36463) (by norm_num)
theorem B14195317 : Blo 1638018 14195317 := bbase (se 5 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 14195317 = 1330811) (by norm_num)
theorem B2767493 : Blo 1638018 2767493 := bbase (se 4 (by rfl) ⟨259452, by rfl⟩ : syracuseStep 2767493 = 518905) (by norm_num)
theorem B3324557 : Blo 1638018 3324557 := bbase (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) (by norm_num)
theorem B6224597 : Blo 1638018 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B2333461 : Blo 1638018 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B5528357 : Blo 1638018 5528357 := bbase (se 4 (by rfl) ⟨518283, by rfl⟩ : syracuseStep 5528357 = 1036567) (by norm_num)
theorem B3111797 : Blo 1638018 3111797 := bbase (se 5 (by rfl) ⟨145865, by rfl⟩ : syracuseStep 3111797 = 291731) (by norm_num)
theorem B8297477 : Blo 1638018 8297477 := bbase (se 4 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 8297477 = 1555777) (by norm_num)
theorem B3111949 : Blo 1638018 3111949 := bbase (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) (by norm_num)
theorem B7871509 : Blo 1638018 7871509 := bbase (se 6 (by rfl) ⟨184488, by rfl⟩ : syracuseStep 7871509 = 368977) (by norm_num)
theorem B5905477 : Blo 1638018 5905477 := bbase (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) (by norm_num)
theorem B5250133 : Blo 1638018 5250133 := bbase (se 8 (by rfl) ⟨30762, by rfl⟩ : syracuseStep 5250133 = 61525) (by norm_num)
theorem B3939437 : Blo 1638018 3939437 := bbase (se 3 (by rfl) ⟨738644, by rfl⟩ : syracuseStep 3939437 = 1477289) (by norm_num)
theorem B7003253 : Blo 1638018 7003253 := bbase (se 5 (by rfl) ⟨328277, by rfl⟩ : syracuseStep 7003253 = 656555) (by norm_num)
theorem B3939445 : Blo 1638018 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B11820181 : Blo 1638018 11820181 := bbase (se 6 (by rfl) ⟨277035, by rfl⟩ : syracuseStep 11820181 = 554071) (by norm_num)
theorem B1662157 : Blo 1638018 1662157 := bbase (se 3 (by rfl) ⟨311654, by rfl⟩ : syracuseStep 1662157 = 623309) (by norm_num)
theorem B3685589 : Blo 1638018 3685589 := bbase (se 7 (by rfl) ⟨43190, by rfl⟩ : syracuseStep 3685589 = 86381) (by norm_num)
theorem B5528789 : Blo 1638018 5528789 := bbase (se 7 (by rfl) ⟨64790, by rfl⟩ : syracuseStep 5528789 = 129581) (by norm_num)
theorem B2276573 : Blo 1638018 2276573 := bbase (se 3 (by rfl) ⟨426857, by rfl⟩ : syracuseStep 2276573 = 853715) (by norm_num)
theorem B3685661 : Blo 1638018 3685661 := bbase (se 3 (by rfl) ⟨691061, by rfl⟩ : syracuseStep 3685661 = 1382123) (by norm_num)
theorem B3112253 : Blo 1638018 3112253 := bbase (se 3 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 3112253 = 1167095) (by norm_num)
theorem B3685733 : Blo 1638018 3685733 := bbase (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) (by norm_num)
theorem B2334053 : Blo 1638018 2334053 := bbase (se 4 (by rfl) ⟨218817, by rfl⟩ : syracuseStep 2334053 = 437635) (by norm_num)
theorem B7003493 : Blo 1638018 7003493 := bbase (se 4 (by rfl) ⟨656577, by rfl⟩ : syracuseStep 7003493 = 1313155) (by norm_num)
theorem B3685805 : Blo 1638018 3685805 := bbase (se 3 (by rfl) ⟨691088, by rfl⟩ : syracuseStep 3685805 = 1382177) (by norm_num)
theorem B2334133 : Blo 1638018 2334133 := bbase (se 5 (by rfl) ⟨109412, by rfl⟩ : syracuseStep 2334133 = 218825) (by norm_num)
theorem B2457029 : Blo 1638018 2457029 := bbase (se 4 (by rfl) ⟨230346, by rfl⟩ : syracuseStep 2457029 = 460693) (by norm_num)
theorem B2457053 : Blo 1638018 2457053 := bbase (se 3 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 2457053 = 921395) (by norm_num)
theorem B2457077 : Blo 1638018 2457077 := bbase (se 5 (by rfl) ⟨115175, by rfl⟩ : syracuseStep 2457077 = 230351) (by norm_num)
theorem B3685877 : Blo 1638018 3685877 := bbase (se 5 (by rfl) ⟨172775, by rfl⟩ : syracuseStep 3685877 = 345551) (by norm_num)
theorem B2457101 : Blo 1638018 2457101 := bbase (se 3 (by rfl) ⟨460706, by rfl⟩ : syracuseStep 2457101 = 921413) (by norm_num)
theorem B2457125 : Blo 1638018 2457125 := bbase (se 4 (by rfl) ⟨230355, by rfl⟩ : syracuseStep 2457125 = 460711) (by norm_num)
theorem B2334253 : Blo 1638018 2334253 := bbase (se 3 (by rfl) ⟨437672, by rfl⟩ : syracuseStep 2334253 = 875345) (by norm_num)
theorem B10649141 : Blo 1638018 10649141 := bbase (se 5 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 10649141 = 998357) (by norm_num)
theorem B2457149 : Blo 1638018 2457149 := bbase (se 3 (by rfl) ⟨460715, by rfl⟩ : syracuseStep 2457149 = 921431) (by norm_num)
theorem B3685949 : Blo 1638018 3685949 := bbase (se 3 (by rfl) ⟨691115, by rfl⟩ : syracuseStep 3685949 = 1382231) (by norm_num)
theorem B2457173 : Blo 1638018 2457173 := bbase (se 8 (by rfl) ⟨14397, by rfl⟩ : syracuseStep 2457173 = 28795) (by norm_num)
theorem B1842781 : Blo 1638018 1842781 := bbase (se 3 (by rfl) ⟨345521, by rfl⟩ : syracuseStep 1842781 = 691043) (by norm_num)
theorem B2457197 : Blo 1638018 2457197 := bbase (se 3 (by rfl) ⟨460724, by rfl⟩ : syracuseStep 2457197 = 921449) (by norm_num)
theorem B1842817 : Blo 1638018 1842817 := bbase (se 2 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 1842817 = 1382113) (by norm_num)
theorem B2457221 : Blo 1638018 2457221 := bbase (se 4 (by rfl) ⟨230364, by rfl⟩ : syracuseStep 2457221 = 460729) (by norm_num)
theorem B3686021 : Blo 1638018 3686021 := bbase (se 4 (by rfl) ⟨345564, by rfl⟩ : syracuseStep 3686021 = 691129) (by norm_num)
theorem B5529221 : Blo 1638018 5529221 := bbase (se 4 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 5529221 = 1036729) (by norm_num)
theorem B2662021 : Blo 1638018 2662021 := bbase (se 4 (by rfl) ⟨249564, by rfl⟩ : syracuseStep 2662021 = 499129) (by norm_num)
theorem B2334349 : Blo 1638018 2334349 := bbase (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) (by norm_num)
theorem B8412821 : Blo 1638018 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B2457245 : Blo 1638018 2457245 := bbase (se 3 (by rfl) ⟨460733, by rfl⟩ : syracuseStep 2457245 = 921467) (by norm_num)
theorem B1842853 : Blo 1638018 1842853 := bbase (se 4 (by rfl) ⟨172767, by rfl⟩ : syracuseStep 1842853 = 345535) (by norm_num)
theorem B2457269 : Blo 1638018 2457269 := bbase (se 5 (by rfl) ⟨115184, by rfl⟩ : syracuseStep 2457269 = 230369) (by norm_num)
theorem B4669109 : Blo 1638018 4669109 := bbase (se 5 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 4669109 = 437729) (by norm_num)
theorem B1842889 : Blo 1638018 1842889 := bbase (se 2 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 1842889 = 1382167) (by norm_num)
theorem B2457293 : Blo 1638018 2457293 := bbase (se 3 (by rfl) ⟨460742, by rfl⟩ : syracuseStep 2457293 = 921485) (by norm_num)
theorem B3686093 : Blo 1638018 3686093 := bbase (se 3 (by rfl) ⟨691142, by rfl⟩ : syracuseStep 3686093 = 1382285) (by norm_num)
theorem B2457317 : Blo 1638018 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B1842925 : Blo 1638018 1842925 := bbase (se 3 (by rfl) ⟨345548, by rfl⟩ : syracuseStep 1842925 = 691097) (by norm_num)
theorem B2244341 : Blo 1638018 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B2457341 : Blo 1638018 2457341 := bbase (se 3 (by rfl) ⟨460751, by rfl⟩ : syracuseStep 2457341 = 921503) (by norm_num)
theorem B1842961 : Blo 1638018 1842961 := bbase (se 2 (by rfl) ⟨691110, by rfl⟩ : syracuseStep 1842961 = 1382221) (by norm_num)
theorem B2457365 : Blo 1638018 2457365 := bbase (se 6 (by rfl) ⟨57594, by rfl⟩ : syracuseStep 2457365 = 115189) (by norm_num)
theorem B3686165 : Blo 1638018 3686165 := bbase (se 6 (by rfl) ⟨86394, by rfl⟩ : syracuseStep 3686165 = 172789) (by norm_num)
theorem B2457389 : Blo 1638018 2457389 := bbase (se 3 (by rfl) ⟨460760, by rfl⟩ : syracuseStep 2457389 = 921521) (by norm_num)
theorem B1842997 : Blo 1638018 1842997 := bbase (se 5 (by rfl) ⟨86390, by rfl⟩ : syracuseStep 1842997 = 172781) (by norm_num)
theorem B2457413 : Blo 1638018 2457413 := bbase (se 4 (by rfl) ⟨230382, by rfl⟩ : syracuseStep 2457413 = 460765) (by norm_num)
theorem B1843033 : Blo 1638018 1843033 := bbase (se 2 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 1843033 = 1382275) (by norm_num)
theorem B2457437 : Blo 1638018 2457437 := bbase (se 3 (by rfl) ⟨460769, by rfl⟩ : syracuseStep 2457437 = 921539) (by norm_num)
theorem B3686237 : Blo 1638018 3686237 := bbase (se 3 (by rfl) ⟨691169, by rfl⟩ : syracuseStep 3686237 = 1382339) (by norm_num)
theorem B2457461 : Blo 1638018 2457461 := bbase (se 5 (by rfl) ⟨115193, by rfl⟩ : syracuseStep 2457461 = 230387) (by norm_num)
theorem B6225781 : Blo 1638018 6225781 := bbase (se 5 (by rfl) ⟨291833, by rfl⟩ : syracuseStep 6225781 = 583667) (by norm_num)
theorem B1843069 : Blo 1638018 1843069 := bbase (se 3 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 1843069 = 691151) (by norm_num)
theorem B7880581 : Blo 1638018 7880581 := bbase (se 4 (by rfl) ⟨738804, by rfl⟩ : syracuseStep 7880581 = 1477609) (by norm_num)
theorem B2457485 : Blo 1638018 2457485 := bbase (se 3 (by rfl) ⟨460778, by rfl⟩ : syracuseStep 2457485 = 921557) (by norm_num)
theorem B3940253 : Blo 1638018 3940253 := bbase (se 3 (by rfl) ⟨738797, by rfl⟩ : syracuseStep 3940253 = 1477595) (by norm_num)
theorem B1843105 : Blo 1638018 1843105 := bbase (se 2 (by rfl) ⟨691164, by rfl⟩ : syracuseStep 1843105 = 1382329) (by norm_num)
theorem B2457509 : Blo 1638018 2457509 := bbase (se 4 (by rfl) ⟨230391, by rfl⟩ : syracuseStep 2457509 = 460783) (by norm_num)
theorem B3686309 : Blo 1638018 3686309 := bbase (se 4 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 3686309 = 691183) (by norm_num)
theorem B2457533 : Blo 1638018 2457533 := bbase (se 3 (by rfl) ⟨460787, by rfl⟩ : syracuseStep 2457533 = 921575) (by norm_num)
theorem B1843141 : Blo 1638018 1843141 := bbase (se 4 (by rfl) ⟨172794, by rfl⟩ : syracuseStep 1843141 = 345589) (by norm_num)
theorem B2457557 : Blo 1638018 2457557 := bbase (se 7 (by rfl) ⟨28799, by rfl⟩ : syracuseStep 2457557 = 57599) (by norm_num)
theorem B2842589 : Blo 1638018 2842589 := bbase (se 3 (by rfl) ⟨532985, by rfl⟩ : syracuseStep 2842589 = 1065971) (by norm_num)
theorem B1843177 : Blo 1638018 1843177 := bbase (se 2 (by rfl) ⟨691191, by rfl⟩ : syracuseStep 1843177 = 1382383) (by norm_num)
theorem B2457581 : Blo 1638018 2457581 := bbase (se 3 (by rfl) ⟨460796, by rfl⟩ : syracuseStep 2457581 = 921593) (by norm_num)
theorem B3686381 : Blo 1638018 3686381 := bbase (se 3 (by rfl) ⟨691196, by rfl⟩ : syracuseStep 3686381 = 1382393) (by norm_num)
theorem B9109493 : Blo 1638018 9109493 := bbase (se 5 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 9109493 = 854015) (by norm_num)
theorem B1638403 : Blo 1638018 1638403 := bstep (se 1 (by rfl) ⟨1228802, by rfl⟩ : syracuseStep 1638403 = 2457605) B2457605
theorem B3686417 : Blo 1638018 3686417 := bstep (se 2 (by rfl) ⟨1382406, by rfl⟩ : syracuseStep 3686417 = 2764813) B2764813
theorem B2457617 : Blo 1638018 2457617 := bstep (se 2 (by rfl) ⟨921606, by rfl⟩ : syracuseStep 2457617 = 1843213) B1843213
theorem B1638419 : Blo 1638018 1638419 := bstep (se 1 (by rfl) ⟨1228814, by rfl⟩ : syracuseStep 1638419 = 2457629) B2457629
theorem B3686435 : Blo 1638018 3686435 := bstep (se 1 (by rfl) ⟨2764826, by rfl⟩ : syracuseStep 3686435 = 5529653) B5529653
theorem B2457635 : Blo 1638018 2457635 := bstep (se 1 (by rfl) ⟨1843226, by rfl⟩ : syracuseStep 2457635 = 3686453) B3686453
theorem B1638435 : Blo 1638018 1638435 := bstep (se 1 (by rfl) ⟨1228826, by rfl⟩ : syracuseStep 1638435 = 2457653) B2457653
theorem B1638451 : Blo 1638018 1638451 := bstep (se 1 (by rfl) ⟨1228838, by rfl⟩ : syracuseStep 1638451 = 2457677) B2457677
theorem B2457665 : Blo 1638018 2457665 := bstep (se 2 (by rfl) ⟨921624, by rfl⟩ : syracuseStep 2457665 = 1843249) B1843249
theorem B1843267 : Blo 1638018 1843267 := bstep (se 1 (by rfl) ⟨1382450, by rfl⟩ : syracuseStep 1843267 = 2764901) B2764901
theorem B1638467 : Blo 1638018 1638467 := bstep (se 1 (by rfl) ⟨1228850, by rfl⟩ : syracuseStep 1638467 = 2457701) B2457701
theorem B2457683 : Blo 1638018 2457683 := bstep (se 1 (by rfl) ⟨1843262, by rfl⟩ : syracuseStep 2457683 = 3686525) B3686525
theorem B1638483 : Blo 1638018 1638483 := bstep (se 1 (by rfl) ⟨1228862, by rfl⟩ : syracuseStep 1638483 = 2457725) B2457725
theorem B1638499 : Blo 1638018 1638499 := bstep (se 1 (by rfl) ⟨1228874, by rfl⟩ : syracuseStep 1638499 = 2457749) B2457749
theorem B2457713 : Blo 1638018 2457713 := bstep (se 2 (by rfl) ⟨921642, by rfl⟩ : syracuseStep 2457713 = 1843285) B1843285
theorem B1638515 : Blo 1638018 1638515 := bstep (se 1 (by rfl) ⟨1228886, by rfl⟩ : syracuseStep 1638515 = 2457773) B2457773
theorem B2457731 : Blo 1638018 2457731 := bstep (se 1 (by rfl) ⟨1843298, by rfl⟩ : syracuseStep 2457731 = 3686597) B3686597
theorem B1638531 : Blo 1638018 1638531 := bstep (se 1 (by rfl) ⟨1228898, by rfl⟩ : syracuseStep 1638531 = 2457797) B2457797
theorem B1638547 : Blo 1638018 1638547 := bstep (se 1 (by rfl) ⟨1228910, by rfl⟩ : syracuseStep 1638547 = 2457821) B2457821
theorem B2457761 : Blo 1638018 2457761 := bstep (se 2 (by rfl) ⟨921660, by rfl⟩ : syracuseStep 2457761 = 1843321) B1843321
theorem B1638563 : Blo 1638018 1638563 := bstep (se 1 (by rfl) ⟨1228922, by rfl⟩ : syracuseStep 1638563 = 2457845) B2457845
theorem B2457779 : Blo 1638018 2457779 := bstep (se 1 (by rfl) ⟨1843334, by rfl⟩ : syracuseStep 2457779 = 3686669) B3686669
theorem B1638579 : Blo 1638018 1638579 := bstep (se 1 (by rfl) ⟨1228934, by rfl⟩ : syracuseStep 1638579 = 2457869) B2457869
theorem B1638595 : Blo 1638018 1638595 := bstep (se 1 (by rfl) ⟨1228946, by rfl⟩ : syracuseStep 1638595 = 2457893) B2457893
theorem B2457809 : Blo 1638018 2457809 := bstep (se 2 (by rfl) ⟨921678, by rfl⟩ : syracuseStep 2457809 = 1843357) B1843357
theorem B1843411 : Blo 1638018 1843411 := bstep (se 1 (by rfl) ⟨1382558, by rfl⟩ : syracuseStep 1843411 = 2765117) B2765117
theorem B1638611 : Blo 1638018 1638611 := bstep (se 1 (by rfl) ⟨1228958, by rfl⟩ : syracuseStep 1638611 = 2457917) B2457917
theorem B50438371 : Blo 1638018 50438371 := bstep (se 1 (by rfl) ⟨37828778, by rfl⟩ : syracuseStep 50438371 = 75657557) B75657557
theorem B2457827 : Blo 1638018 2457827 := bstep (se 1 (by rfl) ⟨1843370, by rfl⟩ : syracuseStep 2457827 = 3686741) B3686741
theorem B1638627 : Blo 1638018 1638627 := bstep (se 1 (by rfl) ⟨1228970, by rfl⟩ : syracuseStep 1638627 = 2457941) B2457941
theorem B1638643 : Blo 1638018 1638643 := bstep (se 1 (by rfl) ⟨1228982, by rfl⟩ : syracuseStep 1638643 = 2457965) B2457965
theorem B2457857 : Blo 1638018 2457857 := bstep (se 2 (by rfl) ⟨921696, by rfl⟩ : syracuseStep 2457857 = 1843393) B1843393
theorem B1638659 : Blo 1638018 1638659 := bstep (se 1 (by rfl) ⟨1228994, by rfl⟩ : syracuseStep 1638659 = 2457989) B2457989
theorem B5529869 : Blo 1638018 5529869 := bstep (se 3 (by rfl) ⟨1036850, by rfl⟩ : syracuseStep 5529869 = 2073701) B2073701
theorem B2457875 : Blo 1638018 2457875 := bstep (se 1 (by rfl) ⟨1843406, by rfl⟩ : syracuseStep 2457875 = 3686813) B3686813
theorem B1638675 : Blo 1638018 1638675 := bstep (se 1 (by rfl) ⟨1229006, by rfl⟩ : syracuseStep 1638675 = 2458013) B2458013
theorem B1638691 : Blo 1638018 1638691 := bstep (se 1 (by rfl) ⟨1229018, by rfl⟩ : syracuseStep 1638691 = 2458037) B2458037
theorem B3686705 : Blo 1638018 3686705 := bstep (se 2 (by rfl) ⟨1382514, by rfl⟩ : syracuseStep 3686705 = 2765029) B2765029
theorem B2457905 : Blo 1638018 2457905 := bstep (se 2 (by rfl) ⟨921714, by rfl⟩ : syracuseStep 2457905 = 1843429) B1843429
theorem B1638707 : Blo 1638018 1638707 := bstep (se 1 (by rfl) ⟨1229030, by rfl⟩ : syracuseStep 1638707 = 2458061) B2458061
theorem B21291317 : Blo 1638018 21291317 := bstep (se 5 (by rfl) ⟨998030, by rfl⟩ : syracuseStep 21291317 = 1996061) B1996061
theorem B5529923 : Blo 1638018 5529923 := bstep (se 1 (by rfl) ⟨4147442, by rfl⟩ : syracuseStep 5529923 = 8294885) B8294885
theorem B3686723 : Blo 1638018 3686723 := bstep (se 1 (by rfl) ⟨2765042, by rfl⟩ : syracuseStep 3686723 = 5530085) B5530085
theorem B2457923 : Blo 1638018 2457923 := bstep (se 1 (by rfl) ⟨1843442, by rfl⟩ : syracuseStep 2457923 = 3686885) B3686885
theorem B1638723 : Blo 1638018 1638723 := bstep (se 1 (by rfl) ⟨1229042, by rfl⟩ : syracuseStep 1638723 = 2458085) B2458085
theorem B6226253 : Blo 1638018 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B1638739 : Blo 1638018 1638739 := bstep (se 1 (by rfl) ⟨1229054, by rfl⟩ : syracuseStep 1638739 = 2458109) B2458109
theorem B2457953 : Blo 1638018 2457953 := bstep (se 2 (by rfl) ⟨921732, by rfl⟩ : syracuseStep 2457953 = 1843465) B1843465
theorem B1843555 : Blo 1638018 1843555 := bstep (se 1 (by rfl) ⟨1382666, by rfl⟩ : syracuseStep 1843555 = 2765333) B2765333
theorem B1638755 : Blo 1638018 1638755 := bstep (se 1 (by rfl) ⟨1229066, by rfl⟩ : syracuseStep 1638755 = 2458133) B2458133
theorem B2457971 : Blo 1638018 2457971 := bstep (se 1 (by rfl) ⟨1843478, by rfl⟩ : syracuseStep 2457971 = 3686957) B3686957
theorem B1638771 : Blo 1638018 1638771 := bstep (se 1 (by rfl) ⟨1229078, by rfl⟩ : syracuseStep 1638771 = 2458157) B2458157
theorem B1638787 : Blo 1638018 1638787 := bstep (se 1 (by rfl) ⟨1229090, by rfl⟩ : syracuseStep 1638787 = 2458181) B2458181
theorem B2458001 : Blo 1638018 2458001 := bstep (se 2 (by rfl) ⟨921750, by rfl⟩ : syracuseStep 2458001 = 1843501) B1843501
theorem B1638803 : Blo 1638018 1638803 := bstep (se 1 (by rfl) ⟨1229102, by rfl⟩ : syracuseStep 1638803 = 2458205) B2458205
theorem B2458019 : Blo 1638018 2458019 := bstep (se 1 (by rfl) ⟨1843514, by rfl⟩ : syracuseStep 2458019 = 3687029) B3687029
theorem B1638819 : Blo 1638018 1638819 := bstep (se 1 (by rfl) ⟨1229114, by rfl⟩ : syracuseStep 1638819 = 2458229) B2458229
theorem B1638835 : Blo 1638018 1638835 := bstep (se 1 (by rfl) ⟨1229126, by rfl⟩ : syracuseStep 1638835 = 2458253) B2458253
theorem B2458049 : Blo 1638018 2458049 := bstep (se 2 (by rfl) ⟨921768, by rfl⟩ : syracuseStep 2458049 = 1843537) B1843537
theorem B1638851 : Blo 1638018 1638851 := bstep (se 1 (by rfl) ⟨1229138, by rfl⟩ : syracuseStep 1638851 = 2458277) B2458277
theorem B2458067 : Blo 1638018 2458067 := bstep (se 1 (by rfl) ⟨1843550, by rfl⟩ : syracuseStep 2458067 = 3687101) B3687101
theorem B1638867 : Blo 1638018 1638867 := bstep (se 1 (by rfl) ⟨1229150, by rfl⟩ : syracuseStep 1638867 = 2458301) B2458301
theorem B1638883 : Blo 1638018 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B2458097 : Blo 1638018 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B1868275 : Blo 1638018 1868275 := bstep (se 1 (by rfl) ⟨1401206, by rfl⟩ : syracuseStep 1868275 = 2802413) B2802413
theorem B1843699 : Blo 1638018 1843699 := bstep (se 1 (by rfl) ⟨1382774, by rfl⟩ : syracuseStep 1843699 = 2765549) B2765549
theorem B1638899 : Blo 1638018 1638899 := bstep (se 1 (by rfl) ⟨1229174, by rfl⟩ : syracuseStep 1638899 = 2458349) B2458349
theorem B2458115 : Blo 1638018 2458115 := bstep (se 1 (by rfl) ⟨1843586, by rfl⟩ : syracuseStep 2458115 = 3687173) B3687173
theorem B1638915 : Blo 1638018 1638915 := bstep (se 1 (by rfl) ⟨1229186, by rfl⟩ : syracuseStep 1638915 = 2458373) B2458373
theorem B1638931 : Blo 1638018 1638931 := bstep (se 1 (by rfl) ⟨1229198, by rfl⟩ : syracuseStep 1638931 = 2458397) B2458397
theorem B2458145 : Blo 1638018 2458145 := bstep (se 2 (by rfl) ⟨921804, by rfl⟩ : syracuseStep 2458145 = 1843609) B1843609
theorem B1638947 : Blo 1638018 1638947 := bstep (se 1 (by rfl) ⟨1229210, by rfl⟩ : syracuseStep 1638947 = 2458421) B2458421
theorem B2458163 : Blo 1638018 2458163 := bstep (se 1 (by rfl) ⟨1843622, by rfl⟩ : syracuseStep 2458163 = 3687245) B3687245
theorem B1638963 : Blo 1638018 1638963 := bstep (se 1 (by rfl) ⟨1229222, by rfl⟩ : syracuseStep 1638963 = 2458445) B2458445
theorem B1638979 : Blo 1638018 1638979 := bstep (se 1 (by rfl) ⟨1229234, by rfl⟩ : syracuseStep 1638979 = 2458469) B2458469
theorem B6070861 : Blo 1638018 6070861 := bstep (se 3 (by rfl) ⟨1138286, by rfl⟩ : syracuseStep 6070861 = 2276573) B2276573
theorem B5530193 : Blo 1638018 5530193 := bstep (se 2 (by rfl) ⟨2073822, by rfl⟩ : syracuseStep 5530193 = 4147645) B4147645
theorem B3686993 : Blo 1638018 3686993 := bstep (se 2 (by rfl) ⟨1382622, by rfl⟩ : syracuseStep 3686993 = 2765245) B2765245
theorem B2458193 : Blo 1638018 2458193 := bstep (se 2 (by rfl) ⟨921822, by rfl⟩ : syracuseStep 2458193 = 1843645) B1843645
theorem B1638995 : Blo 1638018 1638995 := bstep (se 1 (by rfl) ⟨1229246, by rfl⟩ : syracuseStep 1638995 = 2458493) B2458493
theorem B3596881 : Blo 1638018 3596881 := bstep (se 2 (by rfl) ⟨1348830, by rfl⟩ : syracuseStep 3596881 = 2697661) B2697661
theorem B3687011 : Blo 1638018 3687011 := bstep (se 1 (by rfl) ⟨2765258, by rfl⟩ : syracuseStep 3687011 = 5530517) B5530517
theorem B2458211 : Blo 1638018 2458211 := bstep (se 1 (by rfl) ⟨1843658, by rfl⟩ : syracuseStep 2458211 = 3687317) B3687317
theorem B1639011 : Blo 1638018 1639011 := bstep (se 1 (by rfl) ⟨1229258, by rfl⟩ : syracuseStep 1639011 = 2458517) B2458517
theorem B4670065 : Blo 1638018 4670065 := bstep (se 2 (by rfl) ⟨1751274, by rfl⟩ : syracuseStep 4670065 = 3502549) B3502549
theorem B1639027 : Blo 1638018 1639027 := bstep (se 1 (by rfl) ⟨1229270, by rfl⟩ : syracuseStep 1639027 = 2458541) B2458541
theorem B2458241 : Blo 1638018 2458241 := bstep (se 2 (by rfl) ⟨921840, by rfl⟩ : syracuseStep 2458241 = 1843681) B1843681
theorem B1843843 : Blo 1638018 1843843 := bstep (se 1 (by rfl) ⟨1382882, by rfl⟩ : syracuseStep 1843843 = 2765765) B2765765
theorem B1639043 : Blo 1638018 1639043 := bstep (se 1 (by rfl) ⟨1229282, by rfl⟩ : syracuseStep 1639043 = 2458565) B2458565
theorem B2458259 : Blo 1638018 2458259 := bstep (se 1 (by rfl) ⟨1843694, by rfl⟩ : syracuseStep 2458259 = 3687389) B3687389
theorem B1639059 : Blo 1638018 1639059 := bstep (se 1 (by rfl) ⟨1229294, by rfl⟩ : syracuseStep 1639059 = 2458589) B2458589
theorem B1639075 : Blo 1638018 1639075 := bstep (se 1 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 1639075 = 2458613) B2458613
theorem B2458289 : Blo 1638018 2458289 := bstep (se 2 (by rfl) ⟨921858, by rfl⟩ : syracuseStep 2458289 = 1843717) B1843717
theorem B1639091 : Blo 1638018 1639091 := bstep (se 1 (by rfl) ⟨1229318, by rfl⟩ : syracuseStep 1639091 = 2458637) B2458637
theorem B2458307 : Blo 1638018 2458307 := bstep (se 1 (by rfl) ⟨1843730, by rfl⟩ : syracuseStep 2458307 = 3687461) B3687461
theorem B1639107 : Blo 1638018 1639107 := bstep (se 1 (by rfl) ⟨1229330, by rfl⟩ : syracuseStep 1639107 = 2458661) B2458661
theorem B1639123 : Blo 1638018 1639123 := bstep (se 1 (by rfl) ⟨1229342, by rfl⟩ : syracuseStep 1639123 = 2458685) B2458685
theorem B2458337 : Blo 1638018 2458337 := bstep (se 2 (by rfl) ⟨921876, by rfl⟩ : syracuseStep 2458337 = 1843753) B1843753
theorem B1639139 : Blo 1638018 1639139 := bstep (se 1 (by rfl) ⟨1229354, by rfl⟩ : syracuseStep 1639139 = 2458709) B2458709
theorem B5989091 : Blo 1638018 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B21005041 : Blo 1638018 21005041 := bstep (se 2 (by rfl) ⟨7876890, by rfl⟩ : syracuseStep 21005041 = 15753781) B15753781
theorem B2458355 : Blo 1638018 2458355 := bstep (se 1 (by rfl) ⟨1843766, by rfl⟩ : syracuseStep 2458355 = 3687533) B3687533
theorem B1639155 : Blo 1638018 1639155 := bstep (se 1 (by rfl) ⟨1229366, by rfl⟩ : syracuseStep 1639155 = 2458733) B2458733
theorem B1639171 : Blo 1638018 1639171 := bstep (se 1 (by rfl) ⟨1229378, by rfl⟩ : syracuseStep 1639171 = 2458757) B2458757
theorem B2458385 : Blo 1638018 2458385 := bstep (se 2 (by rfl) ⟨921894, by rfl⟩ : syracuseStep 2458385 = 1843789) B1843789
theorem B1843987 : Blo 1638018 1843987 := bstep (se 1 (by rfl) ⟨1382990, by rfl⟩ : syracuseStep 1843987 = 2765981) B2765981
theorem B1639187 : Blo 1638018 1639187 := bstep (se 1 (by rfl) ⟨1229390, by rfl⟩ : syracuseStep 1639187 = 2458781) B2458781
theorem B2458403 : Blo 1638018 2458403 := bstep (se 1 (by rfl) ⟨1843802, by rfl⟩ : syracuseStep 2458403 = 3687605) B3687605
theorem B1639203 : Blo 1638018 1639203 := bstep (se 1 (by rfl) ⟨1229402, by rfl⟩ : syracuseStep 1639203 = 2458805) B2458805
theorem B1639219 : Blo 1638018 1639219 := bstep (se 1 (by rfl) ⟨1229414, by rfl⟩ : syracuseStep 1639219 = 2458829) B2458829
theorem B2458433 : Blo 1638018 2458433 := bstep (se 2 (by rfl) ⟨921912, by rfl⟩ : syracuseStep 2458433 = 1843825) B1843825
theorem B1639235 : Blo 1638018 1639235 := bstep (se 1 (by rfl) ⟨1229426, by rfl⟩ : syracuseStep 1639235 = 2458853) B2458853
theorem B2458451 : Blo 1638018 2458451 := bstep (se 1 (by rfl) ⟨1843838, by rfl⟩ : syracuseStep 2458451 = 3687677) B3687677
theorem B1639251 : Blo 1638018 1639251 := bstep (se 1 (by rfl) ⟨1229438, by rfl⟩ : syracuseStep 1639251 = 2458877) B2458877
theorem B3498851 : Blo 1638018 3498851 := bstep (se 1 (by rfl) ⟨2624138, by rfl⟩ : syracuseStep 3498851 = 5248277) B5248277
theorem B12444515 : Blo 1638018 12444515 := bstep (se 1 (by rfl) ⟨9333386, by rfl⟩ : syracuseStep 12444515 = 18666773) B18666773
theorem B1639267 : Blo 1638018 1639267 := bstep (se 1 (by rfl) ⟨1229450, by rfl⟩ : syracuseStep 1639267 = 2458901) B2458901
theorem B3687281 : Blo 1638018 3687281 := bstep (se 2 (by rfl) ⟨1382730, by rfl⟩ : syracuseStep 3687281 = 2765461) B2765461
theorem B2458481 : Blo 1638018 2458481 := bstep (se 2 (by rfl) ⟨921930, by rfl⟩ : syracuseStep 2458481 = 1843861) B1843861
theorem B1639283 : Blo 1638018 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B3687299 : Blo 1638018 3687299 := bstep (se 1 (by rfl) ⟨2765474, by rfl⟩ : syracuseStep 3687299 = 5530949) B5530949
theorem B2458499 : Blo 1638018 2458499 := bstep (se 1 (by rfl) ⟨1843874, by rfl⟩ : syracuseStep 2458499 = 3687749) B3687749
theorem B1639299 : Blo 1638018 1639299 := bstep (se 1 (by rfl) ⟨1229474, by rfl⟩ : syracuseStep 1639299 = 2458949) B2458949
theorem B13288333 : Blo 1638018 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B1639315 : Blo 1638018 1639315 := bstep (se 1 (by rfl) ⟨1229486, by rfl⟩ : syracuseStep 1639315 = 2458973) B2458973
theorem B2458529 : Blo 1638018 2458529 := bstep (se 2 (by rfl) ⟨921948, by rfl⟩ : syracuseStep 2458529 = 1843897) B1843897
theorem B8405923 : Blo 1638018 8405923 := bstep (se 1 (by rfl) ⟨6304442, by rfl⟩ : syracuseStep 8405923 = 12608885) B12608885
theorem B1844131 : Blo 1638018 1844131 := bstep (se 1 (by rfl) ⟨1383098, by rfl⟩ : syracuseStep 1844131 = 2766197) B2766197
theorem B1639331 : Blo 1638018 1639331 := bstep (se 1 (by rfl) ⟨1229498, by rfl⟩ : syracuseStep 1639331 = 2458997) B2458997
theorem B2458547 : Blo 1638018 2458547 := bstep (se 1 (by rfl) ⟨1843910, by rfl⟩ : syracuseStep 2458547 = 3687821) B3687821
theorem B1639347 : Blo 1638018 1639347 := bstep (se 1 (by rfl) ⟨1229510, by rfl⟩ : syracuseStep 1639347 = 2459021) B2459021
theorem B2073539 : Blo 1638018 2073539 := bstep (se 1 (by rfl) ⟨1555154, by rfl⟩ : syracuseStep 2073539 = 3110309) B3110309
theorem B1639363 : Blo 1638018 1639363 := bstep (se 1 (by rfl) ⟨1229522, by rfl⟩ : syracuseStep 1639363 = 2459045) B2459045
theorem B2458577 : Blo 1638018 2458577 := bstep (se 2 (by rfl) ⟨921966, by rfl⟩ : syracuseStep 2458577 = 1843933) B1843933
theorem B1639379 : Blo 1638018 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B8979427 : Blo 1638018 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B2458595 : Blo 1638018 2458595 := bstep (se 1 (by rfl) ⟨1843946, by rfl⟩ : syracuseStep 2458595 = 3687893) B3687893
theorem B1639395 : Blo 1638018 1639395 := bstep (se 1 (by rfl) ⟨1229546, by rfl⟩ : syracuseStep 1639395 = 2459093) B2459093
theorem B1639411 : Blo 1638018 1639411 := bstep (se 1 (by rfl) ⟨1229558, by rfl⟩ : syracuseStep 1639411 = 2459117) B2459117
theorem B2458625 : Blo 1638018 2458625 := bstep (se 2 (by rfl) ⟨921984, by rfl⟩ : syracuseStep 2458625 = 1843969) B1843969
theorem B1639427 : Blo 1638018 1639427 := bstep (se 1 (by rfl) ⟨1229570, by rfl⟩ : syracuseStep 1639427 = 2459141) B2459141
theorem B2458643 : Blo 1638018 2458643 := bstep (se 1 (by rfl) ⟨1843982, by rfl⟩ : syracuseStep 2458643 = 3687965) B3687965
theorem B1639443 : Blo 1638018 1639443 := bstep (se 1 (by rfl) ⟨1229582, by rfl⟩ : syracuseStep 1639443 = 2459165) B2459165
theorem B1639459 : Blo 1638018 1639459 := bstep (se 1 (by rfl) ⟨1229594, by rfl⟩ : syracuseStep 1639459 = 2459189) B2459189
theorem B2458673 : Blo 1638018 2458673 := bstep (se 2 (by rfl) ⟨922002, by rfl⟩ : syracuseStep 2458673 = 1844005) B1844005
theorem B1844275 : Blo 1638018 1844275 := bstep (se 1 (by rfl) ⟨1383206, by rfl⟩ : syracuseStep 1844275 = 2766413) B2766413
theorem B1639475 : Blo 1638018 1639475 := bstep (se 1 (by rfl) ⟨1229606, by rfl⟩ : syracuseStep 1639475 = 2459213) B2459213
theorem B2458691 : Blo 1638018 2458691 := bstep (se 1 (by rfl) ⟨1844018, by rfl⟩ : syracuseStep 2458691 = 3688037) B3688037
theorem B1639491 : Blo 1638018 1639491 := bstep (se 1 (by rfl) ⟨1229618, by rfl⟩ : syracuseStep 1639491 = 2459237) B2459237
theorem B9462853 : Blo 1638018 9462853 := bstep (se 4 (by rfl) ⟨887142, by rfl⟩ : syracuseStep 9462853 = 1774285) B1774285
theorem B1639507 : Blo 1638018 1639507 := bstep (se 1 (by rfl) ⟨1229630, by rfl⟩ : syracuseStep 1639507 = 2459261) B2459261
theorem B2458721 : Blo 1638018 2458721 := bstep (se 2 (by rfl) ⟨922020, by rfl⟩ : syracuseStep 2458721 = 1844041) B1844041
theorem B1639523 : Blo 1638018 1639523 := bstep (se 1 (by rfl) ⟨1229642, by rfl⟩ : syracuseStep 1639523 = 2459285) B2459285
theorem B5530733 : Blo 1638018 5530733 := bstep (se 3 (by rfl) ⟨1037012, by rfl⟩ : syracuseStep 5530733 = 2074025) B2074025
theorem B2458739 : Blo 1638018 2458739 := bstep (se 1 (by rfl) ⟨1844054, by rfl⟩ : syracuseStep 2458739 = 3688109) B3688109
theorem B1639539 : Blo 1638018 1639539 := bstep (se 1 (by rfl) ⟨1229654, by rfl⟩ : syracuseStep 1639539 = 2459309) B2459309
theorem B1639555 : Blo 1638018 1639555 := bstep (se 1 (by rfl) ⟨1229666, by rfl⟩ : syracuseStep 1639555 = 2459333) B2459333
theorem B3687569 : Blo 1638018 3687569 := bstep (se 2 (by rfl) ⟨1382838, by rfl⟩ : syracuseStep 3687569 = 2765677) B2765677
theorem B2458769 : Blo 1638018 2458769 := bstep (se 2 (by rfl) ⟨922038, by rfl⟩ : syracuseStep 2458769 = 1844077) B1844077
theorem B1639571 : Blo 1638018 1639571 := bstep (se 1 (by rfl) ⟨1229678, by rfl⟩ : syracuseStep 1639571 = 2459357) B2459357
theorem B5530787 : Blo 1638018 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B3687587 : Blo 1638018 3687587 := bstep (se 1 (by rfl) ⟨2765690, by rfl⟩ : syracuseStep 3687587 = 5531381) B5531381
theorem B2458787 : Blo 1638018 2458787 := bstep (se 1 (by rfl) ⟨1844090, by rfl⟩ : syracuseStep 2458787 = 3688181) B3688181
theorem B1639587 : Blo 1638018 1639587 := bstep (se 1 (by rfl) ⟨1229690, by rfl⟩ : syracuseStep 1639587 = 2459381) B2459381
theorem B1639603 : Blo 1638018 1639603 := bstep (se 1 (by rfl) ⟨1229702, by rfl⟩ : syracuseStep 1639603 = 2459405) B2459405
theorem B2458817 : Blo 1638018 2458817 := bstep (se 2 (by rfl) ⟨922056, by rfl⟩ : syracuseStep 2458817 = 1844113) B1844113
theorem B1844419 : Blo 1638018 1844419 := bstep (se 1 (by rfl) ⟨1383314, by rfl⟩ : syracuseStep 1844419 = 2766629) B2766629
theorem B1639619 : Blo 1638018 1639619 := bstep (se 1 (by rfl) ⟨1229714, by rfl⟩ : syracuseStep 1639619 = 2459429) B2459429
theorem B9340109 : Blo 1638018 9340109 := bstep (se 3 (by rfl) ⟨1751270, by rfl⟩ : syracuseStep 9340109 = 3502541) B3502541
theorem B2458835 : Blo 1638018 2458835 := bstep (se 1 (by rfl) ⟨1844126, by rfl⟩ : syracuseStep 2458835 = 3688253) B3688253
theorem B1639635 : Blo 1638018 1639635 := bstep (se 1 (by rfl) ⟨1229726, by rfl⟩ : syracuseStep 1639635 = 2459453) B2459453
theorem B1639651 : Blo 1638018 1639651 := bstep (se 1 (by rfl) ⟨1229738, by rfl⟩ : syracuseStep 1639651 = 2459477) B2459477
theorem B18924785 : Blo 1638018 18924785 := bstep (se 2 (by rfl) ⟨7096794, by rfl⟩ : syracuseStep 18924785 = 14193589) B14193589
theorem B2458865 : Blo 1638018 2458865 := bstep (se 2 (by rfl) ⟨922074, by rfl⟩ : syracuseStep 2458865 = 1844149) B1844149
theorem B1639667 : Blo 1638018 1639667 := bstep (se 1 (by rfl) ⟨1229750, by rfl⟩ : syracuseStep 1639667 = 2459501) B2459501
theorem B2458883 : Blo 1638018 2458883 := bstep (se 1 (by rfl) ⟨1844162, by rfl⟩ : syracuseStep 2458883 = 3688325) B3688325
theorem B1639683 : Blo 1638018 1639683 := bstep (se 1 (by rfl) ⟨1229762, by rfl⟩ : syracuseStep 1639683 = 2459525) B2459525
theorem B1639699 : Blo 1638018 1639699 := bstep (se 1 (by rfl) ⟨1229774, by rfl⟩ : syracuseStep 1639699 = 2459549) B2459549
theorem B2458913 : Blo 1638018 2458913 := bstep (se 2 (by rfl) ⟨922092, by rfl⟩ : syracuseStep 2458913 = 1844185) B1844185
theorem B1639715 : Blo 1638018 1639715 := bstep (se 1 (by rfl) ⟨1229786, by rfl⟩ : syracuseStep 1639715 = 2459573) B2459573
theorem B2458931 : Blo 1638018 2458931 := bstep (se 1 (by rfl) ⟨1844198, by rfl⟩ : syracuseStep 2458931 = 3688397) B3688397
theorem B1639731 : Blo 1638018 1639731 := bstep (se 1 (by rfl) ⟨1229798, by rfl⟩ : syracuseStep 1639731 = 2459597) B2459597
theorem B1639747 : Blo 1638018 1639747 := bstep (se 1 (by rfl) ⟨1229810, by rfl⟩ : syracuseStep 1639747 = 2459621) B2459621
theorem B2458961 : Blo 1638018 2458961 := bstep (se 2 (by rfl) ⟨922110, by rfl⟩ : syracuseStep 2458961 = 1844221) B1844221
theorem B1844563 : Blo 1638018 1844563 := bstep (se 1 (by rfl) ⟨1383422, by rfl⟩ : syracuseStep 1844563 = 2766845) B2766845
theorem B1639763 : Blo 1638018 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B2458979 : Blo 1638018 2458979 := bstep (se 1 (by rfl) ⟨1844234, by rfl⟩ : syracuseStep 2458979 = 3688469) B3688469
theorem B1639779 : Blo 1638018 1639779 := bstep (se 1 (by rfl) ⟨1229834, by rfl⟩ : syracuseStep 1639779 = 2459669) B2459669
theorem B10495345 : Blo 1638018 10495345 := bstep (se 2 (by rfl) ⟨3935754, by rfl⟩ : syracuseStep 10495345 = 7871509) B7871509
theorem B1639795 : Blo 1638018 1639795 := bstep (se 1 (by rfl) ⟨1229846, by rfl⟩ : syracuseStep 1639795 = 2459693) B2459693
theorem B2459009 : Blo 1638018 2459009 := bstep (se 2 (by rfl) ⟨922128, by rfl⟩ : syracuseStep 2459009 = 1844257) B1844257
theorem B1639811 : Blo 1638018 1639811 := bstep (se 1 (by rfl) ⟨1229858, by rfl⟩ : syracuseStep 1639811 = 2459717) B2459717
theorem B2459027 : Blo 1638018 2459027 := bstep (se 1 (by rfl) ⟨1844270, by rfl⟩ : syracuseStep 2459027 = 3688541) B3688541
theorem B1639827 : Blo 1638018 1639827 := bstep (se 1 (by rfl) ⟨1229870, by rfl⟩ : syracuseStep 1639827 = 2459741) B2459741
theorem B1639843 : Blo 1638018 1639843 := bstep (se 1 (by rfl) ⟨1229882, by rfl⟩ : syracuseStep 1639843 = 2459765) B2459765
theorem B5531057 : Blo 1638018 5531057 := bstep (se 2 (by rfl) ⟨2074146, by rfl⟩ : syracuseStep 5531057 = 4148293) B4148293
theorem B3687857 : Blo 1638018 3687857 := bstep (se 2 (by rfl) ⟨1382946, by rfl⟩ : syracuseStep 3687857 = 2765893) B2765893
theorem B2459057 : Blo 1638018 2459057 := bstep (se 2 (by rfl) ⟨922146, by rfl⟩ : syracuseStep 2459057 = 1844293) B1844293
theorem B1639859 : Blo 1638018 1639859 := bstep (se 1 (by rfl) ⟨1229894, by rfl⟩ : syracuseStep 1639859 = 2459789) B2459789
theorem B4203971 : Blo 1638018 4203971 := bstep (se 1 (by rfl) ⟨3152978, by rfl⟩ : syracuseStep 4203971 = 6305957) B6305957
theorem B3687875 : Blo 1638018 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B2459075 : Blo 1638018 2459075 := bstep (se 1 (by rfl) ⟨1844306, by rfl⟩ : syracuseStep 2459075 = 3688613) B3688613
theorem B1639875 : Blo 1638018 1639875 := bstep (se 1 (by rfl) ⟨1229906, by rfl⟩ : syracuseStep 1639875 = 2459813) B2459813
theorem B1639891 : Blo 1638018 1639891 := bstep (se 1 (by rfl) ⟨1229918, by rfl⟩ : syracuseStep 1639891 = 2459837) B2459837
theorem B2459105 : Blo 1638018 2459105 := bstep (se 2 (by rfl) ⟨922164, by rfl⟩ : syracuseStep 2459105 = 1844329) B1844329
theorem B1844707 : Blo 1638018 1844707 := bstep (se 1 (by rfl) ⟨1383530, by rfl⟩ : syracuseStep 1844707 = 2767061) B2767061
theorem B1639907 : Blo 1638018 1639907 := bstep (se 1 (by rfl) ⟨1229930, by rfl⟩ : syracuseStep 1639907 = 2459861) B2459861
theorem B4146673 : Blo 1638018 4146673 := bstep (se 2 (by rfl) ⟨1555002, by rfl⟩ : syracuseStep 4146673 = 3110005) B3110005
theorem B2459123 : Blo 1638018 2459123 := bstep (se 1 (by rfl) ⟨1844342, by rfl⟩ : syracuseStep 2459123 = 3688685) B3688685
theorem B1639923 : Blo 1638018 1639923 := bstep (se 1 (by rfl) ⟨1229942, by rfl⟩ : syracuseStep 1639923 = 2459885) B2459885
theorem B1639939 : Blo 1638018 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B2459153 : Blo 1638018 2459153 := bstep (se 2 (by rfl) ⟨922182, by rfl⟩ : syracuseStep 2459153 = 1844365) B1844365
theorem B1639955 : Blo 1638018 1639955 := bstep (se 1 (by rfl) ⟨1229966, by rfl⟩ : syracuseStep 1639955 = 2459933) B2459933
theorem B2459171 : Blo 1638018 2459171 := bstep (se 1 (by rfl) ⟨1844378, by rfl⟩ : syracuseStep 2459171 = 3688757) B3688757
theorem B1639971 : Blo 1638018 1639971 := bstep (se 1 (by rfl) ⟨1229978, by rfl⟩ : syracuseStep 1639971 = 2459957) B2459957
theorem B1639987 : Blo 1638018 1639987 := bstep (se 1 (by rfl) ⟨1229990, by rfl⟩ : syracuseStep 1639987 = 2459981) B2459981
theorem B2459201 : Blo 1638018 2459201 := bstep (se 2 (by rfl) ⟨922200, by rfl⟩ : syracuseStep 2459201 = 1844401) B1844401
theorem B1640003 : Blo 1638018 1640003 := bstep (se 1 (by rfl) ⟨1230002, by rfl⟩ : syracuseStep 1640003 = 2460005) B2460005
theorem B9332293 : Blo 1638018 9332293 := bstep (se 4 (by rfl) ⟨874902, by rfl⟩ : syracuseStep 9332293 = 1749805) B1749805
theorem B2459219 : Blo 1638018 2459219 := bstep (se 1 (by rfl) ⟨1844414, by rfl⟩ : syracuseStep 2459219 = 3688829) B3688829
theorem B2459249 : Blo 1638018 2459249 := bstep (se 2 (by rfl) ⟨922218, by rfl⟩ : syracuseStep 2459249 = 1844437) B1844437
theorem B1844851 : Blo 1638018 1844851 := bstep (se 1 (by rfl) ⟨1383638, by rfl⟩ : syracuseStep 1844851 = 2767277) B2767277
theorem B2074243 : Blo 1638018 2074243 := bstep (se 1 (by rfl) ⟨1555682, by rfl⟩ : syracuseStep 2074243 = 3111365) B3111365
theorem B2459267 : Blo 1638018 2459267 := bstep (se 1 (by rfl) ⟨1844450, by rfl⟩ : syracuseStep 2459267 = 3688901) B3688901
theorem B2459297 : Blo 1638018 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B2459315 : Blo 1638018 2459315 := bstep (se 1 (by rfl) ⟨1844486, by rfl⟩ : syracuseStep 2459315 = 3688973) B3688973
theorem B3688145 : Blo 1638018 3688145 := bstep (se 2 (by rfl) ⟨1383054, by rfl⟩ : syracuseStep 3688145 = 2766109) B2766109
theorem B2459345 : Blo 1638018 2459345 := bstep (se 2 (by rfl) ⟨922254, by rfl⟩ : syracuseStep 2459345 = 1844509) B1844509
theorem B2074339 : Blo 1638018 2074339 := bstep (se 1 (by rfl) ⟨1555754, by rfl⟩ : syracuseStep 2074339 = 3111509) B3111509
theorem B3688163 : Blo 1638018 3688163 := bstep (se 1 (by rfl) ⟨2766122, by rfl⟩ : syracuseStep 3688163 = 5532245) B5532245
theorem B2459363 : Blo 1638018 2459363 := bstep (se 1 (by rfl) ⟨1844522, by rfl⟩ : syracuseStep 2459363 = 3689045) B3689045
theorem B2459393 : Blo 1638018 2459393 := bstep (se 2 (by rfl) ⟨922272, by rfl⟩ : syracuseStep 2459393 = 1844545) B1844545
theorem B4146947 : Blo 1638018 4146947 := bstep (se 1 (by rfl) ⟨3110210, by rfl⟩ : syracuseStep 4146947 = 6220421) B6220421
theorem B1844995 : Blo 1638018 1844995 := bstep (se 1 (by rfl) ⟨1383746, by rfl⟩ : syracuseStep 1844995 = 2767493) B2767493
theorem B2459411 : Blo 1638018 2459411 := bstep (se 1 (by rfl) ⟨1844558, by rfl⟩ : syracuseStep 2459411 = 3689117) B3689117
theorem B2459441 : Blo 1638018 2459441 := bstep (se 2 (by rfl) ⟨922290, by rfl⟩ : syracuseStep 2459441 = 1844581) B1844581
theorem B2459459 : Blo 1638018 2459459 := bstep (se 1 (by rfl) ⟨1844594, by rfl⟩ : syracuseStep 2459459 = 3689189) B3689189
theorem B2459489 : Blo 1638018 2459489 := bstep (se 2 (by rfl) ⟨922308, by rfl⟩ : syracuseStep 2459489 = 1844617) B1844617
theorem B2459507 : Blo 1638018 2459507 := bstep (se 1 (by rfl) ⟨1844630, by rfl⟩ : syracuseStep 2459507 = 3689261) B3689261
theorem B2459537 : Blo 1638018 2459537 := bstep (se 2 (by rfl) ⟨922326, by rfl⟩ : syracuseStep 2459537 = 1844653) B1844653
theorem B2459555 : Blo 1638018 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B2459585 : Blo 1638018 2459585 := bstep (se 2 (by rfl) ⟨922344, by rfl⟩ : syracuseStep 2459585 = 1844689) B1844689
theorem B4147139 : Blo 1638018 4147139 := bstep (se 1 (by rfl) ⟨3110354, by rfl⟩ : syracuseStep 4147139 = 6220709) B6220709
theorem B5531597 : Blo 1638018 5531597 := bstep (se 3 (by rfl) ⟨1037174, by rfl⟩ : syracuseStep 5531597 = 2074349) B2074349
theorem B2459603 : Blo 1638018 2459603 := bstep (se 1 (by rfl) ⟨1844702, by rfl⟩ : syracuseStep 2459603 = 3689405) B3689405
theorem B3688433 : Blo 1638018 3688433 := bstep (se 2 (by rfl) ⟨1383162, by rfl⟩ : syracuseStep 3688433 = 2766325) B2766325
theorem B2459633 : Blo 1638018 2459633 := bstep (se 2 (by rfl) ⟨922362, by rfl⟩ : syracuseStep 2459633 = 1844725) B1844725
theorem B5531651 : Blo 1638018 5531651 := bstep (se 1 (by rfl) ⟨4148738, by rfl⟩ : syracuseStep 5531651 = 8297477) B8297477
theorem B3688451 : Blo 1638018 3688451 := bstep (se 1 (by rfl) ⟨2766338, by rfl⟩ : syracuseStep 3688451 = 5532677) B5532677
theorem B2459651 : Blo 1638018 2459651 := bstep (se 1 (by rfl) ⟨1844738, by rfl⟩ : syracuseStep 2459651 = 3689477) B3689477
theorem B8857613 : Blo 1638018 8857613 := bstep (se 3 (by rfl) ⟨1660802, by rfl⟩ : syracuseStep 8857613 = 3321605) B3321605
theorem B5253133 : Blo 1638018 5253133 := bstep (se 3 (by rfl) ⟨984962, by rfl⟩ : syracuseStep 5253133 = 1969925) B1969925
theorem B2459681 : Blo 1638018 2459681 := bstep (se 2 (by rfl) ⟨922380, by rfl⟩ : syracuseStep 2459681 = 1844761) B1844761
theorem B3500081 : Blo 1638018 3500081 := bstep (se 2 (by rfl) ⟨1312530, by rfl⟩ : syracuseStep 3500081 = 2625061) B2625061
theorem B2459699 : Blo 1638018 2459699 := bstep (se 1 (by rfl) ⟨1844774, by rfl⟩ : syracuseStep 2459699 = 3689549) B3689549
theorem B2459729 : Blo 1638018 2459729 := bstep (se 2 (by rfl) ⟨922398, by rfl⟩ : syracuseStep 2459729 = 1844797) B1844797
theorem B2459747 : Blo 1638018 2459747 := bstep (se 1 (by rfl) ⟨1844810, by rfl⟩ : syracuseStep 2459747 = 3689621) B3689621
theorem B2459777 : Blo 1638018 2459777 := bstep (se 2 (by rfl) ⟨922416, by rfl⟩ : syracuseStep 2459777 = 1844833) B1844833
theorem B2459795 : Blo 1638018 2459795 := bstep (se 1 (by rfl) ⟨1844846, by rfl⟩ : syracuseStep 2459795 = 3689693) B3689693
theorem B3549361 : Blo 1638018 3549361 := bstep (se 2 (by rfl) ⟨1331010, by rfl⟩ : syracuseStep 3549361 = 2662021) B2662021
theorem B2459825 : Blo 1638018 2459825 := bstep (se 2 (by rfl) ⟨922434, by rfl⟩ : syracuseStep 2459825 = 1844869) B1844869
theorem B2459843 : Blo 1638018 2459843 := bstep (se 1 (by rfl) ⟨1844882, by rfl⟩ : syracuseStep 2459843 = 3689765) B3689765
theorem B2074835 : Blo 1638018 2074835 := bstep (se 1 (by rfl) ⟨1556126, by rfl⟩ : syracuseStep 2074835 = 3112253) B3112253
theorem B2459873 : Blo 1638018 2459873 := bstep (se 2 (by rfl) ⟨922452, by rfl⟩ : syracuseStep 2459873 = 1844905) B1844905
theorem B3737827 : Blo 1638018 3737827 := bstep (se 1 (by rfl) ⟨2803370, by rfl⟩ : syracuseStep 3737827 = 5606741) B5606741
theorem B2459891 : Blo 1638018 2459891 := bstep (se 1 (by rfl) ⟨1844918, by rfl⟩ : syracuseStep 2459891 = 3689837) B3689837
theorem B5531921 : Blo 1638018 5531921 := bstep (se 2 (by rfl) ⟨2074470, by rfl⟩ : syracuseStep 5531921 = 4148941) B4148941
theorem B3688721 : Blo 1638018 3688721 := bstep (se 2 (by rfl) ⟨1383270, by rfl⟩ : syracuseStep 3688721 = 2766541) B2766541
theorem B2459921 : Blo 1638018 2459921 := bstep (se 2 (by rfl) ⟨922470, by rfl⟩ : syracuseStep 2459921 = 1844941) B1844941
theorem B3688739 : Blo 1638018 3688739 := bstep (se 1 (by rfl) ⟨2766554, by rfl⟩ : syracuseStep 3688739 = 5533109) B5533109
theorem B2459939 : Blo 1638018 2459939 := bstep (se 1 (by rfl) ⟨1844954, by rfl⟩ : syracuseStep 2459939 = 3689909) B3689909
theorem B2459969 : Blo 1638018 2459969 := bstep (se 2 (by rfl) ⟨922488, by rfl⟩ : syracuseStep 2459969 = 1844977) B1844977
theorem B2459987 : Blo 1638018 2459987 := bstep (se 1 (by rfl) ⟨1844990, by rfl⟩ : syracuseStep 2459987 = 3689981) B3689981
theorem B19925347 : Blo 1638018 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B7473521 : Blo 1638018 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B2460017 : Blo 1638018 2460017 := bstep (se 2 (by rfl) ⟨922506, by rfl⟩ : syracuseStep 2460017 = 1845013) B1845013
theorem B10103237 : Blo 1638018 10103237 := bstep (se 4 (by rfl) ⟨947178, by rfl⟩ : syracuseStep 10103237 = 1894357) B1894357
theorem B2623985 : Blo 1638018 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B8301041 : Blo 1638018 8301041 := bstep (se 2 (by rfl) ⟨3112890, by rfl⟩ : syracuseStep 8301041 = 6225781) B6225781
theorem B3689009 : Blo 1638018 3689009 := bstep (se 2 (by rfl) ⟨1383378, by rfl⟩ : syracuseStep 3689009 = 2766757) B2766757
theorem B3689027 : Blo 1638018 3689027 := bstep (se 1 (by rfl) ⟨2766770, by rfl⟩ : syracuseStep 3689027 = 5533541) B5533541
theorem B8292941 : Blo 1638018 8292941 := bstep (se 3 (by rfl) ⟨1554926, by rfl⟩ : syracuseStep 8292941 = 3109853) B3109853
theorem B1895059 : Blo 1638018 1895059 := bstep (se 1 (by rfl) ⟨1421294, by rfl⟩ : syracuseStep 1895059 = 2842589) B2842589
theorem B6072995 : Blo 1638018 6072995 := bstep (se 1 (by rfl) ⟨4554746, by rfl⟩ : syracuseStep 6072995 = 9109493) B9109493
theorem B2624195 : Blo 1638018 2624195 := bstep (se 1 (by rfl) ⟨1968146, by rfl⟩ : syracuseStep 2624195 = 3936293) B3936293
theorem B7473869 : Blo 1638018 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B5532461 : Blo 1638018 5532461 := bstep (se 3 (by rfl) ⟨1037336, by rfl⟩ : syracuseStep 5532461 = 2074673) B2074673
theorem B3689297 : Blo 1638018 3689297 := bstep (se 2 (by rfl) ⟨1383486, by rfl⟩ : syracuseStep 3689297 = 2766973) B2766973
theorem B5532515 : Blo 1638018 5532515 := bstep (se 1 (by rfl) ⟨4149386, by rfl⟩ : syracuseStep 5532515 = 8298773) B8298773
theorem B3689315 : Blo 1638018 3689315 := bstep (se 1 (by rfl) ⟨2766986, by rfl⟩ : syracuseStep 3689315 = 5533973) B5533973
theorem B4148081 : Blo 1638018 4148081 := bstep (se 2 (by rfl) ⟨1555530, by rfl⟩ : syracuseStep 4148081 = 3111061) B3111061
theorem B2075539 : Blo 1638018 2075539 := bstep (se 1 (by rfl) ⟨1556654, by rfl⟩ : syracuseStep 2075539 = 3113309) B3113309
theorem B4148131 : Blo 1638018 4148131 := bstep (se 1 (by rfl) ⟨3111098, by rfl⟩ : syracuseStep 4148131 = 6222197) B6222197
theorem B3500977 : Blo 1638018 3500977 := bstep (se 2 (by rfl) ⟨1312866, by rfl⟩ : syracuseStep 3500977 = 2625733) B2625733
theorem B3500995 : Blo 1638018 3500995 := bstep (se 1 (by rfl) ⟨2625746, by rfl⟩ : syracuseStep 3500995 = 5251493) B5251493
theorem B12618737 : Blo 1638018 12618737 := bstep (se 2 (by rfl) ⟨4732026, by rfl⟩ : syracuseStep 12618737 = 9464053) B9464053
theorem B2075635 : Blo 1638018 2075635 := bstep (se 1 (by rfl) ⟨1556726, by rfl⟩ : syracuseStep 2075635 = 3113453) B3113453
theorem B4148273 : Blo 1638018 4148273 := bstep (se 2 (by rfl) ⟨1555602, by rfl⟩ : syracuseStep 4148273 = 3111205) B3111205
theorem B1969219 : Blo 1638018 1969219 := bstep (se 1 (by rfl) ⟨1476914, by rfl⟩ : syracuseStep 1969219 = 2953829) B2953829
theorem B5532785 : Blo 1638018 5532785 := bstep (se 2 (by rfl) ⟨2074794, by rfl⟩ : syracuseStep 5532785 = 4149589) B4149589
theorem B3689585 : Blo 1638018 3689585 := bstep (se 2 (by rfl) ⟨1383594, by rfl⟩ : syracuseStep 3689585 = 2767189) B2767189
theorem B3689603 : Blo 1638018 3689603 := bstep (se 1 (by rfl) ⟨2767202, by rfl⟩ : syracuseStep 3689603 = 5534405) B5534405
theorem B15756515 : Blo 1638018 15756515 := bstep (se 1 (by rfl) ⟨11817386, by rfl⟩ : syracuseStep 15756515 = 23634773) B23634773
theorem B4492561 : Blo 1638018 4492561 := bstep (se 2 (by rfl) ⟨1684710, by rfl⟩ : syracuseStep 4492561 = 3369421) B3369421
theorem B4664621 : Blo 1638018 4664621 := bstep (se 3 (by rfl) ⟨874616, by rfl⟩ : syracuseStep 4664621 = 1749233) B1749233
theorem B3689873 : Blo 1638018 3689873 := bstep (se 2 (by rfl) ⟨1383702, by rfl⟩ : syracuseStep 3689873 = 2767405) B2767405
theorem B3689891 : Blo 1638018 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B2624977 : Blo 1638018 2624977 := bstep (se 2 (by rfl) ⟨984366, by rfl⟩ : syracuseStep 2624977 = 1968733) B1968733
theorem B4664803 : Blo 1638018 4664803 := bstep (se 1 (by rfl) ⟨3498602, by rfl⟩ : syracuseStep 4664803 = 6997205) B6997205
theorem B2764273 : Blo 1638018 2764273 := bstep (se 2 (by rfl) ⟨1036602, by rfl⟩ : syracuseStep 2764273 = 2073205) B2073205
theorem B18927089 : Blo 1638018 18927089 := bstep (se 2 (by rfl) ⟨7097658, by rfl⟩ : syracuseStep 18927089 = 14195317) B14195317
theorem B9334277 : Blo 1638018 9334277 := bstep (se 4 (by rfl) ⟨875088, by rfl⟩ : syracuseStep 9334277 = 1750177) B1750177
theorem B2764307 : Blo 1638018 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B5533325 : Blo 1638018 5533325 := bstep (se 3 (by rfl) ⟨1037498, by rfl⟩ : syracuseStep 5533325 = 2074997) B2074997
theorem B2764435 : Blo 1638018 2764435 := bstep (se 1 (by rfl) ⟨2073326, by rfl⟩ : syracuseStep 2764435 = 4146653) B4146653
theorem B5533379 : Blo 1638018 5533379 := bstep (se 1 (by rfl) ⟨4150034, by rfl⟩ : syracuseStep 5533379 = 8300069) B8300069
theorem B2764577 : Blo 1638018 2764577 := bstep (se 2 (by rfl) ⟨1036716, by rfl⟩ : syracuseStep 2764577 = 2073433) B2073433
theorem B2953027 : Blo 1638018 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B18665315 : Blo 1638018 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B6221681 : Blo 1638018 6221681 := bstep (se 2 (by rfl) ⟨2333130, by rfl⟩ : syracuseStep 6221681 = 4666261) B4666261
theorem B2764705 : Blo 1638018 2764705 := bstep (se 2 (by rfl) ⟨1036764, by rfl⟩ : syracuseStep 2764705 = 2073529) B2073529
theorem B8302499 : Blo 1638018 8302499 := bstep (se 1 (by rfl) ⟨6226874, by rfl⟩ : syracuseStep 8302499 = 12453749) B12453749
theorem B2764739 : Blo 1638018 2764739 := bstep (se 1 (by rfl) ⟨2073554, by rfl⟩ : syracuseStep 2764739 = 4147109) B4147109
theorem B5533649 : Blo 1638018 5533649 := bstep (se 2 (by rfl) ⟨2075118, by rfl⟩ : syracuseStep 5533649 = 4150237) B4150237
theorem B11210723 : Blo 1638018 11210723 := bstep (se 1 (by rfl) ⟨8408042, by rfl⟩ : syracuseStep 11210723 = 16816085) B16816085
theorem B4149265 : Blo 1638018 4149265 := bstep (se 2 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 4149265 = 3111949) B3111949
theorem B2764867 : Blo 1638018 2764867 := bstep (se 1 (by rfl) ⟨2073650, by rfl⟩ : syracuseStep 2764867 = 4147301) B4147301
theorem B7000177 : Blo 1638018 7000177 := bstep (se 2 (by rfl) ⟨2625066, by rfl⟩ : syracuseStep 7000177 = 5250133) B5250133
theorem B3322019 : Blo 1638018 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B8409251 : Blo 1638018 8409251 := bstep (se 1 (by rfl) ⟨6306938, by rfl⟩ : syracuseStep 8409251 = 12613877) B12613877
theorem B2765009 : Blo 1638018 2765009 := bstep (se 2 (by rfl) ⟨1036878, by rfl⟩ : syracuseStep 2765009 = 2073757) B2073757
theorem B2625779 : Blo 1638018 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B2216209 : Blo 1638018 2216209 := bstep (se 2 (by rfl) ⟨831078, by rfl⟩ : syracuseStep 2216209 = 1662157) B1662157
theorem B4149539 : Blo 1638018 4149539 := bstep (se 1 (by rfl) ⟨3112154, by rfl⟩ : syracuseStep 4149539 = 6224309) B6224309
theorem B4731185 : Blo 1638018 4731185 := bstep (se 2 (by rfl) ⟨1774194, by rfl⟩ : syracuseStep 4731185 = 3548389) B3548389
theorem B3936593 : Blo 1638018 3936593 := bstep (se 2 (by rfl) ⟨1476222, by rfl⟩ : syracuseStep 3936593 = 2952445) B2952445
theorem B2765137 : Blo 1638018 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B2765171 : Blo 1638018 2765171 := bstep (se 1 (by rfl) ⟨2073878, by rfl⟩ : syracuseStep 2765171 = 4147757) B4147757
theorem B23622029 : Blo 1638018 23622029 := bstep (se 3 (by rfl) ⟨4429130, by rfl⟩ : syracuseStep 23622029 = 8858261) B8858261
theorem B1749395 : Blo 1638018 1749395 := bstep (se 1 (by rfl) ⟨1312046, by rfl⟩ : syracuseStep 1749395 = 2624093) B2624093
theorem B7877027 : Blo 1638018 7877027 := bstep (se 1 (by rfl) ⟨5907770, by rfl⟩ : syracuseStep 7877027 = 11815541) B11815541
theorem B2216371 : Blo 1638018 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B4149731 : Blo 1638018 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B5534189 : Blo 1638018 5534189 := bstep (se 3 (by rfl) ⟨1037660, by rfl⟩ : syracuseStep 5534189 = 2075321) B2075321
theorem B2765299 : Blo 1638018 2765299 := bstep (se 1 (by rfl) ⟨2073974, by rfl⟩ : syracuseStep 2765299 = 4147949) B4147949
theorem B5534243 : Blo 1638018 5534243 := bstep (se 1 (by rfl) ⟨4150682, by rfl⟩ : syracuseStep 5534243 = 8301365) B8301365
theorem B2765441 : Blo 1638018 2765441 := bstep (se 2 (by rfl) ⟨1037040, by rfl⟩ : syracuseStep 2765441 = 2074081) B2074081
theorem B5984909 : Blo 1638018 5984909 := bstep (se 3 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 5984909 = 2244341) B2244341
theorem B5247661 : Blo 1638018 5247661 := bstep (se 3 (by rfl) ⟨983936, by rfl⟩ : syracuseStep 5247661 = 1967873) B1967873
theorem B42029765 : Blo 1638018 42029765 := bstep (se 4 (by rfl) ⟨3940290, by rfl⟩ : syracuseStep 42029765 = 7880581) B7880581
theorem B3936977 : Blo 1638018 3936977 := bstep (se 2 (by rfl) ⟨1476366, by rfl⟩ : syracuseStep 3936977 = 2952733) B2952733
theorem B2626291 : Blo 1638018 2626291 := bstep (se 1 (by rfl) ⟨1969718, by rfl⟩ : syracuseStep 2626291 = 3939437) B3939437
theorem B2765569 : Blo 1638018 2765569 := bstep (se 2 (by rfl) ⟨1037088, by rfl⟩ : syracuseStep 2765569 = 2074177) B2074177
theorem B35926805 : Blo 1638018 35926805 := bstep (se 6 (by rfl) ⟨842034, by rfl⟩ : syracuseStep 35926805 = 1684069) B1684069
theorem B2765603 : Blo 1638018 2765603 := bstep (se 1 (by rfl) ⟨2074202, by rfl⟩ : syracuseStep 2765603 = 4148405) B4148405
theorem B5534513 : Blo 1638018 5534513 := bstep (se 2 (by rfl) ⟨2075442, by rfl⟩ : syracuseStep 5534513 = 4150885) B4150885
theorem B17953589 : Blo 1638018 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B4666193 : Blo 1638018 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B2954065 : Blo 1638018 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B2765731 : Blo 1638018 2765731 := bstep (se 1 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 2765731 = 4148597) B4148597
theorem B2339777 : Blo 1638018 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B1995779 : Blo 1638018 1995779 := bstep (se 1 (by rfl) ⟨1496834, by rfl⟩ : syracuseStep 1995779 = 2993669) B2993669
theorem B7099427 : Blo 1638018 7099427 := bstep (se 1 (by rfl) ⟨5324570, by rfl⟩ : syracuseStep 7099427 = 10649141) B10649141
theorem B2765873 : Blo 1638018 2765873 := bstep (se 2 (by rfl) ⟨1037202, by rfl⟩ : syracuseStep 2765873 = 2074405) B2074405
theorem B5608547 : Blo 1638018 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B3110051 : Blo 1638018 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B2766001 : Blo 1638018 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B2766035 : Blo 1638018 2766035 := bstep (se 1 (by rfl) ⟨2074526, by rfl⟩ : syracuseStep 2766035 = 4149053) B4149053
theorem B11810033 : Blo 1638018 11810033 := bstep (se 2 (by rfl) ⟨4428762, by rfl⟩ : syracuseStep 11810033 = 8857525) B8857525
theorem B2626835 : Blo 1638018 2626835 := bstep (se 1 (by rfl) ⟨1970126, by rfl⟩ : syracuseStep 2626835 = 3940253) B3940253
theorem B6223139 : Blo 1638018 6223139 := bstep (se 1 (by rfl) ⟨4667354, by rfl⟩ : syracuseStep 6223139 = 9334709) B9334709
theorem B5535053 : Blo 1638018 5535053 := bstep (se 3 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 5535053 = 2075645) B2075645
theorem B2766163 : Blo 1638018 2766163 := bstep (se 1 (by rfl) ⟨2074622, by rfl⟩ : syracuseStep 2766163 = 4149245) B4149245
theorem B39892337 : Blo 1638018 39892337 := bstep (se 2 (by rfl) ⟨14959626, by rfl⟩ : syracuseStep 39892337 = 29919253) B29919253
theorem B4150673 : Blo 1638018 4150673 := bstep (se 2 (by rfl) ⟨1556502, by rfl⟩ : syracuseStep 4150673 = 3113005) B3113005
theorem B8295857 : Blo 1638018 8295857 := bstep (se 2 (by rfl) ⟨3110946, by rfl⟩ : syracuseStep 8295857 = 6221893) B6221893
theorem B3110339 : Blo 1638018 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B4150723 : Blo 1638018 4150723 := bstep (se 1 (by rfl) ⟨3113042, by rfl⟩ : syracuseStep 4150723 = 6226085) B6226085
theorem B2766305 : Blo 1638018 2766305 := bstep (se 2 (by rfl) ⟨1037364, by rfl⟩ : syracuseStep 2766305 = 2074729) B2074729
theorem B5248493 : Blo 1638018 5248493 := bstep (se 3 (by rfl) ⟨984092, by rfl⟩ : syracuseStep 5248493 = 1968185) B1968185
theorem B4429325 : Blo 1638018 4429325 := bstep (se 3 (by rfl) ⟨830498, by rfl⟩ : syracuseStep 4429325 = 1660997) B1660997
theorem B5903921 : Blo 1638018 5903921 := bstep (se 2 (by rfl) ⟨2213970, by rfl⟩ : syracuseStep 5903921 = 4427941) B4427941
theorem B4150865 : Blo 1638018 4150865 := bstep (se 2 (by rfl) ⟨1556574, by rfl⟩ : syracuseStep 4150865 = 3113149) B3113149
theorem B2766433 : Blo 1638018 2766433 := bstep (se 2 (by rfl) ⟨1037412, by rfl⟩ : syracuseStep 2766433 = 2074825) B2074825
theorem B2766467 : Blo 1638018 2766467 := bstep (se 1 (by rfl) ⟨2074850, by rfl⟩ : syracuseStep 2766467 = 4149701) B4149701
theorem B31495877 : Blo 1638018 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B1750771 : Blo 1638018 1750771 := bstep (se 1 (by rfl) ⟨1313078, by rfl⟩ : syracuseStep 1750771 = 2626157) B2626157
theorem B2766595 : Blo 1638018 2766595 := bstep (se 1 (by rfl) ⟨2074946, by rfl⟩ : syracuseStep 2766595 = 4149893) B4149893
theorem B4667149 : Blo 1638018 4667149 := bstep (se 3 (by rfl) ⟨875090, by rfl⟩ : syracuseStep 4667149 = 1750181) B1750181
theorem B2332481 : Blo 1638018 2332481 := bstep (se 2 (by rfl) ⟨874680, by rfl⟩ : syracuseStep 2332481 = 1749361) B1749361
theorem B13997893 : Blo 1638018 13997893 := bstep (se 4 (by rfl) ⟨1312302, by rfl⟩ : syracuseStep 13997893 = 2624605) B2624605
theorem B2766737 : Blo 1638018 2766737 := bstep (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) B2075053
theorem B1660819 : Blo 1638018 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B2332595 : Blo 1638018 2332595 := bstep (se 1 (by rfl) ⟨1749446, by rfl⟩ : syracuseStep 2332595 = 3498893) B3498893
theorem B1660867 : Blo 1638018 1660867 := bstep (se 1 (by rfl) ⟨1245650, by rfl⟩ : syracuseStep 1660867 = 2491301) B2491301
theorem B21010373 : Blo 1638018 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B4667377 : Blo 1638018 4667377 := bstep (se 2 (by rfl) ⟨1750266, by rfl⟩ : syracuseStep 4667377 = 3500533) B3500533
theorem B2332675 : Blo 1638018 2332675 := bstep (se 1 (by rfl) ⟨1749506, by rfl⟩ : syracuseStep 2332675 = 3499013) B3499013
theorem B2766865 : Blo 1638018 2766865 := bstep (se 2 (by rfl) ⟨1037574, by rfl⟩ : syracuseStep 2766865 = 2075149) B2075149
theorem B2766899 : Blo 1638018 2766899 := bstep (se 1 (by rfl) ⟨2075174, by rfl⟩ : syracuseStep 2766899 = 4150349) B4150349
theorem B12449861 : Blo 1638018 12449861 := bstep (se 4 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 12449861 = 2334349) B2334349
theorem B4667537 : Blo 1638018 4667537 := bstep (se 2 (by rfl) ⟨1750326, by rfl⟩ : syracuseStep 4667537 = 3500653) B3500653
theorem B4429997 : Blo 1638018 4429997 := bstep (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) B1661249
theorem B5609645 : Blo 1638018 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B2767027 : Blo 1638018 2767027 := bstep (se 1 (by rfl) ⟨2075270, by rfl⟩ : syracuseStep 2767027 = 4150541) B4150541
theorem B4667651 : Blo 1638018 4667651 := bstep (se 1 (by rfl) ⟨3500738, by rfl⟩ : syracuseStep 4667651 = 7001477) B7001477
theorem B6224141 : Blo 1638018 6224141 := bstep (se 3 (by rfl) ⟨1167026, by rfl⟩ : syracuseStep 6224141 = 2334053) B2334053
theorem B2767169 : Blo 1638018 2767169 := bstep (se 2 (by rfl) ⟨1037688, by rfl⟩ : syracuseStep 2767169 = 2075377) B2075377
theorem B3111281 : Blo 1638018 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B14006641 : Blo 1638018 14006641 := bstep (se 2 (by rfl) ⟨5252490, by rfl⟩ : syracuseStep 14006641 = 10504981) B10504981
theorem B2767297 : Blo 1638018 2767297 := bstep (se 2 (by rfl) ⟨1037736, by rfl⟩ : syracuseStep 2767297 = 2075473) B2075473
theorem B302913989 : Blo 1638018 302913989 := bstep (se 4 (by rfl) ⟨28398186, by rfl⟩ : syracuseStep 302913989 = 56796373) B56796373
theorem B5904845 : Blo 1638018 5904845 := bstep (se 3 (by rfl) ⟨1107158, by rfl⟩ : syracuseStep 5904845 = 2214317) B2214317
theorem B2767331 : Blo 1638018 2767331 := bstep (se 1 (by rfl) ⟨2075498, by rfl⟩ : syracuseStep 2767331 = 4150997) B4150997
theorem B2333233 : Blo 1638018 2333233 := bstep (se 2 (by rfl) ⟨874962, by rfl⟩ : syracuseStep 2333233 = 1749925) B1749925
theorem B10500677 : Blo 1638018 10500677 := bstep (se 4 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 10500677 = 1968877) B1968877
theorem B2767459 : Blo 1638018 2767459 := bstep (se 1 (by rfl) ⟨2075594, by rfl⟩ : syracuseStep 2767459 = 4151189) B4151189
theorem B8862371 : Blo 1638018 8862371 := bstep (se 1 (by rfl) ⟨6646778, by rfl⟩ : syracuseStep 8862371 = 13293557) B13293557
theorem B5610221 : Blo 1638018 5610221 := bstep (se 3 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 5610221 = 2103833) B2103833
theorem B8297315 : Blo 1638018 8297315 := bstep (se 1 (by rfl) ⟨6222986, by rfl⟩ : syracuseStep 8297315 = 12445973) B12445973
theorem B15760241 : Blo 1638018 15760241 := bstep (se 2 (by rfl) ⟨5910090, by rfl⟩ : syracuseStep 15760241 = 11820181) B11820181
theorem B5528465 : Blo 1638018 5528465 := bstep (se 2 (by rfl) ⟨2073174, by rfl⟩ : syracuseStep 5528465 = 4146349) B4146349
theorem B3685553 : Blo 1638018 3685553 := bstep (se 2 (by rfl) ⟨1382082, by rfl⟩ : syracuseStep 3685553 = 2764165) B2764165
theorem B3685571 : Blo 1638018 3685571 := bstep (se 1 (by rfl) ⟨2764178, by rfl⟩ : syracuseStep 3685571 = 5528357) B5528357
theorem B4668653 : Blo 1638018 4668653 := bstep (se 3 (by rfl) ⟨875372, by rfl⟩ : syracuseStep 4668653 = 1750745) B1750745
theorem B3112177 : Blo 1638018 3112177 := bstep (se 2 (by rfl) ⟨1167066, by rfl⟩ : syracuseStep 3112177 = 2334133) B2334133
theorem B2333939 : Blo 1638018 2333939 := bstep (se 1 (by rfl) ⟨1750454, by rfl⟩ : syracuseStep 2333939 = 3500909) B3500909
theorem B9338125 : Blo 1638018 9338125 := bstep (se 3 (by rfl) ⟨1750898, by rfl⟩ : syracuseStep 9338125 = 3501797) B3501797
theorem B3939619 : Blo 1638018 3939619 := bstep (se 1 (by rfl) ⟨2954714, by rfl⟩ : syracuseStep 3939619 = 5909429) B5909429
theorem B5324077 : Blo 1638018 5324077 := bstep (se 3 (by rfl) ⟨998264, by rfl⟩ : syracuseStep 5324077 = 1996529) B1996529
theorem B26934581 : Blo 1638018 26934581 := bstep (se 5 (by rfl) ⟨1262558, by rfl⟩ : syracuseStep 26934581 = 2525117) B2525117
theorem B3112337 : Blo 1638018 3112337 := bstep (se 2 (by rfl) ⟨1167126, by rfl⟩ : syracuseStep 3112337 = 2334253) B2334253
theorem B4668835 : Blo 1638018 4668835 := bstep (se 1 (by rfl) ⟨3501626, by rfl⟩ : syracuseStep 4668835 = 7003253) B7003253
theorem B5529005 : Blo 1638018 5529005 := bstep (se 3 (by rfl) ⟨1036688, by rfl⟩ : syracuseStep 5529005 = 2073377) B2073377
theorem B2457041 : Blo 1638018 2457041 := bstep (se 2 (by rfl) ⟨921390, by rfl⟩ : syracuseStep 2457041 = 1842781) B1842781
theorem B3685841 : Blo 1638018 3685841 := bstep (se 2 (by rfl) ⟨1382190, by rfl⟩ : syracuseStep 3685841 = 2764381) B2764381
theorem B2457059 : Blo 1638018 2457059 := bstep (se 1 (by rfl) ⟨1842794, by rfl⟩ : syracuseStep 2457059 = 3685589) B3685589
theorem B3685859 : Blo 1638018 3685859 := bstep (se 1 (by rfl) ⟨2764394, by rfl⟩ : syracuseStep 3685859 = 5528789) B5528789
theorem B5529059 : Blo 1638018 5529059 := bstep (se 1 (by rfl) ⟨4146794, by rfl⟩ : syracuseStep 5529059 = 8293589) B8293589
theorem B2457089 : Blo 1638018 2457089 := bstep (se 2 (by rfl) ⟨921408, by rfl⟩ : syracuseStep 2457089 = 1842817) B1842817
theorem B2457107 : Blo 1638018 2457107 := bstep (se 1 (by rfl) ⟨1842830, by rfl⟩ : syracuseStep 2457107 = 3685661) B3685661
theorem B5250595 : Blo 1638018 5250595 := bstep (se 1 (by rfl) ⟨3937946, by rfl⟩ : syracuseStep 5250595 = 7875893) B7875893
theorem B2457137 : Blo 1638018 2457137 := bstep (se 2 (by rfl) ⟨921426, by rfl⟩ : syracuseStep 2457137 = 1842853) B1842853
theorem B2457155 : Blo 1638018 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B4668995 : Blo 1638018 4668995 := bstep (se 1 (by rfl) ⟨3501746, by rfl⟩ : syracuseStep 4668995 = 7003493) B7003493
theorem B2457185 : Blo 1638018 2457185 := bstep (se 2 (by rfl) ⟨921444, by rfl⟩ : syracuseStep 2457185 = 1842889) B1842889
theorem B2457203 : Blo 1638018 2457203 := bstep (se 1 (by rfl) ⟨1842902, by rfl⟩ : syracuseStep 2457203 = 3685805) B3685805
theorem B1638019 : Blo 1638018 1638019 := bstep (se 1 (by rfl) ⟨1228514, by rfl⟩ : syracuseStep 1638019 = 2457029) B2457029
theorem B8298125 : Blo 1638018 8298125 := bstep (se 3 (by rfl) ⟨1555898, by rfl⟩ : syracuseStep 8298125 = 3111797) B3111797
theorem B2457233 : Blo 1638018 2457233 := bstep (se 2 (by rfl) ⟨921462, by rfl⟩ : syracuseStep 2457233 = 1842925) B1842925
theorem B1638035 : Blo 1638018 1638035 := bstep (se 1 (by rfl) ⟨1228526, by rfl⟩ : syracuseStep 1638035 = 2457053) B2457053
theorem B1842835 : Blo 1638018 1842835 := bstep (se 1 (by rfl) ⟨1382126, by rfl⟩ : syracuseStep 1842835 = 2764253) B2764253
theorem B1638051 : Blo 1638018 1638051 := bstep (se 1 (by rfl) ⟨1228538, by rfl⟩ : syracuseStep 1638051 = 2457077) B2457077
theorem B2457251 : Blo 1638018 2457251 := bstep (se 1 (by rfl) ⟨1842938, by rfl⟩ : syracuseStep 2457251 = 3685877) B3685877
theorem B5250737 : Blo 1638018 5250737 := bstep (se 2 (by rfl) ⟨1969026, by rfl⟩ : syracuseStep 5250737 = 3938053) B3938053
theorem B1638067 : Blo 1638018 1638067 := bstep (se 1 (by rfl) ⟨1228550, by rfl⟩ : syracuseStep 1638067 = 2457101) B2457101
theorem B2457281 : Blo 1638018 2457281 := bstep (se 2 (by rfl) ⟨921480, by rfl⟩ : syracuseStep 2457281 = 1842961) B1842961
theorem B1638083 : Blo 1638018 1638083 := bstep (se 1 (by rfl) ⟨1228562, by rfl⟩ : syracuseStep 1638083 = 2457125) B2457125
theorem B7003853 : Blo 1638018 7003853 := bstep (se 3 (by rfl) ⟨1313222, by rfl⟩ : syracuseStep 7003853 = 2626445) B2626445
theorem B1638099 : Blo 1638018 1638099 := bstep (se 1 (by rfl) ⟨1228574, by rfl⟩ : syracuseStep 1638099 = 2457149) B2457149
theorem B2457299 : Blo 1638018 2457299 := bstep (se 1 (by rfl) ⟨1842974, by rfl⟩ : syracuseStep 2457299 = 3685949) B3685949
theorem B1638115 : Blo 1638018 1638115 := bstep (se 1 (by rfl) ⟨1228586, by rfl⟩ : syracuseStep 1638115 = 2457173) B2457173
theorem B2457329 : Blo 1638018 2457329 := bstep (se 2 (by rfl) ⟨921498, by rfl⟩ : syracuseStep 2457329 = 1842997) B1842997
theorem B3686129 : Blo 1638018 3686129 := bstep (se 2 (by rfl) ⟨1382298, by rfl⟩ : syracuseStep 3686129 = 2764597) B2764597
theorem B1638131 : Blo 1638018 1638131 := bstep (se 1 (by rfl) ⟨1228598, by rfl⟩ : syracuseStep 1638131 = 2457197) B2457197
theorem B5529329 : Blo 1638018 5529329 := bstep (se 2 (by rfl) ⟨2073498, by rfl⟩ : syracuseStep 5529329 = 4146997) B4146997
theorem B1638147 : Blo 1638018 1638147 := bstep (se 1 (by rfl) ⟨1228610, by rfl⟩ : syracuseStep 1638147 = 2457221) B2457221
theorem B2457347 : Blo 1638018 2457347 := bstep (se 1 (by rfl) ⟨1843010, by rfl⟩ : syracuseStep 2457347 = 3686021) B3686021
theorem B3686147 : Blo 1638018 3686147 := bstep (se 1 (by rfl) ⟨2764610, by rfl⟩ : syracuseStep 3686147 = 5529221) B5529221
theorem B1638163 : Blo 1638018 1638163 := bstep (se 1 (by rfl) ⟨1228622, by rfl⟩ : syracuseStep 1638163 = 2457245) B2457245
theorem B2457377 : Blo 1638018 2457377 := bstep (se 2 (by rfl) ⟨921516, by rfl⟩ : syracuseStep 2457377 = 1843033) B1843033
theorem B1638179 : Blo 1638018 1638179 := bstep (se 1 (by rfl) ⟨1228634, by rfl⟩ : syracuseStep 1638179 = 2457269) B2457269
theorem B1842979 : Blo 1638018 1842979 := bstep (se 1 (by rfl) ⟨1382234, by rfl⟩ : syracuseStep 1842979 = 2764469) B2764469
theorem B3112739 : Blo 1638018 3112739 := bstep (se 1 (by rfl) ⟨2334554, by rfl⟩ : syracuseStep 3112739 = 4669109) B4669109
theorem B1638195 : Blo 1638018 1638195 := bstep (se 1 (by rfl) ⟨1228646, by rfl⟩ : syracuseStep 1638195 = 2457293) B2457293
theorem B2457395 : Blo 1638018 2457395 := bstep (se 1 (by rfl) ⟨1843046, by rfl⟩ : syracuseStep 2457395 = 3686093) B3686093
theorem B1638211 : Blo 1638018 1638211 := bstep (se 1 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 1638211 = 2457317) B2457317
theorem B2457425 : Blo 1638018 2457425 := bstep (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) B1843069
theorem B3940177 : Blo 1638018 3940177 := bstep (se 2 (by rfl) ⟨1477566, by rfl⟩ : syracuseStep 3940177 = 2955133) B2955133
theorem B1638227 : Blo 1638018 1638227 := bstep (se 1 (by rfl) ⟨1228670, by rfl⟩ : syracuseStep 1638227 = 2457341) B2457341
theorem B1638243 : Blo 1638018 1638243 := bstep (se 1 (by rfl) ⟨1228682, by rfl⟩ : syracuseStep 1638243 = 2457365) B2457365
theorem B2457443 : Blo 1638018 2457443 := bstep (se 1 (by rfl) ⟨1843082, by rfl⟩ : syracuseStep 2457443 = 3686165) B3686165
theorem B2334577 : Blo 1638018 2334577 := bstep (se 2 (by rfl) ⟨875466, by rfl⟩ : syracuseStep 2334577 = 1750933) B1750933
theorem B1638259 : Blo 1638018 1638259 := bstep (se 1 (by rfl) ⟨1228694, by rfl⟩ : syracuseStep 1638259 = 2457389) B2457389
theorem B2457473 : Blo 1638018 2457473 := bstep (se 2 (by rfl) ⟨921552, by rfl⟩ : syracuseStep 2457473 = 1843105) B1843105
theorem B1638275 : Blo 1638018 1638275 := bstep (se 1 (by rfl) ⟨1228706, by rfl⟩ : syracuseStep 1638275 = 2457413) B2457413
theorem B1638291 : Blo 1638018 1638291 := bstep (se 1 (by rfl) ⟨1228718, by rfl⟩ : syracuseStep 1638291 = 2457437) B2457437
theorem B2457491 : Blo 1638018 2457491 := bstep (se 1 (by rfl) ⟨1843118, by rfl⟩ : syracuseStep 2457491 = 3686237) B3686237
theorem B1638307 : Blo 1638018 1638307 := bstep (se 1 (by rfl) ⟨1228730, by rfl⟩ : syracuseStep 1638307 = 2457461) B2457461
theorem B2457521 : Blo 1638018 2457521 := bstep (se 2 (by rfl) ⟨921570, by rfl⟩ : syracuseStep 2457521 = 1843141) B1843141
theorem B1638323 : Blo 1638018 1638323 := bstep (se 1 (by rfl) ⟨1228742, by rfl⟩ : syracuseStep 1638323 = 2457485) B2457485
theorem B1843123 : Blo 1638018 1843123 := bstep (se 1 (by rfl) ⟨1382342, by rfl⟩ : syracuseStep 1843123 = 2764685) B2764685
theorem B1638339 : Blo 1638018 1638339 := bstep (se 1 (by rfl) ⟨1228754, by rfl⟩ : syracuseStep 1638339 = 2457509) B2457509
theorem B2457539 : Blo 1638018 2457539 := bstep (se 1 (by rfl) ⟨1843154, by rfl⟩ : syracuseStep 2457539 = 3686309) B3686309
theorem B1638355 : Blo 1638018 1638355 := bstep (se 1 (by rfl) ⟨1228766, by rfl⟩ : syracuseStep 1638355 = 2457533) B2457533
theorem B2457569 : Blo 1638018 2457569 := bstep (se 2 (by rfl) ⟨921588, by rfl⟩ : syracuseStep 2457569 = 1843177) B1843177
theorem B1638371 : Blo 1638018 1638371 := bstep (se 1 (by rfl) ⟨1228778, by rfl⟩ : syracuseStep 1638371 = 2457557) B2457557
theorem B2334691 : Blo 1638018 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B1638387 : Blo 1638018 1638387 := bstep (se 1 (by rfl) ⟨1228790, by rfl⟩ : syracuseStep 1638387 = 2457581) B2457581
theorem B2457587 : Blo 1638018 2457587 := bstep (se 1 (by rfl) ⟨1843190, by rfl⟩ : syracuseStep 2457587 = 3686381) B3686381
theorem B2457611 : Blo 1638018 2457611 := bstep (se 1 (by rfl) ⟨1843208, by rfl⟩ : syracuseStep 2457611 = 3686417) B3686417
theorem B1638411 : Blo 1638018 1638411 := bstep (se 1 (by rfl) ⟨1228808, by rfl⟩ : syracuseStep 1638411 = 2457617) B2457617
theorem B7004177 : Blo 1638018 7004177 := bstep (se 2 (by rfl) ⟨2626566, by rfl⟩ : syracuseStep 7004177 = 5253133) B5253133
theorem B2457623 : Blo 1638018 2457623 := bstep (se 1 (by rfl) ⟨1843217, by rfl⟩ : syracuseStep 2457623 = 3686435) B3686435
theorem B1638423 : Blo 1638018 1638423 := bstep (se 1 (by rfl) ⟨1228817, by rfl⟩ : syracuseStep 1638423 = 2457635) B2457635
theorem B1638443 : Blo 1638018 1638443 := bstep (se 1 (by rfl) ⟨1228832, by rfl⟩ : syracuseStep 1638443 = 2457665) B2457665
theorem B1638455 : Blo 1638018 1638455 := bstep (se 1 (by rfl) ⟨1228841, by rfl⟩ : syracuseStep 1638455 = 2457683) B2457683
theorem B1638475 : Blo 1638018 1638475 := bstep (se 1 (by rfl) ⟨1228856, by rfl⟩ : syracuseStep 1638475 = 2457713) B2457713
theorem B1638487 : Blo 1638018 1638487 := bstep (se 1 (by rfl) ⟨1228865, by rfl⟩ : syracuseStep 1638487 = 2457731) B2457731
theorem B3686489 : Blo 1638018 3686489 := bstep (se 2 (by rfl) ⟨1382433, by rfl⟩ : syracuseStep 3686489 = 2764867) B2764867
theorem B2457689 : Blo 1638018 2457689 := bstep (se 2 (by rfl) ⟨921633, by rfl⟩ : syracuseStep 2457689 = 1843267) B1843267
theorem B1638507 : Blo 1638018 1638507 := bstep (se 1 (by rfl) ⟨1228880, by rfl⟩ : syracuseStep 1638507 = 2457761) B2457761
theorem B1638519 : Blo 1638018 1638519 := bstep (se 1 (by rfl) ⟨1228889, by rfl⟩ : syracuseStep 1638519 = 2457779) B2457779
theorem B1843339 : Blo 1638018 1843339 := bstep (se 1 (by rfl) ⟨1382504, by rfl⟩ : syracuseStep 1843339 = 2765009) B2765009
theorem B1638539 : Blo 1638018 1638539 := bstep (se 1 (by rfl) ⟨1228904, by rfl⟩ : syracuseStep 1638539 = 2457809) B2457809
theorem B1638551 : Blo 1638018 1638551 := bstep (se 1 (by rfl) ⟨1228913, by rfl⟩ : syracuseStep 1638551 = 2457827) B2457827
theorem B1638571 : Blo 1638018 1638571 := bstep (se 1 (by rfl) ⟨1228928, by rfl⟩ : syracuseStep 1638571 = 2457857) B2457857
theorem B3686579 : Blo 1638018 3686579 := bstep (se 1 (by rfl) ⟨2764934, by rfl⟩ : syracuseStep 3686579 = 5529869) B5529869
theorem B1638583 : Blo 1638018 1638583 := bstep (se 1 (by rfl) ⟨1228937, by rfl⟩ : syracuseStep 1638583 = 2457875) B2457875
theorem B2457803 : Blo 1638018 2457803 := bstep (se 1 (by rfl) ⟨1843352, by rfl⟩ : syracuseStep 2457803 = 3686705) B3686705
theorem B1638603 : Blo 1638018 1638603 := bstep (se 1 (by rfl) ⟨1228952, by rfl⟩ : syracuseStep 1638603 = 2457905) B2457905
theorem B3154123 : Blo 1638018 3154123 := bstep (se 1 (by rfl) ⟨2365592, by rfl⟩ : syracuseStep 3154123 = 4731185) B4731185
theorem B3686615 : Blo 1638018 3686615 := bstep (se 1 (by rfl) ⟨2764961, by rfl⟩ : syracuseStep 3686615 = 5529923) B5529923
theorem B2457815 : Blo 1638018 2457815 := bstep (se 1 (by rfl) ⟨1843361, by rfl⟩ : syracuseStep 2457815 = 3686723) B3686723
theorem B1638615 : Blo 1638018 1638615 := bstep (se 1 (by rfl) ⟨1228961, by rfl⟩ : syracuseStep 1638615 = 2457923) B2457923
theorem B1638635 : Blo 1638018 1638635 := bstep (se 1 (by rfl) ⟨1228976, by rfl⟩ : syracuseStep 1638635 = 2457953) B2457953
theorem B1843447 : Blo 1638018 1843447 := bstep (se 1 (by rfl) ⟨1382585, by rfl⟩ : syracuseStep 1843447 = 2765171) B2765171
theorem B1638647 : Blo 1638018 1638647 := bstep (se 1 (by rfl) ⟨1228985, by rfl⟩ : syracuseStep 1638647 = 2457971) B2457971
theorem B1638667 : Blo 1638018 1638667 := bstep (se 1 (by rfl) ⟨1229000, by rfl⟩ : syracuseStep 1638667 = 2458001) B2458001
theorem B1638679 : Blo 1638018 1638679 := bstep (se 1 (by rfl) ⟨1229009, by rfl⟩ : syracuseStep 1638679 = 2458019) B2458019
theorem B2457881 : Blo 1638018 2457881 := bstep (se 2 (by rfl) ⟨921705, by rfl⟩ : syracuseStep 2457881 = 1843411) B1843411
theorem B1638699 : Blo 1638018 1638699 := bstep (se 1 (by rfl) ⟨1229024, by rfl⟩ : syracuseStep 1638699 = 2458049) B2458049
theorem B1638711 : Blo 1638018 1638711 := bstep (se 1 (by rfl) ⟨1229033, by rfl⟩ : syracuseStep 1638711 = 2458067) B2458067
theorem B1638731 : Blo 1638018 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B1638743 : Blo 1638018 1638743 := bstep (se 1 (by rfl) ⟨1229057, by rfl⟩ : syracuseStep 1638743 = 2458115) B2458115
theorem B1638763 : Blo 1638018 1638763 := bstep (se 1 (by rfl) ⟨1229072, by rfl⟩ : syracuseStep 1638763 = 2458145) B2458145
theorem B1638775 : Blo 1638018 1638775 := bstep (se 1 (by rfl) ⟨1229081, by rfl⟩ : syracuseStep 1638775 = 2458163) B2458163
theorem B3686795 : Blo 1638018 3686795 := bstep (se 1 (by rfl) ⟨2765096, by rfl⟩ : syracuseStep 3686795 = 5530193) B5530193
theorem B2457995 : Blo 1638018 2457995 := bstep (se 1 (by rfl) ⟨1843496, by rfl⟩ : syracuseStep 2457995 = 3686993) B3686993
theorem B1638795 : Blo 1638018 1638795 := bstep (se 1 (by rfl) ⟨1229096, by rfl⟩ : syracuseStep 1638795 = 2458193) B2458193
theorem B2458007 : Blo 1638018 2458007 := bstep (se 1 (by rfl) ⟨1843505, by rfl⟩ : syracuseStep 2458007 = 3687011) B3687011
theorem B1638807 : Blo 1638018 1638807 := bstep (se 1 (by rfl) ⟨1229105, by rfl⟩ : syracuseStep 1638807 = 2458211) B2458211
theorem B1638827 : Blo 1638018 1638827 := bstep (se 1 (by rfl) ⟨1229120, by rfl⟩ : syracuseStep 1638827 = 2458241) B2458241
theorem B1843627 : Blo 1638018 1843627 := bstep (se 1 (by rfl) ⟨1382720, by rfl⟩ : syracuseStep 1843627 = 2765441) B2765441
theorem B3989939 : Blo 1638018 3989939 := bstep (se 1 (by rfl) ⟨2992454, by rfl⟩ : syracuseStep 3989939 = 5984909) B5984909
theorem B1638839 : Blo 1638018 1638839 := bstep (se 1 (by rfl) ⟨1229129, by rfl⟩ : syracuseStep 1638839 = 2458259) B2458259
theorem B3686849 : Blo 1638018 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B1638859 : Blo 1638018 1638859 := bstep (se 1 (by rfl) ⟨1229144, by rfl⟩ : syracuseStep 1638859 = 2458289) B2458289
theorem B1638871 : Blo 1638018 1638871 := bstep (se 1 (by rfl) ⟨1229153, by rfl⟩ : syracuseStep 1638871 = 2458307) B2458307
theorem B26567129 : Blo 1638018 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B2458073 : Blo 1638018 2458073 := bstep (se 2 (by rfl) ⟨921777, by rfl⟩ : syracuseStep 2458073 = 1843555) B1843555
theorem B1638891 : Blo 1638018 1638891 := bstep (se 1 (by rfl) ⟨1229168, by rfl⟩ : syracuseStep 1638891 = 2458337) B2458337
theorem B1638903 : Blo 1638018 1638903 := bstep (se 1 (by rfl) ⟨1229177, by rfl⟩ : syracuseStep 1638903 = 2458355) B2458355
theorem B1638923 : Blo 1638018 1638923 := bstep (se 1 (by rfl) ⟨1229192, by rfl⟩ : syracuseStep 1638923 = 2458385) B2458385
theorem B1843735 : Blo 1638018 1843735 := bstep (se 1 (by rfl) ⟨1382801, by rfl⟩ : syracuseStep 1843735 = 2765603) B2765603
theorem B1638935 : Blo 1638018 1638935 := bstep (se 1 (by rfl) ⟨1229201, by rfl⟩ : syracuseStep 1638935 = 2458403) B2458403
theorem B11969059 : Blo 1638018 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B1638955 : Blo 1638018 1638955 := bstep (se 1 (by rfl) ⟨1229216, by rfl⟩ : syracuseStep 1638955 = 2458433) B2458433
theorem B1638967 : Blo 1638018 1638967 := bstep (se 1 (by rfl) ⟨1229225, by rfl⟩ : syracuseStep 1638967 = 2458451) B2458451
theorem B2458187 : Blo 1638018 2458187 := bstep (se 1 (by rfl) ⟨1843640, by rfl⟩ : syracuseStep 2458187 = 3687281) B3687281
theorem B1638987 : Blo 1638018 1638987 := bstep (se 1 (by rfl) ⟨1229240, by rfl⟩ : syracuseStep 1638987 = 2458481) B2458481
theorem B2458199 : Blo 1638018 2458199 := bstep (se 1 (by rfl) ⟨1843649, by rfl⟩ : syracuseStep 2458199 = 3687299) B3687299
theorem B1638999 : Blo 1638018 1638999 := bstep (se 1 (by rfl) ⟨1229249, by rfl⟩ : syracuseStep 1638999 = 2458499) B2458499
theorem B1639019 : Blo 1638018 1639019 := bstep (se 1 (by rfl) ⟨1229264, by rfl⟩ : syracuseStep 1639019 = 2458529) B2458529
theorem B1639031 : Blo 1638018 1639031 := bstep (se 1 (by rfl) ⟨1229273, by rfl⟩ : syracuseStep 1639031 = 2458547) B2458547
theorem B1639051 : Blo 1638018 1639051 := bstep (se 1 (by rfl) ⟨1229288, by rfl⟩ : syracuseStep 1639051 = 2458577) B2458577
theorem B1639063 : Blo 1638018 1639063 := bstep (se 1 (by rfl) ⟨1229297, by rfl⟩ : syracuseStep 1639063 = 2458595) B2458595
theorem B3687065 : Blo 1638018 3687065 := bstep (se 2 (by rfl) ⟨1382649, by rfl⟩ : syracuseStep 3687065 = 2765299) B2765299
theorem B2458265 : Blo 1638018 2458265 := bstep (se 2 (by rfl) ⟨921849, by rfl⟩ : syracuseStep 2458265 = 1843699) B1843699
theorem B1639083 : Blo 1638018 1639083 := bstep (se 1 (by rfl) ⟨1229312, by rfl⟩ : syracuseStep 1639083 = 2458625) B2458625
theorem B1639095 : Blo 1638018 1639095 := bstep (se 1 (by rfl) ⟨1229321, by rfl⟩ : syracuseStep 1639095 = 2458643) B2458643
theorem B1843915 : Blo 1638018 1843915 := bstep (se 1 (by rfl) ⟨1382936, by rfl⟩ : syracuseStep 1843915 = 2765873) B2765873
theorem B1639115 : Blo 1638018 1639115 := bstep (se 1 (by rfl) ⟨1229336, by rfl⟩ : syracuseStep 1639115 = 2458673) B2458673
theorem B1639127 : Blo 1638018 1639127 := bstep (se 1 (by rfl) ⟨1229345, by rfl⟩ : syracuseStep 1639127 = 2458691) B2458691
theorem B7004893 : Blo 1638018 7004893 := bstep (se 3 (by rfl) ⟨1313417, by rfl⟩ : syracuseStep 7004893 = 2626835) B2626835
theorem B1639147 : Blo 1638018 1639147 := bstep (se 1 (by rfl) ⟨1229360, by rfl⟩ : syracuseStep 1639147 = 2458721) B2458721
theorem B3687155 : Blo 1638018 3687155 := bstep (se 1 (by rfl) ⟨2765366, by rfl⟩ : syracuseStep 3687155 = 5530733) B5530733
theorem B1639159 : Blo 1638018 1639159 := bstep (se 1 (by rfl) ⟨1229369, by rfl⟩ : syracuseStep 1639159 = 2458739) B2458739
theorem B2458379 : Blo 1638018 2458379 := bstep (se 1 (by rfl) ⟨1843784, by rfl⟩ : syracuseStep 2458379 = 3687569) B3687569
theorem B1639179 : Blo 1638018 1639179 := bstep (se 1 (by rfl) ⟨1229384, by rfl⟩ : syracuseStep 1639179 = 2458769) B2458769
theorem B8094481 : Blo 1638018 8094481 := bstep (se 2 (by rfl) ⟨3035430, by rfl⟩ : syracuseStep 8094481 = 6070861) B6070861
theorem B2073367 : Blo 1638018 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B3687191 : Blo 1638018 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B2458391 : Blo 1638018 2458391 := bstep (se 1 (by rfl) ⟨1843793, by rfl⟩ : syracuseStep 2458391 = 3687587) B3687587
theorem B1639191 : Blo 1638018 1639191 := bstep (se 1 (by rfl) ⟨1229393, by rfl⟩ : syracuseStep 1639191 = 2458787) B2458787
theorem B1639211 : Blo 1638018 1639211 := bstep (se 1 (by rfl) ⟨1229408, by rfl⟩ : syracuseStep 1639211 = 2458817) B2458817
theorem B6226739 : Blo 1638018 6226739 := bstep (se 1 (by rfl) ⟨4670054, by rfl⟩ : syracuseStep 6226739 = 9340109) B9340109
theorem B1844023 : Blo 1638018 1844023 := bstep (se 1 (by rfl) ⟨1383017, by rfl⟩ : syracuseStep 1844023 = 2766035) B2766035
theorem B1639223 : Blo 1638018 1639223 := bstep (se 1 (by rfl) ⟨1229417, by rfl⟩ : syracuseStep 1639223 = 2458835) B2458835
theorem B6226753 : Blo 1638018 6226753 := bstep (se 2 (by rfl) ⟨2335032, by rfl⟩ : syracuseStep 6226753 = 4670065) B4670065
theorem B7873355 : Blo 1638018 7873355 := bstep (se 1 (by rfl) ⟨5905016, by rfl⟩ : syracuseStep 7873355 = 11810033) B11810033
theorem B12616523 : Blo 1638018 12616523 := bstep (se 1 (by rfl) ⟨9462392, by rfl⟩ : syracuseStep 12616523 = 18924785) B18924785
theorem B1639243 : Blo 1638018 1639243 := bstep (se 1 (by rfl) ⟨1229432, by rfl⟩ : syracuseStep 1639243 = 2458865) B2458865
theorem B1639255 : Blo 1638018 1639255 := bstep (se 1 (by rfl) ⟨1229441, by rfl⟩ : syracuseStep 1639255 = 2458883) B2458883
theorem B2458457 : Blo 1638018 2458457 := bstep (se 2 (by rfl) ⟨921921, by rfl⟩ : syracuseStep 2458457 = 1843843) B1843843
theorem B1639275 : Blo 1638018 1639275 := bstep (se 1 (by rfl) ⟨1229456, by rfl⟩ : syracuseStep 1639275 = 2458913) B2458913
theorem B1639287 : Blo 1638018 1639287 := bstep (se 1 (by rfl) ⟨1229465, by rfl⟩ : syracuseStep 1639287 = 2458931) B2458931
theorem B1639307 : Blo 1638018 1639307 := bstep (se 1 (by rfl) ⟨1229480, by rfl⟩ : syracuseStep 1639307 = 2458961) B2458961
theorem B6996881 : Blo 1638018 6996881 := bstep (se 2 (by rfl) ⟨2623830, by rfl⟩ : syracuseStep 6996881 = 5247661) B5247661
theorem B1639319 : Blo 1638018 1639319 := bstep (se 1 (by rfl) ⟨1229489, by rfl⟩ : syracuseStep 1639319 = 2458979) B2458979
theorem B1639339 : Blo 1638018 1639339 := bstep (se 1 (by rfl) ⟨1229504, by rfl⟩ : syracuseStep 1639339 = 2459009) B2459009
theorem B1639351 : Blo 1638018 1639351 := bstep (se 1 (by rfl) ⟨1229513, by rfl⟩ : syracuseStep 1639351 = 2459027) B2459027
theorem B5530571 : Blo 1638018 5530571 := bstep (se 1 (by rfl) ⟨4147928, by rfl⟩ : syracuseStep 5530571 = 8295857) B8295857
theorem B3687371 : Blo 1638018 3687371 := bstep (se 1 (by rfl) ⟨2765528, by rfl⟩ : syracuseStep 3687371 = 5531057) B5531057
theorem B2458571 : Blo 1638018 2458571 := bstep (se 1 (by rfl) ⟨1843928, by rfl⟩ : syracuseStep 2458571 = 3687857) B3687857
theorem B1639371 : Blo 1638018 1639371 := bstep (se 1 (by rfl) ⟨1229528, by rfl⟩ : syracuseStep 1639371 = 2459057) B2459057
theorem B2802647 : Blo 1638018 2802647 := bstep (se 1 (by rfl) ⟨2101985, by rfl⟩ : syracuseStep 2802647 = 4203971) B4203971
theorem B2458583 : Blo 1638018 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B1639383 : Blo 1638018 1639383 := bstep (se 1 (by rfl) ⟨1229537, by rfl⟩ : syracuseStep 1639383 = 2459075) B2459075
theorem B1844203 : Blo 1638018 1844203 := bstep (se 1 (by rfl) ⟨1383152, by rfl⟩ : syracuseStep 1844203 = 2766305) B2766305
theorem B1639403 : Blo 1638018 1639403 := bstep (se 1 (by rfl) ⟨1229552, by rfl⟩ : syracuseStep 1639403 = 2459105) B2459105
theorem B3498995 : Blo 1638018 3498995 := bstep (se 1 (by rfl) ⟨2624246, by rfl⟩ : syracuseStep 3498995 = 5248493) B5248493
theorem B1639415 : Blo 1638018 1639415 := bstep (se 1 (by rfl) ⟨1229561, by rfl⟩ : syracuseStep 1639415 = 2459123) B2459123
theorem B3687425 : Blo 1638018 3687425 := bstep (se 2 (by rfl) ⟨1382784, by rfl⟩ : syracuseStep 3687425 = 2765569) B2765569
theorem B1639435 : Blo 1638018 1639435 := bstep (se 1 (by rfl) ⟨1229576, by rfl⟩ : syracuseStep 1639435 = 2459153) B2459153
theorem B1639447 : Blo 1638018 1639447 := bstep (se 1 (by rfl) ⟨1229585, by rfl⟩ : syracuseStep 1639447 = 2459171) B2459171
theorem B2458649 : Blo 1638018 2458649 := bstep (se 2 (by rfl) ⟨921993, by rfl⟩ : syracuseStep 2458649 = 1843987) B1843987
theorem B1639467 : Blo 1638018 1639467 := bstep (se 1 (by rfl) ⟨1229600, by rfl⟩ : syracuseStep 1639467 = 2459201) B2459201
theorem B1639479 : Blo 1638018 1639479 := bstep (se 1 (by rfl) ⟨1229609, by rfl⟩ : syracuseStep 1639479 = 2459219) B2459219
theorem B1639499 : Blo 1638018 1639499 := bstep (se 1 (by rfl) ⟨1229624, by rfl⟩ : syracuseStep 1639499 = 2459249) B2459249
theorem B1844311 : Blo 1638018 1844311 := bstep (se 1 (by rfl) ⟨1383233, by rfl⟩ : syracuseStep 1844311 = 2766467) B2766467
theorem B1639511 : Blo 1638018 1639511 := bstep (se 1 (by rfl) ⟨1229633, by rfl⟩ : syracuseStep 1639511 = 2459267) B2459267
theorem B21005405 : Blo 1638018 21005405 := bstep (se 3 (by rfl) ⟨3938513, by rfl⟩ : syracuseStep 21005405 = 7877027) B7877027
theorem B1639531 : Blo 1638018 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B1639543 : Blo 1638018 1639543 := bstep (se 1 (by rfl) ⟨1229657, by rfl⟩ : syracuseStep 1639543 = 2459315) B2459315
theorem B20997251 : Blo 1638018 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B2458763 : Blo 1638018 2458763 := bstep (se 1 (by rfl) ⟨1844072, by rfl⟩ : syracuseStep 2458763 = 3688145) B3688145
theorem B1639563 : Blo 1638018 1639563 := bstep (se 1 (by rfl) ⟨1229672, by rfl⟩ : syracuseStep 1639563 = 2459345) B2459345
theorem B2458775 : Blo 1638018 2458775 := bstep (se 1 (by rfl) ⟨1844081, by rfl⟩ : syracuseStep 2458775 = 3688163) B3688163
theorem B1639575 : Blo 1638018 1639575 := bstep (se 1 (by rfl) ⟨1229681, by rfl⟩ : syracuseStep 1639575 = 2459363) B2459363
theorem B1639595 : Blo 1638018 1639595 := bstep (se 1 (by rfl) ⟨1229696, by rfl⟩ : syracuseStep 1639595 = 2459393) B2459393
theorem B1639607 : Blo 1638018 1639607 := bstep (se 1 (by rfl) ⟨1229705, by rfl⟩ : syracuseStep 1639607 = 2459411) B2459411
theorem B1639627 : Blo 1638018 1639627 := bstep (se 1 (by rfl) ⟨1229720, by rfl⟩ : syracuseStep 1639627 = 2459441) B2459441
theorem B1639639 : Blo 1638018 1639639 := bstep (se 1 (by rfl) ⟨1229729, by rfl⟩ : syracuseStep 1639639 = 2459459) B2459459
theorem B11207897 : Blo 1638018 11207897 := bstep (se 2 (by rfl) ⟨4202961, by rfl⟩ : syracuseStep 11207897 = 8405923) B8405923
theorem B5530841 : Blo 1638018 5530841 := bstep (se 2 (by rfl) ⟨2074065, by rfl⟩ : syracuseStep 5530841 = 4148131) B4148131
theorem B3687641 : Blo 1638018 3687641 := bstep (se 2 (by rfl) ⟨1382865, by rfl⟩ : syracuseStep 3687641 = 2765731) B2765731
theorem B2458841 : Blo 1638018 2458841 := bstep (se 2 (by rfl) ⟨922065, by rfl⟩ : syracuseStep 2458841 = 1844131) B1844131
theorem B1639659 : Blo 1638018 1639659 := bstep (se 1 (by rfl) ⟨1229744, by rfl⟩ : syracuseStep 1639659 = 2459489) B2459489
theorem B1639671 : Blo 1638018 1639671 := bstep (se 1 (by rfl) ⟨1229753, by rfl⟩ : syracuseStep 1639671 = 2459507) B2459507
theorem B1844491 : Blo 1638018 1844491 := bstep (se 1 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 1844491 = 2766737) B2766737
theorem B1639691 : Blo 1638018 1639691 := bstep (se 1 (by rfl) ⟨1229768, by rfl⟩ : syracuseStep 1639691 = 2459537) B2459537
theorem B1639703 : Blo 1638018 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B1639723 : Blo 1638018 1639723 := bstep (se 1 (by rfl) ⟨1229792, by rfl⟩ : syracuseStep 1639723 = 2459585) B2459585
theorem B3687731 : Blo 1638018 3687731 := bstep (se 1 (by rfl) ⟨2765798, by rfl⟩ : syracuseStep 3687731 = 5531597) B5531597
theorem B1639735 : Blo 1638018 1639735 := bstep (se 1 (by rfl) ⟨1229801, by rfl⟩ : syracuseStep 1639735 = 2459603) B2459603
theorem B2458955 : Blo 1638018 2458955 := bstep (se 1 (by rfl) ⟨1844216, by rfl⟩ : syracuseStep 2458955 = 3688433) B3688433
theorem B1639755 : Blo 1638018 1639755 := bstep (se 1 (by rfl) ⟨1229816, by rfl⟩ : syracuseStep 1639755 = 2459633) B2459633
theorem B3687767 : Blo 1638018 3687767 := bstep (se 1 (by rfl) ⟨2765825, by rfl⟩ : syracuseStep 3687767 = 5531651) B5531651
theorem B2458967 : Blo 1638018 2458967 := bstep (se 1 (by rfl) ⟨1844225, by rfl⟩ : syracuseStep 2458967 = 3688451) B3688451
theorem B1639767 : Blo 1638018 1639767 := bstep (se 1 (by rfl) ⟨1229825, by rfl⟩ : syracuseStep 1639767 = 2459651) B2459651
theorem B1639787 : Blo 1638018 1639787 := bstep (se 1 (by rfl) ⟨1229840, by rfl⟩ : syracuseStep 1639787 = 2459681) B2459681
theorem B1844599 : Blo 1638018 1844599 := bstep (se 1 (by rfl) ⟨1383449, by rfl⟩ : syracuseStep 1844599 = 2766899) B2766899
theorem B1639799 : Blo 1638018 1639799 := bstep (se 1 (by rfl) ⟨1229849, by rfl⟩ : syracuseStep 1639799 = 2459699) B2459699
theorem B8299907 : Blo 1638018 8299907 := bstep (se 1 (by rfl) ⟨6224930, by rfl⟩ : syracuseStep 8299907 = 12449861) B12449861
theorem B1639819 : Blo 1638018 1639819 := bstep (se 1 (by rfl) ⟨1229864, by rfl⟩ : syracuseStep 1639819 = 2459729) B2459729
theorem B35431829 : Blo 1638018 35431829 := bstep (se 6 (by rfl) ⟨830433, by rfl⟩ : syracuseStep 35431829 = 1660867) B1660867
theorem B1639831 : Blo 1638018 1639831 := bstep (se 1 (by rfl) ⟨1229873, by rfl⟩ : syracuseStep 1639831 = 2459747) B2459747
theorem B2459033 : Blo 1638018 2459033 := bstep (se 2 (by rfl) ⟨922137, by rfl⟩ : syracuseStep 2459033 = 1844275) B1844275
theorem B1639851 : Blo 1638018 1639851 := bstep (se 1 (by rfl) ⟨1229888, by rfl⟩ : syracuseStep 1639851 = 2459777) B2459777
theorem B12617137 : Blo 1638018 12617137 := bstep (se 2 (by rfl) ⟨4731426, by rfl⟩ : syracuseStep 12617137 = 9462853) B9462853
theorem B1639863 : Blo 1638018 1639863 := bstep (se 1 (by rfl) ⟨1229897, by rfl⟩ : syracuseStep 1639863 = 2459795) B2459795
theorem B1639883 : Blo 1638018 1639883 := bstep (se 1 (by rfl) ⟨1229912, by rfl⟩ : syracuseStep 1639883 = 2459825) B2459825
theorem B1639895 : Blo 1638018 1639895 := bstep (se 1 (by rfl) ⟨1229921, by rfl⟩ : syracuseStep 1639895 = 2459843) B2459843
theorem B1639915 : Blo 1638018 1639915 := bstep (se 1 (by rfl) ⟨1229936, by rfl⟩ : syracuseStep 1639915 = 2459873) B2459873
theorem B1639927 : Blo 1638018 1639927 := bstep (se 1 (by rfl) ⟨1229945, by rfl⟩ : syracuseStep 1639927 = 2459891) B2459891
theorem B3687947 : Blo 1638018 3687947 := bstep (se 1 (by rfl) ⟨2765960, by rfl⟩ : syracuseStep 3687947 = 5531921) B5531921
theorem B2459147 : Blo 1638018 2459147 := bstep (se 1 (by rfl) ⟨1844360, by rfl⟩ : syracuseStep 2459147 = 3688721) B3688721
theorem B1639947 : Blo 1638018 1639947 := bstep (se 1 (by rfl) ⟨1229960, by rfl⟩ : syracuseStep 1639947 = 2459921) B2459921
theorem B2459159 : Blo 1638018 2459159 := bstep (se 1 (by rfl) ⟨1844369, by rfl⟩ : syracuseStep 2459159 = 3688739) B3688739
theorem B1639959 : Blo 1638018 1639959 := bstep (se 1 (by rfl) ⟨1229969, by rfl⟩ : syracuseStep 1639959 = 2459939) B2459939
theorem B1844779 : Blo 1638018 1844779 := bstep (se 1 (by rfl) ⟨1383584, by rfl⟩ : syracuseStep 1844779 = 2767169) B2767169
theorem B1639979 : Blo 1638018 1639979 := bstep (se 1 (by rfl) ⟨1229984, by rfl⟩ : syracuseStep 1639979 = 2459969) B2459969
theorem B1639991 : Blo 1638018 1639991 := bstep (se 1 (by rfl) ⟨1229993, by rfl⟩ : syracuseStep 1639991 = 2459987) B2459987
theorem B3688001 : Blo 1638018 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B4982347 : Blo 1638018 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B2074187 : Blo 1638018 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B1640011 : Blo 1638018 1640011 := bstep (se 1 (by rfl) ⟨1230008, by rfl⟩ : syracuseStep 1640011 = 2460017) B2460017
theorem B2459225 : Blo 1638018 2459225 := bstep (se 2 (by rfl) ⟨922209, by rfl⟩ : syracuseStep 2459225 = 1844419) B1844419
theorem B6735491 : Blo 1638018 6735491 := bstep (se 1 (by rfl) ⟨5051618, by rfl⟩ : syracuseStep 6735491 = 10103237) B10103237
theorem B201942659 : Blo 1638018 201942659 := bstep (se 1 (by rfl) ⟨151456994, by rfl⟩ : syracuseStep 201942659 = 302913989) B302913989
theorem B1844887 : Blo 1638018 1844887 := bstep (se 1 (by rfl) ⟨1383665, by rfl⟩ : syracuseStep 1844887 = 2767331) B2767331
theorem B5990081 : Blo 1638018 5990081 := bstep (se 2 (by rfl) ⟨2246280, by rfl⟩ : syracuseStep 5990081 = 4492561) B4492561
theorem B2459339 : Blo 1638018 2459339 := bstep (se 1 (by rfl) ⟨1844504, by rfl⟩ : syracuseStep 2459339 = 3689009) B3689009
theorem B2459351 : Blo 1638018 2459351 := bstep (se 1 (by rfl) ⟨1844513, by rfl⟩ : syracuseStep 2459351 = 3689027) B3689027
theorem B5252825 : Blo 1638018 5252825 := bstep (se 2 (by rfl) ⟨1969809, by rfl⟩ : syracuseStep 5252825 = 3939619) B3939619
theorem B5908247 : Blo 1638018 5908247 := bstep (se 1 (by rfl) ⟨4431185, by rfl⟩ : syracuseStep 5908247 = 8862371) B8862371
theorem B4048663 : Blo 1638018 4048663 := bstep (se 1 (by rfl) ⟨3036497, by rfl⟩ : syracuseStep 4048663 = 6072995) B6072995
theorem B3688217 : Blo 1638018 3688217 := bstep (se 2 (by rfl) ⟨1383081, by rfl⟩ : syracuseStep 3688217 = 2766163) B2766163
theorem B2459417 : Blo 1638018 2459417 := bstep (se 2 (by rfl) ⟨922281, by rfl⟩ : syracuseStep 2459417 = 1844563) B1844563
theorem B4982579 : Blo 1638018 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B13993793 : Blo 1638018 13993793 := bstep (se 2 (by rfl) ⟨5247672, by rfl⟩ : syracuseStep 13993793 = 10495345) B10495345
theorem B6997853 : Blo 1638018 6997853 := bstep (se 3 (by rfl) ⟨1312097, by rfl⟩ : syracuseStep 6997853 = 2624195) B2624195
theorem B3688307 : Blo 1638018 3688307 := bstep (se 1 (by rfl) ⟨2766230, by rfl⟩ : syracuseStep 3688307 = 5532461) B5532461
theorem B2459531 : Blo 1638018 2459531 := bstep (se 1 (by rfl) ⟨1844648, by rfl⟩ : syracuseStep 2459531 = 3689297) B3689297
theorem B5531543 : Blo 1638018 5531543 := bstep (se 1 (by rfl) ⟨4148657, by rfl⟩ : syracuseStep 5531543 = 8297315) B8297315
theorem B3688343 : Blo 1638018 3688343 := bstep (se 1 (by rfl) ⟨2766257, by rfl⟩ : syracuseStep 3688343 = 5532515) B5532515
theorem B2459543 : Blo 1638018 2459543 := bstep (se 1 (by rfl) ⟨1844657, by rfl⟩ : syracuseStep 2459543 = 3689315) B3689315
theorem B6219737 : Blo 1638018 6219737 := bstep (se 2 (by rfl) ⟨2332401, by rfl⟩ : syracuseStep 6219737 = 4664803) B4664803
theorem B2459609 : Blo 1638018 2459609 := bstep (se 2 (by rfl) ⟨922353, by rfl⟩ : syracuseStep 2459609 = 1844707) B1844707
theorem B3688523 : Blo 1638018 3688523 := bstep (se 1 (by rfl) ⟨2766392, by rfl⟩ : syracuseStep 3688523 = 5532785) B5532785
theorem B2459723 : Blo 1638018 2459723 := bstep (se 1 (by rfl) ⟨1844792, by rfl⟩ : syracuseStep 2459723 = 3689585) B3689585
theorem B2459735 : Blo 1638018 2459735 := bstep (se 1 (by rfl) ⟨1844801, by rfl⟩ : syracuseStep 2459735 = 3689603) B3689603
theorem B3688577 : Blo 1638018 3688577 := bstep (se 2 (by rfl) ⟨1383216, by rfl⟩ : syracuseStep 3688577 = 2766433) B2766433
theorem B10504343 : Blo 1638018 10504343 := bstep (se 1 (by rfl) ⟨7878257, by rfl⟩ : syracuseStep 10504343 = 15756515) B15756515
theorem B2459801 : Blo 1638018 2459801 := bstep (se 2 (by rfl) ⟨922425, by rfl⟩ : syracuseStep 2459801 = 1844851) B1844851
theorem B6219949 : Blo 1638018 6219949 := bstep (se 3 (by rfl) ⟨1166240, by rfl⟩ : syracuseStep 6219949 = 2332481) B2332481
theorem B2074891 : Blo 1638018 2074891 := bstep (se 1 (by rfl) ⟨1556168, by rfl⟩ : syracuseStep 2074891 = 3112337) B3112337
theorem B2459915 : Blo 1638018 2459915 := bstep (se 1 (by rfl) ⟨1844936, by rfl⟩ : syracuseStep 2459915 = 3689873) B3689873
theorem B2459927 : Blo 1638018 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B12618059 : Blo 1638018 12618059 := bstep (se 1 (by rfl) ⟨9463544, by rfl⟩ : syracuseStep 12618059 = 18927089) B18927089
theorem B3688793 : Blo 1638018 3688793 := bstep (se 2 (by rfl) ⟨1383297, by rfl⟩ : syracuseStep 3688793 = 2766595) B2766595
theorem B2459993 : Blo 1638018 2459993 := bstep (se 2 (by rfl) ⟨922497, by rfl⟩ : syracuseStep 2459993 = 1844995) B1844995
theorem B63883637 : Blo 1638018 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B18663857 : Blo 1638018 18663857 := bstep (se 2 (by rfl) ⟨6998946, by rfl⟩ : syracuseStep 18663857 = 13997893) B13997893
theorem B5532083 : Blo 1638018 5532083 := bstep (se 1 (by rfl) ⟨4149062, by rfl⟩ : syracuseStep 5532083 = 8298125) B8298125
theorem B3688883 : Blo 1638018 3688883 := bstep (se 1 (by rfl) ⟨2766662, by rfl⟩ : syracuseStep 3688883 = 5533325) B5533325
theorem B5253569 : Blo 1638018 5253569 := bstep (se 2 (by rfl) ⟨1970088, by rfl⟩ : syracuseStep 5253569 = 3940177) B3940177
theorem B3500491 : Blo 1638018 3500491 := bstep (se 1 (by rfl) ⟨2625368, by rfl⟩ : syracuseStep 3500491 = 5250737) B5250737
theorem B3688919 : Blo 1638018 3688919 := bstep (se 1 (by rfl) ⟨2766689, by rfl⟩ : syracuseStep 3688919 = 5533379) B5533379
theorem B6220253 : Blo 1638018 6220253 := bstep (se 3 (by rfl) ⟨1166297, by rfl⟩ : syracuseStep 6220253 = 2332595) B2332595
theorem B2075159 : Blo 1638018 2075159 := bstep (se 1 (by rfl) ⟨1556369, by rfl⟩ : syracuseStep 2075159 = 3112739) B3112739
theorem B2214425 : Blo 1638018 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B4147787 : Blo 1638018 4147787 := bstep (se 1 (by rfl) ⟨3110840, by rfl⟩ : syracuseStep 4147787 = 6221681) B6221681
theorem B9964133 : Blo 1638018 9964133 := bstep (se 4 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 9964133 = 1868275) B1868275
theorem B3689099 : Blo 1638018 3689099 := bstep (se 1 (by rfl) ⟨2766824, by rfl⟩ : syracuseStep 3689099 = 5533649) B5533649
theorem B7473815 : Blo 1638018 7473815 := bstep (se 1 (by rfl) ⟨5605361, by rfl⟩ : syracuseStep 7473815 = 11210723) B11210723
theorem B5532353 : Blo 1638018 5532353 := bstep (se 2 (by rfl) ⟨2074632, by rfl⟩ : syracuseStep 5532353 = 4149265) B4149265
theorem B3689153 : Blo 1638018 3689153 := bstep (se 2 (by rfl) ⟨1383432, by rfl⟩ : syracuseStep 3689153 = 2766865) B2766865
theorem B99830485 : Blo 1638018 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B5606167 : Blo 1638018 5606167 := bstep (se 1 (by rfl) ⟨4204625, by rfl⟩ : syracuseStep 5606167 = 8409251) B8409251
theorem B9333569 : Blo 1638018 9333569 := bstep (se 2 (by rfl) ⟨3500088, by rfl⟩ : syracuseStep 9333569 = 7000177) B7000177
theorem B2624395 : Blo 1638018 2624395 := bstep (se 1 (by rfl) ⟨1968296, by rfl⟩ : syracuseStep 2624395 = 3936593) B3936593
theorem B3689369 : Blo 1638018 3689369 := bstep (se 2 (by rfl) ⟨1383513, by rfl⟩ : syracuseStep 3689369 = 2767027) B2767027
theorem B15748019 : Blo 1638018 15748019 := bstep (se 1 (by rfl) ⟨11811014, by rfl⟩ : syracuseStep 15748019 = 23622029) B23622029
theorem B67251161 : Blo 1638018 67251161 := bstep (se 2 (by rfl) ⟨25219185, by rfl⟩ : syracuseStep 67251161 = 50438371) B50438371
theorem B4983769 : Blo 1638018 4983769 := bstep (se 2 (by rfl) ⟨1868913, by rfl⟩ : syracuseStep 4983769 = 3737827) B3737827
theorem B3689459 : Blo 1638018 3689459 := bstep (se 1 (by rfl) ⟨2767094, by rfl⟩ : syracuseStep 3689459 = 5534189) B5534189
theorem B3689495 : Blo 1638018 3689495 := bstep (se 1 (by rfl) ⟨2767121, by rfl⟩ : syracuseStep 3689495 = 5534243) B5534243
theorem B8858717 : Blo 1638018 8858717 := bstep (se 3 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 8858717 = 3322019) B3322019
theorem B28019843 : Blo 1638018 28019843 := bstep (se 1 (by rfl) ⟨21014882, by rfl⟩ : syracuseStep 28019843 = 42029765) B42029765
theorem B2624651 : Blo 1638018 2624651 := bstep (se 1 (by rfl) ⟨1968488, by rfl⟩ : syracuseStep 2624651 = 3936977) B3936977
theorem B3689675 : Blo 1638018 3689675 := bstep (se 1 (by rfl) ⟨2767256, by rfl⟩ : syracuseStep 3689675 = 5534513) B5534513
theorem B5532893 : Blo 1638018 5532893 := bstep (se 3 (by rfl) ⟨1037417, by rfl⟩ : syracuseStep 5532893 = 2074835) B2074835
theorem B3689729 : Blo 1638018 3689729 := bstep (se 2 (by rfl) ⟨1383648, by rfl⟩ : syracuseStep 3689729 = 2767297) B2767297
theorem B3739031 : Blo 1638018 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B4795841 : Blo 1638018 4795841 := bstep (se 2 (by rfl) ⟨1798440, by rfl⟩ : syracuseStep 4795841 = 3596881) B3596881
theorem B3689945 : Blo 1638018 3689945 := bstep (se 2 (by rfl) ⟨1383729, by rfl⟩ : syracuseStep 3689945 = 2767459) B2767459
theorem B4148759 : Blo 1638018 4148759 := bstep (se 1 (by rfl) ⟨3111569, by rfl⟩ : syracuseStep 4148759 = 6223139) B6223139
theorem B3690035 : Blo 1638018 3690035 := bstep (se 1 (by rfl) ⟨2767526, by rfl⟩ : syracuseStep 3690035 = 5535053) B5535053
theorem B26594891 : Blo 1638018 26594891 := bstep (se 1 (by rfl) ⟨19946168, by rfl⟩ : syracuseStep 26594891 = 39892337) B39892337
theorem B3501721 : Blo 1638018 3501721 := bstep (se 2 (by rfl) ⟨1313145, by rfl⟩ : syracuseStep 3501721 = 2626291) B2626291
theorem B2952883 : Blo 1638018 2952883 := bstep (se 1 (by rfl) ⟨2214662, by rfl⟩ : syracuseStep 2952883 = 4429325) B4429325
theorem B3935947 : Blo 1638018 3935947 := bstep (se 1 (by rfl) ⟨2951960, by rfl⟩ : syracuseStep 3935947 = 5903921) B5903921
theorem B4665053 : Blo 1638018 4665053 := bstep (se 3 (by rfl) ⟨874697, by rfl⟩ : syracuseStep 4665053 = 1749395) B1749395
theorem B2764631 : Blo 1638018 2764631 := bstep (se 1 (by rfl) ⟨2073473, by rfl⟩ : syracuseStep 2764631 = 4146947) B4146947
theorem B8294237 : Blo 1638018 8294237 := bstep (se 3 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 8294237 = 3110339) B3110339
theorem B2764759 : Blo 1638018 2764759 := bstep (se 1 (by rfl) ⟨2073569, by rfl⟩ : syracuseStep 2764759 = 4147139) B4147139
theorem B11972569 : Blo 1638018 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B2625625 : Blo 1638018 2625625 := bstep (se 2 (by rfl) ⟨984609, by rfl⟩ : syracuseStep 2625625 = 1969219) B1969219
theorem B2953331 : Blo 1638018 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B3739763 : Blo 1638018 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B4149427 : Blo 1638018 4149427 := bstep (se 1 (by rfl) ⟨3112070, by rfl⟩ : syracuseStep 4149427 = 6224141) B6224141
theorem B3936563 : Blo 1638018 3936563 := bstep (se 1 (by rfl) ⟨2952422, by rfl⟩ : syracuseStep 3936563 = 5904845) B5904845
theorem B4149569 : Blo 1638018 4149569 := bstep (se 2 (by rfl) ⟨1556088, by rfl⟩ : syracuseStep 4149569 = 3112177) B3112177
theorem B1749323 : Blo 1638018 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B5534027 : Blo 1638018 5534027 := bstep (se 1 (by rfl) ⟨4150520, by rfl⟩ : syracuseStep 5534027 = 8301041) B8301041
theorem B15749477 : Blo 1638018 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B7000451 : Blo 1638018 7000451 := bstep (se 1 (by rfl) ⟨5250338, by rfl⟩ : syracuseStep 7000451 = 10500677) B10500677
theorem B7098769 : Blo 1638018 7098769 := bstep (se 2 (by rfl) ⟨2662038, by rfl⟩ : syracuseStep 7098769 = 5324077) B5324077
theorem B3740147 : Blo 1638018 3740147 := bstep (se 1 (by rfl) ⟨2805110, by rfl⟩ : syracuseStep 3740147 = 5610221) B5610221
theorem B2765387 : Blo 1638018 2765387 := bstep (se 1 (by rfl) ⟨2074040, by rfl⟩ : syracuseStep 2765387 = 4148081) B4148081
theorem B10506827 : Blo 1638018 10506827 := bstep (se 1 (by rfl) ⟨7880120, by rfl⟩ : syracuseStep 10506827 = 15760241) B15760241
theorem B5534297 : Blo 1638018 5534297 := bstep (se 2 (by rfl) ⟨2075361, by rfl⟩ : syracuseStep 5534297 = 4150723) B4150723
theorem B2765515 : Blo 1638018 2765515 := bstep (se 1 (by rfl) ⟨2074136, by rfl⟩ : syracuseStep 2765515 = 4148273) B4148273
theorem B7000793 : Blo 1638018 7000793 := bstep (se 2 (by rfl) ⟨2625297, by rfl⟩ : syracuseStep 7000793 = 5250595) B5250595
theorem B2765657 : Blo 1638018 2765657 := bstep (se 2 (by rfl) ⟨1037121, by rfl⟩ : syracuseStep 2765657 = 2074243) B2074243
theorem B3109747 : Blo 1638018 3109747 := bstep (se 1 (by rfl) ⟨2332310, by rfl⟩ : syracuseStep 3109747 = 4664621) B4664621
theorem B2765785 : Blo 1638018 2765785 := bstep (se 2 (by rfl) ⟨1037169, by rfl⟩ : syracuseStep 2765785 = 2074339) B2074339
theorem B6222851 : Blo 1638018 6222851 := bstep (se 1 (by rfl) ⟨4667138, by rfl⟩ : syracuseStep 6222851 = 9334277) B9334277
theorem B6222865 : Blo 1638018 6222865 := bstep (se 2 (by rfl) ⟨2333574, by rfl⟩ : syracuseStep 6222865 = 4667149) B4667149
theorem B5534999 : Blo 1638018 5534999 := bstep (se 1 (by rfl) ⟨4151249, by rfl⟩ : syracuseStep 5534999 = 8302499) B8302499
theorem B6223169 : Blo 1638018 6223169 := bstep (se 2 (by rfl) ⟨2333688, by rfl⟩ : syracuseStep 6223169 = 4667377) B4667377
theorem B3110233 : Blo 1638018 3110233 := bstep (se 2 (by rfl) ⟨1166337, by rfl⟩ : syracuseStep 3110233 = 2332675) B2332675
theorem B5322077 : Blo 1638018 5322077 := bstep (se 3 (by rfl) ⟨997889, by rfl⟩ : syracuseStep 5322077 = 1995779) B1995779
theorem B1750519 : Blo 1638018 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B2766359 : Blo 1638018 2766359 := bstep (se 1 (by rfl) ⟨2074769, by rfl⟩ : syracuseStep 2766359 = 4149539) B4149539
theorem B14194211 : Blo 1638018 14194211 := bstep (se 1 (by rfl) ⟨10645658, by rfl⟩ : syracuseStep 14194211 = 21291317) B21291317
theorem B4150835 : Blo 1638018 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B4732481 : Blo 1638018 4732481 := bstep (se 2 (by rfl) ⟨1774680, by rfl⟩ : syracuseStep 4732481 = 3549361) B3549361
theorem B2766487 : Blo 1638018 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B2954945 : Blo 1638018 2954945 := bstep (se 2 (by rfl) ⟨1108104, by rfl⟩ : syracuseStep 2954945 = 2216209) B2216209
theorem B18675521 : Blo 1638018 18675521 := bstep (se 2 (by rfl) ⟨7003320, by rfl⟩ : syracuseStep 18675521 = 14006641) B14006641
theorem B23951203 : Blo 1638018 23951203 := bstep (se 1 (by rfl) ⟨17963402, by rfl⟩ : syracuseStep 23951203 = 35926805) B35926805
theorem B3110795 : Blo 1638018 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B2332567 : Blo 1638018 2332567 := bstep (se 1 (by rfl) ⟨1749425, by rfl⟩ : syracuseStep 2332567 = 3498851) B3498851
theorem B8296343 : Blo 1638018 8296343 := bstep (se 1 (by rfl) ⟨6222257, by rfl⟩ : syracuseStep 8296343 = 12444515) B12444515
theorem B2955161 : Blo 1638018 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B6223837 : Blo 1638018 6223837 := bstep (se 3 (by rfl) ⟨1166969, by rfl⟩ : syracuseStep 6223837 = 2333939) B2333939
theorem B4732951 : Blo 1638018 4732951 := bstep (se 1 (by rfl) ⟨3549713, by rfl⟩ : syracuseStep 4732951 = 7099427) B7099427
theorem B3110977 : Blo 1638018 3110977 := bstep (se 2 (by rfl) ⟨1166616, by rfl⟩ : syracuseStep 3110977 = 2333233) B2333233
theorem B10106981 : Blo 1638018 10106981 := bstep (se 4 (by rfl) ⟨947529, by rfl⟩ : syracuseStep 10106981 = 1895059) B1895059
theorem B2767115 : Blo 1638018 2767115 := bstep (se 1 (by rfl) ⟨2075336, by rfl⟩ : syracuseStep 2767115 = 4150673) B4150673
theorem B28006721 : Blo 1638018 28006721 := bstep (se 2 (by rfl) ⟨10502520, by rfl⟩ : syracuseStep 28006721 = 21005041) B21005041
theorem B2767243 : Blo 1638018 2767243 := bstep (se 1 (by rfl) ⟨2075432, by rfl⟩ : syracuseStep 2767243 = 4150865) B4150865
theorem B3938753 : Blo 1638018 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B17717777 : Blo 1638018 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B2767385 : Blo 1638018 2767385 := bstep (se 2 (by rfl) ⟨1037769, by rfl⟩ : syracuseStep 2767385 = 2075539) B2075539
theorem B4667969 : Blo 1638018 4667969 := bstep (se 2 (by rfl) ⟨1750488, by rfl⟩ : syracuseStep 4667969 = 3500977) B3500977
theorem B4667993 : Blo 1638018 4667993 := bstep (se 2 (by rfl) ⟨1750497, by rfl⟩ : syracuseStep 4667993 = 3500995) B3500995
theorem B14006915 : Blo 1638018 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B2767513 : Blo 1638018 2767513 := bstep (se 2 (by rfl) ⟨1037817, by rfl⟩ : syracuseStep 2767513 = 2075635) B2075635
theorem B5905075 : Blo 1638018 5905075 := bstep (se 1 (by rfl) ⟨4428806, by rfl⟩ : syracuseStep 5905075 = 8857613) B8857613
theorem B2333387 : Blo 1638018 2333387 := bstep (se 1 (by rfl) ⟨1750040, by rfl⟩ : syracuseStep 2333387 = 3500081) B3500081
theorem B3111691 : Blo 1638018 3111691 := bstep (se 1 (by rfl) ⟨2333768, by rfl⟩ : syracuseStep 3111691 = 4667537) B4667537
theorem B3111767 : Blo 1638018 3111767 := bstep (se 1 (by rfl) ⟨2333825, by rfl⟩ : syracuseStep 3111767 = 4667651) B4667651
theorem B12450833 : Blo 1638018 12450833 := bstep (se 2 (by rfl) ⟨4669062, by rfl⟩ : syracuseStep 12450833 = 9338125) B9338125
theorem B5528627 : Blo 1638018 5528627 := bstep (se 1 (by rfl) ⟨4146470, by rfl⟩ : syracuseStep 5528627 = 8292941) B8292941
theorem B6225113 : Blo 1638018 6225113 := bstep (se 2 (by rfl) ⟨2334417, by rfl⟩ : syracuseStep 6225113 = 4668835) B4668835
theorem B3685643 : Blo 1638018 3685643 := bstep (se 1 (by rfl) ⟨2764232, by rfl⟩ : syracuseStep 3685643 = 5528465) B5528465
theorem B3685697 : Blo 1638018 3685697 := bstep (se 2 (by rfl) ⟨1382136, by rfl⟩ : syracuseStep 3685697 = 2764273) B2764273
theorem B5528897 : Blo 1638018 5528897 := bstep (se 2 (by rfl) ⟨2073336, by rfl⟩ : syracuseStep 5528897 = 4146673) B4146673
theorem B8412491 : Blo 1638018 8412491 := bstep (se 1 (by rfl) ⟨6309368, by rfl⟩ : syracuseStep 8412491 = 12618737) B12618737
theorem B12443057 : Blo 1638018 12443057 := bstep (se 2 (by rfl) ⟨4666146, by rfl⟩ : syracuseStep 12443057 = 9332293) B9332293
theorem B2457035 : Blo 1638018 2457035 := bstep (se 1 (by rfl) ⟨1842776, by rfl⟩ : syracuseStep 2457035 = 3685553) B3685553
theorem B2457047 : Blo 1638018 2457047 := bstep (se 1 (by rfl) ⟨1842785, by rfl⟩ : syracuseStep 2457047 = 3685571) B3685571
theorem B3112435 : Blo 1638018 3112435 := bstep (se 1 (by rfl) ⟨2334326, by rfl⟩ : syracuseStep 3112435 = 4668653) B4668653
theorem B2457113 : Blo 1638018 2457113 := bstep (se 2 (by rfl) ⟨921417, by rfl⟩ : syracuseStep 2457113 = 1842835) B1842835
theorem B3685913 : Blo 1638018 3685913 := bstep (se 2 (by rfl) ⟨1382217, by rfl⟩ : syracuseStep 3685913 = 2764435) B2764435
theorem B17956387 : Blo 1638018 17956387 := bstep (se 1 (by rfl) ⟨13467290, by rfl⟩ : syracuseStep 17956387 = 26934581) B26934581
theorem B3686003 : Blo 1638018 3686003 := bstep (se 1 (by rfl) ⟨2764502, by rfl⟩ : syracuseStep 3686003 = 5529005) B5529005
theorem B1638027 : Blo 1638018 1638027 := bstep (se 1 (by rfl) ⟨1228520, by rfl⟩ : syracuseStep 1638027 = 2457041) B2457041
theorem B2457227 : Blo 1638018 2457227 := bstep (se 1 (by rfl) ⟨1842920, by rfl⟩ : syracuseStep 2457227 = 3685841) B3685841
theorem B1638039 : Blo 1638018 1638039 := bstep (se 1 (by rfl) ⟨1228529, by rfl⟩ : syracuseStep 1638039 = 2457059) B2457059
theorem B2457239 : Blo 1638018 2457239 := bstep (se 1 (by rfl) ⟨1842929, by rfl⟩ : syracuseStep 2457239 = 3685859) B3685859
theorem B3686039 : Blo 1638018 3686039 := bstep (se 1 (by rfl) ⟨2764529, by rfl⟩ : syracuseStep 3686039 = 5529059) B5529059
theorem B2334361 : Blo 1638018 2334361 := bstep (se 2 (by rfl) ⟨875385, by rfl⟩ : syracuseStep 2334361 = 1750771) B1750771
theorem B1638059 : Blo 1638018 1638059 := bstep (se 1 (by rfl) ⟨1228544, by rfl⟩ : syracuseStep 1638059 = 2457089) B2457089
theorem B1638071 : Blo 1638018 1638071 := bstep (se 1 (by rfl) ⟨1228553, by rfl⟩ : syracuseStep 1638071 = 2457107) B2457107
theorem B1842871 : Blo 1638018 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B1638091 : Blo 1638018 1638091 := bstep (se 1 (by rfl) ⟨1228568, by rfl⟩ : syracuseStep 1638091 = 2457137) B2457137
theorem B1638103 : Blo 1638018 1638103 := bstep (se 1 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 1638103 = 2457155) B2457155
theorem B3112663 : Blo 1638018 3112663 := bstep (se 1 (by rfl) ⟨2334497, by rfl⟩ : syracuseStep 3112663 = 4668995) B4668995
theorem B2457305 : Blo 1638018 2457305 := bstep (se 2 (by rfl) ⟨921489, by rfl⟩ : syracuseStep 2457305 = 1842979) B1842979
theorem B1638123 : Blo 1638018 1638123 := bstep (se 1 (by rfl) ⟨1228592, by rfl⟩ : syracuseStep 1638123 = 2457185) B2457185
theorem B1638135 : Blo 1638018 1638135 := bstep (se 1 (by rfl) ⟨1228601, by rfl⟩ : syracuseStep 1638135 = 2457203) B2457203
theorem B13999877 : Blo 1638018 13999877 := bstep (se 4 (by rfl) ⟨1312488, by rfl⟩ : syracuseStep 13999877 = 2624977) B2624977
theorem B1638155 : Blo 1638018 1638155 := bstep (se 1 (by rfl) ⟨1228616, by rfl⟩ : syracuseStep 1638155 = 2457233) B2457233
theorem B1638167 : Blo 1638018 1638167 := bstep (se 1 (by rfl) ⟨1228625, by rfl⟩ : syracuseStep 1638167 = 2457251) B2457251
theorem B1638187 : Blo 1638018 1638187 := bstep (se 1 (by rfl) ⟨1228640, by rfl⟩ : syracuseStep 1638187 = 2457281) B2457281
theorem B4669235 : Blo 1638018 4669235 := bstep (se 1 (by rfl) ⟨3501926, by rfl⟩ : syracuseStep 4669235 = 7003853) B7003853
theorem B1638199 : Blo 1638018 1638199 := bstep (se 1 (by rfl) ⟨1228649, by rfl⟩ : syracuseStep 1638199 = 2457299) B2457299
theorem B3112769 : Blo 1638018 3112769 := bstep (se 2 (by rfl) ⟨1167288, by rfl⟩ : syracuseStep 3112769 = 2334577) B2334577
theorem B1638219 : Blo 1638018 1638219 := bstep (se 1 (by rfl) ⟨1228664, by rfl⟩ : syracuseStep 1638219 = 2457329) B2457329
theorem B2457419 : Blo 1638018 2457419 := bstep (se 1 (by rfl) ⟨1843064, by rfl⟩ : syracuseStep 2457419 = 3686129) B3686129
theorem B3686219 : Blo 1638018 3686219 := bstep (se 1 (by rfl) ⟨2764664, by rfl⟩ : syracuseStep 3686219 = 5529329) B5529329
theorem B1638231 : Blo 1638018 1638231 := bstep (se 1 (by rfl) ⟨1228673, by rfl⟩ : syracuseStep 1638231 = 2457347) B2457347
theorem B2457431 : Blo 1638018 2457431 := bstep (se 1 (by rfl) ⟨1843073, by rfl⟩ : syracuseStep 2457431 = 3686147) B3686147
theorem B5529437 : Blo 1638018 5529437 := bstep (se 3 (by rfl) ⟨1036769, by rfl⟩ : syracuseStep 5529437 = 2073539) B2073539
theorem B1638251 : Blo 1638018 1638251 := bstep (se 1 (by rfl) ⟨1228688, by rfl⟩ : syracuseStep 1638251 = 2457377) B2457377
theorem B1843051 : Blo 1638018 1843051 := bstep (se 1 (by rfl) ⟨1382288, by rfl⟩ : syracuseStep 1843051 = 2764577) B2764577
theorem B1638263 : Blo 1638018 1638263 := bstep (se 1 (by rfl) ⟨1228697, by rfl⟩ : syracuseStep 1638263 = 2457395) B2457395
theorem B3686273 : Blo 1638018 3686273 := bstep (se 2 (by rfl) ⟨1382352, by rfl⟩ : syracuseStep 3686273 = 2764705) B2764705
theorem B1638283 : Blo 1638018 1638283 := bstep (se 1 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 1638283 = 2457425) B2457425
theorem B1638295 : Blo 1638018 1638295 := bstep (se 1 (by rfl) ⟨1228721, by rfl⟩ : syracuseStep 1638295 = 2457443) B2457443
theorem B12443543 : Blo 1638018 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B2457497 : Blo 1638018 2457497 := bstep (se 2 (by rfl) ⟨921561, by rfl⟩ : syracuseStep 2457497 = 1843123) B1843123
theorem B1638315 : Blo 1638018 1638315 := bstep (se 1 (by rfl) ⟨1228736, by rfl⟩ : syracuseStep 1638315 = 2457473) B2457473
theorem B1638327 : Blo 1638018 1638327 := bstep (se 1 (by rfl) ⟨1228745, by rfl⟩ : syracuseStep 1638327 = 2457491) B2457491
theorem B1638347 : Blo 1638018 1638347 := bstep (se 1 (by rfl) ⟨1228760, by rfl⟩ : syracuseStep 1638347 = 2457521) B2457521
theorem B1638359 : Blo 1638018 1638359 := bstep (se 1 (by rfl) ⟨1228769, by rfl⟩ : syracuseStep 1638359 = 2457539) B2457539
theorem B1843159 : Blo 1638018 1843159 := bstep (se 1 (by rfl) ⟨1382369, by rfl⟩ : syracuseStep 1843159 = 2764739) B2764739
theorem B3112921 : Blo 1638018 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B1638379 : Blo 1638018 1638379 := bstep (se 1 (by rfl) ⟨1228784, by rfl⟩ : syracuseStep 1638379 = 2457569) B2457569
theorem B1638391 : Blo 1638018 1638391 := bstep (se 1 (by rfl) ⟨1228793, by rfl⟩ : syracuseStep 1638391 = 2457587) B2457587
theorem B1638407 : Blo 1638018 1638407 := bstep (se 1 (by rfl) ⟨1228805, by rfl⟩ : syracuseStep 1638407 = 2457611) B2457611
theorem B4669451 : Blo 1638018 4669451 := bstep (se 1 (by rfl) ⟨3502088, by rfl⟩ : syracuseStep 4669451 = 7004177) B7004177
theorem B1638415 : Blo 1638018 1638415 := bstep (se 1 (by rfl) ⟨1228811, by rfl⟩ : syracuseStep 1638415 = 2457623) B2457623
theorem B2457659 : Blo 1638018 2457659 := bstep (se 1 (by rfl) ⟨1843244, by rfl⟩ : syracuseStep 2457659 = 3686489) B3686489
theorem B1638459 : Blo 1638018 1638459 := bstep (se 1 (by rfl) ⟨1228844, by rfl⟩ : syracuseStep 1638459 = 2457689) B2457689
theorem B2457719 : Blo 1638018 2457719 := bstep (se 1 (by rfl) ⟨1843289, by rfl⟩ : syracuseStep 2457719 = 3686579) B3686579
theorem B1638535 : Blo 1638018 1638535 := bstep (se 1 (by rfl) ⟨1228901, by rfl⟩ : syracuseStep 1638535 = 2457803) B2457803
theorem B2457743 : Blo 1638018 2457743 := bstep (se 1 (by rfl) ⟨1843307, by rfl⟩ : syracuseStep 2457743 = 3686615) B3686615
theorem B1638543 : Blo 1638018 1638543 := bstep (se 1 (by rfl) ⟨1228907, by rfl⟩ : syracuseStep 1638543 = 2457815) B2457815
theorem B2457785 : Blo 1638018 2457785 := bstep (se 2 (by rfl) ⟨921669, by rfl⟩ : syracuseStep 2457785 = 1843339) B1843339
theorem B1638587 : Blo 1638018 1638587 := bstep (se 1 (by rfl) ⟨1228940, by rfl⟩ : syracuseStep 1638587 = 2457881) B2457881
theorem B2457863 : Blo 1638018 2457863 := bstep (se 1 (by rfl) ⟨1843397, by rfl⟩ : syracuseStep 2457863 = 3686795) B3686795
theorem B1638663 : Blo 1638018 1638663 := bstep (se 1 (by rfl) ⟨1228997, by rfl⟩ : syracuseStep 1638663 = 2457995) B2457995
theorem B1638671 : Blo 1638018 1638671 := bstep (se 1 (by rfl) ⟨1229003, by rfl⟩ : syracuseStep 1638671 = 2458007) B2458007
theorem B2457899 : Blo 1638018 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B17711419 : Blo 1638018 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B1638715 : Blo 1638018 1638715 := bstep (se 1 (by rfl) ⟨1229036, by rfl⟩ : syracuseStep 1638715 = 2458073) B2458073
theorem B2457929 : Blo 1638018 2457929 := bstep (se 2 (by rfl) ⟨921723, by rfl⟩ : syracuseStep 2457929 = 1843447) B1843447
theorem B1843591 : Blo 1638018 1843591 := bstep (se 1 (by rfl) ⟨1382693, by rfl⟩ : syracuseStep 1843591 = 2765387) B2765387
theorem B1638791 : Blo 1638018 1638791 := bstep (se 1 (by rfl) ⟨1229093, by rfl⟩ : syracuseStep 1638791 = 2458187) B2458187
theorem B7004551 : Blo 1638018 7004551 := bstep (se 1 (by rfl) ⟨5253413, by rfl⟩ : syracuseStep 7004551 = 10506827) B10506827
theorem B1638799 : Blo 1638018 1638799 := bstep (se 1 (by rfl) ⟨1229099, by rfl⟩ : syracuseStep 1638799 = 2458199) B2458199
theorem B2458043 : Blo 1638018 2458043 := bstep (se 1 (by rfl) ⟨1843532, by rfl⟩ : syracuseStep 2458043 = 3687065) B3687065
theorem B1638843 : Blo 1638018 1638843 := bstep (se 1 (by rfl) ⟨1229132, by rfl⟩ : syracuseStep 1638843 = 2458265) B2458265
theorem B2458103 : Blo 1638018 2458103 := bstep (se 1 (by rfl) ⟨1843577, by rfl⟩ : syracuseStep 2458103 = 3687155) B3687155
theorem B1638919 : Blo 1638018 1638919 := bstep (se 1 (by rfl) ⟨1229189, by rfl⟩ : syracuseStep 1638919 = 2458379) B2458379
theorem B2458127 : Blo 1638018 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B1638927 : Blo 1638018 1638927 := bstep (se 1 (by rfl) ⟨1229195, by rfl⟩ : syracuseStep 1638927 = 2458391) B2458391
theorem B2458169 : Blo 1638018 2458169 := bstep (se 2 (by rfl) ⟨921813, by rfl⟩ : syracuseStep 2458169 = 1843627) B1843627
theorem B1843771 : Blo 1638018 1843771 := bstep (se 1 (by rfl) ⟨1382828, by rfl⟩ : syracuseStep 1843771 = 2765657) B2765657
theorem B1638971 : Blo 1638018 1638971 := bstep (se 1 (by rfl) ⟨1229228, by rfl⟩ : syracuseStep 1638971 = 2458457) B2458457
theorem B3687047 : Blo 1638018 3687047 := bstep (se 1 (by rfl) ⟨2765285, by rfl⟩ : syracuseStep 3687047 = 5530571) B5530571
theorem B2458247 : Blo 1638018 2458247 := bstep (se 1 (by rfl) ⟨1843685, by rfl⟩ : syracuseStep 2458247 = 3687371) B3687371
theorem B1639047 : Blo 1638018 1639047 := bstep (se 1 (by rfl) ⟨1229285, by rfl⟩ : syracuseStep 1639047 = 2458571) B2458571
theorem B1868431 : Blo 1638018 1868431 := bstep (se 1 (by rfl) ⟨1401323, by rfl⟩ : syracuseStep 1868431 = 2802647) B2802647
theorem B1639055 : Blo 1638018 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B2458283 : Blo 1638018 2458283 := bstep (se 1 (by rfl) ⟨1843712, by rfl⟩ : syracuseStep 2458283 = 3687425) B3687425
theorem B1639099 : Blo 1638018 1639099 := bstep (se 1 (by rfl) ⟨1229324, by rfl⟩ : syracuseStep 1639099 = 2458649) B2458649
theorem B2458313 : Blo 1638018 2458313 := bstep (se 2 (by rfl) ⟨921867, by rfl⟩ : syracuseStep 2458313 = 1843735) B1843735
theorem B15958745 : Blo 1638018 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B1639175 : Blo 1638018 1639175 := bstep (se 1 (by rfl) ⟨1229381, by rfl⟩ : syracuseStep 1639175 = 2458763) B2458763
theorem B1639183 : Blo 1638018 1639183 := bstep (se 1 (by rfl) ⟨1229387, by rfl⟩ : syracuseStep 1639183 = 2458775) B2458775
theorem B7471931 : Blo 1638018 7471931 := bstep (se 1 (by rfl) ⟨5603948, by rfl⟩ : syracuseStep 7471931 = 11207897) B11207897
theorem B3687227 : Blo 1638018 3687227 := bstep (se 1 (by rfl) ⟨2765420, by rfl⟩ : syracuseStep 3687227 = 5530841) B5530841
theorem B2458427 : Blo 1638018 2458427 := bstep (se 1 (by rfl) ⟨1843820, by rfl⟩ : syracuseStep 2458427 = 3687641) B3687641
theorem B1639227 : Blo 1638018 1639227 := bstep (se 1 (by rfl) ⟨1229420, by rfl⟩ : syracuseStep 1639227 = 2458841) B2458841
theorem B2458487 : Blo 1638018 2458487 := bstep (se 1 (by rfl) ⟨1843865, by rfl⟩ : syracuseStep 2458487 = 3687731) B3687731
theorem B1639303 : Blo 1638018 1639303 := bstep (se 1 (by rfl) ⟨1229477, by rfl⟩ : syracuseStep 1639303 = 2458955) B2458955
theorem B2458511 : Blo 1638018 2458511 := bstep (se 1 (by rfl) ⟨1843883, by rfl⟩ : syracuseStep 2458511 = 3687767) B3687767
theorem B1639311 : Blo 1638018 1639311 := bstep (se 1 (by rfl) ⟨1229483, by rfl⟩ : syracuseStep 1639311 = 2458967) B2458967
theorem B3548051 : Blo 1638018 3548051 := bstep (se 1 (by rfl) ⟨2661038, by rfl⟩ : syracuseStep 3548051 = 5322077) B5322077
theorem B7873433 : Blo 1638018 7873433 := bstep (se 2 (by rfl) ⟨2952537, by rfl⟩ : syracuseStep 7873433 = 5905075) B5905075
theorem B3687353 : Blo 1638018 3687353 := bstep (se 2 (by rfl) ⟨1382757, by rfl⟩ : syracuseStep 3687353 = 2765515) B2765515
theorem B2458553 : Blo 1638018 2458553 := bstep (se 2 (by rfl) ⟨921957, by rfl⟩ : syracuseStep 2458553 = 1843915) B1843915
theorem B1639355 : Blo 1638018 1639355 := bstep (se 1 (by rfl) ⟨1229516, by rfl⟩ : syracuseStep 1639355 = 2459033) B2459033
theorem B9339857 : Blo 1638018 9339857 := bstep (se 2 (by rfl) ⟨3502446, by rfl⟩ : syracuseStep 9339857 = 7004893) B7004893
theorem B2458631 : Blo 1638018 2458631 := bstep (se 1 (by rfl) ⟨1843973, by rfl⟩ : syracuseStep 2458631 = 3687947) B3687947
theorem B1639431 : Blo 1638018 1639431 := bstep (se 1 (by rfl) ⟨1229573, by rfl⟩ : syracuseStep 1639431 = 2459147) B2459147
theorem B1844239 : Blo 1638018 1844239 := bstep (se 1 (by rfl) ⟨1383179, by rfl⟩ : syracuseStep 1844239 = 2766359) B2766359
theorem B1639439 : Blo 1638018 1639439 := bstep (se 1 (by rfl) ⟨1229579, by rfl⟩ : syracuseStep 1639439 = 2459159) B2459159
theorem B2458667 : Blo 1638018 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B3154987 : Blo 1638018 3154987 := bstep (se 1 (by rfl) ⟨2366240, by rfl⟩ : syracuseStep 3154987 = 4732481) B4732481
theorem B1639483 : Blo 1638018 1639483 := bstep (se 1 (by rfl) ⟨1229612, by rfl⟩ : syracuseStep 1639483 = 2459225) B2459225
theorem B2458697 : Blo 1638018 2458697 := bstep (se 2 (by rfl) ⟨922011, by rfl⟩ : syracuseStep 2458697 = 1844023) B1844023
theorem B4490327 : Blo 1638018 4490327 := bstep (se 1 (by rfl) ⟨3367745, by rfl⟩ : syracuseStep 4490327 = 6735491) B6735491
theorem B134628439 : Blo 1638018 134628439 := bstep (se 1 (by rfl) ⟨100971329, by rfl⟩ : syracuseStep 134628439 = 201942659) B201942659
theorem B1639559 : Blo 1638018 1639559 := bstep (se 1 (by rfl) ⟨1229669, by rfl⟩ : syracuseStep 1639559 = 2459339) B2459339
theorem B1639567 : Blo 1638018 1639567 := bstep (se 1 (by rfl) ⟨1229675, by rfl⟩ : syracuseStep 1639567 = 2459351) B2459351
theorem B4146329 : Blo 1638018 4146329 := bstep (se 2 (by rfl) ⟨1554873, by rfl⟩ : syracuseStep 4146329 = 3109747) B3109747
theorem B10503341 : Blo 1638018 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B3499193 : Blo 1638018 3499193 := bstep (se 2 (by rfl) ⟨1312197, by rfl⟩ : syracuseStep 3499193 = 2624395) B2624395
theorem B2458811 : Blo 1638018 2458811 := bstep (se 1 (by rfl) ⟨1844108, by rfl⟩ : syracuseStep 2458811 = 3688217) B3688217
theorem B1639611 : Blo 1638018 1639611 := bstep (se 1 (by rfl) ⟨1229708, by rfl⟩ : syracuseStep 1639611 = 2459417) B2459417
theorem B2458871 : Blo 1638018 2458871 := bstep (se 1 (by rfl) ⟨1844153, by rfl⟩ : syracuseStep 2458871 = 3688307) B3688307
theorem B2073863 : Blo 1638018 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B1639687 : Blo 1638018 1639687 := bstep (se 1 (by rfl) ⟨1229765, by rfl⟩ : syracuseStep 1639687 = 2459531) B2459531
theorem B5530895 : Blo 1638018 5530895 := bstep (se 1 (by rfl) ⟨4148171, by rfl⟩ : syracuseStep 5530895 = 8296343) B8296343
theorem B3687695 : Blo 1638018 3687695 := bstep (se 1 (by rfl) ⟨2765771, by rfl⟩ : syracuseStep 3687695 = 5531543) B5531543
theorem B2458895 : Blo 1638018 2458895 := bstep (se 1 (by rfl) ⟨1844171, by rfl⟩ : syracuseStep 2458895 = 3688343) B3688343
theorem B1639695 : Blo 1638018 1639695 := bstep (se 1 (by rfl) ⟨1229771, by rfl⟩ : syracuseStep 1639695 = 2459543) B2459543
theorem B6645025 : Blo 1638018 6645025 := bstep (se 2 (by rfl) ⟨2491884, by rfl⟩ : syracuseStep 6645025 = 4983769) B4983769
theorem B3687713 : Blo 1638018 3687713 := bstep (se 2 (by rfl) ⟨1382892, by rfl⟩ : syracuseStep 3687713 = 2765785) B2765785
theorem B2458937 : Blo 1638018 2458937 := bstep (se 2 (by rfl) ⟨922101, by rfl⟩ : syracuseStep 2458937 = 1844203) B1844203
theorem B4146491 : Blo 1638018 4146491 := bstep (se 1 (by rfl) ⟨3109868, by rfl⟩ : syracuseStep 4146491 = 6219737) B6219737
theorem B1639739 : Blo 1638018 1639739 := bstep (se 1 (by rfl) ⟨1229804, by rfl⟩ : syracuseStep 1639739 = 2459609) B2459609
theorem B2459015 : Blo 1638018 2459015 := bstep (se 1 (by rfl) ⟨1844261, by rfl⟩ : syracuseStep 2459015 = 3688523) B3688523
theorem B1639815 : Blo 1638018 1639815 := bstep (se 1 (by rfl) ⟨1229861, by rfl⟩ : syracuseStep 1639815 = 2459723) B2459723
theorem B1639823 : Blo 1638018 1639823 := bstep (se 1 (by rfl) ⟨1229867, by rfl⟩ : syracuseStep 1639823 = 2459735) B2459735
theorem B2459051 : Blo 1638018 2459051 := bstep (se 1 (by rfl) ⟨1844288, by rfl⟩ : syracuseStep 2459051 = 3688577) B3688577
theorem B1639867 : Blo 1638018 1639867 := bstep (se 1 (by rfl) ⟨1229900, by rfl⟩ : syracuseStep 1639867 = 2459801) B2459801
theorem B2459081 : Blo 1638018 2459081 := bstep (se 2 (by rfl) ⟨922155, by rfl⟩ : syracuseStep 2459081 = 1844311) B1844311
theorem B1844743 : Blo 1638018 1844743 := bstep (se 1 (by rfl) ⟨1383557, by rfl⟩ : syracuseStep 1844743 = 2767115) B2767115
theorem B1639943 : Blo 1638018 1639943 := bstep (se 1 (by rfl) ⟨1229957, by rfl⟩ : syracuseStep 1639943 = 2459915) B2459915
theorem B1639951 : Blo 1638018 1639951 := bstep (se 1 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 1639951 = 2459927) B2459927
theorem B5531165 : Blo 1638018 5531165 := bstep (se 3 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 5531165 = 2074187) B2074187
theorem B18671147 : Blo 1638018 18671147 := bstep (se 1 (by rfl) ⟨14003360, by rfl⟩ : syracuseStep 18671147 = 28006721) B28006721
theorem B2459195 : Blo 1638018 2459195 := bstep (se 1 (by rfl) ⟨1844396, by rfl⟩ : syracuseStep 2459195 = 3688793) B3688793
theorem B1639995 : Blo 1638018 1639995 := bstep (se 1 (by rfl) ⟨1229996, by rfl⟩ : syracuseStep 1639995 = 2459993) B2459993
theorem B3688055 : Blo 1638018 3688055 := bstep (se 1 (by rfl) ⟨2766041, by rfl⟩ : syracuseStep 3688055 = 5532083) B5532083
theorem B2459255 : Blo 1638018 2459255 := bstep (se 1 (by rfl) ⟨1844441, by rfl⟩ : syracuseStep 2459255 = 3688883) B3688883
theorem B2459279 : Blo 1638018 2459279 := bstep (se 1 (by rfl) ⟨1844459, by rfl⟩ : syracuseStep 2459279 = 3688919) B3688919
theorem B4146835 : Blo 1638018 4146835 := bstep (se 1 (by rfl) ⟨3110126, by rfl⟩ : syracuseStep 4146835 = 6220253) B6220253
theorem B2459321 : Blo 1638018 2459321 := bstep (se 2 (by rfl) ⟨922245, by rfl⟩ : syracuseStep 2459321 = 1844491) B1844491
theorem B1844923 : Blo 1638018 1844923 := bstep (se 1 (by rfl) ⟨1383692, by rfl⟩ : syracuseStep 1844923 = 2767385) B2767385
theorem B2459399 : Blo 1638018 2459399 := bstep (se 1 (by rfl) ⟨1844549, by rfl⟩ : syracuseStep 2459399 = 3689099) B3689099
theorem B4982543 : Blo 1638018 4982543 := bstep (se 1 (by rfl) ⟨3736907, by rfl⟩ : syracuseStep 4982543 = 7473815) B7473815
theorem B4146977 : Blo 1638018 4146977 := bstep (se 2 (by rfl) ⟨1555116, by rfl⟩ : syracuseStep 4146977 = 3110233) B3110233
theorem B3688235 : Blo 1638018 3688235 := bstep (se 1 (by rfl) ⟨2766176, by rfl⟩ : syracuseStep 3688235 = 5532353) B5532353
theorem B2459435 : Blo 1638018 2459435 := bstep (se 1 (by rfl) ⟨1844576, by rfl⟩ : syracuseStep 2459435 = 3689153) B3689153
theorem B2459465 : Blo 1638018 2459465 := bstep (se 2 (by rfl) ⟨922299, by rfl⟩ : syracuseStep 2459465 = 1844599) B1844599
theorem B127739749 : Blo 1638018 127739749 := bstep (se 4 (by rfl) ⟨11975601, by rfl⟩ : syracuseStep 127739749 = 23951203) B23951203
theorem B2074511 : Blo 1638018 2074511 := bstep (se 1 (by rfl) ⟨1555883, by rfl⟩ : syracuseStep 2074511 = 3111767) B3111767
theorem B2459579 : Blo 1638018 2459579 := bstep (se 1 (by rfl) ⟨1844684, by rfl⟩ : syracuseStep 2459579 = 3689369) B3689369
theorem B2459639 : Blo 1638018 2459639 := bstep (se 1 (by rfl) ⟨1844729, by rfl⟩ : syracuseStep 2459639 = 3689459) B3689459
theorem B8300555 : Blo 1638018 8300555 := bstep (se 1 (by rfl) ⟨6225416, by rfl⟩ : syracuseStep 8300555 = 12450833) B12450833
theorem B2459663 : Blo 1638018 2459663 := bstep (se 1 (by rfl) ⟨1844747, by rfl⟩ : syracuseStep 2459663 = 3689495) B3689495
theorem B2459705 : Blo 1638018 2459705 := bstep (se 2 (by rfl) ⟨922389, by rfl⟩ : syracuseStep 2459705 = 1844779) B1844779
theorem B18679895 : Blo 1638018 18679895 := bstep (se 1 (by rfl) ⟨14009921, by rfl⟩ : syracuseStep 18679895 = 28019843) B28019843
theorem B2459783 : Blo 1638018 2459783 := bstep (se 1 (by rfl) ⟨1844837, by rfl⟩ : syracuseStep 2459783 = 3689675) B3689675
theorem B3688595 : Blo 1638018 3688595 := bstep (se 1 (by rfl) ⟨2766446, by rfl⟩ : syracuseStep 3688595 = 5532893) B5532893
theorem B2459819 : Blo 1638018 2459819 := bstep (se 1 (by rfl) ⟨1844864, by rfl⟩ : syracuseStep 2459819 = 3689729) B3689729
theorem B8300717 : Blo 1638018 8300717 := bstep (se 3 (by rfl) ⟨1556384, by rfl⟩ : syracuseStep 8300717 = 3112769) B3112769
theorem B3688649 : Blo 1638018 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B2459849 : Blo 1638018 2459849 := bstep (se 2 (by rfl) ⟨922443, by rfl⟩ : syracuseStep 2459849 = 1844887) B1844887
theorem B2492687 : Blo 1638018 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B3197227 : Blo 1638018 3197227 := bstep (se 1 (by rfl) ⟨2397920, by rfl⟩ : syracuseStep 3197227 = 4795841) B4795841
theorem B2459963 : Blo 1638018 2459963 := bstep (se 1 (by rfl) ⟨1844972, by rfl⟩ : syracuseStep 2459963 = 3689945) B3689945
theorem B2460023 : Blo 1638018 2460023 := bstep (se 1 (by rfl) ⟨1845017, by rfl⟩ : syracuseStep 2460023 = 3690035) B3690035
theorem B17729927 : Blo 1638018 17729927 := bstep (se 1 (by rfl) ⟨13297445, by rfl⟩ : syracuseStep 17729927 = 26594891) B26594891
theorem B9333251 : Blo 1638018 9333251 := bstep (se 1 (by rfl) ⟨6999938, by rfl⟩ : syracuseStep 9333251 = 13999877) B13999877
theorem B6310601 : Blo 1638018 6310601 := bstep (se 2 (by rfl) ⟨2366475, by rfl⟩ : syracuseStep 6310601 = 4732951) B4732951
theorem B1968887 : Blo 1638018 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B2493175 : Blo 1638018 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B4147969 : Blo 1638018 4147969 := bstep (se 2 (by rfl) ⟨1555488, by rfl⟩ : syracuseStep 4147969 = 3110977) B3110977
theorem B3500833 : Blo 1638018 3500833 := bstep (se 2 (by rfl) ⟨1312812, by rfl⟩ : syracuseStep 3500833 = 2625625) B2625625
theorem B2624375 : Blo 1638018 2624375 := bstep (se 1 (by rfl) ⟨1968281, by rfl⟩ : syracuseStep 2624375 = 3936563) B3936563
theorem B3689351 : Blo 1638018 3689351 := bstep (se 1 (by rfl) ⟨2767013, by rfl⟩ : syracuseStep 3689351 = 5534027) B5534027
theorem B8293265 : Blo 1638018 8293265 := bstep (se 2 (by rfl) ⟨3109974, by rfl⟩ : syracuseStep 8293265 = 6219949) B6219949
theorem B5532569 : Blo 1638018 5532569 := bstep (se 2 (by rfl) ⟨2074713, by rfl⟩ : syracuseStep 5532569 = 4149427) B4149427
theorem B2493431 : Blo 1638018 2493431 := bstep (se 1 (by rfl) ⟨1870073, by rfl⟩ : syracuseStep 2493431 = 3740147) B3740147
theorem B3689531 : Blo 1638018 3689531 := bstep (se 1 (by rfl) ⟨2767148, by rfl⟩ : syracuseStep 3689531 = 5534297) B5534297
theorem B3689657 : Blo 1638018 3689657 := bstep (se 2 (by rfl) ⟨1383621, by rfl⟩ : syracuseStep 3689657 = 2767243) B2767243
theorem B9465025 : Blo 1638018 9465025 := bstep (se 2 (by rfl) ⟨3549384, by rfl⟩ : syracuseStep 9465025 = 7098769) B7098769
theorem B4664587 : Blo 1638018 4664587 := bstep (se 1 (by rfl) ⟨3498440, by rfl⟩ : syracuseStep 4664587 = 6996881) B6996881
theorem B4148567 : Blo 1638018 4148567 := bstep (se 1 (by rfl) ⟨3111425, by rfl⟩ : syracuseStep 4148567 = 6222851) B6222851
theorem B14003603 : Blo 1638018 14003603 := bstep (se 1 (by rfl) ⟨10502702, by rfl⟩ : syracuseStep 14003603 = 21005405) B21005405
theorem B3689999 : Blo 1638018 3689999 := bstep (se 1 (by rfl) ⟨2767499, by rfl⟩ : syracuseStep 3689999 = 5534999) B5534999
theorem B4664861 : Blo 1638018 4664861 := bstep (se 3 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 4664861 = 1749323) B1749323
theorem B33648157 : Blo 1638018 33648157 := bstep (se 3 (by rfl) ⟨6309029, by rfl⟩ : syracuseStep 33648157 = 12618059) B12618059
theorem B3690017 : Blo 1638018 3690017 := bstep (se 2 (by rfl) ⟨1383756, by rfl⟩ : syracuseStep 3690017 = 2767513) B2767513
theorem B4148779 : Blo 1638018 4148779 := bstep (se 1 (by rfl) ⟨3111584, by rfl⟩ : syracuseStep 4148779 = 6223169) B6223169
theorem B5533271 : Blo 1638018 5533271 := bstep (se 1 (by rfl) ⟨4149953, by rfl⟩ : syracuseStep 5533271 = 8299907) B8299907
theorem B23621219 : Blo 1638018 23621219 := bstep (se 1 (by rfl) ⟨17715914, by rfl⟩ : syracuseStep 23621219 = 35431829) B35431829
theorem B133107313 : Blo 1638018 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B4148921 : Blo 1638018 4148921 := bstep (se 2 (by rfl) ⟨1555845, by rfl⟩ : syracuseStep 4148921 = 3111691) B3111691
theorem B7474889 : Blo 1638018 7474889 := bstep (se 2 (by rfl) ⟨2803083, by rfl⟩ : syracuseStep 7474889 = 5606167) B5606167
theorem B2764489 : Blo 1638018 2764489 := bstep (se 2 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 2764489 = 2073367) B2073367
theorem B16821989 : Blo 1638018 16821989 := bstep (se 4 (by rfl) ⟨1577061, by rfl⟩ : syracuseStep 16821989 = 3154123) B3154123
theorem B8302337 : Blo 1638018 8302337 := bstep (se 2 (by rfl) ⟨3113376, by rfl⟩ : syracuseStep 8302337 = 6226753) B6226753
theorem B1969963 : Blo 1638018 1969963 := bstep (se 1 (by rfl) ⟨1477472, by rfl⟩ : syracuseStep 1969963 = 2954945) B2954945
theorem B3501883 : Blo 1638018 3501883 := bstep (se 1 (by rfl) ⟨2626412, by rfl⟩ : syracuseStep 3501883 = 5252825) B5252825
theorem B3321719 : Blo 1638018 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B5533757 : Blo 1638018 5533757 := bstep (se 3 (by rfl) ⟨1037579, by rfl⟩ : syracuseStep 5533757 = 2075159) B2075159
theorem B6737987 : Blo 1638018 6737987 := bstep (se 1 (by rfl) ⟨5053490, by rfl⟩ : syracuseStep 6737987 = 10106981) B10106981
theorem B37851229 : Blo 1638018 37851229 := bstep (se 3 (by rfl) ⟨7097105, by rfl⟩ : syracuseStep 37851229 = 14194211) B14194211
theorem B12447917 : Blo 1638018 12447917 := bstep (se 3 (by rfl) ⟨2333984, by rfl⟩ : syracuseStep 12447917 = 4667969) B4667969
theorem B3502379 : Blo 1638018 3502379 := bstep (se 1 (by rfl) ⟨2626784, by rfl⟩ : syracuseStep 3502379 = 5253569) B5253569
theorem B2765191 : Blo 1638018 2765191 := bstep (se 1 (by rfl) ⟨2073893, by rfl⟩ : syracuseStep 2765191 = 4147787) B4147787
theorem B6222365 : Blo 1638018 6222365 := bstep (se 3 (by rfl) ⟨1166693, by rfl⟩ : syracuseStep 6222365 = 2333387) B2333387
theorem B6222379 : Blo 1638018 6222379 := bstep (se 1 (by rfl) ⟨4666784, by rfl⟩ : syracuseStep 6222379 = 9333569) B9333569
theorem B16822849 : Blo 1638018 16822849 := bstep (se 2 (by rfl) ⟨6308568, by rfl⟩ : syracuseStep 16822849 = 12617137) B12617137
theorem B12440141 : Blo 1638018 12440141 := bstep (se 3 (by rfl) ⟨2332526, by rfl⟩ : syracuseStep 12440141 = 4665053) B4665053
theorem B10498679 : Blo 1638018 10498679 := bstep (se 1 (by rfl) ⟨7874009, by rfl⟩ : syracuseStep 10498679 = 15748019) B15748019
theorem B4149913 : Blo 1638018 4149913 := bstep (se 2 (by rfl) ⟨1556217, by rfl⟩ : syracuseStep 4149913 = 3112435) B3112435
theorem B63894197 : Blo 1638018 63894197 := bstep (se 5 (by rfl) ⟨2995040, by rfl⟩ : syracuseStep 63894197 = 5990081) B5990081
theorem B23941849 : Blo 1638018 23941849 := bstep (se 2 (by rfl) ⟨8978193, by rfl⟩ : syracuseStep 23941849 = 17956387) B17956387
theorem B1749767 : Blo 1638018 1749767 := bstep (se 1 (by rfl) ⟨1312325, by rfl⟩ : syracuseStep 1749767 = 2624651) B2624651
theorem B4150075 : Blo 1638018 4150075 := bstep (se 1 (by rfl) ⟨3112556, by rfl⟩ : syracuseStep 4150075 = 6225113) B6225113
theorem B5608327 : Blo 1638018 5608327 := bstep (se 1 (by rfl) ⟨4206245, by rfl⟩ : syracuseStep 5608327 = 8412491) B8412491
theorem B3937177 : Blo 1638018 3937177 := bstep (se 2 (by rfl) ⟨1476441, by rfl⟩ : syracuseStep 3937177 = 2952883) B2952883
theorem B5247929 : Blo 1638018 5247929 := bstep (se 2 (by rfl) ⟨1967973, by rfl⟩ : syracuseStep 5247929 = 3935947) B3935947
theorem B4150217 : Blo 1638018 4150217 := bstep (se 2 (by rfl) ⟨1556331, by rfl⟩ : syracuseStep 4150217 = 3112663) B3112663
theorem B8295371 : Blo 1638018 8295371 := bstep (se 1 (by rfl) ⟨6221528, by rfl⟩ : syracuseStep 8295371 = 12443057) B12443057
theorem B2765839 : Blo 1638018 2765839 := bstep (se 1 (by rfl) ⟨2074379, by rfl⟩ : syracuseStep 2765839 = 4148759) B4148759
theorem B3110089 : Blo 1638018 3110089 := bstep (se 2 (by rfl) ⟨1166283, by rfl⟩ : syracuseStep 3110089 = 2332567) B2332567
theorem B179336429 : Blo 1638018 179336429 := bstep (se 3 (by rfl) ⟨33625580, by rfl⟩ : syracuseStep 179336429 = 67251161) B67251161
theorem B8295695 : Blo 1638018 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B15963425 : Blo 1638018 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B4150561 : Blo 1638018 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B2766379 : Blo 1638018 2766379 := bstep (se 1 (by rfl) ⟨2074784, by rfl⟩ : syracuseStep 2766379 = 4149569) B4149569
theorem B10499651 : Blo 1638018 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B4666967 : Blo 1638018 4666967 := bstep (se 1 (by rfl) ⟨3500225, by rfl⟩ : syracuseStep 4666967 = 7000451) B7000451
theorem B2766521 : Blo 1638018 2766521 := bstep (se 2 (by rfl) ⟨1037445, by rfl⟩ : syracuseStep 2766521 = 2074891) B2074891
theorem B4667195 : Blo 1638018 4667195 := bstep (se 1 (by rfl) ⟨3500396, by rfl⟩ : syracuseStep 4667195 = 7000793) B7000793
theorem B4151159 : Blo 1638018 4151159 := bstep (se 1 (by rfl) ⟨3113369, by rfl⟩ : syracuseStep 4151159 = 6226739) B6226739
theorem B5248903 : Blo 1638018 5248903 := bstep (se 1 (by rfl) ⟨3936677, by rfl⟩ : syracuseStep 5248903 = 7873355) B7873355
theorem B8411015 : Blo 1638018 8411015 := bstep (se 1 (by rfl) ⟨6308261, by rfl⟩ : syracuseStep 8411015 = 12616523) B12616523
theorem B4667321 : Blo 1638018 4667321 := bstep (se 2 (by rfl) ⟨1750245, by rfl⟩ : syracuseStep 4667321 = 3500491) B3500491
theorem B13998167 : Blo 1638018 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B2767223 : Blo 1638018 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B10639837 : Blo 1638018 10639837 := bstep (se 3 (by rfl) ⟨1994969, by rfl⟩ : syracuseStep 10639837 = 3989939) B3989939
theorem B3938831 : Blo 1638018 3938831 := bstep (se 1 (by rfl) ⟨2954123, by rfl⟩ : syracuseStep 3938831 = 5908247) B5908247
theorem B9329195 : Blo 1638018 9329195 := bstep (se 1 (by rfl) ⟨6996896, by rfl⟩ : syracuseStep 9329195 = 13993793) B13993793
theorem B12450347 : Blo 1638018 12450347 := bstep (se 1 (by rfl) ⟨9337760, by rfl⟩ : syracuseStep 12450347 = 18675521) B18675521
theorem B8297153 : Blo 1638018 8297153 := bstep (se 2 (by rfl) ⟨3111432, by rfl⟩ : syracuseStep 8297153 = 6222865) B6222865
theorem B5905133 : Blo 1638018 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B43170565 : Blo 1638018 43170565 := bstep (se 4 (by rfl) ⟨4047240, by rfl⟩ : syracuseStep 43170565 = 8094481) B8094481
theorem B7002895 : Blo 1638018 7002895 := bstep (se 1 (by rfl) ⟨5252171, by rfl⟩ : syracuseStep 7002895 = 10504343) B10504343
theorem B42589091 : Blo 1638018 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B12442571 : Blo 1638018 12442571 := bstep (se 1 (by rfl) ⟨9331928, by rfl⟩ : syracuseStep 12442571 = 18663857) B18663857
theorem B11811851 : Blo 1638018 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B3111995 : Blo 1638018 3111995 := bstep (se 1 (by rfl) ⟨2333996, by rfl⟩ : syracuseStep 3111995 = 4667993) B4667993
theorem B6642755 : Blo 1638018 6642755 := bstep (se 1 (by rfl) ⟨4982066, by rfl⟩ : syracuseStep 6642755 = 9964133) B9964133
theorem B9337943 : Blo 1638018 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B2334025 : Blo 1638018 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B3685751 : Blo 1638018 3685751 := bstep (se 1 (by rfl) ⟨2764313, by rfl⟩ : syracuseStep 3685751 = 5528627) B5528627
theorem B5905811 : Blo 1638018 5905811 := bstep (se 1 (by rfl) ⟨4429358, by rfl⟩ : syracuseStep 5905811 = 8858717) B8858717
theorem B6643129 : Blo 1638018 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B2457095 : Blo 1638018 2457095 := bstep (se 1 (by rfl) ⟨1842821, by rfl⟩ : syracuseStep 2457095 = 3685643) B3685643
theorem B3112481 : Blo 1638018 3112481 := bstep (se 2 (by rfl) ⟨1167180, by rfl⟩ : syracuseStep 3112481 = 2334361) B2334361
theorem B4668961 : Blo 1638018 4668961 := bstep (se 2 (by rfl) ⟨1750860, by rfl⟩ : syracuseStep 4668961 = 3501721) B3501721
theorem B2457131 : Blo 1638018 2457131 := bstep (se 1 (by rfl) ⟨1842848, by rfl⟩ : syracuseStep 2457131 = 3685697) B3685697
theorem B3685931 : Blo 1638018 3685931 := bstep (se 1 (by rfl) ⟨2764448, by rfl⟩ : syracuseStep 3685931 = 5528897) B5528897
theorem B2457161 : Blo 1638018 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B18660941 : Blo 1638018 18660941 := bstep (se 3 (by rfl) ⟨3498926, by rfl⟩ : syracuseStep 18660941 = 6997853) B6997853
theorem B1638023 : Blo 1638018 1638023 := bstep (se 1 (by rfl) ⟨1228517, by rfl⟩ : syracuseStep 1638023 = 2457035) B2457035
theorem B1638031 : Blo 1638018 1638031 := bstep (se 1 (by rfl) ⟨1228523, by rfl⟩ : syracuseStep 1638031 = 2457047) B2457047
theorem B1638075 : Blo 1638018 1638075 := bstep (se 1 (by rfl) ⟨1228556, by rfl⟩ : syracuseStep 1638075 = 2457113) B2457113
theorem B2457275 : Blo 1638018 2457275 := bstep (se 1 (by rfl) ⟨1842956, by rfl⟩ : syracuseStep 2457275 = 3685913) B3685913
theorem B5398217 : Blo 1638018 5398217 := bstep (se 2 (by rfl) ⟨2024331, by rfl⟩ : syracuseStep 5398217 = 4048663) B4048663
theorem B7880429 : Blo 1638018 7880429 := bstep (se 3 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 7880429 = 2955161) B2955161
theorem B2457335 : Blo 1638018 2457335 := bstep (se 1 (by rfl) ⟨1843001, by rfl⟩ : syracuseStep 2457335 = 3686003) B3686003
theorem B1638151 : Blo 1638018 1638151 := bstep (se 1 (by rfl) ⟨1228613, by rfl⟩ : syracuseStep 1638151 = 2457227) B2457227
theorem B1638159 : Blo 1638018 1638159 := bstep (se 1 (by rfl) ⟨1228619, by rfl⟩ : syracuseStep 1638159 = 2457239) B2457239
theorem B2457359 : Blo 1638018 2457359 := bstep (se 1 (by rfl) ⟨1843019, by rfl⟩ : syracuseStep 2457359 = 3686039) B3686039
theorem B2457401 : Blo 1638018 2457401 := bstep (se 2 (by rfl) ⟨921525, by rfl⟩ : syracuseStep 2457401 = 1843051) B1843051
theorem B1638203 : Blo 1638018 1638203 := bstep (se 1 (by rfl) ⟨1228652, by rfl⟩ : syracuseStep 1638203 = 2457305) B2457305
theorem B3112823 : Blo 1638018 3112823 := bstep (se 1 (by rfl) ⟨2334617, by rfl⟩ : syracuseStep 3112823 = 4669235) B4669235
theorem B1638279 : Blo 1638018 1638279 := bstep (se 1 (by rfl) ⟨1228709, by rfl⟩ : syracuseStep 1638279 = 2457419) B2457419
theorem B2457479 : Blo 1638018 2457479 := bstep (se 1 (by rfl) ⟨1843109, by rfl⟩ : syracuseStep 2457479 = 3686219) B3686219
theorem B1638287 : Blo 1638018 1638287 := bstep (se 1 (by rfl) ⟨1228715, by rfl⟩ : syracuseStep 1638287 = 2457431) B2457431
theorem B1843087 : Blo 1638018 1843087 := bstep (se 1 (by rfl) ⟨1382315, by rfl⟩ : syracuseStep 1843087 = 2764631) B2764631
theorem B3686291 : Blo 1638018 3686291 := bstep (se 1 (by rfl) ⟨2764718, by rfl⟩ : syracuseStep 3686291 = 5529437) B5529437
theorem B5529491 : Blo 1638018 5529491 := bstep (se 1 (by rfl) ⟨4147118, by rfl⟩ : syracuseStep 5529491 = 8294237) B8294237
theorem B2457515 : Blo 1638018 2457515 := bstep (se 1 (by rfl) ⟨1843136, by rfl⟩ : syracuseStep 2457515 = 3686273) B3686273
theorem B1638331 : Blo 1638018 1638331 := bstep (se 1 (by rfl) ⟨1228748, by rfl⟩ : syracuseStep 1638331 = 2457497) B2457497
theorem B2457545 : Blo 1638018 2457545 := bstep (se 2 (by rfl) ⟨921579, by rfl⟩ : syracuseStep 2457545 = 1843159) B1843159
theorem B3686345 : Blo 1638018 3686345 := bstep (se 2 (by rfl) ⟨1382379, by rfl⟩ : syracuseStep 3686345 = 2764759) B2764759
theorem B8298449 : Blo 1638018 8298449 := bstep (se 2 (by rfl) ⟨3111918, by rfl⟩ : syracuseStep 8298449 = 6223837) B6223837
theorem B9330653 : Blo 1638018 9330653 := bstep (se 3 (by rfl) ⟨1749497, by rfl⟩ : syracuseStep 9330653 = 3498995) B3498995
theorem B3112967 : Blo 1638018 3112967 := bstep (se 1 (by rfl) ⟨2334725, by rfl⟩ : syracuseStep 3112967 = 4669451) B4669451
theorem B1638439 : Blo 1638018 1638439 := bstep (se 1 (by rfl) ⟨1228829, by rfl⟩ : syracuseStep 1638439 = 2457659) B2457659
theorem B1638479 : Blo 1638018 1638479 := bstep (se 1 (by rfl) ⟨1228859, by rfl⟩ : syracuseStep 1638479 = 2457719) B2457719
theorem B1638495 : Blo 1638018 1638495 := bstep (se 1 (by rfl) ⟨1228871, by rfl⟩ : syracuseStep 1638495 = 2457743) B2457743
theorem B8298611 : Blo 1638018 8298611 := bstep (se 1 (by rfl) ⟨6223958, by rfl⟩ : syracuseStep 8298611 = 12447917) B12447917
theorem B1638523 : Blo 1638018 1638523 := bstep (se 1 (by rfl) ⟨1228892, by rfl⟩ : syracuseStep 1638523 = 2457785) B2457785
theorem B1638575 : Blo 1638018 1638575 := bstep (se 1 (by rfl) ⟨1228931, by rfl⟩ : syracuseStep 1638575 = 2457863) B2457863
theorem B1638599 : Blo 1638018 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B2334919 : Blo 1638018 2334919 := bstep (se 1 (by rfl) ⟨1751189, by rfl⟩ : syracuseStep 2334919 = 3502379) B3502379
theorem B1638619 : Blo 1638018 1638619 := bstep (se 1 (by rfl) ⟨1228964, by rfl⟩ : syracuseStep 1638619 = 2457929) B2457929
theorem B1638695 : Blo 1638018 1638695 := bstep (se 1 (by rfl) ⟨1229021, by rfl⟩ : syracuseStep 1638695 = 2458043) B2458043
theorem B1638735 : Blo 1638018 1638735 := bstep (se 1 (by rfl) ⟨1229051, by rfl⟩ : syracuseStep 1638735 = 2458103) B2458103
theorem B1638751 : Blo 1638018 1638751 := bstep (se 1 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 1638751 = 2458127) B2458127
theorem B1638779 : Blo 1638018 1638779 := bstep (se 1 (by rfl) ⟨1229084, by rfl⟩ : syracuseStep 1638779 = 2458169) B2458169
theorem B2458031 : Blo 1638018 2458031 := bstep (se 1 (by rfl) ⟨1843523, by rfl⟩ : syracuseStep 2458031 = 3687047) B3687047
theorem B1638831 : Blo 1638018 1638831 := bstep (se 1 (by rfl) ⟨1229123, by rfl⟩ : syracuseStep 1638831 = 2458247) B2458247
theorem B1638855 : Blo 1638018 1638855 := bstep (se 1 (by rfl) ⟨1229141, by rfl⟩ : syracuseStep 1638855 = 2458283) B2458283
theorem B1638875 : Blo 1638018 1638875 := bstep (se 1 (by rfl) ⟨1229156, by rfl⟩ : syracuseStep 1638875 = 2458313) B2458313
theorem B3686921 : Blo 1638018 3686921 := bstep (se 2 (by rfl) ⟨1382595, by rfl⟩ : syracuseStep 3686921 = 2765191) B2765191
theorem B2458121 : Blo 1638018 2458121 := bstep (se 2 (by rfl) ⟨921795, by rfl⟩ : syracuseStep 2458121 = 1843591) B1843591
theorem B9339401 : Blo 1638018 9339401 := bstep (se 2 (by rfl) ⟨3502275, by rfl⟩ : syracuseStep 9339401 = 7004551) B7004551
theorem B2458151 : Blo 1638018 2458151 := bstep (se 1 (by rfl) ⟨1843613, by rfl⟩ : syracuseStep 2458151 = 3687227) B3687227
theorem B1638951 : Blo 1638018 1638951 := bstep (se 1 (by rfl) ⟨1229213, by rfl⟩ : syracuseStep 1638951 = 2458427) B2458427
theorem B1638991 : Blo 1638018 1638991 := bstep (se 1 (by rfl) ⟨1229243, by rfl⟩ : syracuseStep 1638991 = 2458487) B2458487
theorem B1639007 : Blo 1638018 1639007 := bstep (se 1 (by rfl) ⟨1229255, by rfl⟩ : syracuseStep 1639007 = 2458511) B2458511
theorem B2458235 : Blo 1638018 2458235 := bstep (se 1 (by rfl) ⟨1843676, by rfl⟩ : syracuseStep 2458235 = 3687353) B3687353
theorem B1639035 : Blo 1638018 1639035 := bstep (se 1 (by rfl) ⟨1229276, by rfl⟩ : syracuseStep 1639035 = 2458553) B2458553
theorem B5530247 : Blo 1638018 5530247 := bstep (se 1 (by rfl) ⟨4147685, by rfl⟩ : syracuseStep 5530247 = 8295371) B8295371
theorem B6226571 : Blo 1638018 6226571 := bstep (se 1 (by rfl) ⟨4669928, by rfl⟩ : syracuseStep 6226571 = 9339857) B9339857
theorem B1639087 : Blo 1638018 1639087 := bstep (se 1 (by rfl) ⟨1229315, by rfl⟩ : syracuseStep 1639087 = 2458631) B2458631
theorem B5530301 : Blo 1638018 5530301 := bstep (se 3 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 5530301 = 2073863) B2073863
theorem B1639111 : Blo 1638018 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B1639131 : Blo 1638018 1639131 := bstep (se 1 (by rfl) ⟨1229348, by rfl⟩ : syracuseStep 1639131 = 2458697) B2458697
theorem B2458361 : Blo 1638018 2458361 := bstep (se 2 (by rfl) ⟨921885, by rfl⟩ : syracuseStep 2458361 = 1843771) B1843771
theorem B22430465 : Blo 1638018 22430465 := bstep (se 2 (by rfl) ⟨8411424, by rfl⟩ : syracuseStep 22430465 = 16822849) B16822849
theorem B1639207 : Blo 1638018 1639207 := bstep (se 1 (by rfl) ⟨1229405, by rfl⟩ : syracuseStep 1639207 = 2458811) B2458811
theorem B1639247 : Blo 1638018 1639247 := bstep (se 1 (by rfl) ⟨1229435, by rfl⟩ : syracuseStep 1639247 = 2458871) B2458871
theorem B5530463 : Blo 1638018 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B3687263 : Blo 1638018 3687263 := bstep (se 1 (by rfl) ⟨2765447, by rfl⟩ : syracuseStep 3687263 = 5530895) B5530895
theorem B2458463 : Blo 1638018 2458463 := bstep (se 1 (by rfl) ⟨1843847, by rfl⟩ : syracuseStep 2458463 = 3687695) B3687695
theorem B1639263 : Blo 1638018 1639263 := bstep (se 1 (by rfl) ⟨1229447, by rfl⟩ : syracuseStep 1639263 = 2458895) B2458895
theorem B2491241 : Blo 1638018 2491241 := bstep (se 2 (by rfl) ⟨934215, by rfl⟩ : syracuseStep 2491241 = 1868431) B1868431
theorem B10642283 : Blo 1638018 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B2458475 : Blo 1638018 2458475 := bstep (se 1 (by rfl) ⟨1843856, by rfl⟩ : syracuseStep 2458475 = 3687713) B3687713
theorem B1639291 : Blo 1638018 1639291 := bstep (se 1 (by rfl) ⟨1229468, by rfl⟩ : syracuseStep 1639291 = 2458937) B2458937
theorem B1639343 : Blo 1638018 1639343 := bstep (se 1 (by rfl) ⟨1229507, by rfl⟩ : syracuseStep 1639343 = 2459015) B2459015
theorem B1639367 : Blo 1638018 1639367 := bstep (se 1 (by rfl) ⟨1229525, by rfl⟩ : syracuseStep 1639367 = 2459051) B2459051
theorem B1639387 : Blo 1638018 1639387 := bstep (se 1 (by rfl) ⟨1229540, by rfl⟩ : syracuseStep 1639387 = 2459081) B2459081
theorem B5530625 : Blo 1638018 5530625 := bstep (se 2 (by rfl) ⟨2073984, by rfl⟩ : syracuseStep 5530625 = 4147969) B4147969
theorem B3687443 : Blo 1638018 3687443 := bstep (se 1 (by rfl) ⟨2765582, by rfl⟩ : syracuseStep 3687443 = 5531165) B5531165
theorem B1639463 : Blo 1638018 1639463 := bstep (se 1 (by rfl) ⟨1229597, by rfl⟩ : syracuseStep 1639463 = 2459195) B2459195
theorem B2458703 : Blo 1638018 2458703 := bstep (se 1 (by rfl) ⟨1844027, by rfl⟩ : syracuseStep 2458703 = 3688055) B3688055
theorem B1639503 : Blo 1638018 1639503 := bstep (se 1 (by rfl) ⟨1229627, by rfl⟩ : syracuseStep 1639503 = 2459255) B2459255
theorem B1639519 : Blo 1638018 1639519 := bstep (se 1 (by rfl) ⟨1229639, by rfl⟩ : syracuseStep 1639519 = 2459279) B2459279
theorem B1844347 : Blo 1638018 1844347 := bstep (se 1 (by rfl) ⟨1383260, by rfl⟩ : syracuseStep 1844347 = 2766521) B2766521
theorem B1639547 : Blo 1638018 1639547 := bstep (se 1 (by rfl) ⟨1229660, by rfl⟩ : syracuseStep 1639547 = 2459321) B2459321
theorem B1639599 : Blo 1638018 1639599 := bstep (se 1 (by rfl) ⟨1229699, by rfl⟩ : syracuseStep 1639599 = 2459399) B2459399
theorem B2458823 : Blo 1638018 2458823 := bstep (se 1 (by rfl) ⟨1844117, by rfl⟩ : syracuseStep 2458823 = 3688235) B3688235
theorem B1639623 : Blo 1638018 1639623 := bstep (se 1 (by rfl) ⟨1229717, by rfl⟩ : syracuseStep 1639623 = 2459435) B2459435
theorem B1639643 : Blo 1638018 1639643 := bstep (se 1 (by rfl) ⟨1229732, by rfl⟩ : syracuseStep 1639643 = 2459465) B2459465
theorem B1639719 : Blo 1638018 1639719 := bstep (se 1 (by rfl) ⟨1229789, by rfl⟩ : syracuseStep 1639719 = 2459579) B2459579
theorem B1639759 : Blo 1638018 1639759 := bstep (se 1 (by rfl) ⟨1229819, by rfl⟩ : syracuseStep 1639759 = 2459639) B2459639
theorem B1639775 : Blo 1638018 1639775 := bstep (se 1 (by rfl) ⟨1229831, by rfl⟩ : syracuseStep 1639775 = 2459663) B2459663
theorem B3687785 : Blo 1638018 3687785 := bstep (se 2 (by rfl) ⟨1382919, by rfl⟩ : syracuseStep 3687785 = 2765839) B2765839
theorem B2458985 : Blo 1638018 2458985 := bstep (se 2 (by rfl) ⟨922119, by rfl⟩ : syracuseStep 2458985 = 1844239) B1844239
theorem B1639803 : Blo 1638018 1639803 := bstep (se 1 (by rfl) ⟨1229852, by rfl⟩ : syracuseStep 1639803 = 2459705) B2459705
theorem B9332111 : Blo 1638018 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B12453263 : Blo 1638018 12453263 := bstep (se 1 (by rfl) ⟨9339947, by rfl⟩ : syracuseStep 12453263 = 18679895) B18679895
theorem B1639855 : Blo 1638018 1639855 := bstep (se 1 (by rfl) ⟨1229891, by rfl⟩ : syracuseStep 1639855 = 2459783) B2459783
theorem B2459063 : Blo 1638018 2459063 := bstep (se 1 (by rfl) ⟨1844297, by rfl⟩ : syracuseStep 2459063 = 3688595) B3688595
theorem B1639879 : Blo 1638018 1639879 := bstep (se 1 (by rfl) ⟨1229909, by rfl⟩ : syracuseStep 1639879 = 2459819) B2459819
theorem B179504585 : Blo 1638018 179504585 := bstep (se 2 (by rfl) ⟨67314219, by rfl⟩ : syracuseStep 179504585 = 134628439) B134628439
theorem B2459099 : Blo 1638018 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B1639899 : Blo 1638018 1639899 := bstep (se 1 (by rfl) ⟨1229924, by rfl⟩ : syracuseStep 1639899 = 2459849) B2459849
theorem B1639975 : Blo 1638018 1639975 := bstep (se 1 (by rfl) ⟨1229981, by rfl⟩ : syracuseStep 1639975 = 2459963) B2459963
theorem B1844815 : Blo 1638018 1844815 := bstep (se 1 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 1844815 = 2767223) B2767223
theorem B1640015 : Blo 1638018 1640015 := bstep (se 1 (by rfl) ⟨1230011, by rfl⟩ : syracuseStep 1640015 = 2460023) B2460023
theorem B4146785 : Blo 1638018 4146785 := bstep (se 2 (by rfl) ⟨1555044, by rfl⟩ : syracuseStep 4146785 = 3110089) B3110089
theorem B6219449 : Blo 1638018 6219449 := bstep (se 2 (by rfl) ⟨2332293, by rfl⟩ : syracuseStep 6219449 = 4664587) B4664587
theorem B6219463 : Blo 1638018 6219463 := bstep (se 1 (by rfl) ⟨4664597, by rfl⟩ : syracuseStep 6219463 = 9329195) B9329195
theorem B8300231 : Blo 1638018 8300231 := bstep (se 1 (by rfl) ⟨6225173, by rfl⟩ : syracuseStep 8300231 = 12450347) B12450347
theorem B5531435 : Blo 1638018 5531435 := bstep (se 1 (by rfl) ⟨4148576, by rfl⟩ : syracuseStep 5531435 = 8297153) B8297153
theorem B19933037 : Blo 1638018 19933037 := bstep (se 3 (by rfl) ⟨3737444, by rfl⟩ : syracuseStep 19933037 = 7474889) B7474889
theorem B8857505 : Blo 1638018 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B2459567 : Blo 1638018 2459567 := bstep (se 1 (by rfl) ⟨1844675, by rfl⟩ : syracuseStep 2459567 = 3689351) B3689351
theorem B3688379 : Blo 1638018 3688379 := bstep (se 1 (by rfl) ⟨2766284, by rfl⟩ : syracuseStep 3688379 = 5532569) B5532569
theorem B7874567 : Blo 1638018 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B2459657 : Blo 1638018 2459657 := bstep (se 2 (by rfl) ⟨922371, by rfl⟩ : syracuseStep 2459657 = 1844743) B1844743
theorem B2074663 : Blo 1638018 2074663 := bstep (se 1 (by rfl) ⟨1555997, by rfl⟩ : syracuseStep 2074663 = 3111995) B3111995
theorem B2459687 : Blo 1638018 2459687 := bstep (se 1 (by rfl) ⟨1844765, by rfl⟩ : syracuseStep 2459687 = 3689531) B3689531
theorem B5531705 : Blo 1638018 5531705 := bstep (se 2 (by rfl) ⟨2074389, by rfl⟩ : syracuseStep 5531705 = 4148779) B4148779
theorem B3688505 : Blo 1638018 3688505 := bstep (se 2 (by rfl) ⟨1383189, by rfl⟩ : syracuseStep 3688505 = 2766379) B2766379
theorem B2459771 : Blo 1638018 2459771 := bstep (se 1 (by rfl) ⟨1844828, by rfl⟩ : syracuseStep 2459771 = 3689657) B3689657
theorem B20998277 : Blo 1638018 20998277 := bstep (se 4 (by rfl) ⟨1968588, by rfl⟩ : syracuseStep 20998277 = 3937177) B3937177
theorem B19925149 : Blo 1638018 19925149 := bstep (se 3 (by rfl) ⟨3735965, by rfl⟩ : syracuseStep 19925149 = 7471931) B7471931
theorem B2459897 : Blo 1638018 2459897 := bstep (se 2 (by rfl) ⟨922461, by rfl⟩ : syracuseStep 2459897 = 1844923) B1844923
theorem B2459999 : Blo 1638018 2459999 := bstep (se 1 (by rfl) ⟨1844999, by rfl⟩ : syracuseStep 2459999 = 3689999) B3689999
theorem B2074987 : Blo 1638018 2074987 := bstep (se 1 (by rfl) ⟨1556240, by rfl⟩ : syracuseStep 2074987 = 3112481) B3112481
theorem B2460011 : Blo 1638018 2460011 := bstep (se 1 (by rfl) ⟨1845008, by rfl⟩ : syracuseStep 2460011 = 3690017) B3690017
theorem B5532029 : Blo 1638018 5532029 := bstep (se 3 (by rfl) ⟨1037255, by rfl⟩ : syracuseStep 5532029 = 2074511) B2074511
theorem B3688847 : Blo 1638018 3688847 := bstep (se 1 (by rfl) ⟨2766635, by rfl⟩ : syracuseStep 3688847 = 5533271) B5533271
theorem B15747479 : Blo 1638018 15747479 := bstep (se 1 (by rfl) ⟨11810609, by rfl⟩ : syracuseStep 15747479 = 23621219) B23621219
theorem B3598811 : Blo 1638018 3598811 := bstep (se 1 (by rfl) ⟨2699108, by rfl⟩ : syracuseStep 3598811 = 5398217) B5398217
theorem B13994477 : Blo 1638018 13994477 := bstep (se 3 (by rfl) ⟨2623964, by rfl⟩ : syracuseStep 13994477 = 5247929) B5247929
theorem B5253619 : Blo 1638018 5253619 := bstep (se 1 (by rfl) ⟨3940214, by rfl⟩ : syracuseStep 5253619 = 7880429) B7880429
theorem B6998537 : Blo 1638018 6998537 := bstep (se 2 (by rfl) ⟨2624451, by rfl⟩ : syracuseStep 6998537 = 5248903) B5248903
theorem B2214479 : Blo 1638018 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B2075215 : Blo 1638018 2075215 := bstep (se 1 (by rfl) ⟨1556411, by rfl⟩ : syracuseStep 2075215 = 3112823) B3112823
theorem B5532299 : Blo 1638018 5532299 := bstep (se 1 (by rfl) ⟨4149224, by rfl⟩ : syracuseStep 5532299 = 8298449) B8298449
theorem B6220435 : Blo 1638018 6220435 := bstep (se 1 (by rfl) ⟨4665326, by rfl⟩ : syracuseStep 6220435 = 9330653) B9330653
theorem B3689171 : Blo 1638018 3689171 := bstep (se 1 (by rfl) ⟨2766878, by rfl⟩ : syracuseStep 3689171 = 5533757) B5533757
theorem B17967965 : Blo 1638018 17967965 := bstep (se 3 (by rfl) ⟨3368993, by rfl⟩ : syracuseStep 17967965 = 6737987) B6737987
theorem B4148243 : Blo 1638018 4148243 := bstep (se 1 (by rfl) ⟨3111182, by rfl⟩ : syracuseStep 4148243 = 6222365) B6222365
theorem B8293427 : Blo 1638018 8293427 := bstep (se 1 (by rfl) ⟨6220070, by rfl⟩ : syracuseStep 8293427 = 12440141) B12440141
theorem B4262969 : Blo 1638018 4262969 := bstep (se 2 (by rfl) ⟨1598613, by rfl⟩ : syracuseStep 4262969 = 3197227) B3197227
theorem B6999119 : Blo 1638018 6999119 := bstep (se 1 (by rfl) ⟨5249339, by rfl⟩ : syracuseStep 6999119 = 10498679) B10498679
theorem B6647165 : Blo 1638018 6647165 := bstep (se 3 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 6647165 = 2492687) B2492687
theorem B2764219 : Blo 1638018 2764219 := bstep (se 1 (by rfl) ⟨2073164, by rfl⟩ : syracuseStep 2764219 = 4146329) B4146329
theorem B119557619 : Blo 1638018 119557619 := bstep (se 1 (by rfl) ⟨89668214, by rfl⟩ : syracuseStep 119557619 = 179336429) B179336429
theorem B5533217 : Blo 1638018 5533217 := bstep (se 2 (by rfl) ⟨2074956, by rfl⟩ : syracuseStep 5533217 = 4149913) B4149913
theorem B2764327 : Blo 1638018 2764327 := bstep (se 1 (by rfl) ⟨2073245, by rfl⟩ : syracuseStep 2764327 = 4146491) B4146491
theorem B57560753 : Blo 1638018 57560753 := bstep (se 2 (by rfl) ⟨21585282, by rfl⟩ : syracuseStep 57560753 = 43170565) B43170565
theorem B12447431 : Blo 1638018 12447431 := bstep (se 1 (by rfl) ⟨9335573, by rfl⟩ : syracuseStep 12447431 = 18671147) B18671147
theorem B6999767 : Blo 1638018 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B15748829 : Blo 1638018 15748829 := bstep (se 3 (by rfl) ⟨2952905, by rfl⟩ : syracuseStep 15748829 = 5905811) B5905811
theorem B5533433 : Blo 1638018 5533433 := bstep (se 2 (by rfl) ⟨2075037, by rfl⟩ : syracuseStep 5533433 = 4150075) B4150075
theorem B3321695 : Blo 1638018 3321695 := bstep (se 1 (by rfl) ⟨2491271, by rfl⟩ : syracuseStep 3321695 = 4982543) B4982543
theorem B2764651 : Blo 1638018 2764651 := bstep (se 1 (by rfl) ⟨2073488, by rfl⟩ : syracuseStep 2764651 = 4146977) B4146977
theorem B5607343 : Blo 1638018 5607343 := bstep (se 1 (by rfl) ⟨4205507, by rfl⟩ : syracuseStep 5607343 = 8411015) B8411015
theorem B5533703 : Blo 1638018 5533703 := bstep (se 1 (by rfl) ⟨4150277, by rfl⟩ : syracuseStep 5533703 = 8300555) B8300555
theorem B4206649 : Blo 1638018 4206649 := bstep (se 2 (by rfl) ⟨1577493, by rfl⟩ : syracuseStep 4206649 = 3154987) B3154987
theorem B5533811 : Blo 1638018 5533811 := bstep (se 1 (by rfl) ⟨4150358, by rfl⟩ : syracuseStep 5533811 = 8300717) B8300717
theorem B10506469 : Blo 1638018 10506469 := bstep (se 4 (by rfl) ⟨984981, by rfl⟩ : syracuseStep 10506469 = 1969963) B1969963
theorem B12620033 : Blo 1638018 12620033 := bstep (se 2 (by rfl) ⟨4732512, by rfl⟩ : syracuseStep 12620033 = 9465025) B9465025
theorem B6222167 : Blo 1638018 6222167 := bstep (se 1 (by rfl) ⟨4666625, by rfl⟩ : syracuseStep 6222167 = 9333251) B9333251
theorem B2625887 : Blo 1638018 2625887 := bstep (se 1 (by rfl) ⟨1969415, by rfl⟩ : syracuseStep 2625887 = 3938831) B3938831
theorem B8860033 : Blo 1638018 8860033 := bstep (se 2 (by rfl) ⟨3322512, by rfl⟩ : syracuseStep 8860033 = 6645025) B6645025
theorem B5534081 : Blo 1638018 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B4207067 : Blo 1638018 4207067 := bstep (se 1 (by rfl) ⟨3155300, by rfl⟩ : syracuseStep 4207067 = 6310601) B6310601
theorem B3936755 : Blo 1638018 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B1749583 : Blo 1638018 1749583 := bstep (se 1 (by rfl) ⟨1312187, by rfl⟩ : syracuseStep 1749583 = 2624375) B2624375
theorem B8295047 : Blo 1638018 8295047 := bstep (se 1 (by rfl) ⟨6221285, by rfl⟩ : syracuseStep 8295047 = 12442571) B12442571
theorem B4666045 : Blo 1638018 4666045 := bstep (se 3 (by rfl) ⟨874883, by rfl⟩ : syracuseStep 4666045 = 1749767) B1749767
theorem B44864209 : Blo 1638018 44864209 := bstep (se 2 (by rfl) ⟨16824078, by rfl⟩ : syracuseStep 44864209 = 33648157) B33648157
theorem B4428503 : Blo 1638018 4428503 := bstep (se 1 (by rfl) ⟨3321377, by rfl⟩ : syracuseStep 4428503 = 6642755) B6642755
theorem B177476417 : Blo 1638018 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B2765711 : Blo 1638018 2765711 := bstep (se 1 (by rfl) ⟨2074283, by rfl⟩ : syracuseStep 2765711 = 4148567) B4148567
theorem B9335735 : Blo 1638018 9335735 := bstep (se 1 (by rfl) ⟨7001801, by rfl⟩ : syracuseStep 9335735 = 14003603) B14003603
theorem B3109907 : Blo 1638018 3109907 := bstep (se 1 (by rfl) ⟨2332430, by rfl⟩ : syracuseStep 3109907 = 4664861) B4664861
theorem B12440627 : Blo 1638018 12440627 := bstep (se 1 (by rfl) ⟨9330470, by rfl⟩ : syracuseStep 12440627 = 18660941) B18660941
theorem B2765947 : Blo 1638018 2765947 := bstep (se 1 (by rfl) ⟨2074460, by rfl⟩ : syracuseStep 2765947 = 4148921) B4148921
theorem B5534891 : Blo 1638018 5534891 := bstep (se 1 (by rfl) ⟨4151168, by rfl⟩ : syracuseStep 5534891 = 8302337) B8302337
theorem B50468305 : Blo 1638018 50468305 := bstep (se 2 (by rfl) ⟨18925614, by rfl⟩ : syracuseStep 50468305 = 37851229) B37851229
theorem B11974205 : Blo 1638018 11974205 := bstep (se 3 (by rfl) ⟨2245163, by rfl⟩ : syracuseStep 11974205 = 4490327) B4490327
theorem B23615225 : Blo 1638018 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B42596131 : Blo 1638018 42596131 := bstep (se 1 (by rfl) ⟨31947098, by rfl⟩ : syracuseStep 42596131 = 63894197) B63894197
theorem B10639163 : Blo 1638018 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B2365367 : Blo 1638018 2365367 := bstep (se 1 (by rfl) ⟨1774025, by rfl⟩ : syracuseStep 2365367 = 3548051) B3548051
theorem B5248955 : Blo 1638018 5248955 := bstep (se 1 (by rfl) ⟨3936716, by rfl⟩ : syracuseStep 5248955 = 7873433) B7873433
theorem B14186449 : Blo 1638018 14186449 := bstep (se 2 (by rfl) ⟨5319918, by rfl⟩ : syracuseStep 14186449 = 10639837) B10639837
theorem B2766811 : Blo 1638018 2766811 := bstep (se 1 (by rfl) ⟨2075108, by rfl⟩ : syracuseStep 2766811 = 4150217) B4150217
theorem B8296505 : Blo 1638018 8296505 := bstep (se 2 (by rfl) ⟨3111189, by rfl⟩ : syracuseStep 8296505 = 6222379) B6222379
theorem B7002227 : Blo 1638018 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B2332795 : Blo 1638018 2332795 := bstep (se 1 (by rfl) ⟨1749596, by rfl⟩ : syracuseStep 2332795 = 3499193) B3499193
theorem B31922465 : Blo 1638018 31922465 := bstep (se 2 (by rfl) ⟨11970924, by rfl⟩ : syracuseStep 31922465 = 23941849) B23941849
theorem B3324233 : Blo 1638018 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B9337193 : Blo 1638018 9337193 := bstep (se 2 (by rfl) ⟨3501447, by rfl⟩ : syracuseStep 9337193 = 7002895) B7002895
theorem B4667777 : Blo 1638018 4667777 := bstep (se 2 (by rfl) ⟨1750416, by rfl⟩ : syracuseStep 4667777 = 3500833) B3500833
theorem B3111311 : Blo 1638018 3111311 := bstep (se 1 (by rfl) ⟨2333483, by rfl⟩ : syracuseStep 3111311 = 4666967) B4666967
theorem B7477769 : Blo 1638018 7477769 := bstep (se 2 (by rfl) ⟨2804163, by rfl⟩ : syracuseStep 7477769 = 5608327) B5608327
theorem B3111463 : Blo 1638018 3111463 := bstep (se 1 (by rfl) ⟨2333597, by rfl⟩ : syracuseStep 3111463 = 4667195) B4667195
theorem B2767439 : Blo 1638018 2767439 := bstep (se 1 (by rfl) ⟨2075579, by rfl⟩ : syracuseStep 2767439 = 4151159) B4151159
theorem B3111547 : Blo 1638018 3111547 := bstep (se 1 (by rfl) ⟨2333660, by rfl⟩ : syracuseStep 3111547 = 4667321) B4667321
theorem B11819951 : Blo 1638018 11819951 := bstep (se 1 (by rfl) ⟨8864963, by rfl⟩ : syracuseStep 11819951 = 17729927) B17729927
theorem B3112033 : Blo 1638018 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B5528843 : Blo 1638018 5528843 := bstep (se 1 (by rfl) ⟨4146632, by rfl⟩ : syracuseStep 5528843 = 8293265) B8293265
theorem B28392727 : Blo 1638018 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B5250365 : Blo 1638018 5250365 := bstep (se 3 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 5250365 = 1968887) B1968887
theorem B1662287 : Blo 1638018 1662287 := bstep (se 1 (by rfl) ⟨1246715, by rfl⟩ : syracuseStep 1662287 = 2493431) B2493431
theorem B6225281 : Blo 1638018 6225281 := bstep (se 2 (by rfl) ⟨2334480, by rfl⟩ : syracuseStep 6225281 = 4668961) B4668961
theorem B6225295 : Blo 1638018 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B5529113 : Blo 1638018 5529113 := bstep (se 2 (by rfl) ⟨2073417, by rfl⟩ : syracuseStep 5529113 = 4146835) B4146835
theorem B2457167 : Blo 1638018 2457167 := bstep (se 1 (by rfl) ⟨1842875, by rfl⟩ : syracuseStep 2457167 = 3685751) B3685751
theorem B3685985 : Blo 1638018 3685985 := bstep (se 2 (by rfl) ⟨1382244, by rfl⟩ : syracuseStep 3685985 = 2764489) B2764489
theorem B1638063 : Blo 1638018 1638063 := bstep (se 1 (by rfl) ⟨1228547, by rfl⟩ : syracuseStep 1638063 = 2457095) B2457095
theorem B1638087 : Blo 1638018 1638087 := bstep (se 1 (by rfl) ⟨1228565, by rfl⟩ : syracuseStep 1638087 = 2457131) B2457131
theorem B2457287 : Blo 1638018 2457287 := bstep (se 1 (by rfl) ⟨1842965, by rfl⟩ : syracuseStep 2457287 = 3685931) B3685931
theorem B1638107 : Blo 1638018 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B4669177 : Blo 1638018 4669177 := bstep (se 2 (by rfl) ⟨1750941, by rfl⟩ : syracuseStep 4669177 = 3501883) B3501883
theorem B1638183 : Blo 1638018 1638183 := bstep (se 1 (by rfl) ⟨1228637, by rfl⟩ : syracuseStep 1638183 = 2457275) B2457275
theorem B170319665 : Blo 1638018 170319665 := bstep (se 2 (by rfl) ⟨63869874, by rfl⟩ : syracuseStep 170319665 = 127739749) B127739749
theorem B11214659 : Blo 1638018 11214659 := bstep (se 1 (by rfl) ⟨8410994, by rfl⟩ : syracuseStep 11214659 = 16821989) B16821989
theorem B1638223 : Blo 1638018 1638223 := bstep (se 1 (by rfl) ⟨1228667, by rfl⟩ : syracuseStep 1638223 = 2457335) B2457335
theorem B1638239 : Blo 1638018 1638239 := bstep (se 1 (by rfl) ⟨1228679, by rfl⟩ : syracuseStep 1638239 = 2457359) B2457359
theorem B2457449 : Blo 1638018 2457449 := bstep (se 2 (by rfl) ⟨921543, by rfl⟩ : syracuseStep 2457449 = 1843087) B1843087
theorem B1638267 : Blo 1638018 1638267 := bstep (se 1 (by rfl) ⟨1228700, by rfl⟩ : syracuseStep 1638267 = 2457401) B2457401
theorem B1638319 : Blo 1638018 1638319 := bstep (se 1 (by rfl) ⟨1228739, by rfl⟩ : syracuseStep 1638319 = 2457479) B2457479
theorem B2457527 : Blo 1638018 2457527 := bstep (se 1 (by rfl) ⟨1843145, by rfl⟩ : syracuseStep 2457527 = 3686291) B3686291
theorem B3686327 : Blo 1638018 3686327 := bstep (se 1 (by rfl) ⟨2764745, by rfl⟩ : syracuseStep 3686327 = 5529491) B5529491
theorem B1638343 : Blo 1638018 1638343 := bstep (se 1 (by rfl) ⟨1228757, by rfl⟩ : syracuseStep 1638343 = 2457515) B2457515
theorem B1638363 : Blo 1638018 1638363 := bstep (se 1 (by rfl) ⟨1228772, by rfl⟩ : syracuseStep 1638363 = 2457545) B2457545
theorem B2457563 : Blo 1638018 2457563 := bstep (se 1 (by rfl) ⟨1843172, by rfl⟩ : syracuseStep 2457563 = 3686345) B3686345
theorem B8413355 : Blo 1638018 8413355 := bstep (se 1 (by rfl) ⟨6310016, by rfl⟩ : syracuseStep 8413355 = 12620033) B12620033
theorem B26566865 : Blo 1638018 26566865 := bstep (se 2 (by rfl) ⟨9962574, by rfl⟩ : syracuseStep 26566865 = 19925149) B19925149
theorem B3113225 : Blo 1638018 3113225 := bstep (se 2 (by rfl) ⟨1167459, by rfl⟩ : syracuseStep 3113225 = 2334919) B2334919
theorem B1638687 : Blo 1638018 1638687 := bstep (se 1 (by rfl) ⟨1229015, by rfl⟩ : syracuseStep 1638687 = 2458031) B2458031
theorem B14008625 : Blo 1638018 14008625 := bstep (se 2 (by rfl) ⟨5253234, by rfl⟩ : syracuseStep 14008625 = 10506469) B10506469
theorem B2457947 : Blo 1638018 2457947 := bstep (se 1 (by rfl) ⟨1843460, by rfl⟩ : syracuseStep 2457947 = 3686921) B3686921
theorem B1638747 : Blo 1638018 1638747 := bstep (se 1 (by rfl) ⟨1229060, by rfl⟩ : syracuseStep 1638747 = 2458121) B2458121
theorem B6226267 : Blo 1638018 6226267 := bstep (se 1 (by rfl) ⟨4669700, by rfl⟩ : syracuseStep 6226267 = 9339401) B9339401
theorem B1638767 : Blo 1638018 1638767 := bstep (se 1 (by rfl) ⟨1229075, by rfl⟩ : syracuseStep 1638767 = 2458151) B2458151
theorem B9331109 : Blo 1638018 9331109 := bstep (se 4 (by rfl) ⟨874791, by rfl⟩ : syracuseStep 9331109 = 1749583) B1749583
theorem B1638823 : Blo 1638018 1638823 := bstep (se 1 (by rfl) ⟨1229117, by rfl⟩ : syracuseStep 1638823 = 2458235) B2458235
theorem B5530031 : Blo 1638018 5530031 := bstep (se 1 (by rfl) ⟨4147523, by rfl⟩ : syracuseStep 5530031 = 8295047) B8295047
theorem B3686831 : Blo 1638018 3686831 := bstep (se 1 (by rfl) ⟨2765123, by rfl⟩ : syracuseStep 3686831 = 5530247) B5530247
theorem B3686867 : Blo 1638018 3686867 := bstep (se 1 (by rfl) ⟨2765150, by rfl⟩ : syracuseStep 3686867 = 5530301) B5530301
theorem B1638907 : Blo 1638018 1638907 := bstep (se 1 (by rfl) ⟨1229180, by rfl⟩ : syracuseStep 1638907 = 2458361) B2458361
theorem B11813377 : Blo 1638018 11813377 := bstep (se 2 (by rfl) ⟨4430016, by rfl⟩ : syracuseStep 11813377 = 8860033) B8860033
theorem B118317611 : Blo 1638018 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B3686975 : Blo 1638018 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B2458175 : Blo 1638018 2458175 := bstep (se 1 (by rfl) ⟨1843631, by rfl⟩ : syracuseStep 2458175 = 3687263) B3687263
theorem B1638975 : Blo 1638018 1638975 := bstep (se 1 (by rfl) ⟨1229231, by rfl⟩ : syracuseStep 1638975 = 2458463) B2458463
theorem B7094855 : Blo 1638018 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B1638983 : Blo 1638018 1638983 := bstep (se 1 (by rfl) ⟨1229237, by rfl⟩ : syracuseStep 1638983 = 2458475) B2458475
theorem B1843807 : Blo 1638018 1843807 := bstep (se 1 (by rfl) ⟨1382855, by rfl⟩ : syracuseStep 1843807 = 2765711) B2765711
theorem B7004825 : Blo 1638018 7004825 := bstep (se 2 (by rfl) ⟨2626809, by rfl⟩ : syracuseStep 7004825 = 5253619) B5253619
theorem B3687083 : Blo 1638018 3687083 := bstep (se 1 (by rfl) ⟨2765312, by rfl⟩ : syracuseStep 3687083 = 5530625) B5530625
theorem B2073271 : Blo 1638018 2073271 := bstep (se 1 (by rfl) ⟨1554953, by rfl⟩ : syracuseStep 2073271 = 3109907) B3109907
theorem B2458295 : Blo 1638018 2458295 := bstep (se 1 (by rfl) ⟨1843721, by rfl⟩ : syracuseStep 2458295 = 3687443) B3687443
theorem B1639135 : Blo 1638018 1639135 := bstep (se 1 (by rfl) ⟨1229351, by rfl⟩ : syracuseStep 1639135 = 2458703) B2458703
theorem B1639215 : Blo 1638018 1639215 := bstep (se 1 (by rfl) ⟨1229411, by rfl⟩ : syracuseStep 1639215 = 2458823) B2458823
theorem B4432765 : Blo 1638018 4432765 := bstep (se 3 (by rfl) ⟨831143, by rfl⟩ : syracuseStep 4432765 = 1662287) B1662287
theorem B2458523 : Blo 1638018 2458523 := bstep (se 1 (by rfl) ⟨1843892, by rfl⟩ : syracuseStep 2458523 = 3687785) B3687785
theorem B1639323 : Blo 1638018 1639323 := bstep (se 1 (by rfl) ⟨1229492, by rfl⟩ : syracuseStep 1639323 = 2458985) B2458985
theorem B59818945 : Blo 1638018 59818945 := bstep (se 2 (by rfl) ⟨22432104, by rfl⟩ : syracuseStep 59818945 = 44864209) B44864209
theorem B1639375 : Blo 1638018 1639375 := bstep (se 1 (by rfl) ⟨1229531, by rfl⟩ : syracuseStep 1639375 = 2459063) B2459063
theorem B119669723 : Blo 1638018 119669723 := bstep (se 1 (by rfl) ⟨89752292, by rfl⟩ : syracuseStep 119669723 = 179504585) B179504585
theorem B1639399 : Blo 1638018 1639399 := bstep (se 1 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 1639399 = 2459099) B2459099
theorem B4146299 : Blo 1638018 4146299 := bstep (se 1 (by rfl) ⟨3109724, by rfl⟩ : syracuseStep 4146299 = 6219449) B6219449
theorem B3687623 : Blo 1638018 3687623 := bstep (se 1 (by rfl) ⟨2765717, by rfl⟩ : syracuseStep 3687623 = 5531435) B5531435
theorem B13288691 : Blo 1638018 13288691 := bstep (se 1 (by rfl) ⟨9966518, by rfl⟩ : syracuseStep 13288691 = 19933037) B19933037
theorem B1639711 : Blo 1638018 1639711 := bstep (se 1 (by rfl) ⟨1229783, by rfl⟩ : syracuseStep 1639711 = 2459567) B2459567
theorem B3499303 : Blo 1638018 3499303 := bstep (se 1 (by rfl) ⟨2624477, by rfl⟩ : syracuseStep 3499303 = 5248955) B5248955
theorem B2458919 : Blo 1638018 2458919 := bstep (se 1 (by rfl) ⟨1844189, by rfl⟩ : syracuseStep 2458919 = 3688379) B3688379
theorem B1639771 : Blo 1638018 1639771 := bstep (se 1 (by rfl) ⟨1229828, by rfl⟩ : syracuseStep 1639771 = 2459657) B2459657
theorem B19940717 : Blo 1638018 19940717 := bstep (se 3 (by rfl) ⟨3738884, by rfl⟩ : syracuseStep 19940717 = 7477769) B7477769
theorem B1639791 : Blo 1638018 1639791 := bstep (se 1 (by rfl) ⟨1229843, by rfl⟩ : syracuseStep 1639791 = 2459687) B2459687
theorem B5531003 : Blo 1638018 5531003 := bstep (se 1 (by rfl) ⟨4148252, by rfl⟩ : syracuseStep 5531003 = 8296505) B8296505
theorem B3687803 : Blo 1638018 3687803 := bstep (se 1 (by rfl) ⟨2765852, by rfl⟩ : syracuseStep 3687803 = 5531705) B5531705
theorem B2459003 : Blo 1638018 2459003 := bstep (se 1 (by rfl) ⟨1844252, by rfl⟩ : syracuseStep 2459003 = 3688505) B3688505
theorem B1639847 : Blo 1638018 1639847 := bstep (se 1 (by rfl) ⟨1229885, by rfl⟩ : syracuseStep 1639847 = 2459771) B2459771
theorem B3687929 : Blo 1638018 3687929 := bstep (se 2 (by rfl) ⟨1382973, by rfl⟩ : syracuseStep 3687929 = 2765947) B2765947
theorem B2459129 : Blo 1638018 2459129 := bstep (se 2 (by rfl) ⟨922173, by rfl⟩ : syracuseStep 2459129 = 1844347) B1844347
theorem B1639931 : Blo 1638018 1639931 := bstep (se 1 (by rfl) ⟨1229948, by rfl⟩ : syracuseStep 1639931 = 2459897) B2459897
theorem B1639999 : Blo 1638018 1639999 := bstep (se 1 (by rfl) ⟨1229999, by rfl⟩ : syracuseStep 1639999 = 2459999) B2459999
theorem B1640007 : Blo 1638018 1640007 := bstep (se 1 (by rfl) ⟨1230005, by rfl⟩ : syracuseStep 1640007 = 2460011) B2460011
theorem B3688019 : Blo 1638018 3688019 := bstep (se 1 (by rfl) ⟨2766014, by rfl⟩ : syracuseStep 3688019 = 5532029) B5532029
theorem B2459231 : Blo 1638018 2459231 := bstep (se 1 (by rfl) ⟨1844423, by rfl⟩ : syracuseStep 2459231 = 3688847) B3688847
theorem B37856969 : Blo 1638018 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B1844959 : Blo 1638018 1844959 := bstep (se 1 (by rfl) ⟨1383719, by rfl⟩ : syracuseStep 1844959 = 2767439) B2767439
theorem B3688199 : Blo 1638018 3688199 := bstep (se 1 (by rfl) ⟨2766149, by rfl⟩ : syracuseStep 3688199 = 5532299) B5532299
theorem B2459447 : Blo 1638018 2459447 := bstep (se 1 (by rfl) ⟨1844585, by rfl⟩ : syracuseStep 2459447 = 3689171) B3689171
theorem B8300393 : Blo 1638018 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B67291073 : Blo 1638018 67291073 := bstep (se 2 (by rfl) ⟨25234152, by rfl⟩ : syracuseStep 67291073 = 50468305) B50468305
theorem B2459753 : Blo 1638018 2459753 := bstep (se 2 (by rfl) ⟨922407, by rfl⟩ : syracuseStep 2459753 = 1844815) B1844815
theorem B3500243 : Blo 1638018 3500243 := bstep (se 1 (by rfl) ⟨2625182, by rfl⟩ : syracuseStep 3500243 = 5250365) B5250365
theorem B8292617 : Blo 1638018 8292617 := bstep (se 2 (by rfl) ⟨3109731, by rfl⟩ : syracuseStep 8292617 = 6219463) B6219463
theorem B3688811 : Blo 1638018 3688811 := bstep (se 1 (by rfl) ⟨2766608, by rfl⟩ : syracuseStep 3688811 = 5533217) B5533217
theorem B38373835 : Blo 1638018 38373835 := bstep (se 1 (by rfl) ⟨28780376, by rfl⟩ : syracuseStep 38373835 = 57560753) B57560753
theorem B3688955 : Blo 1638018 3688955 := bstep (se 1 (by rfl) ⟨2766716, by rfl⟩ : syracuseStep 3688955 = 5533433) B5533433
theorem B2214463 : Blo 1638018 2214463 := bstep (se 1 (by rfl) ⟨1660847, by rfl⟩ : syracuseStep 2214463 = 3321695) B3321695
theorem B3689081 : Blo 1638018 3689081 := bstep (se 2 (by rfl) ⟨1383405, by rfl⟩ : syracuseStep 3689081 = 2766811) B2766811
theorem B3689135 : Blo 1638018 3689135 := bstep (se 1 (by rfl) ⟨2766851, by rfl⟩ : syracuseStep 3689135 = 5533703) B5533703
theorem B2075311 : Blo 1638018 2075311 := bstep (se 1 (by rfl) ⟨1556483, by rfl⟩ : syracuseStep 2075311 = 3112967) B3112967
theorem B5532407 : Blo 1638018 5532407 := bstep (se 1 (by rfl) ⟨4149305, by rfl⟩ : syracuseStep 5532407 = 8298611) B8298611
theorem B3689207 : Blo 1638018 3689207 := bstep (se 1 (by rfl) ⟨2766905, by rfl⟩ : syracuseStep 3689207 = 5533811) B5533811
theorem B4148111 : Blo 1638018 4148111 := bstep (se 1 (by rfl) ⟨3111083, by rfl⟩ : syracuseStep 4148111 = 6222167) B6222167
theorem B3689387 : Blo 1638018 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B18672605 : Blo 1638018 18672605 := bstep (se 3 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 18672605 = 7002227) B7002227
theorem B2804711 : Blo 1638018 2804711 := bstep (se 1 (by rfl) ⟨2103533, by rfl⟩ : syracuseStep 2804711 = 4207067) B4207067
theorem B2624503 : Blo 1638018 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B2952335 : Blo 1638018 2952335 := bstep (se 1 (by rfl) ⟨2214251, by rfl⟩ : syracuseStep 2952335 = 4428503) B4428503
theorem B14953643 : Blo 1638018 14953643 := bstep (se 1 (by rfl) ⟨11215232, by rfl⟩ : syracuseStep 14953643 = 22430465) B22430465
theorem B8293751 : Blo 1638018 8293751 := bstep (se 1 (by rfl) ⟨6220313, by rfl⟩ : syracuseStep 8293751 = 12440627) B12440627
theorem B4148617 : Blo 1638018 4148617 := bstep (se 2 (by rfl) ⟨1555731, by rfl⟩ : syracuseStep 4148617 = 3111463) B3111463
theorem B85126573 : Blo 1638018 85126573 := bstep (se 3 (by rfl) ⟨15961232, by rfl⟩ : syracuseStep 85126573 = 31922465) B31922465
theorem B3689927 : Blo 1638018 3689927 := bstep (se 1 (by rfl) ⟨2767445, by rfl⟩ : syracuseStep 3689927 = 5534891) B5534891
theorem B4148729 : Blo 1638018 4148729 := bstep (se 2 (by rfl) ⟨1555773, by rfl⟩ : syracuseStep 4148729 = 3111547) B3111547
theorem B8293913 : Blo 1638018 8293913 := bstep (se 2 (by rfl) ⟨3110217, by rfl⟩ : syracuseStep 8293913 = 6220435) B6220435
theorem B6221393 : Blo 1638018 6221393 := bstep (se 2 (by rfl) ⟨2333022, by rfl⟩ : syracuseStep 6221393 = 4666045) B4666045
theorem B6221407 : Blo 1638018 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B8302175 : Blo 1638018 8302175 := bstep (se 1 (by rfl) ⟨6226631, by rfl⟩ : syracuseStep 8302175 = 12453263) B12453263
theorem B7982803 : Blo 1638018 7982803 := bstep (se 1 (by rfl) ⟨5987102, by rfl⟩ : syracuseStep 7982803 = 11974205) B11974205
theorem B2764523 : Blo 1638018 2764523 := bstep (se 1 (by rfl) ⟨2073392, by rfl⟩ : syracuseStep 2764523 = 4146785) B4146785
theorem B5533487 : Blo 1638018 5533487 := bstep (se 1 (by rfl) ⟨4150115, by rfl⟩ : syracuseStep 5533487 = 8300231) B8300231
theorem B4149377 : Blo 1638018 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B2216155 : Blo 1638018 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B10498319 : Blo 1638018 10498319 := bstep (se 1 (by rfl) ⟨7873739, by rfl⟩ : syracuseStep 10498319 = 15747479) B15747479
theorem B4665691 : Blo 1638018 4665691 := bstep (se 1 (by rfl) ⟨3499268, by rfl⟩ : syracuseStep 4665691 = 6998537) B6998537
theorem B2765495 : Blo 1638018 2765495 := bstep (se 1 (by rfl) ⟨2074121, by rfl⟩ : syracuseStep 2765495 = 4148243) B4148243
theorem B4666079 : Blo 1638018 4666079 := bstep (se 1 (by rfl) ⟨3499559, by rfl⟩ : syracuseStep 4666079 = 6999119) B6999119
theorem B29905757 : Blo 1638018 29905757 := bstep (se 3 (by rfl) ⟨5607329, by rfl⟩ : syracuseStep 29905757 = 11214659) B11214659
theorem B4150187 : Blo 1638018 4150187 := bstep (se 1 (by rfl) ⟨3112640, by rfl⟩ : syracuseStep 4150187 = 6225281) B6225281
theorem B79705079 : Blo 1638018 79705079 := bstep (se 1 (by rfl) ⟨59778809, by rfl⟩ : syracuseStep 79705079 = 119557619) B119557619
theorem B4666511 : Blo 1638018 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B10499219 : Blo 1638018 10499219 := bstep (se 1 (by rfl) ⟨7874414, by rfl⟩ : syracuseStep 10499219 = 15748829) B15748829
theorem B113546443 : Blo 1638018 113546443 := bstep (se 1 (by rfl) ⟨85159832, by rfl⟩ : syracuseStep 113546443 = 170319665) B170319665
theorem B7476457 : Blo 1638018 7476457 := bstep (se 2 (by rfl) ⟨2803671, by rfl⟩ : syracuseStep 7476457 = 5607343) B5607343
theorem B2766217 : Blo 1638018 2766217 := bstep (se 2 (by rfl) ⟨1037331, by rfl⟩ : syracuseStep 2766217 = 2074663) B2074663
theorem B5608865 : Blo 1638018 5608865 := bstep (se 2 (by rfl) ⟨2103324, by rfl⟩ : syracuseStep 5608865 = 4206649) B4206649
theorem B3110393 : Blo 1638018 3110393 := bstep (se 2 (by rfl) ⟨1166397, by rfl⟩ : syracuseStep 3110393 = 2332795) B2332795
theorem B1750591 : Blo 1638018 1750591 := bstep (se 1 (by rfl) ⟨1312943, by rfl⟩ : syracuseStep 1750591 = 2625887) B2625887
theorem B4151047 : Blo 1638018 4151047 := bstep (se 1 (by rfl) ⟨3113285, by rfl⟩ : syracuseStep 4151047 = 6226571) B6226571
theorem B2766649 : Blo 1638018 2766649 := bstep (se 2 (by rfl) ⟨1037493, by rfl⟩ : syracuseStep 2766649 = 2074987) B2074987
theorem B6223823 : Blo 1638018 6223823 := bstep (se 1 (by rfl) ⟨4667867, by rfl⟩ : syracuseStep 6223823 = 9335735) B9335735
theorem B2766953 : Blo 1638018 2766953 := bstep (se 2 (by rfl) ⟨1037607, by rfl⟩ : syracuseStep 2766953 = 2075215) B2075215
theorem B8296829 : Blo 1638018 8296829 := bstep (se 3 (by rfl) ⟨1555655, by rfl⟩ : syracuseStep 8296829 = 3111311) B3111311
theorem B153549269 : Blo 1638018 153549269 := bstep (se 7 (by rfl) ⟨1799405, by rfl⟩ : syracuseStep 153549269 = 3598811) B3598811
theorem B15743483 : Blo 1638018 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B7092775 : Blo 1638018 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B5905003 : Blo 1638018 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B5249711 : Blo 1638018 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B13998851 : Blo 1638018 13998851 := bstep (se 1 (by rfl) ⟨10499138, by rfl⟩ : syracuseStep 13998851 = 20998277) B20998277
theorem B5905277 : Blo 1638018 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B6224795 : Blo 1638018 6224795 := bstep (se 1 (by rfl) ⟨4668596, by rfl⟩ : syracuseStep 6224795 = 9337193) B9337193
theorem B3111851 : Blo 1638018 3111851 := bstep (se 1 (by rfl) ⟨2333888, by rfl⟩ : syracuseStep 3111851 = 4667777) B4667777
theorem B9329651 : Blo 1638018 9329651 := bstep (se 1 (by rfl) ⟨6997238, by rfl⟩ : syracuseStep 9329651 = 13994477) B13994477
theorem B3685625 : Blo 1638018 3685625 := bstep (se 2 (by rfl) ⟨1382109, by rfl⟩ : syracuseStep 3685625 = 2764219) B2764219
theorem B7879967 : Blo 1638018 7879967 := bstep (se 1 (by rfl) ⟨5909975, by rfl⟩ : syracuseStep 7879967 = 11819951) B11819951
theorem B5528951 : Blo 1638018 5528951 := bstep (se 1 (by rfl) ⟨4146713, by rfl⟩ : syracuseStep 5528951 = 8293427) B8293427
theorem B2841979 : Blo 1638018 2841979 := bstep (se 1 (by rfl) ⟨2131484, by rfl⟩ : syracuseStep 2841979 = 4262969) B4262969
theorem B3685769 : Blo 1638018 3685769 := bstep (se 2 (by rfl) ⟨1382163, by rfl⟩ : syracuseStep 3685769 = 2764327) B2764327
theorem B3685895 : Blo 1638018 3685895 := bstep (se 1 (by rfl) ⟨2764421, by rfl⟩ : syracuseStep 3685895 = 5528843) B5528843
theorem B47914573 : Blo 1638018 47914573 := bstep (se 3 (by rfl) ⟨8983982, by rfl⟩ : syracuseStep 47914573 = 17967965) B17967965
theorem B4431443 : Blo 1638018 4431443 := bstep (se 1 (by rfl) ⟨3323582, by rfl⟩ : syracuseStep 4431443 = 6647165) B6647165
theorem B6643309 : Blo 1638018 6643309 := bstep (se 3 (by rfl) ⟨1245620, by rfl⟩ : syracuseStep 6643309 = 2491241) B2491241
theorem B6225569 : Blo 1638018 6225569 := bstep (se 2 (by rfl) ⟨2334588, by rfl⟩ : syracuseStep 6225569 = 4669177) B4669177
theorem B3686075 : Blo 1638018 3686075 := bstep (se 1 (by rfl) ⟨2764556, by rfl⟩ : syracuseStep 3686075 = 5529113) B5529113
theorem B56794841 : Blo 1638018 56794841 := bstep (se 2 (by rfl) ⟨21298065, by rfl⟩ : syracuseStep 56794841 = 42596131) B42596131
theorem B1638111 : Blo 1638018 1638111 := bstep (se 1 (by rfl) ⟨1228583, by rfl⟩ : syracuseStep 1638111 = 2457167) B2457167
theorem B2457323 : Blo 1638018 2457323 := bstep (se 1 (by rfl) ⟨1842992, by rfl⟩ : syracuseStep 2457323 = 3685985) B3685985
theorem B1638191 : Blo 1638018 1638191 := bstep (se 1 (by rfl) ⟨1228643, by rfl⟩ : syracuseStep 1638191 = 2457287) B2457287
theorem B8298287 : Blo 1638018 8298287 := bstep (se 1 (by rfl) ⟨6223715, by rfl⟩ : syracuseStep 8298287 = 12447431) B12447431
theorem B3686201 : Blo 1638018 3686201 := bstep (se 2 (by rfl) ⟨1382325, by rfl⟩ : syracuseStep 3686201 = 2764651) B2764651
theorem B6307645 : Blo 1638018 6307645 := bstep (se 3 (by rfl) ⟨1182683, by rfl⟩ : syracuseStep 6307645 = 2365367) B2365367
theorem B1638299 : Blo 1638018 1638299 := bstep (se 1 (by rfl) ⟨1228724, by rfl⟩ : syracuseStep 1638299 = 2457449) B2457449
theorem B18915265 : Blo 1638018 18915265 := bstep (se 2 (by rfl) ⟨7093224, by rfl⟩ : syracuseStep 18915265 = 14186449) B14186449
theorem B1638351 : Blo 1638018 1638351 := bstep (se 1 (by rfl) ⟨1228763, by rfl⟩ : syracuseStep 1638351 = 2457527) B2457527
theorem B2457551 : Blo 1638018 2457551 := bstep (se 1 (by rfl) ⟨1843163, by rfl⟩ : syracuseStep 2457551 = 3686327) B3686327
theorem B1638375 : Blo 1638018 1638375 := bstep (se 1 (by rfl) ⟨1228781, by rfl⟩ : syracuseStep 1638375 = 2457563) B2457563
theorem B17711243 : Blo 1638018 17711243 := bstep (se 1 (by rfl) ⟨13283432, by rfl⟩ : syracuseStep 17711243 = 26566865) B26566865
theorem B9339083 : Blo 1638018 9339083 := bstep (se 1 (by rfl) ⟨7004312, by rfl⟩ : syracuseStep 9339083 = 14008625) B14008625
theorem B1638631 : Blo 1638018 1638631 := bstep (se 1 (by rfl) ⟨1228973, by rfl⟩ : syracuseStep 1638631 = 2457947) B2457947
theorem B3686687 : Blo 1638018 3686687 := bstep (se 1 (by rfl) ⟨2765015, by rfl⟩ : syracuseStep 3686687 = 5530031) B5530031
theorem B2457887 : Blo 1638018 2457887 := bstep (se 1 (by rfl) ⟨1843415, by rfl⟩ : syracuseStep 2457887 = 3686831) B3686831
theorem B2457911 : Blo 1638018 2457911 := bstep (se 1 (by rfl) ⟨1843433, by rfl⟩ : syracuseStep 2457911 = 3686867) B3686867
theorem B7872893 : Blo 1638018 7872893 := bstep (se 3 (by rfl) ⟨1476167, by rfl⟩ : syracuseStep 7872893 = 2952335) B2952335
theorem B12444029 : Blo 1638018 12444029 := bstep (se 3 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 12444029 = 4666511) B4666511
theorem B2457983 : Blo 1638018 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B1638783 : Blo 1638018 1638783 := bstep (se 1 (by rfl) ⟨1229087, by rfl⟩ : syracuseStep 1638783 = 2458175) B2458175
theorem B4669883 : Blo 1638018 4669883 := bstep (se 1 (by rfl) ⟨3502412, by rfl⟩ : syracuseStep 4669883 = 7004825) B7004825
theorem B2458055 : Blo 1638018 2458055 := bstep (se 1 (by rfl) ⟨1843541, by rfl⟩ : syracuseStep 2458055 = 3687083) B3687083
theorem B1843663 : Blo 1638018 1843663 := bstep (se 1 (by rfl) ⟨1382747, by rfl⟩ : syracuseStep 1843663 = 2765495) B2765495
theorem B1638863 : Blo 1638018 1638863 := bstep (se 1 (by rfl) ⟨1229147, by rfl⟩ : syracuseStep 1638863 = 2458295) B2458295
theorem B1639015 : Blo 1638018 1639015 := bstep (se 1 (by rfl) ⟨1229261, by rfl⟩ : syracuseStep 1639015 = 2458523) B2458523
theorem B2458409 : Blo 1638018 2458409 := bstep (se 2 (by rfl) ⟨921903, by rfl⟩ : syracuseStep 2458409 = 1843807) B1843807
theorem B2458415 : Blo 1638018 2458415 := bstep (se 1 (by rfl) ⟨1843811, by rfl⟩ : syracuseStep 2458415 = 3687623) B3687623
theorem B7873337 : Blo 1638018 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B1639279 : Blo 1638018 1639279 := bstep (se 1 (by rfl) ⟨1229459, by rfl⟩ : syracuseStep 1639279 = 2458919) B2458919
theorem B3687335 : Blo 1638018 3687335 := bstep (se 1 (by rfl) ⟨2765501, by rfl⟩ : syracuseStep 3687335 = 5531003) B5531003
theorem B2458535 : Blo 1638018 2458535 := bstep (se 1 (by rfl) ⟨1843901, by rfl⟩ : syracuseStep 2458535 = 3687803) B3687803
theorem B1639335 : Blo 1638018 1639335 := bstep (se 1 (by rfl) ⟨1229501, by rfl⟩ : syracuseStep 1639335 = 2459003) B2459003
theorem B2073595 : Blo 1638018 2073595 := bstep (se 1 (by rfl) ⟨1555196, by rfl⟩ : syracuseStep 2073595 = 3110393) B3110393
theorem B2458619 : Blo 1638018 2458619 := bstep (se 1 (by rfl) ⟨1843964, by rfl⟩ : syracuseStep 2458619 = 3687929) B3687929
theorem B1639419 : Blo 1638018 1639419 := bstep (se 1 (by rfl) ⟨1229564, by rfl⟩ : syracuseStep 1639419 = 2459129) B2459129
theorem B2458679 : Blo 1638018 2458679 := bstep (se 1 (by rfl) ⟨1844009, by rfl⟩ : syracuseStep 2458679 = 3688019) B3688019
theorem B1639487 : Blo 1638018 1639487 := bstep (se 1 (by rfl) ⟨1229615, by rfl⟩ : syracuseStep 1639487 = 2459231) B2459231
theorem B2458799 : Blo 1638018 2458799 := bstep (se 1 (by rfl) ⟨1844099, by rfl⟩ : syracuseStep 2458799 = 3688199) B3688199
theorem B1639631 : Blo 1638018 1639631 := bstep (se 1 (by rfl) ⟨1229723, by rfl⟩ : syracuseStep 1639631 = 2459447) B2459447
theorem B79758593 : Blo 1638018 79758593 := bstep (se 2 (by rfl) ⟨29909472, by rfl⟩ : syracuseStep 79758593 = 59818945) B59818945
theorem B44860715 : Blo 1638018 44860715 := bstep (se 1 (by rfl) ⟨33645536, by rfl⟩ : syracuseStep 44860715 = 67291073) B67291073
theorem B3499337 : Blo 1638018 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B1844635 : Blo 1638018 1844635 := bstep (se 1 (by rfl) ⟨1383476, by rfl⟩ : syracuseStep 1844635 = 2766953) B2766953
theorem B1639835 : Blo 1638018 1639835 := bstep (se 1 (by rfl) ⟨1229876, by rfl⟩ : syracuseStep 1639835 = 2459753) B2459753
theorem B2459207 : Blo 1638018 2459207 := bstep (se 1 (by rfl) ⟨1844405, by rfl⟩ : syracuseStep 2459207 = 3688811) B3688811
theorem B5531219 : Blo 1638018 5531219 := bstep (se 1 (by rfl) ⟨4148414, by rfl⟩ : syracuseStep 5531219 = 8296829) B8296829
theorem B10495655 : Blo 1638018 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B2459303 : Blo 1638018 2459303 := bstep (se 1 (by rfl) ⟨1844477, by rfl⟩ : syracuseStep 2459303 = 3688955) B3688955
theorem B2459387 : Blo 1638018 2459387 := bstep (se 1 (by rfl) ⟨1844540, by rfl⟩ : syracuseStep 2459387 = 3689081) B3689081
theorem B2459423 : Blo 1638018 2459423 := bstep (se 1 (by rfl) ⟨1844567, by rfl⟩ : syracuseStep 2459423 = 3689135) B3689135
theorem B3688271 : Blo 1638018 3688271 := bstep (se 1 (by rfl) ⟨2766203, by rfl⟩ : syracuseStep 3688271 = 5532407) B5532407
theorem B2459471 : Blo 1638018 2459471 := bstep (se 1 (by rfl) ⟨1844603, by rfl⟩ : syracuseStep 2459471 = 3689207) B3689207
theorem B9332567 : Blo 1638018 9332567 := bstep (se 1 (by rfl) ⟨6999425, by rfl⟩ : syracuseStep 9332567 = 13998851) B13998851
theorem B5531489 : Blo 1638018 5531489 := bstep (se 2 (by rfl) ⟨2074308, by rfl⟩ : syracuseStep 5531489 = 4148617) B4148617
theorem B3688289 : Blo 1638018 3688289 := bstep (se 2 (by rfl) ⟨1383108, by rfl⟩ : syracuseStep 3688289 = 2766217) B2766217
theorem B113502097 : Blo 1638018 113502097 := bstep (se 2 (by rfl) ⟨42563286, by rfl⟩ : syracuseStep 113502097 = 85126573) B85126573
theorem B2074567 : Blo 1638018 2074567 := bstep (se 1 (by rfl) ⟨1555925, by rfl⟩ : syracuseStep 2074567 = 3111851) B3111851
theorem B2459591 : Blo 1638018 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B6219767 : Blo 1638018 6219767 := bstep (se 1 (by rfl) ⟨4664825, by rfl⟩ : syracuseStep 6219767 = 9329651) B9329651
theorem B8857745 : Blo 1638018 8857745 := bstep (se 2 (by rfl) ⟨3321654, by rfl⟩ : syracuseStep 8857745 = 6643309) B6643309
theorem B5253311 : Blo 1638018 5253311 := bstep (se 1 (by rfl) ⟨3939983, by rfl⟩ : syracuseStep 5253311 = 7879967) B7879967
theorem B10643737 : Blo 1638018 10643737 := bstep (se 2 (by rfl) ⟨3991401, by rfl⟩ : syracuseStep 10643737 = 7982803) B7982803
theorem B2459945 : Blo 1638018 2459945 := bstep (se 2 (by rfl) ⟨922479, by rfl⟩ : syracuseStep 2459945 = 1844959) B1844959
theorem B2459951 : Blo 1638018 2459951 := bstep (se 1 (by rfl) ⟨1844963, by rfl⟩ : syracuseStep 2459951 = 3689927) B3689927
theorem B4147595 : Blo 1638018 4147595 := bstep (se 1 (by rfl) ⟨3110696, by rfl⟩ : syracuseStep 4147595 = 6221393) B6221393
theorem B3688865 : Blo 1638018 3688865 := bstep (se 2 (by rfl) ⟨1383324, by rfl⟩ : syracuseStep 3688865 = 2766649) B2766649
theorem B5532191 : Blo 1638018 5532191 := bstep (se 1 (by rfl) ⟨4149143, by rfl⟩ : syracuseStep 5532191 = 8298287) B8298287
theorem B3688991 : Blo 1638018 3688991 := bstep (se 1 (by rfl) ⟨2766743, by rfl⟩ : syracuseStep 3688991 = 5533487) B5533487
theorem B2075483 : Blo 1638018 2075483 := bstep (se 1 (by rfl) ⟨1556612, by rfl⟩ : syracuseStep 2075483 = 3113225) B3113225
theorem B6998879 : Blo 1638018 6998879 := bstep (se 1 (by rfl) ⟨5249159, by rfl⟩ : syracuseStep 6998879 = 10498319) B10498319
theorem B6220739 : Blo 1638018 6220739 := bstep (se 1 (by rfl) ⟨4665554, by rfl⟩ : syracuseStep 6220739 = 9331109) B9331109
theorem B4729903 : Blo 1638018 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B6220921 : Blo 1638018 6220921 := bstep (se 2 (by rfl) ⟨2332845, by rfl⟩ : syracuseStep 6220921 = 4665691) B4665691
theorem B8301689 : Blo 1638018 8301689 := bstep (se 2 (by rfl) ⟨3113133, by rfl⟩ : syracuseStep 8301689 = 6226267) B6226267
theorem B53136719 : Blo 1638018 53136719 := bstep (se 1 (by rfl) ⟨39852539, by rfl⟩ : syracuseStep 53136719 = 79705079) B79705079
theorem B9457033 : Blo 1638018 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B2764199 : Blo 1638018 2764199 := bstep (se 1 (by rfl) ⟨2073149, by rfl⟩ : syracuseStep 2764199 = 4146299) B4146299
theorem B2952617 : Blo 1638018 2952617 := bstep (se 2 (by rfl) ⟨1107231, by rfl⟩ : syracuseStep 2952617 = 2214463) B2214463
theorem B6999479 : Blo 1638018 6999479 := bstep (se 1 (by rfl) ⟨5249609, by rfl⟩ : syracuseStep 6999479 = 10499219) B10499219
theorem B8859127 : Blo 1638018 8859127 := bstep (se 1 (by rfl) ⟨6644345, by rfl⟩ : syracuseStep 8859127 = 13288691) B13288691
theorem B2764361 : Blo 1638018 2764361 := bstep (se 2 (by rfl) ⟨1036635, by rfl⟩ : syracuseStep 2764361 = 2073271) B2073271
theorem B3739243 : Blo 1638018 3739243 := bstep (se 1 (by rfl) ⟨2804432, by rfl⟩ : syracuseStep 3739243 = 5608865) B5608865
theorem B5910353 : Blo 1638018 5910353 := bstep (se 2 (by rfl) ⟨2216382, by rfl⟩ : syracuseStep 5910353 = 4432765) B4432765
theorem B5533595 : Blo 1638018 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B4149215 : Blo 1638018 4149215 := bstep (se 1 (by rfl) ⟨3111911, by rfl⟩ : syracuseStep 4149215 = 6223823) B6223823
theorem B11817181 : Blo 1638018 11817181 := bstep (se 3 (by rfl) ⟨2215721, by rfl⟩ : syracuseStep 11817181 = 4431443) B4431443
theorem B4665737 : Blo 1638018 4665737 := bstep (se 2 (by rfl) ⟨1749651, by rfl⟩ : syracuseStep 4665737 = 3499303) B3499303
theorem B3789305 : Blo 1638018 3789305 := bstep (se 2 (by rfl) ⟨1420989, by rfl⟩ : syracuseStep 3789305 = 2841979) B2841979
theorem B3936851 : Blo 1638018 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B2765407 : Blo 1638018 2765407 := bstep (se 1 (by rfl) ⟨2074055, by rfl⟩ : syracuseStep 2765407 = 4148111) B4148111
theorem B4149863 : Blo 1638018 4149863 := bstep (se 1 (by rfl) ⟨3112397, by rfl⟩ : syracuseStep 4149863 = 6224795) B6224795
theorem B12448403 : Blo 1638018 12448403 := bstep (se 1 (by rfl) ⟨9336302, by rfl⟩ : syracuseStep 12448403 = 18672605) B18672605
theorem B63886097 : Blo 1638018 63886097 := bstep (se 2 (by rfl) ⟨23957286, by rfl⟩ : syracuseStep 63886097 = 47914573) B47914573
theorem B8295209 : Blo 1638018 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B2765819 : Blo 1638018 2765819 := bstep (se 1 (by rfl) ⟨2074364, by rfl⟩ : syracuseStep 2765819 = 4148729) B4148729
theorem B100881413 : Blo 1638018 100881413 := bstep (se 4 (by rfl) ⟨9457632, by rfl⟩ : syracuseStep 100881413 = 18915265) B18915265
theorem B5534729 : Blo 1638018 5534729 := bstep (se 2 (by rfl) ⟨2075523, by rfl⟩ : syracuseStep 5534729 = 4151047) B4151047
theorem B5534783 : Blo 1638018 5534783 := bstep (se 1 (by rfl) ⟨4151087, by rfl⟩ : syracuseStep 5534783 = 8302175) B8302175
theorem B8410193 : Blo 1638018 8410193 := bstep (se 2 (by rfl) ⟨3153822, by rfl⟩ : syracuseStep 8410193 = 6307645) B6307645
theorem B4150379 : Blo 1638018 4150379 := bstep (se 1 (by rfl) ⟨3112784, by rfl⟩ : syracuseStep 4150379 = 6225569) B6225569
theorem B2766251 : Blo 1638018 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B2954873 : Blo 1638018 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B9336485 : Blo 1638018 9336485 := bstep (se 4 (by rfl) ⟨875295, by rfl⟩ : syracuseStep 9336485 = 1750591) B1750591
theorem B78878407 : Blo 1638018 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B22435613 : Blo 1638018 22435613 := bstep (se 3 (by rfl) ⟨4206677, by rfl⟩ : syracuseStep 22435613 = 8413355) B8413355
theorem B3110719 : Blo 1638018 3110719 := bstep (se 1 (by rfl) ⟨2333039, by rfl⟩ : syracuseStep 3110719 = 4666079) B4666079
theorem B19937171 : Blo 1638018 19937171 := bstep (se 1 (by rfl) ⟨14952878, by rfl⟩ : syracuseStep 19937171 = 29905757) B29905757
theorem B51165113 : Blo 1638018 51165113 := bstep (se 2 (by rfl) ⟨19186917, by rfl⟩ : syracuseStep 51165113 = 38373835) B38373835
theorem B2766791 : Blo 1638018 2766791 := bstep (se 1 (by rfl) ⟨2075093, by rfl⟩ : syracuseStep 2766791 = 4150187) B4150187
theorem B79779815 : Blo 1638018 79779815 := bstep (se 1 (by rfl) ⟨59834861, by rfl⟩ : syracuseStep 79779815 = 119669723) B119669723
theorem B15751169 : Blo 1638018 15751169 := bstep (se 2 (by rfl) ⟨5906688, by rfl⟩ : syracuseStep 15751169 = 11813377) B11813377
theorem B2767081 : Blo 1638018 2767081 := bstep (se 2 (by rfl) ⟨1037655, by rfl⟩ : syracuseStep 2767081 = 2075311) B2075311
theorem B13293811 : Blo 1638018 13293811 := bstep (se 1 (by rfl) ⟨9970358, by rfl⟩ : syracuseStep 13293811 = 19940717) B19940717
theorem B25237979 : Blo 1638018 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B2333495 : Blo 1638018 2333495 := bstep (se 1 (by rfl) ⟨1750121, by rfl⟩ : syracuseStep 2333495 = 3500243) B3500243
theorem B5528411 : Blo 1638018 5528411 := bstep (se 1 (by rfl) ⟨4146308, by rfl⟩ : syracuseStep 5528411 = 8292617) B8292617
theorem B151395257 : Blo 1638018 151395257 := bstep (se 2 (by rfl) ⟨56773221, by rfl⟩ : syracuseStep 151395257 = 113546443) B113546443
theorem B9968609 : Blo 1638018 9968609 := bstep (se 2 (by rfl) ⟨3738228, by rfl⟩ : syracuseStep 9968609 = 7476457) B7476457
theorem B102366179 : Blo 1638018 102366179 := bstep (se 1 (by rfl) ⟨76774634, by rfl⟩ : syracuseStep 102366179 = 153549269) B153549269
theorem B13999229 : Blo 1638018 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B9969095 : Blo 1638018 9969095 := bstep (se 1 (by rfl) ⟨7476821, by rfl⟩ : syracuseStep 9969095 = 14953643) B14953643
theorem B2457083 : Blo 1638018 2457083 := bstep (se 1 (by rfl) ⟨1842812, by rfl⟩ : syracuseStep 2457083 = 3685625) B3685625
theorem B3685967 : Blo 1638018 3685967 := bstep (se 1 (by rfl) ⟨2764475, by rfl⟩ : syracuseStep 3685967 = 5528951) B5528951
theorem B5529167 : Blo 1638018 5529167 := bstep (se 1 (by rfl) ⟨4146875, by rfl⟩ : syracuseStep 5529167 = 8293751) B8293751
theorem B2457179 : Blo 1638018 2457179 := bstep (se 1 (by rfl) ⟨1842884, by rfl⟩ : syracuseStep 2457179 = 3685769) B3685769
theorem B2457263 : Blo 1638018 2457263 := bstep (se 1 (by rfl) ⟨1842947, by rfl⟩ : syracuseStep 2457263 = 3685895) B3685895
theorem B5529275 : Blo 1638018 5529275 := bstep (se 1 (by rfl) ⟨4146956, by rfl⟩ : syracuseStep 5529275 = 8293913) B8293913
theorem B2457383 : Blo 1638018 2457383 := bstep (se 1 (by rfl) ⟨1843037, by rfl⟩ : syracuseStep 2457383 = 3686075) B3686075
theorem B37863227 : Blo 1638018 37863227 := bstep (se 1 (by rfl) ⟨28397420, by rfl⟩ : syracuseStep 37863227 = 56794841) B56794841
theorem B1638215 : Blo 1638018 1638215 := bstep (se 1 (by rfl) ⟨1228661, by rfl⟩ : syracuseStep 1638215 = 2457323) B2457323
theorem B1843015 : Blo 1638018 1843015 := bstep (se 1 (by rfl) ⟨1382261, by rfl⟩ : syracuseStep 1843015 = 2764523) B2764523
theorem B2457467 : Blo 1638018 2457467 := bstep (se 1 (by rfl) ⟨1843100, by rfl⟩ : syracuseStep 2457467 = 3686201) B3686201
theorem B7479229 : Blo 1638018 7479229 := bstep (se 3 (by rfl) ⟨1402355, by rfl⟩ : syracuseStep 7479229 = 2804711) B2804711
theorem B1638367 : Blo 1638018 1638367 := bstep (se 1 (by rfl) ⟨1228775, by rfl⟩ : syracuseStep 1638367 = 2457551) B2457551
theorem B6226055 : Blo 1638018 6226055 := bstep (se 1 (by rfl) ⟨4669541, by rfl⟩ : syracuseStep 6226055 = 9339083) B9339083
theorem B2457791 : Blo 1638018 2457791 := bstep (se 1 (by rfl) ⟨1843343, by rfl⟩ : syracuseStep 2457791 = 3686687) B3686687
theorem B1638591 : Blo 1638018 1638591 := bstep (se 1 (by rfl) ⟨1228943, by rfl⟩ : syracuseStep 1638591 = 2457887) B2457887
theorem B1638607 : Blo 1638018 1638607 := bstep (se 1 (by rfl) ⟨1228955, by rfl⟩ : syracuseStep 1638607 = 2457911) B2457911
theorem B1638655 : Blo 1638018 1638655 := bstep (se 1 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 1638655 = 2457983) B2457983
theorem B3113255 : Blo 1638018 3113255 := bstep (se 1 (by rfl) ⟨2334941, by rfl⟩ : syracuseStep 3113255 = 4669883) B4669883
theorem B1638703 : Blo 1638018 1638703 := bstep (se 1 (by rfl) ⟨1229027, by rfl⟩ : syracuseStep 1638703 = 2458055) B2458055
theorem B8298935 : Blo 1638018 8298935 := bstep (se 1 (by rfl) ⟨6224201, by rfl⟩ : syracuseStep 8298935 = 12448403) B12448403
theorem B5530139 : Blo 1638018 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B1638939 : Blo 1638018 1638939 := bstep (se 1 (by rfl) ⟨1229204, by rfl⟩ : syracuseStep 1638939 = 2458409) B2458409
theorem B1638943 : Blo 1638018 1638943 := bstep (se 1 (by rfl) ⟨1229207, by rfl⟩ : syracuseStep 1638943 = 2458415) B2458415
theorem B2458217 : Blo 1638018 2458217 := bstep (se 2 (by rfl) ⟨921831, by rfl⟩ : syracuseStep 2458217 = 1843663) B1843663
theorem B2458223 : Blo 1638018 2458223 := bstep (se 1 (by rfl) ⟨1843667, by rfl⟩ : syracuseStep 2458223 = 3687335) B3687335
theorem B1639023 : Blo 1638018 1639023 := bstep (se 1 (by rfl) ⟨1229267, by rfl⟩ : syracuseStep 1639023 = 2458535) B2458535
theorem B1843879 : Blo 1638018 1843879 := bstep (se 1 (by rfl) ⟨1382909, by rfl⟩ : syracuseStep 1843879 = 2765819) B2765819
theorem B1639079 : Blo 1638018 1639079 := bstep (se 1 (by rfl) ⟨1229309, by rfl⟩ : syracuseStep 1639079 = 2458619) B2458619
theorem B1639119 : Blo 1638018 1639119 := bstep (se 1 (by rfl) ⟨1229339, by rfl⟩ : syracuseStep 1639119 = 2458679) B2458679
theorem B1639199 : Blo 1638018 1639199 := bstep (se 1 (by rfl) ⟨1229399, by rfl⟩ : syracuseStep 1639199 = 2458799) B2458799
theorem B3687209 : Blo 1638018 3687209 := bstep (se 2 (by rfl) ⟨1382703, by rfl⟩ : syracuseStep 3687209 = 2765407) B2765407
theorem B1844167 : Blo 1638018 1844167 := bstep (se 1 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 1844167 = 2766251) B2766251
theorem B1639471 : Blo 1638018 1639471 := bstep (se 1 (by rfl) ⟨1229603, by rfl⟩ : syracuseStep 1639471 = 2459207) B2459207
theorem B3687479 : Blo 1638018 3687479 := bstep (se 1 (by rfl) ⟨2765609, by rfl⟩ : syracuseStep 3687479 = 5531219) B5531219
theorem B7873645 : Blo 1638018 7873645 := bstep (se 3 (by rfl) ⟨1476308, by rfl⟩ : syracuseStep 7873645 = 2952617) B2952617
theorem B6997103 : Blo 1638018 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B1639535 : Blo 1638018 1639535 := bstep (se 1 (by rfl) ⟨1229651, by rfl⟩ : syracuseStep 1639535 = 2459303) B2459303
theorem B1639591 : Blo 1638018 1639591 := bstep (se 1 (by rfl) ⟨1229693, by rfl⟩ : syracuseStep 1639591 = 2459387) B2459387
theorem B1639615 : Blo 1638018 1639615 := bstep (se 1 (by rfl) ⟨1229711, by rfl⟩ : syracuseStep 1639615 = 2459423) B2459423
theorem B2458847 : Blo 1638018 2458847 := bstep (se 1 (by rfl) ⟨1844135, by rfl⟩ : syracuseStep 2458847 = 3688271) B3688271
theorem B1639647 : Blo 1638018 1639647 := bstep (se 1 (by rfl) ⟨1229735, by rfl⟩ : syracuseStep 1639647 = 2459471) B2459471
theorem B3687659 : Blo 1638018 3687659 := bstep (se 1 (by rfl) ⟨2765744, by rfl⟩ : syracuseStep 3687659 = 5531489) B5531489
theorem B2458859 : Blo 1638018 2458859 := bstep (se 1 (by rfl) ⟨1844144, by rfl⟩ : syracuseStep 2458859 = 3688289) B3688289
theorem B1844527 : Blo 1638018 1844527 := bstep (se 1 (by rfl) ⟨1383395, by rfl⟩ : syracuseStep 1844527 = 2766791) B2766791
theorem B1639727 : Blo 1638018 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B4146511 : Blo 1638018 4146511 := bstep (se 1 (by rfl) ⟨3109883, by rfl⟩ : syracuseStep 4146511 = 6219767) B6219767
theorem B1639963 : Blo 1638018 1639963 := bstep (se 1 (by rfl) ⟨1229972, by rfl⟩ : syracuseStep 1639963 = 2459945) B2459945
theorem B1639967 : Blo 1638018 1639967 := bstep (se 1 (by rfl) ⟨1229975, by rfl⟩ : syracuseStep 1639967 = 2459951) B2459951
theorem B2459243 : Blo 1638018 2459243 := bstep (se 1 (by rfl) ⟨1844432, by rfl⟩ : syracuseStep 2459243 = 3688865) B3688865
theorem B3688127 : Blo 1638018 3688127 := bstep (se 1 (by rfl) ⟨2766095, by rfl⟩ : syracuseStep 3688127 = 5532191) B5532191
theorem B2459327 : Blo 1638018 2459327 := bstep (se 1 (by rfl) ⟨1844495, by rfl⟩ : syracuseStep 2459327 = 3688991) B3688991
theorem B12609377 : Blo 1638018 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B2459513 : Blo 1638018 2459513 := bstep (se 2 (by rfl) ⟨922317, by rfl⟩ : syracuseStep 2459513 = 1844635) B1844635
theorem B4147159 : Blo 1638018 4147159 := bstep (se 1 (by rfl) ⟨3110369, by rfl⟩ : syracuseStep 4147159 = 6220739) B6220739
theorem B6645739 : Blo 1638018 6645739 := bstep (se 1 (by rfl) ⟨4984304, by rfl⟩ : syracuseStep 6645739 = 9968609) B9968609
theorem B170362925 : Blo 1638018 170362925 := bstep (se 3 (by rfl) ⟨31943048, by rfl⟩ : syracuseStep 170362925 = 63886097) B63886097
theorem B9332819 : Blo 1638018 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B100968605 : Blo 1638018 100968605 := bstep (se 3 (by rfl) ⟨18931613, by rfl⟩ : syracuseStep 100968605 = 37863227) B37863227
theorem B35424479 : Blo 1638018 35424479 := bstep (se 1 (by rfl) ⟨26568359, by rfl⟩ : syracuseStep 35424479 = 53136719) B53136719
theorem B105171209 : Blo 1638018 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B6646063 : Blo 1638018 6646063 := bstep (se 1 (by rfl) ⟨4984547, by rfl⟩ : syracuseStep 6646063 = 9969095) B9969095
theorem B4147625 : Blo 1638018 4147625 := bstep (se 2 (by rfl) ⟨1555359, by rfl⟩ : syracuseStep 4147625 = 3110719) B3110719
theorem B136440301 : Blo 1638018 136440301 := bstep (se 3 (by rfl) ⟨25582556, by rfl⟩ : syracuseStep 136440301 = 51165113) B51165113
theorem B9972305 : Blo 1638018 9972305 := bstep (se 2 (by rfl) ⟨3739614, by rfl⟩ : syracuseStep 9972305 = 7479229) B7479229
theorem B3689063 : Blo 1638018 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B11807495 : Blo 1638018 11807495 := bstep (se 1 (by rfl) ⟨8855621, by rfl⟩ : syracuseStep 11807495 = 17711243) B17711243
theorem B25226149 : Blo 1638018 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B3689441 : Blo 1638018 3689441 := bstep (se 2 (by rfl) ⟨1383540, by rfl⟩ : syracuseStep 3689441 = 2767081) B2767081
theorem B2526203 : Blo 1638018 2526203 := bstep (se 1 (by rfl) ⟨1894652, by rfl⟩ : syracuseStep 2526203 = 3789305) B3789305
theorem B14191649 : Blo 1638018 14191649 := bstep (se 2 (by rfl) ⟨5321868, by rfl⟩ : syracuseStep 14191649 = 10643737) B10643737
theorem B2624567 : Blo 1638018 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B3689819 : Blo 1638018 3689819 := bstep (se 1 (by rfl) ⟨2767364, by rfl⟩ : syracuseStep 3689819 = 5534729) B5534729
theorem B3689855 : Blo 1638018 3689855 := bstep (se 1 (by rfl) ⟨2767391, by rfl⟩ : syracuseStep 3689855 = 5534783) B5534783
theorem B5606795 : Blo 1638018 5606795 := bstep (se 1 (by rfl) ⟨4205096, by rfl⟩ : syracuseStep 5606795 = 8410193) B8410193
theorem B1969915 : Blo 1638018 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B63024965 : Blo 1638018 63024965 := bstep (se 4 (by rfl) ⟨5908590, by rfl⟩ : syracuseStep 63024965 = 11817181) B11817181
theorem B6221711 : Blo 1638018 6221711 := bstep (se 1 (by rfl) ⟨4666283, by rfl⟩ : syracuseStep 6221711 = 9332567) B9332567
theorem B13291447 : Blo 1638018 13291447 := bstep (se 1 (by rfl) ⟨9968585, by rfl⟩ : syracuseStep 13291447 = 19937171) B19937171
theorem B53186543 : Blo 1638018 53186543 := bstep (se 1 (by rfl) ⟨39889907, by rfl⟩ : syracuseStep 53186543 = 79779815) B79779815
theorem B2764793 : Blo 1638018 2764793 := bstep (se 2 (by rfl) ⟨1036797, by rfl⟩ : syracuseStep 2764793 = 2073595) B2073595
theorem B3502207 : Blo 1638018 3502207 := bstep (se 1 (by rfl) ⟨2626655, by rfl⟩ : syracuseStep 3502207 = 5253311) B5253311
theorem B8294561 : Blo 1638018 8294561 := bstep (se 2 (by rfl) ⟨3110460, by rfl⟩ : syracuseStep 8294561 = 6220921) B6220921
theorem B2765063 : Blo 1638018 2765063 := bstep (se 1 (by rfl) ⟨2073797, by rfl⟩ : syracuseStep 2765063 = 4147595) B4147595
theorem B4665919 : Blo 1638018 4665919 := bstep (se 1 (by rfl) ⟨3499439, by rfl⟩ : syracuseStep 4665919 = 6998879) B6998879
theorem B100930171 : Blo 1638018 100930171 := bstep (se 1 (by rfl) ⟨75697628, by rfl⟩ : syracuseStep 100930171 = 151395257) B151395257
theorem B68244119 : Blo 1638018 68244119 := bstep (se 1 (by rfl) ⟨51183089, by rfl⟩ : syracuseStep 68244119 = 102366179) B102366179
theorem B5534459 : Blo 1638018 5534459 := bstep (se 1 (by rfl) ⟨4150844, by rfl⟩ : syracuseStep 5534459 = 8301689) B8301689
theorem B4985657 : Blo 1638018 4985657 := bstep (se 2 (by rfl) ⟨1869621, by rfl⟩ : syracuseStep 4985657 = 3739243) B3739243
theorem B6222653 : Blo 1638018 6222653 := bstep (se 3 (by rfl) ⟨1166747, by rfl⟩ : syracuseStep 6222653 = 2333495) B2333495
theorem B5534621 : Blo 1638018 5534621 := bstep (se 3 (by rfl) ⟨1037741, by rfl⟩ : syracuseStep 5534621 = 2075483) B2075483
theorem B4666319 : Blo 1638018 4666319 := bstep (se 1 (by rfl) ⟨3499739, by rfl⟩ : syracuseStep 4666319 = 6999479) B6999479
theorem B151336129 : Blo 1638018 151336129 := bstep (se 2 (by rfl) ⟨56751048, by rfl⟩ : syracuseStep 151336129 = 113502097) B113502097
theorem B2766089 : Blo 1638018 2766089 := bstep (se 2 (by rfl) ⟨1037283, by rfl⟩ : syracuseStep 2766089 = 2074567) B2074567
theorem B2766143 : Blo 1638018 2766143 := bstep (se 1 (by rfl) ⟨2074607, by rfl⟩ : syracuseStep 2766143 = 4149215) B4149215
theorem B5248595 : Blo 1638018 5248595 := bstep (se 1 (by rfl) ⟨3936446, by rfl⟩ : syracuseStep 5248595 = 7872893) B7872893
theorem B8296019 : Blo 1638018 8296019 := bstep (se 1 (by rfl) ⟨6222014, by rfl⟩ : syracuseStep 8296019 = 12444029) B12444029
theorem B3110491 : Blo 1638018 3110491 := bstep (se 1 (by rfl) ⟨2332868, by rfl⟩ : syracuseStep 3110491 = 4665737) B4665737
theorem B17725081 : Blo 1638018 17725081 := bstep (se 2 (by rfl) ⟨6646905, by rfl⟩ : syracuseStep 17725081 = 13293811) B13293811
theorem B2766575 : Blo 1638018 2766575 := bstep (se 1 (by rfl) ⟨2074931, by rfl⟩ : syracuseStep 2766575 = 4149863) B4149863
theorem B5248891 : Blo 1638018 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B67254275 : Blo 1638018 67254275 := bstep (se 1 (by rfl) ⟨50440706, by rfl⟩ : syracuseStep 67254275 = 100881413) B100881413
theorem B2766919 : Blo 1638018 2766919 := bstep (se 1 (by rfl) ⟨2075189, by rfl⟩ : syracuseStep 2766919 = 4150379) B4150379
theorem B53172395 : Blo 1638018 53172395 := bstep (se 1 (by rfl) ⟨39879296, by rfl⟩ : syracuseStep 53172395 = 79758593) B79758593
theorem B29907143 : Blo 1638018 29907143 := bstep (se 1 (by rfl) ⟨22430357, by rfl⟩ : syracuseStep 29907143 = 44860715) B44860715
theorem B2332891 : Blo 1638018 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B6224323 : Blo 1638018 6224323 := bstep (se 1 (by rfl) ⟨4668242, by rfl⟩ : syracuseStep 6224323 = 9336485) B9336485
theorem B14957075 : Blo 1638018 14957075 := bstep (se 1 (by rfl) ⟨11217806, by rfl⟩ : syracuseStep 14957075 = 22435613) B22435613
theorem B10500779 : Blo 1638018 10500779 := bstep (se 1 (by rfl) ⟨7875584, by rfl⟩ : syracuseStep 10500779 = 15751169) B15751169
theorem B5905163 : Blo 1638018 5905163 := bstep (se 1 (by rfl) ⟨4428872, by rfl⟩ : syracuseStep 5905163 = 8857745) B8857745
theorem B16825319 : Blo 1638018 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B3685607 : Blo 1638018 3685607 := bstep (se 1 (by rfl) ⟨2764205, by rfl⟩ : syracuseStep 3685607 = 5528411) B5528411
theorem B11812169 : Blo 1638018 11812169 := bstep (se 2 (by rfl) ⟨4429563, by rfl⟩ : syracuseStep 11812169 = 8859127) B8859127
theorem B1842799 : Blo 1638018 1842799 := bstep (se 1 (by rfl) ⟨1382099, by rfl⟩ : syracuseStep 1842799 = 2764199) B2764199
theorem B1638055 : Blo 1638018 1638055 := bstep (se 1 (by rfl) ⟨1228541, by rfl⟩ : syracuseStep 1638055 = 2457083) B2457083
theorem B1842907 : Blo 1638018 1842907 := bstep (se 1 (by rfl) ⟨1382180, by rfl⟩ : syracuseStep 1842907 = 2764361) B2764361
theorem B2457311 : Blo 1638018 2457311 := bstep (se 1 (by rfl) ⟨1842983, by rfl⟩ : syracuseStep 2457311 = 3685967) B3685967
theorem B3686111 : Blo 1638018 3686111 := bstep (se 1 (by rfl) ⟨2764583, by rfl⟩ : syracuseStep 3686111 = 5529167) B5529167
theorem B1638119 : Blo 1638018 1638119 := bstep (se 1 (by rfl) ⟨1228589, by rfl⟩ : syracuseStep 1638119 = 2457179) B2457179
theorem B2457353 : Blo 1638018 2457353 := bstep (se 2 (by rfl) ⟨921507, by rfl⟩ : syracuseStep 2457353 = 1843015) B1843015
theorem B1638175 : Blo 1638018 1638175 := bstep (se 1 (by rfl) ⟨1228631, by rfl⟩ : syracuseStep 1638175 = 2457263) B2457263
theorem B3686183 : Blo 1638018 3686183 := bstep (se 1 (by rfl) ⟨2764637, by rfl⟩ : syracuseStep 3686183 = 5529275) B5529275
theorem B1638255 : Blo 1638018 1638255 := bstep (se 1 (by rfl) ⟨1228691, by rfl⟩ : syracuseStep 1638255 = 2457383) B2457383
theorem B3940235 : Blo 1638018 3940235 := bstep (se 1 (by rfl) ⟨2955176, by rfl⟩ : syracuseStep 3940235 = 5910353) B5910353
theorem B1638311 : Blo 1638018 1638311 := bstep (se 1 (by rfl) ⟨1228733, by rfl⟩ : syracuseStep 1638311 = 2457467) B2457467
theorem B5529707 : Blo 1638018 5529707 := bstep (se 1 (by rfl) ⟨4147280, by rfl⟩ : syracuseStep 5529707 = 8294561) B8294561
theorem B1638527 : Blo 1638018 1638527 := bstep (se 1 (by rfl) ⟨1228895, by rfl⟩ : syracuseStep 1638527 = 2457791) B2457791
theorem B1843375 : Blo 1638018 1843375 := bstep (se 1 (by rfl) ⟨1382531, by rfl⟩ : syracuseStep 1843375 = 2765063) B2765063
theorem B3686759 : Blo 1638018 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B1638811 : Blo 1638018 1638811 := bstep (se 1 (by rfl) ⟨1229108, by rfl⟩ : syracuseStep 1638811 = 2458217) B2458217
theorem B1638815 : Blo 1638018 1638815 := bstep (se 1 (by rfl) ⟨1229111, by rfl⟩ : syracuseStep 1638815 = 2458223) B2458223
theorem B2458139 : Blo 1638018 2458139 := bstep (se 1 (by rfl) ⟨1843604, by rfl⟩ : syracuseStep 2458139 = 3687209) B3687209
theorem B8299097 : Blo 1638018 8299097 := bstep (se 2 (by rfl) ⟨3112161, by rfl⟩ : syracuseStep 8299097 = 6224323) B6224323
theorem B181920401 : Blo 1638018 181920401 := bstep (se 2 (by rfl) ⟨68220150, by rfl⟩ : syracuseStep 181920401 = 136440301) B136440301
theorem B18678437 : Blo 1638018 18678437 := bstep (se 4 (by rfl) ⟨1751103, by rfl⟩ : syracuseStep 18678437 = 3502207) B3502207
theorem B2458319 : Blo 1638018 2458319 := bstep (se 1 (by rfl) ⟨1843739, by rfl⟩ : syracuseStep 2458319 = 3687479) B3687479
theorem B1639231 : Blo 1638018 1639231 := bstep (se 1 (by rfl) ⟨1229423, by rfl⟩ : syracuseStep 1639231 = 2458847) B2458847
theorem B2458439 : Blo 1638018 2458439 := bstep (se 1 (by rfl) ⟨1843829, by rfl⟩ : syracuseStep 2458439 = 3687659) B3687659
theorem B1639239 : Blo 1638018 1639239 := bstep (se 1 (by rfl) ⟨1229429, by rfl⟩ : syracuseStep 1639239 = 2458859) B2458859
theorem B1844059 : Blo 1638018 1844059 := bstep (se 1 (by rfl) ⟨1383044, by rfl⟩ : syracuseStep 1844059 = 2766089) B2766089
theorem B1844095 : Blo 1638018 1844095 := bstep (se 1 (by rfl) ⟨1383071, by rfl⟩ : syracuseStep 1844095 = 2766143) B2766143
theorem B2458505 : Blo 1638018 2458505 := bstep (se 2 (by rfl) ⟨921939, by rfl⟩ : syracuseStep 2458505 = 1843879) B1843879
theorem B5530679 : Blo 1638018 5530679 := bstep (se 1 (by rfl) ⟨4148009, by rfl⟩ : syracuseStep 5530679 = 8296019) B8296019
theorem B1639495 : Blo 1638018 1639495 := bstep (se 1 (by rfl) ⟨1229621, by rfl⟩ : syracuseStep 1639495 = 2459243) B2459243
theorem B2458751 : Blo 1638018 2458751 := bstep (se 1 (by rfl) ⟨1844063, by rfl⟩ : syracuseStep 2458751 = 3688127) B3688127
theorem B1639551 : Blo 1638018 1639551 := bstep (se 1 (by rfl) ⟨1229663, by rfl⟩ : syracuseStep 1639551 = 2459327) B2459327
theorem B1844383 : Blo 1638018 1844383 := bstep (se 1 (by rfl) ⟨1383287, by rfl⟩ : syracuseStep 1844383 = 2766575) B2766575
theorem B8406251 : Blo 1638018 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B1639675 : Blo 1638018 1639675 := bstep (se 1 (by rfl) ⟨1229756, by rfl⟩ : syracuseStep 1639675 = 2459513) B2459513
theorem B2458889 : Blo 1638018 2458889 := bstep (se 2 (by rfl) ⟨922083, by rfl⟩ : syracuseStep 2458889 = 1844167) B1844167
theorem B44836183 : Blo 1638018 44836183 := bstep (se 1 (by rfl) ⟨33627137, by rfl⟩ : syracuseStep 44836183 = 67254275) B67254275
theorem B113575283 : Blo 1638018 113575283 := bstep (se 1 (by rfl) ⟨85181462, by rfl⟩ : syracuseStep 113575283 = 170362925) B170362925
theorem B35448263 : Blo 1638018 35448263 := bstep (se 1 (by rfl) ⟨26586197, by rfl⟩ : syracuseStep 35448263 = 53172395) B53172395
theorem B9971383 : Blo 1638018 9971383 := bstep (se 1 (by rfl) ⟨7478537, by rfl⟩ : syracuseStep 9971383 = 14957075) B14957075
theorem B2459369 : Blo 1638018 2459369 := bstep (se 2 (by rfl) ⟨922263, by rfl⟩ : syracuseStep 2459369 = 1844527) B1844527
theorem B2459375 : Blo 1638018 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B2459627 : Blo 1638018 2459627 := bstep (se 1 (by rfl) ⟨1844720, by rfl⟩ : syracuseStep 2459627 = 3689441) B3689441
theorem B11216879 : Blo 1638018 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B4147321 : Blo 1638018 4147321 := bstep (se 2 (by rfl) ⟨1555245, by rfl⟩ : syracuseStep 4147321 = 3110491) B3110491
theorem B7874779 : Blo 1638018 7874779 := bstep (se 1 (by rfl) ⟨5906084, by rfl⟩ : syracuseStep 7874779 = 11812169) B11812169
theorem B2459879 : Blo 1638018 2459879 := bstep (se 1 (by rfl) ⟨1844909, by rfl⟩ : syracuseStep 2459879 = 3689819) B3689819
theorem B2459903 : Blo 1638018 2459903 := bstep (se 1 (by rfl) ⟨1844927, by rfl⟩ : syracuseStep 2459903 = 3689855) B3689855
theorem B3737863 : Blo 1638018 3737863 := bstep (se 1 (by rfl) ⟨2803397, by rfl⟩ : syracuseStep 3737863 = 5606795) B5606795
theorem B6998521 : Blo 1638018 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B17721929 : Blo 1638018 17721929 := bstep (se 2 (by rfl) ⟨6645723, by rfl⟩ : syracuseStep 17721929 = 13291447) B13291447
theorem B4147807 : Blo 1638018 4147807 := bstep (se 1 (by rfl) ⟨3110855, by rfl⟩ : syracuseStep 4147807 = 6221711) B6221711
theorem B6736541 : Blo 1638018 6736541 := bstep (se 3 (by rfl) ⟨1263101, by rfl⟩ : syracuseStep 6736541 = 2526203) B2526203
theorem B35457695 : Blo 1638018 35457695 := bstep (se 1 (by rfl) ⟨26593271, by rfl⟩ : syracuseStep 35457695 = 53186543) B53186543
theorem B3689225 : Blo 1638018 3689225 := bstep (se 2 (by rfl) ⟨1383459, by rfl⟩ : syracuseStep 3689225 = 2766919) B2766919
theorem B6998845 : Blo 1638018 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B5532623 : Blo 1638018 5532623 := bstep (se 1 (by rfl) ⟨4149467, by rfl⟩ : syracuseStep 5532623 = 8298935) B8298935
theorem B3689639 : Blo 1638018 3689639 := bstep (se 1 (by rfl) ⟨2767229, by rfl⟩ : syracuseStep 3689639 = 5534459) B5534459
theorem B4148435 : Blo 1638018 4148435 := bstep (se 1 (by rfl) ⟨3111326, by rfl⟩ : syracuseStep 4148435 = 6222653) B6222653
theorem B3689747 : Blo 1638018 3689747 := bstep (se 1 (by rfl) ⟨2767310, by rfl⟩ : syracuseStep 3689747 = 5534621) B5534621
theorem B4664735 : Blo 1638018 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B6221225 : Blo 1638018 6221225 := bstep (se 2 (by rfl) ⟨2332959, by rfl⟩ : syracuseStep 6221225 = 4665919) B4665919
theorem B8302013 : Blo 1638018 8302013 := bstep (se 3 (by rfl) ⟨1556627, by rfl⟩ : syracuseStep 8302013 = 3113255) B3113255
theorem B134573561 : Blo 1638018 134573561 := bstep (se 2 (by rfl) ⟨50465085, by rfl⟩ : syracuseStep 134573561 = 100930171) B100930171
theorem B6221879 : Blo 1638018 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B10498193 : Blo 1638018 10498193 := bstep (se 2 (by rfl) ⟨3936822, by rfl⟩ : syracuseStep 10498193 = 7873645) B7873645
theorem B13996253 : Blo 1638018 13996253 := bstep (se 3 (by rfl) ⟨2624297, by rfl⟩ : syracuseStep 13996253 = 5248595) B5248595
theorem B201781505 : Blo 1638018 201781505 := bstep (se 2 (by rfl) ⟨75668064, by rfl⟩ : syracuseStep 201781505 = 151336129) B151336129
theorem B2765083 : Blo 1638018 2765083 := bstep (se 1 (by rfl) ⟨2073812, by rfl⟩ : syracuseStep 2765083 = 4147625) B4147625
theorem B6648203 : Blo 1638018 6648203 := bstep (se 1 (by rfl) ⟨4986152, by rfl⟩ : syracuseStep 6648203 = 9972305) B9972305
theorem B7000519 : Blo 1638018 7000519 := bstep (se 1 (by rfl) ⟨5250389, by rfl⟩ : syracuseStep 7000519 = 10500779) B10500779
theorem B3936775 : Blo 1638018 3936775 := bstep (se 1 (by rfl) ⟨2952581, by rfl⟩ : syracuseStep 3936775 = 5905163) B5905163
theorem B2626553 : Blo 1638018 2626553 := bstep (se 2 (by rfl) ⟨984957, by rfl⟩ : syracuseStep 2626553 = 1969915) B1969915
theorem B2626823 : Blo 1638018 2626823 := bstep (se 1 (by rfl) ⟨1970117, by rfl⟩ : syracuseStep 2626823 = 3940235) B3940235
theorem B8860985 : Blo 1638018 8860985 := bstep (se 2 (by rfl) ⟨3322869, by rfl⟩ : syracuseStep 8860985 = 6645739) B6645739
theorem B4150703 : Blo 1638018 4150703 := bstep (se 1 (by rfl) ⟨3113027, by rfl⟩ : syracuseStep 4150703 = 6226055) B6226055
theorem B8861417 : Blo 1638018 8861417 := bstep (se 2 (by rfl) ⟨3323031, by rfl⟩ : syracuseStep 8861417 = 6646063) B6646063
theorem B45496079 : Blo 1638018 45496079 := bstep (se 1 (by rfl) ⟨34122059, by rfl⟩ : syracuseStep 45496079 = 68244119) B68244119
theorem B3323771 : Blo 1638018 3323771 := bstep (se 1 (by rfl) ⟨2492828, by rfl⟩ : syracuseStep 3323771 = 4985657) B4985657
theorem B3110879 : Blo 1638018 3110879 := bstep (se 1 (by rfl) ⟨2333159, by rfl⟩ : syracuseStep 3110879 = 4666319) B4666319
theorem B12442085 : Blo 1638018 12442085 := bstep (se 4 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 12442085 = 2332891) B2332891
theorem B33634865 : Blo 1638018 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B67312403 : Blo 1638018 67312403 := bstep (se 1 (by rfl) ⟨50484302, by rfl⟩ : syracuseStep 67312403 = 100968605) B100968605
theorem B19938095 : Blo 1638018 19938095 := bstep (se 1 (by rfl) ⟨14953571, by rfl⟩ : syracuseStep 19938095 = 29907143) B29907143
theorem B23616319 : Blo 1638018 23616319 := bstep (se 1 (by rfl) ⟨17712239, by rfl⟩ : syracuseStep 23616319 = 35424479) B35424479
theorem B70114139 : Blo 1638018 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B5528681 : Blo 1638018 5528681 := bstep (se 2 (by rfl) ⟨2073255, by rfl⟩ : syracuseStep 5528681 = 4146511) B4146511
theorem B7871663 : Blo 1638018 7871663 := bstep (se 1 (by rfl) ⟨5903747, by rfl⟩ : syracuseStep 7871663 = 11807495) B11807495
theorem B9461099 : Blo 1638018 9461099 := bstep (se 1 (by rfl) ⟨7095824, by rfl⟩ : syracuseStep 9461099 = 14191649) B14191649
theorem B2457065 : Blo 1638018 2457065 := bstep (se 2 (by rfl) ⟨921399, by rfl⟩ : syracuseStep 2457065 = 1842799) B1842799
theorem B2457071 : Blo 1638018 2457071 := bstep (se 1 (by rfl) ⟨1842803, by rfl⟩ : syracuseStep 2457071 = 3685607) B3685607
theorem B23633441 : Blo 1638018 23633441 := bstep (se 2 (by rfl) ⟨8862540, by rfl⟩ : syracuseStep 23633441 = 17725081) B17725081
theorem B2457209 : Blo 1638018 2457209 := bstep (se 2 (by rfl) ⟨921453, by rfl⟩ : syracuseStep 2457209 = 1842907) B1842907
theorem B1638207 : Blo 1638018 1638207 := bstep (se 1 (by rfl) ⟨1228655, by rfl⟩ : syracuseStep 1638207 = 2457311) B2457311
theorem B2457407 : Blo 1638018 2457407 := bstep (se 1 (by rfl) ⟨1843055, by rfl⟩ : syracuseStep 2457407 = 3686111) B3686111
theorem B1638235 : Blo 1638018 1638235 := bstep (se 1 (by rfl) ⟨1228676, by rfl⟩ : syracuseStep 1638235 = 2457353) B2457353
theorem B2457455 : Blo 1638018 2457455 := bstep (se 1 (by rfl) ⟨1843091, by rfl⟩ : syracuseStep 2457455 = 3686183) B3686183
theorem B42016643 : Blo 1638018 42016643 := bstep (se 1 (by rfl) ⟨31512482, by rfl⟩ : syracuseStep 42016643 = 63024965) B63024965
theorem B5529545 : Blo 1638018 5529545 := bstep (se 2 (by rfl) ⟨2073579, by rfl⟩ : syracuseStep 5529545 = 4147159) B4147159
theorem B1843195 : Blo 1638018 1843195 := bstep (se 1 (by rfl) ⟨1382396, by rfl⟩ : syracuseStep 1843195 = 2764793) B2764793
theorem B3686471 : Blo 1638018 3686471 := bstep (se 1 (by rfl) ⟨2764853, by rfl⟩ : syracuseStep 3686471 = 5529707) B5529707
theorem B9330835 : Blo 1638018 9330835 := bstep (se 1 (by rfl) ⟨6998126, by rfl⟩ : syracuseStep 9330835 = 13996253) B13996253
theorem B5529761 : Blo 1638018 5529761 := bstep (se 2 (by rfl) ⟨2073660, by rfl⟩ : syracuseStep 5529761 = 4147321) B4147321
theorem B134521003 : Blo 1638018 134521003 := bstep (se 1 (by rfl) ⟨100890752, by rfl⟩ : syracuseStep 134521003 = 201781505) B201781505
theorem B2457833 : Blo 1638018 2457833 := bstep (se 2 (by rfl) ⟨921687, by rfl⟩ : syracuseStep 2457833 = 1843375) B1843375
theorem B2457839 : Blo 1638018 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B1638759 : Blo 1638018 1638759 := bstep (se 1 (by rfl) ⟨1229069, by rfl⟩ : syracuseStep 1638759 = 2458139) B2458139
theorem B3686777 : Blo 1638018 3686777 := bstep (se 2 (by rfl) ⟨1382541, by rfl⟩ : syracuseStep 3686777 = 2765083) B2765083
theorem B12452291 : Blo 1638018 12452291 := bstep (se 1 (by rfl) ⟨9339218, by rfl⟩ : syracuseStep 12452291 = 18678437) B18678437
theorem B1638879 : Blo 1638018 1638879 := bstep (se 1 (by rfl) ⟨1229159, by rfl⟩ : syracuseStep 1638879 = 2458319) B2458319
theorem B1638959 : Blo 1638018 1638959 := bstep (se 1 (by rfl) ⟨1229219, by rfl⟩ : syracuseStep 1638959 = 2458439) B2458439
theorem B1639003 : Blo 1638018 1639003 := bstep (se 1 (by rfl) ⟨1229252, by rfl⟩ : syracuseStep 1639003 = 2458505) B2458505
theorem B9331361 : Blo 1638018 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B3687119 : Blo 1638018 3687119 := bstep (se 1 (by rfl) ⟨2765339, by rfl⟩ : syracuseStep 3687119 = 5530679) B5530679
theorem B1639167 : Blo 1638018 1639167 := bstep (se 1 (by rfl) ⟨1229375, by rfl⟩ : syracuseStep 1639167 = 2458751) B2458751
theorem B5530409 : Blo 1638018 5530409 := bstep (se 2 (by rfl) ⟨2073903, by rfl⟩ : syracuseStep 5530409 = 4147807) B4147807
theorem B5604167 : Blo 1638018 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B1639259 : Blo 1638018 1639259 := bstep (se 1 (by rfl) ⟨1229444, by rfl⟩ : syracuseStep 1639259 = 2458889) B2458889
theorem B5907323 : Blo 1638018 5907323 := bstep (se 1 (by rfl) ⟨4430492, by rfl⟩ : syracuseStep 5907323 = 8860985) B8860985
theorem B17728541 : Blo 1638018 17728541 := bstep (se 3 (by rfl) ⟨3324101, by rfl⟩ : syracuseStep 17728541 = 6648203) B6648203
theorem B9331793 : Blo 1638018 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B2458745 : Blo 1638018 2458745 := bstep (se 2 (by rfl) ⟨922029, by rfl⟩ : syracuseStep 2458745 = 1844059) B1844059
theorem B5907611 : Blo 1638018 5907611 := bstep (se 1 (by rfl) ⟨4430708, by rfl⟩ : syracuseStep 5907611 = 8861417) B8861417
theorem B1639579 : Blo 1638018 1639579 := bstep (se 1 (by rfl) ⟨1229684, by rfl⟩ : syracuseStep 1639579 = 2459369) B2459369
theorem B1639583 : Blo 1638018 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B2458793 : Blo 1638018 2458793 := bstep (se 2 (by rfl) ⟨922047, by rfl⟩ : syracuseStep 2458793 = 1844095) B1844095
theorem B2073919 : Blo 1638018 2073919 := bstep (se 1 (by rfl) ⟨1555439, by rfl⟩ : syracuseStep 2073919 = 3110879) B3110879
theorem B1639751 : Blo 1638018 1639751 := bstep (se 1 (by rfl) ⟨1229813, by rfl⟩ : syracuseStep 1639751 = 2459627) B2459627
theorem B1639919 : Blo 1638018 1639919 := bstep (se 1 (by rfl) ⟨1229939, by rfl⟩ : syracuseStep 1639919 = 2459879) B2459879
theorem B1639935 : Blo 1638018 1639935 := bstep (se 1 (by rfl) ⟨1229951, by rfl⟩ : syracuseStep 1639935 = 2459903) B2459903
theorem B2459177 : Blo 1638018 2459177 := bstep (se 2 (by rfl) ⟨922191, by rfl⟩ : syracuseStep 2459177 = 1844383) B1844383
theorem B22423243 : Blo 1638018 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B11814619 : Blo 1638018 11814619 := bstep (se 1 (by rfl) ⟨8860964, by rfl⟩ : syracuseStep 11814619 = 17721929) B17721929
theorem B2459483 : Blo 1638018 2459483 := bstep (se 1 (by rfl) ⟨1844612, by rfl⟩ : syracuseStep 2459483 = 3689225) B3689225
theorem B3688415 : Blo 1638018 3688415 := bstep (se 1 (by rfl) ⟨2766311, by rfl⟩ : syracuseStep 3688415 = 5532623) B5532623
theorem B2459759 : Blo 1638018 2459759 := bstep (se 1 (by rfl) ⟨1844819, by rfl⟩ : syracuseStep 2459759 = 3689639) B3689639
theorem B2459831 : Blo 1638018 2459831 := bstep (se 1 (by rfl) ⟨1844873, by rfl⟩ : syracuseStep 2459831 = 3689747) B3689747
theorem B4147483 : Blo 1638018 4147483 := bstep (se 1 (by rfl) ⟨3110612, by rfl⟩ : syracuseStep 4147483 = 6221225) B6221225
theorem B15755627 : Blo 1638018 15755627 := bstep (se 1 (by rfl) ⟨11816720, by rfl⟩ : syracuseStep 15755627 = 23633441) B23633441
theorem B28011095 : Blo 1638018 28011095 := bstep (se 1 (by rfl) ⟨21008321, by rfl⟩ : syracuseStep 28011095 = 42016643) B42016643
theorem B4147919 : Blo 1638018 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B6998795 : Blo 1638018 6998795 := bstep (se 1 (by rfl) ⟨5249096, by rfl⟩ : syracuseStep 6998795 = 10498193) B10498193
theorem B4983817 : Blo 1638018 4983817 := bstep (se 2 (by rfl) ⟨1868931, by rfl⟩ : syracuseStep 4983817 = 3737863) B3737863
theorem B5532731 : Blo 1638018 5532731 := bstep (se 1 (by rfl) ⟨4149548, by rfl⟩ : syracuseStep 5532731 = 8299097) B8299097
theorem B9334025 : Blo 1638018 9334025 := bstep (se 2 (by rfl) ⟨3500259, by rfl⟩ : syracuseStep 9334025 = 7000519) B7000519
theorem B30330719 : Blo 1638018 30330719 := bstep (se 1 (by rfl) ⟨22748039, by rfl⟩ : syracuseStep 30330719 = 45496079) B45496079
theorem B2215847 : Blo 1638018 2215847 := bstep (se 1 (by rfl) ⟨1661885, by rfl⟩ : syracuseStep 2215847 = 3323771) B3323771
theorem B8294723 : Blo 1638018 8294723 := bstep (se 1 (by rfl) ⟨6221042, by rfl⟩ : syracuseStep 8294723 = 12442085) B12442085
theorem B23638463 : Blo 1638018 23638463 := bstep (se 1 (by rfl) ⟨17728847, by rfl⟩ : syracuseStep 23638463 = 35457695) B35457695
theorem B59781577 : Blo 1638018 59781577 := bstep (se 2 (by rfl) ⟨22418091, by rfl⟩ : syracuseStep 59781577 = 44836183) B44836183
theorem B13292063 : Blo 1638018 13292063 := bstep (se 1 (by rfl) ⟨9969047, by rfl⟩ : syracuseStep 13292063 = 19938095) B19938095
theorem B5247775 : Blo 1638018 5247775 := bstep (se 1 (by rfl) ⟨3935831, by rfl⟩ : syracuseStep 5247775 = 7871663) B7871663
theorem B2765623 : Blo 1638018 2765623 := bstep (se 1 (by rfl) ⟨2074217, by rfl⟩ : syracuseStep 2765623 = 4148435) B4148435
theorem B3109823 : Blo 1638018 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B5534675 : Blo 1638018 5534675 := bstep (se 1 (by rfl) ⟨4151006, by rfl⟩ : syracuseStep 5534675 = 8302013) B8302013
theorem B89715707 : Blo 1638018 89715707 := bstep (se 1 (by rfl) ⟨67286780, by rfl⟩ : syracuseStep 89715707 = 134573561) B134573561
theorem B10499705 : Blo 1638018 10499705 := bstep (se 2 (by rfl) ⟨3937389, by rfl⟩ : syracuseStep 10499705 = 7874779) B7874779
theorem B121280267 : Blo 1638018 121280267 := bstep (se 1 (by rfl) ⟨90960200, by rfl⟩ : syracuseStep 121280267 = 181920401) B181920401
theorem B5249033 : Blo 1638018 5249033 := bstep (se 2 (by rfl) ⟨1968387, by rfl⟩ : syracuseStep 5249033 = 3936775) B3936775
theorem B1751215 : Blo 1638018 1751215 := bstep (se 1 (by rfl) ⟨1313411, by rfl⟩ : syracuseStep 1751215 = 2626823) B2626823
theorem B75716855 : Blo 1638018 75716855 := bstep (se 1 (by rfl) ⟨56787641, by rfl⟩ : syracuseStep 75716855 = 113575283) B113575283
theorem B2767135 : Blo 1638018 2767135 := bstep (se 1 (by rfl) ⟨2075351, by rfl⟩ : syracuseStep 2767135 = 4150703) B4150703
theorem B23632175 : Blo 1638018 23632175 := bstep (se 1 (by rfl) ⟨17724131, by rfl⟩ : syracuseStep 23632175 = 35448263) B35448263
theorem B31488425 : Blo 1638018 31488425 := bstep (se 2 (by rfl) ⟨11808159, by rfl⟩ : syracuseStep 31488425 = 23616319) B23616319
theorem B7477919 : Blo 1638018 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B17964109 : Blo 1638018 17964109 := bstep (se 3 (by rfl) ⟨3368270, by rfl⟩ : syracuseStep 17964109 = 6736541) B6736541
theorem B44874935 : Blo 1638018 44874935 := bstep (se 1 (by rfl) ⟨33656201, by rfl⟩ : syracuseStep 44874935 = 67312403) B67312403
theorem B46742759 : Blo 1638018 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B3685787 : Blo 1638018 3685787 := bstep (se 1 (by rfl) ⟨2764340, by rfl⟩ : syracuseStep 3685787 = 5528681) B5528681
theorem B6307399 : Blo 1638018 6307399 := bstep (se 1 (by rfl) ⟨4730549, by rfl⟩ : syracuseStep 6307399 = 9461099) B9461099
theorem B13295177 : Blo 1638018 13295177 := bstep (se 2 (by rfl) ⟨4985691, by rfl⟩ : syracuseStep 13295177 = 9971383) B9971383
theorem B1638043 : Blo 1638018 1638043 := bstep (se 1 (by rfl) ⟨1228532, by rfl⟩ : syracuseStep 1638043 = 2457065) B2457065
theorem B1638047 : Blo 1638018 1638047 := bstep (se 1 (by rfl) ⟨1228535, by rfl⟩ : syracuseStep 1638047 = 2457071) B2457071
theorem B1638139 : Blo 1638018 1638139 := bstep (se 1 (by rfl) ⟨1228604, by rfl⟩ : syracuseStep 1638139 = 2457209) B2457209
theorem B1638271 : Blo 1638018 1638271 := bstep (se 1 (by rfl) ⟨1228703, by rfl⟩ : syracuseStep 1638271 = 2457407) B2457407
theorem B1638303 : Blo 1638018 1638303 := bstep (se 1 (by rfl) ⟨1228727, by rfl⟩ : syracuseStep 1638303 = 2457455) B2457455
theorem B3686363 : Blo 1638018 3686363 := bstep (se 1 (by rfl) ⟨2764772, by rfl⟩ : syracuseStep 3686363 = 5529545) B5529545
theorem B7004141 : Blo 1638018 7004141 := bstep (se 3 (by rfl) ⟨1313276, by rfl⟩ : syracuseStep 7004141 = 2626553) B2626553
theorem B2457593 : Blo 1638018 2457593 := bstep (se 2 (by rfl) ⟨921597, by rfl⟩ : syracuseStep 2457593 = 1843195) B1843195
theorem B2457647 : Blo 1638018 2457647 := bstep (se 1 (by rfl) ⟨1843235, by rfl⟩ : syracuseStep 2457647 = 3686471) B3686471
theorem B3686507 : Blo 1638018 3686507 := bstep (se 1 (by rfl) ⟨2764880, by rfl⟩ : syracuseStep 3686507 = 5529761) B5529761
theorem B1638555 : Blo 1638018 1638555 := bstep (se 1 (by rfl) ⟨1228916, by rfl⟩ : syracuseStep 1638555 = 2457833) B2457833
theorem B1638559 : Blo 1638018 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B5529815 : Blo 1638018 5529815 := bstep (se 1 (by rfl) ⟨4147361, by rfl⟩ : syracuseStep 5529815 = 8294723) B8294723
theorem B2334953 : Blo 1638018 2334953 := bstep (se 2 (by rfl) ⟨875607, by rfl⟩ : syracuseStep 2334953 = 1751215) B1751215
theorem B2457851 : Blo 1638018 2457851 := bstep (se 1 (by rfl) ⟨1843388, by rfl⟩ : syracuseStep 2457851 = 3686777) B3686777
theorem B5529977 : Blo 1638018 5529977 := bstep (se 2 (by rfl) ⟨2073741, by rfl⟩ : syracuseStep 5529977 = 4147483) B4147483
theorem B15753629 : Blo 1638018 15753629 := bstep (se 3 (by rfl) ⟨2953805, by rfl⟩ : syracuseStep 15753629 = 5907611) B5907611
theorem B2458079 : Blo 1638018 2458079 := bstep (se 1 (by rfl) ⟨1843559, by rfl⟩ : syracuseStep 2458079 = 3687119) B3687119
theorem B3686939 : Blo 1638018 3686939 := bstep (se 1 (by rfl) ⟨2765204, by rfl⟩ : syracuseStep 3686939 = 5530409) B5530409
theorem B3736111 : Blo 1638018 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B79708769 : Blo 1638018 79708769 := bstep (se 2 (by rfl) ⟨29890788, by rfl⟩ : syracuseStep 79708769 = 59781577) B59781577
theorem B2073215 : Blo 1638018 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B59810471 : Blo 1638018 59810471 := bstep (se 1 (by rfl) ⟨44857853, by rfl⟩ : syracuseStep 59810471 = 89715707) B89715707
theorem B1639163 : Blo 1638018 1639163 := bstep (se 1 (by rfl) ⟨1229372, by rfl⟩ : syracuseStep 1639163 = 2458745) B2458745
theorem B1639195 : Blo 1638018 1639195 := bstep (se 1 (by rfl) ⟨1229396, by rfl⟩ : syracuseStep 1639195 = 2458793) B2458793
theorem B1639451 : Blo 1638018 1639451 := bstep (se 1 (by rfl) ⟨1229588, by rfl⟩ : syracuseStep 1639451 = 2459177) B2459177
theorem B6997033 : Blo 1638018 6997033 := bstep (se 2 (by rfl) ⟨2623887, by rfl⟩ : syracuseStep 6997033 = 5247775) B5247775
theorem B3687497 : Blo 1638018 3687497 := bstep (se 2 (by rfl) ⟨1382811, by rfl⟩ : syracuseStep 3687497 = 2765623) B2765623
theorem B1639655 : Blo 1638018 1639655 := bstep (se 1 (by rfl) ⟨1229741, by rfl⟩ : syracuseStep 1639655 = 2459483) B2459483
theorem B2458943 : Blo 1638018 2458943 := bstep (se 1 (by rfl) ⟨1844207, by rfl⟩ : syracuseStep 2458943 = 3688415) B3688415
theorem B3499355 : Blo 1638018 3499355 := bstep (se 1 (by rfl) ⟨2624516, by rfl⟩ : syracuseStep 3499355 = 5249033) B5249033
theorem B6645089 : Blo 1638018 6645089 := bstep (se 2 (by rfl) ⟨2491908, by rfl⟩ : syracuseStep 6645089 = 4983817) B4983817
theorem B1639839 : Blo 1638018 1639839 := bstep (se 1 (by rfl) ⟨1229879, by rfl⟩ : syracuseStep 1639839 = 2459759) B2459759
theorem B1639887 : Blo 1638018 1639887 := bstep (se 1 (by rfl) ⟨1229915, by rfl⟩ : syracuseStep 1639887 = 2459831) B2459831
theorem B15754783 : Blo 1638018 15754783 := bstep (se 1 (by rfl) ⟨11816087, by rfl⟩ : syracuseStep 15754783 = 23632175) B23632175
theorem B10503751 : Blo 1638018 10503751 := bstep (se 1 (by rfl) ⟨7877813, by rfl⟩ : syracuseStep 10503751 = 15755627) B15755627
theorem B1638395 : Blo 1638018 1638395 := bstep (se 1 (by rfl) ⟨1228796, by rfl⟩ : syracuseStep 1638395 = 2457593) B2457593
theorem B3688487 : Blo 1638018 3688487 := bstep (se 1 (by rfl) ⟨2766365, by rfl⟩ : syracuseStep 3688487 = 5532731) B5532731
theorem B5908925 : Blo 1638018 5908925 := bstep (se 3 (by rfl) ⟨1107923, by rfl⟩ : syracuseStep 5908925 = 2215847) B2215847
theorem B20220479 : Blo 1638018 20220479 := bstep (se 1 (by rfl) ⟨15165359, by rfl⟩ : syracuseStep 20220479 = 30330719) B30330719
theorem B8301527 : Blo 1638018 8301527 := bstep (se 1 (by rfl) ⟨6226145, by rfl⟩ : syracuseStep 8301527 = 12452291) B12452291
theorem B3689513 : Blo 1638018 3689513 := bstep (se 2 (by rfl) ⟨1383567, by rfl⟩ : syracuseStep 3689513 = 2767135) B2767135
theorem B6220907 : Blo 1638018 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B3689783 : Blo 1638018 3689783 := bstep (se 1 (by rfl) ⟨2767337, by rfl⟩ : syracuseStep 3689783 = 5534675) B5534675
theorem B6221195 : Blo 1638018 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B6999803 : Blo 1638018 6999803 := bstep (se 1 (by rfl) ⟨5249852, by rfl⟩ : syracuseStep 6999803 = 10499705) B10499705
theorem B20992283 : Blo 1638018 20992283 := bstep (se 1 (by rfl) ⟨15744212, by rfl⟩ : syracuseStep 20992283 = 31488425) B31488425
theorem B18674063 : Blo 1638018 18674063 := bstep (se 1 (by rfl) ⟨14005547, by rfl⟩ : syracuseStep 18674063 = 28011095) B28011095
theorem B2765225 : Blo 1638018 2765225 := bstep (se 2 (by rfl) ⟨1036959, by rfl⟩ : syracuseStep 2765225 = 2073919) B2073919
theorem B4985279 : Blo 1638018 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B2765279 : Blo 1638018 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B4665863 : Blo 1638018 4665863 := bstep (se 1 (by rfl) ⟨3499397, by rfl⟩ : syracuseStep 4665863 = 6998795) B6998795
theorem B8409865 : Blo 1638018 8409865 := bstep (se 2 (by rfl) ⟨3153699, by rfl⟩ : syracuseStep 8409865 = 6307399) B6307399
theorem B6222683 : Blo 1638018 6222683 := bstep (se 1 (by rfl) ⟨4667012, by rfl⟩ : syracuseStep 6222683 = 9334025) B9334025
theorem B29897657 : Blo 1638018 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B12441113 : Blo 1638018 12441113 := bstep (se 2 (by rfl) ⟨4665417, by rfl⟩ : syracuseStep 12441113 = 9330835) B9330835
theorem B15758975 : Blo 1638018 15758975 := bstep (se 1 (by rfl) ⟨11819231, by rfl⟩ : syracuseStep 15758975 = 23638463) B23638463
theorem B8861375 : Blo 1638018 8861375 := bstep (se 1 (by rfl) ⟨6646031, by rfl⟩ : syracuseStep 8861375 = 13292063) B13292063
theorem B3938215 : Blo 1638018 3938215 := bstep (se 1 (by rfl) ⟨2953661, by rfl⟩ : syracuseStep 3938215 = 5907323) B5907323
theorem B11819027 : Blo 1638018 11819027 := bstep (se 1 (by rfl) ⟨8864270, by rfl⟩ : syracuseStep 11819027 = 17728541) B17728541
theorem B717445349 : Blo 1638018 717445349 := bstep (se 4 (by rfl) ⟨67260501, by rfl⟩ : syracuseStep 717445349 = 134521003) B134521003
theorem B80853511 : Blo 1638018 80853511 := bstep (se 1 (by rfl) ⟨60640133, by rfl⟩ : syracuseStep 80853511 = 121280267) B121280267
theorem B23952145 : Blo 1638018 23952145 := bstep (se 2 (by rfl) ⟨8982054, by rfl⟩ : syracuseStep 23952145 = 17964109) B17964109
theorem B50477903 : Blo 1638018 50477903 := bstep (se 1 (by rfl) ⟨37858427, by rfl⟩ : syracuseStep 50477903 = 75716855) B75716855
theorem B29916623 : Blo 1638018 29916623 := bstep (se 1 (by rfl) ⟨22437467, by rfl⟩ : syracuseStep 29916623 = 44874935) B44874935
theorem B31161839 : Blo 1638018 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B2457191 : Blo 1638018 2457191 := bstep (se 1 (by rfl) ⟨1842893, by rfl⟩ : syracuseStep 2457191 = 3685787) B3685787
theorem B15752825 : Blo 1638018 15752825 := bstep (se 2 (by rfl) ⟨5907309, by rfl⟩ : syracuseStep 15752825 = 11814619) B11814619
theorem B8863451 : Blo 1638018 8863451 := bstep (se 1 (by rfl) ⟨6647588, by rfl⟩ : syracuseStep 8863451 = 13295177) B13295177
theorem B2457575 : Blo 1638018 2457575 := bstep (se 1 (by rfl) ⟨1843181, by rfl⟩ : syracuseStep 2457575 = 3686363) B3686363
theorem B4669427 : Blo 1638018 4669427 := bstep (se 1 (by rfl) ⟨3502070, by rfl⟩ : syracuseStep 4669427 = 7004141) B7004141
theorem B1638431 : Blo 1638018 1638431 := bstep (se 1 (by rfl) ⟨1228823, by rfl⟩ : syracuseStep 1638431 = 2457647) B2457647
theorem B2457671 : Blo 1638018 2457671 := bstep (se 1 (by rfl) ⟨1843253, by rfl⟩ : syracuseStep 2457671 = 3686507) B3686507
theorem B3686543 : Blo 1638018 3686543 := bstep (se 1 (by rfl) ⟨2764907, by rfl⟩ : syracuseStep 3686543 = 5529815) B5529815
theorem B1638567 : Blo 1638018 1638567 := bstep (se 1 (by rfl) ⟨1228925, by rfl⟩ : syracuseStep 1638567 = 2457851) B2457851
theorem B3686651 : Blo 1638018 3686651 := bstep (se 1 (by rfl) ⟨2764988, by rfl⟩ : syracuseStep 3686651 = 5529977) B5529977
theorem B10502419 : Blo 1638018 10502419 := bstep (se 1 (by rfl) ⟨7876814, by rfl⟩ : syracuseStep 10502419 = 15753629) B15753629
theorem B1843483 : Blo 1638018 1843483 := bstep (se 1 (by rfl) ⟨1382612, by rfl⟩ : syracuseStep 1843483 = 2765225) B2765225
theorem B1843519 : Blo 1638018 1843519 := bstep (se 1 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 1843519 = 2765279) B2765279
theorem B1638719 : Blo 1638018 1638719 := bstep (se 1 (by rfl) ⟨1229039, by rfl⟩ : syracuseStep 1638719 = 2458079) B2458079
theorem B2457959 : Blo 1638018 2457959 := bstep (se 1 (by rfl) ⟨1843469, by rfl⟩ : syracuseStep 2457959 = 3686939) B3686939
theorem B6226541 : Blo 1638018 6226541 := bstep (se 3 (by rfl) ⟨1167476, by rfl⟩ : syracuseStep 6226541 = 2334953) B2334953
theorem B19931771 : Blo 1638018 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B2458331 : Blo 1638018 2458331 := bstep (se 1 (by rfl) ⟨1843748, by rfl⟩ : syracuseStep 2458331 = 3687497) B3687497
theorem B4981481 : Blo 1638018 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B1639295 : Blo 1638018 1639295 := bstep (se 1 (by rfl) ⟨1229471, by rfl⟩ : syracuseStep 1639295 = 2458943) B2458943
theorem B5907583 : Blo 1638018 5907583 := bstep (se 1 (by rfl) ⟨4430687, by rfl⟩ : syracuseStep 5907583 = 8861375) B8861375
theorem B2458991 : Blo 1638018 2458991 := bstep (se 1 (by rfl) ⟨1844243, by rfl⟩ : syracuseStep 2458991 = 3688487) B3688487
theorem B2459675 : Blo 1638018 2459675 := bstep (se 1 (by rfl) ⟨1844756, by rfl⟩ : syracuseStep 2459675 = 3689513) B3689513
theorem B21006377 : Blo 1638018 21006377 := bstep (se 2 (by rfl) ⟨7877391, by rfl⟩ : syracuseStep 21006377 = 15754783) B15754783
theorem B4147271 : Blo 1638018 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B2459855 : Blo 1638018 2459855 := bstep (se 1 (by rfl) ⟨1844891, by rfl⟩ : syracuseStep 2459855 = 3689783) B3689783
theorem B4147463 : Blo 1638018 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B5908967 : Blo 1638018 5908967 := bstep (se 1 (by rfl) ⟨4431725, by rfl⟩ : syracuseStep 5908967 = 8863451) B8863451
theorem B13994855 : Blo 1638018 13994855 := bstep (se 1 (by rfl) ⟨10496141, by rfl⟩ : syracuseStep 13994855 = 20992283) B20992283
theorem B39873647 : Blo 1638018 39873647 := bstep (se 1 (by rfl) ⟨29905235, by rfl⟩ : syracuseStep 39873647 = 59810471) B59810471
theorem B4148455 : Blo 1638018 4148455 := bstep (se 1 (by rfl) ⟨3111341, by rfl⟩ : syracuseStep 4148455 = 6222683) B6222683
theorem B8294075 : Blo 1638018 8294075 := bstep (se 1 (by rfl) ⟨6220556, by rfl⟩ : syracuseStep 8294075 = 12441113) B12441113
theorem B31936193 : Blo 1638018 31936193 := bstep (se 2 (by rfl) ⟨11976072, by rfl⟩ : syracuseStep 31936193 = 23952145) B23952145
theorem B10505983 : Blo 1638018 10505983 := bstep (se 1 (by rfl) ⟨7879487, by rfl⟩ : syracuseStep 10505983 = 15758975) B15758975
theorem B13480319 : Blo 1638018 13480319 := bstep (se 1 (by rfl) ⟨10110239, by rfl⟩ : syracuseStep 13480319 = 20220479) B20220479
theorem B5534351 : Blo 1638018 5534351 := bstep (se 1 (by rfl) ⟨4150763, by rfl⟩ : syracuseStep 5534351 = 8301527) B8301527
theorem B14005001 : Blo 1638018 14005001 := bstep (se 2 (by rfl) ⟨5251875, by rfl⟩ : syracuseStep 14005001 = 10503751) B10503751
theorem B19944415 : Blo 1638018 19944415 := bstep (se 1 (by rfl) ⟨14958311, by rfl⟩ : syracuseStep 19944415 = 29916623) B29916623
theorem B4666535 : Blo 1638018 4666535 := bstep (se 1 (by rfl) ⟨3499901, by rfl⟩ : syracuseStep 4666535 = 6999803) B6999803
theorem B12449375 : Blo 1638018 12449375 := bstep (se 1 (by rfl) ⟨9337031, by rfl⟩ : syracuseStep 12449375 = 18674063) B18674063
theorem B3323519 : Blo 1638018 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B3110575 : Blo 1638018 3110575 := bstep (se 1 (by rfl) ⟨2332931, by rfl⟩ : syracuseStep 3110575 = 4665863) B4665863
theorem B53139179 : Blo 1638018 53139179 := bstep (se 1 (by rfl) ⟨39854384, by rfl⟩ : syracuseStep 53139179 = 79708769) B79708769
theorem B107804681 : Blo 1638018 107804681 := bstep (se 2 (by rfl) ⟨40426755, by rfl⟩ : syracuseStep 107804681 = 80853511) B80853511
theorem B2332903 : Blo 1638018 2332903 := bstep (se 1 (by rfl) ⟨1749677, by rfl⟩ : syracuseStep 2332903 = 3499355) B3499355
theorem B4430059 : Blo 1638018 4430059 := bstep (se 1 (by rfl) ⟨3322544, by rfl⟩ : syracuseStep 4430059 = 6645089) B6645089
theorem B11213153 : Blo 1638018 11213153 := bstep (se 2 (by rfl) ⟨4204932, by rfl⟩ : syracuseStep 11213153 = 8409865) B8409865
theorem B83098237 : Blo 1638018 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B7879351 : Blo 1638018 7879351 := bstep (se 1 (by rfl) ⟨5909513, by rfl⟩ : syracuseStep 7879351 = 11819027) B11819027
theorem B9329377 : Blo 1638018 9329377 := bstep (se 2 (by rfl) ⟨3498516, by rfl⟩ : syracuseStep 9329377 = 6997033) B6997033
theorem B478296899 : Blo 1638018 478296899 := bstep (se 1 (by rfl) ⟨358722674, by rfl⟩ : syracuseStep 478296899 = 717445349) B717445349
theorem B3939283 : Blo 1638018 3939283 := bstep (se 1 (by rfl) ⟨2954462, by rfl⟩ : syracuseStep 3939283 = 5908925) B5908925
theorem B5528573 : Blo 1638018 5528573 := bstep (se 3 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 5528573 = 2073215) B2073215
theorem B33651935 : Blo 1638018 33651935 := bstep (se 1 (by rfl) ⟨25238951, by rfl⟩ : syracuseStep 33651935 = 50477903) B50477903
theorem B1638127 : Blo 1638018 1638127 := bstep (se 1 (by rfl) ⟨1228595, by rfl⟩ : syracuseStep 1638127 = 2457191) B2457191
theorem B10501883 : Blo 1638018 10501883 := bstep (se 1 (by rfl) ⟨7876412, by rfl⟩ : syracuseStep 10501883 = 15752825) B15752825
theorem B5250953 : Blo 1638018 5250953 := bstep (se 2 (by rfl) ⟨1969107, by rfl⟩ : syracuseStep 5250953 = 3938215) B3938215
theorem B12451805 : Blo 1638018 12451805 := bstep (se 3 (by rfl) ⟨2334713, by rfl⟩ : syracuseStep 12451805 = 4669427) B4669427
theorem B1638383 : Blo 1638018 1638383 := bstep (se 1 (by rfl) ⟨1228787, by rfl⟩ : syracuseStep 1638383 = 2457575) B2457575
theorem B1638447 : Blo 1638018 1638447 := bstep (se 1 (by rfl) ⟨1228835, by rfl⟩ : syracuseStep 1638447 = 2457671) B2457671
theorem B2457695 : Blo 1638018 2457695 := bstep (se 1 (by rfl) ⟨1843271, by rfl⟩ : syracuseStep 2457695 = 3686543) B3686543
theorem B2457767 : Blo 1638018 2457767 := bstep (se 1 (by rfl) ⟨1843325, by rfl⟩ : syracuseStep 2457767 = 3686651) B3686651
theorem B1638639 : Blo 1638018 1638639 := bstep (se 1 (by rfl) ⟨1228979, by rfl⟩ : syracuseStep 1638639 = 2457959) B2457959
theorem B8986879 : Blo 1638018 8986879 := bstep (se 1 (by rfl) ⟨6740159, by rfl⟩ : syracuseStep 8986879 = 13480319) B13480319
theorem B2457977 : Blo 1638018 2457977 := bstep (se 2 (by rfl) ⟨921741, by rfl⟩ : syracuseStep 2457977 = 1843483) B1843483
theorem B13287847 : Blo 1638018 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B2458025 : Blo 1638018 2458025 := bstep (se 2 (by rfl) ⟨921759, by rfl⟩ : syracuseStep 2458025 = 1843519) B1843519
theorem B1638887 : Blo 1638018 1638887 := bstep (se 1 (by rfl) ⟨1229165, by rfl⟩ : syracuseStep 1638887 = 2458331) B2458331
theorem B110797649 : Blo 1638018 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B1639327 : Blo 1638018 1639327 := bstep (se 1 (by rfl) ⟨1229495, by rfl⟩ : syracuseStep 1639327 = 2458991) B2458991
theorem B8299583 : Blo 1638018 8299583 := bstep (se 1 (by rfl) ⟨6224687, by rfl⟩ : syracuseStep 8299583 = 12449375) B12449375
theorem B23626981 : Blo 1638018 23626981 := bstep (se 4 (by rfl) ⟨2215029, by rfl⟩ : syracuseStep 23626981 = 4430059) B4430059
theorem B5252377 : Blo 1638018 5252377 := bstep (se 2 (by rfl) ⟨1969641, by rfl⟩ : syracuseStep 5252377 = 3939283) B3939283
theorem B26592553 : Blo 1638018 26592553 := bstep (se 2 (by rfl) ⟨9972207, by rfl⟩ : syracuseStep 26592553 = 19944415) B19944415
theorem B71869787 : Blo 1638018 71869787 := bstep (se 1 (by rfl) ⟨53902340, by rfl⟩ : syracuseStep 71869787 = 107804681) B107804681
theorem B1639783 : Blo 1638018 1639783 := bstep (se 1 (by rfl) ⟨1229837, by rfl⟩ : syracuseStep 1639783 = 2459675) B2459675
theorem B1639903 : Blo 1638018 1639903 := bstep (se 1 (by rfl) ⟨1229927, by rfl⟩ : syracuseStep 1639903 = 2459855) B2459855
theorem B5531273 : Blo 1638018 5531273 := bstep (se 2 (by rfl) ⟨2074227, by rfl⟩ : syracuseStep 5531273 = 4148455) B4148455
theorem B4147433 : Blo 1638018 4147433 := bstep (se 2 (by rfl) ⟨1555287, by rfl⟩ : syracuseStep 4147433 = 3110575) B3110575
theorem B14002541 : Blo 1638018 14002541 := bstep (se 3 (by rfl) ⟨2625476, by rfl⟩ : syracuseStep 14002541 = 5250953) B5250953
theorem B53135797 : Blo 1638018 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B8301203 : Blo 1638018 8301203 := bstep (se 1 (by rfl) ⟨6225902, by rfl⟩ : syracuseStep 8301203 = 12451805) B12451805
theorem B14003225 : Blo 1638018 14003225 := bstep (se 2 (by rfl) ⟨5251209, by rfl⟩ : syracuseStep 14003225 = 10502419) B10502419
theorem B3689567 : Blo 1638018 3689567 := bstep (se 1 (by rfl) ⟨2767175, by rfl⟩ : syracuseStep 3689567 = 5534351) B5534351
theorem B10505801 : Blo 1638018 10505801 := bstep (se 2 (by rfl) ⟨3939675, by rfl⟩ : syracuseStep 10505801 = 7879351) B7879351
theorem B12439169 : Blo 1638018 12439169 := bstep (se 2 (by rfl) ⟨4664688, by rfl⟩ : syracuseStep 12439169 = 9329377) B9329377
theorem B2215679 : Blo 1638018 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B35426119 : Blo 1638018 35426119 := bstep (se 1 (by rfl) ⟨26569589, by rfl⟩ : syracuseStep 35426119 = 53139179) B53139179
theorem B14004251 : Blo 1638018 14004251 := bstep (se 1 (by rfl) ⟨10503188, by rfl⟩ : syracuseStep 14004251 = 21006377) B21006377
theorem B2764847 : Blo 1638018 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B7876777 : Blo 1638018 7876777 := bstep (se 2 (by rfl) ⟨2953791, by rfl⟩ : syracuseStep 7876777 = 5907583) B5907583
theorem B2764975 : Blo 1638018 2764975 := bstep (se 1 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 2764975 = 4147463) B4147463
theorem B7475435 : Blo 1638018 7475435 := bstep (se 1 (by rfl) ⟨5606576, by rfl⟩ : syracuseStep 7475435 = 11213153) B11213153
theorem B22434623 : Blo 1638018 22434623 := bstep (se 1 (by rfl) ⟨16825967, by rfl⟩ : syracuseStep 22434623 = 33651935) B33651935
theorem B7001255 : Blo 1638018 7001255 := bstep (se 1 (by rfl) ⟨5250941, by rfl⟩ : syracuseStep 7001255 = 10501883) B10501883
theorem B3110537 : Blo 1638018 3110537 := bstep (se 2 (by rfl) ⟨1166451, by rfl⟩ : syracuseStep 3110537 = 2332903) B2332903
theorem B4151027 : Blo 1638018 4151027 := bstep (se 1 (by rfl) ⟨3113270, by rfl⟩ : syracuseStep 4151027 = 6226541) B6226541
theorem B9336667 : Blo 1638018 9336667 := bstep (se 1 (by rfl) ⟨7002500, by rfl⟩ : syracuseStep 9336667 = 14005001) B14005001
theorem B3111023 : Blo 1638018 3111023 := bstep (se 1 (by rfl) ⟨2333267, by rfl⟩ : syracuseStep 3111023 = 4666535) B4666535
theorem B3939311 : Blo 1638018 3939311 := bstep (se 1 (by rfl) ⟨2954483, by rfl⟩ : syracuseStep 3939311 = 5908967) B5908967
theorem B318864599 : Blo 1638018 318864599 := bstep (se 1 (by rfl) ⟨239148449, by rfl⟩ : syracuseStep 318864599 = 478296899) B478296899
theorem B9329903 : Blo 1638018 9329903 := bstep (se 1 (by rfl) ⟨6997427, by rfl⟩ : syracuseStep 9329903 = 13994855) B13994855
theorem B3685715 : Blo 1638018 3685715 := bstep (se 1 (by rfl) ⟨2764286, by rfl⟩ : syracuseStep 3685715 = 5528573) B5528573
theorem B26582431 : Blo 1638018 26582431 := bstep (se 1 (by rfl) ⟨19936823, by rfl⟩ : syracuseStep 26582431 = 39873647) B39873647
theorem B14007977 : Blo 1638018 14007977 := bstep (se 2 (by rfl) ⟨5252991, by rfl⟩ : syracuseStep 14007977 = 10505983) B10505983
theorem B5529383 : Blo 1638018 5529383 := bstep (se 1 (by rfl) ⟨4147037, by rfl⟩ : syracuseStep 5529383 = 8294075) B8294075
theorem B21290795 : Blo 1638018 21290795 := bstep (se 1 (by rfl) ⟨15968096, by rfl⟩ : syracuseStep 21290795 = 31936193) B31936193
theorem B1843231 : Blo 1638018 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B1638463 : Blo 1638018 1638463 := bstep (se 1 (by rfl) ⟨1228847, by rfl⟩ : syracuseStep 1638463 = 2457695) B2457695
theorem B1638511 : Blo 1638018 1638511 := bstep (se 1 (by rfl) ⟨1228883, by rfl⟩ : syracuseStep 1638511 = 2457767) B2457767
theorem B10502369 : Blo 1638018 10502369 := bstep (se 2 (by rfl) ⟨3938388, by rfl⟩ : syracuseStep 10502369 = 7876777) B7876777
theorem B3686633 : Blo 1638018 3686633 := bstep (se 2 (by rfl) ⟨1382487, by rfl⟩ : syracuseStep 3686633 = 2764975) B2764975
theorem B1638651 : Blo 1638018 1638651 := bstep (se 1 (by rfl) ⟨1228988, by rfl⟩ : syracuseStep 1638651 = 2457977) B2457977
theorem B1638683 : Blo 1638018 1638683 := bstep (se 1 (by rfl) ⟨1229012, by rfl⟩ : syracuseStep 1638683 = 2458025) B2458025
theorem B2073691 : Blo 1638018 2073691 := bstep (se 1 (by rfl) ⟨1555268, by rfl⟩ : syracuseStep 2073691 = 3110537) B3110537
theorem B3687515 : Blo 1638018 3687515 := bstep (se 1 (by rfl) ⟨2765636, by rfl⟩ : syracuseStep 3687515 = 5531273) B5531273
theorem B2074015 : Blo 1638018 2074015 := bstep (se 1 (by rfl) ⟨1555511, by rfl⟩ : syracuseStep 2074015 = 3111023) B3111023
theorem B35456737 : Blo 1638018 35456737 := bstep (se 2 (by rfl) ⟨13296276, by rfl⟩ : syracuseStep 35456737 = 26592553) B26592553
theorem B5908477 : Blo 1638018 5908477 := bstep (se 3 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 5908477 = 2215679) B2215679
theorem B2459711 : Blo 1638018 2459711 := bstep (se 1 (by rfl) ⟨1844783, by rfl⟩ : syracuseStep 2459711 = 3689567) B3689567
theorem B212576399 : Blo 1638018 212576399 := bstep (se 1 (by rfl) ⟨159432299, by rfl⟩ : syracuseStep 212576399 = 318864599) B318864599
theorem B6219935 : Blo 1638018 6219935 := bstep (se 1 (by rfl) ⟨4664951, by rfl⟩ : syracuseStep 6219935 = 9329903) B9329903
theorem B8292779 : Blo 1638018 8292779 := bstep (se 1 (by rfl) ⟨6219584, by rfl⟩ : syracuseStep 8292779 = 12439169) B12439169
theorem B10504829 : Blo 1638018 10504829 := bstep (se 3 (by rfl) ⟨1969655, by rfl⟩ : syracuseStep 10504829 = 3939311) B3939311
theorem B4983623 : Blo 1638018 4983623 := bstep (se 1 (by rfl) ⟨3737717, by rfl⟩ : syracuseStep 4983623 = 7475435) B7475435
theorem B70847729 : Blo 1638018 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B5533055 : Blo 1638018 5533055 := bstep (se 1 (by rfl) ⟨4149791, by rfl⟩ : syracuseStep 5533055 = 8299583) B8299583
theorem B2764955 : Blo 1638018 2764955 := bstep (se 1 (by rfl) ⟨2073716, by rfl⟩ : syracuseStep 2764955 = 4147433) B4147433
theorem B9335027 : Blo 1638018 9335027 := bstep (se 1 (by rfl) ⟨7001270, by rfl⟩ : syracuseStep 9335027 = 14002541) B14002541
theorem B31502641 : Blo 1638018 31502641 := bstep (se 2 (by rfl) ⟨11813490, by rfl⟩ : syracuseStep 31502641 = 23626981) B23626981
theorem B5534135 : Blo 1638018 5534135 := bstep (se 1 (by rfl) ⟨4150601, by rfl⟩ : syracuseStep 5534135 = 8301203) B8301203
theorem B35443241 : Blo 1638018 35443241 := bstep (se 2 (by rfl) ⟨13291215, by rfl⟩ : syracuseStep 35443241 = 26582431) B26582431
theorem B9335483 : Blo 1638018 9335483 := bstep (se 1 (by rfl) ⟨7001612, by rfl⟩ : syracuseStep 9335483 = 14003225) B14003225
theorem B12448889 : Blo 1638018 12448889 := bstep (se 2 (by rfl) ⟨4668333, by rfl⟩ : syracuseStep 12448889 = 9336667) B9336667
theorem B14193863 : Blo 1638018 14193863 := bstep (se 1 (by rfl) ⟨10645397, by rfl⟩ : syracuseStep 14193863 = 21290795) B21290795
theorem B9336167 : Blo 1638018 9336167 := bstep (se 1 (by rfl) ⟨7002125, by rfl⟩ : syracuseStep 9336167 = 14004251) B14004251
theorem B11982505 : Blo 1638018 11982505 := bstep (se 2 (by rfl) ⟨4493439, by rfl⟩ : syracuseStep 11982505 = 8986879) B8986879
theorem B14956415 : Blo 1638018 14956415 := bstep (se 1 (by rfl) ⟨11217311, by rfl⟩ : syracuseStep 14956415 = 22434623) B22434623
theorem B17717129 : Blo 1638018 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B73865099 : Blo 1638018 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B4667503 : Blo 1638018 4667503 := bstep (se 1 (by rfl) ⟨3500627, by rfl⟩ : syracuseStep 4667503 = 7001255) B7001255
theorem B47913191 : Blo 1638018 47913191 := bstep (se 1 (by rfl) ⟨35934893, by rfl⟩ : syracuseStep 47913191 = 71869787) B71869787
theorem B2767351 : Blo 1638018 2767351 := bstep (se 1 (by rfl) ⟨2075513, by rfl⟩ : syracuseStep 2767351 = 4151027) B4151027
theorem B28015469 : Blo 1638018 28015469 := bstep (se 3 (by rfl) ⟨5252900, by rfl⟩ : syracuseStep 28015469 = 10505801) B10505801
theorem B7003169 : Blo 1638018 7003169 := bstep (se 2 (by rfl) ⟨2626188, by rfl⟩ : syracuseStep 7003169 = 5252377) B5252377
theorem B2457143 : Blo 1638018 2457143 := bstep (se 1 (by rfl) ⟨1842857, by rfl⟩ : syracuseStep 2457143 = 3685715) B3685715
theorem B47234825 : Blo 1638018 47234825 := bstep (se 2 (by rfl) ⟨17713059, by rfl⟩ : syracuseStep 47234825 = 35426119) B35426119
theorem B9338651 : Blo 1638018 9338651 := bstep (se 1 (by rfl) ⟨7003988, by rfl⟩ : syracuseStep 9338651 = 14007977) B14007977
theorem B3686255 : Blo 1638018 3686255 := bstep (se 1 (by rfl) ⟨2764691, by rfl⟩ : syracuseStep 3686255 = 5529383) B5529383
theorem B2457641 : Blo 1638018 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B1843303 : Blo 1638018 1843303 := bstep (se 1 (by rfl) ⟨1382477, by rfl⟩ : syracuseStep 1843303 = 2764955) B2764955
theorem B2457755 : Blo 1638018 2457755 := bstep (se 1 (by rfl) ⟨1843316, by rfl⟩ : syracuseStep 2457755 = 3686633) B3686633
theorem B2458343 : Blo 1638018 2458343 := bstep (se 1 (by rfl) ⟨1843757, by rfl⟩ : syracuseStep 2458343 = 3687515) B3687515
theorem B8299259 : Blo 1638018 8299259 := bstep (se 1 (by rfl) ⟨6224444, by rfl⟩ : syracuseStep 8299259 = 12448889) B12448889
theorem B9462575 : Blo 1638018 9462575 := bstep (se 1 (by rfl) ⟨7096931, by rfl⟩ : syracuseStep 9462575 = 14193863) B14193863
theorem B9970943 : Blo 1638018 9970943 := bstep (se 1 (by rfl) ⟨7478207, by rfl⟩ : syracuseStep 9970943 = 14956415) B14956415
theorem B49243399 : Blo 1638018 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B1639807 : Blo 1638018 1639807 := bstep (se 1 (by rfl) ⟨1229855, by rfl⟩ : syracuseStep 1639807 = 2459711) B2459711
theorem B4146623 : Blo 1638018 4146623 := bstep (se 1 (by rfl) ⟨3109967, by rfl⟩ : syracuseStep 4146623 = 6219935) B6219935
theorem B31942127 : Blo 1638018 31942127 := bstep (se 1 (by rfl) ⟨23956595, by rfl⟩ : syracuseStep 31942127 = 47913191) B47913191
theorem B15976673 : Blo 1638018 15976673 := bstep (se 2 (by rfl) ⟨5991252, by rfl⟩ : syracuseStep 15976673 = 11982505) B11982505
theorem B3688703 : Blo 1638018 3688703 := bstep (se 1 (by rfl) ⟨2766527, by rfl⟩ : syracuseStep 3688703 = 5533055) B5533055
theorem B3689423 : Blo 1638018 3689423 := bstep (se 1 (by rfl) ⟨2767067, by rfl⟩ : syracuseStep 3689423 = 5534135) B5534135
theorem B23628827 : Blo 1638018 23628827 := bstep (se 1 (by rfl) ⟨17721620, by rfl⟩ : syracuseStep 23628827 = 35443241) B35443241
theorem B42003521 : Blo 1638018 42003521 := bstep (se 2 (by rfl) ⟨15751320, by rfl⟩ : syracuseStep 42003521 = 31502641) B31502641
theorem B3689801 : Blo 1638018 3689801 := bstep (se 2 (by rfl) ⟨1383675, by rfl⟩ : syracuseStep 3689801 = 2767351) B2767351
theorem B141717599 : Blo 1638018 141717599 := bstep (se 1 (by rfl) ⟨106288199, by rfl⟩ : syracuseStep 141717599 = 212576399) B212576399
theorem B2764921 : Blo 1638018 2764921 := bstep (se 2 (by rfl) ⟨1036845, by rfl⟩ : syracuseStep 2764921 = 2073691) B2073691
theorem B2765353 : Blo 1638018 2765353 := bstep (se 2 (by rfl) ⟨1037007, by rfl⟩ : syracuseStep 2765353 = 2074015) B2074015
theorem B3322415 : Blo 1638018 3322415 := bstep (se 1 (by rfl) ⟨2491811, by rfl⟩ : syracuseStep 3322415 = 4983623) B4983623
theorem B47231819 : Blo 1638018 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B7877969 : Blo 1638018 7877969 := bstep (se 2 (by rfl) ⟨2954238, by rfl⟩ : syracuseStep 7877969 = 5908477) B5908477
theorem B6223337 : Blo 1638018 6223337 := bstep (se 2 (by rfl) ⟨2333751, by rfl⟩ : syracuseStep 6223337 = 4667503) B4667503
theorem B7001579 : Blo 1638018 7001579 := bstep (se 1 (by rfl) ⟨5251184, by rfl⟩ : syracuseStep 7001579 = 10502369) B10502369
theorem B6223351 : Blo 1638018 6223351 := bstep (se 1 (by rfl) ⟨4667513, by rfl⟩ : syracuseStep 6223351 = 9335027) B9335027
theorem B6223655 : Blo 1638018 6223655 := bstep (se 1 (by rfl) ⟨4667741, by rfl⟩ : syracuseStep 6223655 = 9335483) B9335483
theorem B6224111 : Blo 1638018 6224111 := bstep (se 1 (by rfl) ⟨4668083, by rfl⟩ : syracuseStep 6224111 = 9336167) B9336167
theorem B11811419 : Blo 1638018 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B5528519 : Blo 1638018 5528519 := bstep (se 1 (by rfl) ⟨4146389, by rfl⟩ : syracuseStep 5528519 = 8292779) B8292779
theorem B7003219 : Blo 1638018 7003219 := bstep (se 1 (by rfl) ⟨5252414, by rfl⟩ : syracuseStep 7003219 = 10504829) B10504829
theorem B18676979 : Blo 1638018 18676979 := bstep (se 1 (by rfl) ⟨14007734, by rfl⟩ : syracuseStep 18676979 = 28015469) B28015469
theorem B4668779 : Blo 1638018 4668779 := bstep (se 1 (by rfl) ⟨3501584, by rfl⟩ : syracuseStep 4668779 = 7003169) B7003169
theorem B47275649 : Blo 1638018 47275649 := bstep (se 2 (by rfl) ⟨17728368, by rfl⟩ : syracuseStep 47275649 = 35456737) B35456737
theorem B1638095 : Blo 1638018 1638095 := bstep (se 1 (by rfl) ⟨1228571, by rfl⟩ : syracuseStep 1638095 = 2457143) B2457143
theorem B31489883 : Blo 1638018 31489883 := bstep (se 1 (by rfl) ⟨23617412, by rfl⟩ : syracuseStep 31489883 = 47234825) B47234825
theorem B6225767 : Blo 1638018 6225767 := bstep (se 1 (by rfl) ⟨4669325, by rfl⟩ : syracuseStep 6225767 = 9338651) B9338651
theorem B2457503 : Blo 1638018 2457503 := bstep (se 1 (by rfl) ⟨1843127, by rfl⟩ : syracuseStep 2457503 = 3686255) B3686255
theorem B1638427 : Blo 1638018 1638427 := bstep (se 1 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 1638427 = 2457641) B2457641
theorem B94478399 : Blo 1638018 94478399 := bstep (se 1 (by rfl) ⟨70858799, by rfl⟩ : syracuseStep 94478399 = 141717599) B141717599
theorem B1638503 : Blo 1638018 1638503 := bstep (se 1 (by rfl) ⟨1228877, by rfl⟩ : syracuseStep 1638503 = 2457755) B2457755
theorem B2457737 : Blo 1638018 2457737 := bstep (se 2 (by rfl) ⟨921651, by rfl⟩ : syracuseStep 2457737 = 1843303) B1843303
theorem B1050525845 : Blo 1638018 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B3686561 : Blo 1638018 3686561 := bstep (se 2 (by rfl) ⟨1382460, by rfl⟩ : syracuseStep 3686561 = 2764921) B2764921
theorem B1638895 : Blo 1638018 1638895 := bstep (se 1 (by rfl) ⟨1229171, by rfl⟩ : syracuseStep 1638895 = 2458343) B2458343
theorem B6308383 : Blo 1638018 6308383 := bstep (se 1 (by rfl) ⟨4731287, by rfl⟩ : syracuseStep 6308383 = 9462575) B9462575
theorem B3687137 : Blo 1638018 3687137 := bstep (se 2 (by rfl) ⟨1382676, by rfl⟩ : syracuseStep 3687137 = 2765353) B2765353
theorem B5251979 : Blo 1638018 5251979 := bstep (se 1 (by rfl) ⟨3938984, by rfl⟩ : syracuseStep 5251979 = 7877969) B7877969
theorem B10651115 : Blo 1638018 10651115 := bstep (se 1 (by rfl) ⟨7988336, by rfl⟩ : syracuseStep 10651115 = 15976673) B15976673
theorem B2459135 : Blo 1638018 2459135 := bstep (se 1 (by rfl) ⟨1844351, by rfl⟩ : syracuseStep 2459135 = 3688703) B3688703
theorem B7874279 : Blo 1638018 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B2459615 : Blo 1638018 2459615 := bstep (se 1 (by rfl) ⟨1844711, by rfl⟩ : syracuseStep 2459615 = 3689423) B3689423
theorem B28002347 : Blo 1638018 28002347 := bstep (se 1 (by rfl) ⟨21001760, by rfl⟩ : syracuseStep 28002347 = 42003521) B42003521
theorem B2459867 : Blo 1638018 2459867 := bstep (se 1 (by rfl) ⟨1844900, by rfl⟩ : syracuseStep 2459867 = 3689801) B3689801
theorem B31517099 : Blo 1638018 31517099 := bstep (se 1 (by rfl) ⟨23637824, by rfl⟩ : syracuseStep 31517099 = 47275649) B47275649
theorem B5532839 : Blo 1638018 5532839 := bstep (se 1 (by rfl) ⟨4149629, by rfl⟩ : syracuseStep 5532839 = 8299259) B8299259
theorem B2764415 : Blo 1638018 2764415 := bstep (se 1 (by rfl) ⟨2073311, by rfl⟩ : syracuseStep 2764415 = 4146623) B4146623
theorem B4148891 : Blo 1638018 4148891 := bstep (se 1 (by rfl) ⟨3111668, by rfl⟩ : syracuseStep 4148891 = 6223337) B6223337
theorem B21294751 : Blo 1638018 21294751 := bstep (se 1 (by rfl) ⟨15971063, by rfl⟩ : syracuseStep 21294751 = 31942127) B31942127
theorem B4149103 : Blo 1638018 4149103 := bstep (se 1 (by rfl) ⟨3111827, by rfl⟩ : syracuseStep 4149103 = 6223655) B6223655
theorem B8859773 : Blo 1638018 8859773 := bstep (se 3 (by rfl) ⟨1661207, by rfl⟩ : syracuseStep 8859773 = 3322415) B3322415
theorem B4149407 : Blo 1638018 4149407 := bstep (se 1 (by rfl) ⟨3112055, by rfl⟩ : syracuseStep 4149407 = 6224111) B6224111
theorem B20993255 : Blo 1638018 20993255 := bstep (se 1 (by rfl) ⟨15744941, by rfl⟩ : syracuseStep 20993255 = 31489883) B31489883
theorem B4150511 : Blo 1638018 4150511 := bstep (se 1 (by rfl) ⟨3112883, by rfl⟩ : syracuseStep 4150511 = 6225767) B6225767
theorem B31487879 : Blo 1638018 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B26589181 : Blo 1638018 26589181 := bstep (se 3 (by rfl) ⟨4985471, by rfl⟩ : syracuseStep 26589181 = 9970943) B9970943
theorem B4667719 : Blo 1638018 4667719 := bstep (se 1 (by rfl) ⟨3500789, by rfl⟩ : syracuseStep 4667719 = 7001579) B7001579
theorem B9337625 : Blo 1638018 9337625 := bstep (se 2 (by rfl) ⟨3501609, by rfl⟩ : syracuseStep 9337625 = 7003219) B7003219
theorem B3685679 : Blo 1638018 3685679 := bstep (se 1 (by rfl) ⟨2764259, by rfl⟩ : syracuseStep 3685679 = 5528519) B5528519
theorem B8297801 : Blo 1638018 8297801 := bstep (se 2 (by rfl) ⟨3111675, by rfl⟩ : syracuseStep 8297801 = 6223351) B6223351
theorem B15752551 : Blo 1638018 15752551 := bstep (se 1 (by rfl) ⟨11814413, by rfl⟩ : syracuseStep 15752551 = 23628827) B23628827
theorem B12451319 : Blo 1638018 12451319 := bstep (se 1 (by rfl) ⟨9338489, by rfl⟩ : syracuseStep 12451319 = 18676979) B18676979
theorem B3112519 : Blo 1638018 3112519 := bstep (se 1 (by rfl) ⟨2334389, by rfl⟩ : syracuseStep 3112519 = 4668779) B4668779
theorem B1638335 : Blo 1638018 1638335 := bstep (se 1 (by rfl) ⟨1228751, by rfl⟩ : syracuseStep 1638335 = 2457503) B2457503
theorem B5906515 : Blo 1638018 5906515 := bstep (se 1 (by rfl) ⟨4429886, by rfl⟩ : syracuseStep 5906515 = 8859773) B8859773
theorem B1638491 : Blo 1638018 1638491 := bstep (se 1 (by rfl) ⟨1228868, by rfl⟩ : syracuseStep 1638491 = 2457737) B2457737
theorem B700350563 : Blo 1638018 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B2457707 : Blo 1638018 2457707 := bstep (se 1 (by rfl) ⟨1843280, by rfl⟩ : syracuseStep 2457707 = 3686561) B3686561
theorem B2458091 : Blo 1638018 2458091 := bstep (se 1 (by rfl) ⟨1843568, by rfl⟩ : syracuseStep 2458091 = 3687137) B3687137
theorem B1639423 : Blo 1638018 1639423 := bstep (se 1 (by rfl) ⟨1229567, by rfl⟩ : syracuseStep 1639423 = 2459135) B2459135
theorem B1639743 : Blo 1638018 1639743 := bstep (se 1 (by rfl) ⟨1229807, by rfl⟩ : syracuseStep 1639743 = 2459615) B2459615
theorem B1639911 : Blo 1638018 1639911 := bstep (se 1 (by rfl) ⟨1229933, by rfl⟩ : syracuseStep 1639911 = 2459867) B2459867
theorem B3688559 : Blo 1638018 3688559 := bstep (se 1 (by rfl) ⟨2766419, by rfl⟩ : syracuseStep 3688559 = 5532839) B5532839
theorem B5531867 : Blo 1638018 5531867 := bstep (se 1 (by rfl) ⟨4148900, by rfl⟩ : syracuseStep 5531867 = 8297801) B8297801
theorem B8300879 : Blo 1638018 8300879 := bstep (se 1 (by rfl) ⟨6225659, by rfl⟩ : syracuseStep 8300879 = 12451319) B12451319
theorem B5532137 : Blo 1638018 5532137 := bstep (se 2 (by rfl) ⟨2074551, by rfl⟩ : syracuseStep 5532137 = 4149103) B4149103
theorem B3501319 : Blo 1638018 3501319 := bstep (se 1 (by rfl) ⟨2625989, by rfl⟩ : syracuseStep 3501319 = 5251979) B5251979
theorem B13995503 : Blo 1638018 13995503 := bstep (se 1 (by rfl) ⟨10496627, by rfl⟩ : syracuseStep 13995503 = 20993255) B20993255
theorem B20991919 : Blo 1638018 20991919 := bstep (se 1 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 20991919 = 31487879) B31487879
theorem B4150025 : Blo 1638018 4150025 := bstep (se 2 (by rfl) ⟨1556259, by rfl⟩ : syracuseStep 4150025 = 3112519) B3112519
theorem B2765927 : Blo 1638018 2765927 := bstep (se 1 (by rfl) ⟨2074445, by rfl⟩ : syracuseStep 2765927 = 4148891) B4148891
theorem B35452241 : Blo 1638018 35452241 := bstep (se 2 (by rfl) ⟨13294590, by rfl⟩ : syracuseStep 35452241 = 26589181) B26589181
theorem B62985599 : Blo 1638018 62985599 := bstep (se 1 (by rfl) ⟨47239199, by rfl⟩ : syracuseStep 62985599 = 94478399) B94478399
theorem B2766271 : Blo 1638018 2766271 := bstep (se 1 (by rfl) ⟨2074703, by rfl⟩ : syracuseStep 2766271 = 4149407) B4149407
theorem B6223625 : Blo 1638018 6223625 := bstep (se 2 (by rfl) ⟨2333859, by rfl⟩ : syracuseStep 6223625 = 4667719) B4667719
theorem B8411177 : Blo 1638018 8411177 := bstep (se 2 (by rfl) ⟨3154191, by rfl⟩ : syracuseStep 8411177 = 6308383) B6308383
theorem B2767007 : Blo 1638018 2767007 := bstep (se 1 (by rfl) ⟨2075255, by rfl⟩ : syracuseStep 2767007 = 4150511) B4150511
theorem B7100743 : Blo 1638018 7100743 := bstep (se 1 (by rfl) ⟨5325557, by rfl⟩ : syracuseStep 7100743 = 10651115) B10651115
theorem B5249519 : Blo 1638018 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B18668231 : Blo 1638018 18668231 := bstep (se 1 (by rfl) ⟨14001173, by rfl⟩ : syracuseStep 18668231 = 28002347) B28002347
theorem B21011399 : Blo 1638018 21011399 := bstep (se 1 (by rfl) ⟨15758549, by rfl⟩ : syracuseStep 21011399 = 31517099) B31517099
theorem B21003401 : Blo 1638018 21003401 := bstep (se 2 (by rfl) ⟨7876275, by rfl⟩ : syracuseStep 21003401 = 15752551) B15752551
theorem B6225083 : Blo 1638018 6225083 := bstep (se 1 (by rfl) ⟨4668812, by rfl⟩ : syracuseStep 6225083 = 9337625) B9337625
theorem B2457119 : Blo 1638018 2457119 := bstep (se 1 (by rfl) ⟨1842839, by rfl⟩ : syracuseStep 2457119 = 3685679) B3685679
theorem B28393001 : Blo 1638018 28393001 := bstep (se 2 (by rfl) ⟨10647375, by rfl⟩ : syracuseStep 28393001 = 21294751) B21294751
theorem B1842943 : Blo 1638018 1842943 := bstep (se 1 (by rfl) ⟨1382207, by rfl⟩ : syracuseStep 1842943 = 2764415) B2764415
theorem B1638471 : Blo 1638018 1638471 := bstep (se 1 (by rfl) ⟨1228853, by rfl⟩ : syracuseStep 1638471 = 2457707) B2457707
theorem B1638727 : Blo 1638018 1638727 := bstep (se 1 (by rfl) ⟨1229045, by rfl⟩ : syracuseStep 1638727 = 2458091) B2458091
theorem B1843951 : Blo 1638018 1843951 := bstep (se 1 (by rfl) ⟨1382963, by rfl⟩ : syracuseStep 1843951 = 2765927) B2765927
theorem B2459039 : Blo 1638018 2459039 := bstep (se 1 (by rfl) ⟨1844279, by rfl⟩ : syracuseStep 2459039 = 3688559) B3688559
theorem B1844671 : Blo 1638018 1844671 := bstep (se 1 (by rfl) ⟨1383503, by rfl⟩ : syracuseStep 1844671 = 2767007) B2767007
theorem B3687911 : Blo 1638018 3687911 := bstep (se 1 (by rfl) ⟨2765933, by rfl⟩ : syracuseStep 3687911 = 5531867) B5531867
theorem B3688091 : Blo 1638018 3688091 := bstep (se 1 (by rfl) ⟨2766068, by rfl⟩ : syracuseStep 3688091 = 5532137) B5532137
theorem B3499679 : Blo 1638018 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B12445487 : Blo 1638018 12445487 := bstep (se 1 (by rfl) ⟨9334115, by rfl⟩ : syracuseStep 12445487 = 18668231) B18668231
theorem B3688361 : Blo 1638018 3688361 := bstep (se 2 (by rfl) ⟨1383135, by rfl⟩ : syracuseStep 3688361 = 2766271) B2766271
theorem B14002267 : Blo 1638018 14002267 := bstep (se 1 (by rfl) ⟨10501700, by rfl⟩ : syracuseStep 14002267 = 21003401) B21003401
theorem B7875353 : Blo 1638018 7875353 := bstep (se 2 (by rfl) ⟨2953257, by rfl⟩ : syracuseStep 7875353 = 5906515) B5906515
theorem B4149083 : Blo 1638018 4149083 := bstep (se 1 (by rfl) ⟨3111812, by rfl⟩ : syracuseStep 4149083 = 6223625) B6223625
theorem B5607451 : Blo 1638018 5607451 := bstep (se 1 (by rfl) ⟨4205588, by rfl⟩ : syracuseStep 5607451 = 8411177) B8411177
theorem B5533919 : Blo 1638018 5533919 := bstep (se 1 (by rfl) ⟨4150439, by rfl⟩ : syracuseStep 5533919 = 8300879) B8300879
theorem B4150055 : Blo 1638018 4150055 := bstep (se 1 (by rfl) ⟨3112541, by rfl⟩ : syracuseStep 4150055 = 6225083) B6225083
theorem B18928667 : Blo 1638018 18928667 := bstep (se 1 (by rfl) ⟨14196500, by rfl⟩ : syracuseStep 18928667 = 28393001) B28393001
theorem B27989225 : Blo 1638018 27989225 := bstep (se 2 (by rfl) ⟨10495959, by rfl⟩ : syracuseStep 27989225 = 20991919) B20991919
theorem B466900375 : Blo 1638018 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B23634827 : Blo 1638018 23634827 := bstep (se 1 (by rfl) ⟨17726120, by rfl⟩ : syracuseStep 23634827 = 35452241) B35452241
theorem B9467657 : Blo 1638018 9467657 := bstep (se 2 (by rfl) ⟨3550371, by rfl⟩ : syracuseStep 9467657 = 7100743) B7100743
theorem B2766683 : Blo 1638018 2766683 := bstep (se 1 (by rfl) ⟨2075012, by rfl⟩ : syracuseStep 2766683 = 4150025) B4150025
theorem B41990399 : Blo 1638018 41990399 := bstep (se 1 (by rfl) ⟨31492799, by rfl⟩ : syracuseStep 41990399 = 62985599) B62985599
theorem B4668425 : Blo 1638018 4668425 := bstep (se 2 (by rfl) ⟨1750659, by rfl⟩ : syracuseStep 4668425 = 3501319) B3501319
theorem B14007599 : Blo 1638018 14007599 := bstep (se 1 (by rfl) ⟨10505699, by rfl⟩ : syracuseStep 14007599 = 21011399) B21011399
theorem B9330335 : Blo 1638018 9330335 := bstep (se 1 (by rfl) ⟨6997751, by rfl⟩ : syracuseStep 9330335 = 13995503) B13995503
theorem B2457257 : Blo 1638018 2457257 := bstep (se 2 (by rfl) ⟨921471, by rfl⟩ : syracuseStep 2457257 = 1842943) B1842943
theorem B1638079 : Blo 1638018 1638079 := bstep (se 1 (by rfl) ⟨1228559, by rfl⟩ : syracuseStep 1638079 = 2457119) B2457119
theorem B18669689 : Blo 1638018 18669689 := bstep (se 2 (by rfl) ⟨7001133, by rfl⟩ : syracuseStep 18669689 = 14002267) B14002267
theorem B1639359 : Blo 1638018 1639359 := bstep (se 1 (by rfl) ⟨1229519, by rfl⟩ : syracuseStep 1639359 = 2459039) B2459039
theorem B2458601 : Blo 1638018 2458601 := bstep (se 2 (by rfl) ⟨921975, by rfl⟩ : syracuseStep 2458601 = 1843951) B1843951
theorem B2458607 : Blo 1638018 2458607 := bstep (se 1 (by rfl) ⟨1843955, by rfl⟩ : syracuseStep 2458607 = 3687911) B3687911
theorem B2458727 : Blo 1638018 2458727 := bstep (se 1 (by rfl) ⟨1844045, by rfl⟩ : syracuseStep 2458727 = 3688091) B3688091
theorem B1844455 : Blo 1638018 1844455 := bstep (se 1 (by rfl) ⟨1383341, by rfl⟩ : syracuseStep 1844455 = 2766683) B2766683
theorem B2458907 : Blo 1638018 2458907 := bstep (se 1 (by rfl) ⟨1844180, by rfl⟩ : syracuseStep 2458907 = 3688361) B3688361
theorem B27993599 : Blo 1638018 27993599 := bstep (se 1 (by rfl) ⟨20995199, by rfl⟩ : syracuseStep 27993599 = 41990399) B41990399
theorem B2459561 : Blo 1638018 2459561 := bstep (se 2 (by rfl) ⟨922335, by rfl⟩ : syracuseStep 2459561 = 1844671) B1844671
theorem B6220223 : Blo 1638018 6220223 := bstep (se 1 (by rfl) ⟨4665167, by rfl⟩ : syracuseStep 6220223 = 9330335) B9330335
theorem B3689279 : Blo 1638018 3689279 := bstep (se 1 (by rfl) ⟨2766959, by rfl⟩ : syracuseStep 3689279 = 5533919) B5533919
theorem B15756551 : Blo 1638018 15756551 := bstep (se 1 (by rfl) ⟨11817413, by rfl⟩ : syracuseStep 15756551 = 23634827) B23634827
theorem B12619111 : Blo 1638018 12619111 := bstep (se 1 (by rfl) ⟨9464333, by rfl⟩ : syracuseStep 12619111 = 18928667) B18928667
theorem B6311771 : Blo 1638018 6311771 := bstep (se 1 (by rfl) ⟨4733828, by rfl⟩ : syracuseStep 6311771 = 9467657) B9467657
theorem B21000941 : Blo 1638018 21000941 := bstep (se 3 (by rfl) ⟨3937676, by rfl⟩ : syracuseStep 21000941 = 7875353) B7875353
theorem B2766055 : Blo 1638018 2766055 := bstep (se 1 (by rfl) ⟨2074541, by rfl⟩ : syracuseStep 2766055 = 4149083) B4149083
theorem B29906405 : Blo 1638018 29906405 := bstep (se 4 (by rfl) ⟨2803725, by rfl⟩ : syracuseStep 29906405 = 5607451) B5607451
theorem B2766703 : Blo 1638018 2766703 := bstep (se 1 (by rfl) ⟨2075027, by rfl⟩ : syracuseStep 2766703 = 4150055) B4150055
theorem B18659483 : Blo 1638018 18659483 := bstep (se 1 (by rfl) ⟨13994612, by rfl⟩ : syracuseStep 18659483 = 27989225) B27989225
theorem B2333119 : Blo 1638018 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B8296991 : Blo 1638018 8296991 := bstep (se 1 (by rfl) ⟨6222743, by rfl⟩ : syracuseStep 8296991 = 12445487) B12445487
theorem B622533833 : Blo 1638018 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B3112283 : Blo 1638018 3112283 := bstep (se 1 (by rfl) ⟨2334212, by rfl⟩ : syracuseStep 3112283 = 4668425) B4668425
theorem B9338399 : Blo 1638018 9338399 := bstep (se 1 (by rfl) ⟨7003799, by rfl⟩ : syracuseStep 9338399 = 14007599) B14007599
theorem B1638171 : Blo 1638018 1638171 := bstep (se 1 (by rfl) ⟨1228628, by rfl⟩ : syracuseStep 1638171 = 2457257) B2457257
theorem B14000627 : Blo 1638018 14000627 := bstep (se 1 (by rfl) ⟨10500470, by rfl⟩ : syracuseStep 14000627 = 21000941) B21000941
theorem B1639067 : Blo 1638018 1639067 := bstep (se 1 (by rfl) ⟨1229300, by rfl⟩ : syracuseStep 1639067 = 2458601) B2458601
theorem B1639071 : Blo 1638018 1639071 := bstep (se 1 (by rfl) ⟨1229303, by rfl⟩ : syracuseStep 1639071 = 2458607) B2458607
theorem B1639151 : Blo 1638018 1639151 := bstep (se 1 (by rfl) ⟨1229363, by rfl⟩ : syracuseStep 1639151 = 2458727) B2458727
theorem B1639271 : Blo 1638018 1639271 := bstep (se 1 (by rfl) ⟨1229453, by rfl⟩ : syracuseStep 1639271 = 2458907) B2458907
theorem B8299421 : Blo 1638018 8299421 := bstep (se 3 (by rfl) ⟨1556141, by rfl⟩ : syracuseStep 8299421 = 3112283) B3112283
theorem B18662399 : Blo 1638018 18662399 := bstep (se 1 (by rfl) ⟨13996799, by rfl⟩ : syracuseStep 18662399 = 27993599) B27993599
theorem B1639707 : Blo 1638018 1639707 := bstep (se 1 (by rfl) ⟨1229780, by rfl⟩ : syracuseStep 1639707 = 2459561) B2459561
theorem B4146815 : Blo 1638018 4146815 := bstep (se 1 (by rfl) ⟨3110111, by rfl⟩ : syracuseStep 4146815 = 6220223) B6220223
theorem B3688073 : Blo 1638018 3688073 := bstep (se 2 (by rfl) ⟨1383027, by rfl⟩ : syracuseStep 3688073 = 2766055) B2766055
theorem B2459273 : Blo 1638018 2459273 := bstep (se 2 (by rfl) ⟨922227, by rfl⟩ : syracuseStep 2459273 = 1844455) B1844455
theorem B5531327 : Blo 1638018 5531327 := bstep (se 1 (by rfl) ⟨4148495, by rfl⟩ : syracuseStep 5531327 = 8296991) B8296991
theorem B2459519 : Blo 1638018 2459519 := bstep (se 1 (by rfl) ⟨1844639, by rfl⟩ : syracuseStep 2459519 = 3689279) B3689279
theorem B10504367 : Blo 1638018 10504367 := bstep (se 1 (by rfl) ⟨7878275, by rfl⟩ : syracuseStep 10504367 = 15756551) B15756551
theorem B3688937 : Blo 1638018 3688937 := bstep (se 2 (by rfl) ⟨1383351, by rfl⟩ : syracuseStep 3688937 = 2766703) B2766703
theorem B12446459 : Blo 1638018 12446459 := bstep (se 1 (by rfl) ⟨9334844, by rfl⟩ : syracuseStep 12446459 = 18669689) B18669689
theorem B12439655 : Blo 1638018 12439655 := bstep (se 1 (by rfl) ⟨9329741, by rfl⟩ : syracuseStep 12439655 = 18659483) B18659483
theorem B4207847 : Blo 1638018 4207847 := bstep (se 1 (by rfl) ⟨3155885, by rfl⟩ : syracuseStep 4207847 = 6311771) B6311771
theorem B3110825 : Blo 1638018 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B19937603 : Blo 1638018 19937603 := bstep (se 1 (by rfl) ⟨14953202, by rfl⟩ : syracuseStep 19937603 = 29906405) B29906405
theorem B16825481 : Blo 1638018 16825481 := bstep (se 2 (by rfl) ⟨6309555, by rfl⟩ : syracuseStep 16825481 = 12619111) B12619111
theorem B415022555 : Blo 1638018 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B6225599 : Blo 1638018 6225599 := bstep (se 1 (by rfl) ⟨4669199, by rfl⟩ : syracuseStep 6225599 = 9338399) B9338399
theorem B53166941 : Blo 1638018 53166941 := bstep (se 3 (by rfl) ⟨9968801, by rfl⟩ : syracuseStep 53166941 = 19937603) B19937603
theorem B2458715 : Blo 1638018 2458715 := bstep (se 1 (by rfl) ⟨1844036, by rfl⟩ : syracuseStep 2458715 = 3688073) B3688073
theorem B1639515 : Blo 1638018 1639515 := bstep (se 1 (by rfl) ⟨1229636, by rfl⟩ : syracuseStep 1639515 = 2459273) B2459273
theorem B3687551 : Blo 1638018 3687551 := bstep (se 1 (by rfl) ⟨2765663, by rfl⟩ : syracuseStep 3687551 = 5531327) B5531327
theorem B1639679 : Blo 1638018 1639679 := bstep (se 1 (by rfl) ⟨1229759, by rfl⟩ : syracuseStep 1639679 = 2459519) B2459519
theorem B2459291 : Blo 1638018 2459291 := bstep (se 1 (by rfl) ⟨1844468, by rfl⟩ : syracuseStep 2459291 = 3688937) B3688937
theorem B11216987 : Blo 1638018 11216987 := bstep (se 1 (by rfl) ⟨8412740, by rfl⟩ : syracuseStep 11216987 = 16825481) B16825481
theorem B8293103 : Blo 1638018 8293103 := bstep (se 1 (by rfl) ⟨6219827, by rfl⟩ : syracuseStep 8293103 = 12439655) B12439655
theorem B9333751 : Blo 1638018 9333751 := bstep (se 1 (by rfl) ⟨7000313, by rfl⟩ : syracuseStep 9333751 = 14000627) B14000627
theorem B5532947 : Blo 1638018 5532947 := bstep (se 1 (by rfl) ⟨4149710, by rfl⟩ : syracuseStep 5532947 = 8299421) B8299421
theorem B2764543 : Blo 1638018 2764543 := bstep (se 1 (by rfl) ⟨2073407, by rfl⟩ : syracuseStep 2764543 = 4146815) B4146815
theorem B276681703 : Blo 1638018 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B8295533 : Blo 1638018 8295533 := bstep (se 3 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 8295533 = 3110825) B3110825
theorem B4150399 : Blo 1638018 4150399 := bstep (se 1 (by rfl) ⟨3112799, by rfl⟩ : syracuseStep 4150399 = 6225599) B6225599
theorem B11220925 : Blo 1638018 11220925 := bstep (se 3 (by rfl) ⟨2103923, by rfl⟩ : syracuseStep 11220925 = 4207847) B4207847
theorem B12441599 : Blo 1638018 12441599 := bstep (se 1 (by rfl) ⟨9331199, by rfl⟩ : syracuseStep 12441599 = 18662399) B18662399
theorem B7002911 : Blo 1638018 7002911 := bstep (se 1 (by rfl) ⟨5252183, by rfl⟩ : syracuseStep 7002911 = 10504367) B10504367
theorem B8297639 : Blo 1638018 8297639 := bstep (se 1 (by rfl) ⟨6223229, by rfl⟩ : syracuseStep 8297639 = 12446459) B12446459
theorem B1639143 : Blo 1638018 1639143 := bstep (se 1 (by rfl) ⟨1229357, by rfl⟩ : syracuseStep 1639143 = 2458715) B2458715
theorem B5530355 : Blo 1638018 5530355 := bstep (se 1 (by rfl) ⟨4147766, by rfl⟩ : syracuseStep 5530355 = 8295533) B8295533
theorem B2458367 : Blo 1638018 2458367 := bstep (se 1 (by rfl) ⟨1843775, by rfl⟩ : syracuseStep 2458367 = 3687551) B3687551
theorem B1639527 : Blo 1638018 1639527 := bstep (se 1 (by rfl) ⟨1229645, by rfl⟩ : syracuseStep 1639527 = 2459291) B2459291
theorem B12445001 : Blo 1638018 12445001 := bstep (se 2 (by rfl) ⟨4666875, by rfl⟩ : syracuseStep 12445001 = 9333751) B9333751
theorem B5531759 : Blo 1638018 5531759 := bstep (se 1 (by rfl) ⟨4148819, by rfl⟩ : syracuseStep 5531759 = 8297639) B8297639
theorem B3688631 : Blo 1638018 3688631 := bstep (se 1 (by rfl) ⟨2766473, by rfl⟩ : syracuseStep 3688631 = 5532947) B5532947
theorem B14961233 : Blo 1638018 14961233 := bstep (se 2 (by rfl) ⟨5610462, by rfl⟩ : syracuseStep 14961233 = 11220925) B11220925
theorem B8294399 : Blo 1638018 8294399 := bstep (se 1 (by rfl) ⟨6220799, by rfl⟩ : syracuseStep 8294399 = 12441599) B12441599
theorem B5533865 : Blo 1638018 5533865 := bstep (se 2 (by rfl) ⟨2075199, by rfl⟩ : syracuseStep 5533865 = 4150399) B4150399
theorem B35444627 : Blo 1638018 35444627 := bstep (se 1 (by rfl) ⟨26583470, by rfl⟩ : syracuseStep 35444627 = 53166941) B53166941
theorem B368908937 : Blo 1638018 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B7477991 : Blo 1638018 7477991 := bstep (se 1 (by rfl) ⟨5608493, by rfl⟩ : syracuseStep 7477991 = 11216987) B11216987
theorem B5528735 : Blo 1638018 5528735 := bstep (se 1 (by rfl) ⟨4146551, by rfl⟩ : syracuseStep 5528735 = 8293103) B8293103
theorem B4668607 : Blo 1638018 4668607 := bstep (se 1 (by rfl) ⟨3501455, by rfl⟩ : syracuseStep 4668607 = 7002911) B7002911
theorem B3686057 : Blo 1638018 3686057 := bstep (se 2 (by rfl) ⟨1382271, by rfl⟩ : syracuseStep 3686057 = 2764543) B2764543
theorem B3686903 : Blo 1638018 3686903 := bstep (se 1 (by rfl) ⟨2765177, by rfl⟩ : syracuseStep 3686903 = 5530355) B5530355
theorem B1638911 : Blo 1638018 1638911 := bstep (se 1 (by rfl) ⟨1229183, by rfl⟩ : syracuseStep 1638911 = 2458367) B2458367
theorem B5529599 : Blo 1638018 5529599 := bstep (se 1 (by rfl) ⟨4147199, by rfl⟩ : syracuseStep 5529599 = 8294399) B8294399
theorem B3687839 : Blo 1638018 3687839 := bstep (se 1 (by rfl) ⟨2765879, by rfl⟩ : syracuseStep 3687839 = 5531759) B5531759
theorem B2459087 : Blo 1638018 2459087 := bstep (se 1 (by rfl) ⟨1844315, by rfl⟩ : syracuseStep 2459087 = 3688631) B3688631
theorem B39896621 : Blo 1638018 39896621 := bstep (se 3 (by rfl) ⟨7480616, by rfl⟩ : syracuseStep 39896621 = 14961233) B14961233
theorem B3689243 : Blo 1638018 3689243 := bstep (se 1 (by rfl) ⟨2766932, by rfl⟩ : syracuseStep 3689243 = 5533865) B5533865
theorem B23629751 : Blo 1638018 23629751 := bstep (se 1 (by rfl) ⟨17722313, by rfl⟩ : syracuseStep 23629751 = 35444627) B35444627
theorem B4985327 : Blo 1638018 4985327 := bstep (se 1 (by rfl) ⟨3738995, by rfl⟩ : syracuseStep 4985327 = 7477991) B7477991
theorem B8296667 : Blo 1638018 8296667 := bstep (se 1 (by rfl) ⟨6222500, by rfl⟩ : syracuseStep 8296667 = 12445001) B12445001
theorem B6224809 : Blo 1638018 6224809 := bstep (se 2 (by rfl) ⟨2334303, by rfl⟩ : syracuseStep 6224809 = 4668607) B4668607
theorem B245939291 : Blo 1638018 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B3685823 : Blo 1638018 3685823 := bstep (se 1 (by rfl) ⟨2764367, by rfl⟩ : syracuseStep 3685823 = 5528735) B5528735
theorem B2457371 : Blo 1638018 2457371 := bstep (se 1 (by rfl) ⟨1843028, by rfl⟩ : syracuseStep 2457371 = 3686057) B3686057
theorem B2457935 : Blo 1638018 2457935 := bstep (se 1 (by rfl) ⟨1843451, by rfl⟩ : syracuseStep 2457935 = 3686903) B3686903
theorem B2458559 : Blo 1638018 2458559 := bstep (se 1 (by rfl) ⟨1843919, by rfl⟩ : syracuseStep 2458559 = 3687839) B3687839
theorem B1639391 : Blo 1638018 1639391 := bstep (se 1 (by rfl) ⟨1229543, by rfl⟩ : syracuseStep 1639391 = 2459087) B2459087
theorem B8299745 : Blo 1638018 8299745 := bstep (se 2 (by rfl) ⟨3112404, by rfl⟩ : syracuseStep 8299745 = 6224809) B6224809
theorem B5531111 : Blo 1638018 5531111 := bstep (se 1 (by rfl) ⟨4148333, by rfl⟩ : syracuseStep 5531111 = 8296667) B8296667
theorem B2459495 : Blo 1638018 2459495 := bstep (se 1 (by rfl) ⟨1844621, by rfl⟩ : syracuseStep 2459495 = 3689243) B3689243
theorem B163959527 : Blo 1638018 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B26597747 : Blo 1638018 26597747 := bstep (se 1 (by rfl) ⟨19948310, by rfl⟩ : syracuseStep 26597747 = 39896621) B39896621
theorem B13294205 : Blo 1638018 13294205 := bstep (se 3 (by rfl) ⟨2492663, by rfl⟩ : syracuseStep 13294205 = 4985327) B4985327
theorem B2457215 : Blo 1638018 2457215 := bstep (se 1 (by rfl) ⟨1842911, by rfl⟩ : syracuseStep 2457215 = 3685823) B3685823
theorem B1638247 : Blo 1638018 1638247 := bstep (se 1 (by rfl) ⟨1228685, by rfl⟩ : syracuseStep 1638247 = 2457371) B2457371
theorem B15753167 : Blo 1638018 15753167 := bstep (se 1 (by rfl) ⟨11814875, by rfl⟩ : syracuseStep 15753167 = 23629751) B23629751
theorem B3686399 : Blo 1638018 3686399 := bstep (se 1 (by rfl) ⟨2764799, by rfl⟩ : syracuseStep 3686399 = 5529599) B5529599
theorem B1638623 : Blo 1638018 1638623 := bstep (se 1 (by rfl) ⟨1228967, by rfl⟩ : syracuseStep 1638623 = 2457935) B2457935
theorem B109306351 : Blo 1638018 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B1639039 : Blo 1638018 1639039 := bstep (se 1 (by rfl) ⟨1229279, by rfl⟩ : syracuseStep 1639039 = 2458559) B2458559
theorem B3687407 : Blo 1638018 3687407 := bstep (se 1 (by rfl) ⟨2765555, by rfl⟩ : syracuseStep 3687407 = 5531111) B5531111
theorem B1639663 : Blo 1638018 1639663 := bstep (se 1 (by rfl) ⟨1229747, by rfl⟩ : syracuseStep 1639663 = 2459495) B2459495
theorem B2457599 : Blo 1638018 2457599 := bstep (se 1 (by rfl) ⟨1843199, by rfl⟩ : syracuseStep 2457599 = 3686399) B3686399
theorem B5533163 : Blo 1638018 5533163 := bstep (se 1 (by rfl) ⟨4149872, by rfl⟩ : syracuseStep 5533163 = 8299745) B8299745
theorem B17731831 : Blo 1638018 17731831 := bstep (se 1 (by rfl) ⟨13298873, by rfl⟩ : syracuseStep 17731831 = 26597747) B26597747
theorem B8862803 : Blo 1638018 8862803 := bstep (se 1 (by rfl) ⟨6647102, by rfl⟩ : syracuseStep 8862803 = 13294205) B13294205
theorem B1638143 : Blo 1638018 1638143 := bstep (se 1 (by rfl) ⟨1228607, by rfl⟩ : syracuseStep 1638143 = 2457215) B2457215
theorem B10502111 : Blo 1638018 10502111 := bstep (se 1 (by rfl) ⟨7876583, by rfl⟩ : syracuseStep 10502111 = 15753167) B15753167
theorem B23642441 : Blo 1638018 23642441 := bstep (se 2 (by rfl) ⟨8865915, by rfl⟩ : syracuseStep 23642441 = 17731831) B17731831
theorem B2458271 : Blo 1638018 2458271 := bstep (se 1 (by rfl) ⟨1843703, by rfl⟩ : syracuseStep 2458271 = 3687407) B3687407
theorem B1638399 : Blo 1638018 1638399 := bstep (se 1 (by rfl) ⟨1228799, by rfl⟩ : syracuseStep 1638399 = 2457599) B2457599
theorem B5908535 : Blo 1638018 5908535 := bstep (se 1 (by rfl) ⟨4431401, by rfl⟩ : syracuseStep 5908535 = 8862803) B8862803
theorem B3688775 : Blo 1638018 3688775 := bstep (se 1 (by rfl) ⟨2766581, by rfl⟩ : syracuseStep 3688775 = 5533163) B5533163
theorem B7001407 : Blo 1638018 7001407 := bstep (se 1 (by rfl) ⟨5251055, by rfl⟩ : syracuseStep 7001407 = 10502111) B10502111
theorem B145741801 : Blo 1638018 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B15761627 : Blo 1638018 15761627 := bstep (se 1 (by rfl) ⟨11821220, by rfl⟩ : syracuseStep 15761627 = 23642441) B23642441
theorem B1638847 : Blo 1638018 1638847 := bstep (se 1 (by rfl) ⟨1229135, by rfl⟩ : syracuseStep 1638847 = 2458271) B2458271
theorem B2459183 : Blo 1638018 2459183 := bstep (se 1 (by rfl) ⟨1844387, by rfl⟩ : syracuseStep 2459183 = 3688775) B3688775
theorem B9335209 : Blo 1638018 9335209 := bstep (se 2 (by rfl) ⟨3500703, by rfl⟩ : syracuseStep 9335209 = 7001407) B7001407
theorem B3939023 : Blo 1638018 3939023 := bstep (se 1 (by rfl) ⟨2954267, by rfl⟩ : syracuseStep 3939023 = 5908535) B5908535
theorem B194322401 : Blo 1638018 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B1639455 : Blo 1638018 1639455 := bstep (se 1 (by rfl) ⟨1229591, by rfl⟩ : syracuseStep 1639455 = 2459183) B2459183
theorem B12446945 : Blo 1638018 12446945 := bstep (se 2 (by rfl) ⟨4667604, by rfl⟩ : syracuseStep 12446945 = 9335209) B9335209
theorem B2626015 : Blo 1638018 2626015 := bstep (se 1 (by rfl) ⟨1969511, by rfl⟩ : syracuseStep 2626015 = 3939023) B3939023
theorem B10507751 : Blo 1638018 10507751 := bstep (se 1 (by rfl) ⟨7880813, by rfl⟩ : syracuseStep 10507751 = 15761627) B15761627
theorem B129548267 : Blo 1638018 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B7005167 : Blo 1638018 7005167 := bstep (se 1 (by rfl) ⟨5253875, by rfl⟩ : syracuseStep 7005167 = 10507751) B10507751
theorem B3501353 : Blo 1638018 3501353 := bstep (se 2 (by rfl) ⟨1313007, by rfl⟩ : syracuseStep 3501353 = 2626015) B2626015
theorem B86365511 : Blo 1638018 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B8297963 : Blo 1638018 8297963 := bstep (se 1 (by rfl) ⟨6223472, by rfl⟩ : syracuseStep 8297963 = 12446945) B12446945
theorem B4670111 : Blo 1638018 4670111 := bstep (se 1 (by rfl) ⟨3502583, by rfl⟩ : syracuseStep 4670111 = 7005167) B7005167
theorem B5531975 : Blo 1638018 5531975 := bstep (se 1 (by rfl) ⟨4148981, by rfl⟩ : syracuseStep 5531975 = 8297963) B8297963
theorem B57577007 : Blo 1638018 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B9336941 : Blo 1638018 9336941 := bstep (se 3 (by rfl) ⟨1750676, by rfl⟩ : syracuseStep 9336941 = 3501353) B3501353
theorem B3113407 : Blo 1638018 3113407 := bstep (se 1 (by rfl) ⟨2335055, by rfl⟩ : syracuseStep 3113407 = 4670111) B4670111
theorem B3687983 : Blo 1638018 3687983 := bstep (se 1 (by rfl) ⟨2765987, by rfl⟩ : syracuseStep 3687983 = 5531975) B5531975
theorem B38384671 : Blo 1638018 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B6224627 : Blo 1638018 6224627 := bstep (se 1 (by rfl) ⟨4668470, by rfl⟩ : syracuseStep 6224627 = 9336941) B9336941
theorem B2458655 : Blo 1638018 2458655 := bstep (se 1 (by rfl) ⟨1843991, by rfl⟩ : syracuseStep 2458655 = 3687983) B3687983
theorem B51179561 : Blo 1638018 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B4149751 : Blo 1638018 4149751 := bstep (se 1 (by rfl) ⟨3112313, by rfl⟩ : syracuseStep 4149751 = 6224627) B6224627
theorem B4151209 : Blo 1638018 4151209 := bstep (se 2 (by rfl) ⟨1556703, by rfl⟩ : syracuseStep 4151209 = 3113407) B3113407
theorem B34119707 : Blo 1638018 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B1639103 : Blo 1638018 1639103 := bstep (se 1 (by rfl) ⟨1229327, by rfl⟩ : syracuseStep 1639103 = 2458655) B2458655
theorem B5533001 : Blo 1638018 5533001 := bstep (se 2 (by rfl) ⟨2074875, by rfl⟩ : syracuseStep 5533001 = 4149751) B4149751
theorem B5534945 : Blo 1638018 5534945 := bstep (se 2 (by rfl) ⟨2075604, by rfl⟩ : syracuseStep 5534945 = 4151209) B4151209
theorem B3688667 : Blo 1638018 3688667 := bstep (se 1 (by rfl) ⟨2766500, by rfl⟩ : syracuseStep 3688667 = 5533001) B5533001
theorem B3689963 : Blo 1638018 3689963 := bstep (se 1 (by rfl) ⟨2767472, by rfl⟩ : syracuseStep 3689963 = 5534945) B5534945
theorem B90985885 : Blo 1638018 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B2459111 : Blo 1638018 2459111 := bstep (se 1 (by rfl) ⟨1844333, by rfl⟩ : syracuseStep 2459111 = 3688667) B3688667
theorem B2459975 : Blo 1638018 2459975 := bstep (se 1 (by rfl) ⟨1844981, by rfl⟩ : syracuseStep 2459975 = 3689963) B3689963
theorem B485258053 : Blo 1638018 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B1639407 : Blo 1638018 1639407 := bstep (se 1 (by rfl) ⟨1229555, by rfl⟩ : syracuseStep 1639407 = 2459111) B2459111
theorem B1639983 : Blo 1638018 1639983 := bstep (se 1 (by rfl) ⟨1229987, by rfl⟩ : syracuseStep 1639983 = 2459975) B2459975
theorem B647010737 : Blo 1638018 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B431340491 : Blo 1638018 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B287560327 : Blo 1638018 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B383413769 : Blo 1638018 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B255609179 : Blo 1638018 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B170406119 : Blo 1638018 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B454416317 : Blo 1638018 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B302944211 : Blo 1638018 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B201962807 : Blo 1638018 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B134641871 : Blo 1638018 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B89761247 : Blo 1638018 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B59840831 : Blo 1638018 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B39893887 : Blo 1638018 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B53191849 : Blo 1638018 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B70922465 : Blo 1638018 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B47281643 : Blo 1638018 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B31521095 : Blo 1638018 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B21014063 : Blo 1638018 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B14009375 : Blo 1638018 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B9339583 : Blo 1638018 9339583 := bstep (se 1 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 9339583 = 14009375) B14009375
theorem B12452777 : Blo 1638018 12452777 := bstep (se 2 (by rfl) ⟨4669791, by rfl⟩ : syracuseStep 12452777 = 9339583) B9339583
theorem B8301851 : Blo 1638018 8301851 := bstep (se 1 (by rfl) ⟨6226388, by rfl⟩ : syracuseStep 8301851 = 12452777) B12452777
theorem B5534567 : Blo 1638018 5534567 := bstep (se 1 (by rfl) ⟨4150925, by rfl⟩ : syracuseStep 5534567 = 8301851) B8301851
theorem B3689711 : Blo 1638018 3689711 := bstep (se 1 (by rfl) ⟨2767283, by rfl⟩ : syracuseStep 3689711 = 5534567) B5534567
theorem B2459807 : Blo 1638018 2459807 := bstep (se 1 (by rfl) ⟨1844855, by rfl⟩ : syracuseStep 2459807 = 3689711) B3689711
theorem B1639871 : Blo 1638018 1639871 := bstep (se 1 (by rfl) ⟨1229903, by rfl⟩ : syracuseStep 1639871 = 2459807) B2459807

theorem C0 (j : ℕ) (h1 : 409504 ≤ j) (h2 : j ≤ 410003) : Blo 1638018 (4 * j + 3) := by
  interval_cases j
  · exact B1638019
  · exact B1638023
  · exact B1638027
  · exact B1638031
  · exact B1638035
  · exact B1638039
  · exact B1638043
  · exact B1638047
  · exact B1638051
  · exact B1638055
  · exact B1638059
  · exact B1638063
  · exact B1638067
  · exact B1638071
  · exact B1638075
  · exact B1638079
  · exact B1638083
  · exact B1638087
  · exact B1638091
  · exact B1638095
  · exact B1638099
  · exact B1638103
  · exact B1638107
  · exact B1638111
  · exact B1638115
  · exact B1638119
  · exact B1638123
  · exact B1638127
  · exact B1638131
  · exact B1638135
  · exact B1638139
  · exact B1638143
  · exact B1638147
  · exact B1638151
  · exact B1638155
  · exact B1638159
  · exact B1638163
  · exact B1638167
  · exact B1638171
  · exact B1638175
  · exact B1638179
  · exact B1638183
  · exact B1638187
  · exact B1638191
  · exact B1638195
  · exact B1638199
  · exact B1638203
  · exact B1638207
  · exact B1638211
  · exact B1638215
  · exact B1638219
  · exact B1638223
  · exact B1638227
  · exact B1638231
  · exact B1638235
  · exact B1638239
  · exact B1638243
  · exact B1638247
  · exact B1638251
  · exact B1638255
  · exact B1638259
  · exact B1638263
  · exact B1638267
  · exact B1638271
  · exact B1638275
  · exact B1638279
  · exact B1638283
  · exact B1638287
  · exact B1638291
  · exact B1638295
  · exact B1638299
  · exact B1638303
  · exact B1638307
  · exact B1638311
  · exact B1638315
  · exact B1638319
  · exact B1638323
  · exact B1638327
  · exact B1638331
  · exact B1638335
  · exact B1638339
  · exact B1638343
  · exact B1638347
  · exact B1638351
  · exact B1638355
  · exact B1638359
  · exact B1638363
  · exact B1638367
  · exact B1638371
  · exact B1638375
  · exact B1638379
  · exact B1638383
  · exact B1638387
  · exact B1638391
  · exact B1638395
  · exact B1638399
  · exact B1638403
  · exact B1638407
  · exact B1638411
  · exact B1638415
  · exact B1638419
  · exact B1638423
  · exact B1638427
  · exact B1638431
  · exact B1638435
  · exact B1638439
  · exact B1638443
  · exact B1638447
  · exact B1638451
  · exact B1638455
  · exact B1638459
  · exact B1638463
  · exact B1638467
  · exact B1638471
  · exact B1638475
  · exact B1638479
  · exact B1638483
  · exact B1638487
  · exact B1638491
  · exact B1638495
  · exact B1638499
  · exact B1638503
  · exact B1638507
  · exact B1638511
  · exact B1638515
  · exact B1638519
  · exact B1638523
  · exact B1638527
  · exact B1638531
  · exact B1638535
  · exact B1638539
  · exact B1638543
  · exact B1638547
  · exact B1638551
  · exact B1638555
  · exact B1638559
  · exact B1638563
  · exact B1638567
  · exact B1638571
  · exact B1638575
  · exact B1638579
  · exact B1638583
  · exact B1638587
  · exact B1638591
  · exact B1638595
  · exact B1638599
  · exact B1638603
  · exact B1638607
  · exact B1638611
  · exact B1638615
  · exact B1638619
  · exact B1638623
  · exact B1638627
  · exact B1638631
  · exact B1638635
  · exact B1638639
  · exact B1638643
  · exact B1638647
  · exact B1638651
  · exact B1638655
  · exact B1638659
  · exact B1638663
  · exact B1638667
  · exact B1638671
  · exact B1638675
  · exact B1638679
  · exact B1638683
  · exact B1638687
  · exact B1638691
  · exact B1638695
  · exact B1638699
  · exact B1638703
  · exact B1638707
  · exact B1638711
  · exact B1638715
  · exact B1638719
  · exact B1638723
  · exact B1638727
  · exact B1638731
  · exact B1638735
  · exact B1638739
  · exact B1638743
  · exact B1638747
  · exact B1638751
  · exact B1638755
  · exact B1638759
  · exact B1638763
  · exact B1638767
  · exact B1638771
  · exact B1638775
  · exact B1638779
  · exact B1638783
  · exact B1638787
  · exact B1638791
  · exact B1638795
  · exact B1638799
  · exact B1638803
  · exact B1638807
  · exact B1638811
  · exact B1638815
  · exact B1638819
  · exact B1638823
  · exact B1638827
  · exact B1638831
  · exact B1638835
  · exact B1638839
  · exact B1638843
  · exact B1638847
  · exact B1638851
  · exact B1638855
  · exact B1638859
  · exact B1638863
  · exact B1638867
  · exact B1638871
  · exact B1638875
  · exact B1638879
  · exact B1638883
  · exact B1638887
  · exact B1638891
  · exact B1638895
  · exact B1638899
  · exact B1638903
  · exact B1638907
  · exact B1638911
  · exact B1638915
  · exact B1638919
  · exact B1638923
  · exact B1638927
  · exact B1638931
  · exact B1638935
  · exact B1638939
  · exact B1638943
  · exact B1638947
  · exact B1638951
  · exact B1638955
  · exact B1638959
  · exact B1638963
  · exact B1638967
  · exact B1638971
  · exact B1638975
  · exact B1638979
  · exact B1638983
  · exact B1638987
  · exact B1638991
  · exact B1638995
  · exact B1638999
  · exact B1639003
  · exact B1639007
  · exact B1639011
  · exact B1639015
  · exact B1639019
  · exact B1639023
  · exact B1639027
  · exact B1639031
  · exact B1639035
  · exact B1639039
  · exact B1639043
  · exact B1639047
  · exact B1639051
  · exact B1639055
  · exact B1639059
  · exact B1639063
  · exact B1639067
  · exact B1639071
  · exact B1639075
  · exact B1639079
  · exact B1639083
  · exact B1639087
  · exact B1639091
  · exact B1639095
  · exact B1639099
  · exact B1639103
  · exact B1639107
  · exact B1639111
  · exact B1639115
  · exact B1639119
  · exact B1639123
  · exact B1639127
  · exact B1639131
  · exact B1639135
  · exact B1639139
  · exact B1639143
  · exact B1639147
  · exact B1639151
  · exact B1639155
  · exact B1639159
  · exact B1639163
  · exact B1639167
  · exact B1639171
  · exact B1639175
  · exact B1639179
  · exact B1639183
  · exact B1639187
  · exact B1639191
  · exact B1639195
  · exact B1639199
  · exact B1639203
  · exact B1639207
  · exact B1639211
  · exact B1639215
  · exact B1639219
  · exact B1639223
  · exact B1639227
  · exact B1639231
  · exact B1639235
  · exact B1639239
  · exact B1639243
  · exact B1639247
  · exact B1639251
  · exact B1639255
  · exact B1639259
  · exact B1639263
  · exact B1639267
  · exact B1639271
  · exact B1639275
  · exact B1639279
  · exact B1639283
  · exact B1639287
  · exact B1639291
  · exact B1639295
  · exact B1639299
  · exact B1639303
  · exact B1639307
  · exact B1639311
  · exact B1639315
  · exact B1639319
  · exact B1639323
  · exact B1639327
  · exact B1639331
  · exact B1639335
  · exact B1639339
  · exact B1639343
  · exact B1639347
  · exact B1639351
  · exact B1639355
  · exact B1639359
  · exact B1639363
  · exact B1639367
  · exact B1639371
  · exact B1639375
  · exact B1639379
  · exact B1639383
  · exact B1639387
  · exact B1639391
  · exact B1639395
  · exact B1639399
  · exact B1639403
  · exact B1639407
  · exact B1639411
  · exact B1639415
  · exact B1639419
  · exact B1639423
  · exact B1639427
  · exact B1639431
  · exact B1639435
  · exact B1639439
  · exact B1639443
  · exact B1639447
  · exact B1639451
  · exact B1639455
  · exact B1639459
  · exact B1639463
  · exact B1639467
  · exact B1639471
  · exact B1639475
  · exact B1639479
  · exact B1639483
  · exact B1639487
  · exact B1639491
  · exact B1639495
  · exact B1639499
  · exact B1639503
  · exact B1639507
  · exact B1639511
  · exact B1639515
  · exact B1639519
  · exact B1639523
  · exact B1639527
  · exact B1639531
  · exact B1639535
  · exact B1639539
  · exact B1639543
  · exact B1639547
  · exact B1639551
  · exact B1639555
  · exact B1639559
  · exact B1639563
  · exact B1639567
  · exact B1639571
  · exact B1639575
  · exact B1639579
  · exact B1639583
  · exact B1639587
  · exact B1639591
  · exact B1639595
  · exact B1639599
  · exact B1639603
  · exact B1639607
  · exact B1639611
  · exact B1639615
  · exact B1639619
  · exact B1639623
  · exact B1639627
  · exact B1639631
  · exact B1639635
  · exact B1639639
  · exact B1639643
  · exact B1639647
  · exact B1639651
  · exact B1639655
  · exact B1639659
  · exact B1639663
  · exact B1639667
  · exact B1639671
  · exact B1639675
  · exact B1639679
  · exact B1639683
  · exact B1639687
  · exact B1639691
  · exact B1639695
  · exact B1639699
  · exact B1639703
  · exact B1639707
  · exact B1639711
  · exact B1639715
  · exact B1639719
  · exact B1639723
  · exact B1639727
  · exact B1639731
  · exact B1639735
  · exact B1639739
  · exact B1639743
  · exact B1639747
  · exact B1639751
  · exact B1639755
  · exact B1639759
  · exact B1639763
  · exact B1639767
  · exact B1639771
  · exact B1639775
  · exact B1639779
  · exact B1639783
  · exact B1639787
  · exact B1639791
  · exact B1639795
  · exact B1639799
  · exact B1639803
  · exact B1639807
  · exact B1639811
  · exact B1639815
  · exact B1639819
  · exact B1639823
  · exact B1639827
  · exact B1639831
  · exact B1639835
  · exact B1639839
  · exact B1639843
  · exact B1639847
  · exact B1639851
  · exact B1639855
  · exact B1639859
  · exact B1639863
  · exact B1639867
  · exact B1639871
  · exact B1639875
  · exact B1639879
  · exact B1639883
  · exact B1639887
  · exact B1639891
  · exact B1639895
  · exact B1639899
  · exact B1639903
  · exact B1639907
  · exact B1639911
  · exact B1639915
  · exact B1639919
  · exact B1639923
  · exact B1639927
  · exact B1639931
  · exact B1639935
  · exact B1639939
  · exact B1639943
  · exact B1639947
  · exact B1639951
  · exact B1639955
  · exact B1639959
  · exact B1639963
  · exact B1639967
  · exact B1639971
  · exact B1639975
  · exact B1639979
  · exact B1639983
  · exact B1639987
  · exact B1639991
  · exact B1639995
  · exact B1639999
  · exact B1640003
  · exact B1640007
  · exact B1640011
  · exact B1640015

theorem solution (m : ℕ) (hlo : 1638018 ≤ m) (hhi : m ≤ 1640018) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 409504 ≤ j := by omega
    have hj2 : j ≤ 410003 := by omega
    have hb : Blo 1638018 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
