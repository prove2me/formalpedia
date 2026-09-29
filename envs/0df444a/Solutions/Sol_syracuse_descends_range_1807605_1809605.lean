-- Prove2me | solution 1 for syracuse_descends_range_1807605_1809605
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:52:32.773018+00:00
-- url     : https://prove2.me/submissions/cb6f3814-4d4e-4213-b669-35a37fb591ad

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


theorem B4071437 : Blo 1807605 4071437 := bbase (se 3 (by rfl) ⟨763394, by rfl⟩ : syracuseStep 4071437 = 1526789) (by norm_num)
theorem B2711573 : Blo 1807605 2711573 := bbase (se 6 (by rfl) ⟨63552, by rfl⟩ : syracuseStep 2711573 = 127105) (by norm_num)
theorem B2711597 : Blo 1807605 2711597 := bbase (se 3 (by rfl) ⟨508424, by rfl⟩ : syracuseStep 2711597 = 1016849) (by norm_num)
theorem B2711621 : Blo 1807605 2711621 := bbase (se 4 (by rfl) ⟨254214, by rfl⟩ : syracuseStep 2711621 = 508429) (by norm_num)
theorem B4071509 : Blo 1807605 4071509 := bbase (se 8 (by rfl) ⟨23856, by rfl⟩ : syracuseStep 4071509 = 47713) (by norm_num)
theorem B2711645 : Blo 1807605 2711645 := bbase (se 3 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 2711645 = 1016867) (by norm_num)
theorem B3432557 : Blo 1807605 3432557 := bbase (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) (by norm_num)
theorem B2711669 : Blo 1807605 2711669 := bbase (se 5 (by rfl) ⟨127109, by rfl⟩ : syracuseStep 2711669 = 254219) (by norm_num)
theorem B2711693 : Blo 1807605 2711693 := bbase (se 3 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 2711693 = 1016885) (by norm_num)
theorem B4071581 : Blo 1807605 4071581 := bbase (se 3 (by rfl) ⟨763421, by rfl⟩ : syracuseStep 4071581 = 1526843) (by norm_num)
theorem B2711717 : Blo 1807605 2711717 := bbase (se 4 (by rfl) ⟨254223, by rfl⟩ : syracuseStep 2711717 = 508447) (by norm_num)
theorem B8249525 : Blo 1807605 8249525 := bbase (se 5 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 8249525 = 773393) (by norm_num)
theorem B2711741 : Blo 1807605 2711741 := bbase (se 3 (by rfl) ⟨508451, by rfl⟩ : syracuseStep 2711741 = 1016903) (by norm_num)
theorem B4579517 : Blo 1807605 4579517 := bbase (se 3 (by rfl) ⟨858659, by rfl⟩ : syracuseStep 4579517 = 1717319) (by norm_num)
theorem B2711765 : Blo 1807605 2711765 := bbase (se 7 (by rfl) ⟨31778, by rfl⟩ : syracuseStep 2711765 = 63557) (by norm_num)
theorem B6185173 : Blo 1807605 6185173 := bbase (se 7 (by rfl) ⟨72482, by rfl⟩ : syracuseStep 6185173 = 144965) (by norm_num)
theorem B2711789 : Blo 1807605 2711789 := bbase (se 3 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 2711789 = 1016921) (by norm_num)
theorem B2711813 : Blo 1807605 2711813 := bbase (se 4 (by rfl) ⟨254232, by rfl⟩ : syracuseStep 2711813 = 508465) (by norm_num)
theorem B3432709 : Blo 1807605 3432709 := bbase (se 4 (by rfl) ⟨321816, by rfl⟩ : syracuseStep 3432709 = 643633) (by norm_num)
theorem B2711837 : Blo 1807605 2711837 := bbase (se 3 (by rfl) ⟨508469, by rfl⟩ : syracuseStep 2711837 = 1016939) (by norm_num)
theorem B2711861 : Blo 1807605 2711861 := bbase (se 5 (by rfl) ⟨127118, by rfl⟩ : syracuseStep 2711861 = 254237) (by norm_num)
theorem B6103349 : Blo 1807605 6103349 := bbase (se 5 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 6103349 = 572189) (by norm_num)
theorem B2711885 : Blo 1807605 2711885 := bbase (se 3 (by rfl) ⟨508478, by rfl⟩ : syracuseStep 2711885 = 1016957) (by norm_num)
theorem B4464989 : Blo 1807605 4464989 := bbase (se 3 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 4464989 = 1674371) (by norm_num)
theorem B2711909 : Blo 1807605 2711909 := bbase (se 4 (by rfl) ⟨254241, by rfl⟩ : syracuseStep 2711909 = 508483) (by norm_num)
theorem B2711933 : Blo 1807605 2711933 := bbase (se 3 (by rfl) ⟨508487, by rfl⟩ : syracuseStep 2711933 = 1016975) (by norm_num)
theorem B2711957 : Blo 1807605 2711957 := bbase (se 6 (by rfl) ⟨63561, by rfl⟩ : syracuseStep 2711957 = 127123) (by norm_num)
theorem B2711981 : Blo 1807605 2711981 := bbase (se 3 (by rfl) ⟨508496, by rfl⟩ : syracuseStep 2711981 = 1016993) (by norm_num)
theorem B2712005 : Blo 1807605 2712005 := bbase (se 4 (by rfl) ⟨254250, by rfl⟩ : syracuseStep 2712005 = 508501) (by norm_num)
theorem B2712029 : Blo 1807605 2712029 := bbase (se 3 (by rfl) ⟨508505, by rfl⟩ : syracuseStep 2712029 = 1017011) (by norm_num)
theorem B2712053 : Blo 1807605 2712053 := bbase (se 5 (by rfl) ⟨127127, by rfl⟩ : syracuseStep 2712053 = 254255) (by norm_num)
theorem B13033973 : Blo 1807605 13033973 := bbase (se 5 (by rfl) ⟨610967, by rfl⟩ : syracuseStep 13033973 = 1221935) (by norm_num)
theorem B4956677 : Blo 1807605 4956677 := bbase (se 4 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 4956677 = 929377) (by norm_num)
theorem B2712077 : Blo 1807605 2712077 := bbase (se 3 (by rfl) ⟨508514, by rfl⟩ : syracuseStep 2712077 = 1017029) (by norm_num)
theorem B4579861 : Blo 1807605 4579861 := bbase (se 6 (by rfl) ⟨107340, by rfl⟩ : syracuseStep 4579861 = 214681) (by norm_num)
theorem B2712101 : Blo 1807605 2712101 := bbase (se 4 (by rfl) ⟨254259, by rfl⟩ : syracuseStep 2712101 = 508519) (by norm_num)
theorem B3433013 : Blo 1807605 3433013 := bbase (se 5 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 3433013 = 321845) (by norm_num)
theorem B2712125 : Blo 1807605 2712125 := bbase (se 3 (by rfl) ⟨508523, by rfl⟩ : syracuseStep 2712125 = 1017047) (by norm_num)
theorem B2712149 : Blo 1807605 2712149 := bbase (se 8 (by rfl) ⟨15891, by rfl⟩ : syracuseStep 2712149 = 31783) (by norm_num)
theorem B2712173 : Blo 1807605 2712173 := bbase (se 3 (by rfl) ⟨508532, by rfl⟩ : syracuseStep 2712173 = 1017065) (by norm_num)
theorem B14672501 : Blo 1807605 14672501 := bbase (se 5 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 14672501 = 1375547) (by norm_num)
theorem B2712197 : Blo 1807605 2712197 := bbase (se 4 (by rfl) ⟨254268, by rfl⟩ : syracuseStep 2712197 = 508537) (by norm_num)
theorem B4579973 : Blo 1807605 4579973 := bbase (se 4 (by rfl) ⟨429372, by rfl⟩ : syracuseStep 4579973 = 858745) (by norm_num)
theorem B9159317 : Blo 1807605 9159317 := bbase (se 6 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 9159317 = 429343) (by norm_num)
theorem B2712221 : Blo 1807605 2712221 := bbase (se 3 (by rfl) ⟨508541, by rfl⟩ : syracuseStep 2712221 = 1017083) (by norm_num)
theorem B2712245 : Blo 1807605 2712245 := bbase (se 5 (by rfl) ⟨127136, by rfl⟩ : syracuseStep 2712245 = 254273) (by norm_num)
theorem B2712269 : Blo 1807605 2712269 := bbase (se 3 (by rfl) ⟨508550, by rfl⟩ : syracuseStep 2712269 = 1017101) (by norm_num)
theorem B2712293 : Blo 1807605 2712293 := bbase (se 4 (by rfl) ⟨254277, by rfl⟩ : syracuseStep 2712293 = 508555) (by norm_num)
theorem B6103781 : Blo 1807605 6103781 := bbase (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) (by norm_num)
theorem B2712317 : Blo 1807605 2712317 := bbase (se 3 (by rfl) ⟨508559, by rfl⟩ : syracuseStep 2712317 = 1017119) (by norm_num)
theorem B2712341 : Blo 1807605 2712341 := bbase (se 6 (by rfl) ⟨63570, by rfl⟩ : syracuseStep 2712341 = 127141) (by norm_num)
theorem B2712365 : Blo 1807605 2712365 := bbase (se 3 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 2712365 = 1017137) (by norm_num)
theorem B2712389 : Blo 1807605 2712389 := bbase (se 4 (by rfl) ⟨254286, by rfl⟩ : syracuseStep 2712389 = 508573) (by norm_num)
theorem B4580165 : Blo 1807605 4580165 := bbase (se 4 (by rfl) ⟨429390, by rfl⟩ : syracuseStep 4580165 = 858781) (by norm_num)
theorem B2712413 : Blo 1807605 2712413 := bbase (se 3 (by rfl) ⟨508577, by rfl⟩ : syracuseStep 2712413 = 1017155) (by norm_num)
theorem B2712437 : Blo 1807605 2712437 := bbase (se 5 (by rfl) ⟨127145, by rfl⟩ : syracuseStep 2712437 = 254291) (by norm_num)
theorem B2712461 : Blo 1807605 2712461 := bbase (se 3 (by rfl) ⟨508586, by rfl⟩ : syracuseStep 2712461 = 1017173) (by norm_num)
theorem B6865829 : Blo 1807605 6865829 := bbase (se 4 (by rfl) ⟨643671, by rfl⟩ : syracuseStep 6865829 = 1287343) (by norm_num)
theorem B2712485 : Blo 1807605 2712485 := bbase (se 4 (by rfl) ⟨254295, by rfl⟩ : syracuseStep 2712485 = 508591) (by norm_num)
theorem B2712509 : Blo 1807605 2712509 := bbase (se 3 (by rfl) ⟨508595, by rfl⟩ : syracuseStep 2712509 = 1017191) (by norm_num)
theorem B2712533 : Blo 1807605 2712533 := bbase (se 7 (by rfl) ⟨31787, by rfl⟩ : syracuseStep 2712533 = 63575) (by norm_num)
theorem B2712557 : Blo 1807605 2712557 := bbase (se 3 (by rfl) ⟨508604, by rfl⟩ : syracuseStep 2712557 = 1017209) (by norm_num)
theorem B2712581 : Blo 1807605 2712581 := bbase (se 4 (by rfl) ⟨254304, by rfl⟩ : syracuseStep 2712581 = 508609) (by norm_num)
theorem B2712605 : Blo 1807605 2712605 := bbase (se 3 (by rfl) ⟨508613, by rfl⟩ : syracuseStep 2712605 = 1017227) (by norm_num)
theorem B9151541 : Blo 1807605 9151541 := bbase (se 5 (by rfl) ⟨428978, by rfl⟩ : syracuseStep 9151541 = 857957) (by norm_num)
theorem B2712629 : Blo 1807605 2712629 := bbase (se 5 (by rfl) ⟨127154, by rfl⟩ : syracuseStep 2712629 = 254309) (by norm_num)
theorem B2712653 : Blo 1807605 2712653 := bbase (se 3 (by rfl) ⟨508622, by rfl⟩ : syracuseStep 2712653 = 1017245) (by norm_num)
theorem B2712677 : Blo 1807605 2712677 := bbase (se 4 (by rfl) ⟨254313, by rfl⟩ : syracuseStep 2712677 = 508627) (by norm_num)
theorem B2712701 : Blo 1807605 2712701 := bbase (se 3 (by rfl) ⟨508631, by rfl⟩ : syracuseStep 2712701 = 1017263) (by norm_num)
theorem B2712725 : Blo 1807605 2712725 := bbase (se 6 (by rfl) ⟨63579, by rfl⟩ : syracuseStep 2712725 = 127159) (by norm_num)
theorem B6104213 : Blo 1807605 6104213 := bbase (se 6 (by rfl) ⟨143067, by rfl⟩ : syracuseStep 6104213 = 286135) (by norm_num)
theorem B4580509 : Blo 1807605 4580509 := bbase (se 3 (by rfl) ⟨858845, by rfl⟩ : syracuseStep 4580509 = 1717691) (by norm_num)
theorem B2712749 : Blo 1807605 2712749 := bbase (se 3 (by rfl) ⟨508640, by rfl⟩ : syracuseStep 2712749 = 1017281) (by norm_num)
theorem B7726261 : Blo 1807605 7726261 := bbase (se 5 (by rfl) ⟨362168, by rfl⟩ : syracuseStep 7726261 = 724337) (by norm_num)
theorem B2319553 : Blo 1807605 2319553 := bbase (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) (by norm_num)
theorem B6866117 : Blo 1807605 6866117 := bbase (se 4 (by rfl) ⟨643698, by rfl⟩ : syracuseStep 6866117 = 1287397) (by norm_num)
theorem B2712773 : Blo 1807605 2712773 := bbase (se 4 (by rfl) ⟨254322, by rfl⟩ : syracuseStep 2712773 = 508645) (by norm_num)
theorem B2712797 : Blo 1807605 2712797 := bbase (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) (by norm_num)
theorem B2712821 : Blo 1807605 2712821 := bbase (se 5 (by rfl) ⟨127163, by rfl⟩ : syracuseStep 2712821 = 254327) (by norm_num)
theorem B2712845 : Blo 1807605 2712845 := bbase (se 3 (by rfl) ⟨508658, by rfl⟩ : syracuseStep 2712845 = 1017317) (by norm_num)
theorem B2712869 : Blo 1807605 2712869 := bbase (se 4 (by rfl) ⟨254331, by rfl⟩ : syracuseStep 2712869 = 508663) (by norm_num)
theorem B3433765 : Blo 1807605 3433765 := bbase (se 4 (by rfl) ⟨321915, by rfl⟩ : syracuseStep 3433765 = 643831) (by norm_num)
theorem B8693045 : Blo 1807605 8693045 := bbase (se 5 (by rfl) ⟨407486, by rfl⟩ : syracuseStep 8693045 = 814973) (by norm_num)
theorem B2712893 : Blo 1807605 2712893 := bbase (se 3 (by rfl) ⟨508667, by rfl⟩ : syracuseStep 2712893 = 1017335) (by norm_num)
theorem B2712917 : Blo 1807605 2712917 := bbase (se 12 (by rfl) ⟨993, by rfl⟩ : syracuseStep 2712917 = 1987) (by norm_num)
theorem B2712941 : Blo 1807605 2712941 := bbase (se 3 (by rfl) ⟨508676, by rfl⟩ : syracuseStep 2712941 = 1017353) (by norm_num)
theorem B2712965 : Blo 1807605 2712965 := bbase (se 4 (by rfl) ⟨254340, by rfl⟩ : syracuseStep 2712965 = 508681) (by norm_num)
theorem B2712989 : Blo 1807605 2712989 := bbase (se 3 (by rfl) ⟨508685, by rfl⟩ : syracuseStep 2712989 = 1017371) (by norm_num)
theorem B2713013 : Blo 1807605 2713013 := bbase (se 5 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 2713013 = 254345) (by norm_num)
theorem B3433909 : Blo 1807605 3433909 := bbase (se 5 (by rfl) ⟨160964, by rfl⟩ : syracuseStep 3433909 = 321929) (by norm_num)
theorem B2713037 : Blo 1807605 2713037 := bbase (se 3 (by rfl) ⟨508694, by rfl⟩ : syracuseStep 2713037 = 1017389) (by norm_num)
theorem B2713061 : Blo 1807605 2713061 := bbase (se 4 (by rfl) ⟨254349, by rfl⟩ : syracuseStep 2713061 = 508699) (by norm_num)
theorem B2713085 : Blo 1807605 2713085 := bbase (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) (by norm_num)
theorem B2713109 : Blo 1807605 2713109 := bbase (se 6 (by rfl) ⟨63588, by rfl⟩ : syracuseStep 2713109 = 127177) (by norm_num)
theorem B2713133 : Blo 1807605 2713133 := bbase (se 3 (by rfl) ⟨508712, by rfl⟩ : syracuseStep 2713133 = 1017425) (by norm_num)
theorem B5219909 : Blo 1807605 5219909 := bbase (se 4 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 5219909 = 978733) (by norm_num)
theorem B2713157 : Blo 1807605 2713157 := bbase (se 4 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 2713157 = 508717) (by norm_num)
theorem B6104645 : Blo 1807605 6104645 := bbase (se 4 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 6104645 = 1144621) (by norm_num)
theorem B3434069 : Blo 1807605 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B2713181 : Blo 1807605 2713181 := bbase (se 3 (by rfl) ⟨508721, by rfl⟩ : syracuseStep 2713181 = 1017443) (by norm_num)
theorem B12371573 : Blo 1807605 12371573 := bbase (se 5 (by rfl) ⟨579917, by rfl⟩ : syracuseStep 12371573 = 1159835) (by norm_num)
theorem B2713205 : Blo 1807605 2713205 := bbase (se 5 (by rfl) ⟨127181, by rfl⟩ : syracuseStep 2713205 = 254363) (by norm_num)
theorem B2573957 : Blo 1807605 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B2713229 : Blo 1807605 2713229 := bbase (se 3 (by rfl) ⟨508730, by rfl⟩ : syracuseStep 2713229 = 1017461) (by norm_num)
theorem B4638365 : Blo 1807605 4638365 := bbase (se 3 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 4638365 = 1739387) (by norm_num)
theorem B2713253 : Blo 1807605 2713253 := bbase (se 4 (by rfl) ⟨254367, by rfl⟩ : syracuseStep 2713253 = 508735) (by norm_num)
theorem B4343485 : Blo 1807605 4343485 := bbase (se 3 (by rfl) ⟨814403, by rfl⟩ : syracuseStep 4343485 = 1628807) (by norm_num)
theorem B2713277 : Blo 1807605 2713277 := bbase (se 3 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 2713277 = 1017479) (by norm_num)
theorem B2713301 : Blo 1807605 2713301 := bbase (se 7 (by rfl) ⟨31796, by rfl⟩ : syracuseStep 2713301 = 63593) (by norm_num)
theorem B3434213 : Blo 1807605 3434213 := bbase (se 4 (by rfl) ⟨321957, by rfl⟩ : syracuseStep 3434213 = 643915) (by norm_num)
theorem B2713325 : Blo 1807605 2713325 := bbase (se 3 (by rfl) ⟨508748, by rfl⟩ : syracuseStep 2713325 = 1017497) (by norm_num)
theorem B2172665 : Blo 1807605 2172665 := bbase (se 2 (by rfl) ⟨814749, by rfl⟩ : syracuseStep 2172665 = 1629499) (by norm_num)
theorem B2713349 : Blo 1807605 2713349 := bbase (se 4 (by rfl) ⟨254376, by rfl⟩ : syracuseStep 2713349 = 508753) (by norm_num)
theorem B11593493 : Blo 1807605 11593493 := bbase (se 6 (by rfl) ⟨271722, by rfl⟩ : syracuseStep 11593493 = 543445) (by norm_num)
theorem B2713373 : Blo 1807605 2713373 := bbase (se 3 (by rfl) ⟨508757, by rfl⟩ : syracuseStep 2713373 = 1017515) (by norm_num)
theorem B2713397 : Blo 1807605 2713397 := bbase (se 5 (by rfl) ⟨127190, by rfl⟩ : syracuseStep 2713397 = 254381) (by norm_num)
theorem B2713421 : Blo 1807605 2713421 := bbase (se 3 (by rfl) ⟨508766, by rfl⟩ : syracuseStep 2713421 = 1017533) (by norm_num)
theorem B10299221 : Blo 1807605 10299221 := bbase (se 9 (by rfl) ⟨30173, by rfl⟩ : syracuseStep 10299221 = 60347) (by norm_num)
theorem B2713445 : Blo 1807605 2713445 := bbase (se 4 (by rfl) ⟨254385, by rfl⟩ : syracuseStep 2713445 = 508771) (by norm_num)
theorem B2172781 : Blo 1807605 2172781 := bbase (se 3 (by rfl) ⟨407396, by rfl⟩ : syracuseStep 2172781 = 814793) (by norm_num)
theorem B2713469 : Blo 1807605 2713469 := bbase (se 3 (by rfl) ⟨508775, by rfl⟩ : syracuseStep 2713469 = 1017551) (by norm_num)
theorem B2713493 : Blo 1807605 2713493 := bbase (se 6 (by rfl) ⟨63597, by rfl⟩ : syracuseStep 2713493 = 127195) (by norm_num)
theorem B9160613 : Blo 1807605 9160613 := bbase (se 4 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 9160613 = 1717615) (by norm_num)
theorem B2033581 : Blo 1807605 2033581 := bbase (se 3 (by rfl) ⟨381296, by rfl⟩ : syracuseStep 2033581 = 762593) (by norm_num)
theorem B2713517 : Blo 1807605 2713517 := bbase (se 3 (by rfl) ⟨508784, by rfl⟩ : syracuseStep 2713517 = 1017569) (by norm_num)
theorem B2172853 : Blo 1807605 2172853 := bbase (se 5 (by rfl) ⟨101852, by rfl⟩ : syracuseStep 2172853 = 203705) (by norm_num)
theorem B2713541 : Blo 1807605 2713541 := bbase (se 4 (by rfl) ⟨254394, by rfl⟩ : syracuseStep 2713541 = 508789) (by norm_num)
theorem B2033617 : Blo 1807605 2033617 := bbase (se 2 (by rfl) ⟨762606, by rfl⟩ : syracuseStep 2033617 = 1525213) (by norm_num)
theorem B2713565 : Blo 1807605 2713565 := bbase (se 3 (by rfl) ⟨508793, by rfl⟩ : syracuseStep 2713565 = 1017587) (by norm_num)
theorem B2033653 : Blo 1807605 2033653 := bbase (se 5 (by rfl) ⟨95327, by rfl⟩ : syracuseStep 2033653 = 190655) (by norm_num)
theorem B6105077 : Blo 1807605 6105077 := bbase (se 5 (by rfl) ⟨286175, by rfl⟩ : syracuseStep 6105077 = 572351) (by norm_num)
theorem B2713589 : Blo 1807605 2713589 := bbase (se 5 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 2713589 = 254399) (by norm_num)
theorem B2353153 : Blo 1807605 2353153 := bbase (se 2 (by rfl) ⟨882432, by rfl⟩ : syracuseStep 2353153 = 1764865) (by norm_num)
theorem B3434501 : Blo 1807605 3434501 := bbase (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) (by norm_num)
theorem B2713613 : Blo 1807605 2713613 := bbase (se 3 (by rfl) ⟨508802, by rfl⟩ : syracuseStep 2713613 = 1017605) (by norm_num)
theorem B2033689 : Blo 1807605 2033689 := bbase (se 2 (by rfl) ⟨762633, by rfl⟩ : syracuseStep 2033689 = 1525267) (by norm_num)
theorem B2713637 : Blo 1807605 2713637 := bbase (se 4 (by rfl) ⟨254403, by rfl⟩ : syracuseStep 2713637 = 508807) (by norm_num)
theorem B2172973 : Blo 1807605 2172973 := bbase (se 3 (by rfl) ⟨407432, by rfl⟩ : syracuseStep 2172973 = 814865) (by norm_num)
theorem B4343861 : Blo 1807605 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B2033725 : Blo 1807605 2033725 := bbase (se 3 (by rfl) ⟨381323, by rfl⟩ : syracuseStep 2033725 = 762647) (by norm_num)
theorem B2713661 : Blo 1807605 2713661 := bbase (se 3 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 2713661 = 1017623) (by norm_num)
theorem B2713685 : Blo 1807605 2713685 := bbase (se 8 (by rfl) ⟨15900, by rfl⟩ : syracuseStep 2713685 = 31801) (by norm_num)
theorem B8366165 : Blo 1807605 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B2033761 : Blo 1807605 2033761 := bbase (se 2 (by rfl) ⟨762660, by rfl⟩ : syracuseStep 2033761 = 1525321) (by norm_num)
theorem B2713709 : Blo 1807605 2713709 := bbase (se 3 (by rfl) ⟨508820, by rfl⟩ : syracuseStep 2713709 = 1017641) (by norm_num)
theorem B2033797 : Blo 1807605 2033797 := bbase (se 4 (by rfl) ⟨190668, by rfl⟩ : syracuseStep 2033797 = 381337) (by norm_num)
theorem B2713733 : Blo 1807605 2713733 := bbase (se 4 (by rfl) ⟨254412, by rfl⟩ : syracuseStep 2713733 = 508825) (by norm_num)
theorem B2713757 : Blo 1807605 2713757 := bbase (se 3 (by rfl) ⟨508829, by rfl⟩ : syracuseStep 2713757 = 1017659) (by norm_num)
theorem B3434653 : Blo 1807605 3434653 := bbase (se 3 (by rfl) ⟨643997, by rfl⟩ : syracuseStep 3434653 = 1287995) (by norm_num)
theorem B2033833 : Blo 1807605 2033833 := bbase (se 2 (by rfl) ⟨762687, by rfl⟩ : syracuseStep 2033833 = 1525375) (by norm_num)
theorem B2574509 : Blo 1807605 2574509 := bbase (se 3 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 2574509 = 965441) (by norm_num)
theorem B2713781 : Blo 1807605 2713781 := bbase (se 5 (by rfl) ⟨127208, by rfl⟩ : syracuseStep 2713781 = 254417) (by norm_num)
theorem B2033869 : Blo 1807605 2033869 := bbase (se 3 (by rfl) ⟨381350, by rfl⟩ : syracuseStep 2033869 = 762701) (by norm_num)
theorem B2713805 : Blo 1807605 2713805 := bbase (se 3 (by rfl) ⟨508838, by rfl⟩ : syracuseStep 2713805 = 1017677) (by norm_num)
theorem B2713829 : Blo 1807605 2713829 := bbase (se 4 (by rfl) ⟨254421, by rfl⟩ : syracuseStep 2713829 = 508843) (by norm_num)
theorem B2033905 : Blo 1807605 2033905 := bbase (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) (by norm_num)
theorem B2287865 : Blo 1807605 2287865 := bbase (se 2 (by rfl) ⟨857949, by rfl⟩ : syracuseStep 2287865 = 1715899) (by norm_num)
theorem B2713853 : Blo 1807605 2713853 := bbase (se 3 (by rfl) ⟨508847, by rfl⟩ : syracuseStep 2713853 = 1017695) (by norm_num)
theorem B2033941 : Blo 1807605 2033941 := bbase (se 6 (by rfl) ⟨47670, by rfl⟩ : syracuseStep 2033941 = 95341) (by norm_num)
theorem B2713877 : Blo 1807605 2713877 := bbase (se 6 (by rfl) ⟨63606, by rfl⟩ : syracuseStep 2713877 = 127213) (by norm_num)
theorem B2713901 : Blo 1807605 2713901 := bbase (se 3 (by rfl) ⟨508856, by rfl⟩ : syracuseStep 2713901 = 1017713) (by norm_num)
theorem B2287921 : Blo 1807605 2287921 := bbase (se 2 (by rfl) ⟨857970, by rfl⟩ : syracuseStep 2287921 = 1715941) (by norm_num)
theorem B2033977 : Blo 1807605 2033977 := bbase (se 2 (by rfl) ⟨762741, by rfl⟩ : syracuseStep 2033977 = 1525483) (by norm_num)
theorem B9152837 : Blo 1807605 9152837 := bbase (se 4 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 9152837 = 1716157) (by norm_num)
theorem B2713925 : Blo 1807605 2713925 := bbase (se 4 (by rfl) ⟨254430, by rfl⟩ : syracuseStep 2713925 = 508861) (by norm_num)
theorem B2034013 : Blo 1807605 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B2713949 : Blo 1807605 2713949 := bbase (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) (by norm_num)
theorem B6867301 : Blo 1807605 6867301 := bbase (se 4 (by rfl) ⟨643809, by rfl⟩ : syracuseStep 6867301 = 1287619) (by norm_num)
theorem B2713973 : Blo 1807605 2713973 := bbase (se 5 (by rfl) ⟨127217, by rfl⟩ : syracuseStep 2713973 = 254435) (by norm_num)
theorem B2034049 : Blo 1807605 2034049 := bbase (se 2 (by rfl) ⟨762768, by rfl⟩ : syracuseStep 2034049 = 1525537) (by norm_num)
theorem B2713997 : Blo 1807605 2713997 := bbase (se 3 (by rfl) ⟨508874, by rfl⟩ : syracuseStep 2713997 = 1017749) (by norm_num)
theorem B2288017 : Blo 1807605 2288017 := bbase (se 2 (by rfl) ⟨858006, by rfl⟩ : syracuseStep 2288017 = 1716013) (by norm_num)
theorem B2034085 : Blo 1807605 2034085 := bbase (se 4 (by rfl) ⟨190695, by rfl⟩ : syracuseStep 2034085 = 381391) (by norm_num)
theorem B6105509 : Blo 1807605 6105509 := bbase (se 4 (by rfl) ⟨572391, by rfl⟩ : syracuseStep 6105509 = 1144783) (by norm_num)
theorem B2714021 : Blo 1807605 2714021 := bbase (se 4 (by rfl) ⟨254439, by rfl⟩ : syracuseStep 2714021 = 508879) (by norm_num)
theorem B2173357 : Blo 1807605 2173357 := bbase (se 3 (by rfl) ⟨407504, by rfl⟩ : syracuseStep 2173357 = 815009) (by norm_num)
theorem B2714045 : Blo 1807605 2714045 := bbase (se 3 (by rfl) ⟨508883, by rfl⟩ : syracuseStep 2714045 = 1017767) (by norm_num)
theorem B2034121 : Blo 1807605 2034121 := bbase (se 2 (by rfl) ⟨762795, by rfl⟩ : syracuseStep 2034121 = 1525591) (by norm_num)
theorem B3434957 : Blo 1807605 3434957 := bbase (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) (by norm_num)
theorem B2714069 : Blo 1807605 2714069 := bbase (se 7 (by rfl) ⟨31805, by rfl⟩ : syracuseStep 2714069 = 63611) (by norm_num)
theorem B4344293 : Blo 1807605 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B2034157 : Blo 1807605 2034157 := bbase (se 3 (by rfl) ⟨381404, by rfl⟩ : syracuseStep 2034157 = 762809) (by norm_num)
theorem B2714093 : Blo 1807605 2714093 := bbase (se 3 (by rfl) ⟨508892, by rfl⟩ : syracuseStep 2714093 = 1017785) (by norm_num)
theorem B2714117 : Blo 1807605 2714117 := bbase (se 4 (by rfl) ⟨254448, by rfl⟩ : syracuseStep 2714117 = 508897) (by norm_num)
theorem B2034193 : Blo 1807605 2034193 := bbase (se 2 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 2034193 = 1525645) (by norm_num)
theorem B2714141 : Blo 1807605 2714141 := bbase (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) (by norm_num)
theorem B2034229 : Blo 1807605 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2714165 : Blo 1807605 2714165 := bbase (se 5 (by rfl) ⟨127226, by rfl⟩ : syracuseStep 2714165 = 254453) (by norm_num)
theorem B2288189 : Blo 1807605 2288189 := bbase (se 3 (by rfl) ⟨429035, by rfl⟩ : syracuseStep 2288189 = 858071) (by norm_num)
theorem B2714189 : Blo 1807605 2714189 := bbase (se 3 (by rfl) ⟨508910, by rfl⟩ : syracuseStep 2714189 = 1017821) (by norm_num)
theorem B2034265 : Blo 1807605 2034265 := bbase (se 2 (by rfl) ⟨762849, by rfl⟩ : syracuseStep 2034265 = 1525699) (by norm_num)
theorem B2714213 : Blo 1807605 2714213 := bbase (se 4 (by rfl) ⟨254457, by rfl⟩ : syracuseStep 2714213 = 508915) (by norm_num)
theorem B2288245 : Blo 1807605 2288245 := bbase (se 5 (by rfl) ⟨107261, by rfl⟩ : syracuseStep 2288245 = 214523) (by norm_num)
theorem B2034301 : Blo 1807605 2034301 := bbase (se 3 (by rfl) ⟨381431, by rfl⟩ : syracuseStep 2034301 = 762863) (by norm_num)
theorem B2714237 : Blo 1807605 2714237 := bbase (se 3 (by rfl) ⟨508919, by rfl⟩ : syracuseStep 2714237 = 1017839) (by norm_num)
theorem B6867605 : Blo 1807605 6867605 := bbase (se 6 (by rfl) ⟨160959, by rfl⟩ : syracuseStep 6867605 = 321919) (by norm_num)
theorem B2714261 : Blo 1807605 2714261 := bbase (se 6 (by rfl) ⟨63615, by rfl⟩ : syracuseStep 2714261 = 127231) (by norm_num)
theorem B2034337 : Blo 1807605 2034337 := bbase (se 2 (by rfl) ⟨762876, by rfl⟩ : syracuseStep 2034337 = 1525753) (by norm_num)
theorem B2714285 : Blo 1807605 2714285 := bbase (se 3 (by rfl) ⟨508928, by rfl⟩ : syracuseStep 2714285 = 1017857) (by norm_num)
theorem B2034373 : Blo 1807605 2034373 := bbase (se 4 (by rfl) ⟨190722, by rfl⟩ : syracuseStep 2034373 = 381445) (by norm_num)
theorem B2714309 : Blo 1807605 2714309 := bbase (se 4 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 2714309 = 508933) (by norm_num)
theorem B2288341 : Blo 1807605 2288341 := bbase (se 7 (by rfl) ⟨26816, by rfl⟩ : syracuseStep 2288341 = 53633) (by norm_num)
theorem B9775829 : Blo 1807605 9775829 := bbase (se 7 (by rfl) ⟨114560, by rfl⟩ : syracuseStep 9775829 = 229121) (by norm_num)
theorem B5794517 : Blo 1807605 5794517 := bbase (se 7 (by rfl) ⟨67904, by rfl⟩ : syracuseStep 5794517 = 135809) (by norm_num)
theorem B2476765 : Blo 1807605 2476765 := bbase (se 3 (by rfl) ⟨464393, by rfl⟩ : syracuseStep 2476765 = 928787) (by norm_num)
theorem B2714333 : Blo 1807605 2714333 := bbase (se 3 (by rfl) ⟨508937, by rfl⟩ : syracuseStep 2714333 = 1017875) (by norm_num)
theorem B3304165 : Blo 1807605 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B2034409 : Blo 1807605 2034409 := bbase (se 2 (by rfl) ⟨762903, by rfl⟩ : syracuseStep 2034409 = 1525807) (by norm_num)
theorem B2714357 : Blo 1807605 2714357 := bbase (se 5 (by rfl) ⟨127235, by rfl⟩ : syracuseStep 2714357 = 254471) (by norm_num)
theorem B2034445 : Blo 1807605 2034445 := bbase (se 3 (by rfl) ⟨381458, by rfl⟩ : syracuseStep 2034445 = 762917) (by norm_num)
theorem B2714381 : Blo 1807605 2714381 := bbase (se 3 (by rfl) ⟨508946, by rfl⟩ : syracuseStep 2714381 = 1017893) (by norm_num)
theorem B2714405 : Blo 1807605 2714405 := bbase (se 4 (by rfl) ⟨254475, by rfl⟩ : syracuseStep 2714405 = 508951) (by norm_num)
theorem B2034481 : Blo 1807605 2034481 := bbase (se 2 (by rfl) ⟨762930, by rfl⟩ : syracuseStep 2034481 = 1525861) (by norm_num)
theorem B2034517 : Blo 1807605 2034517 := bbase (se 9 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 2034517 = 11921) (by norm_num)
theorem B6105941 : Blo 1807605 6105941 := bbase (se 9 (by rfl) ⟨17888, by rfl⟩ : syracuseStep 6105941 = 35777) (by norm_num)
theorem B2444141 : Blo 1807605 2444141 := bbase (se 3 (by rfl) ⟨458276, by rfl⟩ : syracuseStep 2444141 = 916553) (by norm_num)
theorem B2034553 : Blo 1807605 2034553 := bbase (se 2 (by rfl) ⟨762957, by rfl⟩ : syracuseStep 2034553 = 1525915) (by norm_num)
theorem B3050365 : Blo 1807605 3050365 := bbase (se 3 (by rfl) ⟨571943, by rfl⟩ : syracuseStep 3050365 = 1143887) (by norm_num)
theorem B2288513 : Blo 1807605 2288513 := bbase (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) (by norm_num)
theorem B2034589 : Blo 1807605 2034589 := bbase (se 3 (by rfl) ⟨381485, by rfl⟩ : syracuseStep 2034589 = 762971) (by norm_num)
theorem B2575261 : Blo 1807605 2575261 := bbase (se 3 (by rfl) ⟨482861, by rfl⟩ : syracuseStep 2575261 = 965723) (by norm_num)
theorem B2288569 : Blo 1807605 2288569 := bbase (se 2 (by rfl) ⟨858213, by rfl⟩ : syracuseStep 2288569 = 1716427) (by norm_num)
theorem B2034625 : Blo 1807605 2034625 := bbase (se 2 (by rfl) ⟨762984, by rfl⟩ : syracuseStep 2034625 = 1525969) (by norm_num)
theorem B3050453 : Blo 1807605 3050453 := bbase (se 7 (by rfl) ⟨35747, by rfl⟩ : syracuseStep 3050453 = 71495) (by norm_num)
theorem B33008597 : Blo 1807605 33008597 := bbase (se 7 (by rfl) ⟨386819, by rfl⟩ : syracuseStep 33008597 = 773639) (by norm_num)
theorem B2034661 : Blo 1807605 2034661 := bbase (se 4 (by rfl) ⟨190749, by rfl⟩ : syracuseStep 2034661 = 381499) (by norm_num)
theorem B10300405 : Blo 1807605 10300405 := bbase (se 5 (by rfl) ⟨482831, by rfl⟩ : syracuseStep 10300405 = 965663) (by norm_num)
theorem B2034697 : Blo 1807605 2034697 := bbase (se 2 (by rfl) ⟨763011, by rfl⟩ : syracuseStep 2034697 = 1526023) (by norm_num)
theorem B2288665 : Blo 1807605 2288665 := bbase (se 2 (by rfl) ⟨858249, by rfl⟩ : syracuseStep 2288665 = 1716499) (by norm_num)
theorem B4344869 : Blo 1807605 4344869 := bbase (se 4 (by rfl) ⟨407331, by rfl⟩ : syracuseStep 4344869 = 814663) (by norm_num)
theorem B2034733 : Blo 1807605 2034733 := bbase (se 3 (by rfl) ⟨381512, by rfl⟩ : syracuseStep 2034733 = 763025) (by norm_num)
theorem B2034769 : Blo 1807605 2034769 := bbase (se 2 (by rfl) ⟨763038, by rfl⟩ : syracuseStep 2034769 = 1526077) (by norm_num)
theorem B3050581 : Blo 1807605 3050581 := bbase (se 8 (by rfl) ⟨17874, by rfl⟩ : syracuseStep 3050581 = 35749) (by norm_num)
theorem B2034805 : Blo 1807605 2034805 := bbase (se 5 (by rfl) ⟨95381, by rfl⟩ : syracuseStep 2034805 = 190763) (by norm_num)
theorem B2034841 : Blo 1807605 2034841 := bbase (se 2 (by rfl) ⟨763065, by rfl⟩ : syracuseStep 2034841 = 1526131) (by norm_num)
theorem B3050669 : Blo 1807605 3050669 := bbase (se 3 (by rfl) ⟨572000, by rfl⟩ : syracuseStep 3050669 = 1144001) (by norm_num)
theorem B2935997 : Blo 1807605 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B2034877 : Blo 1807605 2034877 := bbase (se 3 (by rfl) ⟨381539, by rfl⟩ : syracuseStep 2034877 = 763079) (by norm_num)
theorem B2288837 : Blo 1807605 2288837 := bbase (se 4 (by rfl) ⟨214578, by rfl⟩ : syracuseStep 2288837 = 429157) (by norm_num)
theorem B2034913 : Blo 1807605 2034913 := bbase (se 2 (by rfl) ⟨763092, by rfl⟩ : syracuseStep 2034913 = 1526185) (by norm_num)
theorem B2288893 : Blo 1807605 2288893 := bbase (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) (by norm_num)
theorem B2034949 : Blo 1807605 2034949 := bbase (se 4 (by rfl) ⟨190776, by rfl⟩ : syracuseStep 2034949 = 381553) (by norm_num)
theorem B6106373 : Blo 1807605 6106373 := bbase (se 4 (by rfl) ⟨572472, by rfl⟩ : syracuseStep 6106373 = 1144945) (by norm_num)
theorem B3665173 : Blo 1807605 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B2034985 : Blo 1807605 2034985 := bbase (se 2 (by rfl) ⟨763119, by rfl⟩ : syracuseStep 2034985 = 1526239) (by norm_num)
theorem B3050797 : Blo 1807605 3050797 := bbase (se 3 (by rfl) ⟨572024, by rfl⟩ : syracuseStep 3050797 = 1144049) (by norm_num)
theorem B2035021 : Blo 1807605 2035021 := bbase (se 3 (by rfl) ⟨381566, by rfl⟩ : syracuseStep 2035021 = 763133) (by norm_num)
theorem B2288989 : Blo 1807605 2288989 := bbase (se 3 (by rfl) ⟨429185, by rfl⟩ : syracuseStep 2288989 = 858371) (by norm_num)
theorem B2035057 : Blo 1807605 2035057 := bbase (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) (by norm_num)
theorem B3526021 : Blo 1807605 3526021 := bbase (se 4 (by rfl) ⟨330564, by rfl⟩ : syracuseStep 3526021 = 661129) (by norm_num)
theorem B3050885 : Blo 1807605 3050885 := bbase (se 4 (by rfl) ⟨286020, by rfl⟩ : syracuseStep 3050885 = 572041) (by norm_num)
theorem B3861893 : Blo 1807605 3861893 := bbase (se 4 (by rfl) ⟨362052, by rfl⟩ : syracuseStep 3861893 = 724105) (by norm_num)
theorem B2035093 : Blo 1807605 2035093 := bbase (se 6 (by rfl) ⟨47697, by rfl⟩ : syracuseStep 2035093 = 95395) (by norm_num)
theorem B16494005 : Blo 1807605 16494005 := bbase (se 5 (by rfl) ⟨773156, by rfl⟩ : syracuseStep 16494005 = 1546313) (by norm_num)
theorem B2035129 : Blo 1807605 2035129 := bbase (se 2 (by rfl) ⟨763173, by rfl⟩ : syracuseStep 2035129 = 1526347) (by norm_num)
theorem B2035165 : Blo 1807605 2035165 := bbase (se 3 (by rfl) ⟨381593, by rfl⟩ : syracuseStep 2035165 = 763187) (by norm_num)
theorem B2035201 : Blo 1807605 2035201 := bbase (se 2 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 2035201 = 1526401) (by norm_num)
theorem B3051013 : Blo 1807605 3051013 := bbase (se 4 (by rfl) ⟨286032, by rfl⟩ : syracuseStep 3051013 = 572065) (by norm_num)
theorem B2289161 : Blo 1807605 2289161 := bbase (se 2 (by rfl) ⟨858435, by rfl⟩ : syracuseStep 2289161 = 1716871) (by norm_num)
theorem B3862037 : Blo 1807605 3862037 := bbase (se 6 (by rfl) ⟨90516, by rfl⟩ : syracuseStep 3862037 = 181033) (by norm_num)
theorem B2035237 : Blo 1807605 2035237 := bbase (se 4 (by rfl) ⟨190803, by rfl⟩ : syracuseStep 2035237 = 381607) (by norm_num)
theorem B2289217 : Blo 1807605 2289217 := bbase (se 2 (by rfl) ⟨858456, by rfl⟩ : syracuseStep 2289217 = 1716913) (by norm_num)
theorem B2035273 : Blo 1807605 2035273 := bbase (se 2 (by rfl) ⟨763227, by rfl⟩ : syracuseStep 2035273 = 1526455) (by norm_num)
theorem B9154133 : Blo 1807605 9154133 := bbase (se 8 (by rfl) ⟨53637, by rfl⟩ : syracuseStep 9154133 = 107275) (by norm_num)
theorem B3051101 : Blo 1807605 3051101 := bbase (se 3 (by rfl) ⟨572081, by rfl⟩ : syracuseStep 3051101 = 1144163) (by norm_num)
theorem B2035309 : Blo 1807605 2035309 := bbase (se 3 (by rfl) ⟨381620, by rfl⟩ : syracuseStep 2035309 = 763241) (by norm_num)
theorem B2035345 : Blo 1807605 2035345 := bbase (se 2 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 2035345 = 1526509) (by norm_num)
theorem B2289313 : Blo 1807605 2289313 := bbase (se 2 (by rfl) ⟨858492, by rfl⟩ : syracuseStep 2289313 = 1716985) (by norm_num)
theorem B2035381 : Blo 1807605 2035381 := bbase (se 5 (by rfl) ⟨95408, by rfl⟩ : syracuseStep 2035381 = 190817) (by norm_num)
theorem B2576053 : Blo 1807605 2576053 := bbase (se 5 (by rfl) ⟨120752, by rfl⟩ : syracuseStep 2576053 = 241505) (by norm_num)
theorem B6106805 : Blo 1807605 6106805 := bbase (se 5 (by rfl) ⟨286256, by rfl⟩ : syracuseStep 6106805 = 572513) (by norm_num)
theorem B2035417 : Blo 1807605 2035417 := bbase (se 2 (by rfl) ⟨763281, by rfl⟩ : syracuseStep 2035417 = 1526563) (by norm_num)
theorem B3051229 : Blo 1807605 3051229 := bbase (se 3 (by rfl) ⟨572105, by rfl⟩ : syracuseStep 3051229 = 1144211) (by norm_num)
theorem B4579325 : Blo 1807605 4579325 := bbase (se 3 (by rfl) ⟨858623, by rfl⟩ : syracuseStep 4579325 = 1717247) (by norm_num)
theorem B8359669 : Blo 1807605 8359669 := bbase (se 5 (by rfl) ⟨391859, by rfl⟩ : syracuseStep 8359669 = 783719) (by norm_num)
theorem B2035453 : Blo 1807605 2035453 := bbase (se 3 (by rfl) ⟨381647, by rfl⟩ : syracuseStep 2035453 = 763295) (by norm_num)
theorem B2035489 : Blo 1807605 2035489 := bbase (se 2 (by rfl) ⟨763308, by rfl⟩ : syracuseStep 2035489 = 1526617) (by norm_num)
theorem B4067117 : Blo 1807605 4067117 := bbase (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) (by norm_num)
theorem B3051317 : Blo 1807605 3051317 := bbase (se 5 (by rfl) ⟨143030, by rfl⟩ : syracuseStep 3051317 = 286061) (by norm_num)
theorem B2035525 : Blo 1807605 2035525 := bbase (se 4 (by rfl) ⟨190830, by rfl⟩ : syracuseStep 2035525 = 381661) (by norm_num)
theorem B2289485 : Blo 1807605 2289485 := bbase (se 3 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 2289485 = 858557) (by norm_num)
theorem B5148517 : Blo 1807605 5148517 := bbase (se 4 (by rfl) ⟨482673, by rfl⟩ : syracuseStep 5148517 = 965347) (by norm_num)
theorem B2445157 : Blo 1807605 2445157 := bbase (se 4 (by rfl) ⟨229233, by rfl⟩ : syracuseStep 2445157 = 458467) (by norm_num)
theorem B2035561 : Blo 1807605 2035561 := bbase (se 2 (by rfl) ⟨763335, by rfl⟩ : syracuseStep 2035561 = 1526671) (by norm_num)
theorem B4067189 : Blo 1807605 4067189 := bbase (se 5 (by rfl) ⟨190649, by rfl⟩ : syracuseStep 4067189 = 381299) (by norm_num)
theorem B11587445 : Blo 1807605 11587445 := bbase (se 5 (by rfl) ⟨543161, by rfl⟩ : syracuseStep 11587445 = 1086323) (by norm_num)
theorem B3305333 : Blo 1807605 3305333 := bbase (se 5 (by rfl) ⟨154937, by rfl⟩ : syracuseStep 3305333 = 309875) (by norm_num)
theorem B3862397 : Blo 1807605 3862397 := bbase (se 3 (by rfl) ⟨724199, by rfl⟩ : syracuseStep 3862397 = 1448399) (by norm_num)
theorem B2289541 : Blo 1807605 2289541 := bbase (se 4 (by rfl) ⟨214644, by rfl⟩ : syracuseStep 2289541 = 429289) (by norm_num)
theorem B2035597 : Blo 1807605 2035597 := bbase (se 3 (by rfl) ⟨381674, by rfl⟩ : syracuseStep 2035597 = 763349) (by norm_num)
theorem B2035633 : Blo 1807605 2035633 := bbase (se 2 (by rfl) ⟨763362, by rfl⟩ : syracuseStep 2035633 = 1526725) (by norm_num)
theorem B3051445 : Blo 1807605 3051445 := bbase (se 5 (by rfl) ⟨143036, by rfl⟩ : syracuseStep 3051445 = 286073) (by norm_num)
theorem B4067261 : Blo 1807605 4067261 := bbase (se 3 (by rfl) ⟨762611, by rfl⟩ : syracuseStep 4067261 = 1525223) (by norm_num)
theorem B2035669 : Blo 1807605 2035669 := bbase (se 7 (by rfl) ⟨23855, by rfl⟩ : syracuseStep 2035669 = 47711) (by norm_num)
theorem B2289637 : Blo 1807605 2289637 := bbase (se 4 (by rfl) ⟨214653, by rfl⟩ : syracuseStep 2289637 = 429307) (by norm_num)
theorem B5795813 : Blo 1807605 5795813 := bbase (se 4 (by rfl) ⟨543357, by rfl⟩ : syracuseStep 5795813 = 1086715) (by norm_num)
theorem B2035705 : Blo 1807605 2035705 := bbase (se 2 (by rfl) ⟨763389, by rfl⟩ : syracuseStep 2035705 = 1526779) (by norm_num)
theorem B8245253 : Blo 1807605 8245253 := bbase (se 4 (by rfl) ⟨772992, by rfl⟩ : syracuseStep 8245253 = 1545985) (by norm_num)
theorem B4067333 : Blo 1807605 4067333 := bbase (se 4 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 4067333 = 762625) (by norm_num)
theorem B5148677 : Blo 1807605 5148677 := bbase (se 4 (by rfl) ⟨482688, by rfl⟩ : syracuseStep 5148677 = 965377) (by norm_num)
theorem B2576389 : Blo 1807605 2576389 := bbase (se 4 (by rfl) ⟨241536, by rfl⟩ : syracuseStep 2576389 = 483073) (by norm_num)
theorem B3051533 : Blo 1807605 3051533 := bbase (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) (by norm_num)
theorem B2035741 : Blo 1807605 2035741 := bbase (se 3 (by rfl) ⟨381701, by rfl⟩ : syracuseStep 2035741 = 763403) (by norm_num)
theorem B2445373 : Blo 1807605 2445373 := bbase (se 3 (by rfl) ⟨458507, by rfl⟩ : syracuseStep 2445373 = 917015) (by norm_num)
theorem B2035777 : Blo 1807605 2035777 := bbase (se 2 (by rfl) ⟨763416, by rfl⟩ : syracuseStep 2035777 = 1526833) (by norm_num)
theorem B4067405 : Blo 1807605 4067405 := bbase (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) (by norm_num)
theorem B7729253 : Blo 1807605 7729253 := bbase (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) (by norm_num)
theorem B6107237 : Blo 1807605 6107237 := bbase (se 4 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 6107237 = 1145107) (by norm_num)
theorem B3051661 : Blo 1807605 3051661 := bbase (se 3 (by rfl) ⟨572186, by rfl⟩ : syracuseStep 3051661 = 1144373) (by norm_num)
theorem B2289809 : Blo 1807605 2289809 := bbase (se 2 (by rfl) ⟨858678, by rfl⟩ : syracuseStep 2289809 = 1717357) (by norm_num)
theorem B4067477 : Blo 1807605 4067477 := bbase (se 6 (by rfl) ⟨95331, by rfl⟩ : syracuseStep 4067477 = 190663) (by norm_num)
theorem B2289865 : Blo 1807605 2289865 := bbase (se 2 (by rfl) ⟨858699, by rfl⟩ : syracuseStep 2289865 = 1717399) (by norm_num)
theorem B14110933 : Blo 1807605 14110933 := bbase (se 7 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 14110933 = 330725) (by norm_num)
theorem B4067549 : Blo 1807605 4067549 := bbase (se 3 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 4067549 = 1525331) (by norm_num)
theorem B7721189 : Blo 1807605 7721189 := bbase (se 4 (by rfl) ⟨723861, by rfl⟩ : syracuseStep 7721189 = 1447723) (by norm_num)
theorem B3051749 : Blo 1807605 3051749 := bbase (se 4 (by rfl) ⟨286101, by rfl⟩ : syracuseStep 3051749 = 572203) (by norm_num)
theorem B5148917 : Blo 1807605 5148917 := bbase (se 5 (by rfl) ⟨241355, by rfl⟩ : syracuseStep 5148917 = 482711) (by norm_num)
theorem B2748709 : Blo 1807605 2748709 := bbase (se 4 (by rfl) ⟨257691, by rfl⟩ : syracuseStep 2748709 = 515383) (by norm_num)
theorem B4067621 : Blo 1807605 4067621 := bbase (se 4 (by rfl) ⟨381339, by rfl⟩ : syracuseStep 4067621 = 762679) (by norm_num)
theorem B2289961 : Blo 1807605 2289961 := bbase (se 2 (by rfl) ⟨858735, by rfl⟩ : syracuseStep 2289961 = 1717471) (by norm_num)
theorem B3051877 : Blo 1807605 3051877 := bbase (se 4 (by rfl) ⟨286113, by rfl⟩ : syracuseStep 3051877 = 572227) (by norm_num)
theorem B4067693 : Blo 1807605 4067693 := bbase (se 3 (by rfl) ⟨762692, by rfl⟩ : syracuseStep 4067693 = 1525385) (by norm_num)
theorem B3092845 : Blo 1807605 3092845 := bbase (se 3 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 3092845 = 1159817) (by norm_num)
theorem B4575629 : Blo 1807605 4575629 := bbase (se 3 (by rfl) ⟨857930, by rfl⟩ : syracuseStep 4575629 = 1715861) (by norm_num)
theorem B3666325 : Blo 1807605 3666325 := bbase (se 6 (by rfl) ⟨85929, by rfl⟩ : syracuseStep 3666325 = 171859) (by norm_num)
theorem B4067765 : Blo 1807605 4067765 := bbase (se 5 (by rfl) ⟨190676, by rfl⟩ : syracuseStep 4067765 = 381353) (by norm_num)
theorem B5149109 : Blo 1807605 5149109 := bbase (se 5 (by rfl) ⟨241364, by rfl⟩ : syracuseStep 5149109 = 482729) (by norm_num)
theorem B3051965 : Blo 1807605 3051965 := bbase (se 3 (by rfl) ⟨572243, by rfl⟩ : syracuseStep 3051965 = 1144487) (by norm_num)
theorem B2290133 : Blo 1807605 2290133 := bbase (se 7 (by rfl) ⟨26837, by rfl⟩ : syracuseStep 2290133 = 53675) (by norm_num)
theorem B15454709 : Blo 1807605 15454709 := bbase (se 5 (by rfl) ⟨724439, by rfl⟩ : syracuseStep 15454709 = 1448879) (by norm_num)
theorem B4067837 : Blo 1807605 4067837 := bbase (se 3 (by rfl) ⟨762719, by rfl⟩ : syracuseStep 4067837 = 1525439) (by norm_num)
theorem B7721477 : Blo 1807605 7721477 := bbase (se 4 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 7721477 = 1447777) (by norm_num)
theorem B2290189 : Blo 1807605 2290189 := bbase (se 3 (by rfl) ⟨429410, by rfl⟩ : syracuseStep 2290189 = 858821) (by norm_num)
theorem B9777685 : Blo 1807605 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B3052093 : Blo 1807605 3052093 := bbase (se 3 (by rfl) ⟨572267, by rfl⟩ : syracuseStep 3052093 = 1144535) (by norm_num)
theorem B4067909 : Blo 1807605 4067909 := bbase (se 4 (by rfl) ⟨381366, by rfl⟩ : syracuseStep 4067909 = 762733) (by norm_num)
theorem B15446645 : Blo 1807605 15446645 := bbase (se 5 (by rfl) ⟨724061, by rfl⟩ : syracuseStep 15446645 = 1448123) (by norm_num)
theorem B4067981 : Blo 1807605 4067981 := bbase (se 3 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 4067981 = 1525493) (by norm_num)
theorem B3052181 : Blo 1807605 3052181 := bbase (se 6 (by rfl) ⟨71535, by rfl⟩ : syracuseStep 3052181 = 143071) (by norm_num)
theorem B4068053 : Blo 1807605 4068053 := bbase (se 7 (by rfl) ⟨47672, by rfl⟩ : syracuseStep 4068053 = 95345) (by norm_num)
theorem B6869717 : Blo 1807605 6869717 := bbase (se 7 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 6869717 = 161009) (by norm_num)
theorem B4575973 : Blo 1807605 4575973 := bbase (se 4 (by rfl) ⟨428997, by rfl⟩ : syracuseStep 4575973 = 857995) (by norm_num)
theorem B3863285 : Blo 1807605 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B3052309 : Blo 1807605 3052309 := bbase (se 6 (by rfl) ⟨71538, by rfl⟩ : syracuseStep 3052309 = 143077) (by norm_num)
theorem B4068125 : Blo 1807605 4068125 := bbase (se 3 (by rfl) ⟨762773, by rfl⟩ : syracuseStep 4068125 = 1525547) (by norm_num)
theorem B4576085 : Blo 1807605 4576085 := bbase (se 9 (by rfl) ⟨13406, by rfl⟩ : syracuseStep 4576085 = 26813) (by norm_num)
theorem B2896733 : Blo 1807605 2896733 := bbase (se 3 (by rfl) ⟨543137, by rfl⟩ : syracuseStep 2896733 = 1086275) (by norm_num)
theorem B4068197 : Blo 1807605 4068197 := bbase (se 4 (by rfl) ⟨381393, by rfl⟩ : syracuseStep 4068197 = 762787) (by norm_num)
theorem B9155429 : Blo 1807605 9155429 := bbase (se 4 (by rfl) ⟨858321, by rfl⟩ : syracuseStep 9155429 = 1716643) (by norm_num)
theorem B3052397 : Blo 1807605 3052397 := bbase (se 3 (by rfl) ⟨572324, by rfl⟩ : syracuseStep 3052397 = 1144649) (by norm_num)
theorem B6517637 : Blo 1807605 6517637 := bbase (se 4 (by rfl) ⟨611028, by rfl⟩ : syracuseStep 6517637 = 1222057) (by norm_num)
theorem B4068269 : Blo 1807605 4068269 := bbase (se 3 (by rfl) ⟨762800, by rfl⟩ : syracuseStep 4068269 = 1525601) (by norm_num)
theorem B10302389 : Blo 1807605 10302389 := bbase (se 5 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 10302389 = 965849) (by norm_num)
theorem B3052525 : Blo 1807605 3052525 := bbase (se 3 (by rfl) ⟨572348, by rfl⟩ : syracuseStep 3052525 = 1144697) (by norm_num)
theorem B3863533 : Blo 1807605 3863533 := bbase (se 3 (by rfl) ⟨724412, by rfl⟩ : syracuseStep 3863533 = 1448825) (by norm_num)
theorem B4068341 : Blo 1807605 4068341 := bbase (se 5 (by rfl) ⟨190703, by rfl⟩ : syracuseStep 4068341 = 381407) (by norm_num)
theorem B6870005 : Blo 1807605 6870005 := bbase (se 5 (by rfl) ⟨322031, by rfl⟩ : syracuseStep 6870005 = 644063) (by norm_num)
theorem B4576277 : Blo 1807605 4576277 := bbase (se 6 (by rfl) ⟨107256, by rfl⟩ : syracuseStep 4576277 = 214513) (by norm_num)
theorem B4068413 : Blo 1807605 4068413 := bbase (se 3 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 4068413 = 1525655) (by norm_num)
theorem B2864189 : Blo 1807605 2864189 := bbase (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) (by norm_num)
theorem B3052613 : Blo 1807605 3052613 := bbase (se 4 (by rfl) ⟨286182, by rfl⟩ : syracuseStep 3052613 = 572365) (by norm_num)
theorem B3667021 : Blo 1807605 3667021 := bbase (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) (by norm_num)
theorem B2937973 : Blo 1807605 2937973 := bbase (se 5 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 2937973 = 275435) (by norm_num)
theorem B4068485 : Blo 1807605 4068485 := bbase (se 4 (by rfl) ⟨381420, by rfl⟩ : syracuseStep 4068485 = 762841) (by norm_num)
theorem B3052741 : Blo 1807605 3052741 := bbase (se 4 (by rfl) ⟨286194, by rfl⟩ : syracuseStep 3052741 = 572389) (by norm_num)
theorem B4068557 : Blo 1807605 4068557 := bbase (se 3 (by rfl) ⟨762854, by rfl⟩ : syracuseStep 4068557 = 1525709) (by norm_num)
theorem B7722229 : Blo 1807605 7722229 := bbase (se 5 (by rfl) ⟨361979, by rfl⟩ : syracuseStep 7722229 = 723959) (by norm_num)
theorem B6354197 : Blo 1807605 6354197 := bbase (se 6 (by rfl) ⟨148926, by rfl⟩ : syracuseStep 6354197 = 297853) (by norm_num)
theorem B4068629 : Blo 1807605 4068629 := bbase (se 6 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 4068629 = 190717) (by norm_num)
theorem B3052829 : Blo 1807605 3052829 := bbase (se 3 (by rfl) ⟨572405, by rfl⟩ : syracuseStep 3052829 = 1144811) (by norm_num)
theorem B1930549 : Blo 1807605 1930549 := bbase (se 5 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 1930549 = 180989) (by norm_num)
theorem B4068701 : Blo 1807605 4068701 := bbase (se 3 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 4068701 = 1525763) (by norm_num)
theorem B4576621 : Blo 1807605 4576621 := bbase (se 3 (by rfl) ⟨858116, by rfl⟩ : syracuseStep 4576621 = 1716233) (by norm_num)
theorem B5150101 : Blo 1807605 5150101 := bbase (se 6 (by rfl) ⟨120705, by rfl⟩ : syracuseStep 5150101 = 241411) (by norm_num)
theorem B3052957 : Blo 1807605 3052957 := bbase (se 3 (by rfl) ⟨572429, by rfl⟩ : syracuseStep 3052957 = 1144859) (by norm_num)
theorem B4068773 : Blo 1807605 4068773 := bbase (se 4 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 4068773 = 762895) (by norm_num)
theorem B1930673 : Blo 1807605 1930673 := bbase (se 2 (by rfl) ⟨724002, by rfl⟩ : syracuseStep 1930673 = 1448005) (by norm_num)
theorem B4576733 : Blo 1807605 4576733 := bbase (se 3 (by rfl) ⟨858137, by rfl⟩ : syracuseStep 4576733 = 1716275) (by norm_num)
theorem B3864037 : Blo 1807605 3864037 := bbase (se 4 (by rfl) ⟨362253, by rfl⟩ : syracuseStep 3864037 = 724507) (by norm_num)
theorem B4068845 : Blo 1807605 4068845 := bbase (se 3 (by rfl) ⟨762908, by rfl⟩ : syracuseStep 4068845 = 1525817) (by norm_num)
theorem B3053045 : Blo 1807605 3053045 := bbase (se 5 (by rfl) ⟨143111, by rfl⟩ : syracuseStep 3053045 = 286223) (by norm_num)
theorem B3667493 : Blo 1807605 3667493 := bbase (se 4 (by rfl) ⟨343827, by rfl⟩ : syracuseStep 3667493 = 687655) (by norm_num)
theorem B4068917 : Blo 1807605 4068917 := bbase (se 5 (by rfl) ⟨190730, by rfl⟩ : syracuseStep 4068917 = 381461) (by norm_num)
theorem B4347445 : Blo 1807605 4347445 := bbase (se 5 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 4347445 = 407573) (by norm_num)
theorem B4126277 : Blo 1807605 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B3053173 : Blo 1807605 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B4068989 : Blo 1807605 4068989 := bbase (se 3 (by rfl) ⟨762935, by rfl⟩ : syracuseStep 4068989 = 1525871) (by norm_num)
theorem B4576925 : Blo 1807605 4576925 := bbase (se 3 (by rfl) ⟨858173, by rfl⟩ : syracuseStep 4576925 = 1716347) (by norm_num)
theorem B1930925 : Blo 1807605 1930925 := bbase (se 3 (by rfl) ⟨362048, by rfl⟩ : syracuseStep 1930925 = 724097) (by norm_num)
theorem B4069061 : Blo 1807605 4069061 := bbase (se 4 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 4069061 = 762949) (by norm_num)
theorem B3053261 : Blo 1807605 3053261 := bbase (se 3 (by rfl) ⟨572486, by rfl⟩ : syracuseStep 3053261 = 1144973) (by norm_num)
theorem B4126421 : Blo 1807605 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B4888325 : Blo 1807605 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B2750213 : Blo 1807605 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B2897669 : Blo 1807605 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B4069133 : Blo 1807605 4069133 := bbase (se 3 (by rfl) ⟨762962, by rfl⟩ : syracuseStep 4069133 = 1525925) (by norm_num)
theorem B6100757 : Blo 1807605 6100757 := bbase (se 6 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 6100757 = 285973) (by norm_num)
theorem B17372981 : Blo 1807605 17372981 := bbase (se 5 (by rfl) ⟨814358, by rfl⟩ : syracuseStep 17372981 = 1628717) (by norm_num)
theorem B3053389 : Blo 1807605 3053389 := bbase (se 3 (by rfl) ⟨572510, by rfl⟩ : syracuseStep 3053389 = 1145021) (by norm_num)
theorem B22288213 : Blo 1807605 22288213 := bbase (se 9 (by rfl) ⟨65297, by rfl⟩ : syracuseStep 22288213 = 130595) (by norm_num)
theorem B4069205 : Blo 1807605 4069205 := bbase (se 9 (by rfl) ⟨11921, by rfl⟩ : syracuseStep 4069205 = 23843) (by norm_num)
theorem B2062189 : Blo 1807605 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B5502869 : Blo 1807605 5502869 := bbase (se 6 (by rfl) ⟨128973, by rfl⟩ : syracuseStep 5502869 = 257947) (by norm_num)
theorem B4069277 : Blo 1807605 4069277 := bbase (se 3 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 4069277 = 1525979) (by norm_num)
theorem B3053477 : Blo 1807605 3053477 := bbase (se 4 (by rfl) ⟨286263, by rfl⟩ : syracuseStep 3053477 = 572527) (by norm_num)
theorem B7722965 : Blo 1807605 7722965 := bbase (se 7 (by rfl) ⟨90503, by rfl⟩ : syracuseStep 7722965 = 181007) (by norm_num)
theorem B4069349 : Blo 1807605 4069349 := bbase (se 4 (by rfl) ⟨381501, by rfl⟩ : syracuseStep 4069349 = 763003) (by norm_num)
theorem B4577269 : Blo 1807605 4577269 := bbase (se 5 (by rfl) ⟨214559, by rfl⟩ : syracuseStep 4577269 = 429119) (by norm_num)
theorem B3094517 : Blo 1807605 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B3053605 : Blo 1807605 3053605 := bbase (se 4 (by rfl) ⟨286275, by rfl⟩ : syracuseStep 3053605 = 572551) (by norm_num)
theorem B4069421 : Blo 1807605 4069421 := bbase (se 3 (by rfl) ⟨763016, by rfl⟩ : syracuseStep 4069421 = 1526033) (by norm_num)
theorem B1833025 : Blo 1807605 1833025 := bbase (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) (by norm_num)
theorem B4577381 : Blo 1807605 4577381 := bbase (se 4 (by rfl) ⟨429129, by rfl⟩ : syracuseStep 4577381 = 858259) (by norm_num)
theorem B1931369 : Blo 1807605 1931369 := bbase (se 2 (by rfl) ⟨724263, by rfl⟩ : syracuseStep 1931369 = 1448527) (by norm_num)
theorem B3479669 : Blo 1807605 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B4069493 : Blo 1807605 4069493 := bbase (se 5 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 4069493 = 381515) (by norm_num)
theorem B9156725 : Blo 1807605 9156725 := bbase (se 5 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 9156725 = 858443) (by norm_num)
theorem B3053693 : Blo 1807605 3053693 := bbase (se 3 (by rfl) ⟨572567, by rfl⟩ : syracuseStep 3053693 = 1145135) (by norm_num)
theorem B2062477 : Blo 1807605 2062477 := bbase (se 3 (by rfl) ⟨386714, by rfl⟩ : syracuseStep 2062477 = 773429) (by norm_num)
theorem B4069565 : Blo 1807605 4069565 := bbase (se 3 (by rfl) ⟨763043, by rfl⟩ : syracuseStep 4069565 = 1526087) (by norm_num)
theorem B6101189 : Blo 1807605 6101189 := bbase (se 4 (by rfl) ⟨571986, by rfl⟩ : syracuseStep 6101189 = 1143973) (by norm_num)
theorem B24762581 : Blo 1807605 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B4069637 : Blo 1807605 4069637 := bbase (se 4 (by rfl) ⟨381528, by rfl⟩ : syracuseStep 4069637 = 763057) (by norm_num)
theorem B4577573 : Blo 1807605 4577573 := bbase (se 4 (by rfl) ⟨429147, by rfl⟩ : syracuseStep 4577573 = 858295) (by norm_num)
theorem B6609205 : Blo 1807605 6609205 := bbase (se 5 (by rfl) ⟨309806, by rfl⟩ : syracuseStep 6609205 = 619613) (by norm_num)
theorem B4069709 : Blo 1807605 4069709 := bbase (se 3 (by rfl) ⟨763070, by rfl⟩ : syracuseStep 4069709 = 1526141) (by norm_num)
theorem B23181653 : Blo 1807605 23181653 := bbase (se 10 (by rfl) ⟨33957, by rfl⟩ : syracuseStep 23181653 = 67915) (by norm_num)
theorem B1931617 : Blo 1807605 1931617 := bbase (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) (by norm_num)
theorem B2898317 : Blo 1807605 2898317 := bbase (se 3 (by rfl) ⟨543434, by rfl⟩ : syracuseStep 2898317 = 1086869) (by norm_num)
theorem B4069781 : Blo 1807605 4069781 := bbase (se 6 (by rfl) ⟨95385, by rfl⟩ : syracuseStep 4069781 = 190771) (by norm_num)
theorem B10041781 : Blo 1807605 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B4069853 : Blo 1807605 4069853 := bbase (se 3 (by rfl) ⟨763097, by rfl⟩ : syracuseStep 4069853 = 1526195) (by norm_num)
theorem B5151205 : Blo 1807605 5151205 := bbase (se 4 (by rfl) ⟨482925, by rfl⟩ : syracuseStep 5151205 = 965851) (by norm_num)
theorem B4069925 : Blo 1807605 4069925 := bbase (se 4 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 4069925 = 763111) (by norm_num)
theorem B6863413 : Blo 1807605 6863413 := bbase (se 5 (by rfl) ⟨321722, by rfl⟩ : syracuseStep 6863413 = 643445) (by norm_num)
theorem B4069997 : Blo 1807605 4069997 := bbase (se 3 (by rfl) ⟨763124, by rfl⟩ : syracuseStep 4069997 = 1526249) (by norm_num)
theorem B6101621 : Blo 1807605 6101621 := bbase (se 5 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 6101621 = 572027) (by norm_num)
theorem B4577917 : Blo 1807605 4577917 := bbase (se 3 (by rfl) ⟨858359, by rfl⟩ : syracuseStep 4577917 = 1716719) (by norm_num)
theorem B1833625 : Blo 1807605 1833625 := bbase (se 2 (by rfl) ⟨687609, by rfl⟩ : syracuseStep 1833625 = 1375219) (by norm_num)
theorem B4070069 : Blo 1807605 4070069 := bbase (se 5 (by rfl) ⟨190784, by rfl⟩ : syracuseStep 4070069 = 381569) (by norm_num)
theorem B4578029 : Blo 1807605 4578029 := bbase (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) (by norm_num)
theorem B4070141 : Blo 1807605 4070141 := bbase (se 3 (by rfl) ⟨763151, by rfl⟩ : syracuseStep 4070141 = 1526303) (by norm_num)
theorem B3095309 : Blo 1807605 3095309 := bbase (se 3 (by rfl) ⟨580370, by rfl⟩ : syracuseStep 3095309 = 1160741) (by norm_num)
theorem B1932061 : Blo 1807605 1932061 := bbase (se 3 (by rfl) ⟨362261, by rfl⟩ : syracuseStep 1932061 = 724523) (by norm_num)
theorem B9280325 : Blo 1807605 9280325 := bbase (se 4 (by rfl) ⟨870030, by rfl⟩ : syracuseStep 9280325 = 1740061) (by norm_num)
theorem B4070213 : Blo 1807605 4070213 := bbase (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) (by norm_num)
theorem B13736789 : Blo 1807605 13736789 := bbase (se 9 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 13736789 = 80489) (by norm_num)
theorem B1932121 : Blo 1807605 1932121 := bbase (se 2 (by rfl) ⟨724545, by rfl⟩ : syracuseStep 1932121 = 1449091) (by norm_num)
theorem B6863717 : Blo 1807605 6863717 := bbase (se 4 (by rfl) ⟨643473, by rfl⟩ : syracuseStep 6863717 = 1286947) (by norm_num)
theorem B4070285 : Blo 1807605 4070285 := bbase (se 3 (by rfl) ⟨763178, by rfl⟩ : syracuseStep 4070285 = 1526357) (by norm_num)
theorem B4578221 : Blo 1807605 4578221 := bbase (se 3 (by rfl) ⟨858416, by rfl⟩ : syracuseStep 4578221 = 1716833) (by norm_num)
theorem B4070357 : Blo 1807605 4070357 := bbase (se 7 (by rfl) ⟨47699, by rfl⟩ : syracuseStep 4070357 = 95399) (by norm_num)
theorem B1833941 : Blo 1807605 1833941 := bbase (se 7 (by rfl) ⟨21491, by rfl⟩ : syracuseStep 1833941 = 42983) (by norm_num)
theorem B4070429 : Blo 1807605 4070429 := bbase (se 3 (by rfl) ⟨763205, by rfl⟩ : syracuseStep 4070429 = 1526411) (by norm_num)
theorem B6102053 : Blo 1807605 6102053 := bbase (se 4 (by rfl) ⟨572067, by rfl⟩ : syracuseStep 6102053 = 1144135) (by norm_num)
theorem B10304597 : Blo 1807605 10304597 := bbase (se 8 (by rfl) ⟨60378, by rfl⟩ : syracuseStep 10304597 = 120757) (by norm_num)
theorem B3718237 : Blo 1807605 3718237 := bbase (se 3 (by rfl) ⟨697169, by rfl⟩ : syracuseStep 3718237 = 1394339) (by norm_num)
theorem B4070501 : Blo 1807605 4070501 := bbase (se 4 (by rfl) ⟨381609, by rfl⟩ : syracuseStep 4070501 = 763219) (by norm_num)
theorem B2063485 : Blo 1807605 2063485 := bbase (se 3 (by rfl) ⟨386903, by rfl⟩ : syracuseStep 2063485 = 773807) (by norm_num)
theorem B4070573 : Blo 1807605 4070573 := bbase (se 3 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 4070573 = 1526465) (by norm_num)
theorem B3767501 : Blo 1807605 3767501 := bbase (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) (by norm_num)
theorem B13729013 : Blo 1807605 13729013 := bbase (se 5 (by rfl) ⟨643547, by rfl⟩ : syracuseStep 13729013 = 1287095) (by norm_num)
theorem B4070645 : Blo 1807605 4070645 := bbase (se 5 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 4070645 = 381623) (by norm_num)
theorem B4578565 : Blo 1807605 4578565 := bbase (se 4 (by rfl) ⟨429240, by rfl⟩ : syracuseStep 4578565 = 858481) (by norm_num)
theorem B3259661 : Blo 1807605 3259661 := bbase (se 3 (by rfl) ⟨611186, by rfl⟩ : syracuseStep 3259661 = 1222373) (by norm_num)
theorem B7331093 : Blo 1807605 7331093 := bbase (se 6 (by rfl) ⟨171822, by rfl⟩ : syracuseStep 7331093 = 343645) (by norm_num)
theorem B3480869 : Blo 1807605 3480869 := bbase (se 4 (by rfl) ⟨326331, by rfl⟩ : syracuseStep 3480869 = 652663) (by norm_num)
theorem B4070717 : Blo 1807605 4070717 := bbase (se 3 (by rfl) ⟨763259, by rfl⟩ : syracuseStep 4070717 = 1526519) (by norm_num)
theorem B17390933 : Blo 1807605 17390933 := bbase (se 11 (by rfl) ⟨12737, by rfl⟩ : syracuseStep 17390933 = 25475) (by norm_num)
theorem B4578677 : Blo 1807605 4578677 := bbase (se 5 (by rfl) ⟨214625, by rfl⟩ : syracuseStep 4578677 = 429251) (by norm_num)
theorem B9158021 : Blo 1807605 9158021 := bbase (se 4 (by rfl) ⟨858564, by rfl⟩ : syracuseStep 9158021 = 1717129) (by norm_num)
theorem B4070789 : Blo 1807605 4070789 := bbase (se 4 (by rfl) ⟨381636, by rfl⟩ : syracuseStep 4070789 = 763273) (by norm_num)
theorem B3431821 : Blo 1807605 3431821 := bbase (se 3 (by rfl) ⟨643466, by rfl⟩ : syracuseStep 3431821 = 1286933) (by norm_num)
theorem B4070861 : Blo 1807605 4070861 := bbase (se 3 (by rfl) ⟨763286, by rfl⟩ : syracuseStep 4070861 = 1526573) (by norm_num)
theorem B6102485 : Blo 1807605 6102485 := bbase (se 7 (by rfl) ⟨71513, by rfl⟩ : syracuseStep 6102485 = 143027) (by norm_num)
theorem B22306261 : Blo 1807605 22306261 := bbase (se 7 (by rfl) ⟨261401, by rfl⟩ : syracuseStep 22306261 = 522803) (by norm_num)
theorem B1883633 : Blo 1807605 1883633 := bbase (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) (by norm_num)
theorem B4070933 : Blo 1807605 4070933 := bbase (se 6 (by rfl) ⟨95412, by rfl⟩ : syracuseStep 4070933 = 190825) (by norm_num)
theorem B3431965 : Blo 1807605 3431965 := bbase (se 3 (by rfl) ⟨643493, by rfl⟩ : syracuseStep 3431965 = 1286987) (by norm_num)
theorem B4578869 : Blo 1807605 4578869 := bbase (se 5 (by rfl) ⟨214634, by rfl⟩ : syracuseStep 4578869 = 429269) (by norm_num)
theorem B4071005 : Blo 1807605 4071005 := bbase (se 3 (by rfl) ⟨763313, by rfl⟩ : syracuseStep 4071005 = 1526627) (by norm_num)
theorem B4071077 : Blo 1807605 4071077 := bbase (se 4 (by rfl) ⟨381663, by rfl⟩ : syracuseStep 4071077 = 763327) (by norm_num)
theorem B3432125 : Blo 1807605 3432125 := bbase (se 3 (by rfl) ⟨643523, by rfl⟩ : syracuseStep 3432125 = 1287047) (by norm_num)
theorem B4071149 : Blo 1807605 4071149 := bbase (se 3 (by rfl) ⟨763340, by rfl⟩ : syracuseStep 4071149 = 1526681) (by norm_num)
theorem B35249941 : Blo 1807605 35249941 := bbase (se 6 (by rfl) ⟨826170, by rfl⟩ : syracuseStep 35249941 = 1652341) (by norm_num)
theorem B4071221 : Blo 1807605 4071221 := bbase (se 5 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 4071221 = 381677) (by norm_num)
theorem B3432269 : Blo 1807605 3432269 := bbase (se 3 (by rfl) ⟨643550, by rfl⟩ : syracuseStep 3432269 = 1287101) (by norm_num)
theorem B46333781 : Blo 1807605 46333781 := bbase (se 9 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 46333781 = 271487) (by norm_num)
theorem B4071293 : Blo 1807605 4071293 := bbase (se 3 (by rfl) ⟨763367, by rfl⟩ : syracuseStep 4071293 = 1526735) (by norm_num)
theorem B2711429 : Blo 1807605 2711429 := bbase (se 4 (by rfl) ⟨254196, by rfl⟩ : syracuseStep 2711429 = 508393) (by norm_num)
theorem B5791621 : Blo 1807605 5791621 := bbase (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) (by norm_num)
theorem B6102917 : Blo 1807605 6102917 := bbase (se 4 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 6102917 = 1144297) (by norm_num)
theorem B4579213 : Blo 1807605 4579213 := bbase (se 3 (by rfl) ⟨858602, by rfl⟩ : syracuseStep 4579213 = 1717205) (by norm_num)
theorem B2711453 : Blo 1807605 2711453 := bbase (se 3 (by rfl) ⟨508397, by rfl⟩ : syracuseStep 2711453 = 1016795) (by norm_num)
theorem B2711477 : Blo 1807605 2711477 := bbase (se 5 (by rfl) ⟨127100, by rfl⟩ : syracuseStep 2711477 = 254201) (by norm_num)
theorem B5152709 : Blo 1807605 5152709 := bbase (se 4 (by rfl) ⟨483066, by rfl⟩ : syracuseStep 5152709 = 966133) (by norm_num)
theorem B4071365 : Blo 1807605 4071365 := bbase (se 4 (by rfl) ⟨381690, by rfl⟩ : syracuseStep 4071365 = 763381) (by norm_num)
theorem B2711501 : Blo 1807605 2711501 := bbase (se 3 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 2711501 = 1016813) (by norm_num)
theorem B2711525 : Blo 1807605 2711525 := bbase (se 4 (by rfl) ⟨254205, by rfl⟩ : syracuseStep 2711525 = 508411) (by norm_num)
theorem B2711549 : Blo 1807605 2711549 := bbase (se 3 (by rfl) ⟨508415, by rfl⟩ : syracuseStep 2711549 = 1016831) (by norm_num)
theorem B3137537 : Blo 1807605 3137537 := bstep (se 2 (by rfl) ⟨1176576, by rfl⟩ : syracuseStep 3137537 = 2353153) B2353153
theorem B5496835 : Blo 1807605 5496835 := bstep (se 1 (by rfl) ⟨4122626, by rfl⟩ : syracuseStep 5496835 = 8245253) B8245253
theorem B2711555 : Blo 1807605 2711555 := bstep (se 1 (by rfl) ⟨2033666, by rfl⟩ : syracuseStep 2711555 = 4067333) B4067333
theorem B3432451 : Blo 1807605 3432451 := bstep (se 1 (by rfl) ⟨2574338, by rfl⟩ : syracuseStep 3432451 = 5148677) B5148677
theorem B9158669 : Blo 1807605 9158669 := bstep (se 3 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 9158669 = 3434501) B3434501
theorem B2711585 : Blo 1807605 2711585 := bstep (se 2 (by rfl) ⟨1016844, by rfl⟩ : syracuseStep 2711585 = 2033689) B2033689
theorem B4071473 : Blo 1807605 4071473 := bstep (se 2 (by rfl) ⟨1526802, by rfl⟩ : syracuseStep 4071473 = 3053605) B3053605
theorem B2711603 : Blo 1807605 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B5152835 : Blo 1807605 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B4071491 : Blo 1807605 4071491 := bstep (se 1 (by rfl) ⟨3053618, by rfl⟩ : syracuseStep 4071491 = 6107237) B6107237
theorem B2711633 : Blo 1807605 2711633 := bstep (se 2 (by rfl) ⟨1016862, by rfl⟩ : syracuseStep 2711633 = 2033725) B2033725
theorem B3260497 : Blo 1807605 3260497 := bstep (se 2 (by rfl) ⟨1222686, by rfl⟩ : syracuseStep 3260497 = 2445373) B2445373
theorem B2711651 : Blo 1807605 2711651 := bstep (se 1 (by rfl) ⟨2033738, by rfl⟩ : syracuseStep 2711651 = 4067477) B4067477
theorem B2711681 : Blo 1807605 2711681 := bstep (se 2 (by rfl) ⟨1016880, by rfl⟩ : syracuseStep 2711681 = 2033761) B2033761
theorem B2711699 : Blo 1807605 2711699 := bstep (se 1 (by rfl) ⟨2033774, by rfl⟩ : syracuseStep 2711699 = 4067549) B4067549
theorem B3432611 : Blo 1807605 3432611 := bstep (se 1 (by rfl) ⟨2574458, by rfl⟩ : syracuseStep 3432611 = 5148917) B5148917
theorem B2711729 : Blo 1807605 2711729 := bstep (se 2 (by rfl) ⟨1016898, by rfl⟩ : syracuseStep 2711729 = 2033797) B2033797
theorem B2711747 : Blo 1807605 2711747 := bstep (se 1 (by rfl) ⟨2033810, by rfl⟩ : syracuseStep 2711747 = 4067621) B4067621
theorem B4579537 : Blo 1807605 4579537 := bstep (se 2 (by rfl) ⟨1717326, by rfl⟩ : syracuseStep 4579537 = 3434653) B3434653
theorem B2711777 : Blo 1807605 2711777 := bstep (se 2 (by rfl) ⟨1016916, by rfl⟩ : syracuseStep 2711777 = 2033833) B2033833
theorem B2711795 : Blo 1807605 2711795 := bstep (se 1 (by rfl) ⟨2033846, by rfl⟩ : syracuseStep 2711795 = 4067693) B4067693
theorem B2711825 : Blo 1807605 2711825 := bstep (se 2 (by rfl) ⟨1016934, by rfl⟩ : syracuseStep 2711825 = 2033869) B2033869
theorem B2711843 : Blo 1807605 2711843 := bstep (se 1 (by rfl) ⟨2033882, by rfl⟩ : syracuseStep 2711843 = 4067765) B4067765
theorem B2711873 : Blo 1807605 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B2711891 : Blo 1807605 2711891 := bstep (se 1 (by rfl) ⟨2033918, by rfl⟩ : syracuseStep 2711891 = 4067837) B4067837
theorem B2711921 : Blo 1807605 2711921 := bstep (se 2 (by rfl) ⟨1016970, by rfl⟩ : syracuseStep 2711921 = 2033941) B2033941
theorem B2711939 : Blo 1807605 2711939 := bstep (se 1 (by rfl) ⟨2033954, by rfl⟩ : syracuseStep 2711939 = 4067909) B4067909
theorem B2711969 : Blo 1807605 2711969 := bstep (se 2 (by rfl) ⟨1016988, by rfl⟩ : syracuseStep 2711969 = 2033977) B2033977
theorem B10297763 : Blo 1807605 10297763 := bstep (se 1 (by rfl) ⟨7723322, by rfl⟩ : syracuseStep 10297763 = 15446645) B15446645
theorem B9781667 : Blo 1807605 9781667 := bstep (se 1 (by rfl) ⟨7336250, by rfl⟩ : syracuseStep 9781667 = 14672501) B14672501
theorem B2711987 : Blo 1807605 2711987 := bstep (se 1 (by rfl) ⟨2033990, by rfl⟩ : syracuseStep 2711987 = 4067981) B4067981
theorem B6865357 : Blo 1807605 6865357 := bstep (se 3 (by rfl) ⟨1287254, by rfl⟩ : syracuseStep 6865357 = 2574509) B2574509
theorem B2712017 : Blo 1807605 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B2712035 : Blo 1807605 2712035 := bstep (se 1 (by rfl) ⟨2034026, by rfl⟩ : syracuseStep 2712035 = 4068053) B4068053
theorem B4579811 : Blo 1807605 4579811 := bstep (se 1 (by rfl) ⟨3434858, by rfl⟩ : syracuseStep 4579811 = 6869717) B6869717
theorem B2712065 : Blo 1807605 2712065 := bstep (se 2 (by rfl) ⟨1017024, by rfl⟩ : syracuseStep 2712065 = 2034049) B2034049
theorem B6103565 : Blo 1807605 6103565 := bstep (se 3 (by rfl) ⟨1144418, by rfl⟩ : syracuseStep 6103565 = 2288837) B2288837
theorem B2712083 : Blo 1807605 2712083 := bstep (se 1 (by rfl) ⟨2034062, by rfl⟩ : syracuseStep 2712083 = 4068125) B4068125
theorem B2712113 : Blo 1807605 2712113 := bstep (se 2 (by rfl) ⟨1017042, by rfl⟩ : syracuseStep 2712113 = 2034085) B2034085
theorem B2712131 : Blo 1807605 2712131 := bstep (se 1 (by rfl) ⟨2034098, by rfl⟩ : syracuseStep 2712131 = 4068197) B4068197
theorem B6103619 : Blo 1807605 6103619 := bstep (se 1 (by rfl) ⟨4577714, by rfl⟩ : syracuseStep 6103619 = 9155429) B9155429
theorem B2712161 : Blo 1807605 2712161 := bstep (se 2 (by rfl) ⟨1017060, by rfl⟩ : syracuseStep 2712161 = 2034121) B2034121
theorem B2712179 : Blo 1807605 2712179 := bstep (se 1 (by rfl) ⟨2034134, by rfl⟩ : syracuseStep 2712179 = 4068269) B4068269
theorem B2712209 : Blo 1807605 2712209 := bstep (se 2 (by rfl) ⟨1017078, by rfl⟩ : syracuseStep 2712209 = 2034157) B2034157
theorem B2712227 : Blo 1807605 2712227 := bstep (se 1 (by rfl) ⟨2034170, by rfl⟩ : syracuseStep 2712227 = 4068341) B4068341
theorem B4580003 : Blo 1807605 4580003 := bstep (se 1 (by rfl) ⟨3435002, by rfl⟩ : syracuseStep 4580003 = 6870005) B6870005
theorem B2712257 : Blo 1807605 2712257 := bstep (se 2 (by rfl) ⟨1017096, by rfl⟩ : syracuseStep 2712257 = 2034193) B2034193
theorem B8692429 : Blo 1807605 8692429 := bstep (se 3 (by rfl) ⟨1629830, by rfl⟩ : syracuseStep 8692429 = 3259661) B3259661
theorem B2712275 : Blo 1807605 2712275 := bstep (se 1 (by rfl) ⟨2034206, by rfl⟩ : syracuseStep 2712275 = 4068413) B4068413
theorem B1909459 : Blo 1807605 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B9151217 : Blo 1807605 9151217 := bstep (se 2 (by rfl) ⟨3431706, by rfl⟩ : syracuseStep 9151217 = 6863413) B6863413
theorem B2712305 : Blo 1807605 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B2712323 : Blo 1807605 2712323 := bstep (se 1 (by rfl) ⟨2034242, by rfl⟩ : syracuseStep 2712323 = 4068485) B4068485
theorem B2712353 : Blo 1807605 2712353 := bstep (se 2 (by rfl) ⟨1017132, by rfl⟩ : syracuseStep 2712353 = 2034265) B2034265
theorem B2712371 : Blo 1807605 2712371 := bstep (se 1 (by rfl) ⟨2034278, by rfl⟩ : syracuseStep 2712371 = 4068557) B4068557
theorem B2712401 : Blo 1807605 2712401 := bstep (se 2 (by rfl) ⟨1017150, by rfl⟩ : syracuseStep 2712401 = 2034301) B2034301
theorem B6103889 : Blo 1807605 6103889 := bstep (se 2 (by rfl) ⟨2288958, by rfl⟩ : syracuseStep 6103889 = 4577917) B4577917
theorem B4236131 : Blo 1807605 4236131 := bstep (se 1 (by rfl) ⟨3177098, by rfl⟩ : syracuseStep 4236131 = 6354197) B6354197
theorem B2712419 : Blo 1807605 2712419 := bstep (se 1 (by rfl) ⟨2034314, by rfl⟩ : syracuseStep 2712419 = 4068629) B4068629
theorem B2712449 : Blo 1807605 2712449 := bstep (se 2 (by rfl) ⟨1017168, by rfl⟩ : syracuseStep 2712449 = 2034337) B2034337
theorem B2712467 : Blo 1807605 2712467 := bstep (se 1 (by rfl) ⟨2034350, by rfl⟩ : syracuseStep 2712467 = 4068701) B4068701
theorem B2712497 : Blo 1807605 2712497 := bstep (se 2 (by rfl) ⟨1017186, by rfl⟩ : syracuseStep 2712497 = 2034373) B2034373
theorem B2712515 : Blo 1807605 2712515 := bstep (se 1 (by rfl) ⟨2034386, by rfl⟩ : syracuseStep 2712515 = 4068773) B4068773
theorem B3302353 : Blo 1807605 3302353 := bstep (se 2 (by rfl) ⟨1238382, by rfl⟩ : syracuseStep 3302353 = 2476765) B2476765
theorem B2712545 : Blo 1807605 2712545 := bstep (se 2 (by rfl) ⟨1017204, by rfl⟩ : syracuseStep 2712545 = 2034409) B2034409
theorem B2712563 : Blo 1807605 2712563 := bstep (se 1 (by rfl) ⟨2034422, by rfl⟩ : syracuseStep 2712563 = 4068845) B4068845
theorem B2712593 : Blo 1807605 2712593 := bstep (se 2 (by rfl) ⟨1017222, by rfl⟩ : syracuseStep 2712593 = 2034445) B2034445
theorem B2712611 : Blo 1807605 2712611 := bstep (se 1 (by rfl) ⟨2034458, by rfl⟩ : syracuseStep 2712611 = 4068917) B4068917
theorem B2712641 : Blo 1807605 2712641 := bstep (se 2 (by rfl) ⟨1017240, by rfl⟩ : syracuseStep 2712641 = 2034481) B2034481
theorem B2712659 : Blo 1807605 2712659 := bstep (se 1 (by rfl) ⟨2034494, by rfl⟩ : syracuseStep 2712659 = 4068989) B4068989
theorem B2712689 : Blo 1807605 2712689 := bstep (se 2 (by rfl) ⟨1017258, by rfl⟩ : syracuseStep 2712689 = 2034517) B2034517
theorem B2712707 : Blo 1807605 2712707 := bstep (se 1 (by rfl) ⟨2034530, by rfl⟩ : syracuseStep 2712707 = 4069061) B4069061
theorem B13730957 : Blo 1807605 13730957 := bstep (se 3 (by rfl) ⟨2574554, by rfl⟩ : syracuseStep 13730957 = 5149109) B5149109
theorem B2712737 : Blo 1807605 2712737 := bstep (se 2 (by rfl) ⟨1017276, by rfl⟩ : syracuseStep 2712737 = 2034553) B2034553
theorem B2712755 : Blo 1807605 2712755 := bstep (se 1 (by rfl) ⟨2034566, by rfl⟩ : syracuseStep 2712755 = 4069133) B4069133
theorem B2712785 : Blo 1807605 2712785 := bstep (se 2 (by rfl) ⟨1017294, by rfl⟩ : syracuseStep 2712785 = 2034589) B2034589
theorem B3433681 : Blo 1807605 3433681 := bstep (se 2 (by rfl) ⟨1287630, by rfl⟩ : syracuseStep 3433681 = 2575261) B2575261
theorem B6866147 : Blo 1807605 6866147 := bstep (se 1 (by rfl) ⟨5149610, by rfl⟩ : syracuseStep 6866147 = 10299221) B10299221
theorem B2712803 : Blo 1807605 2712803 := bstep (se 1 (by rfl) ⟨2034602, by rfl⟩ : syracuseStep 2712803 = 4069205) B4069205
theorem B2712833 : Blo 1807605 2712833 := bstep (se 2 (by rfl) ⟨1017312, by rfl⟩ : syracuseStep 2712833 = 2034625) B2034625
theorem B11584781 : Blo 1807605 11584781 := bstep (se 3 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 11584781 = 4344293) B4344293
theorem B2712851 : Blo 1807605 2712851 := bstep (se 1 (by rfl) ⟨2034638, by rfl⟩ : syracuseStep 2712851 = 4069277) B4069277
theorem B2712881 : Blo 1807605 2712881 := bstep (se 2 (by rfl) ⟨1017330, by rfl⟩ : syracuseStep 2712881 = 2034661) B2034661
theorem B2712899 : Blo 1807605 2712899 := bstep (se 1 (by rfl) ⟨2034674, by rfl⟩ : syracuseStep 2712899 = 4069349) B4069349
theorem B2712929 : Blo 1807605 2712929 := bstep (se 2 (by rfl) ⟨1017348, by rfl⟩ : syracuseStep 2712929 = 2034697) B2034697
theorem B6104429 : Blo 1807605 6104429 := bstep (se 3 (by rfl) ⟨1144580, by rfl⟩ : syracuseStep 6104429 = 2289161) B2289161
theorem B2712947 : Blo 1807605 2712947 := bstep (se 1 (by rfl) ⟨2034710, by rfl⟩ : syracuseStep 2712947 = 4069421) B4069421
theorem B10298765 : Blo 1807605 10298765 := bstep (se 3 (by rfl) ⟨1931018, by rfl⟩ : syracuseStep 10298765 = 3862037) B3862037
theorem B2712977 : Blo 1807605 2712977 := bstep (se 2 (by rfl) ⟨1017366, by rfl⟩ : syracuseStep 2712977 = 2034733) B2034733
theorem B2319779 : Blo 1807605 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B2712995 : Blo 1807605 2712995 := bstep (se 1 (by rfl) ⟨2034746, by rfl⟩ : syracuseStep 2712995 = 4069493) B4069493
theorem B6104483 : Blo 1807605 6104483 := bstep (se 1 (by rfl) ⟨4578362, by rfl⟩ : syracuseStep 6104483 = 9156725) B9156725
theorem B2713025 : Blo 1807605 2713025 := bstep (se 2 (by rfl) ⟨1017384, by rfl⟩ : syracuseStep 2713025 = 2034769) B2034769
theorem B4957649 : Blo 1807605 4957649 := bstep (se 2 (by rfl) ⟨1859118, by rfl⟩ : syracuseStep 4957649 = 3718237) B3718237
theorem B2713043 : Blo 1807605 2713043 := bstep (se 1 (by rfl) ⟨2034782, by rfl⟩ : syracuseStep 2713043 = 4069565) B4069565
theorem B16508387 : Blo 1807605 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B2713073 : Blo 1807605 2713073 := bstep (se 2 (by rfl) ⟨1017402, by rfl⟩ : syracuseStep 2713073 = 2034805) B2034805
theorem B3917297 : Blo 1807605 3917297 := bstep (se 2 (by rfl) ⟨1468986, by rfl⟩ : syracuseStep 3917297 = 2937973) B2937973
theorem B2713091 : Blo 1807605 2713091 := bstep (se 1 (by rfl) ⟨2034818, by rfl⟩ : syracuseStep 2713091 = 4069637) B4069637
theorem B2713121 : Blo 1807605 2713121 := bstep (se 2 (by rfl) ⟨1017420, by rfl⟩ : syracuseStep 2713121 = 2034841) B2034841
theorem B2713139 : Blo 1807605 2713139 := bstep (se 1 (by rfl) ⟨2034854, by rfl⟩ : syracuseStep 2713139 = 4069709) B4069709
theorem B2713169 : Blo 1807605 2713169 := bstep (se 2 (by rfl) ⟨1017438, by rfl⟩ : syracuseStep 2713169 = 2034877) B2034877
theorem B2713187 : Blo 1807605 2713187 := bstep (se 1 (by rfl) ⟨2034890, by rfl⟩ : syracuseStep 2713187 = 4069781) B4069781
theorem B2713217 : Blo 1807605 2713217 := bstep (se 2 (by rfl) ⟨1017456, by rfl⟩ : syracuseStep 2713217 = 2034913) B2034913
theorem B32990861 : Blo 1807605 32990861 := bstep (se 3 (by rfl) ⟨6185786, by rfl⟩ : syracuseStep 32990861 = 12371573) B12371573
theorem B2713235 : Blo 1807605 2713235 := bstep (se 1 (by rfl) ⟨2034926, by rfl⟩ : syracuseStep 2713235 = 4069853) B4069853
theorem B6104753 : Blo 1807605 6104753 := bstep (se 2 (by rfl) ⟨2289282, by rfl⟩ : syracuseStep 6104753 = 4578565) B4578565
theorem B2713265 : Blo 1807605 2713265 := bstep (se 2 (by rfl) ⟨1017474, by rfl⟩ : syracuseStep 2713265 = 2034949) B2034949
theorem B2713283 : Blo 1807605 2713283 := bstep (se 1 (by rfl) ⟨2034962, by rfl⟩ : syracuseStep 2713283 = 4069925) B4069925
theorem B2713313 : Blo 1807605 2713313 := bstep (se 2 (by rfl) ⟨1017492, by rfl⟩ : syracuseStep 2713313 = 2034985) B2034985
theorem B2574065 : Blo 1807605 2574065 := bstep (se 2 (by rfl) ⟨965274, by rfl⟩ : syracuseStep 2574065 = 1930549) B1930549
theorem B2713331 : Blo 1807605 2713331 := bstep (se 1 (by rfl) ⟨2034998, by rfl⟩ : syracuseStep 2713331 = 4069997) B4069997
theorem B2713361 : Blo 1807605 2713361 := bstep (se 2 (by rfl) ⟨1017510, by rfl⟩ : syracuseStep 2713361 = 2035021) B2035021
theorem B2713379 : Blo 1807605 2713379 := bstep (se 1 (by rfl) ⟨2035034, by rfl⟩ : syracuseStep 2713379 = 4070069) B4070069
theorem B2713409 : Blo 1807605 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B2713427 : Blo 1807605 2713427 := bstep (se 1 (by rfl) ⟨2035070, by rfl⟩ : syracuseStep 2713427 = 4070141) B4070141
theorem B6866801 : Blo 1807605 6866801 := bstep (se 2 (by rfl) ⟨2575050, by rfl⟩ : syracuseStep 6866801 = 5150101) B5150101
theorem B2713457 : Blo 1807605 2713457 := bstep (se 2 (by rfl) ⟨1017546, by rfl⟩ : syracuseStep 2713457 = 2035093) B2035093
theorem B6186883 : Blo 1807605 6186883 := bstep (se 1 (by rfl) ⟨4640162, by rfl⟩ : syracuseStep 6186883 = 9280325) B9280325
theorem B2713475 : Blo 1807605 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B15452045 : Blo 1807605 15452045 := bstep (se 3 (by rfl) ⟨2897258, by rfl⟩ : syracuseStep 15452045 = 5794517) B5794517
theorem B11003789 : Blo 1807605 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B2713505 : Blo 1807605 2713505 := bstep (se 2 (by rfl) ⟨1017564, by rfl⟩ : syracuseStep 2713505 = 2035129) B2035129
theorem B2713523 : Blo 1807605 2713523 := bstep (se 1 (by rfl) ⟨2035142, by rfl⟩ : syracuseStep 2713523 = 4070285) B4070285
theorem B2713553 : Blo 1807605 2713553 := bstep (se 2 (by rfl) ⟨1017582, by rfl⟩ : syracuseStep 2713553 = 2035165) B2035165
theorem B2033635 : Blo 1807605 2033635 := bstep (se 1 (by rfl) ⟨1525226, by rfl⟩ : syracuseStep 2033635 = 3050453) B3050453
theorem B2713571 : Blo 1807605 2713571 := bstep (se 1 (by rfl) ⟨2035178, by rfl⟩ : syracuseStep 2713571 = 4070357) B4070357
theorem B22005731 : Blo 1807605 22005731 := bstep (se 1 (by rfl) ⟨16504298, by rfl⟩ : syracuseStep 22005731 = 33008597) B33008597
theorem B5793773 : Blo 1807605 5793773 := bstep (se 3 (by rfl) ⟨1086332, by rfl⟩ : syracuseStep 5793773 = 2172665) B2172665
theorem B2713601 : Blo 1807605 2713601 := bstep (se 2 (by rfl) ⟨1017600, by rfl⟩ : syracuseStep 2713601 = 2035201) B2035201
theorem B7333901 : Blo 1807605 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B2713619 : Blo 1807605 2713619 := bstep (se 1 (by rfl) ⟨2035214, by rfl⟩ : syracuseStep 2713619 = 4070429) B4070429
theorem B2713649 : Blo 1807605 2713649 := bstep (se 2 (by rfl) ⟨1017618, by rfl⟩ : syracuseStep 2713649 = 2035237) B2035237
theorem B2713667 : Blo 1807605 2713667 := bstep (se 1 (by rfl) ⟨2035250, by rfl⟩ : syracuseStep 2713667 = 4070501) B4070501
theorem B2713697 : Blo 1807605 2713697 := bstep (se 2 (by rfl) ⟨1017636, by rfl⟩ : syracuseStep 2713697 = 2035273) B2035273
theorem B2033779 : Blo 1807605 2033779 := bstep (se 1 (by rfl) ⟨1525334, by rfl⟩ : syracuseStep 2033779 = 3050669) B3050669
theorem B2713715 : Blo 1807605 2713715 := bstep (se 1 (by rfl) ⟨2035286, by rfl⟩ : syracuseStep 2713715 = 4070573) B4070573
theorem B2713745 : Blo 1807605 2713745 := bstep (se 2 (by rfl) ⟨1017654, by rfl⟩ : syracuseStep 2713745 = 2035309) B2035309
theorem B9152675 : Blo 1807605 9152675 := bstep (se 1 (by rfl) ⟨6864506, by rfl⟩ : syracuseStep 9152675 = 13729013) B13729013
theorem B2713763 : Blo 1807605 2713763 := bstep (se 1 (by rfl) ⟨2035322, by rfl⟩ : syracuseStep 2713763 = 4070645) B4070645
theorem B2713793 : Blo 1807605 2713793 := bstep (se 2 (by rfl) ⟨1017672, by rfl⟩ : syracuseStep 2713793 = 2035345) B2035345
theorem B2320579 : Blo 1807605 2320579 := bstep (se 1 (by rfl) ⟨1740434, by rfl⟩ : syracuseStep 2320579 = 3480869) B3480869
theorem B6105293 : Blo 1807605 6105293 := bstep (se 3 (by rfl) ⟨1144742, by rfl⟩ : syracuseStep 6105293 = 2289485) B2289485
theorem B2713811 : Blo 1807605 2713811 := bstep (se 1 (by rfl) ⟨2035358, by rfl⟩ : syracuseStep 2713811 = 4070717) B4070717
theorem B11593955 : Blo 1807605 11593955 := bstep (se 1 (by rfl) ⟨8695466, by rfl⟩ : syracuseStep 11593955 = 17390933) B17390933
theorem B2713841 : Blo 1807605 2713841 := bstep (se 2 (by rfl) ⟨1017690, by rfl⟩ : syracuseStep 2713841 = 2035381) B2035381
theorem B3434737 : Blo 1807605 3434737 := bstep (se 2 (by rfl) ⟨1288026, by rfl⟩ : syracuseStep 3434737 = 2576053) B2576053
theorem B2033923 : Blo 1807605 2033923 := bstep (se 1 (by rfl) ⟨1525442, by rfl⟩ : syracuseStep 2033923 = 3050885) B3050885
theorem B2574595 : Blo 1807605 2574595 := bstep (se 1 (by rfl) ⟨1930946, by rfl⟩ : syracuseStep 2574595 = 3861893) B3861893
theorem B6105347 : Blo 1807605 6105347 := bstep (se 1 (by rfl) ⟨4579010, by rfl⟩ : syracuseStep 6105347 = 9158021) B9158021
theorem B2713859 : Blo 1807605 2713859 := bstep (se 1 (by rfl) ⟨2035394, by rfl⟩ : syracuseStep 2713859 = 4070789) B4070789
theorem B2713889 : Blo 1807605 2713889 := bstep (se 2 (by rfl) ⟨1017708, by rfl⟩ : syracuseStep 2713889 = 2035417) B2035417
theorem B10996003 : Blo 1807605 10996003 := bstep (se 1 (by rfl) ⟨8247002, by rfl⟩ : syracuseStep 10996003 = 16494005) B16494005
theorem B2713907 : Blo 1807605 2713907 := bstep (se 1 (by rfl) ⟨2035430, by rfl⟩ : syracuseStep 2713907 = 4070861) B4070861
theorem B2713937 : Blo 1807605 2713937 := bstep (se 2 (by rfl) ⟨1017726, by rfl⟩ : syracuseStep 2713937 = 2035453) B2035453
theorem B2713955 : Blo 1807605 2713955 := bstep (se 1 (by rfl) ⟨2035466, by rfl⟩ : syracuseStep 2713955 = 4070933) B4070933
theorem B46999921 : Blo 1807605 46999921 := bstep (se 2 (by rfl) ⟨17624970, by rfl⟩ : syracuseStep 46999921 = 35249941) B35249941
theorem B2713985 : Blo 1807605 2713985 := bstep (se 2 (by rfl) ⟨1017744, by rfl⟩ : syracuseStep 2713985 = 2035489) B2035489
theorem B2034067 : Blo 1807605 2034067 := bstep (se 1 (by rfl) ⟨1525550, by rfl⟩ : syracuseStep 2034067 = 3051101) B3051101
theorem B2714003 : Blo 1807605 2714003 := bstep (se 1 (by rfl) ⟨2035502, by rfl⟩ : syracuseStep 2714003 = 4071005) B4071005
theorem B2714033 : Blo 1807605 2714033 := bstep (se 2 (by rfl) ⟨1017762, by rfl⟩ : syracuseStep 2714033 = 2035525) B2035525
theorem B2714051 : Blo 1807605 2714051 := bstep (se 1 (by rfl) ⟨2035538, by rfl⟩ : syracuseStep 2714051 = 4071077) B4071077
theorem B2288083 : Blo 1807605 2288083 := bstep (se 1 (by rfl) ⟨1716062, by rfl⟩ : syracuseStep 2288083 = 3432125) B3432125
theorem B2714081 : Blo 1807605 2714081 := bstep (se 2 (by rfl) ⟨1017780, by rfl⟩ : syracuseStep 2714081 = 2035561) B2035561
theorem B2714099 : Blo 1807605 2714099 := bstep (se 1 (by rfl) ⟨2035574, by rfl⟩ : syracuseStep 2714099 = 4071149) B4071149
theorem B6105617 : Blo 1807605 6105617 := bstep (se 2 (by rfl) ⟨2289606, by rfl⟩ : syracuseStep 6105617 = 4579213) B4579213
theorem B2714129 : Blo 1807605 2714129 := bstep (se 2 (by rfl) ⟨1017798, by rfl⟩ : syracuseStep 2714129 = 2035597) B2035597
theorem B2034211 : Blo 1807605 2034211 := bstep (se 1 (by rfl) ⟨1525658, by rfl⟩ : syracuseStep 2034211 = 3051317) B3051317
theorem B2714147 : Blo 1807605 2714147 := bstep (se 1 (by rfl) ⟨2035610, by rfl⟩ : syracuseStep 2714147 = 4071221) B4071221
theorem B2288179 : Blo 1807605 2288179 := bstep (se 1 (by rfl) ⟨1716134, by rfl⟩ : syracuseStep 2288179 = 3432269) B3432269
theorem B2714177 : Blo 1807605 2714177 := bstep (se 2 (by rfl) ⟨1017816, by rfl⟩ : syracuseStep 2714177 = 2035633) B2035633
theorem B2574931 : Blo 1807605 2574931 := bstep (se 1 (by rfl) ⟨1931198, by rfl⟩ : syracuseStep 2574931 = 3862397) B3862397
theorem B2714195 : Blo 1807605 2714195 := bstep (se 1 (by rfl) ⟨2035646, by rfl⟩ : syracuseStep 2714195 = 4071293) B4071293
theorem B2714225 : Blo 1807605 2714225 := bstep (se 2 (by rfl) ⟨1017834, by rfl⟩ : syracuseStep 2714225 = 2035669) B2035669
theorem B3435139 : Blo 1807605 3435139 := bstep (se 1 (by rfl) ⟨2576354, by rfl⟩ : syracuseStep 3435139 = 5152709) B5152709
theorem B2714243 : Blo 1807605 2714243 := bstep (se 1 (by rfl) ⟨2035682, by rfl⟩ : syracuseStep 2714243 = 4071365) B4071365
theorem B2714273 : Blo 1807605 2714273 := bstep (se 2 (by rfl) ⟨1017852, by rfl⟩ : syracuseStep 2714273 = 2035705) B2035705
theorem B3435185 : Blo 1807605 3435185 := bstep (se 2 (by rfl) ⟨1288194, by rfl⟩ : syracuseStep 3435185 = 2576389) B2576389
theorem B2034355 : Blo 1807605 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B2714291 : Blo 1807605 2714291 := bstep (se 1 (by rfl) ⟨2035718, by rfl⟩ : syracuseStep 2714291 = 4071437) B4071437
theorem B2714321 : Blo 1807605 2714321 := bstep (se 2 (by rfl) ⟨1017870, by rfl⟩ : syracuseStep 2714321 = 2035741) B2035741
theorem B2714339 : Blo 1807605 2714339 := bstep (se 1 (by rfl) ⟨2035754, by rfl⟩ : syracuseStep 2714339 = 4071509) B4071509
theorem B2444033 : Blo 1807605 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2714369 : Blo 1807605 2714369 := bstep (se 2 (by rfl) ⟨1017888, by rfl⟩ : syracuseStep 2714369 = 2035777) B2035777
theorem B2714387 : Blo 1807605 2714387 := bstep (se 1 (by rfl) ⟨2035790, by rfl⟩ : syracuseStep 2714387 = 4071581) B4071581
theorem B5499683 : Blo 1807605 5499683 := bstep (se 1 (by rfl) ⟨4124762, by rfl⟩ : syracuseStep 5499683 = 8249525) B8249525
theorem B5147459 : Blo 1807605 5147459 := bstep (se 1 (by rfl) ⟨3860594, by rfl⟩ : syracuseStep 5147459 = 7721189) B7721189
theorem B2034499 : Blo 1807605 2034499 := bstep (se 1 (by rfl) ⟨1525874, by rfl⟩ : syracuseStep 2034499 = 3051749) B3051749
theorem B2976659 : Blo 1807605 2976659 := bstep (se 1 (by rfl) ⟨2232494, by rfl⟩ : syracuseStep 2976659 = 4464989) B4464989
theorem B3050419 : Blo 1807605 3050419 := bstep (se 1 (by rfl) ⟨2287814, by rfl⟩ : syracuseStep 3050419 = 4575629) B4575629
theorem B9153485 : Blo 1807605 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B2034643 : Blo 1807605 2034643 := bstep (se 1 (by rfl) ⟨1525982, by rfl⟩ : syracuseStep 2034643 = 3051965) B3051965
theorem B5147651 : Blo 1807605 5147651 := bstep (se 1 (by rfl) ⟨3860738, by rfl⟩ : syracuseStep 5147651 = 7721477) B7721477
theorem B3304451 : Blo 1807605 3304451 := bstep (se 1 (by rfl) ⟨2478338, by rfl⟩ : syracuseStep 3304451 = 4956677) B4956677
theorem B2288675 : Blo 1807605 2288675 := bstep (se 1 (by rfl) ⟨1716506, by rfl⟩ : syracuseStep 2288675 = 3433013) B3433013
theorem B6106157 : Blo 1807605 6106157 := bstep (se 3 (by rfl) ⟨1144904, by rfl⟩ : syracuseStep 6106157 = 2289809) B2289809
theorem B3664945 : Blo 1807605 3664945 := bstep (se 2 (by rfl) ⟨1374354, by rfl⟩ : syracuseStep 3664945 = 2748709) B2748709
theorem B3050561 : Blo 1807605 3050561 := bstep (se 2 (by rfl) ⟨1143960, by rfl⟩ : syracuseStep 3050561 = 2287921) B2287921
theorem B19557445 : Blo 1807605 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B2034787 : Blo 1807605 2034787 := bstep (se 1 (by rfl) ⟨1526090, by rfl⟩ : syracuseStep 2034787 = 3052181) B3052181
theorem B6106211 : Blo 1807605 6106211 := bstep (se 1 (by rfl) ⟨4579658, by rfl⟩ : syracuseStep 6106211 = 9159317) B9159317
theorem B2575489 : Blo 1807605 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B4123793 : Blo 1807605 4123793 := bstep (se 2 (by rfl) ⟨1546422, by rfl⟩ : syracuseStep 4123793 = 3092845) B3092845
theorem B2575523 : Blo 1807605 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B3050689 : Blo 1807605 3050689 := bstep (se 2 (by rfl) ⟨1144008, by rfl⟩ : syracuseStep 3050689 = 2288017) B2288017
theorem B3050723 : Blo 1807605 3050723 := bstep (se 1 (by rfl) ⟨2288042, by rfl⟩ : syracuseStep 3050723 = 4576085) B4576085
theorem B13389041 : Blo 1807605 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B2034931 : Blo 1807605 2034931 := bstep (se 1 (by rfl) ⟨1526198, by rfl⟩ : syracuseStep 2034931 = 3052397) B3052397
theorem B4345091 : Blo 1807605 4345091 := bstep (se 1 (by rfl) ⟨3258818, by rfl⟩ : syracuseStep 4345091 = 6517637) B6517637
theorem B6868259 : Blo 1807605 6868259 := bstep (se 1 (by rfl) ⟨5151194, by rfl⟩ : syracuseStep 6868259 = 10302389) B10302389
theorem B6868273 : Blo 1807605 6868273 := bstep (se 2 (by rfl) ⟨2575602, by rfl⟩ : syracuseStep 6868273 = 5151205) B5151205
theorem B3050851 : Blo 1807605 3050851 := bstep (se 1 (by rfl) ⟨2288138, by rfl⟩ : syracuseStep 3050851 = 4576277) B4576277
theorem B13036913 : Blo 1807605 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B6106481 : Blo 1807605 6106481 := bstep (se 2 (by rfl) ⟨2289930, by rfl⟩ : syracuseStep 6106481 = 4579861) B4579861
theorem B2035075 : Blo 1807605 2035075 := bstep (se 1 (by rfl) ⟨1526306, by rfl⟩ : syracuseStep 2035075 = 3052613) B3052613
theorem B3050993 : Blo 1807605 3050993 := bstep (se 2 (by rfl) ⟨1144122, by rfl⟩ : syracuseStep 3050993 = 2288245) B2288245
theorem B2035219 : Blo 1807605 2035219 := bstep (se 1 (by rfl) ⟨1526414, by rfl⟩ : syracuseStep 2035219 = 3052829) B3052829
theorem B2444833 : Blo 1807605 2444833 := bstep (se 2 (by rfl) ⟨916812, by rfl⟩ : syracuseStep 2444833 = 1833625) B1833625
theorem B5795363 : Blo 1807605 5795363 := bstep (se 1 (by rfl) ⟨4346522, by rfl⟩ : syracuseStep 5795363 = 8693045) B8693045
theorem B3051121 : Blo 1807605 3051121 := bstep (se 2 (by rfl) ⟨1144170, by rfl⟩ : syracuseStep 3051121 = 2288341) B2288341
theorem B3051155 : Blo 1807605 3051155 := bstep (se 1 (by rfl) ⟨2288366, by rfl⟩ : syracuseStep 3051155 = 4576733) B4576733
theorem B2035363 : Blo 1807605 2035363 := bstep (se 1 (by rfl) ⟨1526522, by rfl⟩ : syracuseStep 2035363 = 3053045) B3053045
theorem B2444995 : Blo 1807605 2444995 := bstep (se 1 (by rfl) ⟨1833746, by rfl⟩ : syracuseStep 2444995 = 3667493) B3667493
theorem B2576081 : Blo 1807605 2576081 := bstep (se 2 (by rfl) ⟨966030, by rfl⟩ : syracuseStep 2576081 = 1932061) B1932061
theorem B2289379 : Blo 1807605 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B3092243 : Blo 1807605 3092243 := bstep (se 1 (by rfl) ⟨2319182, by rfl⟩ : syracuseStep 3092243 = 4638365) B4638365
theorem B3051283 : Blo 1807605 3051283 := bstep (se 1 (by rfl) ⟨2288462, by rfl⟩ : syracuseStep 3051283 = 4576925) B4576925
theorem B2576161 : Blo 1807605 2576161 := bstep (se 2 (by rfl) ⟨966060, by rfl⟩ : syracuseStep 2576161 = 1932121) B1932121
theorem B5148461 : Blo 1807605 5148461 := bstep (se 3 (by rfl) ⟨965336, by rfl⟩ : syracuseStep 5148461 = 1930673) B1930673
theorem B2035507 : Blo 1807605 2035507 := bstep (se 1 (by rfl) ⟨1526630, by rfl⟩ : syracuseStep 2035507 = 3053261) B3053261
theorem B2289475 : Blo 1807605 2289475 := bstep (se 1 (by rfl) ⟨1717106, by rfl⟩ : syracuseStep 2289475 = 3434213) B3434213
theorem B4067153 : Blo 1807605 4067153 := bstep (se 2 (by rfl) ⟨1525182, by rfl⟩ : syracuseStep 4067153 = 3050365) B3050365
theorem B4067171 : Blo 1807605 4067171 := bstep (se 1 (by rfl) ⟨3050378, by rfl⟩ : syracuseStep 4067171 = 6100757) B6100757
theorem B7728995 : Blo 1807605 7728995 := bstep (se 1 (by rfl) ⟨5796746, by rfl⟩ : syracuseStep 7728995 = 11593493) B11593493
theorem B6107021 : Blo 1807605 6107021 := bstep (se 3 (by rfl) ⟨1145066, by rfl⟩ : syracuseStep 6107021 = 2290133) B2290133
theorem B3051425 : Blo 1807605 3051425 := bstep (se 2 (by rfl) ⟨1144284, by rfl⟩ : syracuseStep 3051425 = 2288569) B2288569
theorem B2035651 : Blo 1807605 2035651 := bstep (se 1 (by rfl) ⟨1526738, by rfl⟩ : syracuseStep 2035651 = 3053477) B3053477
theorem B6107075 : Blo 1807605 6107075 := bstep (se 1 (by rfl) ⟨4580306, by rfl⟩ : syracuseStep 6107075 = 9160613) B9160613
theorem B44584901 : Blo 1807605 44584901 := bstep (se 4 (by rfl) ⟨4179834, by rfl⟩ : syracuseStep 44584901 = 8359669) B8359669
theorem B5148643 : Blo 1807605 5148643 := bstep (se 1 (by rfl) ⟨3861482, by rfl⟩ : syracuseStep 5148643 = 7722965) B7722965
theorem B13733873 : Blo 1807605 13733873 := bstep (se 2 (by rfl) ⟨5150202, by rfl⟩ : syracuseStep 13733873 = 10300405) B10300405
theorem B3051553 : Blo 1807605 3051553 := bstep (se 2 (by rfl) ⟨1144332, by rfl⟩ : syracuseStep 3051553 = 2288665) B2288665
theorem B2895907 : Blo 1807605 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B3051587 : Blo 1807605 3051587 := bstep (se 1 (by rfl) ⟨2288690, by rfl⟩ : syracuseStep 3051587 = 4577381) B4577381
theorem B2035795 : Blo 1807605 2035795 := bstep (se 1 (by rfl) ⟨1526846, by rfl⟩ : syracuseStep 2035795 = 3053693) B3053693
theorem B4067441 : Blo 1807605 4067441 := bstep (se 2 (by rfl) ⟨1525290, by rfl⟩ : syracuseStep 4067441 = 3050581) B3050581
theorem B4067459 : Blo 1807605 4067459 := bstep (se 1 (by rfl) ⟨3050594, by rfl⟩ : syracuseStep 4067459 = 6101189) B6101189
theorem B3051715 : Blo 1807605 3051715 := bstep (se 1 (by rfl) ⟨2288786, by rfl⟩ : syracuseStep 3051715 = 4577573) B4577573
theorem B6107345 : Blo 1807605 6107345 := bstep (se 2 (by rfl) ⟨2290254, by rfl⟩ : syracuseStep 6107345 = 4580509) B4580509
theorem B15454435 : Blo 1807605 15454435 := bstep (se 1 (by rfl) ⟨11590826, by rfl⟩ : syracuseStep 15454435 = 23181653) B23181653
theorem B10301681 : Blo 1807605 10301681 := bstep (se 2 (by rfl) ⟨3863130, by rfl⟩ : syracuseStep 10301681 = 7726261) B7726261
theorem B3092737 : Blo 1807605 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B2289971 : Blo 1807605 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B3051857 : Blo 1807605 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B4886897 : Blo 1807605 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B4067729 : Blo 1807605 4067729 := bstep (se 2 (by rfl) ⟨1525398, by rfl⟩ : syracuseStep 4067729 = 3050797) B3050797
theorem B4067747 : Blo 1807605 4067747 := bstep (se 1 (by rfl) ⟨3050810, by rfl⟩ : syracuseStep 4067747 = 6101621) B6101621
theorem B5149133 : Blo 1807605 5149133 := bstep (se 3 (by rfl) ⟨965462, by rfl⟩ : syracuseStep 5149133 = 1930925) B1930925
theorem B3051985 : Blo 1807605 3051985 := bstep (se 2 (by rfl) ⟨1144494, by rfl⟩ : syracuseStep 3051985 = 2288989) B2288989
theorem B6517219 : Blo 1807605 6517219 := bstep (se 1 (by rfl) ⟨4887914, by rfl⟩ : syracuseStep 6517219 = 9775829) B9775829
theorem B3052019 : Blo 1807605 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B4575761 : Blo 1807605 4575761 := bstep (se 2 (by rfl) ⟨1715910, by rfl⟩ : syracuseStep 4575761 = 3431821) B3431821
theorem B4575811 : Blo 1807605 4575811 := bstep (se 1 (by rfl) ⟨3431858, by rfl⟩ : syracuseStep 4575811 = 6863717) B6863717
theorem B29741681 : Blo 1807605 29741681 := bstep (se 2 (by rfl) ⟨11153130, by rfl⟩ : syracuseStep 29741681 = 22306261) B22306261
theorem B3052147 : Blo 1807605 3052147 := bstep (se 1 (by rfl) ⟨2289110, by rfl⟩ : syracuseStep 3052147 = 4578221) B4578221
theorem B4068017 : Blo 1807605 4068017 := bstep (se 2 (by rfl) ⟨1525506, by rfl⟩ : syracuseStep 4068017 = 3051013) B3051013
theorem B4068035 : Blo 1807605 4068035 := bstep (se 1 (by rfl) ⟨3051026, by rfl⟩ : syracuseStep 4068035 = 6102053) B6102053
theorem B2896579 : Blo 1807605 2896579 := bstep (se 1 (by rfl) ⟨2172434, by rfl⟩ : syracuseStep 2896579 = 4344869) B4344869
theorem B18805445 : Blo 1807605 18805445 := bstep (se 4 (by rfl) ⟨1763010, by rfl⟩ : syracuseStep 18805445 = 3526021) B3526021
theorem B4575953 : Blo 1807605 4575953 := bstep (se 2 (by rfl) ⟨1715982, by rfl⟩ : syracuseStep 4575953 = 3431965) B3431965
theorem B6869731 : Blo 1807605 6869731 := bstep (se 1 (by rfl) ⟨5152298, by rfl⟩ : syracuseStep 6869731 = 10304597) B10304597
theorem B5796593 : Blo 1807605 5796593 := bstep (se 2 (by rfl) ⟨2173722, by rfl⟩ : syracuseStep 5796593 = 4347445) B4347445
theorem B3052289 : Blo 1807605 3052289 := bstep (se 2 (by rfl) ⟨1144608, by rfl⟩ : syracuseStep 3052289 = 2289217) B2289217
theorem B2511667 : Blo 1807605 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B4887395 : Blo 1807605 4887395 := bstep (se 1 (by rfl) ⟨3665546, by rfl⟩ : syracuseStep 4887395 = 7331093) B7331093
theorem B3052417 : Blo 1807605 3052417 := bstep (se 2 (by rfl) ⟨1144656, by rfl⟩ : syracuseStep 3052417 = 2289313) B2289313
theorem B3052451 : Blo 1807605 3052451 := bstep (se 1 (by rfl) ⟨2289338, by rfl⟩ : syracuseStep 3052451 = 4578677) B4578677
theorem B6517709 : Blo 1807605 6517709 := bstep (se 3 (by rfl) ⟨1222070, by rfl⟩ : syracuseStep 6517709 = 2444141) B2444141
theorem B4068305 : Blo 1807605 4068305 := bstep (se 2 (by rfl) ⟨1525614, by rfl⟩ : syracuseStep 4068305 = 3051229) B3051229
theorem B4068323 : Blo 1807605 4068323 := bstep (se 1 (by rfl) ⟨3051242, by rfl⟩ : syracuseStep 4068323 = 6102485) B6102485
theorem B3052579 : Blo 1807605 3052579 := bstep (se 1 (by rfl) ⟨2289434, by rfl⟩ : syracuseStep 3052579 = 4578869) B4578869
theorem B29717617 : Blo 1807605 29717617 := bstep (se 2 (by rfl) ⟨11144106, by rfl⟩ : syracuseStep 29717617 = 22288213) B22288213
theorem B2749585 : Blo 1807605 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B2897041 : Blo 1807605 2897041 := bstep (se 2 (by rfl) ⟨1086390, by rfl⟩ : syracuseStep 2897041 = 2172781) B2172781
theorem B7722161 : Blo 1807605 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B3052721 : Blo 1807605 3052721 := bstep (se 2 (by rfl) ⟨1144770, by rfl⟩ : syracuseStep 3052721 = 2289541) B2289541
theorem B20092085 : Blo 1807605 20092085 := bstep (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) B1883633
theorem B30889187 : Blo 1807605 30889187 := bstep (se 1 (by rfl) ⟨23166890, by rfl⟩ : syracuseStep 30889187 = 46333781) B46333781
theorem B4068593 : Blo 1807605 4068593 := bstep (se 2 (by rfl) ⟨1525722, by rfl⟩ : syracuseStep 4068593 = 3051445) B3051445
theorem B2897137 : Blo 1807605 2897137 := bstep (se 2 (by rfl) ⟨1086426, by rfl⟩ : syracuseStep 2897137 = 2172853) B2172853
theorem B1807619 : Blo 1807605 1807619 := bstep (se 1 (by rfl) ⟨1355714, by rfl⟩ : syracuseStep 1807619 = 2711429) B2711429
theorem B4068611 : Blo 1807605 4068611 := bstep (se 1 (by rfl) ⟨3051458, by rfl⟩ : syracuseStep 4068611 = 6102917) B6102917
theorem B1807635 : Blo 1807605 1807635 := bstep (se 1 (by rfl) ⟨1355726, by rfl⟩ : syracuseStep 1807635 = 2711453) B2711453
theorem B1807651 : Blo 1807605 1807651 := bstep (se 1 (by rfl) ⟨1355738, by rfl⟩ : syracuseStep 1807651 = 2711477) B2711477
theorem B3052849 : Blo 1807605 3052849 := bstep (se 2 (by rfl) ⟨1144818, by rfl⟩ : syracuseStep 3052849 = 2289637) B2289637
theorem B1807667 : Blo 1807605 1807667 := bstep (se 1 (by rfl) ⟨1355750, by rfl⟩ : syracuseStep 1807667 = 2711501) B2711501
theorem B1807683 : Blo 1807605 1807683 := bstep (se 1 (by rfl) ⟨1355762, by rfl⟩ : syracuseStep 1807683 = 2711525) B2711525
theorem B3863875 : Blo 1807605 3863875 := bstep (se 1 (by rfl) ⟨2897906, by rfl⟩ : syracuseStep 3863875 = 5795813) B5795813
theorem B1807699 : Blo 1807605 1807699 := bstep (se 1 (by rfl) ⟨1355774, by rfl⟩ : syracuseStep 1807699 = 2711549) B2711549
theorem B3052883 : Blo 1807605 3052883 := bstep (se 1 (by rfl) ⟨2289662, by rfl⟩ : syracuseStep 3052883 = 4579325) B4579325
theorem B1807715 : Blo 1807605 1807715 := bstep (se 1 (by rfl) ⟨1355786, by rfl⟩ : syracuseStep 1807715 = 2711573) B2711573
theorem B1807731 : Blo 1807605 1807731 := bstep (se 1 (by rfl) ⟨1355798, by rfl⟩ : syracuseStep 1807731 = 2711597) B2711597
theorem B1807747 : Blo 1807605 1807747 := bstep (se 1 (by rfl) ⟨1355810, by rfl⟩ : syracuseStep 1807747 = 2711621) B2711621
theorem B2897297 : Blo 1807605 2897297 := bstep (se 2 (by rfl) ⟨1086486, by rfl⟩ : syracuseStep 2897297 = 2172973) B2172973
theorem B1807763 : Blo 1807605 1807763 := bstep (se 1 (by rfl) ⟨1355822, by rfl⟩ : syracuseStep 1807763 = 2711645) B2711645
theorem B1807779 : Blo 1807605 1807779 := bstep (se 1 (by rfl) ⟨1355834, by rfl⟩ : syracuseStep 1807779 = 2711669) B2711669
theorem B1807795 : Blo 1807605 1807795 := bstep (se 1 (by rfl) ⟨1355846, by rfl⟩ : syracuseStep 1807795 = 2711693) B2711693
theorem B1807811 : Blo 1807605 1807811 := bstep (se 1 (by rfl) ⟨1355858, by rfl⟩ : syracuseStep 1807811 = 2711717) B2711717
theorem B1807827 : Blo 1807605 1807827 := bstep (se 1 (by rfl) ⟨1355870, by rfl⟩ : syracuseStep 1807827 = 2711741) B2711741
theorem B3053011 : Blo 1807605 3053011 := bstep (se 1 (by rfl) ⟨2289758, by rfl⟩ : syracuseStep 3053011 = 4579517) B4579517
theorem B1807843 : Blo 1807605 1807843 := bstep (se 1 (by rfl) ⟨1355882, by rfl⟩ : syracuseStep 1807843 = 2711765) B2711765
theorem B1807859 : Blo 1807605 1807859 := bstep (se 1 (by rfl) ⟨1355894, by rfl⟩ : syracuseStep 1807859 = 2711789) B2711789
theorem B1807875 : Blo 1807605 1807875 := bstep (se 1 (by rfl) ⟨1355906, by rfl⟩ : syracuseStep 1807875 = 2711813) B2711813
theorem B4068881 : Blo 1807605 4068881 := bstep (se 2 (by rfl) ⟨1525830, by rfl⟩ : syracuseStep 4068881 = 3051661) B3051661
theorem B2749969 : Blo 1807605 2749969 := bstep (se 2 (by rfl) ⟨1031238, by rfl⟩ : syracuseStep 2749969 = 2062477) B2062477
theorem B1807891 : Blo 1807605 1807891 := bstep (se 1 (by rfl) ⟨1355918, by rfl⟩ : syracuseStep 1807891 = 2711837) B2711837
theorem B1807907 : Blo 1807605 1807907 := bstep (se 1 (by rfl) ⟨1355930, by rfl⟩ : syracuseStep 1807907 = 2711861) B2711861
theorem B4068899 : Blo 1807605 4068899 := bstep (se 1 (by rfl) ⟨3051674, by rfl⟩ : syracuseStep 4068899 = 6103349) B6103349
theorem B1807923 : Blo 1807605 1807923 := bstep (se 1 (by rfl) ⟨1355942, by rfl⟩ : syracuseStep 1807923 = 2711885) B2711885
theorem B1807939 : Blo 1807605 1807939 := bstep (se 1 (by rfl) ⟨1355954, by rfl⟩ : syracuseStep 1807939 = 2711909) B2711909
theorem B1807955 : Blo 1807605 1807955 := bstep (se 1 (by rfl) ⟨1355966, by rfl⟩ : syracuseStep 1807955 = 2711933) B2711933
theorem B3053153 : Blo 1807605 3053153 := bstep (se 2 (by rfl) ⟨1144932, by rfl⟩ : syracuseStep 3053153 = 2289865) B2289865
theorem B1807971 : Blo 1807605 1807971 := bstep (se 1 (by rfl) ⟨1355978, by rfl⟩ : syracuseStep 1807971 = 2711957) B2711957
theorem B5150317 : Blo 1807605 5150317 := bstep (se 3 (by rfl) ⟨965684, by rfl⟩ : syracuseStep 5150317 = 1931369) B1931369
theorem B8246897 : Blo 1807605 8246897 := bstep (se 2 (by rfl) ⟨3092586, by rfl⟩ : syracuseStep 8246897 = 6185173) B6185173
theorem B18814577 : Blo 1807605 18814577 := bstep (se 2 (by rfl) ⟨7055466, by rfl⟩ : syracuseStep 18814577 = 14110933) B14110933
theorem B1807987 : Blo 1807605 1807987 := bstep (se 1 (by rfl) ⟨1355990, by rfl⟩ : syracuseStep 1807987 = 2711981) B2711981
theorem B1808003 : Blo 1807605 1808003 := bstep (se 1 (by rfl) ⟨1356002, by rfl⟩ : syracuseStep 1808003 = 2712005) B2712005
theorem B1808019 : Blo 1807605 1808019 := bstep (se 1 (by rfl) ⟨1356014, by rfl⟩ : syracuseStep 1808019 = 2712029) B2712029
theorem B1808035 : Blo 1807605 1808035 := bstep (se 1 (by rfl) ⟨1356026, by rfl⟩ : syracuseStep 1808035 = 2712053) B2712053
theorem B10303139 : Blo 1807605 10303139 := bstep (se 1 (by rfl) ⟨7727354, by rfl⟩ : syracuseStep 10303139 = 15454709) B15454709
theorem B4576945 : Blo 1807605 4576945 := bstep (se 2 (by rfl) ⟨1716354, by rfl⟩ : syracuseStep 4576945 = 3432709) B3432709
theorem B1808051 : Blo 1807605 1808051 := bstep (se 1 (by rfl) ⟨1356038, by rfl⟩ : syracuseStep 1808051 = 2712077) B2712077
theorem B1808067 : Blo 1807605 1808067 := bstep (se 1 (by rfl) ⟨1356050, by rfl⟩ : syracuseStep 1808067 = 2712101) B2712101
theorem B1808083 : Blo 1807605 1808083 := bstep (se 1 (by rfl) ⟨1356062, by rfl⟩ : syracuseStep 1808083 = 2712125) B2712125
theorem B3053281 : Blo 1807605 3053281 := bstep (se 2 (by rfl) ⟨1144980, by rfl⟩ : syracuseStep 3053281 = 2289961) B2289961
theorem B1808099 : Blo 1807605 1808099 := bstep (se 1 (by rfl) ⟨1356074, by rfl⟩ : syracuseStep 1808099 = 2712149) B2712149
theorem B8812273 : Blo 1807605 8812273 := bstep (se 2 (by rfl) ⟨3304602, by rfl⟩ : syracuseStep 8812273 = 6609205) B6609205
theorem B1808115 : Blo 1807605 1808115 := bstep (se 1 (by rfl) ⟨1356086, by rfl⟩ : syracuseStep 1808115 = 2712173) B2712173
theorem B1808131 : Blo 1807605 1808131 := bstep (se 1 (by rfl) ⟨1356098, by rfl⟩ : syracuseStep 1808131 = 2712197) B2712197
theorem B3053315 : Blo 1807605 3053315 := bstep (se 1 (by rfl) ⟨2289986, by rfl⟩ : syracuseStep 3053315 = 4579973) B4579973
theorem B1808147 : Blo 1807605 1808147 := bstep (se 1 (by rfl) ⟨1356110, by rfl⟩ : syracuseStep 1808147 = 2712221) B2712221
theorem B1808163 : Blo 1807605 1808163 := bstep (se 1 (by rfl) ⟨1356122, by rfl⟩ : syracuseStep 1808163 = 2712245) B2712245
theorem B4069169 : Blo 1807605 4069169 := bstep (se 2 (by rfl) ⟨1525938, by rfl⟩ : syracuseStep 4069169 = 3051877) B3051877
theorem B9156401 : Blo 1807605 9156401 := bstep (se 2 (by rfl) ⟨3433650, by rfl⟩ : syracuseStep 9156401 = 6867301) B6867301
theorem B1808179 : Blo 1807605 1808179 := bstep (se 1 (by rfl) ⟨1356134, by rfl⟩ : syracuseStep 1808179 = 2712269) B2712269
theorem B1808195 : Blo 1807605 1808195 := bstep (se 1 (by rfl) ⟨1356146, by rfl⟩ : syracuseStep 1808195 = 2712293) B2712293
theorem B4069187 : Blo 1807605 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B1808211 : Blo 1807605 1808211 := bstep (se 1 (by rfl) ⟨1356158, by rfl⟩ : syracuseStep 1808211 = 2712317) B2712317
theorem B1808227 : Blo 1807605 1808227 := bstep (se 1 (by rfl) ⟨1356170, by rfl⟩ : syracuseStep 1808227 = 2712341) B2712341
theorem B4888433 : Blo 1807605 4888433 := bstep (se 2 (by rfl) ⟨1833162, by rfl⟩ : syracuseStep 4888433 = 3666325) B3666325
theorem B1808243 : Blo 1807605 1808243 := bstep (se 1 (by rfl) ⟨1356182, by rfl⟩ : syracuseStep 1808243 = 2712365) B2712365
theorem B1808259 : Blo 1807605 1808259 := bstep (se 1 (by rfl) ⟨1356194, by rfl⟩ : syracuseStep 1808259 = 2712389) B2712389
theorem B3053443 : Blo 1807605 3053443 := bstep (se 1 (by rfl) ⟨2290082, by rfl⟩ : syracuseStep 3053443 = 4580165) B4580165
theorem B1808275 : Blo 1807605 1808275 := bstep (se 1 (by rfl) ⟨1356206, by rfl⟩ : syracuseStep 1808275 = 2712413) B2712413
theorem B1808291 : Blo 1807605 1808291 := bstep (se 1 (by rfl) ⟨1356218, by rfl⟩ : syracuseStep 1808291 = 2712437) B2712437
theorem B1808307 : Blo 1807605 1808307 := bstep (se 1 (by rfl) ⟨1356230, by rfl⟩ : syracuseStep 1808307 = 2712461) B2712461
theorem B4577219 : Blo 1807605 4577219 := bstep (se 1 (by rfl) ⟨3432914, by rfl⟩ : syracuseStep 4577219 = 6865829) B6865829
theorem B1808323 : Blo 1807605 1808323 := bstep (se 1 (by rfl) ⟨1356242, by rfl⟩ : syracuseStep 1808323 = 2712485) B2712485
theorem B1808339 : Blo 1807605 1808339 := bstep (se 1 (by rfl) ⟨1356254, by rfl⟩ : syracuseStep 1808339 = 2712509) B2712509
theorem B1808355 : Blo 1807605 1808355 := bstep (se 1 (by rfl) ⟨1356266, by rfl⟩ : syracuseStep 1808355 = 2712533) B2712533
theorem B6100973 : Blo 1807605 6100973 := bstep (se 3 (by rfl) ⟨1143932, by rfl⟩ : syracuseStep 6100973 = 2287865) B2287865
theorem B1808371 : Blo 1807605 1808371 := bstep (se 1 (by rfl) ⟨1356278, by rfl⟩ : syracuseStep 1808371 = 2712557) B2712557
theorem B1808387 : Blo 1807605 1808387 := bstep (se 1 (by rfl) ⟨1356290, by rfl⟩ : syracuseStep 1808387 = 2712581) B2712581
theorem B3053585 : Blo 1807605 3053585 := bstep (se 2 (by rfl) ⟨1145094, by rfl⟩ : syracuseStep 3053585 = 2290189) B2290189
theorem B1808403 : Blo 1807605 1808403 := bstep (se 1 (by rfl) ⟨1356302, by rfl⟩ : syracuseStep 1808403 = 2712605) B2712605
theorem B6101027 : Blo 1807605 6101027 := bstep (se 1 (by rfl) ⟨4575770, by rfl⟩ : syracuseStep 6101027 = 9151541) B9151541
theorem B1808419 : Blo 1807605 1808419 := bstep (se 1 (by rfl) ⟨1356314, by rfl⟩ : syracuseStep 1808419 = 2712629) B2712629
theorem B1808435 : Blo 1807605 1808435 := bstep (se 1 (by rfl) ⟨1356326, by rfl⟩ : syracuseStep 1808435 = 2712653) B2712653
theorem B1808451 : Blo 1807605 1808451 := bstep (se 1 (by rfl) ⟨1356338, by rfl⟩ : syracuseStep 1808451 = 2712677) B2712677
theorem B4069457 : Blo 1807605 4069457 := bstep (se 2 (by rfl) ⟨1526046, by rfl⟩ : syracuseStep 4069457 = 3052093) B3052093
theorem B1808467 : Blo 1807605 1808467 := bstep (se 1 (by rfl) ⟨1356350, by rfl⟩ : syracuseStep 1808467 = 2712701) B2712701
theorem B1808483 : Blo 1807605 1808483 := bstep (se 1 (by rfl) ⟨1356362, by rfl⟩ : syracuseStep 1808483 = 2712725) B2712725
theorem B4069475 : Blo 1807605 4069475 := bstep (se 1 (by rfl) ⟨3052106, by rfl⟩ : syracuseStep 4069475 = 6104213) B6104213
theorem B1808499 : Blo 1807605 1808499 := bstep (se 1 (by rfl) ⟨1356374, by rfl⟩ : syracuseStep 1808499 = 2712749) B2712749
theorem B4577411 : Blo 1807605 4577411 := bstep (se 1 (by rfl) ⟨3433058, by rfl⟩ : syracuseStep 4577411 = 6866117) B6866117
theorem B1808515 : Blo 1807605 1808515 := bstep (se 1 (by rfl) ⟨1356386, by rfl⟩ : syracuseStep 1808515 = 2712773) B2712773
theorem B1808531 : Blo 1807605 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B1808547 : Blo 1807605 1808547 := bstep (se 1 (by rfl) ⟨1356410, by rfl⟩ : syracuseStep 1808547 = 2712821) B2712821
theorem B1808563 : Blo 1807605 1808563 := bstep (se 1 (by rfl) ⟨1356422, by rfl⟩ : syracuseStep 1808563 = 2712845) B2712845
theorem B1808579 : Blo 1807605 1808579 := bstep (se 1 (by rfl) ⟨1356434, by rfl⟩ : syracuseStep 1808579 = 2712869) B2712869
theorem B1808595 : Blo 1807605 1808595 := bstep (se 1 (by rfl) ⟨1356446, by rfl⟩ : syracuseStep 1808595 = 2712893) B2712893
theorem B1808611 : Blo 1807605 1808611 := bstep (se 1 (by rfl) ⟨1356458, by rfl⟩ : syracuseStep 1808611 = 2712917) B2712917
theorem B1808627 : Blo 1807605 1808627 := bstep (se 1 (by rfl) ⟨1356470, by rfl⟩ : syracuseStep 1808627 = 2712941) B2712941
theorem B1808643 : Blo 1807605 1808643 := bstep (se 1 (by rfl) ⟨1356482, by rfl⟩ : syracuseStep 1808643 = 2712965) B2712965
theorem B1808659 : Blo 1807605 1808659 := bstep (se 1 (by rfl) ⟨1356494, by rfl⟩ : syracuseStep 1808659 = 2712989) B2712989
theorem B1808675 : Blo 1807605 1808675 := bstep (se 1 (by rfl) ⟨1356506, by rfl⟩ : syracuseStep 1808675 = 2713013) B2713013
theorem B6101297 : Blo 1807605 6101297 := bstep (se 2 (by rfl) ⟨2287986, by rfl⟩ : syracuseStep 6101297 = 4575973) B4575973
theorem B4405553 : Blo 1807605 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1808691 : Blo 1807605 1808691 := bstep (se 1 (by rfl) ⟨1356518, by rfl⟩ : syracuseStep 1808691 = 2713037) B2713037
theorem B1808707 : Blo 1807605 1808707 := bstep (se 1 (by rfl) ⟨1356530, by rfl⟩ : syracuseStep 1808707 = 2713061) B2713061
theorem B1808723 : Blo 1807605 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B1808739 : Blo 1807605 1808739 := bstep (se 1 (by rfl) ⟨1356554, by rfl⟩ : syracuseStep 1808739 = 2713109) B2713109
theorem B4069745 : Blo 1807605 4069745 := bstep (se 2 (by rfl) ⟨1526154, by rfl⟩ : syracuseStep 4069745 = 3052309) B3052309
theorem B1808755 : Blo 1807605 1808755 := bstep (se 1 (by rfl) ⟨1356566, by rfl⟩ : syracuseStep 1808755 = 2713133) B2713133
theorem B3479939 : Blo 1807605 3479939 := bstep (se 1 (by rfl) ⟨2609954, by rfl⟩ : syracuseStep 3479939 = 5219909) B5219909
theorem B1808771 : Blo 1807605 1808771 := bstep (se 1 (by rfl) ⟨1356578, by rfl⟩ : syracuseStep 1808771 = 2713157) B2713157
theorem B4069763 : Blo 1807605 4069763 := bstep (se 1 (by rfl) ⟨3052322, by rfl⟩ : syracuseStep 4069763 = 6104645) B6104645
theorem B2750851 : Blo 1807605 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B1808787 : Blo 1807605 1808787 := bstep (se 1 (by rfl) ⟨1356590, by rfl⟩ : syracuseStep 1808787 = 2713181) B2713181
theorem B1808803 : Blo 1807605 1808803 := bstep (se 1 (by rfl) ⟨1356602, by rfl⟩ : syracuseStep 1808803 = 2713205) B2713205
theorem B1808819 : Blo 1807605 1808819 := bstep (se 1 (by rfl) ⟨1356614, by rfl⟩ : syracuseStep 1808819 = 2713229) B2713229
theorem B1808835 : Blo 1807605 1808835 := bstep (se 1 (by rfl) ⟨1356626, by rfl⟩ : syracuseStep 1808835 = 2713253) B2713253
theorem B1808851 : Blo 1807605 1808851 := bstep (se 1 (by rfl) ⟨1356638, by rfl⟩ : syracuseStep 1808851 = 2713277) B2713277
theorem B1808867 : Blo 1807605 1808867 := bstep (se 1 (by rfl) ⟨1356650, by rfl⟩ : syracuseStep 1808867 = 2713301) B2713301
theorem B1808883 : Blo 1807605 1808883 := bstep (se 1 (by rfl) ⟨1356662, by rfl⟩ : syracuseStep 1808883 = 2713325) B2713325
theorem B3258883 : Blo 1807605 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B1808899 : Blo 1807605 1808899 := bstep (se 1 (by rfl) ⟨1356674, by rfl⟩ : syracuseStep 1808899 = 2713349) B2713349
theorem B1931779 : Blo 1807605 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B1808915 : Blo 1807605 1808915 := bstep (se 1 (by rfl) ⟨1356686, by rfl⟩ : syracuseStep 1808915 = 2713373) B2713373
theorem B11581987 : Blo 1807605 11581987 := bstep (se 1 (by rfl) ⟨8686490, by rfl⟩ : syracuseStep 11581987 = 17372981) B17372981
theorem B1808931 : Blo 1807605 1808931 := bstep (se 1 (by rfl) ⟨1356698, by rfl⟩ : syracuseStep 1808931 = 2713397) B2713397
theorem B1808947 : Blo 1807605 1808947 := bstep (se 1 (by rfl) ⟨1356710, by rfl⟩ : syracuseStep 1808947 = 2713421) B2713421
theorem B1808963 : Blo 1807605 1808963 := bstep (se 1 (by rfl) ⟨1356722, by rfl⟩ : syracuseStep 1808963 = 2713445) B2713445
theorem B1808979 : Blo 1807605 1808979 := bstep (se 1 (by rfl) ⟨1356734, by rfl⟩ : syracuseStep 1808979 = 2713469) B2713469
theorem B1808995 : Blo 1807605 1808995 := bstep (se 1 (by rfl) ⟨1356746, by rfl⟩ : syracuseStep 1808995 = 2713493) B2713493
theorem B3668579 : Blo 1807605 3668579 := bstep (se 1 (by rfl) ⟨2751434, by rfl⟩ : syracuseStep 3668579 = 5502869) B5502869
theorem B1809011 : Blo 1807605 1809011 := bstep (se 1 (by rfl) ⟨1356758, by rfl⟩ : syracuseStep 1809011 = 2713517) B2713517
theorem B1809027 : Blo 1807605 1809027 := bstep (se 1 (by rfl) ⟨1356770, by rfl⟩ : syracuseStep 1809027 = 2713541) B2713541
theorem B34757261 : Blo 1807605 34757261 := bstep (se 3 (by rfl) ⟨6516986, by rfl⟩ : syracuseStep 34757261 = 13033973) B13033973
theorem B4070033 : Blo 1807605 4070033 := bstep (se 2 (by rfl) ⟨1526262, by rfl⟩ : syracuseStep 4070033 = 3052525) B3052525
theorem B5151377 : Blo 1807605 5151377 := bstep (se 2 (by rfl) ⟨1931766, by rfl⟩ : syracuseStep 5151377 = 3863533) B3863533
theorem B1809043 : Blo 1807605 1809043 := bstep (se 1 (by rfl) ⟨1356782, by rfl⟩ : syracuseStep 1809043 = 2713565) B2713565
theorem B4070051 : Blo 1807605 4070051 := bstep (se 1 (by rfl) ⟨3052538, by rfl⟩ : syracuseStep 4070051 = 6105077) B6105077
theorem B1809059 : Blo 1807605 1809059 := bstep (se 1 (by rfl) ⟨1356794, by rfl⟩ : syracuseStep 1809059 = 2713589) B2713589
theorem B2063011 : Blo 1807605 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B1809075 : Blo 1807605 1809075 := bstep (se 1 (by rfl) ⟨1356806, by rfl⟩ : syracuseStep 1809075 = 2713613) B2713613
theorem B1809091 : Blo 1807605 1809091 := bstep (se 1 (by rfl) ⟨1356818, by rfl⟩ : syracuseStep 1809091 = 2713637) B2713637
theorem B1809107 : Blo 1807605 1809107 := bstep (se 1 (by rfl) ⟨1356830, by rfl⟩ : syracuseStep 1809107 = 2713661) B2713661
theorem B1809123 : Blo 1807605 1809123 := bstep (se 1 (by rfl) ⟨1356842, by rfl⟩ : syracuseStep 1809123 = 2713685) B2713685
theorem B5577443 : Blo 1807605 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B1809139 : Blo 1807605 1809139 := bstep (se 1 (by rfl) ⟨1356854, by rfl⟩ : syracuseStep 1809139 = 2713709) B2713709
theorem B1809155 : Blo 1807605 1809155 := bstep (se 1 (by rfl) ⟨1356866, by rfl⟩ : syracuseStep 1809155 = 2713733) B2713733
theorem B1809171 : Blo 1807605 1809171 := bstep (se 1 (by rfl) ⟨1356878, by rfl⟩ : syracuseStep 1809171 = 2713757) B2713757
theorem B1809187 : Blo 1807605 1809187 := bstep (se 1 (by rfl) ⟨1356890, by rfl⟩ : syracuseStep 1809187 = 2713781) B2713781
theorem B1809203 : Blo 1807605 1809203 := bstep (se 1 (by rfl) ⟨1356902, by rfl⟩ : syracuseStep 1809203 = 2713805) B2713805
theorem B1809219 : Blo 1807605 1809219 := bstep (se 1 (by rfl) ⟨1356914, by rfl⟩ : syracuseStep 1809219 = 2713829) B2713829
theorem B6101837 : Blo 1807605 6101837 := bstep (se 3 (by rfl) ⟨1144094, by rfl⟩ : syracuseStep 6101837 = 2288189) B2288189
theorem B2751313 : Blo 1807605 2751313 := bstep (se 2 (by rfl) ⟨1031742, by rfl⟩ : syracuseStep 2751313 = 2063485) B2063485
theorem B1809235 : Blo 1807605 1809235 := bstep (se 1 (by rfl) ⟨1356926, by rfl⟩ : syracuseStep 1809235 = 2713853) B2713853
theorem B1809251 : Blo 1807605 1809251 := bstep (se 1 (by rfl) ⟨1356938, by rfl⟩ : syracuseStep 1809251 = 2713877) B2713877
theorem B1809267 : Blo 1807605 1809267 := bstep (se 1 (by rfl) ⟨1356950, by rfl⟩ : syracuseStep 1809267 = 2713901) B2713901
theorem B6101891 : Blo 1807605 6101891 := bstep (se 1 (by rfl) ⟨4576418, by rfl⟩ : syracuseStep 6101891 = 9152837) B9152837
theorem B1809283 : Blo 1807605 1809283 := bstep (se 1 (by rfl) ⟨1356962, by rfl⟩ : syracuseStep 1809283 = 2713925) B2713925
theorem B1809299 : Blo 1807605 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1809315 : Blo 1807605 1809315 := bstep (se 1 (by rfl) ⟨1356986, by rfl⟩ : syracuseStep 1809315 = 2713973) B2713973
theorem B4070321 : Blo 1807605 4070321 := bstep (se 2 (by rfl) ⟨1526370, by rfl⟩ : syracuseStep 4070321 = 3052741) B3052741
theorem B1809331 : Blo 1807605 1809331 := bstep (se 1 (by rfl) ⟨1356998, by rfl⟩ : syracuseStep 1809331 = 2713997) B2713997
theorem B1932211 : Blo 1807605 1932211 := bstep (se 1 (by rfl) ⟨1449158, by rfl⟩ : syracuseStep 1932211 = 2898317) B2898317
theorem B4070339 : Blo 1807605 4070339 := bstep (se 1 (by rfl) ⟨3052754, by rfl⟩ : syracuseStep 4070339 = 6105509) B6105509
theorem B1809347 : Blo 1807605 1809347 := bstep (se 1 (by rfl) ⟨1357010, by rfl⟩ : syracuseStep 1809347 = 2714021) B2714021
theorem B1809363 : Blo 1807605 1809363 := bstep (se 1 (by rfl) ⟨1357022, by rfl⟩ : syracuseStep 1809363 = 2714045) B2714045
theorem B1809379 : Blo 1807605 1809379 := bstep (se 1 (by rfl) ⟨1357034, by rfl⟩ : syracuseStep 1809379 = 2714069) B2714069
theorem B10296305 : Blo 1807605 10296305 := bstep (se 2 (by rfl) ⟨3861114, by rfl⟩ : syracuseStep 10296305 = 7722229) B7722229
theorem B1809395 : Blo 1807605 1809395 := bstep (se 1 (by rfl) ⟨1357046, by rfl⟩ : syracuseStep 1809395 = 2714093) B2714093
theorem B1809411 : Blo 1807605 1809411 := bstep (se 1 (by rfl) ⟨1357058, by rfl⟩ : syracuseStep 1809411 = 2714117) B2714117
theorem B6863885 : Blo 1807605 6863885 := bstep (se 3 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 6863885 = 2573957) B2573957
theorem B1809427 : Blo 1807605 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B1809443 : Blo 1807605 1809443 := bstep (se 1 (by rfl) ⟨1357082, by rfl⟩ : syracuseStep 1809443 = 2714165) B2714165
theorem B4578353 : Blo 1807605 4578353 := bstep (se 2 (by rfl) ⟨1716882, by rfl⟩ : syracuseStep 4578353 = 3433765) B3433765
theorem B1809459 : Blo 1807605 1809459 := bstep (se 1 (by rfl) ⟨1357094, by rfl⟩ : syracuseStep 1809459 = 2714189) B2714189
theorem B1809475 : Blo 1807605 1809475 := bstep (se 1 (by rfl) ⟨1357106, by rfl⟩ : syracuseStep 1809475 = 2714213) B2714213
theorem B1809491 : Blo 1807605 1809491 := bstep (se 1 (by rfl) ⟨1357118, by rfl⟩ : syracuseStep 1809491 = 2714237) B2714237
theorem B4578403 : Blo 1807605 4578403 := bstep (se 1 (by rfl) ⟨3433802, by rfl⟩ : syracuseStep 4578403 = 6867605) B6867605
theorem B1809507 : Blo 1807605 1809507 := bstep (se 1 (by rfl) ⟨1357130, by rfl⟩ : syracuseStep 1809507 = 2714261) B2714261
theorem B1809523 : Blo 1807605 1809523 := bstep (se 1 (by rfl) ⟨1357142, by rfl⟩ : syracuseStep 1809523 = 2714285) B2714285
theorem B1809539 : Blo 1807605 1809539 := bstep (se 1 (by rfl) ⟨1357154, by rfl⟩ : syracuseStep 1809539 = 2714309) B2714309
theorem B6102161 : Blo 1807605 6102161 := bstep (se 2 (by rfl) ⟨2288310, by rfl⟩ : syracuseStep 6102161 = 4576621) B4576621
theorem B1809555 : Blo 1807605 1809555 := bstep (se 1 (by rfl) ⟨1357166, by rfl⟩ : syracuseStep 1809555 = 2714333) B2714333
theorem B1809571 : Blo 1807605 1809571 := bstep (se 1 (by rfl) ⟨1357178, by rfl⟩ : syracuseStep 1809571 = 2714357) B2714357
theorem B2063539 : Blo 1807605 2063539 := bstep (se 1 (by rfl) ⟨1547654, by rfl⟩ : syracuseStep 2063539 = 3095309) B3095309
theorem B1809587 : Blo 1807605 1809587 := bstep (se 1 (by rfl) ⟨1357190, by rfl⟩ : syracuseStep 1809587 = 2714381) B2714381
theorem B1809603 : Blo 1807605 1809603 := bstep (se 1 (by rfl) ⟨1357202, by rfl⟩ : syracuseStep 1809603 = 2714405) B2714405
theorem B13040837 : Blo 1807605 13040837 := bstep (se 4 (by rfl) ⟨1222578, by rfl⟩ : syracuseStep 13040837 = 2445157) B2445157
theorem B4070609 : Blo 1807605 4070609 := bstep (se 2 (by rfl) ⟨1526478, by rfl⟩ : syracuseStep 4070609 = 3052957) B3052957
theorem B9157859 : Blo 1807605 9157859 := bstep (se 1 (by rfl) ⟨6868394, by rfl⟩ : syracuseStep 9157859 = 13736789) B13736789
theorem B4070627 : Blo 1807605 4070627 := bstep (se 1 (by rfl) ⟨3052970, by rfl⟩ : syracuseStep 4070627 = 6105941) B6105941
theorem B4578545 : Blo 1807605 4578545 := bstep (se 2 (by rfl) ⟨1716954, by rfl⟩ : syracuseStep 4578545 = 3433909) B3433909
theorem B5152049 : Blo 1807605 5152049 := bstep (se 2 (by rfl) ⟨1932018, by rfl⟩ : syracuseStep 5152049 = 3864037) B3864037
theorem B1957331 : Blo 1807605 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B4070897 : Blo 1807605 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B4070915 : Blo 1807605 4070915 := bstep (se 1 (by rfl) ⟨3053186, by rfl⟩ : syracuseStep 4070915 = 6106373) B6106373
theorem B11591237 : Blo 1807605 11591237 := bstep (se 4 (by rfl) ⟨1086678, by rfl⟩ : syracuseStep 11591237 = 2173357) B2173357
theorem B7724621 : Blo 1807605 7724621 := bstep (se 3 (by rfl) ⟨1448366, by rfl⟩ : syracuseStep 7724621 = 2896733) B2896733
theorem B5791313 : Blo 1807605 5791313 := bstep (se 2 (by rfl) ⟨2171742, by rfl⟩ : syracuseStep 5791313 = 4343485) B4343485
theorem B8814221 : Blo 1807605 8814221 := bstep (se 3 (by rfl) ⟨1652666, by rfl⟩ : syracuseStep 8814221 = 3305333) B3305333
theorem B6102701 : Blo 1807605 6102701 := bstep (se 3 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 6102701 = 2288513) B2288513
theorem B6102755 : Blo 1807605 6102755 := bstep (se 1 (by rfl) ⟨4577066, by rfl⟩ : syracuseStep 6102755 = 9154133) B9154133
theorem B4071185 : Blo 1807605 4071185 := bstep (se 2 (by rfl) ⟨1526694, by rfl⟩ : syracuseStep 4071185 = 3053389) B3053389
theorem B4071203 : Blo 1807605 4071203 := bstep (se 1 (by rfl) ⟨3053402, by rfl⟩ : syracuseStep 4071203 = 6106805) B6106805
theorem B6864689 : Blo 1807605 6864689 := bstep (se 2 (by rfl) ⟨2574258, by rfl⟩ : syracuseStep 6864689 = 5148517) B5148517
theorem B2711411 : Blo 1807605 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B4890509 : Blo 1807605 4890509 := bstep (se 3 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 4890509 = 1833941) B1833941
theorem B2711441 : Blo 1807605 2711441 := bstep (se 2 (by rfl) ⟨1016790, by rfl⟩ : syracuseStep 2711441 = 2033581) B2033581
theorem B2711459 : Blo 1807605 2711459 := bstep (se 1 (by rfl) ⟨2033594, by rfl⟩ : syracuseStep 2711459 = 4067189) B4067189
theorem B7724963 : Blo 1807605 7724963 := bstep (se 1 (by rfl) ⟨5793722, by rfl⟩ : syracuseStep 7724963 = 11587445) B11587445
theorem B2711489 : Blo 1807605 2711489 := bstep (se 2 (by rfl) ⟨1016808, by rfl⟩ : syracuseStep 2711489 = 2033617) B2033617
theorem B2711507 : Blo 1807605 2711507 := bstep (se 1 (by rfl) ⟨2033630, by rfl⟩ : syracuseStep 2711507 = 4067261) B4067261
theorem B2711537 : Blo 1807605 2711537 := bstep (se 2 (by rfl) ⟨1016826, by rfl⟩ : syracuseStep 2711537 = 2033653) B2033653
theorem B6103025 : Blo 1807605 6103025 := bstep (se 2 (by rfl) ⟨2288634, by rfl⟩ : syracuseStep 6103025 = 4577269) B4577269
theorem B2711627 : Blo 1807605 2711627 := bstep (se 1 (by rfl) ⟨2033720, by rfl⟩ : syracuseStep 2711627 = 4067441) B4067441
theorem B2711639 : Blo 1807605 2711639 := bstep (se 1 (by rfl) ⟨2033729, by rfl⟩ : syracuseStep 2711639 = 4067459) B4067459
theorem B6103133 : Blo 1807605 6103133 := bstep (se 3 (by rfl) ⟨1144337, by rfl⟩ : syracuseStep 6103133 = 2288675) B2288675
theorem B4071563 : Blo 1807605 4071563 := bstep (se 1 (by rfl) ⟨3053672, by rfl⟩ : syracuseStep 4071563 = 6107345) B6107345
theorem B2711705 : Blo 1807605 2711705 := bstep (se 2 (by rfl) ⟨1016889, by rfl⟩ : syracuseStep 2711705 = 2033779) B2033779
theorem B19546373 : Blo 1807605 19546373 := bstep (se 4 (by rfl) ⟨1832472, by rfl⟩ : syracuseStep 19546373 = 3664945) B3664945
theorem B2711819 : Blo 1807605 2711819 := bstep (se 1 (by rfl) ⟨2033864, by rfl⟩ : syracuseStep 2711819 = 4067729) B4067729
theorem B2711831 : Blo 1807605 2711831 := bstep (se 1 (by rfl) ⟨2033873, by rfl⟩ : syracuseStep 2711831 = 4067747) B4067747
theorem B6865175 : Blo 1807605 6865175 := bstep (se 1 (by rfl) ⟨5148881, by rfl⟩ : syracuseStep 6865175 = 10297763) B10297763
theorem B6521111 : Blo 1807605 6521111 := bstep (se 1 (by rfl) ⟨4890833, by rfl⟩ : syracuseStep 6521111 = 9781667) B9781667
theorem B3432755 : Blo 1807605 3432755 := bstep (se 1 (by rfl) ⟨2574566, by rfl⟩ : syracuseStep 3432755 = 5149133) B5149133
theorem B4579649 : Blo 1807605 4579649 := bstep (se 2 (by rfl) ⟨1717368, by rfl⟩ : syracuseStep 4579649 = 3434737) B3434737
theorem B2711897 : Blo 1807605 2711897 := bstep (se 2 (by rfl) ⟨1016961, by rfl⟩ : syracuseStep 2711897 = 2033923) B2033923
theorem B3432793 : Blo 1807605 3432793 := bstep (se 2 (by rfl) ⟨1287297, by rfl⟩ : syracuseStep 3432793 = 2574595) B2574595
theorem B2712011 : Blo 1807605 2712011 := bstep (se 1 (by rfl) ⟨2034008, by rfl⟩ : syracuseStep 2712011 = 4068017) B4068017
theorem B2712023 : Blo 1807605 2712023 := bstep (se 1 (by rfl) ⟨2034017, by rfl⟩ : syracuseStep 2712023 = 4068035) B4068035
theorem B2712089 : Blo 1807605 2712089 := bstep (se 2 (by rfl) ⟨1017033, by rfl⟩ : syracuseStep 2712089 = 2034067) B2034067
theorem B2712203 : Blo 1807605 2712203 := bstep (se 1 (by rfl) ⟨2034152, by rfl⟩ : syracuseStep 2712203 = 4068305) B4068305
theorem B2712215 : Blo 1807605 2712215 := bstep (se 1 (by rfl) ⟨2034161, by rfl⟩ : syracuseStep 2712215 = 4068323) B4068323
theorem B15442649 : Blo 1807605 15442649 := bstep (se 2 (by rfl) ⟨5790993, by rfl⟩ : syracuseStep 15442649 = 11581987) B11581987
theorem B2712281 : Blo 1807605 2712281 := bstep (se 2 (by rfl) ⟨1017105, by rfl⟩ : syracuseStep 2712281 = 2034211) B2034211
theorem B3433241 : Blo 1807605 3433241 := bstep (se 2 (by rfl) ⟨1287465, by rfl⟩ : syracuseStep 3433241 = 2574931) B2574931
theorem B13394723 : Blo 1807605 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B2712395 : Blo 1807605 2712395 := bstep (se 1 (by rfl) ⟨2034296, by rfl⟩ : syracuseStep 2712395 = 4068593) B4068593
theorem B2712407 : Blo 1807605 2712407 := bstep (se 1 (by rfl) ⟨2034305, by rfl⟩ : syracuseStep 2712407 = 4068611) B4068611
theorem B4580185 : Blo 1807605 4580185 := bstep (se 2 (by rfl) ⟨1717569, by rfl⟩ : syracuseStep 4580185 = 3435139) B3435139
theorem B2712473 : Blo 1807605 2712473 := bstep (se 2 (by rfl) ⟨1017177, by rfl⟩ : syracuseStep 2712473 = 2034355) B2034355
theorem B6865843 : Blo 1807605 6865843 := bstep (se 1 (by rfl) ⟨5149382, by rfl⟩ : syracuseStep 6865843 = 10298765) B10298765
theorem B9159641 : Blo 1807605 9159641 := bstep (se 2 (by rfl) ⟨3434865, by rfl⟩ : syracuseStep 9159641 = 6869731) B6869731
theorem B2712587 : Blo 1807605 2712587 := bstep (se 1 (by rfl) ⟨2034440, by rfl⟩ : syracuseStep 2712587 = 4068881) B4068881
theorem B2712599 : Blo 1807605 2712599 := bstep (se 1 (by rfl) ⟨2034449, by rfl⟩ : syracuseStep 2712599 = 4068899) B4068899
theorem B5497931 : Blo 1807605 5497931 := bstep (se 1 (by rfl) ⟨4123448, by rfl⟩ : syracuseStep 5497931 = 8246897) B8246897
theorem B2712665 : Blo 1807605 2712665 := bstep (se 2 (by rfl) ⟨1017249, by rfl⟩ : syracuseStep 2712665 = 2034499) B2034499
theorem B6186077 : Blo 1807605 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B10183781 : Blo 1807605 10183781 := bstep (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) B1909459
theorem B2712779 : Blo 1807605 2712779 := bstep (se 1 (by rfl) ⟨2034584, by rfl⟩ : syracuseStep 2712779 = 4069169) B4069169
theorem B6104267 : Blo 1807605 6104267 := bstep (se 1 (by rfl) ⟨4578200, by rfl⟩ : syracuseStep 6104267 = 9156401) B9156401
theorem B2712791 : Blo 1807605 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B5219549 : Blo 1807605 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B15451397 : Blo 1807605 15451397 := bstep (se 4 (by rfl) ⟨1448568, by rfl⟩ : syracuseStep 15451397 = 2897137) B2897137
theorem B2712857 : Blo 1807605 2712857 := bstep (se 2 (by rfl) ⟨1017321, by rfl⟩ : syracuseStep 2712857 = 2034643) B2034643
theorem B2712971 : Blo 1807605 2712971 := bstep (se 1 (by rfl) ⟨2034728, by rfl⟩ : syracuseStep 2712971 = 4069457) B4069457
theorem B2712983 : Blo 1807605 2712983 := bstep (se 1 (by rfl) ⟨2034737, by rfl⟩ : syracuseStep 2712983 = 4069475) B4069475
theorem B26076593 : Blo 1807605 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B2713049 : Blo 1807605 2713049 := bstep (se 2 (by rfl) ⟨1017393, by rfl⟩ : syracuseStep 2713049 = 2034787) B2034787
theorem B6104537 : Blo 1807605 6104537 := bstep (se 2 (by rfl) ⟨2289201, by rfl⟩ : syracuseStep 6104537 = 4578403) B4578403
theorem B3433985 : Blo 1807605 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B2713163 : Blo 1807605 2713163 := bstep (se 1 (by rfl) ⟨2034872, by rfl⟩ : syracuseStep 2713163 = 4069745) B4069745
theorem B2319959 : Blo 1807605 2319959 := bstep (se 1 (by rfl) ⟨1739969, by rfl⟩ : syracuseStep 2319959 = 3479939) B3479939
theorem B2713175 : Blo 1807605 2713175 := bstep (se 1 (by rfl) ⟨2034881, by rfl⟩ : syracuseStep 2713175 = 4069763) B4069763
theorem B13395557 : Blo 1807605 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B2713241 : Blo 1807605 2713241 := bstep (se 2 (by rfl) ⟨1017465, by rfl⟩ : syracuseStep 2713241 = 2034931) B2034931
theorem B87975629 : Blo 1807605 87975629 := bstep (se 3 (by rfl) ⟨16495430, by rfl⟩ : syracuseStep 87975629 = 32990861) B32990861
theorem B2713355 : Blo 1807605 2713355 := bstep (se 1 (by rfl) ⟨2035016, by rfl⟩ : syracuseStep 2713355 = 4070033) B4070033
theorem B3434251 : Blo 1807605 3434251 := bstep (se 1 (by rfl) ⟨2575688, by rfl⟩ : syracuseStep 3434251 = 5151377) B5151377
theorem B2713367 : Blo 1807605 2713367 := bstep (se 1 (by rfl) ⟨2035025, by rfl⟩ : syracuseStep 2713367 = 4070051) B4070051
theorem B2713433 : Blo 1807605 2713433 := bstep (se 2 (by rfl) ⟨1017537, by rfl⟩ : syracuseStep 2713433 = 2035075) B2035075
theorem B1984439 : Blo 1807605 1984439 := bstep (se 1 (by rfl) ⟨1488329, by rfl⟩ : syracuseStep 1984439 = 2976659) B2976659
theorem B2713547 : Blo 1807605 2713547 := bstep (se 1 (by rfl) ⟨2035160, by rfl⟩ : syracuseStep 2713547 = 4070321) B4070321
theorem B2713559 : Blo 1807605 2713559 := bstep (se 1 (by rfl) ⟨2035169, by rfl⟩ : syracuseStep 2713559 = 4070339) B4070339
theorem B2713625 : Blo 1807605 2713625 := bstep (se 2 (by rfl) ⟨1017609, by rfl⟩ : syracuseStep 2713625 = 2035219) B2035219
theorem B2033707 : Blo 1807605 2033707 := bstep (se 1 (by rfl) ⟨1525280, by rfl⟩ : syracuseStep 2033707 = 3050561) B3050561
theorem B8693891 : Blo 1807605 8693891 := bstep (se 1 (by rfl) ⟨6520418, by rfl⟩ : syracuseStep 8693891 = 13040837) B13040837
theorem B2713739 : Blo 1807605 2713739 := bstep (se 1 (by rfl) ⟨2035304, by rfl⟩ : syracuseStep 2713739 = 4070609) B4070609
theorem B6867089 : Blo 1807605 6867089 := bstep (se 2 (by rfl) ⟨2575158, by rfl⟩ : syracuseStep 6867089 = 5150317) B5150317
theorem B2033815 : Blo 1807605 2033815 := bstep (se 1 (by rfl) ⟨1525361, by rfl⟩ : syracuseStep 2033815 = 3050723) B3050723
theorem B6105239 : Blo 1807605 6105239 := bstep (se 1 (by rfl) ⟨4578929, by rfl⟩ : syracuseStep 6105239 = 9157859) B9157859
theorem B2713751 : Blo 1807605 2713751 := bstep (se 1 (by rfl) ⟨2035313, by rfl⟩ : syracuseStep 2713751 = 4070627) B4070627
theorem B3434699 : Blo 1807605 3434699 := bstep (se 1 (by rfl) ⟨2576024, by rfl⟩ : syracuseStep 3434699 = 5152049) B5152049
theorem B2713817 : Blo 1807605 2713817 := bstep (se 2 (by rfl) ⟨1017681, by rfl⟩ : syracuseStep 2713817 = 2035363) B2035363
theorem B11749697 : Blo 1807605 11749697 := bstep (se 2 (by rfl) ⟨4406136, by rfl⟩ : syracuseStep 11749697 = 8812273) B8812273
theorem B2033995 : Blo 1807605 2033995 := bstep (se 1 (by rfl) ⟨1525496, by rfl⟩ : syracuseStep 2033995 = 3050993) B3050993
theorem B2713931 : Blo 1807605 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B2713943 : Blo 1807605 2713943 := bstep (se 1 (by rfl) ⟨2035457, by rfl⟩ : syracuseStep 2713943 = 4070915) B4070915
theorem B3434881 : Blo 1807605 3434881 := bstep (se 2 (by rfl) ⟨1288080, by rfl⟩ : syracuseStep 3434881 = 2576161) B2576161
theorem B7727491 : Blo 1807605 7727491 := bstep (se 1 (by rfl) ⟨5795618, by rfl⟩ : syracuseStep 7727491 = 11591237) B11591237
theorem B3860875 : Blo 1807605 3860875 := bstep (se 1 (by rfl) ⟨2895656, by rfl⟩ : syracuseStep 3860875 = 5791313) B5791313
theorem B2714009 : Blo 1807605 2714009 := bstep (se 2 (by rfl) ⟨1017753, by rfl⟩ : syracuseStep 2714009 = 2035507) B2035507
theorem B5876147 : Blo 1807605 5876147 := bstep (se 1 (by rfl) ⟨4407110, by rfl⟩ : syracuseStep 5876147 = 8814221) B8814221
theorem B2034103 : Blo 1807605 2034103 := bstep (se 1 (by rfl) ⟨1525577, by rfl⟩ : syracuseStep 2034103 = 3051155) B3051155
theorem B2714123 : Blo 1807605 2714123 := bstep (se 1 (by rfl) ⟨2035592, by rfl⟩ : syracuseStep 2714123 = 4071185) B4071185
theorem B2714135 : Blo 1807605 2714135 := bstep (se 1 (by rfl) ⟨2035601, by rfl⟩ : syracuseStep 2714135 = 4071203) B4071203
theorem B2714201 : Blo 1807605 2714201 := bstep (se 2 (by rfl) ⟨1017825, by rfl⟩ : syracuseStep 2714201 = 2035651) B2035651
theorem B2034283 : Blo 1807605 2034283 := bstep (se 1 (by rfl) ⟨1525712, by rfl⟩ : syracuseStep 2034283 = 3051425) B3051425
theorem B29723267 : Blo 1807605 29723267 := bstep (se 1 (by rfl) ⟨22292450, by rfl⟩ : syracuseStep 29723267 = 44584901) B44584901
theorem B2091691 : Blo 1807605 2091691 := bstep (se 1 (by rfl) ⟨1568768, by rfl⟩ : syracuseStep 2091691 = 3137537) B3137537
theorem B6105779 : Blo 1807605 6105779 := bstep (se 1 (by rfl) ⟨4579334, by rfl⟩ : syracuseStep 6105779 = 9158669) B9158669
theorem B2714315 : Blo 1807605 2714315 := bstep (se 1 (by rfl) ⟨2035736, by rfl⟩ : syracuseStep 2714315 = 4071473) B4071473
theorem B2034391 : Blo 1807605 2034391 := bstep (se 1 (by rfl) ⟨1525793, by rfl⟩ : syracuseStep 2034391 = 3051587) B3051587
theorem B3861209 : Blo 1807605 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B3435223 : Blo 1807605 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B2714327 : Blo 1807605 2714327 := bstep (se 1 (by rfl) ⟨2035745, by rfl⟩ : syracuseStep 2714327 = 4071491) B4071491
theorem B14666501 : Blo 1807605 14666501 := bstep (se 4 (by rfl) ⟨1374984, by rfl⟩ : syracuseStep 14666501 = 2749969) B2749969
theorem B2288407 : Blo 1807605 2288407 := bstep (se 1 (by rfl) ⟨1716305, by rfl⟩ : syracuseStep 2288407 = 3432611) B3432611
theorem B2714393 : Blo 1807605 2714393 := bstep (se 2 (by rfl) ⟨1017897, by rfl⟩ : syracuseStep 2714393 = 2035795) B2035795
theorem B6867787 : Blo 1807605 6867787 := bstep (se 1 (by rfl) ⟨5150840, by rfl⟩ : syracuseStep 6867787 = 10301681) B10301681
theorem B2034571 : Blo 1807605 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B6106049 : Blo 1807605 6106049 := bstep (se 2 (by rfl) ⟨2289768, by rfl⟩ : syracuseStep 6106049 = 4579537) B4579537
theorem B20605913 : Blo 1807605 20605913 := bstep (se 2 (by rfl) ⟨7727217, by rfl⟩ : syracuseStep 20605913 = 15454435) B15454435
theorem B2034679 : Blo 1807605 2034679 := bstep (se 1 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 2034679 = 3052019) B3052019
theorem B4123649 : Blo 1807605 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B3050507 : Blo 1807605 3050507 := bstep (se 1 (by rfl) ⟨2287880, by rfl⟩ : syracuseStep 3050507 = 4575761) B4575761
theorem B10996781 : Blo 1807605 10996781 := bstep (se 3 (by rfl) ⟨2061896, by rfl⟩ : syracuseStep 10996781 = 4123793) B4123793
theorem B19827787 : Blo 1807605 19827787 := bstep (se 1 (by rfl) ⟨14870840, by rfl⟩ : syracuseStep 19827787 = 29741681) B29741681
theorem B6868061 : Blo 1807605 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B12536963 : Blo 1807605 12536963 := bstep (se 1 (by rfl) ⟨9402722, by rfl⟩ : syracuseStep 12536963 = 18805445) B18805445
theorem B3050635 : Blo 1807605 3050635 := bstep (se 1 (by rfl) ⟨2287976, by rfl⟩ : syracuseStep 3050635 = 4575953) B4575953
theorem B2034859 : Blo 1807605 2034859 := bstep (se 1 (by rfl) ⟨1526144, by rfl⟩ : syracuseStep 2034859 = 3052289) B3052289
theorem B9153809 : Blo 1807605 9153809 := bstep (se 2 (by rfl) ⟨3432678, by rfl⟩ : syracuseStep 9153809 = 6865357) B6865357
theorem B2034967 : Blo 1807605 2034967 := bstep (se 1 (by rfl) ⟨1526225, by rfl⟩ : syracuseStep 2034967 = 3052451) B3052451
theorem B3050777 : Blo 1807605 3050777 := bstep (se 2 (by rfl) ⟨1144041, by rfl⟩ : syracuseStep 3050777 = 2288083) B2288083
theorem B4345139 : Blo 1807605 4345139 := bstep (se 1 (by rfl) ⟨3258854, by rfl⟩ : syracuseStep 4345139 = 6517709) B6517709
theorem B4345177 : Blo 1807605 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B3050905 : Blo 1807605 3050905 := bstep (se 2 (by rfl) ⟨1144089, by rfl⟩ : syracuseStep 3050905 = 2288179) B2288179
theorem B9153971 : Blo 1807605 9153971 := bstep (se 1 (by rfl) ⟨6865478, by rfl⟩ : syracuseStep 9153971 = 13730957) B13730957
theorem B5148107 : Blo 1807605 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B2035147 : Blo 1807605 2035147 := bstep (se 1 (by rfl) ⟨1526360, by rfl⟩ : syracuseStep 2035147 = 3052721) B3052721
theorem B6106589 : Blo 1807605 6106589 := bstep (se 3 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 6106589 = 2289971) B2289971
theorem B2035255 : Blo 1807605 2035255 := bstep (se 1 (by rfl) ⟨1526441, by rfl⟩ : syracuseStep 2035255 = 3052883) B3052883
theorem B11005541 : Blo 1807605 11005541 := bstep (se 4 (by rfl) ⟨1031769, by rfl⟩ : syracuseStep 11005541 = 2063539) B2063539
theorem B3305099 : Blo 1807605 3305099 := bstep (se 1 (by rfl) ⟨2478824, by rfl⟩ : syracuseStep 3305099 = 4957649) B4957649
theorem B2035435 : Blo 1807605 2035435 := bstep (se 1 (by rfl) ⟨1526576, by rfl⟩ : syracuseStep 2035435 = 3053153) B3053153
theorem B6868759 : Blo 1807605 6868759 := bstep (se 1 (by rfl) ⟨5151569, by rfl⟩ : syracuseStep 6868759 = 10303139) B10303139
theorem B2035543 : Blo 1807605 2035543 := bstep (se 1 (by rfl) ⟨1526657, by rfl⟩ : syracuseStep 2035543 = 3053315) B3053315
theorem B4067225 : Blo 1807605 4067225 := bstep (se 2 (by rfl) ⟨1525209, by rfl⟩ : syracuseStep 4067225 = 3050419) B3050419
theorem B2576281 : Blo 1807605 2576281 := bstep (se 2 (by rfl) ⟨966105, by rfl⟩ : syracuseStep 2576281 = 1932211) B1932211
theorem B10301363 : Blo 1807605 10301363 := bstep (se 1 (by rfl) ⟨7726022, by rfl⟩ : syracuseStep 10301363 = 15452045) B15452045
theorem B7335859 : Blo 1807605 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B3051479 : Blo 1807605 3051479 := bstep (se 1 (by rfl) ⟨2288609, by rfl⟩ : syracuseStep 3051479 = 4577219) B4577219
theorem B4067315 : Blo 1807605 4067315 := bstep (se 1 (by rfl) ⟨3050486, by rfl⟩ : syracuseStep 4067315 = 6100973) B6100973
theorem B2035723 : Blo 1807605 2035723 := bstep (se 1 (by rfl) ⟨1526792, by rfl⟩ : syracuseStep 2035723 = 3053585) B3053585
theorem B4067351 : Blo 1807605 4067351 := bstep (se 1 (by rfl) ⟨3050513, by rfl⟩ : syracuseStep 4067351 = 6101027) B6101027
theorem B3051607 : Blo 1807605 3051607 := bstep (se 1 (by rfl) ⟨2288705, by rfl⟩ : syracuseStep 3051607 = 4577411) B4577411
theorem B7729303 : Blo 1807605 7729303 := bstep (se 1 (by rfl) ⟨5796977, by rfl⟩ : syracuseStep 7729303 = 11593955) B11593955
theorem B3666113 : Blo 1807605 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B3862721 : Blo 1807605 3862721 := bstep (se 2 (by rfl) ⟨1448520, by rfl⟩ : syracuseStep 3862721 = 2897041) B2897041
theorem B4067531 : Blo 1807605 4067531 := bstep (se 1 (by rfl) ⟨3050648, by rfl⟩ : syracuseStep 4067531 = 6101297) B6101297
theorem B2937035 : Blo 1807605 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B4067585 : Blo 1807605 4067585 := bstep (se 2 (by rfl) ⟨1525344, by rfl⟩ : syracuseStep 4067585 = 3050689) B3050689
theorem B50172205 : Blo 1807605 50172205 := bstep (se 3 (by rfl) ⟨9407288, by rfl⟩ : syracuseStep 50172205 = 18814577) B18814577
theorem B2445719 : Blo 1807605 2445719 := bstep (se 1 (by rfl) ⟨1834289, by rfl⟩ : syracuseStep 2445719 = 3668579) B3668579
theorem B23171507 : Blo 1807605 23171507 := bstep (se 1 (by rfl) ⟨17378630, by rfl⟩ : syracuseStep 23171507 = 34757261) B34757261
theorem B2290123 : Blo 1807605 2290123 := bstep (se 1 (by rfl) ⟨1717592, by rfl⟩ : syracuseStep 2290123 = 3435185) B3435185
theorem B4067801 : Blo 1807605 4067801 := bstep (se 2 (by rfl) ⟨1525425, by rfl⟩ : syracuseStep 4067801 = 3050851) B3050851
theorem B3666455 : Blo 1807605 3666455 := bstep (se 1 (by rfl) ⟨2749841, by rfl⟩ : syracuseStep 3666455 = 5499683) B5499683
theorem B6869549 : Blo 1807605 6869549 := bstep (se 3 (by rfl) ⟨1288040, by rfl⟩ : syracuseStep 6869549 = 2576081) B2576081
theorem B4067891 : Blo 1807605 4067891 := bstep (se 1 (by rfl) ⟨3050918, by rfl⟩ : syracuseStep 4067891 = 6101837) B6101837
theorem B4067927 : Blo 1807605 4067927 := bstep (se 1 (by rfl) ⟨3050945, by rfl⟩ : syracuseStep 4067927 = 6101891) B6101891
theorem B6517421 : Blo 1807605 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B4575923 : Blo 1807605 4575923 := bstep (se 1 (by rfl) ⟨3431942, by rfl⟩ : syracuseStep 4575923 = 6863885) B6863885
theorem B3052235 : Blo 1807605 3052235 := bstep (se 1 (by rfl) ⟨2289176, by rfl⟩ : syracuseStep 3052235 = 4578353) B4578353
theorem B8245981 : Blo 1807605 8245981 := bstep (se 3 (by rfl) ⟨1546121, by rfl⟩ : syracuseStep 8245981 = 3092243) B3092243
theorem B4068107 : Blo 1807605 4068107 := bstep (se 1 (by rfl) ⟨3051080, by rfl⟩ : syracuseStep 4068107 = 6102161) B6102161
theorem B4068161 : Blo 1807605 4068161 := bstep (se 2 (by rfl) ⟨1525560, by rfl⟩ : syracuseStep 4068161 = 3051121) B3051121
theorem B8926027 : Blo 1807605 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B3052363 : Blo 1807605 3052363 := bstep (se 1 (by rfl) ⟨2289272, by rfl⟩ : syracuseStep 3052363 = 4578545) B4578545
theorem B2896727 : Blo 1807605 2896727 := bstep (se 1 (by rfl) ⟨2172545, by rfl⟩ : syracuseStep 2896727 = 4345091) B4345091
theorem B3052505 : Blo 1807605 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B3863575 : Blo 1807605 3863575 := bstep (se 1 (by rfl) ⟨2897681, by rfl⟩ : syracuseStep 3863575 = 5795363) B5795363
theorem B4068377 : Blo 1807605 4068377 := bstep (se 2 (by rfl) ⟨1525641, by rfl⟩ : syracuseStep 4068377 = 3051283) B3051283
theorem B5149747 : Blo 1807605 5149747 := bstep (se 1 (by rfl) ⟨3862310, by rfl⟩ : syracuseStep 5149747 = 7724621) B7724621
theorem B3052633 : Blo 1807605 3052633 := bstep (se 2 (by rfl) ⟨1144737, by rfl⟩ : syracuseStep 3052633 = 2289475) B2289475
theorem B4068467 : Blo 1807605 4068467 := bstep (se 1 (by rfl) ⟨3051350, by rfl⟩ : syracuseStep 4068467 = 6102701) B6102701
theorem B4068503 : Blo 1807605 4068503 := bstep (se 1 (by rfl) ⟨3051377, by rfl⟩ : syracuseStep 4068503 = 6102755) B6102755
theorem B4576459 : Blo 1807605 4576459 := bstep (se 1 (by rfl) ⟨3432344, by rfl⟩ : syracuseStep 4576459 = 6864689) B6864689
theorem B1807607 : Blo 1807605 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B1807627 : Blo 1807605 1807627 := bstep (se 1 (by rfl) ⟨1355720, by rfl⟩ : syracuseStep 1807627 = 2711441) B2711441
theorem B1807639 : Blo 1807605 1807639 := bstep (se 1 (by rfl) ⟨1355729, by rfl⟩ : syracuseStep 1807639 = 2711459) B2711459
theorem B5149975 : Blo 1807605 5149975 := bstep (se 1 (by rfl) ⟨3862481, by rfl⟩ : syracuseStep 5149975 = 7724963) B7724963
theorem B1807659 : Blo 1807605 1807659 := bstep (se 1 (by rfl) ⟨1355744, by rfl⟩ : syracuseStep 1807659 = 2711489) B2711489
theorem B1807671 : Blo 1807605 1807671 := bstep (se 1 (by rfl) ⟨1355753, by rfl⟩ : syracuseStep 1807671 = 2711507) B2711507
theorem B1807691 : Blo 1807605 1807691 := bstep (se 1 (by rfl) ⟨1355768, by rfl⟩ : syracuseStep 1807691 = 2711537) B2711537
theorem B4068683 : Blo 1807605 4068683 := bstep (se 1 (by rfl) ⟨3051512, by rfl⟩ : syracuseStep 4068683 = 6103025) B6103025
theorem B9155915 : Blo 1807605 9155915 := bstep (se 1 (by rfl) ⟨6866936, by rfl⟩ : syracuseStep 9155915 = 13733873) B13733873
theorem B1807703 : Blo 1807605 1807703 := bstep (se 1 (by rfl) ⟨1355777, by rfl⟩ : syracuseStep 1807703 = 2711555) B2711555
theorem B7329113 : Blo 1807605 7329113 := bstep (se 2 (by rfl) ⟨2748417, by rfl⟩ : syracuseStep 7329113 = 5496835) B5496835
theorem B4576601 : Blo 1807605 4576601 := bstep (se 2 (by rfl) ⟨1716225, by rfl⟩ : syracuseStep 4576601 = 3432451) B3432451
theorem B13727069 : Blo 1807605 13727069 := bstep (se 3 (by rfl) ⟨2573825, by rfl⟩ : syracuseStep 13727069 = 5147651) B5147651
theorem B10302821 : Blo 1807605 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B1807723 : Blo 1807605 1807723 := bstep (se 1 (by rfl) ⟨1355792, by rfl⟩ : syracuseStep 1807723 = 2711585) B2711585
theorem B1807735 : Blo 1807605 1807735 := bstep (se 1 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 1807735 = 2711603) B2711603
theorem B4068737 : Blo 1807605 4068737 := bstep (se 2 (by rfl) ⟨1525776, by rfl⟩ : syracuseStep 4068737 = 3051553) B3051553
theorem B1807755 : Blo 1807605 1807755 := bstep (se 1 (by rfl) ⟨1355816, by rfl⟩ : syracuseStep 1807755 = 2711633) B2711633
theorem B1807767 : Blo 1807605 1807767 := bstep (se 1 (by rfl) ⟨1355825, by rfl⟩ : syracuseStep 1807767 = 2711651) B2711651
theorem B1807787 : Blo 1807605 1807787 := bstep (se 1 (by rfl) ⟨1355840, by rfl⟩ : syracuseStep 1807787 = 2711681) B2711681
theorem B1807799 : Blo 1807605 1807799 := bstep (se 1 (by rfl) ⟨1355849, by rfl⟩ : syracuseStep 1807799 = 2711699) B2711699
theorem B4347329 : Blo 1807605 4347329 := bstep (se 2 (by rfl) ⟨1630248, by rfl⟩ : syracuseStep 4347329 = 3260497) B3260497
theorem B1807819 : Blo 1807605 1807819 := bstep (se 1 (by rfl) ⟨1355864, by rfl⟩ : syracuseStep 1807819 = 2711729) B2711729
theorem B1807831 : Blo 1807605 1807831 := bstep (se 1 (by rfl) ⟨1355873, by rfl⟩ : syracuseStep 1807831 = 2711747) B2711747
theorem B1807851 : Blo 1807605 1807851 := bstep (se 1 (by rfl) ⟨1355888, by rfl⟩ : syracuseStep 1807851 = 2711777) B2711777
theorem B1807863 : Blo 1807605 1807863 := bstep (se 1 (by rfl) ⟨1355897, by rfl⟩ : syracuseStep 1807863 = 2711795) B2711795
theorem B1807883 : Blo 1807605 1807883 := bstep (se 1 (by rfl) ⟨1355912, by rfl⟩ : syracuseStep 1807883 = 2711825) B2711825
theorem B1807895 : Blo 1807605 1807895 := bstep (se 1 (by rfl) ⟨1355921, by rfl⟩ : syracuseStep 1807895 = 2711843) B2711843
theorem B1807915 : Blo 1807605 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B1807927 : Blo 1807605 1807927 := bstep (se 1 (by rfl) ⟨1355945, by rfl⟩ : syracuseStep 1807927 = 2711891) B2711891
theorem B1807947 : Blo 1807605 1807947 := bstep (se 1 (by rfl) ⟨1355960, by rfl⟩ : syracuseStep 1807947 = 2711921) B2711921
theorem B1807959 : Blo 1807605 1807959 := bstep (se 1 (by rfl) ⟨1355969, by rfl⟩ : syracuseStep 1807959 = 2711939) B2711939
theorem B4068953 : Blo 1807605 4068953 := bstep (se 2 (by rfl) ⟨1525857, by rfl⟩ : syracuseStep 4068953 = 3051715) B3051715
theorem B3094105 : Blo 1807605 3094105 := bstep (se 2 (by rfl) ⟨1160289, by rfl⟩ : syracuseStep 3094105 = 2320579) B2320579
theorem B1807979 : Blo 1807605 1807979 := bstep (se 1 (by rfl) ⟨1355984, by rfl⟩ : syracuseStep 1807979 = 2711969) B2711969
theorem B1807991 : Blo 1807605 1807991 := bstep (se 1 (by rfl) ⟨1355993, by rfl⟩ : syracuseStep 1807991 = 2711987) B2711987
theorem B1808011 : Blo 1807605 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B1808023 : Blo 1807605 1808023 := bstep (se 1 (by rfl) ⟨1356017, by rfl⟩ : syracuseStep 1808023 = 2712035) B2712035
theorem B3053207 : Blo 1807605 3053207 := bstep (se 1 (by rfl) ⟨2289905, by rfl⟩ : syracuseStep 3053207 = 4579811) B4579811
theorem B1808043 : Blo 1807605 1808043 := bstep (se 1 (by rfl) ⟨1356032, by rfl⟩ : syracuseStep 1808043 = 2712065) B2712065
theorem B4069043 : Blo 1807605 4069043 := bstep (se 1 (by rfl) ⟨3051782, by rfl⟩ : syracuseStep 4069043 = 6103565) B6103565
theorem B1808055 : Blo 1807605 1808055 := bstep (se 1 (by rfl) ⟨1356041, by rfl⟩ : syracuseStep 1808055 = 2712083) B2712083
theorem B1808075 : Blo 1807605 1808075 := bstep (se 1 (by rfl) ⟨1356056, by rfl⟩ : syracuseStep 1808075 = 2712113) B2712113
theorem B1808087 : Blo 1807605 1808087 := bstep (se 1 (by rfl) ⟨1356065, by rfl⟩ : syracuseStep 1808087 = 2712131) B2712131
theorem B4069079 : Blo 1807605 4069079 := bstep (se 1 (by rfl) ⟨3051809, by rfl⟩ : syracuseStep 4069079 = 6103619) B6103619
theorem B14661337 : Blo 1807605 14661337 := bstep (se 2 (by rfl) ⟨5498001, by rfl⟩ : syracuseStep 14661337 = 10996003) B10996003
theorem B1808107 : Blo 1807605 1808107 := bstep (se 1 (by rfl) ⟨1356080, by rfl⟩ : syracuseStep 1808107 = 2712161) B2712161
theorem B1808119 : Blo 1807605 1808119 := bstep (se 1 (by rfl) ⟨1356089, by rfl⟩ : syracuseStep 1808119 = 2712179) B2712179
theorem B1808139 : Blo 1807605 1808139 := bstep (se 1 (by rfl) ⟨1356104, by rfl⟩ : syracuseStep 1808139 = 2712209) B2712209
theorem B1808151 : Blo 1807605 1808151 := bstep (se 1 (by rfl) ⟨1356113, by rfl⟩ : syracuseStep 1808151 = 2712227) B2712227
theorem B3053335 : Blo 1807605 3053335 := bstep (se 1 (by rfl) ⟨2290001, by rfl⟩ : syracuseStep 3053335 = 4580003) B4580003
theorem B1808171 : Blo 1807605 1808171 := bstep (se 1 (by rfl) ⟨1356128, by rfl⟩ : syracuseStep 1808171 = 2712257) B2712257
theorem B1808183 : Blo 1807605 1808183 := bstep (se 1 (by rfl) ⟨1356137, by rfl⟩ : syracuseStep 1808183 = 2712275) B2712275
theorem B62666561 : Blo 1807605 62666561 := bstep (se 2 (by rfl) ⟨23499960, by rfl⟩ : syracuseStep 62666561 = 46999921) B46999921
theorem B6100811 : Blo 1807605 6100811 := bstep (se 1 (by rfl) ⟨4575608, by rfl⟩ : syracuseStep 6100811 = 9151217) B9151217
theorem B1808203 : Blo 1807605 1808203 := bstep (se 1 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 1808203 = 2712305) B2712305
theorem B3864395 : Blo 1807605 3864395 := bstep (se 1 (by rfl) ⟨2898296, by rfl⟩ : syracuseStep 3864395 = 5796593) B5796593
theorem B1808215 : Blo 1807605 1808215 := bstep (se 1 (by rfl) ⟨1356161, by rfl⟩ : syracuseStep 1808215 = 2712323) B2712323
theorem B3667801 : Blo 1807605 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B1808235 : Blo 1807605 1808235 := bstep (se 1 (by rfl) ⟨1356176, by rfl⟩ : syracuseStep 1808235 = 2712353) B2712353
theorem B1808247 : Blo 1807605 1808247 := bstep (se 1 (by rfl) ⟨1356185, by rfl⟩ : syracuseStep 1808247 = 2712371) B2712371
theorem B1808267 : Blo 1807605 1808267 := bstep (se 1 (by rfl) ⟨1356200, by rfl⟩ : syracuseStep 1808267 = 2712401) B2712401
theorem B4069259 : Blo 1807605 4069259 := bstep (se 1 (by rfl) ⟨3051944, by rfl⟩ : syracuseStep 4069259 = 6103889) B6103889
theorem B3258263 : Blo 1807605 3258263 := bstep (se 1 (by rfl) ⟨2443697, by rfl⟩ : syracuseStep 3258263 = 4887395) B4887395
theorem B1808279 : Blo 1807605 1808279 := bstep (se 1 (by rfl) ⟨1356209, by rfl⟩ : syracuseStep 1808279 = 2712419) B2712419
theorem B1808299 : Blo 1807605 1808299 := bstep (se 1 (by rfl) ⟨1356224, by rfl⟩ : syracuseStep 1808299 = 2712449) B2712449
theorem B1808311 : Blo 1807605 1808311 := bstep (se 1 (by rfl) ⟨1356233, by rfl⟩ : syracuseStep 1808311 = 2712467) B2712467
theorem B4069313 : Blo 1807605 4069313 := bstep (se 2 (by rfl) ⟨1525992, by rfl⟩ : syracuseStep 4069313 = 3051985) B3051985
theorem B1808331 : Blo 1807605 1808331 := bstep (se 1 (by rfl) ⟨1356248, by rfl⟩ : syracuseStep 1808331 = 2712497) B2712497
theorem B1808343 : Blo 1807605 1808343 := bstep (se 1 (by rfl) ⟨1356257, by rfl⟩ : syracuseStep 1808343 = 2712515) B2712515
theorem B8689625 : Blo 1807605 8689625 := bstep (se 2 (by rfl) ⟨3258609, by rfl⟩ : syracuseStep 8689625 = 6517219) B6517219
theorem B1808363 : Blo 1807605 1808363 := bstep (se 1 (by rfl) ⟨1356272, by rfl⟩ : syracuseStep 1808363 = 2712545) B2712545
theorem B1808375 : Blo 1807605 1808375 := bstep (se 1 (by rfl) ⟨1356281, by rfl⟩ : syracuseStep 1808375 = 2712563) B2712563
theorem B1808395 : Blo 1807605 1808395 := bstep (se 1 (by rfl) ⟨1356296, by rfl⟩ : syracuseStep 1808395 = 2712593) B2712593
theorem B1808407 : Blo 1807605 1808407 := bstep (se 1 (by rfl) ⟨1356305, by rfl⟩ : syracuseStep 1808407 = 2712611) B2712611
theorem B1808427 : Blo 1807605 1808427 := bstep (se 1 (by rfl) ⟨1356320, by rfl⟩ : syracuseStep 1808427 = 2712641) B2712641
theorem B1808439 : Blo 1807605 1808439 := bstep (se 1 (by rfl) ⟨1356329, by rfl⟩ : syracuseStep 1808439 = 2712659) B2712659
theorem B1808459 : Blo 1807605 1808459 := bstep (se 1 (by rfl) ⟨1356344, by rfl⟩ : syracuseStep 1808459 = 2712689) B2712689
theorem B1808471 : Blo 1807605 1808471 := bstep (se 1 (by rfl) ⟨1356353, by rfl⟩ : syracuseStep 1808471 = 2712707) B2712707
theorem B6101081 : Blo 1807605 6101081 := bstep (se 2 (by rfl) ⟨2287905, by rfl⟩ : syracuseStep 6101081 = 4575811) B4575811
theorem B1808491 : Blo 1807605 1808491 := bstep (se 1 (by rfl) ⟨1356368, by rfl⟩ : syracuseStep 1808491 = 2712737) B2712737
theorem B1808503 : Blo 1807605 1808503 := bstep (se 1 (by rfl) ⟨1356377, by rfl⟩ : syracuseStep 1808503 = 2712755) B2712755
theorem B1808523 : Blo 1807605 1808523 := bstep (se 1 (by rfl) ⟨1356392, by rfl⟩ : syracuseStep 1808523 = 2712785) B2712785
theorem B20592791 : Blo 1807605 20592791 := bstep (se 1 (by rfl) ⟨15444593, by rfl⟩ : syracuseStep 20592791 = 30889187) B30889187
theorem B4577431 : Blo 1807605 4577431 := bstep (se 1 (by rfl) ⟨3433073, by rfl⟩ : syracuseStep 4577431 = 6866147) B6866147
theorem B1808535 : Blo 1807605 1808535 := bstep (se 1 (by rfl) ⟨1356401, by rfl⟩ : syracuseStep 1808535 = 2712803) B2712803
theorem B4069529 : Blo 1807605 4069529 := bstep (se 2 (by rfl) ⟨1526073, by rfl⟩ : syracuseStep 4069529 = 3052147) B3052147
theorem B1808555 : Blo 1807605 1808555 := bstep (se 1 (by rfl) ⟨1356416, by rfl⟩ : syracuseStep 1808555 = 2712833) B2712833
theorem B7723187 : Blo 1807605 7723187 := bstep (se 1 (by rfl) ⟨5792390, by rfl⟩ : syracuseStep 7723187 = 11584781) B11584781
theorem B1808567 : Blo 1807605 1808567 := bstep (se 1 (by rfl) ⟨1356425, by rfl⟩ : syracuseStep 1808567 = 2712851) B2712851
theorem B1808587 : Blo 1807605 1808587 := bstep (se 1 (by rfl) ⟨1356440, by rfl⟩ : syracuseStep 1808587 = 2712881) B2712881
theorem B1808599 : Blo 1807605 1808599 := bstep (se 1 (by rfl) ⟨1356449, by rfl⟩ : syracuseStep 1808599 = 2712899) B2712899
theorem B2750681 : Blo 1807605 2750681 := bstep (se 2 (by rfl) ⟨1031505, by rfl⟩ : syracuseStep 2750681 = 2063011) B2063011
theorem B1808619 : Blo 1807605 1808619 := bstep (se 1 (by rfl) ⟨1356464, by rfl⟩ : syracuseStep 1808619 = 2712929) B2712929
theorem B4069619 : Blo 1807605 4069619 := bstep (se 1 (by rfl) ⟨3052214, by rfl⟩ : syracuseStep 4069619 = 6104429) B6104429
theorem B1808631 : Blo 1807605 1808631 := bstep (se 1 (by rfl) ⟨1356473, by rfl⟩ : syracuseStep 1808631 = 2712947) B2712947
theorem B1808651 : Blo 1807605 1808651 := bstep (se 1 (by rfl) ⟨1356488, by rfl⟩ : syracuseStep 1808651 = 2712977) B2712977
theorem B1931531 : Blo 1807605 1931531 := bstep (se 1 (by rfl) ⟨1448648, by rfl⟩ : syracuseStep 1931531 = 2897297) B2897297
theorem B11589905 : Blo 1807605 11589905 := bstep (se 2 (by rfl) ⟨4346214, by rfl⟩ : syracuseStep 11589905 = 8692429) B8692429
theorem B1808663 : Blo 1807605 1808663 := bstep (se 1 (by rfl) ⟨1356497, by rfl⟩ : syracuseStep 1808663 = 2712995) B2712995
theorem B4069655 : Blo 1807605 4069655 := bstep (se 1 (by rfl) ⟨3052241, by rfl⟩ : syracuseStep 4069655 = 6104483) B6104483
theorem B1808683 : Blo 1807605 1808683 := bstep (se 1 (by rfl) ⟨1356512, by rfl⟩ : syracuseStep 1808683 = 2713025) B2713025
theorem B13031725 : Blo 1807605 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B1808695 : Blo 1807605 1808695 := bstep (se 1 (by rfl) ⟨1356521, by rfl⟩ : syracuseStep 1808695 = 2713043) B2713043
theorem B1808715 : Blo 1807605 1808715 := bstep (se 1 (by rfl) ⟨1356536, by rfl⟩ : syracuseStep 1808715 = 2713073) B2713073
theorem B2611531 : Blo 1807605 2611531 := bstep (se 1 (by rfl) ⟨1958648, by rfl⟩ : syracuseStep 2611531 = 3917297) B3917297
theorem B1808727 : Blo 1807605 1808727 := bstep (se 1 (by rfl) ⟨1356545, by rfl⟩ : syracuseStep 1808727 = 2713091) B2713091
theorem B15448421 : Blo 1807605 15448421 := bstep (se 4 (by rfl) ⟨1448289, by rfl⟩ : syracuseStep 15448421 = 2896579) B2896579
theorem B13039973 : Blo 1807605 13039973 := bstep (se 4 (by rfl) ⟨1222497, by rfl⟩ : syracuseStep 13039973 = 2444995) B2444995
theorem B1808747 : Blo 1807605 1808747 := bstep (se 1 (by rfl) ⟨1356560, by rfl⟩ : syracuseStep 1808747 = 2713121) B2713121
theorem B1808759 : Blo 1807605 1808759 := bstep (se 1 (by rfl) ⟨1356569, by rfl⟩ : syracuseStep 1808759 = 2713139) B2713139
theorem B1808779 : Blo 1807605 1808779 := bstep (se 1 (by rfl) ⟨1356584, by rfl⟩ : syracuseStep 1808779 = 2713169) B2713169
theorem B1808791 : Blo 1807605 1808791 := bstep (se 1 (by rfl) ⟨1356593, by rfl⟩ : syracuseStep 1808791 = 2713187) B2713187
theorem B1808811 : Blo 1807605 1808811 := bstep (se 1 (by rfl) ⟨1356608, by rfl⟩ : syracuseStep 1808811 = 2713217) B2713217
theorem B1808823 : Blo 1807605 1808823 := bstep (se 1 (by rfl) ⟨1356617, by rfl⟩ : syracuseStep 1808823 = 2713235) B2713235
theorem B3668417 : Blo 1807605 3668417 := bstep (se 2 (by rfl) ⟨1375656, by rfl⟩ : syracuseStep 3668417 = 2751313) B2751313
theorem B4069835 : Blo 1807605 4069835 := bstep (se 1 (by rfl) ⟨3052376, by rfl⟩ : syracuseStep 4069835 = 6104753) B6104753
theorem B1808843 : Blo 1807605 1808843 := bstep (se 1 (by rfl) ⟨1356632, by rfl⟩ : syracuseStep 1808843 = 2713265) B2713265
theorem B1808855 : Blo 1807605 1808855 := bstep (se 1 (by rfl) ⟨1356641, by rfl⟩ : syracuseStep 1808855 = 2713283) B2713283
theorem B1808875 : Blo 1807605 1808875 := bstep (se 1 (by rfl) ⟨1356656, by rfl⟩ : syracuseStep 1808875 = 2713313) B2713313
theorem B1808887 : Blo 1807605 1808887 := bstep (se 1 (by rfl) ⟨1356665, by rfl⟩ : syracuseStep 1808887 = 2713331) B2713331
theorem B4069889 : Blo 1807605 4069889 := bstep (se 2 (by rfl) ⟨1526208, by rfl⟩ : syracuseStep 4069889 = 3052417) B3052417
theorem B1808907 : Blo 1807605 1808907 := bstep (se 1 (by rfl) ⟨1356680, by rfl⟩ : syracuseStep 1808907 = 2713361) B2713361
theorem B1808919 : Blo 1807605 1808919 := bstep (se 1 (by rfl) ⟨1356689, by rfl⟩ : syracuseStep 1808919 = 2713379) B2713379
theorem B1808939 : Blo 1807605 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B1808951 : Blo 1807605 1808951 := bstep (se 1 (by rfl) ⟨1356713, by rfl⟩ : syracuseStep 1808951 = 2713427) B2713427
theorem B3258955 : Blo 1807605 3258955 := bstep (se 1 (by rfl) ⟨2444216, by rfl⟩ : syracuseStep 3258955 = 4888433) B4888433
theorem B4577867 : Blo 1807605 4577867 := bstep (se 1 (by rfl) ⟨3433400, by rfl⟩ : syracuseStep 4577867 = 6866801) B6866801
theorem B1808971 : Blo 1807605 1808971 := bstep (se 1 (by rfl) ⟨1356728, by rfl⟩ : syracuseStep 1808971 = 2713457) B2713457
theorem B1808983 : Blo 1807605 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B44022365 : Blo 1807605 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B1809003 : Blo 1807605 1809003 := bstep (se 1 (by rfl) ⟨1356752, by rfl⟩ : syracuseStep 1809003 = 2713505) B2713505
theorem B1809015 : Blo 1807605 1809015 := bstep (se 1 (by rfl) ⟨1356761, by rfl⟩ : syracuseStep 1809015 = 2713523) B2713523
theorem B1809035 : Blo 1807605 1809035 := bstep (se 1 (by rfl) ⟨1356776, by rfl⟩ : syracuseStep 1809035 = 2713553) B2713553
theorem B1809047 : Blo 1807605 1809047 := bstep (se 1 (by rfl) ⟨1356785, by rfl⟩ : syracuseStep 1809047 = 2713571) B2713571
theorem B14670487 : Blo 1807605 14670487 := bstep (se 1 (by rfl) ⟨11002865, by rfl⟩ : syracuseStep 14670487 = 22005731) B22005731
theorem B1809067 : Blo 1807605 1809067 := bstep (se 1 (by rfl) ⟨1356800, by rfl⟩ : syracuseStep 1809067 = 2713601) B2713601
theorem B4889267 : Blo 1807605 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B1809079 : Blo 1807605 1809079 := bstep (se 1 (by rfl) ⟨1356809, by rfl⟩ : syracuseStep 1809079 = 2713619) B2713619
theorem B1809099 : Blo 1807605 1809099 := bstep (se 1 (by rfl) ⟨1356824, by rfl⟩ : syracuseStep 1809099 = 2713649) B2713649
theorem B1809111 : Blo 1807605 1809111 := bstep (se 1 (by rfl) ⟨1356833, by rfl⟩ : syracuseStep 1809111 = 2713667) B2713667
theorem B4070105 : Blo 1807605 4070105 := bstep (se 2 (by rfl) ⟨1526289, by rfl⟩ : syracuseStep 4070105 = 3052579) B3052579
theorem B1809131 : Blo 1807605 1809131 := bstep (se 1 (by rfl) ⟨1356848, by rfl⟩ : syracuseStep 1809131 = 2713697) B2713697
theorem B1809143 : Blo 1807605 1809143 := bstep (se 1 (by rfl) ⟨1356857, by rfl⟩ : syracuseStep 1809143 = 2713715) B2713715
theorem B1809163 : Blo 1807605 1809163 := bstep (se 1 (by rfl) ⟨1356872, by rfl⟩ : syracuseStep 1809163 = 2713745) B2713745
theorem B6101783 : Blo 1807605 6101783 := bstep (se 1 (by rfl) ⟨4576337, by rfl⟩ : syracuseStep 6101783 = 9152675) B9152675
theorem B1809175 : Blo 1807605 1809175 := bstep (se 1 (by rfl) ⟨1356881, by rfl⟩ : syracuseStep 1809175 = 2713763) B2713763
theorem B1809195 : Blo 1807605 1809195 := bstep (se 1 (by rfl) ⟨1356896, by rfl⟩ : syracuseStep 1809195 = 2713793) B2713793
theorem B4070195 : Blo 1807605 4070195 := bstep (se 1 (by rfl) ⟨3052646, by rfl⟩ : syracuseStep 4070195 = 6105293) B6105293
theorem B1809207 : Blo 1807605 1809207 := bstep (se 1 (by rfl) ⟨1356905, by rfl⟩ : syracuseStep 1809207 = 2713811) B2713811
theorem B39623489 : Blo 1807605 39623489 := bstep (se 2 (by rfl) ⟨14858808, by rfl⟩ : syracuseStep 39623489 = 29717617) B29717617
theorem B1809227 : Blo 1807605 1809227 := bstep (se 1 (by rfl) ⟨1356920, by rfl⟩ : syracuseStep 1809227 = 2713841) B2713841
theorem B4070231 : Blo 1807605 4070231 := bstep (se 1 (by rfl) ⟨3052673, by rfl⟩ : syracuseStep 4070231 = 6105347) B6105347
theorem B1809239 : Blo 1807605 1809239 := bstep (se 1 (by rfl) ⟨1356929, by rfl⟩ : syracuseStep 1809239 = 2713859) B2713859
theorem B1809259 : Blo 1807605 1809259 := bstep (se 1 (by rfl) ⟨1356944, by rfl⟩ : syracuseStep 1809259 = 2713889) B2713889
theorem B1809271 : Blo 1807605 1809271 := bstep (se 1 (by rfl) ⟨1356953, by rfl⟩ : syracuseStep 1809271 = 2713907) B2713907
theorem B1809291 : Blo 1807605 1809291 := bstep (se 1 (by rfl) ⟨1356968, by rfl⟩ : syracuseStep 1809291 = 2713937) B2713937
theorem B1809303 : Blo 1807605 1809303 := bstep (se 1 (by rfl) ⟨1356977, by rfl⟩ : syracuseStep 1809303 = 2713955) B2713955
theorem B1809323 : Blo 1807605 1809323 := bstep (se 1 (by rfl) ⟨1356992, by rfl⟩ : syracuseStep 1809323 = 2713985) B2713985
theorem B1809335 : Blo 1807605 1809335 := bstep (se 1 (by rfl) ⟨1357001, by rfl⟩ : syracuseStep 1809335 = 2714003) B2714003
theorem B4578241 : Blo 1807605 4578241 := bstep (se 2 (by rfl) ⟨1716840, by rfl⟩ : syracuseStep 4578241 = 3433681) B3433681
theorem B1809355 : Blo 1807605 1809355 := bstep (se 1 (by rfl) ⟨1357016, by rfl⟩ : syracuseStep 1809355 = 2714033) B2714033
theorem B1809367 : Blo 1807605 1809367 := bstep (se 1 (by rfl) ⟨1357025, by rfl⟩ : syracuseStep 1809367 = 2714051) B2714051
theorem B1809387 : Blo 1807605 1809387 := bstep (se 1 (by rfl) ⟨1357040, by rfl⟩ : syracuseStep 1809387 = 2714081) B2714081
theorem B1809399 : Blo 1807605 1809399 := bstep (se 1 (by rfl) ⟨1357049, by rfl⟩ : syracuseStep 1809399 = 2714099) B2714099
theorem B4070411 : Blo 1807605 4070411 := bstep (se 1 (by rfl) ⟨3052808, by rfl⟩ : syracuseStep 4070411 = 6105617) B6105617
theorem B1809419 : Blo 1807605 1809419 := bstep (se 1 (by rfl) ⟨1357064, by rfl⟩ : syracuseStep 1809419 = 2714129) B2714129
theorem B1809431 : Blo 1807605 1809431 := bstep (se 1 (by rfl) ⟨1357073, by rfl⟩ : syracuseStep 1809431 = 2714147) B2714147
theorem B1809451 : Blo 1807605 1809451 := bstep (se 1 (by rfl) ⟨1357088, by rfl⟩ : syracuseStep 1809451 = 2714177) B2714177
theorem B1809463 : Blo 1807605 1809463 := bstep (se 1 (by rfl) ⟨1357097, by rfl⟩ : syracuseStep 1809463 = 2714195) B2714195
theorem B9157697 : Blo 1807605 9157697 := bstep (se 2 (by rfl) ⟨3434136, by rfl⟩ : syracuseStep 9157697 = 6868273) B6868273
theorem B4070465 : Blo 1807605 4070465 := bstep (se 2 (by rfl) ⟨1526424, by rfl⟩ : syracuseStep 4070465 = 3052849) B3052849
theorem B1809483 : Blo 1807605 1809483 := bstep (se 1 (by rfl) ⟨1357112, by rfl⟩ : syracuseStep 1809483 = 2714225) B2714225
theorem B1809495 : Blo 1807605 1809495 := bstep (se 1 (by rfl) ⟨1357121, by rfl⟩ : syracuseStep 1809495 = 2714243) B2714243
theorem B5151833 : Blo 1807605 5151833 := bstep (se 2 (by rfl) ⟨1931937, by rfl⟩ : syracuseStep 5151833 = 3863875) B3863875
theorem B1809515 : Blo 1807605 1809515 := bstep (se 1 (by rfl) ⟨1357136, by rfl⟩ : syracuseStep 1809515 = 2714273) B2714273
theorem B1809527 : Blo 1807605 1809527 := bstep (se 1 (by rfl) ⟨1357145, by rfl⟩ : syracuseStep 1809527 = 2714291) B2714291
theorem B1809547 : Blo 1807605 1809547 := bstep (se 1 (by rfl) ⟨1357160, by rfl⟩ : syracuseStep 1809547 = 2714321) B2714321
theorem B3718295 : Blo 1807605 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B1809559 : Blo 1807605 1809559 := bstep (se 1 (by rfl) ⟨1357169, by rfl⟩ : syracuseStep 1809559 = 2714339) B2714339
theorem B1809579 : Blo 1807605 1809579 := bstep (se 1 (by rfl) ⟨1357184, by rfl⟩ : syracuseStep 1809579 = 2714369) B2714369
theorem B1809591 : Blo 1807605 1809591 := bstep (se 1 (by rfl) ⟨1357193, by rfl⟩ : syracuseStep 1809591 = 2714387) B2714387
theorem B3431639 : Blo 1807605 3431639 := bstep (se 1 (by rfl) ⟨2573729, by rfl⟩ : syracuseStep 3431639 = 5147459) B5147459
theorem B4070681 : Blo 1807605 4070681 := bstep (se 2 (by rfl) ⟨1526505, by rfl⟩ : syracuseStep 4070681 = 3053011) B3053011
theorem B6864173 : Blo 1807605 6864173 := bstep (se 3 (by rfl) ⟨1287032, by rfl⟩ : syracuseStep 6864173 = 2574065) B2574065
theorem B6102323 : Blo 1807605 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B6864203 : Blo 1807605 6864203 := bstep (se 1 (by rfl) ⟨5148152, by rfl⟩ : syracuseStep 6864203 = 10296305) B10296305
theorem B2202967 : Blo 1807605 2202967 := bstep (se 1 (by rfl) ⟨1652225, by rfl⟩ : syracuseStep 2202967 = 3304451) B3304451
theorem B4070771 : Blo 1807605 4070771 := bstep (se 1 (by rfl) ⟨3053078, by rfl⟩ : syracuseStep 4070771 = 6106157) B6106157
theorem B3259777 : Blo 1807605 3259777 := bstep (se 2 (by rfl) ⟨1222416, by rfl⟩ : syracuseStep 3259777 = 2444833) B2444833
theorem B4070807 : Blo 1807605 4070807 := bstep (se 1 (by rfl) ⟨3053105, by rfl⟩ : syracuseStep 4070807 = 6106211) B6106211
theorem B4578839 : Blo 1807605 4578839 := bstep (se 1 (by rfl) ⟨3434129, by rfl⟩ : syracuseStep 4578839 = 6868259) B6868259
theorem B6102593 : Blo 1807605 6102593 := bstep (se 2 (by rfl) ⟨2288472, by rfl⟩ : syracuseStep 6102593 = 4576945) B4576945
theorem B8691275 : Blo 1807605 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B4070987 : Blo 1807605 4070987 := bstep (se 1 (by rfl) ⟨3053240, by rfl⟩ : syracuseStep 4070987 = 6106481) B6106481
theorem B11296349 : Blo 1807605 11296349 := bstep (se 3 (by rfl) ⟨2118065, by rfl⟩ : syracuseStep 11296349 = 4236131) B4236131
theorem B4071041 : Blo 1807605 4071041 := bstep (se 2 (by rfl) ⟨1526640, by rfl⟩ : syracuseStep 4071041 = 3053281) B3053281
theorem B17612549 : Blo 1807605 17612549 := bstep (se 4 (by rfl) ⟨1651176, by rfl⟩ : syracuseStep 17612549 = 3302353) B3302353
theorem B8249177 : Blo 1807605 8249177 := bstep (se 2 (by rfl) ⟨3093441, by rfl⟩ : syracuseStep 8249177 = 6186883) B6186883
theorem B4071257 : Blo 1807605 4071257 := bstep (se 2 (by rfl) ⟨1526721, by rfl⟩ : syracuseStep 4071257 = 3053443) B3053443
theorem B3432307 : Blo 1807605 3432307 := bstep (se 1 (by rfl) ⟨2574230, by rfl⟩ : syracuseStep 3432307 = 5148461) B5148461
theorem B2711435 : Blo 1807605 2711435 := bstep (se 1 (by rfl) ⟨2033576, by rfl⟩ : syracuseStep 2711435 = 4067153) B4067153
theorem B2711447 : Blo 1807605 2711447 := bstep (se 1 (by rfl) ⟨2033585, by rfl⟩ : syracuseStep 2711447 = 4067171) B4067171
theorem B5152663 : Blo 1807605 5152663 := bstep (se 1 (by rfl) ⟨3864497, by rfl⟩ : syracuseStep 5152663 = 7728995) B7728995
theorem B3260339 : Blo 1807605 3260339 := bstep (se 1 (by rfl) ⟨2445254, by rfl⟩ : syracuseStep 3260339 = 4890509) B4890509
theorem B4071347 : Blo 1807605 4071347 := bstep (se 1 (by rfl) ⟨3053510, by rfl⟩ : syracuseStep 4071347 = 6107021) B6107021
theorem B15450061 : Blo 1807605 15450061 := bstep (se 3 (by rfl) ⟨2896886, by rfl⟩ : syracuseStep 15450061 = 5793773) B5793773
theorem B4071383 : Blo 1807605 4071383 := bstep (se 1 (by rfl) ⟨3053537, by rfl⟩ : syracuseStep 4071383 = 6107075) B6107075
theorem B2711513 : Blo 1807605 2711513 := bstep (se 2 (by rfl) ⟨1016817, by rfl⟩ : syracuseStep 2711513 = 2033635) B2033635
theorem B6864857 : Blo 1807605 6864857 := bstep (se 2 (by rfl) ⟨2574321, by rfl⟩ : syracuseStep 6864857 = 5148643) B5148643
theorem B2711567 : Blo 1807605 2711567 := bstep (se 1 (by rfl) ⟨2033675, by rfl⟩ : syracuseStep 2711567 = 4067351) B4067351
theorem B2711609 : Blo 1807605 2711609 := bstep (se 2 (by rfl) ⟨1016853, by rfl⟩ : syracuseStep 2711609 = 2033707) B2033707
theorem B20602997 : Blo 1807605 20602997 := bstep (se 5 (by rfl) ⟨965765, by rfl⟩ : syracuseStep 20602997 = 1931531) B1931531
theorem B2711687 : Blo 1807605 2711687 := bstep (se 1 (by rfl) ⟨2033765, by rfl⟩ : syracuseStep 2711687 = 4067531) B4067531
theorem B1958023 : Blo 1807605 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2711723 : Blo 1807605 2711723 := bstep (se 1 (by rfl) ⟨2033792, by rfl⟩ : syracuseStep 2711723 = 4067585) B4067585
theorem B2711753 : Blo 1807605 2711753 := bstep (se 2 (by rfl) ⟨1016907, by rfl⟩ : syracuseStep 2711753 = 2033815) B2033815
theorem B6103241 : Blo 1807605 6103241 := bstep (se 2 (by rfl) ⟨2288715, by rfl⟩ : syracuseStep 6103241 = 4577431) B4577431
theorem B10305737 : Blo 1807605 10305737 := bstep (se 2 (by rfl) ⟨3864651, by rfl⟩ : syracuseStep 10305737 = 7729303) B7729303
theorem B2711867 : Blo 1807605 2711867 := bstep (se 1 (by rfl) ⟨2033900, by rfl⟩ : syracuseStep 2711867 = 4067801) B4067801
theorem B4579699 : Blo 1807605 4579699 := bstep (se 1 (by rfl) ⟨3434774, by rfl⟩ : syracuseStep 4579699 = 6869549) B6869549
theorem B2711927 : Blo 1807605 2711927 := bstep (se 1 (by rfl) ⟨2033945, by rfl⟩ : syracuseStep 2711927 = 4067891) B4067891
theorem B2711951 : Blo 1807605 2711951 := bstep (se 1 (by rfl) ⟨2033963, by rfl⟩ : syracuseStep 2711951 = 4067927) B4067927
theorem B17375633 : Blo 1807605 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B66896273 : Blo 1807605 66896273 := bstep (se 2 (by rfl) ⟨25086102, by rfl⟩ : syracuseStep 66896273 = 50172205) B50172205
theorem B2711993 : Blo 1807605 2711993 := bstep (se 2 (by rfl) ⟨1016997, by rfl⟩ : syracuseStep 2711993 = 2033995) B2033995
theorem B3482041 : Blo 1807605 3482041 := bstep (se 2 (by rfl) ⟨1305765, by rfl⟩ : syracuseStep 3482041 = 2611531) B2611531
theorem B4579841 : Blo 1807605 4579841 := bstep (se 2 (by rfl) ⟨1717440, by rfl⟩ : syracuseStep 4579841 = 3434881) B3434881
theorem B2712071 : Blo 1807605 2712071 := bstep (se 1 (by rfl) ⟨2034053, by rfl⟩ : syracuseStep 2712071 = 4068107) B4068107
theorem B2712107 : Blo 1807605 2712107 := bstep (se 1 (by rfl) ⟨2034080, by rfl⟩ : syracuseStep 2712107 = 4068161) B4068161
theorem B2712137 : Blo 1807605 2712137 := bstep (se 2 (by rfl) ⟨1017051, by rfl⟩ : syracuseStep 2712137 = 2034103) B2034103
theorem B2712251 : Blo 1807605 2712251 := bstep (se 1 (by rfl) ⟨2034188, by rfl⟩ : syracuseStep 2712251 = 4068377) B4068377
theorem B2712311 : Blo 1807605 2712311 := bstep (se 1 (by rfl) ⟨2034233, by rfl⟩ : syracuseStep 2712311 = 4068467) B4068467
theorem B2712335 : Blo 1807605 2712335 := bstep (se 1 (by rfl) ⟨2034251, by rfl⟩ : syracuseStep 2712335 = 4068503) B4068503
theorem B2712377 : Blo 1807605 2712377 := bstep (se 2 (by rfl) ⟨1017141, by rfl⟩ : syracuseStep 2712377 = 2034283) B2034283
theorem B2712455 : Blo 1807605 2712455 := bstep (se 1 (by rfl) ⟨2034341, by rfl⟩ : syracuseStep 2712455 = 4068683) B4068683
theorem B6103943 : Blo 1807605 6103943 := bstep (se 1 (by rfl) ⟨4577957, by rfl⟩ : syracuseStep 6103943 = 9155915) B9155915
theorem B9151379 : Blo 1807605 9151379 := bstep (se 1 (by rfl) ⟨6863534, by rfl⟩ : syracuseStep 9151379 = 13727069) B13727069
theorem B2712491 : Blo 1807605 2712491 := bstep (se 1 (by rfl) ⟨2034368, by rfl⟩ : syracuseStep 2712491 = 4068737) B4068737
theorem B2712521 : Blo 1807605 2712521 := bstep (se 2 (by rfl) ⟨1017195, by rfl⟩ : syracuseStep 2712521 = 2034391) B2034391
theorem B17384395 : Blo 1807605 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B4580297 : Blo 1807605 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B2712635 : Blo 1807605 2712635 := bstep (se 1 (by rfl) ⟨2034476, by rfl⟩ : syracuseStep 2712635 = 4068953) B4068953
theorem B6521917 : Blo 1807605 6521917 := bstep (se 3 (by rfl) ⟨1222859, by rfl⟩ : syracuseStep 6521917 = 2445719) B2445719
theorem B8930371 : Blo 1807605 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B2712695 : Blo 1807605 2712695 := bstep (se 1 (by rfl) ⟨2034521, by rfl⟩ : syracuseStep 2712695 = 4069043) B4069043
theorem B2712719 : Blo 1807605 2712719 := bstep (se 1 (by rfl) ⟨2034539, by rfl⟩ : syracuseStep 2712719 = 4069079) B4069079
theorem B11592877 : Blo 1807605 11592877 := bstep (se 3 (by rfl) ⟨2173664, by rfl⟩ : syracuseStep 11592877 = 4347329) B4347329
theorem B2712761 : Blo 1807605 2712761 := bstep (se 2 (by rfl) ⟨1017285, by rfl⟩ : syracuseStep 2712761 = 2034571) B2034571
theorem B6104321 : Blo 1807605 6104321 := bstep (se 2 (by rfl) ⟨2289120, by rfl⟩ : syracuseStep 6104321 = 4578241) B4578241
theorem B2712839 : Blo 1807605 2712839 := bstep (se 1 (by rfl) ⟨2034629, by rfl⟩ : syracuseStep 2712839 = 4069259) B4069259
theorem B2712875 : Blo 1807605 2712875 := bstep (se 1 (by rfl) ⟨2034656, by rfl⟩ : syracuseStep 2712875 = 4069313) B4069313
theorem B5793083 : Blo 1807605 5793083 := bstep (se 1 (by rfl) ⟨4344812, by rfl⟩ : syracuseStep 5793083 = 8689625) B8689625
theorem B2712905 : Blo 1807605 2712905 := bstep (se 2 (by rfl) ⟨1017339, by rfl⟩ : syracuseStep 2712905 = 2034679) B2034679
theorem B6866329 : Blo 1807605 6866329 := bstep (se 2 (by rfl) ⟨2574873, by rfl⟩ : syracuseStep 6866329 = 5149747) B5149747
theorem B26437049 : Blo 1807605 26437049 := bstep (se 2 (by rfl) ⟨9913893, by rfl⟩ : syracuseStep 26437049 = 19827787) B19827787
theorem B2713019 : Blo 1807605 2713019 := bstep (se 1 (by rfl) ⟨2034764, by rfl⟩ : syracuseStep 2713019 = 4069529) B4069529
theorem B2713079 : Blo 1807605 2713079 := bstep (se 1 (by rfl) ⟨2034809, by rfl⟩ : syracuseStep 2713079 = 4069619) B4069619
theorem B7726603 : Blo 1807605 7726603 := bstep (se 1 (by rfl) ⟨5794952, by rfl⟩ : syracuseStep 7726603 = 11589905) B11589905
theorem B2713103 : Blo 1807605 2713103 := bstep (se 1 (by rfl) ⟨2034827, by rfl⟩ : syracuseStep 2713103 = 4069655) B4069655
theorem B7833131 : Blo 1807605 7833131 := bstep (se 1 (by rfl) ⟨5874848, by rfl⟩ : syracuseStep 7833131 = 11749697) B11749697
theorem B2713145 : Blo 1807605 2713145 := bstep (se 2 (by rfl) ⟨1017429, by rfl⟩ : syracuseStep 2713145 = 2034859) B2034859
theorem B6186557 : Blo 1807605 6186557 := bstep (se 3 (by rfl) ⟨1159979, by rfl⟩ : syracuseStep 6186557 = 2319959) B2319959
theorem B10298947 : Blo 1807605 10298947 := bstep (se 1 (by rfl) ⟨7724210, by rfl⟩ : syracuseStep 10298947 = 15448421) B15448421
theorem B8693315 : Blo 1807605 8693315 := bstep (se 1 (by rfl) ⟨6519986, by rfl⟩ : syracuseStep 8693315 = 13039973) B13039973
theorem B3917431 : Blo 1807605 3917431 := bstep (se 1 (by rfl) ⟨2938073, by rfl⟩ : syracuseStep 3917431 = 5876147) B5876147
theorem B2713223 : Blo 1807605 2713223 := bstep (se 1 (by rfl) ⟨2034917, by rfl⟩ : syracuseStep 2713223 = 4069835) B4069835
theorem B2713259 : Blo 1807605 2713259 := bstep (se 1 (by rfl) ⟨2034944, by rfl⟩ : syracuseStep 2713259 = 4069889) B4069889
theorem B6866633 : Blo 1807605 6866633 := bstep (se 2 (by rfl) ⟨2574987, by rfl⟩ : syracuseStep 6866633 = 5149975) B5149975
theorem B2713289 : Blo 1807605 2713289 := bstep (se 2 (by rfl) ⟨1017483, by rfl⟩ : syracuseStep 2713289 = 2034967) B2034967
theorem B47605477 : Blo 1807605 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B5793569 : Blo 1807605 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B11749157 : Blo 1807605 11749157 := bstep (se 4 (by rfl) ⟨1101483, by rfl⟩ : syracuseStep 11749157 = 2202967) B2202967
theorem B2713403 : Blo 1807605 2713403 := bstep (se 1 (by rfl) ⟨2035052, by rfl⟩ : syracuseStep 2713403 = 4070105) B4070105
theorem B2713463 : Blo 1807605 2713463 := bstep (se 1 (by rfl) ⟨2035097, by rfl⟩ : syracuseStep 2713463 = 4070195) B4070195
theorem B2713487 : Blo 1807605 2713487 := bstep (se 1 (by rfl) ⟨2035115, by rfl⟩ : syracuseStep 2713487 = 4070231) B4070231
theorem B2713529 : Blo 1807605 2713529 := bstep (se 2 (by rfl) ⟨1017573, by rfl⟩ : syracuseStep 2713529 = 2035147) B2035147
theorem B2033671 : Blo 1807605 2033671 := bstep (se 1 (by rfl) ⟨1525253, by rfl⟩ : syracuseStep 2033671 = 3050507) B3050507
theorem B2713607 : Blo 1807605 2713607 := bstep (se 1 (by rfl) ⟨2035205, by rfl⟩ : syracuseStep 2713607 = 4070411) B4070411
theorem B6105131 : Blo 1807605 6105131 := bstep (se 1 (by rfl) ⟨4578848, by rfl⟩ : syracuseStep 6105131 = 9157697) B9157697
theorem B2713643 : Blo 1807605 2713643 := bstep (se 1 (by rfl) ⟨2035232, by rfl⟩ : syracuseStep 2713643 = 4070465) B4070465
theorem B3434555 : Blo 1807605 3434555 := bstep (se 1 (by rfl) ⟨2575916, by rfl⟩ : syracuseStep 3434555 = 5151833) B5151833
theorem B2713673 : Blo 1807605 2713673 := bstep (se 2 (by rfl) ⟨1017627, by rfl⟩ : syracuseStep 2713673 = 2035255) B2035255
theorem B8357975 : Blo 1807605 8357975 := bstep (se 1 (by rfl) ⟨6268481, by rfl⟩ : syracuseStep 8357975 = 12536963) B12536963
theorem B35719261 : Blo 1807605 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B2287759 : Blo 1807605 2287759 := bstep (se 1 (by rfl) ⟨1715819, by rfl⟩ : syracuseStep 2287759 = 3431639) B3431639
theorem B2033851 : Blo 1807605 2033851 := bstep (se 1 (by rfl) ⟨1525388, by rfl⟩ : syracuseStep 2033851 = 3050777) B3050777
theorem B2713787 : Blo 1807605 2713787 := bstep (se 1 (by rfl) ⟨2035340, by rfl⟩ : syracuseStep 2713787 = 4070681) B4070681
theorem B2713847 : Blo 1807605 2713847 := bstep (se 1 (by rfl) ⟨2035385, by rfl⟩ : syracuseStep 2713847 = 4070771) B4070771
theorem B2713871 : Blo 1807605 2713871 := bstep (se 1 (by rfl) ⟨2035403, by rfl⟩ : syracuseStep 2713871 = 4070807) B4070807
theorem B19548449 : Blo 1807605 19548449 := bstep (se 2 (by rfl) ⟨7330668, by rfl⟩ : syracuseStep 19548449 = 14661337) B14661337
theorem B2713913 : Blo 1807605 2713913 := bstep (se 2 (by rfl) ⟨1017717, by rfl⟩ : syracuseStep 2713913 = 2035435) B2035435
theorem B5794183 : Blo 1807605 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B2713991 : Blo 1807605 2713991 := bstep (se 1 (by rfl) ⟨2035493, by rfl⟩ : syracuseStep 2713991 = 4070987) B4070987
theorem B7530899 : Blo 1807605 7530899 := bstep (se 1 (by rfl) ⟨5648174, by rfl⟩ : syracuseStep 7530899 = 11296349) B11296349
theorem B2714027 : Blo 1807605 2714027 := bstep (se 1 (by rfl) ⟨2035520, by rfl⟩ : syracuseStep 2714027 = 4071041) B4071041
theorem B2714057 : Blo 1807605 2714057 := bstep (se 2 (by rfl) ⟨1017771, by rfl⟩ : syracuseStep 2714057 = 2035543) B2035543
theorem B11741699 : Blo 1807605 11741699 := bstep (se 1 (by rfl) ⟨8806274, by rfl⟩ : syracuseStep 11741699 = 17612549) B17612549
theorem B3435041 : Blo 1807605 3435041 := bstep (se 2 (by rfl) ⟨1288140, by rfl⟩ : syracuseStep 3435041 = 2576281) B2576281
theorem B5499451 : Blo 1807605 5499451 := bstep (se 1 (by rfl) ⟨4124588, by rfl⟩ : syracuseStep 5499451 = 8249177) B8249177
theorem B2714171 : Blo 1807605 2714171 := bstep (se 1 (by rfl) ⟨2035628, by rfl⟩ : syracuseStep 2714171 = 4071257) B4071257
theorem B6867575 : Blo 1807605 6867575 := bstep (se 1 (by rfl) ⟨5150681, by rfl⟩ : syracuseStep 6867575 = 10301363) B10301363
theorem B2173559 : Blo 1807605 2173559 := bstep (se 1 (by rfl) ⟨1630169, by rfl⟩ : syracuseStep 2173559 = 3260339) B3260339
theorem B2714231 : Blo 1807605 2714231 := bstep (se 1 (by rfl) ⟨2035673, by rfl⟩ : syracuseStep 2714231 = 4071347) B4071347
theorem B2034319 : Blo 1807605 2034319 := bstep (se 1 (by rfl) ⟨1525739, by rfl⟩ : syracuseStep 2034319 = 3051479) B3051479
theorem B2714255 : Blo 1807605 2714255 := bstep (se 1 (by rfl) ⟨2035691, by rfl⟩ : syracuseStep 2714255 = 4071383) B4071383
theorem B10996397 : Blo 1807605 10996397 := bstep (se 3 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 10996397 = 4123649) B4123649
theorem B2714297 : Blo 1807605 2714297 := bstep (se 2 (by rfl) ⟨1017861, by rfl⟩ : syracuseStep 2714297 = 2035723) B2035723
theorem B2711543 : Blo 1807605 2711543 := bstep (se 1 (by rfl) ⟨2033657, by rfl⟩ : syracuseStep 2711543 = 4067315) B4067315
theorem B2714375 : Blo 1807605 2714375 := bstep (se 1 (by rfl) ⟨2035781, by rfl⟩ : syracuseStep 2714375 = 4071563) B4071563
theorem B2444075 : Blo 1807605 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B2575147 : Blo 1807605 2575147 := bstep (se 1 (by rfl) ⟨1931360, by rfl⟩ : syracuseStep 2575147 = 3862721) B3862721
theorem B2288503 : Blo 1807605 2288503 := bstep (se 1 (by rfl) ⟨1716377, by rfl⟩ : syracuseStep 2288503 = 3432755) B3432755
theorem B2444303 : Blo 1807605 2444303 := bstep (se 1 (by rfl) ⟨1833227, by rfl⟩ : syracuseStep 2444303 = 3666455) B3666455
theorem B4344947 : Blo 1807605 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B3050615 : Blo 1807605 3050615 := bstep (se 1 (by rfl) ⟨2287961, by rfl⟩ : syracuseStep 3050615 = 4575923) B4575923
theorem B2034823 : Blo 1807605 2034823 := bstep (se 1 (by rfl) ⟨1526117, by rfl⟩ : syracuseStep 2034823 = 3052235) B3052235
theorem B2288827 : Blo 1807605 2288827 := bstep (se 1 (by rfl) ⟨1716620, by rfl⟩ : syracuseStep 2288827 = 3433241) B3433241
theorem B2035003 : Blo 1807605 2035003 := bstep (se 1 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 2035003 = 3052505) B3052505
theorem B6106427 : Blo 1807605 6106427 := bstep (se 1 (by rfl) ⟨4579820, by rfl⟩ : syracuseStep 6106427 = 9159641) B9159641
theorem B3665287 : Blo 1807605 3665287 := bstep (se 1 (by rfl) ⟨2748965, by rfl⟩ : syracuseStep 3665287 = 5497931) B5497931
theorem B4124051 : Blo 1807605 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B4345273 : Blo 1807605 4345273 := bstep (se 2 (by rfl) ⟨1629477, by rfl⟩ : syracuseStep 4345273 = 3258955) B3258955
theorem B10300931 : Blo 1807605 10300931 := bstep (se 1 (by rfl) ⟨7725698, by rfl⟩ : syracuseStep 10300931 = 15451397) B15451397
theorem B2788921 : Blo 1807605 2788921 := bstep (se 2 (by rfl) ⟨1045845, by rfl⟩ : syracuseStep 2788921 = 2091691) B2091691
theorem B4886075 : Blo 1807605 4886075 := bstep (se 1 (by rfl) ⟨3664556, by rfl⟩ : syracuseStep 4886075 = 7329113) B7329113
theorem B3051067 : Blo 1807605 3051067 := bstep (se 1 (by rfl) ⟨2288300, by rfl⟩ : syracuseStep 3051067 = 4576601) B4576601
theorem B6868547 : Blo 1807605 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B2289323 : Blo 1807605 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B3051209 : Blo 1807605 3051209 := bstep (se 2 (by rfl) ⟨1144203, by rfl⟩ : syracuseStep 3051209 = 2288407) B2288407
theorem B2035471 : Blo 1807605 2035471 := bstep (se 1 (by rfl) ⟨1526603, by rfl⟩ : syracuseStep 2035471 = 3053207) B3053207
theorem B6106913 : Blo 1807605 6106913 := bstep (se 2 (by rfl) ⟨2290092, by rfl⟩ : syracuseStep 6106913 = 4580185) B4580185
theorem B58650419 : Blo 1807605 58650419 := bstep (se 1 (by rfl) ⟨43987814, by rfl⟩ : syracuseStep 58650419 = 87975629) B87975629
theorem B43978565 : Blo 1807605 43978565 := bstep (se 4 (by rfl) ⟨4122990, by rfl⟩ : syracuseStep 43978565 = 8245981) B8245981
theorem B4067207 : Blo 1807605 4067207 := bstep (se 1 (by rfl) ⟨3050405, by rfl⟩ : syracuseStep 4067207 = 6100811) B6100811
theorem B9154457 : Blo 1807605 9154457 := bstep (se 2 (by rfl) ⟨3432921, by rfl⟩ : syracuseStep 9154457 = 6865843) B6865843
theorem B4067387 : Blo 1807605 4067387 := bstep (se 1 (by rfl) ⟨3050540, by rfl⟩ : syracuseStep 4067387 = 6101081) B6101081
theorem B5795927 : Blo 1807605 5795927 := bstep (se 1 (by rfl) ⟨4346945, by rfl⟩ : syracuseStep 5795927 = 8693891) B8693891
theorem B5148791 : Blo 1807605 5148791 := bstep (se 1 (by rfl) ⟨3861593, by rfl⟩ : syracuseStep 5148791 = 7723187) B7723187
theorem B2289799 : Blo 1807605 2289799 := bstep (se 1 (by rfl) ⟨1717349, by rfl⟩ : syracuseStep 2289799 = 3434699) B3434699
theorem B4067513 : Blo 1807605 4067513 := bstep (se 2 (by rfl) ⟨1525317, by rfl⟩ : syracuseStep 4067513 = 3050635) B3050635
theorem B2445611 : Blo 1807605 2445611 := bstep (se 1 (by rfl) ⟨1834208, by rfl⟩ : syracuseStep 2445611 = 3668417) B3668417
theorem B3051911 : Blo 1807605 3051911 := bstep (se 1 (by rfl) ⟨2288933, by rfl⟩ : syracuseStep 3051911 = 4577867) B4577867
theorem B29348243 : Blo 1807605 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B4346369 : Blo 1807605 4346369 := bstep (se 2 (by rfl) ⟨1629888, by rfl⟩ : syracuseStep 4346369 = 3259777) B3259777
theorem B9777667 : Blo 1807605 9777667 := bstep (se 1 (by rfl) ⟨7333250, by rfl⟩ : syracuseStep 9777667 = 14666501) B14666501
theorem B4067855 : Blo 1807605 4067855 := bstep (se 1 (by rfl) ⟨3050891, by rfl⟩ : syracuseStep 4067855 = 6101783) B6101783
theorem B4067873 : Blo 1807605 4067873 := bstep (se 2 (by rfl) ⟨1525452, by rfl⟩ : syracuseStep 4067873 = 3050905) B3050905
theorem B26415659 : Blo 1807605 26415659 := bstep (se 1 (by rfl) ⟨19811744, by rfl⟩ : syracuseStep 26415659 = 39623489) B39623489
theorem B20591333 : Blo 1807605 20591333 := bstep (se 4 (by rfl) ⟨1930437, by rfl⟩ : syracuseStep 20591333 = 3860875) B3860875
theorem B2478863 : Blo 1807605 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B4125473 : Blo 1807605 4125473 := bstep (se 2 (by rfl) ⟨1547052, by rfl⟩ : syracuseStep 4125473 = 3094105) B3094105
theorem B4576115 : Blo 1807605 4576115 := bstep (se 1 (by rfl) ⟨3432086, by rfl⟩ : syracuseStep 4576115 = 6864173) B6864173
theorem B4068215 : Blo 1807605 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B2896759 : Blo 1807605 2896759 := bstep (se 1 (by rfl) ⟨2172569, by rfl⟩ : syracuseStep 2896759 = 4345139) B4345139
theorem B4576135 : Blo 1807605 4576135 := bstep (se 1 (by rfl) ⟨3432101, by rfl⟩ : syracuseStep 4576135 = 6864203) B6864203
theorem B3052559 : Blo 1807605 3052559 := bstep (se 1 (by rfl) ⟨2289419, by rfl⟩ : syracuseStep 3052559 = 4578839) B4578839
theorem B4068395 : Blo 1807605 4068395 := bstep (se 1 (by rfl) ⟨3051296, by rfl⟩ : syracuseStep 4068395 = 6102593) B6102593
theorem B8688701 : Blo 1807605 8688701 := bstep (se 3 (by rfl) ⟨1629131, by rfl⟩ : syracuseStep 8688701 = 3258263) B3258263
theorem B7337027 : Blo 1807605 7337027 := bstep (se 1 (by rfl) ⟨5502770, by rfl⟩ : syracuseStep 7337027 = 11005541) B11005541
theorem B4576409 : Blo 1807605 4576409 := bstep (se 2 (by rfl) ⟨1716153, by rfl⟩ : syracuseStep 4576409 = 3432307) B3432307
theorem B6870217 : Blo 1807605 6870217 := bstep (se 2 (by rfl) ⟨2576331, by rfl⟩ : syracuseStep 6870217 = 5152663) B5152663
theorem B1807623 : Blo 1807605 1807623 := bstep (se 1 (by rfl) ⟨1355717, by rfl⟩ : syracuseStep 1807623 = 2711435) B2711435
theorem B1807631 : Blo 1807605 1807631 := bstep (se 1 (by rfl) ⟨1355723, by rfl⟩ : syracuseStep 1807631 = 2711447) B2711447
theorem B20600081 : Blo 1807605 20600081 := bstep (se 2 (by rfl) ⟨7725030, by rfl⟩ : syracuseStep 20600081 = 15450061) B15450061
theorem B1807675 : Blo 1807605 1807675 := bstep (se 1 (by rfl) ⟨1355756, by rfl⟩ : syracuseStep 1807675 = 2711513) B2711513
theorem B4576571 : Blo 1807605 4576571 := bstep (se 1 (by rfl) ⟨3432428, by rfl⟩ : syracuseStep 4576571 = 6864857) B6864857
theorem B1807751 : Blo 1807605 1807751 := bstep (se 1 (by rfl) ⟨1355813, by rfl⟩ : syracuseStep 1807751 = 2711627) B2711627
theorem B1807759 : Blo 1807605 1807759 := bstep (se 1 (by rfl) ⟨1355819, by rfl⟩ : syracuseStep 1807759 = 2711639) B2711639
theorem B4068755 : Blo 1807605 4068755 := bstep (se 1 (by rfl) ⟨3051566, by rfl⟩ : syracuseStep 4068755 = 6103133) B6103133
theorem B1807803 : Blo 1807605 1807803 := bstep (se 1 (by rfl) ⟨1355852, by rfl⟩ : syracuseStep 1807803 = 2711705) B2711705
theorem B4068809 : Blo 1807605 4068809 := bstep (se 2 (by rfl) ⟨1525803, by rfl⟩ : syracuseStep 4068809 = 3051607) B3051607
theorem B29324749 : Blo 1807605 29324749 := bstep (se 3 (by rfl) ⟨5498390, by rfl⟩ : syracuseStep 29324749 = 10996781) B10996781
theorem B1807879 : Blo 1807605 1807879 := bstep (se 1 (by rfl) ⟨1355909, by rfl⟩ : syracuseStep 1807879 = 2711819) B2711819
theorem B1807887 : Blo 1807605 1807887 := bstep (se 1 (by rfl) ⟨1355915, by rfl⟩ : syracuseStep 1807887 = 2711831) B2711831
theorem B4576783 : Blo 1807605 4576783 := bstep (se 1 (by rfl) ⟨3432587, by rfl⟩ : syracuseStep 4576783 = 6865175) B6865175
theorem B4347407 : Blo 1807605 4347407 := bstep (se 1 (by rfl) ⟨3260555, by rfl⟩ : syracuseStep 4347407 = 6521111) B6521111
theorem B3053099 : Blo 1807605 3053099 := bstep (se 1 (by rfl) ⟨2289824, by rfl⟩ : syracuseStep 3053099 = 4579649) B4579649
theorem B1807931 : Blo 1807605 1807931 := bstep (se 1 (by rfl) ⟨1355948, by rfl⟩ : syracuseStep 1807931 = 2711897) B2711897
theorem B15447671 : Blo 1807605 15447671 := bstep (se 1 (by rfl) ⟨11585753, by rfl⟩ : syracuseStep 15447671 = 23171507) B23171507
theorem B1808007 : Blo 1807605 1808007 := bstep (se 1 (by rfl) ⟨1356005, by rfl⟩ : syracuseStep 1808007 = 2712011) B2712011
theorem B1808015 : Blo 1807605 1808015 := bstep (se 1 (by rfl) ⟨1356011, by rfl⟩ : syracuseStep 1808015 = 2712023) B2712023
theorem B1808059 : Blo 1807605 1808059 := bstep (se 1 (by rfl) ⟨1356044, by rfl⟩ : syracuseStep 1808059 = 2712089) B2712089
theorem B1808135 : Blo 1807605 1808135 := bstep (se 1 (by rfl) ⟨1356101, by rfl⟩ : syracuseStep 1808135 = 2712203) B2712203
theorem B1808143 : Blo 1807605 1808143 := bstep (se 1 (by rfl) ⟨1356107, by rfl⟩ : syracuseStep 1808143 = 2712215) B2712215
theorem B4577057 : Blo 1807605 4577057 := bstep (se 2 (by rfl) ⟨1716396, by rfl⟩ : syracuseStep 4577057 = 3432793) B3432793
theorem B10295099 : Blo 1807605 10295099 := bstep (se 1 (by rfl) ⟨7721324, by rfl⟩ : syracuseStep 10295099 = 15442649) B15442649
theorem B1808187 : Blo 1807605 1808187 := bstep (se 1 (by rfl) ⟨1356140, by rfl⟩ : syracuseStep 1808187 = 2712281) B2712281
theorem B10303321 : Blo 1807605 10303321 := bstep (se 2 (by rfl) ⟨3863745, by rfl⟩ : syracuseStep 10303321 = 7727491) B7727491
theorem B1808263 : Blo 1807605 1808263 := bstep (se 1 (by rfl) ⟨1356197, by rfl⟩ : syracuseStep 1808263 = 2712395) B2712395
theorem B1808271 : Blo 1807605 1808271 := bstep (se 1 (by rfl) ⟨1356203, by rfl⟩ : syracuseStep 1808271 = 2712407) B2712407
theorem B3053497 : Blo 1807605 3053497 := bstep (se 2 (by rfl) ⟨1145061, by rfl⟩ : syracuseStep 3053497 = 2290123) B2290123
theorem B1808315 : Blo 1807605 1808315 := bstep (se 1 (by rfl) ⟨1356236, by rfl⟩ : syracuseStep 1808315 = 2712473) B2712473
theorem B1808391 : Blo 1807605 1808391 := bstep (se 1 (by rfl) ⟨1356293, by rfl⟩ : syracuseStep 1808391 = 2712587) B2712587
theorem B52123661 : Blo 1807605 52123661 := bstep (se 3 (by rfl) ⟨9773186, by rfl⟩ : syracuseStep 52123661 = 19546373) B19546373
theorem B1808399 : Blo 1807605 1808399 := bstep (se 1 (by rfl) ⟨1356299, by rfl⟩ : syracuseStep 1808399 = 2712599) B2712599
theorem B1808443 : Blo 1807605 1808443 := bstep (se 1 (by rfl) ⟨1356332, by rfl⟩ : syracuseStep 1808443 = 2712665) B2712665
theorem B6789187 : Blo 1807605 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B1808519 : Blo 1807605 1808519 := bstep (se 1 (by rfl) ⟨1356389, by rfl⟩ : syracuseStep 1808519 = 2712779) B2712779
theorem B4069511 : Blo 1807605 4069511 := bstep (se 1 (by rfl) ⟨3052133, by rfl⟩ : syracuseStep 4069511 = 6104267) B6104267
theorem B1808527 : Blo 1807605 1808527 := bstep (se 1 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 1808527 = 2712791) B2712791
theorem B3479699 : Blo 1807605 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B1808571 : Blo 1807605 1808571 := bstep (se 1 (by rfl) ⟨1356428, by rfl⟩ : syracuseStep 1808571 = 2712857) B2712857
theorem B19560649 : Blo 1807605 19560649 := bstep (se 2 (by rfl) ⟨7335243, by rfl⟩ : syracuseStep 19560649 = 14670487) B14670487
theorem B1808647 : Blo 1807605 1808647 := bstep (se 1 (by rfl) ⟨1356485, by rfl⟩ : syracuseStep 1808647 = 2712971) B2712971
theorem B1808655 : Blo 1807605 1808655 := bstep (se 1 (by rfl) ⟨1356491, by rfl⟩ : syracuseStep 1808655 = 2712983) B2712983
theorem B1808699 : Blo 1807605 1808699 := bstep (se 1 (by rfl) ⟨1356524, by rfl⟩ : syracuseStep 1808699 = 2713049) B2713049
theorem B4069691 : Blo 1807605 4069691 := bstep (se 1 (by rfl) ⟨3052268, by rfl⟩ : syracuseStep 4069691 = 6104537) B6104537
theorem B1808775 : Blo 1807605 1808775 := bstep (se 1 (by rfl) ⟨1356581, by rfl⟩ : syracuseStep 1808775 = 2713163) B2713163
theorem B1808783 : Blo 1807605 1808783 := bstep (se 1 (by rfl) ⟨1356587, by rfl⟩ : syracuseStep 1808783 = 2713175) B2713175
theorem B9157049 : Blo 1807605 9157049 := bstep (se 2 (by rfl) ⟨3433893, by rfl⟩ : syracuseStep 9157049 = 6867787) B6867787
theorem B4069817 : Blo 1807605 4069817 := bstep (se 2 (by rfl) ⟨1526181, by rfl⟩ : syracuseStep 4069817 = 3052363) B3052363
theorem B1808827 : Blo 1807605 1808827 := bstep (se 1 (by rfl) ⟨1356620, by rfl⟩ : syracuseStep 1808827 = 2713241) B2713241
theorem B1808903 : Blo 1807605 1808903 := bstep (se 1 (by rfl) ⟨1356677, by rfl⟩ : syracuseStep 1808903 = 2713355) B2713355
theorem B1808911 : Blo 1807605 1808911 := bstep (se 1 (by rfl) ⟨1356683, by rfl⟩ : syracuseStep 1808911 = 2713367) B2713367
theorem B41777707 : Blo 1807605 41777707 := bstep (se 1 (by rfl) ⟨31333280, by rfl⟩ : syracuseStep 41777707 = 62666561) B62666561
theorem B1808955 : Blo 1807605 1808955 := bstep (se 1 (by rfl) ⟨1356716, by rfl⟩ : syracuseStep 1808955 = 2713433) B2713433
theorem B1809031 : Blo 1807605 1809031 := bstep (se 1 (by rfl) ⟨1356773, by rfl⟩ : syracuseStep 1809031 = 2713547) B2713547
theorem B1809039 : Blo 1807605 1809039 := bstep (se 1 (by rfl) ⟨1356779, by rfl⟩ : syracuseStep 1809039 = 2713559) B2713559
theorem B1809083 : Blo 1807605 1809083 := bstep (se 1 (by rfl) ⟨1356812, by rfl⟩ : syracuseStep 1809083 = 2713625) B2713625
theorem B5151433 : Blo 1807605 5151433 := bstep (se 2 (by rfl) ⟨1931787, by rfl⟩ : syracuseStep 5151433 = 3863575) B3863575
theorem B1809159 : Blo 1807605 1809159 := bstep (se 1 (by rfl) ⟨1356869, by rfl⟩ : syracuseStep 1809159 = 2713739) B2713739
theorem B4578059 : Blo 1807605 4578059 := bstep (se 1 (by rfl) ⟨3433544, by rfl⟩ : syracuseStep 4578059 = 6867089) B6867089
theorem B13728527 : Blo 1807605 13728527 := bstep (se 1 (by rfl) ⟨10296395, by rfl⟩ : syracuseStep 13728527 = 20592791) B20592791
theorem B4070159 : Blo 1807605 4070159 := bstep (se 1 (by rfl) ⟨3052619, by rfl⟩ : syracuseStep 4070159 = 6105239) B6105239
theorem B1809167 : Blo 1807605 1809167 := bstep (se 1 (by rfl) ⟨1356875, by rfl⟩ : syracuseStep 1809167 = 2713751) B2713751
theorem B4070177 : Blo 1807605 4070177 := bstep (se 2 (by rfl) ⟨1526316, by rfl⟩ : syracuseStep 4070177 = 3052633) B3052633
theorem B1833787 : Blo 1807605 1833787 := bstep (se 1 (by rfl) ⟨1375340, by rfl⟩ : syracuseStep 1833787 = 2750681) B2750681
theorem B1809211 : Blo 1807605 1809211 := bstep (se 1 (by rfl) ⟨1356908, by rfl⟩ : syracuseStep 1809211 = 2713817) B2713817
theorem B1809287 : Blo 1807605 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B1809295 : Blo 1807605 1809295 := bstep (se 1 (by rfl) ⟨1356971, by rfl⟩ : syracuseStep 1809295 = 2713943) B2713943
theorem B6101945 : Blo 1807605 6101945 := bstep (se 2 (by rfl) ⟨2288229, by rfl⟩ : syracuseStep 6101945 = 4576459) B4576459
theorem B1809339 : Blo 1807605 1809339 := bstep (se 1 (by rfl) ⟨1357004, by rfl⟩ : syracuseStep 1809339 = 2714009) B2714009
theorem B1809415 : Blo 1807605 1809415 := bstep (se 1 (by rfl) ⟨1357061, by rfl⟩ : syracuseStep 1809415 = 2714123) B2714123
theorem B1809423 : Blo 1807605 1809423 := bstep (se 1 (by rfl) ⟨1357067, by rfl⟩ : syracuseStep 1809423 = 2714135) B2714135
theorem B1809467 : Blo 1807605 1809467 := bstep (se 1 (by rfl) ⟨1357100, by rfl⟩ : syracuseStep 1809467 = 2714201) B2714201
theorem B19815511 : Blo 1807605 19815511 := bstep (se 1 (by rfl) ⟨14861633, by rfl⟩ : syracuseStep 19815511 = 29723267) B29723267
theorem B3259511 : Blo 1807605 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B4070519 : Blo 1807605 4070519 := bstep (se 1 (by rfl) ⟨3052889, by rfl⟩ : syracuseStep 4070519 = 6105779) B6105779
theorem B1809543 : Blo 1807605 1809543 := bstep (se 1 (by rfl) ⟨1357157, by rfl⟩ : syracuseStep 1809543 = 2714315) B2714315
theorem B1809551 : Blo 1807605 1809551 := bstep (se 1 (by rfl) ⟨1357163, by rfl⟩ : syracuseStep 1809551 = 2714327) B2714327
theorem B1809595 : Blo 1807605 1809595 := bstep (se 1 (by rfl) ⟨1357196, by rfl⟩ : syracuseStep 1809595 = 2714393) B2714393
theorem B10296557 : Blo 1807605 10296557 := bstep (se 3 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 10296557 = 3861209) B3861209
theorem B4070699 : Blo 1807605 4070699 := bstep (se 1 (by rfl) ⟨3053024, by rfl⟩ : syracuseStep 4070699 = 6106049) B6106049
theorem B13737275 : Blo 1807605 13737275 := bstep (se 1 (by rfl) ⟨10302956, by rfl⟩ : syracuseStep 13737275 = 20605913) B20605913
theorem B4578707 : Blo 1807605 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B6102539 : Blo 1807605 6102539 := bstep (se 1 (by rfl) ⟨4576904, by rfl⟩ : syracuseStep 6102539 = 9153809) B9153809
theorem B10305053 : Blo 1807605 10305053 := bstep (se 3 (by rfl) ⟨1932197, by rfl⟩ : syracuseStep 10305053 = 3864395) B3864395
theorem B7724605 : Blo 1807605 7724605 := bstep (se 3 (by rfl) ⟨1448363, by rfl⟩ : syracuseStep 7724605 = 2896727) B2896727
theorem B6102647 : Blo 1807605 6102647 := bstep (se 1 (by rfl) ⟨4576985, by rfl⟩ : syracuseStep 6102647 = 9153971) B9153971
theorem B3432071 : Blo 1807605 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B4071059 : Blo 1807605 4071059 := bstep (se 1 (by rfl) ⟨3053294, by rfl⟩ : syracuseStep 4071059 = 6106589) B6106589
theorem B4579001 : Blo 1807605 4579001 := bstep (se 2 (by rfl) ⟨1717125, by rfl⟩ : syracuseStep 4579001 = 3434251) B3434251
theorem B9158345 : Blo 1807605 9158345 := bstep (se 2 (by rfl) ⟨3434379, by rfl⟩ : syracuseStep 9158345 = 6868759) B6868759
theorem B4071113 : Blo 1807605 4071113 := bstep (se 2 (by rfl) ⟨1526667, by rfl⟩ : syracuseStep 4071113 = 3053335) B3053335
theorem B2203399 : Blo 1807605 2203399 := bstep (se 1 (by rfl) ⟨1652549, by rfl⟩ : syracuseStep 2203399 = 3305099) B3305099
theorem B4890401 : Blo 1807605 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B5291837 : Blo 1807605 5291837 := bstep (se 3 (by rfl) ⟨992219, by rfl⟩ : syracuseStep 5291837 = 1984439) B1984439
theorem B9781145 : Blo 1807605 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B2711483 : Blo 1807605 2711483 := bstep (se 1 (by rfl) ⟨2033612, by rfl⟩ : syracuseStep 2711483 = 4067225) B4067225
theorem B2711561 : Blo 1807605 2711561 := bstep (se 2 (by rfl) ⟨1016835, by rfl⟩ : syracuseStep 2711561 = 2033671) B2033671
theorem B2711591 : Blo 1807605 2711591 := bstep (se 1 (by rfl) ⟨2033693, by rfl⟩ : syracuseStep 2711591 = 4067387) B4067387
theorem B3432527 : Blo 1807605 3432527 := bstep (se 1 (by rfl) ⟨2574395, by rfl⟩ : syracuseStep 3432527 = 5148791) B5148791
theorem B9052249 : Blo 1807605 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B2711675 : Blo 1807605 2711675 := bstep (se 1 (by rfl) ⟨2033756, by rfl⟩ : syracuseStep 2711675 = 4067513) B4067513
theorem B2711801 : Blo 1807605 2711801 := bstep (se 2 (by rfl) ⟨1016925, by rfl⟩ : syracuseStep 2711801 = 2033851) B2033851
theorem B11583755 : Blo 1807605 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B44597515 : Blo 1807605 44597515 := bstep (se 1 (by rfl) ⟨33448136, by rfl⟩ : syracuseStep 44597515 = 66896273) B66896273
theorem B2711903 : Blo 1807605 2711903 := bstep (se 1 (by rfl) ⟨2033927, by rfl⟩ : syracuseStep 2711903 = 4067855) B4067855
theorem B2711915 : Blo 1807605 2711915 := bstep (se 1 (by rfl) ⟨2033936, by rfl⟩ : syracuseStep 2711915 = 4067873) B4067873
theorem B2712143 : Blo 1807605 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B2712263 : Blo 1807605 2712263 := bstep (se 1 (by rfl) ⟨2034197, by rfl⟩ : syracuseStep 2712263 = 4068395) B4068395
theorem B5792467 : Blo 1807605 5792467 := bstep (se 1 (by rfl) ⟨4344350, by rfl⟩ : syracuseStep 5792467 = 8688701) B8688701
theorem B4891351 : Blo 1807605 4891351 := bstep (se 1 (by rfl) ⟨3668513, by rfl⟩ : syracuseStep 4891351 = 7337027) B7337027
theorem B7332601 : Blo 1807605 7332601 := bstep (se 2 (by rfl) ⟨2749725, by rfl⟩ : syracuseStep 7332601 = 5499451) B5499451
theorem B6521629 : Blo 1807605 6521629 := bstep (se 3 (by rfl) ⟨1222805, by rfl⟩ : syracuseStep 6521629 = 2445611) B2445611
theorem B2712425 : Blo 1807605 2712425 := bstep (se 2 (by rfl) ⟨1017159, by rfl⟩ : syracuseStep 2712425 = 2034319) B2034319
theorem B2712503 : Blo 1807605 2712503 := bstep (se 1 (by rfl) ⟨2034377, by rfl⟩ : syracuseStep 2712503 = 4068755) B4068755
theorem B2712539 : Blo 1807605 2712539 := bstep (se 1 (by rfl) ⟨2034404, by rfl⟩ : syracuseStep 2712539 = 4068809) B4068809
theorem B3433529 : Blo 1807605 3433529 := bstep (se 2 (by rfl) ⟨1287573, by rfl⟩ : syracuseStep 3433529 = 2575147) B2575147
theorem B10298447 : Blo 1807605 10298447 := bstep (se 1 (by rfl) ⟨7723835, by rfl⟩ : syracuseStep 10298447 = 15447671) B15447671
theorem B7832771 : Blo 1807605 7832771 := bstep (se 1 (by rfl) ⟨5874578, by rfl⟩ : syracuseStep 7832771 = 11749157) B11749157
theorem B23184629 : Blo 1807605 23184629 := bstep (se 5 (by rfl) ⟨1086779, by rfl⟩ : syracuseStep 23184629 = 2173559) B2173559
theorem B31311197 : Blo 1807605 31311197 := bstep (se 3 (by rfl) ⟨5870849, by rfl⟩ : syracuseStep 31311197 = 11741699) B11741699
theorem B5571983 : Blo 1807605 5571983 := bstep (se 1 (by rfl) ⟨4178987, by rfl⟩ : syracuseStep 5571983 = 8357975) B8357975
theorem B2713007 : Blo 1807605 2713007 := bstep (se 1 (by rfl) ⟨2034755, by rfl⟩ : syracuseStep 2713007 = 4069511) B4069511
theorem B26420681 : Blo 1807605 26420681 := bstep (se 2 (by rfl) ⟨9907755, by rfl⟩ : syracuseStep 26420681 = 19815511) B19815511
theorem B2713097 : Blo 1807605 2713097 := bstep (se 2 (by rfl) ⟨1017411, by rfl⟩ : syracuseStep 2713097 = 2034823) B2034823
theorem B2713127 : Blo 1807605 2713127 := bstep (se 1 (by rfl) ⟨2034845, by rfl⟩ : syracuseStep 2713127 = 4069691) B4069691
theorem B9160289 : Blo 1807605 9160289 := bstep (se 2 (by rfl) ⟨3435108, by rfl⟩ : syracuseStep 9160289 = 6870217) B6870217
theorem B6104699 : Blo 1807605 6104699 := bstep (se 1 (by rfl) ⟨4578524, by rfl⟩ : syracuseStep 6104699 = 9157049) B9157049
theorem B2713211 : Blo 1807605 2713211 := bstep (se 1 (by rfl) ⟨2034908, by rfl⟩ : syracuseStep 2713211 = 4069817) B4069817
theorem B9152189 : Blo 1807605 9152189 := bstep (se 3 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 9152189 = 3432071) B3432071
theorem B2713337 : Blo 1807605 2713337 := bstep (se 2 (by rfl) ⟨1017501, by rfl⟩ : syracuseStep 2713337 = 2035003) B2035003
theorem B6104861 : Blo 1807605 6104861 := bstep (se 3 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 6104861 = 2289323) B2289323
theorem B9152351 : Blo 1807605 9152351 := bstep (se 1 (by rfl) ⟨6864263, by rfl⟩ : syracuseStep 9152351 = 13728527) B13728527
theorem B2713439 : Blo 1807605 2713439 := bstep (se 1 (by rfl) ⟨2035079, by rfl⟩ : syracuseStep 2713439 = 4070159) B4070159
theorem B2713451 : Blo 1807605 2713451 := bstep (se 1 (by rfl) ⟨2035088, by rfl⟩ : syracuseStep 2713451 = 4070177) B4070177
theorem B5793697 : Blo 1807605 5793697 := bstep (se 2 (by rfl) ⟨2172636, by rfl⟩ : syracuseStep 5793697 = 4345273) B4345273
theorem B30902309 : Blo 1807605 30902309 := bstep (se 4 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 30902309 = 5794183) B5794183
theorem B2033743 : Blo 1807605 2033743 := bstep (se 1 (by rfl) ⟨1525307, by rfl⟩ : syracuseStep 2033743 = 3050615) B3050615
theorem B10299473 : Blo 1807605 10299473 := bstep (se 2 (by rfl) ⟨3862302, by rfl⟩ : syracuseStep 10299473 = 7724605) B7724605
theorem B2173007 : Blo 1807605 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B2713679 : Blo 1807605 2713679 := bstep (se 1 (by rfl) ⟨2035259, by rfl⟩ : syracuseStep 2713679 = 4070519) B4070519
theorem B13731929 : Blo 1807605 13731929 := bstep (se 2 (by rfl) ⟨5149473, by rfl⟩ : syracuseStep 13731929 = 10298947) B10298947
theorem B2713799 : Blo 1807605 2713799 := bstep (se 1 (by rfl) ⟨2035349, by rfl⟩ : syracuseStep 2713799 = 4070699) B4070699
theorem B63473969 : Blo 1807605 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B6867287 : Blo 1807605 6867287 := bstep (se 1 (by rfl) ⟨5150465, by rfl⟩ : syracuseStep 6867287 = 10300931) B10300931
theorem B2713961 : Blo 1807605 2713961 := bstep (se 2 (by rfl) ⟨1017735, by rfl⟩ : syracuseStep 2713961 = 2035471) B2035471
theorem B2714039 : Blo 1807605 2714039 := bstep (se 1 (by rfl) ⟨2035529, by rfl⟩ : syracuseStep 2714039 = 4071059) B4071059
theorem B2034139 : Blo 1807605 2034139 := bstep (se 1 (by rfl) ⟨1525604, by rfl⟩ : syracuseStep 2034139 = 3051209) B3051209
theorem B6105563 : Blo 1807605 6105563 := bstep (se 1 (by rfl) ⟨4579172, by rfl⟩ : syracuseStep 6105563 = 9158345) B9158345
theorem B2714075 : Blo 1807605 2714075 := bstep (se 1 (by rfl) ⟨2035556, by rfl⟩ : syracuseStep 2714075 = 4071113) B4071113
theorem B3050345 : Blo 1807605 3050345 := bstep (se 2 (by rfl) ⟨1143879, by rfl⟩ : syracuseStep 3050345 = 2287759) B2287759
theorem B2034607 : Blo 1807605 2034607 := bstep (se 1 (by rfl) ⟨1525955, by rfl⟩ : syracuseStep 2034607 = 3051911) B3051911
theorem B19565495 : Blo 1807605 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B6106265 : Blo 1807605 6106265 := bstep (se 2 (by rfl) ⟨2289849, by rfl⟩ : syracuseStep 6106265 = 4579699) B4579699
theorem B3050743 : Blo 1807605 3050743 := bstep (se 1 (by rfl) ⟨2288057, by rfl⟩ : syracuseStep 3050743 = 4576115) B4576115
theorem B13036889 : Blo 1807605 13036889 := bstep (se 2 (by rfl) ⟨4888833, by rfl⟩ : syracuseStep 13036889 = 9777667) B9777667
theorem B2035039 : Blo 1807605 2035039 := bstep (se 1 (by rfl) ⟨1526279, by rfl⟩ : syracuseStep 2035039 = 3052559) B3052559
theorem B3050939 : Blo 1807605 3050939 := bstep (se 1 (by rfl) ⟨2288204, by rfl⟩ : syracuseStep 3050939 = 4576409) B4576409
theorem B13733387 : Blo 1807605 13733387 := bstep (se 1 (by rfl) ⟨10300040, by rfl⟩ : syracuseStep 13733387 = 20600081) B20600081
theorem B3051047 : Blo 1807605 3051047 := bstep (se 1 (by rfl) ⟨2288285, by rfl⟩ : syracuseStep 3051047 = 4576571) B4576571
theorem B3862055 : Blo 1807605 3862055 := bstep (se 1 (by rfl) ⟨2896541, by rfl⟩ : syracuseStep 3862055 = 5793083) B5793083
theorem B6868577 : Blo 1807605 6868577 := bstep (se 2 (by rfl) ⟨2575716, by rfl⟩ : syracuseStep 6868577 = 5151433) B5151433
theorem B17624699 : Blo 1807605 17624699 := bstep (se 1 (by rfl) ⟨13218524, by rfl⟩ : syracuseStep 17624699 = 26437049) B26437049
theorem B5222087 : Blo 1807605 5222087 := bstep (se 1 (by rfl) ⟨3916565, by rfl⟩ : syracuseStep 5222087 = 7833131) B7833131
theorem B2035399 : Blo 1807605 2035399 := bstep (se 1 (by rfl) ⟨1526549, by rfl⟩ : syracuseStep 2035399 = 3053099) B3053099
theorem B4124371 : Blo 1807605 4124371 := bstep (se 1 (by rfl) ⟨3093278, by rfl⟩ : syracuseStep 4124371 = 6186557) B6186557
theorem B5795543 : Blo 1807605 5795543 := bstep (se 1 (by rfl) ⟨4346657, by rfl⟩ : syracuseStep 5795543 = 8693315) B8693315
theorem B2445049 : Blo 1807605 2445049 := bstep (se 2 (by rfl) ⟨916893, by rfl⟩ : syracuseStep 2445049 = 1833787) B1833787
theorem B3051337 : Blo 1807605 3051337 := bstep (se 2 (by rfl) ⟨1144251, by rfl⟩ : syracuseStep 3051337 = 2288503) B2288503
theorem B3862345 : Blo 1807605 3862345 := bstep (se 2 (by rfl) ⟨1448379, by rfl⟩ : syracuseStep 3862345 = 2896759) B2896759
theorem B3051371 : Blo 1807605 3051371 := bstep (se 1 (by rfl) ⟨2288528, by rfl⟩ : syracuseStep 3051371 = 4577057) B4577057
theorem B3862379 : Blo 1807605 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B23179193 : Blo 1807605 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B2289703 : Blo 1807605 2289703 := bstep (se 1 (by rfl) ⟨1717277, by rfl⟩ : syracuseStep 2289703 = 3434555) B3434555
theorem B8695889 : Blo 1807605 8695889 := bstep (se 2 (by rfl) ⟨3260958, by rfl⟩ : syracuseStep 8695889 = 6521917) B6521917
theorem B11907161 : Blo 1807605 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B3051769 : Blo 1807605 3051769 := bstep (se 2 (by rfl) ⟨1144413, by rfl⟩ : syracuseStep 3051769 = 2288827) B2288827
theorem B2290027 : Blo 1807605 2290027 := bstep (se 1 (by rfl) ⟨1717520, by rfl⟩ : syracuseStep 2290027 = 3435041) B3435041
theorem B104280533 : Blo 1807605 104280533 := bstep (se 7 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 104280533 = 2444075) B2444075
theorem B3052039 : Blo 1807605 3052039 := bstep (se 1 (by rfl) ⟨2289029, by rfl⟩ : syracuseStep 3052039 = 4578059) B4578059
theorem B4887049 : Blo 1807605 4887049 := bstep (se 2 (by rfl) ⟨1832643, by rfl⟩ : syracuseStep 4887049 = 3665287) B3665287
theorem B9155105 : Blo 1807605 9155105 := bstep (se 2 (by rfl) ⟨3433164, by rfl⟩ : syracuseStep 9155105 = 6866329) B6866329
theorem B4067963 : Blo 1807605 4067963 := bstep (se 1 (by rfl) ⟨3050972, by rfl⟩ : syracuseStep 4067963 = 6101945) B6101945
theorem B10302137 : Blo 1807605 10302137 := bstep (se 2 (by rfl) ⟨3863301, by rfl⟩ : syracuseStep 10302137 = 7726603) B7726603
theorem B2896631 : Blo 1807605 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B4068089 : Blo 1807605 4068089 := bstep (se 2 (by rfl) ⟨1525533, by rfl⟩ : syracuseStep 4068089 = 3051067) B3051067
theorem B5223241 : Blo 1807605 5223241 := bstep (se 2 (by rfl) ⟨1958715, by rfl⟩ : syracuseStep 5223241 = 3917431) B3917431
theorem B2749367 : Blo 1807605 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B3052471 : Blo 1807605 3052471 := bstep (se 1 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 3052471 = 4578707) B4578707
theorem B4068359 : Blo 1807605 4068359 := bstep (se 1 (by rfl) ⟨3051269, by rfl⟩ : syracuseStep 4068359 = 6102539) B6102539
theorem B2937865 : Blo 1807605 2937865 := bstep (se 2 (by rfl) ⟨1101699, by rfl⟩ : syracuseStep 2937865 = 2203399) B2203399
theorem B6870035 : Blo 1807605 6870035 := bstep (se 1 (by rfl) ⟨5152526, by rfl⟩ : syracuseStep 6870035 = 10305053) B10305053
theorem B3257383 : Blo 1807605 3257383 := bstep (se 1 (by rfl) ⟨2443037, by rfl⟩ : syracuseStep 3257383 = 4886075) B4886075
theorem B4068431 : Blo 1807605 4068431 := bstep (se 1 (by rfl) ⟨3051323, by rfl⟩ : syracuseStep 4068431 = 6102647) B6102647
theorem B3052667 : Blo 1807605 3052667 := bstep (se 1 (by rfl) ⟨2289500, by rfl⟩ : syracuseStep 3052667 = 4579001) B4579001
theorem B3527891 : Blo 1807605 3527891 := bstep (se 1 (by rfl) ⟨2645918, by rfl⟩ : syracuseStep 3527891 = 5291837) B5291837
theorem B1807655 : Blo 1807605 1807655 := bstep (se 1 (by rfl) ⟨1355741, by rfl⟩ : syracuseStep 1807655 = 2711483) B2711483
theorem B1807695 : Blo 1807605 1807695 := bstep (se 1 (by rfl) ⟨1355771, by rfl⟩ : syracuseStep 1807695 = 2711543) B2711543
theorem B1807711 : Blo 1807605 1807711 := bstep (se 1 (by rfl) ⟨1355783, by rfl⟩ : syracuseStep 1807711 = 2711567) B2711567
theorem B1807739 : Blo 1807605 1807739 := bstep (se 1 (by rfl) ⟨1355804, by rfl⟩ : syracuseStep 1807739 = 2711609) B2711609
theorem B6518141 : Blo 1807605 6518141 := bstep (se 3 (by rfl) ⟨1222151, by rfl⟩ : syracuseStep 6518141 = 2444303) B2444303
theorem B3863951 : Blo 1807605 3863951 := bstep (se 1 (by rfl) ⟨2897963, by rfl⟩ : syracuseStep 3863951 = 5795927) B5795927
theorem B13735331 : Blo 1807605 13735331 := bstep (se 1 (by rfl) ⟨10301498, by rfl⟩ : syracuseStep 13735331 = 20602997) B20602997
theorem B1807791 : Blo 1807605 1807791 := bstep (se 1 (by rfl) ⟨1355843, by rfl⟩ : syracuseStep 1807791 = 2711687) B2711687
theorem B1807815 : Blo 1807605 1807815 := bstep (se 1 (by rfl) ⟨1355861, by rfl⟩ : syracuseStep 1807815 = 2711723) B2711723
theorem B1807835 : Blo 1807605 1807835 := bstep (se 1 (by rfl) ⟨1355876, by rfl⟩ : syracuseStep 1807835 = 2711753) B2711753
theorem B4068827 : Blo 1807605 4068827 := bstep (se 1 (by rfl) ⟨3051620, by rfl⟩ : syracuseStep 4068827 = 6103241) B6103241
theorem B6870491 : Blo 1807605 6870491 := bstep (se 1 (by rfl) ⟨5152868, by rfl⟩ : syracuseStep 6870491 = 10305737) B10305737
theorem B3053065 : Blo 1807605 3053065 := bstep (se 2 (by rfl) ⟨1144899, by rfl⟩ : syracuseStep 3053065 = 2289799) B2289799
theorem B1807911 : Blo 1807605 1807911 := bstep (se 1 (by rfl) ⟨1355933, by rfl⟩ : syracuseStep 1807911 = 2711867) B2711867
theorem B1807951 : Blo 1807605 1807951 := bstep (se 1 (by rfl) ⟨1355963, by rfl⟩ : syracuseStep 1807951 = 2711927) B2711927
theorem B1807967 : Blo 1807605 1807967 := bstep (se 1 (by rfl) ⟨1355975, by rfl⟩ : syracuseStep 1807967 = 2711951) B2711951
theorem B26080865 : Blo 1807605 26080865 := bstep (se 2 (by rfl) ⟨9780324, by rfl⟩ : syracuseStep 26080865 = 19560649) B19560649
theorem B1807995 : Blo 1807605 1807995 := bstep (se 1 (by rfl) ⟨1355996, by rfl⟩ : syracuseStep 1807995 = 2711993) B2711993
theorem B2897579 : Blo 1807605 2897579 := bstep (se 1 (by rfl) ⟨2173184, by rfl⟩ : syracuseStep 2897579 = 4346369) B4346369
theorem B3053227 : Blo 1807605 3053227 := bstep (se 1 (by rfl) ⟨2289920, by rfl⟩ : syracuseStep 3053227 = 4579841) B4579841
theorem B1808047 : Blo 1807605 1808047 := bstep (se 1 (by rfl) ⟨1356035, by rfl⟩ : syracuseStep 1808047 = 2712071) B2712071
theorem B1808071 : Blo 1807605 1808071 := bstep (se 1 (by rfl) ⟨1356053, by rfl⟩ : syracuseStep 1808071 = 2712107) B2712107
theorem B1808091 : Blo 1807605 1808091 := bstep (se 1 (by rfl) ⟨1356068, by rfl⟩ : syracuseStep 1808091 = 2712137) B2712137
theorem B9279197 : Blo 1807605 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B1808167 : Blo 1807605 1808167 := bstep (se 1 (by rfl) ⟨1356125, by rfl⟩ : syracuseStep 1808167 = 2712251) B2712251
theorem B13727555 : Blo 1807605 13727555 := bstep (se 1 (by rfl) ⟨10295666, by rfl⟩ : syracuseStep 13727555 = 20591333) B20591333
theorem B190502725 : Blo 1807605 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B1808207 : Blo 1807605 1808207 := bstep (se 1 (by rfl) ⟨1356155, by rfl⟩ : syracuseStep 1808207 = 2712311) B2712311
theorem B1808223 : Blo 1807605 1808223 := bstep (se 1 (by rfl) ⟨1356167, by rfl⟩ : syracuseStep 1808223 = 2712335) B2712335
theorem B2750315 : Blo 1807605 2750315 := bstep (se 1 (by rfl) ⟨2062736, by rfl⟩ : syracuseStep 2750315 = 4125473) B4125473
theorem B1808251 : Blo 1807605 1808251 := bstep (se 1 (by rfl) ⟨1356188, by rfl⟩ : syracuseStep 1808251 = 2712377) B2712377
theorem B4642721 : Blo 1807605 4642721 := bstep (se 2 (by rfl) ⟨1741020, by rfl⟩ : syracuseStep 4642721 = 3482041) B3482041
theorem B1808303 : Blo 1807605 1808303 := bstep (se 1 (by rfl) ⟨1356227, by rfl⟩ : syracuseStep 1808303 = 2712455) B2712455
theorem B4069295 : Blo 1807605 4069295 := bstep (se 1 (by rfl) ⟨3051971, by rfl⟩ : syracuseStep 4069295 = 6103943) B6103943
theorem B6100919 : Blo 1807605 6100919 := bstep (se 1 (by rfl) ⟨4575689, by rfl⟩ : syracuseStep 6100919 = 9151379) B9151379
theorem B1808327 : Blo 1807605 1808327 := bstep (se 1 (by rfl) ⟨1356245, by rfl⟩ : syracuseStep 1808327 = 2712491) B2712491
theorem B1808347 : Blo 1807605 1808347 := bstep (se 1 (by rfl) ⟨1356260, by rfl⟩ : syracuseStep 1808347 = 2712521) B2712521
theorem B3053531 : Blo 1807605 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B10442789 : Blo 1807605 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B1808423 : Blo 1807605 1808423 := bstep (se 1 (by rfl) ⟨1356317, by rfl⟩ : syracuseStep 1808423 = 2712635) B2712635
theorem B55703609 : Blo 1807605 55703609 := bstep (se 2 (by rfl) ⟨20888853, by rfl⟩ : syracuseStep 55703609 = 41777707) B41777707
theorem B1808463 : Blo 1807605 1808463 := bstep (se 1 (by rfl) ⟨1356347, by rfl⟩ : syracuseStep 1808463 = 2712695) B2712695
theorem B1808479 : Blo 1807605 1808479 := bstep (se 1 (by rfl) ⟨1356359, by rfl⟩ : syracuseStep 1808479 = 2712719) B2712719
theorem B1808507 : Blo 1807605 1808507 := bstep (se 1 (by rfl) ⟨1356380, by rfl⟩ : syracuseStep 1808507 = 2712761) B2712761
theorem B4069547 : Blo 1807605 4069547 := bstep (se 1 (by rfl) ⟨3052160, by rfl⟩ : syracuseStep 4069547 = 6104321) B6104321
theorem B1808559 : Blo 1807605 1808559 := bstep (se 1 (by rfl) ⟨1356419, by rfl⟩ : syracuseStep 1808559 = 2712839) B2712839
theorem B1808583 : Blo 1807605 1808583 := bstep (se 1 (by rfl) ⟨1356437, by rfl⟩ : syracuseStep 1808583 = 2712875) B2712875
theorem B1808603 : Blo 1807605 1808603 := bstep (se 1 (by rfl) ⟨1356452, by rfl⟩ : syracuseStep 1808603 = 2712905) B2712905
theorem B1808679 : Blo 1807605 1808679 := bstep (se 1 (by rfl) ⟨1356509, by rfl⟩ : syracuseStep 1808679 = 2713019) B2713019
theorem B1808719 : Blo 1807605 1808719 := bstep (se 1 (by rfl) ⟨1356539, by rfl⟩ : syracuseStep 1808719 = 2713079) B2713079
theorem B1808735 : Blo 1807605 1808735 := bstep (se 1 (by rfl) ⟨1356551, by rfl⟩ : syracuseStep 1808735 = 2713103) B2713103
theorem B2898271 : Blo 1807605 2898271 := bstep (se 1 (by rfl) ⟨2173703, by rfl⟩ : syracuseStep 2898271 = 4347407) B4347407
theorem B1808763 : Blo 1807605 1808763 := bstep (se 1 (by rfl) ⟨1356572, by rfl⟩ : syracuseStep 1808763 = 2713145) B2713145
theorem B1808815 : Blo 1807605 1808815 := bstep (se 1 (by rfl) ⟨1356611, by rfl⟩ : syracuseStep 1808815 = 2713223) B2713223
theorem B1808839 : Blo 1807605 1808839 := bstep (se 1 (by rfl) ⟨1356629, by rfl⟩ : syracuseStep 1808839 = 2713259) B2713259
theorem B4577755 : Blo 1807605 4577755 := bstep (se 1 (by rfl) ⟨3433316, by rfl⟩ : syracuseStep 4577755 = 6866633) B6866633
theorem B1808859 : Blo 1807605 1808859 := bstep (se 1 (by rfl) ⟨1356644, by rfl⟩ : syracuseStep 1808859 = 2713289) B2713289
theorem B6101513 : Blo 1807605 6101513 := bstep (se 2 (by rfl) ⟨2288067, by rfl⟩ : syracuseStep 6101513 = 4576135) B4576135
theorem B6863399 : Blo 1807605 6863399 := bstep (se 1 (by rfl) ⟨5147549, by rfl⟩ : syracuseStep 6863399 = 10295099) B10295099
theorem B1808935 : Blo 1807605 1808935 := bstep (se 1 (by rfl) ⟨1356701, by rfl⟩ : syracuseStep 1808935 = 2713403) B2713403
theorem B1808975 : Blo 1807605 1808975 := bstep (se 1 (by rfl) ⟨1356731, by rfl⟩ : syracuseStep 1808975 = 2713463) B2713463
theorem B1808991 : Blo 1807605 1808991 := bstep (se 1 (by rfl) ⟨1356743, by rfl⟩ : syracuseStep 1808991 = 2713487) B2713487
theorem B1809019 : Blo 1807605 1809019 := bstep (se 1 (by rfl) ⟨1356764, by rfl⟩ : syracuseStep 1809019 = 2713529) B2713529
theorem B1809071 : Blo 1807605 1809071 := bstep (se 1 (by rfl) ⟨1356803, by rfl⟩ : syracuseStep 1809071 = 2713607) B2713607
theorem B34749107 : Blo 1807605 34749107 := bstep (se 1 (by rfl) ⟨26061830, by rfl⟩ : syracuseStep 34749107 = 52123661) B52123661
theorem B4070087 : Blo 1807605 4070087 := bstep (se 1 (by rfl) ⟨3052565, by rfl⟩ : syracuseStep 4070087 = 6105131) B6105131
theorem B1809095 : Blo 1807605 1809095 := bstep (se 1 (by rfl) ⟨1356821, by rfl⟩ : syracuseStep 1809095 = 2713643) B2713643
theorem B1809115 : Blo 1807605 1809115 := bstep (se 1 (by rfl) ⟨1356836, by rfl⟩ : syracuseStep 1809115 = 2713673) B2713673
theorem B70441757 : Blo 1807605 70441757 := bstep (se 3 (by rfl) ⟨13207829, by rfl⟩ : syracuseStep 70441757 = 26415659) B26415659
theorem B1809191 : Blo 1807605 1809191 := bstep (se 1 (by rfl) ⟨1356893, by rfl⟩ : syracuseStep 1809191 = 2713787) B2713787
theorem B1809231 : Blo 1807605 1809231 := bstep (se 1 (by rfl) ⟨1356923, by rfl⟩ : syracuseStep 1809231 = 2713847) B2713847
theorem B1809247 : Blo 1807605 1809247 := bstep (se 1 (by rfl) ⟨1356935, by rfl⟩ : syracuseStep 1809247 = 2713871) B2713871
theorem B13032299 : Blo 1807605 13032299 := bstep (se 1 (by rfl) ⟨9774224, by rfl⟩ : syracuseStep 13032299 = 19548449) B19548449
theorem B80329589 : Blo 1807605 80329589 := bstep (se 5 (by rfl) ⟨3765449, by rfl⟩ : syracuseStep 80329589 = 7530899) B7530899
theorem B1809275 : Blo 1807605 1809275 := bstep (se 1 (by rfl) ⟨1356956, by rfl⟩ : syracuseStep 1809275 = 2713913) B2713913
theorem B15457169 : Blo 1807605 15457169 := bstep (se 2 (by rfl) ⟨5796438, by rfl⟩ : syracuseStep 15457169 = 11592877) B11592877
theorem B1809327 : Blo 1807605 1809327 := bstep (se 1 (by rfl) ⟨1356995, by rfl⟩ : syracuseStep 1809327 = 2713991) B2713991
theorem B1809351 : Blo 1807605 1809351 := bstep (se 1 (by rfl) ⟨1357013, by rfl⟩ : syracuseStep 1809351 = 2714027) B2714027
theorem B1809371 : Blo 1807605 1809371 := bstep (se 1 (by rfl) ⟨1357028, by rfl⟩ : syracuseStep 1809371 = 2714057) B2714057
theorem B1809447 : Blo 1807605 1809447 := bstep (se 1 (by rfl) ⟨1357085, by rfl⟩ : syracuseStep 1809447 = 2714171) B2714171
theorem B4578383 : Blo 1807605 4578383 := bstep (se 1 (by rfl) ⟨3433787, by rfl⟩ : syracuseStep 4578383 = 6867575) B6867575
theorem B1809487 : Blo 1807605 1809487 := bstep (se 1 (by rfl) ⟨1357115, by rfl⟩ : syracuseStep 1809487 = 2714231) B2714231
theorem B1809503 : Blo 1807605 1809503 := bstep (se 1 (by rfl) ⟨1357127, by rfl⟩ : syracuseStep 1809503 = 2714255) B2714255
theorem B7330931 : Blo 1807605 7330931 := bstep (se 1 (by rfl) ⟨5498198, by rfl⟩ : syracuseStep 7330931 = 10996397) B10996397
theorem B1809531 : Blo 1807605 1809531 := bstep (se 1 (by rfl) ⟨1357148, by rfl⟩ : syracuseStep 1809531 = 2714297) B2714297
theorem B1809583 : Blo 1807605 1809583 := bstep (se 1 (by rfl) ⟨1357187, by rfl⟩ : syracuseStep 1809583 = 2714375) B2714375
theorem B39099665 : Blo 1807605 39099665 := bstep (se 2 (by rfl) ⟨14662374, by rfl⟩ : syracuseStep 39099665 = 29324749) B29324749
theorem B6102377 : Blo 1807605 6102377 := bstep (se 2 (by rfl) ⟨2288391, by rfl⟩ : syracuseStep 6102377 = 4576783) B4576783
theorem B6610301 : Blo 1807605 6610301 := bstep (se 3 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 6610301 = 2478863) B2478863
theorem B3718561 : Blo 1807605 3718561 := bstep (se 2 (by rfl) ⟨1394460, by rfl⟩ : syracuseStep 3718561 = 2788921) B2788921
theorem B6864371 : Blo 1807605 6864371 := bstep (se 1 (by rfl) ⟨5148278, by rfl⟩ : syracuseStep 6864371 = 10296557) B10296557
theorem B9158183 : Blo 1807605 9158183 := bstep (se 1 (by rfl) ⟨6868637, by rfl⟩ : syracuseStep 9158183 = 13737275) B13737275
theorem B4070951 : Blo 1807605 4070951 := bstep (se 1 (by rfl) ⟨3053213, by rfl⟩ : syracuseStep 4070951 = 6106427) B6106427
theorem B4579031 : Blo 1807605 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B13737761 : Blo 1807605 13737761 := bstep (se 2 (by rfl) ⟨5151660, by rfl⟩ : syracuseStep 13737761 = 10303321) B10303321
theorem B3260267 : Blo 1807605 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B4071275 : Blo 1807605 4071275 := bstep (se 1 (by rfl) ⟨3053456, by rfl⟩ : syracuseStep 4071275 = 6106913) B6106913
theorem B39100279 : Blo 1807605 39100279 := bstep (se 1 (by rfl) ⟨29325209, by rfl⟩ : syracuseStep 39100279 = 58650419) B58650419
theorem B29319043 : Blo 1807605 29319043 := bstep (se 1 (by rfl) ⟨21989282, by rfl⟩ : syracuseStep 29319043 = 43978565) B43978565
theorem B4071329 : Blo 1807605 4071329 := bstep (se 2 (by rfl) ⟨1526748, by rfl⟩ : syracuseStep 4071329 = 3053497) B3053497
theorem B2711471 : Blo 1807605 2711471 := bstep (se 1 (by rfl) ⟨2033603, by rfl⟩ : syracuseStep 2711471 = 4067207) B4067207
theorem B6102971 : Blo 1807605 6102971 := bstep (se 1 (by rfl) ⟨4577228, by rfl⟩ : syracuseStep 6102971 = 9154457) B9154457
theorem B6520763 : Blo 1807605 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B7938107 : Blo 1807605 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B2711657 : Blo 1807605 2711657 := bstep (se 2 (by rfl) ⟨1016871, by rfl⟩ : syracuseStep 2711657 = 2033743) B2033743
theorem B6103403 : Blo 1807605 6103403 := bstep (se 1 (by rfl) ⟨4577552, by rfl⟩ : syracuseStep 6103403 = 9155105) B9155105
theorem B2711975 : Blo 1807605 2711975 := bstep (se 1 (by rfl) ⟨2033981, by rfl⟩ : syracuseStep 2711975 = 4067963) B4067963
theorem B2712059 : Blo 1807605 2712059 := bstep (se 1 (by rfl) ⟨2034044, by rfl⟩ : syracuseStep 2712059 = 4068089) B4068089
theorem B2712185 : Blo 1807605 2712185 := bstep (se 2 (by rfl) ⟨1017069, by rfl⟩ : syracuseStep 2712185 = 2034139) B2034139
theorem B6103673 : Blo 1807605 6103673 := bstep (se 2 (by rfl) ⟨2288877, by rfl⟩ : syracuseStep 6103673 = 4577755) B4577755
theorem B2712239 : Blo 1807605 2712239 := bstep (se 1 (by rfl) ⟨2034179, by rfl⟩ : syracuseStep 2712239 = 4068359) B4068359
theorem B4580023 : Blo 1807605 4580023 := bstep (se 1 (by rfl) ⟨3435017, by rfl⟩ : syracuseStep 4580023 = 6870035) B6870035
theorem B2712287 : Blo 1807605 2712287 := bstep (se 1 (by rfl) ⟨2034215, by rfl⟩ : syracuseStep 2712287 = 4068431) B4068431
theorem B6865631 : Blo 1807605 6865631 := bstep (se 1 (by rfl) ⟨5149223, by rfl⟩ : syracuseStep 6865631 = 10298447) B10298447
theorem B2351927 : Blo 1807605 2351927 := bstep (se 1 (by rfl) ⟨1763945, by rfl⟩ : syracuseStep 2351927 = 3527891) B3527891
theorem B20874131 : Blo 1807605 20874131 := bstep (se 1 (by rfl) ⟨15655598, by rfl⟩ : syracuseStep 20874131 = 31311197) B31311197
theorem B6521801 : Blo 1807605 6521801 := bstep (se 2 (by rfl) ⟨2445675, by rfl⟩ : syracuseStep 6521801 = 4891351) B4891351
theorem B17613787 : Blo 1807605 17613787 := bstep (se 1 (by rfl) ⟨13210340, by rfl⟩ : syracuseStep 17613787 = 26420681) B26420681
theorem B2712551 : Blo 1807605 2712551 := bstep (se 1 (by rfl) ⟨2034413, by rfl⟩ : syracuseStep 2712551 = 4068827) B4068827
theorem B4580327 : Blo 1807605 4580327 := bstep (se 1 (by rfl) ⟨3435245, by rfl⟩ : syracuseStep 4580327 = 6870491) B6870491
theorem B6964321 : Blo 1807605 6964321 := bstep (se 2 (by rfl) ⟨2611620, by rfl⟩ : syracuseStep 6964321 = 5223241) B5223241
theorem B6186131 : Blo 1807605 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B9151703 : Blo 1807605 9151703 := bstep (se 1 (by rfl) ⟨6863777, by rfl⟩ : syracuseStep 9151703 = 13727555) B13727555
theorem B2712809 : Blo 1807605 2712809 := bstep (se 2 (by rfl) ⟨1017303, by rfl⟩ : syracuseStep 2712809 = 2034607) B2034607
theorem B2712863 : Blo 1807605 2712863 := bstep (se 1 (by rfl) ⟨2034647, by rfl⟩ : syracuseStep 2712863 = 4069295) B4069295
theorem B3917153 : Blo 1807605 3917153 := bstep (se 2 (by rfl) ⟨1468932, by rfl⟩ : syracuseStep 3917153 = 2937865) B2937865
theorem B37135739 : Blo 1807605 37135739 := bstep (se 1 (by rfl) ⟨27851804, by rfl⟩ : syracuseStep 37135739 = 55703609) B55703609
theorem B4343177 : Blo 1807605 4343177 := bstep (se 2 (by rfl) ⟨1628691, by rfl⟩ : syracuseStep 4343177 = 3257383) B3257383
theorem B6866315 : Blo 1807605 6866315 := bstep (se 1 (by rfl) ⟨5149736, by rfl⟩ : syracuseStep 6866315 = 10299473) B10299473
theorem B2713031 : Blo 1807605 2713031 := bstep (se 1 (by rfl) ⟨2034773, by rfl⟩ : syracuseStep 2713031 = 4069547) B4069547
theorem B7726877 : Blo 1807605 7726877 := bstep (se 3 (by rfl) ⟨1448789, by rfl⟩ : syracuseStep 7726877 = 2897579) B2897579
theorem B2713385 : Blo 1807605 2713385 := bstep (se 2 (by rfl) ⟨1017519, by rfl⟩ : syracuseStep 2713385 = 2035039) B2035039
theorem B2713391 : Blo 1807605 2713391 := bstep (se 1 (by rfl) ⟨2035043, by rfl⟩ : syracuseStep 2713391 = 4070087) B4070087
theorem B4958081 : Blo 1807605 4958081 := bstep (se 2 (by rfl) ⟨1859280, by rfl⟩ : syracuseStep 4958081 = 3718561) B3718561
theorem B2033563 : Blo 1807605 2033563 := bstep (se 1 (by rfl) ⟨1525172, by rfl⟩ : syracuseStep 2033563 = 3050345) B3050345
theorem B53553059 : Blo 1807605 53553059 := bstep (se 1 (by rfl) ⟨40164794, by rfl⟩ : syracuseStep 53553059 = 80329589) B80329589
theorem B13043663 : Blo 1807605 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B2713865 : Blo 1807605 2713865 := bstep (se 2 (by rfl) ⟨1017699, by rfl⟩ : syracuseStep 2713865 = 2035399) B2035399
theorem B5499161 : Blo 1807605 5499161 := bstep (se 2 (by rfl) ⟨2062185, by rfl⟩ : syracuseStep 5499161 = 4124371) B4124371
theorem B34752797 : Blo 1807605 34752797 := bstep (se 3 (by rfl) ⟨6516149, by rfl⟩ : syracuseStep 34752797 = 13032299) B13032299
theorem B7334173 : Blo 1807605 7334173 := bstep (se 3 (by rfl) ⟨1375157, by rfl⟩ : syracuseStep 7334173 = 2750315) B2750315
theorem B2033959 : Blo 1807605 2033959 := bstep (se 1 (by rfl) ⟨1525469, by rfl⟩ : syracuseStep 2033959 = 3050939) B3050939
theorem B2034031 : Blo 1807605 2034031 := bstep (se 1 (by rfl) ⟨1525523, by rfl⟩ : syracuseStep 2034031 = 3051047) B3051047
theorem B2574703 : Blo 1807605 2574703 := bstep (se 1 (by rfl) ⟨1931027, by rfl⟩ : syracuseStep 2574703 = 3862055) B3862055
theorem B6105455 : Blo 1807605 6105455 := bstep (se 1 (by rfl) ⟨4579091, by rfl⟩ : syracuseStep 6105455 = 9158183) B9158183
theorem B2713967 : Blo 1807605 2713967 := bstep (se 1 (by rfl) ⟨2035475, by rfl⟩ : syracuseStep 2713967 = 4070951) B4070951
theorem B11749799 : Blo 1807605 11749799 := bstep (se 1 (by rfl) ⟨8812349, by rfl⟩ : syracuseStep 11749799 = 17624699) B17624699
theorem B254003633 : Blo 1807605 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B2034247 : Blo 1807605 2034247 := bstep (se 1 (by rfl) ⟨1525685, by rfl⟩ : syracuseStep 2034247 = 3051371) B3051371
theorem B2574919 : Blo 1807605 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B2173511 : Blo 1807605 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B2714183 : Blo 1807605 2714183 := bstep (se 1 (by rfl) ⟨2035637, by rfl⟩ : syracuseStep 2714183 = 4071275) B4071275
theorem B2714219 : Blo 1807605 2714219 := bstep (se 1 (by rfl) ⟨2035664, by rfl⟩ : syracuseStep 2714219 = 4071329) B4071329
theorem B15452795 : Blo 1807605 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B2288351 : Blo 1807605 2288351 := bstep (se 1 (by rfl) ⟨1716263, by rfl⟩ : syracuseStep 2288351 = 3432527) B3432527
theorem B12069665 : Blo 1807605 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B5794685 : Blo 1807605 5794685 := bstep (se 3 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 5794685 = 2173007) B2173007
theorem B69520355 : Blo 1807605 69520355 := bstep (se 1 (by rfl) ⟨52140266, by rfl⟩ : syracuseStep 69520355 = 104280533) B104280533
theorem B6868091 : Blo 1807605 6868091 := bstep (se 1 (by rfl) ⟨5151068, by rfl⟩ : syracuseStep 6868091 = 10302137) B10302137
theorem B6516065 : Blo 1807605 6516065 := bstep (se 2 (by rfl) ⟨2443524, by rfl⟩ : syracuseStep 6516065 = 4887049) B4887049
theorem B2035111 : Blo 1807605 2035111 := bstep (se 1 (by rfl) ⟨1526333, by rfl⟩ : syracuseStep 2035111 = 3052667) B3052667
theorem B5221847 : Blo 1807605 5221847 := bstep (se 1 (by rfl) ⟨3916385, by rfl⟩ : syracuseStep 5221847 = 7832771) B7832771
theorem B4345427 : Blo 1807605 4345427 := bstep (se 1 (by rfl) ⟨3259070, by rfl⟩ : syracuseStep 4345427 = 6518141) B6518141
theorem B3714655 : Blo 1807605 3714655 := bstep (se 1 (by rfl) ⟨2785991, by rfl⟩ : syracuseStep 3714655 = 5571983) B5571983
theorem B2575967 : Blo 1807605 2575967 := bstep (se 1 (by rfl) ⟨1931975, by rfl⟩ : syracuseStep 2575967 = 3863951) B3863951
theorem B9776801 : Blo 1807605 9776801 := bstep (se 2 (by rfl) ⟨3666300, by rfl⟩ : syracuseStep 9776801 = 7332601) B7332601
theorem B8695505 : Blo 1807605 8695505 := bstep (se 2 (by rfl) ⟨3260814, by rfl⟩ : syracuseStep 8695505 = 6521629) B6521629
theorem B17387243 : Blo 1807605 17387243 := bstep (se 1 (by rfl) ⟨13040432, by rfl⟩ : syracuseStep 17387243 = 26080865) B26080865
theorem B6106859 : Blo 1807605 6106859 := bstep (se 1 (by rfl) ⟨4580144, by rfl⟩ : syracuseStep 6106859 = 9160289) B9160289
theorem B4067279 : Blo 1807605 4067279 := bstep (se 1 (by rfl) ⟨3050459, by rfl⟩ : syracuseStep 4067279 = 6100919) B6100919
theorem B2035687 : Blo 1807605 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B9154619 : Blo 1807605 9154619 := bstep (se 1 (by rfl) ⟨6865964, by rfl⟩ : syracuseStep 9154619 = 13731929) B13731929
theorem B42315979 : Blo 1807605 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B4067657 : Blo 1807605 4067657 := bstep (se 2 (by rfl) ⟨1525371, by rfl⟩ : syracuseStep 4067657 = 3050743) B3050743
theorem B4067675 : Blo 1807605 4067675 := bstep (se 1 (by rfl) ⟨3050756, by rfl⟩ : syracuseStep 4067675 = 6101513) B6101513
theorem B4575599 : Blo 1807605 4575599 := bstep (se 1 (by rfl) ⟨3431699, by rfl⟩ : syracuseStep 4575599 = 6863399) B6863399
theorem B46961171 : Blo 1807605 46961171 := bstep (se 1 (by rfl) ⟨35220878, by rfl⟩ : syracuseStep 46961171 = 70441757) B70441757
theorem B3052255 : Blo 1807605 3052255 := bstep (se 1 (by rfl) ⟨2289191, by rfl⟩ : syracuseStep 3052255 = 4578383) B4578383
theorem B4887287 : Blo 1807605 4887287 := bstep (se 1 (by rfl) ⟨3665465, by rfl⟩ : syracuseStep 4887287 = 7330931) B7330931
theorem B4068251 : Blo 1807605 4068251 := bstep (se 1 (by rfl) ⟨3051188, by rfl⟩ : syracuseStep 4068251 = 6102377) B6102377
theorem B4576247 : Blo 1807605 4576247 := bstep (se 1 (by rfl) ⟨3432185, by rfl⟩ : syracuseStep 4576247 = 6864371) B6864371
theorem B9155591 : Blo 1807605 9155591 := bstep (se 1 (by rfl) ⟨6866693, by rfl⟩ : syracuseStep 9155591 = 13733387) B13733387
theorem B4068449 : Blo 1807605 4068449 := bstep (se 2 (by rfl) ⟨1525668, by rfl⟩ : syracuseStep 4068449 = 3051337) B3051337
theorem B5149793 : Blo 1807605 5149793 := bstep (se 2 (by rfl) ⟨1931172, by rfl⟩ : syracuseStep 5149793 = 3862345) B3862345
theorem B3052687 : Blo 1807605 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B3863695 : Blo 1807605 3863695 := bstep (se 1 (by rfl) ⟨2897771, by rfl⟩ : syracuseStep 3863695 = 5795543) B5795543
theorem B17388701 : Blo 1807605 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B1807647 : Blo 1807605 1807647 := bstep (se 1 (by rfl) ⟨1355735, by rfl⟩ : syracuseStep 1807647 = 2711471) B2711471
theorem B4068647 : Blo 1807605 4068647 := bstep (se 1 (by rfl) ⟨3051485, by rfl⟩ : syracuseStep 4068647 = 6102971) B6102971
theorem B1807707 : Blo 1807605 1807707 := bstep (se 1 (by rfl) ⟨1355780, by rfl⟩ : syracuseStep 1807707 = 2711561) B2711561
theorem B1807727 : Blo 1807605 1807727 := bstep (se 1 (by rfl) ⟨1355795, by rfl⟩ : syracuseStep 1807727 = 2711591) B2711591
theorem B3052937 : Blo 1807605 3052937 := bstep (se 2 (by rfl) ⟨1144851, by rfl⟩ : syracuseStep 3052937 = 2289703) B2289703
theorem B5797259 : Blo 1807605 5797259 := bstep (se 1 (by rfl) ⟨4347944, by rfl⟩ : syracuseStep 5797259 = 8695889) B8695889
theorem B1807783 : Blo 1807605 1807783 := bstep (se 1 (by rfl) ⟨1355837, by rfl⟩ : syracuseStep 1807783 = 2711675) B2711675
theorem B9156077 : Blo 1807605 9156077 := bstep (se 3 (by rfl) ⟨1716764, by rfl⟩ : syracuseStep 9156077 = 3433529) B3433529
theorem B1807867 : Blo 1807605 1807867 := bstep (se 1 (by rfl) ⟨1355900, by rfl⟩ : syracuseStep 1807867 = 2711801) B2711801
theorem B7722503 : Blo 1807605 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B1807935 : Blo 1807605 1807935 := bstep (se 1 (by rfl) ⟨1355951, by rfl⟩ : syracuseStep 1807935 = 2711903) B2711903
theorem B1807943 : Blo 1807605 1807943 := bstep (se 1 (by rfl) ⟨1355957, by rfl⟩ : syracuseStep 1807943 = 2711915) B2711915
theorem B4069025 : Blo 1807605 4069025 := bstep (se 2 (by rfl) ⟨1525884, by rfl⟩ : syracuseStep 4069025 = 3051769) B3051769
theorem B59463353 : Blo 1807605 59463353 := bstep (se 2 (by rfl) ⟨22298757, by rfl⟩ : syracuseStep 59463353 = 44597515) B44597515
theorem B1808095 : Blo 1807605 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B3864361 : Blo 1807605 3864361 := bstep (se 2 (by rfl) ⟨1449135, by rfl⟩ : syracuseStep 3864361 = 2898271) B2898271
theorem B1808175 : Blo 1807605 1808175 := bstep (se 1 (by rfl) ⟨1356131, by rfl⟩ : syracuseStep 1808175 = 2712263) B2712263
theorem B3053369 : Blo 1807605 3053369 := bstep (se 2 (by rfl) ⟨1145013, by rfl⟩ : syracuseStep 3053369 = 2290027) B2290027
theorem B1931087 : Blo 1807605 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B1808283 : Blo 1807605 1808283 := bstep (se 1 (by rfl) ⟨1356212, by rfl⟩ : syracuseStep 1808283 = 2712425) B2712425
theorem B1832911 : Blo 1807605 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B1808335 : Blo 1807605 1808335 := bstep (se 1 (by rfl) ⟨1356251, by rfl⟩ : syracuseStep 1808335 = 2712503) B2712503
theorem B1808359 : Blo 1807605 1808359 := bstep (se 1 (by rfl) ⟨1356269, by rfl⟩ : syracuseStep 1808359 = 2712539) B2712539
theorem B4069385 : Blo 1807605 4069385 := bstep (se 2 (by rfl) ⟨1526019, by rfl⟩ : syracuseStep 4069385 = 3052039) B3052039
theorem B15456419 : Blo 1807605 15456419 := bstep (se 1 (by rfl) ⟨11592314, by rfl⟩ : syracuseStep 15456419 = 23184629) B23184629
theorem B7723289 : Blo 1807605 7723289 := bstep (se 2 (by rfl) ⟨2896233, by rfl⟩ : syracuseStep 7723289 = 5792467) B5792467
theorem B9156887 : Blo 1807605 9156887 := bstep (se 1 (by rfl) ⟨6867665, by rfl⟩ : syracuseStep 9156887 = 13735331) B13735331
theorem B1808671 : Blo 1807605 1808671 := bstep (se 1 (by rfl) ⟨1356503, by rfl⟩ : syracuseStep 1808671 = 2713007) B2713007
theorem B1808731 : Blo 1807605 1808731 := bstep (se 1 (by rfl) ⟨1356548, by rfl⟩ : syracuseStep 1808731 = 2713097) B2713097
theorem B1808751 : Blo 1807605 1808751 := bstep (se 1 (by rfl) ⟨1356563, by rfl⟩ : syracuseStep 1808751 = 2713127) B2713127
theorem B4069799 : Blo 1807605 4069799 := bstep (se 1 (by rfl) ⟨3052349, by rfl⟩ : syracuseStep 4069799 = 6104699) B6104699
theorem B1808807 : Blo 1807605 1808807 := bstep (se 1 (by rfl) ⟨1356605, by rfl⟩ : syracuseStep 1808807 = 2713211) B2713211
theorem B6101459 : Blo 1807605 6101459 := bstep (se 1 (by rfl) ⟨4576094, by rfl⟩ : syracuseStep 6101459 = 9152189) B9152189
theorem B1808891 : Blo 1807605 1808891 := bstep (se 1 (by rfl) ⟨1356668, by rfl⟩ : syracuseStep 1808891 = 2713337) B2713337
theorem B4069907 : Blo 1807605 4069907 := bstep (se 1 (by rfl) ⟨3052430, by rfl⟩ : syracuseStep 4069907 = 6104861) B6104861
theorem B6101567 : Blo 1807605 6101567 := bstep (se 1 (by rfl) ⟨4576175, by rfl⟩ : syracuseStep 6101567 = 9152351) B9152351
theorem B1808959 : Blo 1807605 1808959 := bstep (se 1 (by rfl) ⟨1356719, by rfl⟩ : syracuseStep 1808959 = 2713439) B2713439
theorem B1808967 : Blo 1807605 1808967 := bstep (se 1 (by rfl) ⟨1356725, by rfl⟩ : syracuseStep 1808967 = 2713451) B2713451
theorem B4069961 : Blo 1807605 4069961 := bstep (se 2 (by rfl) ⟨1526235, by rfl⟩ : syracuseStep 4069961 = 3052471) B3052471
theorem B3095147 : Blo 1807605 3095147 := bstep (se 1 (by rfl) ⟨2321360, by rfl⟩ : syracuseStep 3095147 = 4642721) B4642721
theorem B13040261 : Blo 1807605 13040261 := bstep (se 4 (by rfl) ⟨1222524, by rfl⟩ : syracuseStep 13040261 = 2445049) B2445049
theorem B20601539 : Blo 1807605 20601539 := bstep (se 1 (by rfl) ⟨15451154, by rfl⟩ : syracuseStep 20601539 = 30902309) B30902309
theorem B6961859 : Blo 1807605 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B1809119 : Blo 1807605 1809119 := bstep (se 1 (by rfl) ⟨1356839, by rfl⟩ : syracuseStep 1809119 = 2713679) B2713679
theorem B1809199 : Blo 1807605 1809199 := bstep (se 1 (by rfl) ⟨1356899, by rfl⟩ : syracuseStep 1809199 = 2713799) B2713799
theorem B4578191 : Blo 1807605 4578191 := bstep (se 1 (by rfl) ⟨3433643, by rfl⟩ : syracuseStep 4578191 = 6867287) B6867287
theorem B1809307 : Blo 1807605 1809307 := bstep (se 1 (by rfl) ⟨1356980, by rfl⟩ : syracuseStep 1809307 = 2713961) B2713961
theorem B1809359 : Blo 1807605 1809359 := bstep (se 1 (by rfl) ⟨1357019, by rfl⟩ : syracuseStep 1809359 = 2714039) B2714039
theorem B4070375 : Blo 1807605 4070375 := bstep (se 1 (by rfl) ⟨3052781, by rfl⟩ : syracuseStep 4070375 = 6105563) B6105563
theorem B1809383 : Blo 1807605 1809383 := bstep (se 1 (by rfl) ⟨1357037, by rfl⟩ : syracuseStep 1809383 = 2714075) B2714075
theorem B23166071 : Blo 1807605 23166071 := bstep (se 1 (by rfl) ⟨17374553, by rfl⟩ : syracuseStep 23166071 = 34749107) B34749107
theorem B10304779 : Blo 1807605 10304779 := bstep (se 1 (by rfl) ⟨7728584, by rfl⟩ : syracuseStep 10304779 = 15457169) B15457169
theorem B4070753 : Blo 1807605 4070753 := bstep (se 2 (by rfl) ⟨1526532, by rfl⟩ : syracuseStep 4070753 = 3053065) B3053065
theorem B4070843 : Blo 1807605 4070843 := bstep (se 1 (by rfl) ⟨3053132, by rfl⟩ : syracuseStep 4070843 = 6106265) B6106265
theorem B26066443 : Blo 1807605 26066443 := bstep (se 1 (by rfl) ⟨19549832, by rfl⟩ : syracuseStep 26066443 = 39099665) B39099665
theorem B4070969 : Blo 1807605 4070969 := bstep (se 2 (by rfl) ⟨1526613, by rfl⟩ : syracuseStep 4070969 = 3053227) B3053227
theorem B8691259 : Blo 1807605 8691259 := bstep (se 1 (by rfl) ⟨6518444, by rfl⟩ : syracuseStep 8691259 = 13036889) B13036889
theorem B4406867 : Blo 1807605 4406867 := bstep (se 1 (by rfl) ⟨3305150, by rfl⟩ : syracuseStep 4406867 = 6610301) B6610301
theorem B4579051 : Blo 1807605 4579051 := bstep (se 1 (by rfl) ⟨3434288, by rfl⟩ : syracuseStep 4579051 = 6868577) B6868577
theorem B3481391 : Blo 1807605 3481391 := bstep (se 1 (by rfl) ⟨2611043, by rfl⟩ : syracuseStep 3481391 = 5222087) B5222087
theorem B52133705 : Blo 1807605 52133705 := bstep (se 2 (by rfl) ⟨19550139, by rfl⟩ : syracuseStep 52133705 = 39100279) B39100279
theorem B39092057 : Blo 1807605 39092057 := bstep (se 2 (by rfl) ⟨14659521, by rfl⟩ : syracuseStep 39092057 = 29319043) B29319043
theorem B9158507 : Blo 1807605 9158507 := bstep (se 1 (by rfl) ⟨6868880, by rfl⟩ : syracuseStep 9158507 = 13737761) B13737761
theorem B7724929 : Blo 1807605 7724929 := bstep (se 2 (by rfl) ⟨2896848, by rfl⟩ : syracuseStep 7724929 = 5793697) B5793697
theorem B6103079 : Blo 1807605 6103079 := bstep (se 1 (by rfl) ⟨4577309, by rfl⟩ : syracuseStep 6103079 = 9154619) B9154619
theorem B5292071 : Blo 1807605 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B2711771 : Blo 1807605 2711771 := bstep (se 1 (by rfl) ⟨2033828, by rfl⟩ : syracuseStep 2711771 = 4067657) B4067657
theorem B2711783 : Blo 1807605 2711783 := bstep (se 1 (by rfl) ⟨2033837, by rfl⟩ : syracuseStep 2711783 = 4067675) B4067675
theorem B2711945 : Blo 1807605 2711945 := bstep (se 2 (by rfl) ⟨1016979, by rfl⟩ : syracuseStep 2711945 = 2033959) B2033959
theorem B2712041 : Blo 1807605 2712041 := bstep (se 2 (by rfl) ⟨1017015, by rfl⟩ : syracuseStep 2712041 = 2034031) B2034031
theorem B3432937 : Blo 1807605 3432937 := bstep (se 2 (by rfl) ⟨1287351, by rfl⟩ : syracuseStep 3432937 = 2574703) B2574703
theorem B2712167 : Blo 1807605 2712167 := bstep (se 1 (by rfl) ⟨2034125, by rfl⟩ : syracuseStep 2712167 = 4068251) B4068251
theorem B6103727 : Blo 1807605 6103727 := bstep (se 1 (by rfl) ⟨4577795, by rfl⟩ : syracuseStep 6103727 = 9155591) B9155591
theorem B2712299 : Blo 1807605 2712299 := bstep (se 1 (by rfl) ⟨2034224, by rfl⟩ : syracuseStep 2712299 = 4068449) B4068449
theorem B3433195 : Blo 1807605 3433195 := bstep (se 1 (by rfl) ⟨2574896, by rfl⟩ : syracuseStep 3433195 = 5149793) B5149793
theorem B2712329 : Blo 1807605 2712329 := bstep (se 2 (by rfl) ⟨1017123, by rfl⟩ : syracuseStep 2712329 = 2034247) B2034247
theorem B11592467 : Blo 1807605 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B2712431 : Blo 1807605 2712431 := bstep (se 1 (by rfl) ⟨2034323, by rfl⟩ : syracuseStep 2712431 = 4068647) B4068647
theorem B47006581 : Blo 1807605 47006581 := bstep (se 5 (by rfl) ⟨2203433, by rfl⟩ : syracuseStep 47006581 = 4406867) B4406867
theorem B24757159 : Blo 1807605 24757159 := bstep (se 1 (by rfl) ⟨18567869, by rfl⟩ : syracuseStep 24757159 = 37135739) B37135739
theorem B6104051 : Blo 1807605 6104051 := bstep (se 1 (by rfl) ⟨4578038, by rfl⟩ : syracuseStep 6104051 = 9156077) B9156077
theorem B2712683 : Blo 1807605 2712683 := bstep (se 1 (by rfl) ⟨2034512, by rfl⟩ : syracuseStep 2712683 = 4069025) B4069025
theorem B35702039 : Blo 1807605 35702039 := bstep (se 1 (by rfl) ⟨26776529, by rfl⟩ : syracuseStep 35702039 = 53553059) B53553059
theorem B2712923 : Blo 1807605 2712923 := bstep (se 1 (by rfl) ⟨2034692, by rfl⟩ : syracuseStep 2712923 = 4069385) B4069385
theorem B6104591 : Blo 1807605 6104591 := bstep (se 1 (by rfl) ⟨4578443, by rfl⟩ : syracuseStep 6104591 = 9156887) B9156887
theorem B23168531 : Blo 1807605 23168531 := bstep (se 1 (by rfl) ⟨17376398, by rfl⟩ : syracuseStep 23168531 = 34752797) B34752797
theorem B2713199 : Blo 1807605 2713199 := bstep (se 1 (by rfl) ⟨2034899, by rfl⟩ : syracuseStep 2713199 = 4069799) B4069799
theorem B7833199 : Blo 1807605 7833199 := bstep (se 1 (by rfl) ⟨5874899, by rfl⟩ : syracuseStep 7833199 = 11749799) B11749799
theorem B2713271 : Blo 1807605 2713271 := bstep (se 1 (by rfl) ⟨2034953, by rfl⟩ : syracuseStep 2713271 = 4069907) B4069907
theorem B13739705 : Blo 1807605 13739705 := bstep (se 2 (by rfl) ⟨5152389, by rfl⟩ : syracuseStep 13739705 = 10304779) B10304779
theorem B2713307 : Blo 1807605 2713307 := bstep (se 1 (by rfl) ⟨2034980, by rfl⟩ : syracuseStep 2713307 = 4069961) B4069961
theorem B8693507 : Blo 1807605 8693507 := bstep (se 1 (by rfl) ⟨6520130, by rfl⟩ : syracuseStep 8693507 = 13040261) B13040261
theorem B8046443 : Blo 1807605 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B2713481 : Blo 1807605 2713481 := bstep (se 2 (by rfl) ⟨1017555, by rfl⟩ : syracuseStep 2713481 = 2035111) B2035111
theorem B2713583 : Blo 1807605 2713583 := bstep (se 1 (by rfl) ⟨2035187, by rfl⟩ : syracuseStep 2713583 = 4070375) B4070375
theorem B15444047 : Blo 1807605 15444047 := bstep (se 1 (by rfl) ⟨11583035, by rfl⟩ : syracuseStep 15444047 = 23166071) B23166071
theorem B9283709 : Blo 1807605 9283709 := bstep (se 3 (by rfl) ⟨1740695, by rfl⟩ : syracuseStep 9283709 = 3481391) B3481391
theorem B4344043 : Blo 1807605 4344043 := bstep (se 1 (by rfl) ⟨3258032, by rfl⟩ : syracuseStep 4344043 = 6516065) B6516065
theorem B2713835 : Blo 1807605 2713835 := bstep (se 1 (by rfl) ⟨2035376, by rfl⟩ : syracuseStep 2713835 = 4070753) B4070753
theorem B2713895 : Blo 1807605 2713895 := bstep (se 1 (by rfl) ⟨2035421, by rfl⟩ : syracuseStep 2713895 = 4070843) B4070843
theorem B6105401 : Blo 1807605 6105401 := bstep (se 2 (by rfl) ⟨2289525, by rfl⟩ : syracuseStep 6105401 = 4579051) B4579051
theorem B2713979 : Blo 1807605 2713979 := bstep (se 1 (by rfl) ⟨2035484, by rfl⟩ : syracuseStep 2713979 = 4070969) B4070969
theorem B9775525 : Blo 1807605 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B10299905 : Blo 1807605 10299905 := bstep (se 2 (by rfl) ⟨3862464, by rfl⟩ : syracuseStep 10299905 = 7724929) B7724929
theorem B26061371 : Blo 1807605 26061371 := bstep (se 1 (by rfl) ⟨19546028, by rfl⟩ : syracuseStep 26061371 = 39092057) B39092057
theorem B6105671 : Blo 1807605 6105671 := bstep (se 1 (by rfl) ⟨4579253, by rfl⟩ : syracuseStep 6105671 = 9158507) B9158507
theorem B2714249 : Blo 1807605 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B3050399 : Blo 1807605 3050399 := bstep (se 1 (by rfl) ⟨2287799, by rfl⟩ : syracuseStep 3050399 = 4575599) B4575599
theorem B56421305 : Blo 1807605 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B13732901 : Blo 1807605 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B3050831 : Blo 1807605 3050831 := bstep (se 1 (by rfl) ⟨2288123, by rfl⟩ : syracuseStep 3050831 = 4576247) B4576247
theorem B4124087 : Blo 1807605 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B6106697 : Blo 1807605 6106697 := bstep (se 2 (by rfl) ⟨2290011, by rfl⟩ : syracuseStep 6106697 = 4580023) B4580023
theorem B2035291 : Blo 1807605 2035291 := bstep (se 1 (by rfl) ⟨1526468, by rfl⟩ : syracuseStep 2035291 = 3052937) B3052937
theorem B5148335 : Blo 1807605 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B2035579 : Blo 1807605 2035579 := bstep (se 1 (by rfl) ⟨1526684, by rfl⟩ : syracuseStep 2035579 = 3053369) B3053369
theorem B3305387 : Blo 1807605 3305387 := bstep (se 1 (by rfl) ⟨2479040, by rfl⟩ : syracuseStep 3305387 = 4958081) B4958081
theorem B8695775 : Blo 1807605 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B9285761 : Blo 1807605 9285761 := bstep (se 2 (by rfl) ⟨3482160, by rfl⟩ : syracuseStep 9285761 = 6964321) B6964321
theorem B5148859 : Blo 1807605 5148859 := bstep (se 1 (by rfl) ⟨3861644, by rfl⟩ : syracuseStep 5148859 = 7723289) B7723289
theorem B3666107 : Blo 1807605 3666107 := bstep (se 1 (by rfl) ⟨2749580, by rfl⟩ : syracuseStep 3666107 = 5499161) B5499161
theorem B5796029 : Blo 1807605 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B11587805 : Blo 1807605 11587805 := bstep (se 3 (by rfl) ⟨2172713, by rfl⟩ : syracuseStep 11587805 = 4345427) B4345427
theorem B6869245 : Blo 1807605 6869245 := bstep (se 3 (by rfl) ⟨1287983, by rfl⟩ : syracuseStep 6869245 = 2575967) B2575967
theorem B4067639 : Blo 1807605 4067639 := bstep (se 1 (by rfl) ⟨3050729, by rfl⟩ : syracuseStep 4067639 = 6101459) B6101459
theorem B4067711 : Blo 1807605 4067711 := bstep (se 1 (by rfl) ⟨3050783, by rfl⟩ : syracuseStep 4067711 = 6101567) B6101567
theorem B10301863 : Blo 1807605 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B26071469 : Blo 1807605 26071469 := bstep (se 3 (by rfl) ⟨4888400, by rfl⟩ : syracuseStep 26071469 = 9776801) B9776801
theorem B13734359 : Blo 1807605 13734359 := bstep (se 1 (by rfl) ⟨10300769, by rfl⟩ : syracuseStep 13734359 = 20601539) B20601539
theorem B4641239 : Blo 1807605 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B158568941 : Blo 1807605 158568941 := bstep (se 3 (by rfl) ⟨29731676, by rfl⟩ : syracuseStep 158568941 = 59463353) B59463353
theorem B3863123 : Blo 1807605 3863123 := bstep (se 1 (by rfl) ⟨2897342, by rfl⟩ : syracuseStep 3863123 = 5794685) B5794685
theorem B3052127 : Blo 1807605 3052127 := bstep (se 1 (by rfl) ⟨2289095, by rfl⟩ : syracuseStep 3052127 = 4578191) B4578191
theorem B46346903 : Blo 1807605 46346903 := bstep (se 1 (by rfl) ⟨34760177, by rfl⟩ : syracuseStep 46346903 = 69520355) B69520355
theorem B34755257 : Blo 1807605 34755257 := bstep (se 2 (by rfl) ⟨13033221, by rfl⟩ : syracuseStep 34755257 = 26066443) B26066443
theorem B11588345 : Blo 1807605 11588345 := bstep (se 2 (by rfl) ⟨4345629, by rfl⟩ : syracuseStep 11588345 = 8691259) B8691259
theorem B4952873 : Blo 1807605 4952873 := bstep (se 2 (by rfl) ⟨1857327, by rfl⟩ : syracuseStep 4952873 = 3714655) B3714655
theorem B6271805 : Blo 1807605 6271805 := bstep (se 3 (by rfl) ⟨1175963, by rfl⟩ : syracuseStep 6271805 = 2351927) B2351927
theorem B5149565 : Blo 1807605 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B5797003 : Blo 1807605 5797003 := bstep (se 1 (by rfl) ⟨4347752, by rfl⟩ : syracuseStep 5797003 = 8695505) B8695505
theorem B34755803 : Blo 1807605 34755803 := bstep (se 1 (by rfl) ⟨26066852, by rfl⟩ : syracuseStep 34755803 = 52133705) B52133705
theorem B1807771 : Blo 1807605 1807771 := bstep (se 1 (by rfl) ⟨1355828, by rfl⟩ : syracuseStep 1807771 = 2711657) B2711657
theorem B4068935 : Blo 1807605 4068935 := bstep (se 1 (by rfl) ⟨3051701, by rfl⟩ : syracuseStep 4068935 = 6103403) B6103403
theorem B1807983 : Blo 1807605 1807983 := bstep (se 1 (by rfl) ⟨1355987, by rfl⟩ : syracuseStep 1807983 = 2711975) B2711975
theorem B1808039 : Blo 1807605 1808039 := bstep (se 1 (by rfl) ⟨1356029, by rfl⟩ : syracuseStep 1808039 = 2712059) B2712059
theorem B31307447 : Blo 1807605 31307447 := bstep (se 1 (by rfl) ⟨23480585, by rfl⟩ : syracuseStep 31307447 = 46961171) B46961171
theorem B9778897 : Blo 1807605 9778897 := bstep (se 2 (by rfl) ⟨3667086, by rfl⟩ : syracuseStep 9778897 = 7334173) B7334173
theorem B1808123 : Blo 1807605 1808123 := bstep (se 1 (by rfl) ⟨1356092, by rfl⟩ : syracuseStep 1808123 = 2712185) B2712185
theorem B4069115 : Blo 1807605 4069115 := bstep (se 1 (by rfl) ⟨3051836, by rfl⟩ : syracuseStep 4069115 = 6103673) B6103673
theorem B1808159 : Blo 1807605 1808159 := bstep (se 1 (by rfl) ⟨1356119, by rfl⟩ : syracuseStep 1808159 = 2712239) B2712239
theorem B1808191 : Blo 1807605 1808191 := bstep (se 1 (by rfl) ⟨1356143, by rfl⟩ : syracuseStep 1808191 = 2712287) B2712287
theorem B4577087 : Blo 1807605 4577087 := bstep (se 1 (by rfl) ⟨3432815, by rfl⟩ : syracuseStep 4577087 = 6865631) B6865631
theorem B3258191 : Blo 1807605 3258191 := bstep (se 1 (by rfl) ⟨2443643, by rfl⟩ : syracuseStep 3258191 = 4887287) B4887287
theorem B13916087 : Blo 1807605 13916087 := bstep (se 1 (by rfl) ⟨10437065, by rfl⟩ : syracuseStep 13916087 = 20874131) B20874131
theorem B1808367 : Blo 1807605 1808367 := bstep (se 1 (by rfl) ⟨1356275, by rfl⟩ : syracuseStep 1808367 = 2712551) B2712551
theorem B3053551 : Blo 1807605 3053551 := bstep (se 1 (by rfl) ⟨2290163, by rfl⟩ : syracuseStep 3053551 = 4580327) B4580327
theorem B6101135 : Blo 1807605 6101135 := bstep (se 1 (by rfl) ⟨4575851, by rfl⟩ : syracuseStep 6101135 = 9151703) B9151703
theorem B1808539 : Blo 1807605 1808539 := bstep (se 1 (by rfl) ⟨1356404, by rfl⟩ : syracuseStep 1808539 = 2712809) B2712809
theorem B1808575 : Blo 1807605 1808575 := bstep (se 1 (by rfl) ⟨1356431, by rfl⟩ : syracuseStep 1808575 = 2712863) B2712863
theorem B2611435 : Blo 1807605 2611435 := bstep (se 1 (by rfl) ⟨1958576, by rfl⟩ : syracuseStep 2611435 = 3917153) B3917153
theorem B4577543 : Blo 1807605 4577543 := bstep (se 1 (by rfl) ⟨3433157, by rfl⟩ : syracuseStep 4577543 = 6866315) B6866315
theorem B3864839 : Blo 1807605 3864839 := bstep (se 1 (by rfl) ⟨2898629, by rfl⟩ : syracuseStep 3864839 = 5797259) B5797259
theorem B4069673 : Blo 1807605 4069673 := bstep (se 2 (by rfl) ⟨1526127, by rfl⟩ : syracuseStep 4069673 = 3052255) B3052255
theorem B1808687 : Blo 1807605 1808687 := bstep (se 1 (by rfl) ⟨1356515, by rfl⟩ : syracuseStep 1808687 = 2713031) B2713031
theorem B11581805 : Blo 1807605 11581805 := bstep (se 3 (by rfl) ⟨2171588, by rfl⟩ : syracuseStep 11581805 = 4343177) B4343177
theorem B5151251 : Blo 1807605 5151251 := bstep (se 1 (by rfl) ⟨3863438, by rfl⟩ : syracuseStep 5151251 = 7726877) B7726877
theorem B1808923 : Blo 1807605 1808923 := bstep (se 1 (by rfl) ⟨1356692, by rfl⟩ : syracuseStep 1808923 = 2713385) B2713385
theorem B1808927 : Blo 1807605 1808927 := bstep (se 1 (by rfl) ⟨1356695, by rfl⟩ : syracuseStep 1808927 = 2713391) B2713391
theorem B23485049 : Blo 1807605 23485049 := bstep (se 2 (by rfl) ⟨8806893, by rfl⟩ : syracuseStep 23485049 = 17613787) B17613787
theorem B10304279 : Blo 1807605 10304279 := bstep (se 1 (by rfl) ⟨7728209, by rfl⟩ : syracuseStep 10304279 = 15456419) B15456419
theorem B1809243 : Blo 1807605 1809243 := bstep (se 1 (by rfl) ⟨1356932, by rfl⟩ : syracuseStep 1809243 = 2713865) B2713865
theorem B4070249 : Blo 1807605 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B5151593 : Blo 1807605 5151593 := bstep (se 2 (by rfl) ⟨1931847, by rfl⟩ : syracuseStep 5151593 = 3863695) B3863695
theorem B4070303 : Blo 1807605 4070303 := bstep (se 1 (by rfl) ⟨3052727, by rfl⟩ : syracuseStep 4070303 = 6105455) B6105455
theorem B1809311 : Blo 1807605 1809311 := bstep (se 1 (by rfl) ⟨1356983, by rfl⟩ : syracuseStep 1809311 = 2713967) B2713967
theorem B169335755 : Blo 1807605 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B1809455 : Blo 1807605 1809455 := bstep (se 1 (by rfl) ⟨1357091, by rfl⟩ : syracuseStep 1809455 = 2714183) B2714183
theorem B2063431 : Blo 1807605 2063431 := bstep (se 1 (by rfl) ⟨1547573, by rfl⟩ : syracuseStep 2063431 = 3095147) B3095147
theorem B1809479 : Blo 1807605 1809479 := bstep (se 1 (by rfl) ⟨1357109, by rfl⟩ : syracuseStep 1809479 = 2714219) B2714219
theorem B6102269 : Blo 1807605 6102269 := bstep (se 3 (by rfl) ⟨1144175, by rfl⟩ : syracuseStep 6102269 = 2288351) B2288351
theorem B4578727 : Blo 1807605 4578727 := bstep (se 1 (by rfl) ⟨3434045, by rfl⟩ : syracuseStep 4578727 = 6868091) B6868091
theorem B3481231 : Blo 1807605 3481231 := bstep (se 1 (by rfl) ⟨2610923, by rfl⟩ : syracuseStep 3481231 = 5221847) B5221847
theorem B5152481 : Blo 1807605 5152481 := bstep (se 2 (by rfl) ⟨1932180, by rfl⟩ : syracuseStep 5152481 = 3864361) B3864361
theorem B11591495 : Blo 1807605 11591495 := bstep (se 1 (by rfl) ⟨8693621, by rfl⟩ : syracuseStep 11591495 = 17387243) B17387243
theorem B4071239 : Blo 1807605 4071239 := bstep (se 1 (by rfl) ⟨3053429, by rfl⟩ : syracuseStep 4071239 = 6106859) B6106859
theorem B17391469 : Blo 1807605 17391469 := bstep (se 3 (by rfl) ⟨3260900, by rfl⟩ : syracuseStep 17391469 = 6521801) B6521801
theorem B2711417 : Blo 1807605 2711417 := bstep (se 2 (by rfl) ⟨1016781, by rfl⟩ : syracuseStep 2711417 = 2033563) B2033563
theorem B2711519 : Blo 1807605 2711519 := bstep (se 1 (by rfl) ⟨2033639, by rfl⟩ : syracuseStep 2711519 = 4067279) B4067279
theorem B7725203 : Blo 1807605 7725203 := bstep (se 1 (by rfl) ⟨5793902, by rfl⟩ : syracuseStep 7725203 = 11587805) B11587805
theorem B2711759 : Blo 1807605 2711759 := bstep (se 1 (by rfl) ⟨2033819, by rfl⟩ : syracuseStep 2711759 = 4067639) B4067639
theorem B6865145 : Blo 1807605 6865145 := bstep (se 2 (by rfl) ⟨2574429, by rfl⟩ : syracuseStep 6865145 = 5148859) B5148859
theorem B2711807 : Blo 1807605 2711807 := bstep (se 1 (by rfl) ⟨2033855, by rfl⟩ : syracuseStep 2711807 = 4067711) B4067711
theorem B5792057 : Blo 1807605 5792057 := bstep (se 2 (by rfl) ⟨2172021, by rfl⟩ : syracuseStep 5792057 = 4344043) B4344043
theorem B9158993 : Blo 1807605 9158993 := bstep (se 2 (by rfl) ⟨3434622, by rfl⟩ : syracuseStep 9158993 = 6869245) B6869245
theorem B7725563 : Blo 1807605 7725563 := bstep (se 1 (by rfl) ⟨5794172, by rfl⟩ : syracuseStep 7725563 = 11588345) B11588345
theorem B3301915 : Blo 1807605 3301915 := bstep (se 1 (by rfl) ⟨2476436, by rfl⟩ : syracuseStep 3301915 = 4952873) B4952873
theorem B13034033 : Blo 1807605 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B3433043 : Blo 1807605 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B10306237 : Blo 1807605 10306237 := bstep (se 3 (by rfl) ⟨1932419, by rfl⟩ : syracuseStep 10306237 = 3864839) B3864839
theorem B30884813 : Blo 1807605 30884813 := bstep (se 3 (by rfl) ⟨5790902, by rfl⟩ : syracuseStep 30884813 = 11581805) B11581805
theorem B2712623 : Blo 1807605 2712623 := bstep (se 1 (by rfl) ⟨2034467, by rfl⟩ : syracuseStep 2712623 = 4068935) B4068935
theorem B9159803 : Blo 1807605 9159803 := bstep (se 1 (by rfl) ⟨6869852, by rfl⟩ : syracuseStep 9159803 = 13739705) B13739705
theorem B2712743 : Blo 1807605 2712743 := bstep (se 1 (by rfl) ⟨2034557, by rfl⟩ : syracuseStep 2712743 = 4069115) B4069115
theorem B2172127 : Blo 1807605 2172127 := bstep (se 1 (by rfl) ⟨1629095, by rfl⟩ : syracuseStep 2172127 = 3258191) B3258191
theorem B2713115 : Blo 1807605 2713115 := bstep (se 1 (by rfl) ⟨2034836, by rfl⟩ : syracuseStep 2713115 = 4069673) B4069673
theorem B6866603 : Blo 1807605 6866603 := bstep (se 1 (by rfl) ⟨5149952, by rfl⟩ : syracuseStep 6866603 = 10299905) B10299905
theorem B3434167 : Blo 1807605 3434167 := bstep (se 1 (by rfl) ⟨2575625, by rfl⟩ : syracuseStep 3434167 = 5151251) B5151251
theorem B15656699 : Blo 1807605 15656699 := bstep (se 1 (by rfl) ⟨11742524, by rfl⟩ : syracuseStep 15656699 = 23485049) B23485049
theorem B6104969 : Blo 1807605 6104969 := bstep (se 2 (by rfl) ⟨2289363, by rfl⟩ : syracuseStep 6104969 = 4578727) B4578727
theorem B2713499 : Blo 1807605 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B3434395 : Blo 1807605 3434395 := bstep (se 1 (by rfl) ⟨2575796, by rfl⟩ : syracuseStep 3434395 = 5151593) B5151593
theorem B2033599 : Blo 1807605 2033599 := bstep (se 1 (by rfl) ⟨1525199, by rfl⟩ : syracuseStep 2033599 = 3050399) B3050399
theorem B2713535 : Blo 1807605 2713535 := bstep (se 1 (by rfl) ⟨2035151, by rfl⟩ : syracuseStep 2713535 = 4070303) B4070303
theorem B2713721 : Blo 1807605 2713721 := bstep (se 2 (by rfl) ⟨1017645, by rfl⟩ : syracuseStep 2713721 = 2035291) B2035291
theorem B2033887 : Blo 1807605 2033887 := bstep (se 1 (by rfl) ⟨1525415, by rfl⟩ : syracuseStep 2033887 = 3050831) B3050831
theorem B21457181 : Blo 1807605 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B3434987 : Blo 1807605 3434987 := bstep (se 1 (by rfl) ⟨2576240, by rfl⟩ : syracuseStep 3434987 = 5152481) B5152481
theorem B2714105 : Blo 1807605 2714105 := bstep (se 2 (by rfl) ⟨1017789, by rfl⟩ : syracuseStep 2714105 = 2035579) B2035579
theorem B7727663 : Blo 1807605 7727663 := bstep (se 1 (by rfl) ⟨5795747, by rfl⟩ : syracuseStep 7727663 = 11591495) B11591495
theorem B2714159 : Blo 1807605 2714159 := bstep (se 1 (by rfl) ⟨2035619, by rfl⟩ : syracuseStep 2714159 = 4071239) B4071239
theorem B105712627 : Blo 1807605 105712627 := bstep (se 1 (by rfl) ⟨79284470, by rfl⟩ : syracuseStep 105712627 = 158568941) B158568941
theorem B2575415 : Blo 1807605 2575415 := bstep (se 1 (by rfl) ⟨1931561, by rfl⟩ : syracuseStep 2575415 = 3863123) B3863123
theorem B2034751 : Blo 1807605 2034751 := bstep (se 1 (by rfl) ⟨1526063, by rfl⟩ : syracuseStep 2034751 = 3052127) B3052127
theorem B23170171 : Blo 1807605 23170171 := bstep (se 1 (by rfl) ⟨17377628, by rfl⟩ : syracuseStep 23170171 = 34755257) B34755257
theorem B9776285 : Blo 1807605 9776285 := bstep (se 3 (by rfl) ⟨1833053, by rfl⟩ : syracuseStep 9776285 = 3666107) B3666107
theorem B7728311 : Blo 1807605 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B4181203 : Blo 1807605 4181203 := bstep (se 1 (by rfl) ⟨3135902, by rfl⟩ : syracuseStep 4181203 = 6271805) B6271805
theorem B23170535 : Blo 1807605 23170535 := bstep (se 1 (by rfl) ⟨17377901, by rfl⟩ : syracuseStep 23170535 = 34755803) B34755803
theorem B23801359 : Blo 1807605 23801359 := bstep (se 1 (by rfl) ⟨17851019, by rfl⟩ : syracuseStep 23801359 = 35702039) B35702039
theorem B15445687 : Blo 1807605 15445687 := bstep (se 1 (by rfl) ⟨11584265, by rfl⟩ : syracuseStep 15445687 = 23168531) B23168531
theorem B5795671 : Blo 1807605 5795671 := bstep (se 1 (by rfl) ⟨4346753, by rfl⟩ : syracuseStep 5795671 = 8693507) B8693507
theorem B3051391 : Blo 1807605 3051391 := bstep (se 1 (by rfl) ⟨2288543, by rfl⟩ : syracuseStep 3051391 = 4577087) B4577087
theorem B33009545 : Blo 1807605 33009545 := bstep (se 2 (by rfl) ⟨12378579, by rfl⟩ : syracuseStep 33009545 = 24757159) B24757159
theorem B9277391 : Blo 1807605 9277391 := bstep (se 1 (by rfl) ⟨6958043, by rfl⟩ : syracuseStep 9277391 = 13916087) B13916087
theorem B6189139 : Blo 1807605 6189139 := bstep (se 1 (by rfl) ⟨4641854, by rfl⟩ : syracuseStep 6189139 = 9283709) B9283709
theorem B4067423 : Blo 1807605 4067423 := bstep (se 1 (by rfl) ⟨3050567, by rfl⟩ : syracuseStep 4067423 = 6101135) B6101135
theorem B3051695 : Blo 1807605 3051695 := bstep (se 1 (by rfl) ⟨2288771, by rfl⟩ : syracuseStep 3051695 = 4577543) B4577543
theorem B7729337 : Blo 1807605 7729337 := bstep (se 2 (by rfl) ⟨2898501, by rfl⟩ : syracuseStep 7729337 = 5797003) B5797003
theorem B6869519 : Blo 1807605 6869519 := bstep (se 1 (by rfl) ⟨5152139, by rfl⟩ : syracuseStep 6869519 = 10304279) B10304279
theorem B37614203 : Blo 1807605 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B112890503 : Blo 1807605 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B9155267 : Blo 1807605 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B4068179 : Blo 1807605 4068179 := bstep (se 1 (by rfl) ⟨3051134, by rfl⟩ : syracuseStep 4068179 = 6102269) B6102269
theorem B4641641 : Blo 1807605 4641641 := bstep (se 2 (by rfl) ⟨1740615, by rfl⟩ : syracuseStep 4641641 = 3481231) B3481231
theorem B55710613 : Blo 1807605 55710613 := bstep (se 6 (by rfl) ⟨1305717, by rfl⟩ : syracuseStep 55710613 = 2611435) B2611435
theorem B13038529 : Blo 1807605 13038529 := bstep (se 2 (by rfl) ⟨4889448, by rfl⟩ : syracuseStep 13038529 = 9778897) B9778897
theorem B2749391 : Blo 1807605 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B23188625 : Blo 1807605 23188625 := bstep (se 2 (by rfl) ⟨8695734, by rfl⟩ : syracuseStep 23188625 = 17391469) B17391469
theorem B1807611 : Blo 1807605 1807611 := bstep (se 1 (by rfl) ⟨1355708, by rfl⟩ : syracuseStep 1807611 = 2711417) B2711417
theorem B1807679 : Blo 1807605 1807679 := bstep (se 1 (by rfl) ⟨1355759, by rfl⟩ : syracuseStep 1807679 = 2711519) B2711519
theorem B5797183 : Blo 1807605 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B4068719 : Blo 1807605 4068719 := bstep (se 1 (by rfl) ⟨3051539, by rfl⟩ : syracuseStep 4068719 = 6103079) B6103079
theorem B3528047 : Blo 1807605 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B6190507 : Blo 1807605 6190507 := bstep (se 1 (by rfl) ⟨4642880, by rfl⟩ : syracuseStep 6190507 = 9285761) B9285761
theorem B3864019 : Blo 1807605 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B1807847 : Blo 1807605 1807847 := bstep (se 1 (by rfl) ⟨1355885, by rfl⟩ : syracuseStep 1807847 = 2711771) B2711771
theorem B1807855 : Blo 1807605 1807855 := bstep (se 1 (by rfl) ⟨1355891, by rfl⟩ : syracuseStep 1807855 = 2711783) B2711783
theorem B1807963 : Blo 1807605 1807963 := bstep (se 1 (by rfl) ⟨1355972, by rfl⟩ : syracuseStep 1807963 = 2711945) B2711945
theorem B17380979 : Blo 1807605 17380979 := bstep (se 1 (by rfl) ⟨13035734, by rfl⟩ : syracuseStep 17380979 = 26071469) B26071469
theorem B9156239 : Blo 1807605 9156239 := bstep (se 1 (by rfl) ⟨6867179, by rfl⟩ : syracuseStep 9156239 = 13734359) B13734359
theorem B1808027 : Blo 1807605 1808027 := bstep (se 1 (by rfl) ⟨1356020, by rfl⟩ : syracuseStep 1808027 = 2712041) B2712041
theorem B1808111 : Blo 1807605 1808111 := bstep (se 1 (by rfl) ⟨1356083, by rfl⟩ : syracuseStep 1808111 = 2712167) B2712167
theorem B30897935 : Blo 1807605 30897935 := bstep (se 1 (by rfl) ⟨23173451, by rfl⟩ : syracuseStep 30897935 = 46346903) B46346903
theorem B4069151 : Blo 1807605 4069151 := bstep (se 1 (by rfl) ⟨3051863, by rfl⟩ : syracuseStep 4069151 = 6103727) B6103727
theorem B1808199 : Blo 1807605 1808199 := bstep (se 1 (by rfl) ⟨1356149, by rfl⟩ : syracuseStep 1808199 = 2712299) B2712299
theorem B1808219 : Blo 1807605 1808219 := bstep (se 1 (by rfl) ⟨1356164, by rfl⟩ : syracuseStep 1808219 = 2712329) B2712329
theorem B13735817 : Blo 1807605 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B1808287 : Blo 1807605 1808287 := bstep (se 1 (by rfl) ⟨1356215, by rfl⟩ : syracuseStep 1808287 = 2712431) B2712431
theorem B4577249 : Blo 1807605 4577249 := bstep (se 2 (by rfl) ⟨1716468, by rfl⟩ : syracuseStep 4577249 = 3432937) B3432937
theorem B4069367 : Blo 1807605 4069367 := bstep (se 1 (by rfl) ⟨3052025, by rfl⟩ : syracuseStep 4069367 = 6104051) B6104051
theorem B1808455 : Blo 1807605 1808455 := bstep (se 1 (by rfl) ⟨1356341, by rfl⟩ : syracuseStep 1808455 = 2712683) B2712683
theorem B1808615 : Blo 1807605 1808615 := bstep (se 1 (by rfl) ⟨1356461, by rfl⟩ : syracuseStep 1808615 = 2712923) B2712923
theorem B4577593 : Blo 1807605 4577593 := bstep (se 2 (by rfl) ⟨1716597, by rfl⟩ : syracuseStep 4577593 = 3433195) B3433195
theorem B4069727 : Blo 1807605 4069727 := bstep (se 1 (by rfl) ⟨3052295, by rfl⟩ : syracuseStep 4069727 = 6104591) B6104591
theorem B1808799 : Blo 1807605 1808799 := bstep (se 1 (by rfl) ⟨1356599, by rfl⟩ : syracuseStep 1808799 = 2713199) B2713199
theorem B20871631 : Blo 1807605 20871631 := bstep (se 1 (by rfl) ⟨15653723, by rfl⟩ : syracuseStep 20871631 = 31307447) B31307447
theorem B1808847 : Blo 1807605 1808847 := bstep (se 1 (by rfl) ⟨1356635, by rfl⟩ : syracuseStep 1808847 = 2713271) B2713271
theorem B1808871 : Blo 1807605 1808871 := bstep (se 1 (by rfl) ⟨1356653, by rfl⟩ : syracuseStep 1808871 = 2713307) B2713307
theorem B62675441 : Blo 1807605 62675441 := bstep (se 2 (by rfl) ⟨23503290, by rfl⟩ : syracuseStep 62675441 = 47006581) B47006581
theorem B12376637 : Blo 1807605 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B1808987 : Blo 1807605 1808987 := bstep (se 1 (by rfl) ⟨1356740, by rfl⟩ : syracuseStep 1808987 = 2713481) B2713481
theorem B1809055 : Blo 1807605 1809055 := bstep (se 1 (by rfl) ⟨1356791, by rfl⟩ : syracuseStep 1809055 = 2713583) B2713583
theorem B10296031 : Blo 1807605 10296031 := bstep (se 1 (by rfl) ⟨7722023, by rfl⟩ : syracuseStep 10296031 = 15444047) B15444047
theorem B2751241 : Blo 1807605 2751241 := bstep (se 2 (by rfl) ⟨1031715, by rfl⟩ : syracuseStep 2751241 = 2063431) B2063431
theorem B1809223 : Blo 1807605 1809223 := bstep (se 1 (by rfl) ⟨1356917, by rfl⟩ : syracuseStep 1809223 = 2713835) B2713835
theorem B1809263 : Blo 1807605 1809263 := bstep (se 1 (by rfl) ⟨1356947, by rfl⟩ : syracuseStep 1809263 = 2713895) B2713895
theorem B4070267 : Blo 1807605 4070267 := bstep (se 1 (by rfl) ⟨3052700, by rfl⟩ : syracuseStep 4070267 = 6105401) B6105401
theorem B1809319 : Blo 1807605 1809319 := bstep (se 1 (by rfl) ⟨1356989, by rfl⟩ : syracuseStep 1809319 = 2713979) B2713979
theorem B17374247 : Blo 1807605 17374247 := bstep (se 1 (by rfl) ⟨13030685, by rfl⟩ : syracuseStep 17374247 = 26061371) B26061371
theorem B4070447 : Blo 1807605 4070447 := bstep (se 1 (by rfl) ⟨3052835, by rfl⟩ : syracuseStep 4070447 = 6105671) B6105671
theorem B1809499 : Blo 1807605 1809499 := bstep (se 1 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 1809499 = 2714249) B2714249
theorem B10444265 : Blo 1807605 10444265 := bstep (se 2 (by rfl) ⟨3916599, by rfl⟩ : syracuseStep 10444265 = 7833199) B7833199
theorem B4071131 : Blo 1807605 4071131 := bstep (se 1 (by rfl) ⟨3053348, by rfl⟩ : syracuseStep 4071131 = 6106697) B6106697
theorem B3432223 : Blo 1807605 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B2203591 : Blo 1807605 2203591 := bstep (se 1 (by rfl) ⟨1652693, by rfl⟩ : syracuseStep 2203591 = 3305387) B3305387
theorem B4071401 : Blo 1807605 4071401 := bstep (se 2 (by rfl) ⟨1526775, by rfl⟩ : syracuseStep 4071401 = 3053551) B3053551
theorem B2711615 : Blo 1807605 2711615 := bstep (se 1 (by rfl) ⟨2033711, by rfl⟩ : syracuseStep 2711615 = 4067423) B4067423
theorem B5152891 : Blo 1807605 5152891 := bstep (se 1 (by rfl) ⟨3864668, by rfl⟩ : syracuseStep 5152891 = 7729337) B7729337
theorem B2711849 : Blo 1807605 2711849 := bstep (se 2 (by rfl) ⟨1016943, by rfl⟩ : syracuseStep 2711849 = 2033887) B2033887
theorem B4579679 : Blo 1807605 4579679 := bstep (se 1 (by rfl) ⟨3434759, by rfl⟩ : syracuseStep 4579679 = 6869519) B6869519
theorem B6103457 : Blo 1807605 6103457 := bstep (se 2 (by rfl) ⟨2288796, by rfl⟩ : syracuseStep 6103457 = 4577593) B4577593
theorem B25076135 : Blo 1807605 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B75260335 : Blo 1807605 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B6103511 : Blo 1807605 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B2712119 : Blo 1807605 2712119 := bstep (se 1 (by rfl) ⟨2034089, by rfl⟩ : syracuseStep 2712119 = 4068179) B4068179
theorem B27828841 : Blo 1807605 27828841 := bstep (se 2 (by rfl) ⟨10435815, by rfl⟩ : syracuseStep 27828841 = 20871631) B20871631
theorem B15459083 : Blo 1807605 15459083 := bstep (se 1 (by rfl) ⟨11594312, by rfl⟩ : syracuseStep 15459083 = 23188625) B23188625
theorem B2712479 : Blo 1807605 2712479 := bstep (se 1 (by rfl) ⟨2034359, by rfl⟩ : syracuseStep 2712479 = 4068719) B4068719
theorem B6104159 : Blo 1807605 6104159 := bstep (se 1 (by rfl) ⟨4578119, by rfl⟩ : syracuseStep 6104159 = 9156239) B9156239
theorem B22299749 : Blo 1807605 22299749 := bstep (se 4 (by rfl) ⟨2090601, by rfl⟩ : syracuseStep 22299749 = 4181203) B4181203
theorem B2712767 : Blo 1807605 2712767 := bstep (se 1 (by rfl) ⟨2034575, by rfl⟩ : syracuseStep 2712767 = 4069151) B4069151
theorem B17384705 : Blo 1807605 17384705 := bstep (se 2 (by rfl) ⟨6519264, by rfl⟩ : syracuseStep 17384705 = 13038529) B13038529
theorem B9159965 : Blo 1807605 9159965 := bstep (se 3 (by rfl) ⟨1717493, by rfl⟩ : syracuseStep 9159965 = 3434987) B3434987
theorem B2712911 : Blo 1807605 2712911 := bstep (se 1 (by rfl) ⟨2034683, by rfl⟩ : syracuseStep 2712911 = 4069367) B4069367
theorem B2713001 : Blo 1807605 2713001 := bstep (se 2 (by rfl) ⟨1017375, by rfl⟩ : syracuseStep 2713001 = 2034751) B2034751
theorem B30893561 : Blo 1807605 30893561 := bstep (se 2 (by rfl) ⟨11585085, by rfl⟩ : syracuseStep 30893561 = 23170171) B23170171
theorem B2713151 : Blo 1807605 2713151 := bstep (se 1 (by rfl) ⟨2034863, by rfl⟩ : syracuseStep 2713151 = 4069727) B4069727
theorem B8251091 : Blo 1807605 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B2713511 : Blo 1807605 2713511 := bstep (se 1 (by rfl) ⟨2035133, by rfl⟩ : syracuseStep 2713511 = 4070267) B4070267
theorem B2713631 : Blo 1807605 2713631 := bstep (se 1 (by rfl) ⟨2035223, by rfl⟩ : syracuseStep 2713631 = 4070447) B4070447
theorem B88025453 : Blo 1807605 88025453 := bstep (se 3 (by rfl) ⟨16504772, by rfl⟩ : syracuseStep 88025453 = 33009545) B33009545
theorem B7727561 : Blo 1807605 7727561 := bstep (se 2 (by rfl) ⟨2897835, by rfl⟩ : syracuseStep 7727561 = 5795671) B5795671
theorem B2714087 : Blo 1807605 2714087 := bstep (se 1 (by rfl) ⟨2035565, by rfl⟩ : syracuseStep 2714087 = 4071131) B4071131
theorem B2714267 : Blo 1807605 2714267 := bstep (se 1 (by rfl) ⟨2035700, by rfl⟩ : syracuseStep 2714267 = 4071401) B4071401
theorem B2034463 : Blo 1807605 2034463 := bstep (se 1 (by rfl) ⟨1525847, by rfl⟩ : syracuseStep 2034463 = 3051695) B3051695
theorem B6867773 : Blo 1807605 6867773 := bstep (se 3 (by rfl) ⟨1287707, by rfl⟩ : syracuseStep 6867773 = 2575415) B2575415
theorem B3861371 : Blo 1807605 3861371 := bstep (se 1 (by rfl) ⟨2896028, by rfl⟩ : syracuseStep 3861371 = 5792057) B5792057
theorem B6105995 : Blo 1807605 6105995 := bstep (se 1 (by rfl) ⟨4579496, by rfl⟩ : syracuseStep 6105995 = 9158993) B9158993
theorem B33008741 : Blo 1807605 33008741 := bstep (se 4 (by rfl) ⟨3094569, by rfl⟩ : syracuseStep 33008741 = 6189139) B6189139
theorem B20589875 : Blo 1807605 20589875 := bstep (se 1 (by rfl) ⟨15442406, by rfl⟩ : syracuseStep 20589875 = 30884813) B30884813
theorem B4402553 : Blo 1807605 4402553 := bstep (se 2 (by rfl) ⟨1650957, by rfl⟩ : syracuseStep 4402553 = 3301915) B3301915
theorem B6106535 : Blo 1807605 6106535 := bstep (se 1 (by rfl) ⟨4579901, by rfl⟩ : syracuseStep 6106535 = 9159803) B9159803
theorem B13741649 : Blo 1807605 13741649 := bstep (se 2 (by rfl) ⟨5153118, by rfl⟩ : syracuseStep 13741649 = 10306237) B10306237
theorem B9408125 : Blo 1807605 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B11587319 : Blo 1807605 11587319 := bstep (se 1 (by rfl) ⟨8690489, by rfl⟩ : syracuseStep 11587319 = 17380979) B17380979
theorem B20598623 : Blo 1807605 20598623 := bstep (se 1 (by rfl) ⟨15448967, by rfl⟩ : syracuseStep 20598623 = 30897935) B30897935
theorem B74280817 : Blo 1807605 74280817 := bstep (se 2 (by rfl) ⟨27855306, by rfl⟩ : syracuseStep 74280817 = 55710613) B55710613
theorem B3051499 : Blo 1807605 3051499 := bstep (se 1 (by rfl) ⟨2288624, by rfl⟩ : syracuseStep 3051499 = 4577249) B4577249
theorem B9154781 : Blo 1807605 9154781 := bstep (se 3 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 9154781 = 3433043) B3433043
theorem B2896169 : Blo 1807605 2896169 := bstep (se 2 (by rfl) ⟨1086063, by rfl⟩ : syracuseStep 2896169 = 2172127) B2172127
theorem B41783627 : Blo 1807605 41783627 := bstep (se 1 (by rfl) ⟨31337720, by rfl⟩ : syracuseStep 41783627 = 62675441) B62675441
theorem B7729577 : Blo 1807605 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B8254009 : Blo 1807605 8254009 := bstep (se 2 (by rfl) ⟨3095253, by rfl⟩ : syracuseStep 8254009 = 6190507) B6190507
theorem B41751197 : Blo 1807605 41751197 := bstep (se 3 (by rfl) ⟨7828349, by rfl⟩ : syracuseStep 41751197 = 15656699) B15656699
theorem B6517523 : Blo 1807605 6517523 := bstep (se 1 (by rfl) ⟨4888142, by rfl⟩ : syracuseStep 6517523 = 9776285) B9776285
theorem B15447023 : Blo 1807605 15447023 := bstep (se 1 (by rfl) ⟨11585267, by rfl⟩ : syracuseStep 15447023 = 23170535) B23170535
theorem B4576297 : Blo 1807605 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B4068521 : Blo 1807605 4068521 := bstep (se 2 (by rfl) ⟨1525695, by rfl⟩ : syracuseStep 4068521 = 3051391) B3051391
theorem B2938121 : Blo 1807605 2938121 := bstep (se 2 (by rfl) ⟨1101795, by rfl⟩ : syracuseStep 2938121 = 2203591) B2203591
theorem B5150135 : Blo 1807605 5150135 := bstep (se 1 (by rfl) ⟨3862601, by rfl⟩ : syracuseStep 5150135 = 7725203) B7725203
theorem B1807839 : Blo 1807605 1807839 := bstep (se 1 (by rfl) ⟨1355879, by rfl⟩ : syracuseStep 1807839 = 2711759) B2711759
theorem B4576763 : Blo 1807605 4576763 := bstep (se 1 (by rfl) ⟨3432572, by rfl⟩ : syracuseStep 4576763 = 6865145) B6865145
theorem B1807871 : Blo 1807605 1807871 := bstep (se 1 (by rfl) ⟨1355903, by rfl⟩ : syracuseStep 1807871 = 2711807) B2711807
theorem B5150375 : Blo 1807605 5150375 := bstep (se 1 (by rfl) ⟨3862781, by rfl⟩ : syracuseStep 5150375 = 7725563) B7725563
theorem B8689355 : Blo 1807605 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B20608829 : Blo 1807605 20608829 := bstep (se 3 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 20608829 = 7728311) B7728311
theorem B3094427 : Blo 1807605 3094427 := bstep (se 1 (by rfl) ⟨2320820, by rfl⟩ : syracuseStep 3094427 = 4641641) B4641641
theorem B1832927 : Blo 1807605 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B1808415 : Blo 1807605 1808415 := bstep (se 1 (by rfl) ⟨1356311, by rfl⟩ : syracuseStep 1808415 = 2712623) B2712623
theorem B57219149 : Blo 1807605 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B1808495 : Blo 1807605 1808495 := bstep (se 1 (by rfl) ⟨1356371, by rfl⟩ : syracuseStep 1808495 = 2712743) B2712743
theorem B13728041 : Blo 1807605 13728041 := bstep (se 2 (by rfl) ⟨5148015, by rfl⟩ : syracuseStep 13728041 = 10296031) B10296031
theorem B3668321 : Blo 1807605 3668321 := bstep (se 2 (by rfl) ⟨1375620, by rfl⟩ : syracuseStep 3668321 = 2751241) B2751241
theorem B1808743 : Blo 1807605 1808743 := bstep (se 1 (by rfl) ⟨1356557, by rfl⟩ : syracuseStep 1808743 = 2713115) B2713115
theorem B4577735 : Blo 1807605 4577735 := bstep (se 1 (by rfl) ⟨3433301, by rfl⟩ : syracuseStep 4577735 = 6866603) B6866603
theorem B9157211 : Blo 1807605 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B4069979 : Blo 1807605 4069979 := bstep (se 1 (by rfl) ⟨3052484, by rfl⟩ : syracuseStep 4069979 = 6104969) B6104969
theorem B1808999 : Blo 1807605 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B1809023 : Blo 1807605 1809023 := bstep (se 1 (by rfl) ⟨1356767, by rfl⟩ : syracuseStep 1809023 = 2713535) B2713535
theorem B140950169 : Blo 1807605 140950169 := bstep (se 2 (by rfl) ⟨52856313, by rfl⟩ : syracuseStep 140950169 = 105712627) B105712627
theorem B1809147 : Blo 1807605 1809147 := bstep (se 1 (by rfl) ⟨1356860, by rfl⟩ : syracuseStep 1809147 = 2713721) B2713721
theorem B1809403 : Blo 1807605 1809403 := bstep (se 1 (by rfl) ⟨1357052, by rfl⟩ : syracuseStep 1809403 = 2714105) B2714105
theorem B5151775 : Blo 1807605 5151775 := bstep (se 1 (by rfl) ⟨3863831, by rfl⟩ : syracuseStep 5151775 = 7727663) B7727663
theorem B1809439 : Blo 1807605 1809439 := bstep (se 1 (by rfl) ⟨1357079, by rfl⟩ : syracuseStep 1809439 = 2714159) B2714159
theorem B5152025 : Blo 1807605 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B31735145 : Blo 1807605 31735145 := bstep (se 2 (by rfl) ⟨11900679, by rfl⟩ : syracuseStep 31735145 = 23801359) B23801359
theorem B11582831 : Blo 1807605 11582831 := bstep (se 1 (by rfl) ⟨8687123, by rfl⟩ : syracuseStep 11582831 = 17374247) B17374247
theorem B20594249 : Blo 1807605 20594249 := bstep (se 2 (by rfl) ⟨7722843, by rfl⟩ : syracuseStep 20594249 = 15445687) B15445687
theorem B4578889 : Blo 1807605 4578889 := bstep (se 2 (by rfl) ⟨1717083, by rfl⟩ : syracuseStep 4578889 = 3434167) B3434167
theorem B6962843 : Blo 1807605 6962843 := bstep (se 1 (by rfl) ⟨5222132, by rfl⟩ : syracuseStep 6962843 = 10444265) B10444265
theorem B4579193 : Blo 1807605 4579193 := bstep (se 2 (by rfl) ⟨1717197, by rfl⟩ : syracuseStep 4579193 = 3434395) B3434395
theorem B2711465 : Blo 1807605 2711465 := bstep (se 2 (by rfl) ⟨1016799, by rfl⟩ : syracuseStep 2711465 = 2033599) B2033599
theorem B6184927 : Blo 1807605 6184927 := bstep (se 1 (by rfl) ⟨4638695, by rfl⟩ : syracuseStep 6184927 = 9277391) B9277391
theorem B6103187 : Blo 1807605 6103187 := bstep (se 1 (by rfl) ⟨4577390, by rfl⟩ : syracuseStep 6103187 = 9154781) B9154781
theorem B152584397 : Blo 1807605 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B5153051 : Blo 1807605 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B10306055 : Blo 1807605 10306055 := bstep (se 1 (by rfl) ⟨7729541, by rfl⟩ : syracuseStep 10306055 = 15459083) B15459083
theorem B10298015 : Blo 1807605 10298015 := bstep (se 1 (by rfl) ⟨7723511, by rfl⟩ : syracuseStep 10298015 = 15447023) B15447023
theorem B13738733 : Blo 1807605 13738733 := bstep (se 3 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 13738733 = 5152025) B5152025
theorem B2712347 : Blo 1807605 2712347 := bstep (se 1 (by rfl) ⟨2034260, by rfl⟩ : syracuseStep 2712347 = 4068521) B4068521
theorem B1958747 : Blo 1807605 1958747 := bstep (se 1 (by rfl) ⟨1469060, by rfl⟩ : syracuseStep 1958747 = 2938121) B2938121
theorem B3433423 : Blo 1807605 3433423 := bstep (se 1 (by rfl) ⟨2575067, by rfl⟩ : syracuseStep 3433423 = 5150135) B5150135
theorem B11740141 : Blo 1807605 11740141 := bstep (se 3 (by rfl) ⟨2201276, by rfl⟩ : syracuseStep 11740141 = 4402553) B4402553
theorem B20595707 : Blo 1807605 20595707 := bstep (se 1 (by rfl) ⟨15446780, by rfl⟩ : syracuseStep 20595707 = 30893561) B30893561
theorem B2712617 : Blo 1807605 2712617 := bstep (se 2 (by rfl) ⟨1017231, by rfl⟩ : syracuseStep 2712617 = 2034463) B2034463
theorem B3433583 : Blo 1807605 3433583 := bstep (se 1 (by rfl) ⟨2575187, by rfl⟩ : syracuseStep 3433583 = 5150375) B5150375
theorem B5792903 : Blo 1807605 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B13739219 : Blo 1807605 13739219 := bstep (se 1 (by rfl) ⟨10304414, by rfl⟩ : syracuseStep 13739219 = 20608829) B20608829
theorem B9152027 : Blo 1807605 9152027 := bstep (se 1 (by rfl) ⟨6864020, by rfl⟩ : syracuseStep 9152027 = 13728041) B13728041
theorem B6104807 : Blo 1807605 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B2713319 : Blo 1807605 2713319 := bstep (se 1 (by rfl) ⟨2034989, by rfl⟩ : syracuseStep 2713319 = 4069979) B4069979
theorem B22005827 : Blo 1807605 22005827 := bstep (se 1 (by rfl) ⟨16504370, by rfl⟩ : syracuseStep 22005827 = 33008741) B33008741
theorem B6105185 : Blo 1807605 6105185 := bstep (se 2 (by rfl) ⟨2289444, by rfl⟩ : syracuseStep 6105185 = 4578889) B4578889
theorem B9161099 : Blo 1807605 9161099 := bstep (se 1 (by rfl) ⟨6870824, by rfl⟩ : syracuseStep 9161099 = 13741649) B13741649
theorem B13732415 : Blo 1807605 13732415 := bstep (se 1 (by rfl) ⟨10299311, by rfl⟩ : syracuseStep 13732415 = 20598623) B20598623
theorem B27855751 : Blo 1807605 27855751 := bstep (se 1 (by rfl) ⟨20891813, by rfl⟩ : syracuseStep 27855751 = 41783627) B41783627
theorem B4345015 : Blo 1807605 4345015 := bstep (se 1 (by rfl) ⟨3258761, by rfl⟩ : syracuseStep 4345015 = 6517523) B6517523
theorem B100347113 : Blo 1807605 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B11005345 : Blo 1807605 11005345 := bstep (se 2 (by rfl) ⟨4127004, by rfl⟩ : syracuseStep 11005345 = 8254009) B8254009
theorem B37105121 : Blo 1807605 37105121 := bstep (se 2 (by rfl) ⟨13914420, by rfl⟩ : syracuseStep 37105121 = 27828841) B27828841
theorem B6106643 : Blo 1807605 6106643 := bstep (se 1 (by rfl) ⟨4579982, by rfl⟩ : syracuseStep 6106643 = 9159965) B9159965
theorem B3051175 : Blo 1807605 3051175 := bstep (se 1 (by rfl) ⟨2288381, by rfl⟩ : syracuseStep 3051175 = 4576763) B4576763
theorem B5500727 : Blo 1807605 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B6869033 : Blo 1807605 6869033 := bstep (se 2 (by rfl) ⟨2575887, by rfl⟩ : syracuseStep 6869033 = 5151775) B5151775
theorem B2445547 : Blo 1807605 2445547 := bstep (se 1 (by rfl) ⟨1834160, by rfl⟩ : syracuseStep 2445547 = 3668321) B3668321
theorem B58683635 : Blo 1807605 58683635 := bstep (se 1 (by rfl) ⟨44012726, by rfl⟩ : syracuseStep 58683635 = 88025453) B88025453
theorem B3051823 : Blo 1807605 3051823 := bstep (se 1 (by rfl) ⟨2288867, by rfl⟩ : syracuseStep 3051823 = 4577735) B4577735
theorem B93966779 : Blo 1807605 93966779 := bstep (se 1 (by rfl) ⟨70475084, by rfl⟩ : syracuseStep 93966779 = 140950169) B140950169
theorem B13726583 : Blo 1807605 13726583 := bstep (se 1 (by rfl) ⟨10294937, by rfl⟩ : syracuseStep 13726583 = 20589875) B20589875
theorem B21156763 : Blo 1807605 21156763 := bstep (se 1 (by rfl) ⟨15867572, by rfl⟩ : syracuseStep 21156763 = 31735145) B31735145
theorem B7721887 : Blo 1807605 7721887 := bstep (se 1 (by rfl) ⟨5791415, by rfl⟩ : syracuseStep 7721887 = 11582831) B11582831
theorem B6272083 : Blo 1807605 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B4641895 : Blo 1807605 4641895 := bstep (se 1 (by rfl) ⟨3481421, by rfl⟩ : syracuseStep 4641895 = 6962843) B6962843
theorem B3052795 : Blo 1807605 3052795 := bstep (se 1 (by rfl) ⟨2289596, by rfl⟩ : syracuseStep 3052795 = 4579193) B4579193
theorem B4887805 : Blo 1807605 4887805 := bstep (se 3 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 4887805 = 1832927) B1832927
theorem B1807643 : Blo 1807605 1807643 := bstep (se 1 (by rfl) ⟨1355732, by rfl⟩ : syracuseStep 1807643 = 2711465) B2711465
theorem B8246569 : Blo 1807605 8246569 := bstep (se 2 (by rfl) ⟨3092463, by rfl⟩ : syracuseStep 8246569 = 6184927) B6184927
theorem B4068665 : Blo 1807605 4068665 := bstep (se 2 (by rfl) ⟨1525749, by rfl⟩ : syracuseStep 4068665 = 3051499) B3051499
theorem B1807743 : Blo 1807605 1807743 := bstep (se 1 (by rfl) ⟨1355807, by rfl⟩ : syracuseStep 1807743 = 2711615) B2711615
theorem B6870521 : Blo 1807605 6870521 := bstep (se 2 (by rfl) ⟨2576445, by rfl⟩ : syracuseStep 6870521 = 5152891) B5152891
theorem B1807899 : Blo 1807605 1807899 := bstep (se 1 (by rfl) ⟨1355924, by rfl⟩ : syracuseStep 1807899 = 2711849) B2711849
theorem B3053119 : Blo 1807605 3053119 := bstep (se 1 (by rfl) ⟨2289839, by rfl⟩ : syracuseStep 3053119 = 4579679) B4579679
theorem B4068971 : Blo 1807605 4068971 := bstep (se 1 (by rfl) ⟨3051728, by rfl⟩ : syracuseStep 4068971 = 6103457) B6103457
theorem B16717423 : Blo 1807605 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B4069007 : Blo 1807605 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B1808079 : Blo 1807605 1808079 := bstep (se 1 (by rfl) ⟨1356059, by rfl⟩ : syracuseStep 1808079 = 2712119) B2712119
theorem B27834131 : Blo 1807605 27834131 := bstep (se 1 (by rfl) ⟨20875598, by rfl⟩ : syracuseStep 27834131 = 41751197) B41751197
theorem B1808319 : Blo 1807605 1808319 := bstep (se 1 (by rfl) ⟨1356239, by rfl⟩ : syracuseStep 1808319 = 2712479) B2712479
theorem B4069439 : Blo 1807605 4069439 := bstep (se 1 (by rfl) ⟨3052079, by rfl⟩ : syracuseStep 4069439 = 6104159) B6104159
theorem B14866499 : Blo 1807605 14866499 := bstep (se 1 (by rfl) ⟨11149874, by rfl⟩ : syracuseStep 14866499 = 22299749) B22299749
theorem B7723117 : Blo 1807605 7723117 := bstep (se 3 (by rfl) ⟨1448084, by rfl⟩ : syracuseStep 7723117 = 2896169) B2896169
theorem B1808511 : Blo 1807605 1808511 := bstep (se 1 (by rfl) ⟨1356383, by rfl⟩ : syracuseStep 1808511 = 2712767) B2712767
theorem B11589803 : Blo 1807605 11589803 := bstep (se 1 (by rfl) ⟨8692352, by rfl⟩ : syracuseStep 11589803 = 17384705) B17384705
theorem B1808607 : Blo 1807605 1808607 := bstep (se 1 (by rfl) ⟨1356455, by rfl⟩ : syracuseStep 1808607 = 2712911) B2712911
theorem B1808667 : Blo 1807605 1808667 := bstep (se 1 (by rfl) ⟨1356500, by rfl⟩ : syracuseStep 1808667 = 2713001) B2713001
theorem B1808767 : Blo 1807605 1808767 := bstep (se 1 (by rfl) ⟨1356575, by rfl⟩ : syracuseStep 1808767 = 2713151) B2713151
theorem B2062951 : Blo 1807605 2062951 := bstep (se 1 (by rfl) ⟨1547213, by rfl⟩ : syracuseStep 2062951 = 3094427) B3094427
theorem B1809007 : Blo 1807605 1809007 := bstep (se 1 (by rfl) ⟨1356755, by rfl⟩ : syracuseStep 1809007 = 2713511) B2713511
theorem B1809087 : Blo 1807605 1809087 := bstep (se 1 (by rfl) ⟨1356815, by rfl⟩ : syracuseStep 1809087 = 2713631) B2713631
theorem B6101729 : Blo 1807605 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B5151707 : Blo 1807605 5151707 := bstep (se 1 (by rfl) ⟨3863780, by rfl⟩ : syracuseStep 5151707 = 7727561) B7727561
theorem B1809391 : Blo 1807605 1809391 := bstep (se 1 (by rfl) ⟨1357043, by rfl⟩ : syracuseStep 1809391 = 2714087) B2714087
theorem B1809511 : Blo 1807605 1809511 := bstep (se 1 (by rfl) ⟨1357133, by rfl⟩ : syracuseStep 1809511 = 2714267) B2714267
theorem B4578515 : Blo 1807605 4578515 := bstep (se 1 (by rfl) ⟨3433886, by rfl⟩ : syracuseStep 4578515 = 6867773) B6867773
theorem B396164357 : Blo 1807605 396164357 := bstep (se 4 (by rfl) ⟨37140408, by rfl⟩ : syracuseStep 396164357 = 74280817) B74280817
theorem B4070663 : Blo 1807605 4070663 := bstep (se 1 (by rfl) ⟨3052997, by rfl⟩ : syracuseStep 4070663 = 6105995) B6105995
theorem B4071023 : Blo 1807605 4071023 := bstep (se 1 (by rfl) ⟨3053267, by rfl⟩ : syracuseStep 4071023 = 6106535) B6106535
theorem B10296989 : Blo 1807605 10296989 := bstep (se 3 (by rfl) ⟨1930685, by rfl⟩ : syracuseStep 10296989 = 3861371) B3861371
theorem B13729499 : Blo 1807605 13729499 := bstep (se 1 (by rfl) ⟨10297124, by rfl⟩ : syracuseStep 13729499 = 20594249) B20594249
theorem B7724879 : Blo 1807605 7724879 := bstep (se 1 (by rfl) ⟨5793659, by rfl⟩ : syracuseStep 7724879 = 11587319) B11587319
theorem B4579355 : Blo 1807605 4579355 := bstep (se 1 (by rfl) ⟨3434516, by rfl⟩ : syracuseStep 4579355 = 6869033) B6869033
theorem B10297489 : Blo 1807605 10297489 := bstep (se 2 (by rfl) ⟨3861558, by rfl⟩ : syracuseStep 10297489 = 7723117) B7723117
theorem B62644519 : Blo 1807605 62644519 := bstep (se 1 (by rfl) ⟨46983389, by rfl⟩ : syracuseStep 62644519 = 93966779) B93966779
theorem B3260729 : Blo 1807605 3260729 := bstep (se 2 (by rfl) ⟨1222773, by rfl⟩ : syracuseStep 3260729 = 2445547) B2445547
theorem B6865343 : Blo 1807605 6865343 := bstep (se 1 (by rfl) ⟨5149007, by rfl⟩ : syracuseStep 6865343 = 10298015) B10298015
theorem B9159155 : Blo 1807605 9159155 := bstep (se 1 (by rfl) ⟨6869366, by rfl⟩ : syracuseStep 9159155 = 13738733) B13738733
theorem B11002405 : Blo 1807605 11002405 := bstep (se 4 (by rfl) ⟨1031475, by rfl⟩ : syracuseStep 11002405 = 2062951) B2062951
theorem B9151055 : Blo 1807605 9151055 := bstep (se 1 (by rfl) ⟨6863291, by rfl⟩ : syracuseStep 9151055 = 13726583) B13726583
theorem B13730471 : Blo 1807605 13730471 := bstep (se 1 (by rfl) ⟨10297853, by rfl⟩ : syracuseStep 13730471 = 20595707) B20595707
theorem B9159479 : Blo 1807605 9159479 := bstep (se 1 (by rfl) ⟨6869609, by rfl⟩ : syracuseStep 9159479 = 13739219) B13739219
theorem B2712443 : Blo 1807605 2712443 := bstep (se 1 (by rfl) ⟨2034332, by rfl⟩ : syracuseStep 2712443 = 4068665) B4068665
theorem B4580347 : Blo 1807605 4580347 := bstep (se 1 (by rfl) ⟨3435260, by rfl⟩ : syracuseStep 4580347 = 6870521) B6870521
theorem B2712647 : Blo 1807605 2712647 := bstep (se 1 (by rfl) ⟨2034485, by rfl⟩ : syracuseStep 2712647 = 4068971) B4068971
theorem B2712671 : Blo 1807605 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B18556087 : Blo 1807605 18556087 := bstep (se 1 (by rfl) ⟨13917065, by rfl⟩ : syracuseStep 18556087 = 27834131) B27834131
theorem B2712959 : Blo 1807605 2712959 := bstep (se 1 (by rfl) ⟨2034719, by rfl⟩ : syracuseStep 2712959 = 4069439) B4069439
theorem B7726535 : Blo 1807605 7726535 := bstep (se 1 (by rfl) ⟨5794901, by rfl⟩ : syracuseStep 7726535 = 11589803) B11589803
theorem B5793353 : Blo 1807605 5793353 := bstep (se 2 (by rfl) ⟨2172507, by rfl⟩ : syracuseStep 5793353 = 4345015) B4345015
theorem B10995425 : Blo 1807605 10995425 := bstep (se 2 (by rfl) ⟨4123284, by rfl⟩ : syracuseStep 10995425 = 8246569) B8246569
theorem B14673793 : Blo 1807605 14673793 := bstep (se 2 (by rfl) ⟨5502672, by rfl⟩ : syracuseStep 14673793 = 11005345) B11005345
theorem B3434471 : Blo 1807605 3434471 := bstep (se 1 (by rfl) ⟨2575853, by rfl⟩ : syracuseStep 3434471 = 5151707) B5151707
theorem B66898075 : Blo 1807605 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B2713775 : Blo 1807605 2713775 := bstep (se 1 (by rfl) ⟨2035331, by rfl⟩ : syracuseStep 2713775 = 4070663) B4070663
theorem B2714015 : Blo 1807605 2714015 := bstep (se 1 (by rfl) ⟨2035511, by rfl⟩ : syracuseStep 2714015 = 4071023) B4071023
theorem B9152999 : Blo 1807605 9152999 := bstep (se 1 (by rfl) ⟨6864749, by rfl⟩ : syracuseStep 9152999 = 13729499) B13729499
theorem B101722931 : Blo 1807605 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B3435367 : Blo 1807605 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B2289055 : Blo 1807605 2289055 := bstep (se 1 (by rfl) ⟨1716791, by rfl⟩ : syracuseStep 2289055 = 3433583) B3433583
theorem B3861935 : Blo 1807605 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B20893301 : Blo 1807605 20893301 := bstep (se 5 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 20893301 = 1958747) B1958747
theorem B28209017 : Blo 1807605 28209017 := bstep (se 2 (by rfl) ⟨10578381, by rfl⟩ : syracuseStep 28209017 = 21156763) B21156763
theorem B6189193 : Blo 1807605 6189193 := bstep (se 2 (by rfl) ⟨2320947, by rfl⟩ : syracuseStep 6189193 = 4641895) B4641895
theorem B6107399 : Blo 1807605 6107399 := bstep (se 1 (by rfl) ⟨4580549, by rfl⟩ : syracuseStep 6107399 = 9161099) B9161099
theorem B6517073 : Blo 1807605 6517073 := bstep (se 2 (by rfl) ⟨2443902, by rfl⟩ : syracuseStep 6517073 = 4887805) B4887805
theorem B9154943 : Blo 1807605 9154943 := bstep (se 1 (by rfl) ⟨6866207, by rfl⟩ : syracuseStep 9154943 = 13732415) B13732415
theorem B4067819 : Blo 1807605 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B3052343 : Blo 1807605 3052343 := bstep (se 1 (by rfl) ⟨2289257, by rfl⟩ : syracuseStep 3052343 = 4578515) B4578515
theorem B4068233 : Blo 1807605 4068233 := bstep (se 2 (by rfl) ⟨1525587, by rfl⟩ : syracuseStep 4068233 = 3051175) B3051175
theorem B24736747 : Blo 1807605 24736747 := bstep (se 1 (by rfl) ⟨18552560, by rfl⟩ : syracuseStep 24736747 = 37105121) B37105121
theorem B3667151 : Blo 1807605 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B5149919 : Blo 1807605 5149919 := bstep (se 1 (by rfl) ⟨3862439, by rfl⟩ : syracuseStep 5149919 = 7724879) B7724879
theorem B4068791 : Blo 1807605 4068791 := bstep (se 1 (by rfl) ⟨3051593, by rfl⟩ : syracuseStep 4068791 = 6103187) B6103187
theorem B39122423 : Blo 1807605 39122423 := bstep (se 1 (by rfl) ⟨29341817, by rfl⟩ : syracuseStep 39122423 = 58683635) B58683635
theorem B6870703 : Blo 1807605 6870703 := bstep (se 1 (by rfl) ⟨5153027, by rfl⟩ : syracuseStep 6870703 = 10306055) B10306055
theorem B4069097 : Blo 1807605 4069097 := bstep (se 2 (by rfl) ⟨1525911, by rfl⟩ : syracuseStep 4069097 = 3051823) B3051823
theorem B1808231 : Blo 1807605 1808231 := bstep (se 1 (by rfl) ⟨1356173, by rfl⟩ : syracuseStep 1808231 = 2712347) B2712347
theorem B1808411 : Blo 1807605 1808411 := bstep (se 1 (by rfl) ⟨1356308, by rfl⟩ : syracuseStep 1808411 = 2712617) B2712617
theorem B6101351 : Blo 1807605 6101351 := bstep (se 1 (by rfl) ⟨4576013, by rfl⟩ : syracuseStep 6101351 = 9152027) B9152027
theorem B4069871 : Blo 1807605 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B1808879 : Blo 1807605 1808879 := bstep (se 1 (by rfl) ⟨1356659, by rfl⟩ : syracuseStep 1808879 = 2713319) B2713319
theorem B37141001 : Blo 1807605 37141001 := bstep (se 2 (by rfl) ⟨13927875, by rfl⟩ : syracuseStep 37141001 = 27855751) B27855751
theorem B10295849 : Blo 1807605 10295849 := bstep (se 2 (by rfl) ⟨3860943, by rfl⟩ : syracuseStep 10295849 = 7721887) B7721887
theorem B4577897 : Blo 1807605 4577897 := bstep (se 2 (by rfl) ⟨1716711, by rfl⟩ : syracuseStep 4577897 = 3433423) B3433423
theorem B15653521 : Blo 1807605 15653521 := bstep (se 2 (by rfl) ⟨5870070, by rfl⟩ : syracuseStep 15653521 = 11740141) B11740141
theorem B9910999 : Blo 1807605 9910999 := bstep (se 1 (by rfl) ⟨7433249, by rfl⟩ : syracuseStep 9910999 = 14866499) B14866499
theorem B14670551 : Blo 1807605 14670551 := bstep (se 1 (by rfl) ⟨11002913, by rfl⟩ : syracuseStep 14670551 = 22005827) B22005827
theorem B4070123 : Blo 1807605 4070123 := bstep (se 1 (by rfl) ⟨3052592, by rfl⟩ : syracuseStep 4070123 = 6105185) B6105185
theorem B8362777 : Blo 1807605 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B4070393 : Blo 1807605 4070393 := bstep (se 2 (by rfl) ⟨1526397, by rfl⟩ : syracuseStep 4070393 = 3052795) B3052795
theorem B4070825 : Blo 1807605 4070825 := bstep (se 2 (by rfl) ⟨1526559, by rfl⟩ : syracuseStep 4070825 = 3053119) B3053119
theorem B22289897 : Blo 1807605 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B264109571 : Blo 1807605 264109571 := bstep (se 1 (by rfl) ⟨198082178, by rfl⟩ : syracuseStep 264109571 = 396164357) B396164357
theorem B4071095 : Blo 1807605 4071095 := bstep (se 1 (by rfl) ⟨3053321, by rfl⟩ : syracuseStep 4071095 = 6106643) B6106643
theorem B6864659 : Blo 1807605 6864659 := bstep (se 1 (by rfl) ⟨5148494, by rfl⟩ : syracuseStep 6864659 = 10296989) B10296989
theorem B4071599 : Blo 1807605 4071599 := bstep (se 1 (by rfl) ⟨3053699, by rfl⟩ : syracuseStep 4071599 = 6107399) B6107399
theorem B13729985 : Blo 1807605 13729985 := bstep (se 2 (by rfl) ⟨5148744, by rfl⟩ : syracuseStep 13729985 = 10297489) B10297489
theorem B6103295 : Blo 1807605 6103295 := bstep (se 1 (by rfl) ⟨4577471, by rfl⟩ : syracuseStep 6103295 = 9154943) B9154943
theorem B2711879 : Blo 1807605 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B83526025 : Blo 1807605 83526025 := bstep (se 2 (by rfl) ⟨31322259, by rfl⟩ : syracuseStep 83526025 = 62644519) B62644519
theorem B2712155 : Blo 1807605 2712155 := bstep (se 1 (by rfl) ⟨2034116, by rfl⟩ : syracuseStep 2712155 = 4068233) B4068233
theorem B3433279 : Blo 1807605 3433279 := bstep (se 1 (by rfl) ⟨2574959, by rfl⟩ : syracuseStep 3433279 = 5149919) B5149919
theorem B13214665 : Blo 1807605 13214665 := bstep (se 2 (by rfl) ⟨4955499, by rfl⟩ : syracuseStep 13214665 = 9910999) B9910999
theorem B2712527 : Blo 1807605 2712527 := bstep (se 1 (by rfl) ⟨2034395, by rfl⟩ : syracuseStep 2712527 = 4068791) B4068791
theorem B11150369 : Blo 1807605 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B4580489 : Blo 1807605 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B2712731 : Blo 1807605 2712731 := bstep (se 1 (by rfl) ⟨2034548, by rfl⟩ : syracuseStep 2712731 = 4069097) B4069097
theorem B32982329 : Blo 1807605 32982329 := bstep (se 2 (by rfl) ⟨12368373, by rfl⟩ : syracuseStep 32982329 = 24736747) B24736747
theorem B24741449 : Blo 1807605 24741449 := bstep (se 2 (by rfl) ⟨9278043, by rfl⟩ : syracuseStep 24741449 = 18556087) B18556087
theorem B2713247 : Blo 1807605 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B2713415 : Blo 1807605 2713415 := bstep (se 1 (by rfl) ⟨2035061, by rfl⟩ : syracuseStep 2713415 = 4070123) B4070123
theorem B67815287 : Blo 1807605 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B2713595 : Blo 1807605 2713595 := bstep (se 1 (by rfl) ⟨2035196, by rfl⟩ : syracuseStep 2713595 = 4070393) B4070393
theorem B9160937 : Blo 1807605 9160937 := bstep (se 2 (by rfl) ⟨3435351, by rfl⟩ : syracuseStep 9160937 = 6870703) B6870703
theorem B2713883 : Blo 1807605 2713883 := bstep (se 1 (by rfl) ⟨2035412, by rfl⟩ : syracuseStep 2713883 = 4070825) B4070825
theorem B2574623 : Blo 1807605 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B176073047 : Blo 1807605 176073047 := bstep (se 1 (by rfl) ⟨132054785, by rfl⟩ : syracuseStep 176073047 = 264109571) B264109571
theorem B13928867 : Blo 1807605 13928867 := bstep (se 1 (by rfl) ⟨10446650, by rfl⟩ : syracuseStep 13928867 = 20893301) B20893301
theorem B2714063 : Blo 1807605 2714063 := bstep (se 1 (by rfl) ⟨2035547, by rfl⟩ : syracuseStep 2714063 = 4071095) B4071095
theorem B19565057 : Blo 1807605 19565057 := bstep (se 2 (by rfl) ⟨7336896, by rfl⟩ : syracuseStep 19565057 = 14673793) B14673793
theorem B89197433 : Blo 1807605 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B2173819 : Blo 1807605 2173819 := bstep (se 1 (by rfl) ⟨1630364, by rfl⟩ : syracuseStep 2173819 = 3260729) B3260729
theorem B4344715 : Blo 1807605 4344715 := bstep (se 1 (by rfl) ⟨3258536, by rfl⟩ : syracuseStep 4344715 = 6517073) B6517073
theorem B6106103 : Blo 1807605 6106103 := bstep (se 1 (by rfl) ⟨4579577, by rfl⟩ : syracuseStep 6106103 = 9159155) B9159155
theorem B9153647 : Blo 1807605 9153647 := bstep (se 1 (by rfl) ⟨6865235, by rfl⟩ : syracuseStep 9153647 = 13730471) B13730471
theorem B2034895 : Blo 1807605 2034895 := bstep (se 1 (by rfl) ⟨1526171, by rfl⟩ : syracuseStep 2034895 = 3052343) B3052343
theorem B6106319 : Blo 1807605 6106319 := bstep (se 1 (by rfl) ⟨4579739, by rfl⟩ : syracuseStep 6106319 = 9159479) B9159479
theorem B33009029 : Blo 1807605 33009029 := bstep (se 4 (by rfl) ⟨3094596, by rfl⟩ : syracuseStep 33009029 = 6189193) B6189193
theorem B2444767 : Blo 1807605 2444767 := bstep (se 1 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 2444767 = 3667151) B3667151
theorem B3862235 : Blo 1807605 3862235 := bstep (se 1 (by rfl) ⟨2896676, by rfl⟩ : syracuseStep 3862235 = 5793353) B5793353
theorem B2289647 : Blo 1807605 2289647 := bstep (se 1 (by rfl) ⟨1717235, by rfl⟩ : syracuseStep 2289647 = 3434471) B3434471
theorem B6107129 : Blo 1807605 6107129 := bstep (se 2 (by rfl) ⟨2290173, by rfl⟩ : syracuseStep 6107129 = 4580347) B4580347
theorem B4067567 : Blo 1807605 4067567 := bstep (se 1 (by rfl) ⟨3050675, by rfl⟩ : syracuseStep 4067567 = 6101351) B6101351
theorem B24760667 : Blo 1807605 24760667 := bstep (se 1 (by rfl) ⟨18570500, by rfl⟩ : syracuseStep 24760667 = 37141001) B37141001
theorem B3051931 : Blo 1807605 3051931 := bstep (se 1 (by rfl) ⟨2288948, by rfl⟩ : syracuseStep 3051931 = 4577897) B4577897
theorem B3052073 : Blo 1807605 3052073 := bstep (se 2 (by rfl) ⟨1144527, by rfl⟩ : syracuseStep 3052073 = 2289055) B2289055
theorem B75224045 : Blo 1807605 75224045 := bstep (se 3 (by rfl) ⟨14104508, by rfl⟩ : syracuseStep 75224045 = 28209017) B28209017
theorem B4576439 : Blo 1807605 4576439 := bstep (se 1 (by rfl) ⟨3432329, by rfl⟩ : syracuseStep 4576439 = 6864659) B6864659
theorem B3052903 : Blo 1807605 3052903 := bstep (se 1 (by rfl) ⟨2289677, by rfl⟩ : syracuseStep 3052903 = 4579355) B4579355
theorem B4576895 : Blo 1807605 4576895 := bstep (se 1 (by rfl) ⟨3432671, by rfl⟩ : syracuseStep 4576895 = 6865343) B6865343
theorem B6100703 : Blo 1807605 6100703 := bstep (se 1 (by rfl) ⟨4575527, by rfl⟩ : syracuseStep 6100703 = 9151055) B9151055
theorem B1808295 : Blo 1807605 1808295 := bstep (se 1 (by rfl) ⟨1356221, by rfl⟩ : syracuseStep 1808295 = 2712443) B2712443
theorem B1808431 : Blo 1807605 1808431 := bstep (se 1 (by rfl) ⟨1356323, by rfl⟩ : syracuseStep 1808431 = 2712647) B2712647
theorem B14669873 : Blo 1807605 14669873 := bstep (se 2 (by rfl) ⟨5501202, by rfl⟩ : syracuseStep 14669873 = 11002405) B11002405
theorem B1808447 : Blo 1807605 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B20871361 : Blo 1807605 20871361 := bstep (se 2 (by rfl) ⟨7826760, by rfl⟩ : syracuseStep 20871361 = 15653521) B15653521
theorem B1808639 : Blo 1807605 1808639 := bstep (se 1 (by rfl) ⟨1356479, by rfl⟩ : syracuseStep 1808639 = 2712959) B2712959
theorem B5151023 : Blo 1807605 5151023 := bstep (se 1 (by rfl) ⟨3863267, by rfl⟩ : syracuseStep 5151023 = 7726535) B7726535
theorem B26081615 : Blo 1807605 26081615 := bstep (se 1 (by rfl) ⟨19561211, by rfl⟩ : syracuseStep 26081615 = 39122423) B39122423
theorem B7330283 : Blo 1807605 7330283 := bstep (se 1 (by rfl) ⟨5497712, by rfl⟩ : syracuseStep 7330283 = 10995425) B10995425
theorem B1809183 : Blo 1807605 1809183 := bstep (se 1 (by rfl) ⟨1356887, by rfl⟩ : syracuseStep 1809183 = 2713775) B2713775
theorem B1809343 : Blo 1807605 1809343 := bstep (se 1 (by rfl) ⟨1357007, by rfl⟩ : syracuseStep 1809343 = 2714015) B2714015
theorem B6101999 : Blo 1807605 6101999 := bstep (se 1 (by rfl) ⟨4576499, by rfl⟩ : syracuseStep 6101999 = 9152999) B9152999
theorem B6863899 : Blo 1807605 6863899 := bstep (se 1 (by rfl) ⟨5147924, by rfl⟩ : syracuseStep 6863899 = 10295849) B10295849
theorem B9780367 : Blo 1807605 9780367 := bstep (se 1 (by rfl) ⟨7335275, by rfl⟩ : syracuseStep 9780367 = 14670551) B14670551
theorem B14859931 : Blo 1807605 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B2711711 : Blo 1807605 2711711 := bstep (se 1 (by rfl) ⟨2033783, by rfl⟩ : syracuseStep 2711711 = 4067567) B4067567
theorem B16507111 : Blo 1807605 16507111 := bstep (se 1 (by rfl) ⟨12380333, by rfl⟩ : syracuseStep 16507111 = 24760667) B24760667
theorem B27828481 : Blo 1807605 27828481 := bstep (se 2 (by rfl) ⟨10435680, by rfl⟩ : syracuseStep 27828481 = 20871361) B20871361
theorem B6865661 : Blo 1807605 6865661 := bstep (se 3 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 6865661 = 2574623) B2574623
theorem B21988219 : Blo 1807605 21988219 := bstep (se 1 (by rfl) ⟨16491164, by rfl⟩ : syracuseStep 21988219 = 32982329) B32982329
theorem B5792953 : Blo 1807605 5792953 := bstep (se 2 (by rfl) ⟨2172357, by rfl⟩ : syracuseStep 5792953 = 4344715) B4344715
theorem B9151865 : Blo 1807605 9151865 := bstep (se 2 (by rfl) ⟨3431949, by rfl⟩ : syracuseStep 9151865 = 6863899) B6863899
theorem B3434015 : Blo 1807605 3434015 := bstep (se 1 (by rfl) ⟨2575511, by rfl⟩ : syracuseStep 3434015 = 5151023) B5151023
theorem B2713193 : Blo 1807605 2713193 := bstep (se 2 (by rfl) ⟨1017447, by rfl⟩ : syracuseStep 2713193 = 2034895) B2034895
theorem B13043371 : Blo 1807605 13043371 := bstep (se 1 (by rfl) ⟨9782528, by rfl⟩ : syracuseStep 13043371 = 19565057) B19565057
theorem B22006019 : Blo 1807605 22006019 := bstep (se 1 (by rfl) ⟨16504514, by rfl⟩ : syracuseStep 22006019 = 33009029) B33009029
theorem B2574823 : Blo 1807605 2574823 := bstep (se 1 (by rfl) ⟨1931117, by rfl⟩ : syracuseStep 2574823 = 3862235) B3862235
theorem B6105725 : Blo 1807605 6105725 := bstep (se 3 (by rfl) ⟨1144823, by rfl⟩ : syracuseStep 6105725 = 2289647) B2289647
theorem B2714399 : Blo 1807605 2714399 := bstep (se 1 (by rfl) ⟨2035799, by rfl⟩ : syracuseStep 2714399 = 4071599) B4071599
theorem B9153323 : Blo 1807605 9153323 := bstep (se 1 (by rfl) ⟨6864992, by rfl⟩ : syracuseStep 9153323 = 13729985) B13729985
theorem B2034715 : Blo 1807605 2034715 := bstep (se 1 (by rfl) ⟨1526036, by rfl⟩ : syracuseStep 2034715 = 3052073) B3052073
theorem B7433579 : Blo 1807605 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B3050959 : Blo 1807605 3050959 := bstep (se 1 (by rfl) ⟨2288219, by rfl⟩ : syracuseStep 3050959 = 4576439) B4576439
theorem B16494299 : Blo 1807605 16494299 := bstep (se 1 (by rfl) ⟨12370724, by rfl⟩ : syracuseStep 16494299 = 24741449) B24741449
theorem B3051263 : Blo 1807605 3051263 := bstep (se 1 (by rfl) ⟨2288447, by rfl⟩ : syracuseStep 3051263 = 4576895) B4576895
theorem B4067135 : Blo 1807605 4067135 := bstep (se 1 (by rfl) ⟨3050351, by rfl⟩ : syracuseStep 4067135 = 6100703) B6100703
theorem B6107291 : Blo 1807605 6107291 := bstep (se 1 (by rfl) ⟨4580468, by rfl⟩ : syracuseStep 6107291 = 9160937) B9160937
theorem B17387743 : Blo 1807605 17387743 := bstep (se 1 (by rfl) ⟨13040807, by rfl⟩ : syracuseStep 17387743 = 26081615) B26081615
theorem B9285911 : Blo 1807605 9285911 := bstep (se 1 (by rfl) ⟨6964433, by rfl⟩ : syracuseStep 9285911 = 13928867) B13928867
theorem B4886855 : Blo 1807605 4886855 := bstep (se 1 (by rfl) ⟨3665141, by rfl⟩ : syracuseStep 4886855 = 7330283) B7330283
theorem B52155029 : Blo 1807605 52155029 := bstep (se 6 (by rfl) ⟨1222383, by rfl⟩ : syracuseStep 52155029 = 2444767) B2444767
theorem B4067999 : Blo 1807605 4067999 := bstep (se 1 (by rfl) ⟨3050999, by rfl⟩ : syracuseStep 4067999 = 6101999) B6101999
theorem B19813241 : Blo 1807605 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B4068863 : Blo 1807605 4068863 := bstep (se 1 (by rfl) ⟨3051647, by rfl⟩ : syracuseStep 4068863 = 6103295) B6103295
theorem B1807919 : Blo 1807605 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B1808103 : Blo 1807605 1808103 := bstep (se 1 (by rfl) ⟨1356077, by rfl⟩ : syracuseStep 1808103 = 2712155) B2712155
theorem B111368033 : Blo 1807605 111368033 := bstep (se 2 (by rfl) ⟨41763012, by rfl⟩ : syracuseStep 111368033 = 83526025) B83526025
theorem B4069241 : Blo 1807605 4069241 := bstep (se 2 (by rfl) ⟨1525965, by rfl⟩ : syracuseStep 4069241 = 3051931) B3051931
theorem B1808351 : Blo 1807605 1808351 := bstep (se 1 (by rfl) ⟨1356263, by rfl⟩ : syracuseStep 1808351 = 2712527) B2712527
theorem B50149363 : Blo 1807605 50149363 := bstep (se 1 (by rfl) ⟨37612022, by rfl⟩ : syracuseStep 50149363 = 75224045) B75224045
theorem B3053659 : Blo 1807605 3053659 := bstep (se 1 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 3053659 = 4580489) B4580489
theorem B1808487 : Blo 1807605 1808487 := bstep (se 1 (by rfl) ⟨1356365, by rfl⟩ : syracuseStep 1808487 = 2712731) B2712731
theorem B4577705 : Blo 1807605 4577705 := bstep (se 2 (by rfl) ⟨1716639, by rfl⟩ : syracuseStep 4577705 = 3433279) B3433279
theorem B1808831 : Blo 1807605 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B2898425 : Blo 1807605 2898425 := bstep (se 2 (by rfl) ⟨1086909, by rfl⟩ : syracuseStep 2898425 = 2173819) B2173819
theorem B1808943 : Blo 1807605 1808943 := bstep (se 1 (by rfl) ⟨1356707, by rfl⟩ : syracuseStep 1808943 = 2713415) B2713415
theorem B45210191 : Blo 1807605 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B17619553 : Blo 1807605 17619553 := bstep (se 2 (by rfl) ⟨6607332, by rfl⟩ : syracuseStep 17619553 = 13214665) B13214665
theorem B1809063 : Blo 1807605 1809063 := bstep (se 1 (by rfl) ⟨1356797, by rfl⟩ : syracuseStep 1809063 = 2713595) B2713595
theorem B9779915 : Blo 1807605 9779915 := bstep (se 1 (by rfl) ⟨7334936, by rfl⟩ : syracuseStep 9779915 = 14669873) B14669873
theorem B1809255 : Blo 1807605 1809255 := bstep (se 1 (by rfl) ⟨1356941, by rfl⟩ : syracuseStep 1809255 = 2713883) B2713883
theorem B13040489 : Blo 1807605 13040489 := bstep (se 2 (by rfl) ⟨4890183, by rfl⟩ : syracuseStep 13040489 = 9780367) B9780367
theorem B117382031 : Blo 1807605 117382031 := bstep (se 1 (by rfl) ⟨88036523, by rfl⟩ : syracuseStep 117382031 = 176073047) B176073047
theorem B1809375 : Blo 1807605 1809375 := bstep (se 1 (by rfl) ⟨1357031, by rfl⟩ : syracuseStep 1809375 = 2714063) B2714063
theorem B4070537 : Blo 1807605 4070537 := bstep (se 2 (by rfl) ⟨1526451, by rfl⟩ : syracuseStep 4070537 = 3052903) B3052903
theorem B59464955 : Blo 1807605 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B4070735 : Blo 1807605 4070735 := bstep (se 1 (by rfl) ⟨3053051, by rfl⟩ : syracuseStep 4070735 = 6106103) B6106103
theorem B6102431 : Blo 1807605 6102431 := bstep (se 1 (by rfl) ⟨4576823, by rfl⟩ : syracuseStep 6102431 = 9153647) B9153647
theorem B4070879 : Blo 1807605 4070879 := bstep (se 1 (by rfl) ⟨3053159, by rfl⟩ : syracuseStep 4070879 = 6106319) B6106319
theorem B4071419 : Blo 1807605 4071419 := bstep (se 1 (by rfl) ⟨3053564, by rfl⟩ : syracuseStep 4071419 = 6107129) B6107129
theorem B4071527 : Blo 1807605 4071527 := bstep (se 1 (by rfl) ⟨3053645, by rfl⟩ : syracuseStep 4071527 = 6107291) B6107291
theorem B4071545 : Blo 1807605 4071545 := bstep (se 2 (by rfl) ⟨1526829, by rfl⟩ : syracuseStep 4071545 = 3053659) B3053659
theorem B23183657 : Blo 1807605 23183657 := bstep (se 2 (by rfl) ⟨8693871, by rfl⟩ : syracuseStep 23183657 = 17387743) B17387743
theorem B2711999 : Blo 1807605 2711999 := bstep (se 1 (by rfl) ⟨2033999, by rfl⟩ : syracuseStep 2711999 = 4067999) B4067999
theorem B3433097 : Blo 1807605 3433097 := bstep (se 2 (by rfl) ⟨1287411, by rfl⟩ : syracuseStep 3433097 = 2574823) B2574823
theorem B2712575 : Blo 1807605 2712575 := bstep (se 1 (by rfl) ⟨2034431, by rfl⟩ : syracuseStep 2712575 = 4068863) B4068863
theorem B74245355 : Blo 1807605 74245355 := bstep (se 1 (by rfl) ⟨55684016, by rfl⟩ : syracuseStep 74245355 = 111368033) B111368033
theorem B2712827 : Blo 1807605 2712827 := bstep (se 1 (by rfl) ⟨2034620, by rfl⟩ : syracuseStep 2712827 = 4069241) B4069241
theorem B2712953 : Blo 1807605 2712953 := bstep (se 2 (by rfl) ⟨1017357, by rfl⟩ : syracuseStep 2712953 = 2034715) B2034715
theorem B8693659 : Blo 1807605 8693659 := bstep (se 1 (by rfl) ⟨6520244, by rfl⟩ : syracuseStep 8693659 = 13040489) B13040489
theorem B2713691 : Blo 1807605 2713691 := bstep (se 1 (by rfl) ⟨2035268, by rfl⟩ : syracuseStep 2713691 = 4070537) B4070537
theorem B39643303 : Blo 1807605 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B2713823 : Blo 1807605 2713823 := bstep (se 1 (by rfl) ⟨2035367, by rfl⟩ : syracuseStep 2713823 = 4070735) B4070735
theorem B2713919 : Blo 1807605 2713919 := bstep (se 1 (by rfl) ⟨2035439, by rfl⟩ : syracuseStep 2713919 = 4070879) B4070879
theorem B10996199 : Blo 1807605 10996199 := bstep (se 1 (by rfl) ⟨8247149, by rfl⟩ : syracuseStep 10996199 = 16494299) B16494299
theorem B2034175 : Blo 1807605 2034175 := bstep (se 1 (by rfl) ⟨1525631, by rfl⟩ : syracuseStep 2034175 = 3051263) B3051263
theorem B66865817 : Blo 1807605 66865817 := bstep (se 2 (by rfl) ⟨25074681, by rfl⟩ : syracuseStep 66865817 = 50149363) B50149363
theorem B2714279 : Blo 1807605 2714279 := bstep (se 1 (by rfl) ⟨2035709, by rfl⟩ : syracuseStep 2714279 = 4071419) B4071419
theorem B37104641 : Blo 1807605 37104641 := bstep (se 2 (by rfl) ⟨13914240, by rfl⟩ : syracuseStep 37104641 = 27828481) B27828481
theorem B34770019 : Blo 1807605 34770019 := bstep (se 1 (by rfl) ⟨26077514, by rfl⟩ : syracuseStep 34770019 = 52155029) B52155029
theorem B13208827 : Blo 1807605 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B3051803 : Blo 1807605 3051803 := bstep (se 1 (by rfl) ⟨2288852, by rfl⟩ : syracuseStep 3051803 = 4577705) B4577705
theorem B78254687 : Blo 1807605 78254687 := bstep (se 1 (by rfl) ⟨58691015, by rfl⟩ : syracuseStep 78254687 = 117382031) B117382031
theorem B4067945 : Blo 1807605 4067945 := bstep (se 2 (by rfl) ⟨1525479, by rfl⟩ : syracuseStep 4067945 = 3050959) B3050959
theorem B4068287 : Blo 1807605 4068287 := bstep (se 1 (by rfl) ⟨3051215, by rfl⟩ : syracuseStep 4068287 = 6102431) B6102431
theorem B1807807 : Blo 1807605 1807807 := bstep (se 1 (by rfl) ⟨1355855, by rfl⟩ : syracuseStep 1807807 = 2711711) B2711711
theorem B6190607 : Blo 1807605 6190607 := bstep (se 1 (by rfl) ⟨4642955, by rfl⟩ : syracuseStep 6190607 = 9285911) B9285911
theorem B3257903 : Blo 1807605 3257903 := bstep (se 1 (by rfl) ⟨2443427, by rfl⟩ : syracuseStep 3257903 = 4886855) B4886855
theorem B22009481 : Blo 1807605 22009481 := bstep (se 2 (by rfl) ⟨8253555, by rfl⟩ : syracuseStep 22009481 = 16507111) B16507111
theorem B4577107 : Blo 1807605 4577107 := bstep (se 1 (by rfl) ⟨3432830, by rfl⟩ : syracuseStep 4577107 = 6865661) B6865661
theorem B23492737 : Blo 1807605 23492737 := bstep (se 2 (by rfl) ⟨8809776, by rfl⟩ : syracuseStep 23492737 = 17619553) B17619553
theorem B6101243 : Blo 1807605 6101243 := bstep (se 1 (by rfl) ⟨4575932, by rfl⟩ : syracuseStep 6101243 = 9151865) B9151865
theorem B19822877 : Blo 1807605 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B1808795 : Blo 1807605 1808795 := bstep (se 1 (by rfl) ⟨1356596, by rfl⟩ : syracuseStep 1808795 = 2713193) B2713193
theorem B29317625 : Blo 1807605 29317625 := bstep (se 2 (by rfl) ⟨10994109, by rfl⟩ : syracuseStep 29317625 = 21988219) B21988219
theorem B9157373 : Blo 1807605 9157373 := bstep (se 3 (by rfl) ⟨1717007, by rfl⟩ : syracuseStep 9157373 = 3434015) B3434015
theorem B14670679 : Blo 1807605 14670679 := bstep (se 1 (by rfl) ⟨11003009, by rfl⟩ : syracuseStep 14670679 = 22006019) B22006019
theorem B120560509 : Blo 1807605 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B7723937 : Blo 1807605 7723937 := bstep (se 2 (by rfl) ⟨2896476, by rfl⟩ : syracuseStep 7723937 = 5792953) B5792953
theorem B1932283 : Blo 1807605 1932283 := bstep (se 1 (by rfl) ⟨1449212, by rfl⟩ : syracuseStep 1932283 = 2898425) B2898425
theorem B4070483 : Blo 1807605 4070483 := bstep (se 1 (by rfl) ⟨3052862, by rfl⟩ : syracuseStep 4070483 = 6105725) B6105725
theorem B6519943 : Blo 1807605 6519943 := bstep (se 1 (by rfl) ⟨4889957, by rfl⟩ : syracuseStep 6519943 = 9779915) B9779915
theorem B1809599 : Blo 1807605 1809599 := bstep (se 1 (by rfl) ⟨1357199, by rfl⟩ : syracuseStep 1809599 = 2714399) B2714399
theorem B6102215 : Blo 1807605 6102215 := bstep (se 1 (by rfl) ⟨4576661, by rfl⟩ : syracuseStep 6102215 = 9153323) B9153323
theorem B17391161 : Blo 1807605 17391161 := bstep (se 2 (by rfl) ⟨6521685, by rfl⟩ : syracuseStep 17391161 = 13043371) B13043371
theorem B2711423 : Blo 1807605 2711423 := bstep (se 1 (by rfl) ⟨2033567, by rfl⟩ : syracuseStep 2711423 = 4067135) B4067135
theorem B2711963 : Blo 1807605 2711963 := bstep (se 1 (by rfl) ⟨2033972, by rfl⟩ : syracuseStep 2711963 = 4067945) B4067945
theorem B2712191 : Blo 1807605 2712191 := bstep (se 1 (by rfl) ⟨2034143, by rfl⟩ : syracuseStep 2712191 = 4068287) B4068287
theorem B2712233 : Blo 1807605 2712233 := bstep (se 2 (by rfl) ⟨1017087, by rfl⟩ : syracuseStep 2712233 = 2034175) B2034175
theorem B49496903 : Blo 1807605 49496903 := bstep (se 1 (by rfl) ⟨37122677, by rfl⟩ : syracuseStep 49496903 = 74245355) B74245355
theorem B2171935 : Blo 1807605 2171935 := bstep (se 1 (by rfl) ⟨1628951, by rfl⟩ : syracuseStep 2171935 = 3257903) B3257903
theorem B14672987 : Blo 1807605 14672987 := bstep (se 1 (by rfl) ⟨11004740, by rfl⟩ : syracuseStep 14672987 = 22009481) B22009481
theorem B46360025 : Blo 1807605 46360025 := bstep (se 2 (by rfl) ⟨17385009, by rfl⟩ : syracuseStep 46360025 = 34770019) B34770019
theorem B8693257 : Blo 1807605 8693257 := bstep (se 2 (by rfl) ⟨3259971, by rfl⟩ : syracuseStep 8693257 = 6519943) B6519943
theorem B13215251 : Blo 1807605 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B6104915 : Blo 1807605 6104915 := bstep (se 1 (by rfl) ⟨4578686, by rfl⟩ : syracuseStep 6104915 = 9157373) B9157373
theorem B2713655 : Blo 1807605 2713655 := bstep (se 1 (by rfl) ⟨2035241, by rfl⟩ : syracuseStep 2713655 = 4070483) B4070483
theorem B11594107 : Blo 1807605 11594107 := bstep (se 1 (by rfl) ⟨8695580, by rfl⟩ : syracuseStep 11594107 = 17391161) B17391161
theorem B20597165 : Blo 1807605 20597165 := bstep (se 3 (by rfl) ⟨3861968, by rfl⟩ : syracuseStep 20597165 = 7723937) B7723937
theorem B2714351 : Blo 1807605 2714351 := bstep (se 1 (by rfl) ⟨2035763, by rfl⟩ : syracuseStep 2714351 = 4071527) B4071527
theorem B2714363 : Blo 1807605 2714363 := bstep (se 1 (by rfl) ⟨2035772, by rfl⟩ : syracuseStep 2714363 = 4071545) B4071545
theorem B2034535 : Blo 1807605 2034535 := bstep (se 1 (by rfl) ⟨1525901, by rfl⟩ : syracuseStep 2034535 = 3051803) B3051803
theorem B52857737 : Blo 1807605 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B52169791 : Blo 1807605 52169791 := bstep (se 1 (by rfl) ⟨39127343, by rfl⟩ : syracuseStep 52169791 = 78254687) B78254687
theorem B2288731 : Blo 1807605 2288731 := bstep (se 1 (by rfl) ⟨1716548, by rfl⟩ : syracuseStep 2288731 = 3433097) B3433097
theorem B160747345 : Blo 1807605 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B2576377 : Blo 1807605 2576377 := bstep (se 2 (by rfl) ⟨966141, by rfl⟩ : syracuseStep 2576377 = 1932283) B1932283
theorem B4067495 : Blo 1807605 4067495 := bstep (se 1 (by rfl) ⟨3050621, by rfl⟩ : syracuseStep 4067495 = 6101243) B6101243
theorem B44577211 : Blo 1807605 44577211 := bstep (se 1 (by rfl) ⟨33432908, by rfl⟩ : syracuseStep 44577211 = 66865817) B66865817
theorem B24736427 : Blo 1807605 24736427 := bstep (se 1 (by rfl) ⟨18552320, by rfl⟩ : syracuseStep 24736427 = 37104641) B37104641
theorem B4068143 : Blo 1807605 4068143 := bstep (se 1 (by rfl) ⟨3051107, by rfl⟩ : syracuseStep 4068143 = 6102215) B6102215
theorem B1807615 : Blo 1807605 1807615 := bstep (se 1 (by rfl) ⟨1355711, by rfl⟩ : syracuseStep 1807615 = 2711423) B2711423
theorem B15455771 : Blo 1807605 15455771 := bstep (se 1 (by rfl) ⟨11591828, by rfl⟩ : syracuseStep 15455771 = 23183657) B23183657
theorem B1807999 : Blo 1807605 1807999 := bstep (se 1 (by rfl) ⟨1355999, by rfl⟩ : syracuseStep 1807999 = 2711999) B2711999
theorem B4127071 : Blo 1807605 4127071 := bstep (se 1 (by rfl) ⟨3095303, by rfl⟩ : syracuseStep 4127071 = 6190607) B6190607
theorem B1808383 : Blo 1807605 1808383 := bstep (se 1 (by rfl) ⟨1356287, by rfl⟩ : syracuseStep 1808383 = 2712575) B2712575
theorem B125294597 : Blo 1807605 125294597 := bstep (se 4 (by rfl) ⟨11746368, by rfl⟩ : syracuseStep 125294597 = 23492737) B23492737
theorem B1808551 : Blo 1807605 1808551 := bstep (se 1 (by rfl) ⟨1356413, by rfl⟩ : syracuseStep 1808551 = 2712827) B2712827
theorem B1808635 : Blo 1807605 1808635 := bstep (se 1 (by rfl) ⟨1356476, by rfl⟩ : syracuseStep 1808635 = 2712953) B2712953
theorem B19560905 : Blo 1807605 19560905 := bstep (se 2 (by rfl) ⟨7335339, by rfl⟩ : syracuseStep 19560905 = 14670679) B14670679
theorem B1809127 : Blo 1807605 1809127 := bstep (se 1 (by rfl) ⟨1356845, by rfl⟩ : syracuseStep 1809127 = 2713691) B2713691
theorem B1809215 : Blo 1807605 1809215 := bstep (se 1 (by rfl) ⟨1356911, by rfl⟩ : syracuseStep 1809215 = 2713823) B2713823
theorem B1809279 : Blo 1807605 1809279 := bstep (se 1 (by rfl) ⟨1356959, by rfl⟩ : syracuseStep 1809279 = 2713919) B2713919
theorem B7330799 : Blo 1807605 7330799 := bstep (se 1 (by rfl) ⟨5498099, by rfl⟩ : syracuseStep 7330799 = 10996199) B10996199
theorem B17611769 : Blo 1807605 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B19545083 : Blo 1807605 19545083 := bstep (se 1 (by rfl) ⟨14658812, by rfl⟩ : syracuseStep 19545083 = 29317625) B29317625
theorem B1809519 : Blo 1807605 1809519 := bstep (se 1 (by rfl) ⟨1357139, by rfl⟩ : syracuseStep 1809519 = 2714279) B2714279
theorem B6102809 : Blo 1807605 6102809 := bstep (se 2 (by rfl) ⟨2288553, by rfl⟩ : syracuseStep 6102809 = 4577107) B4577107
theorem B11591545 : Blo 1807605 11591545 := bstep (se 2 (by rfl) ⟨4346829, by rfl⟩ : syracuseStep 11591545 = 8693659) B8693659
theorem B2711663 : Blo 1807605 2711663 := bstep (se 1 (by rfl) ⟨2033747, by rfl⟩ : syracuseStep 2711663 = 4067495) B4067495
theorem B16490951 : Blo 1807605 16490951 := bstep (se 1 (by rfl) ⟨12368213, by rfl⟩ : syracuseStep 16490951 = 24736427) B24736427
theorem B15458809 : Blo 1807605 15458809 := bstep (se 2 (by rfl) ⟨5797053, by rfl⟩ : syracuseStep 15458809 = 11594107) B11594107
theorem B2712095 : Blo 1807605 2712095 := bstep (se 1 (by rfl) ⟨2034071, by rfl⟩ : syracuseStep 2712095 = 4068143) B4068143
theorem B32997935 : Blo 1807605 32997935 := bstep (se 1 (by rfl) ⟨24748451, by rfl⟩ : syracuseStep 32997935 = 49496903) B49496903
theorem B9781991 : Blo 1807605 9781991 := bstep (se 1 (by rfl) ⟨7336493, by rfl⟩ : syracuseStep 9781991 = 14672987) B14672987
theorem B2712713 : Blo 1807605 2712713 := bstep (se 2 (by rfl) ⟨1017267, by rfl⟩ : syracuseStep 2712713 = 2034535) B2034535
theorem B69559721 : Blo 1807605 69559721 := bstep (se 2 (by rfl) ⟨26084895, by rfl⟩ : syracuseStep 69559721 = 52169791) B52169791
theorem B13731443 : Blo 1807605 13731443 := bstep (se 1 (by rfl) ⟨10298582, by rfl⟩ : syracuseStep 13731443 = 20597165) B20597165
theorem B857319173 : Blo 1807605 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B13740677 : Blo 1807605 13740677 := bstep (se 4 (by rfl) ⟨1288188, by rfl⟩ : syracuseStep 13740677 = 2576377) B2576377
theorem B59436281 : Blo 1807605 59436281 := bstep (se 2 (by rfl) ⟨22288605, by rfl⟩ : syracuseStep 59436281 = 44577211) B44577211
theorem B8810167 : Blo 1807605 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B83529731 : Blo 1807605 83529731 := bstep (se 1 (by rfl) ⟨62647298, by rfl⟩ : syracuseStep 83529731 = 125294597) B125294597
theorem B2895913 : Blo 1807605 2895913 := bstep (se 2 (by rfl) ⟨1085967, by rfl⟩ : syracuseStep 2895913 = 2171935) B2171935
theorem B3051641 : Blo 1807605 3051641 := bstep (se 2 (by rfl) ⟨1144365, by rfl⟩ : syracuseStep 3051641 = 2288731) B2288731
theorem B35238491 : Blo 1807605 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B4887199 : Blo 1807605 4887199 := bstep (se 1 (by rfl) ⟨3665399, by rfl⟩ : syracuseStep 4887199 = 7330799) B7330799
theorem B13030055 : Blo 1807605 13030055 := bstep (se 1 (by rfl) ⟨9772541, by rfl⟩ : syracuseStep 13030055 = 19545083) B19545083
theorem B15455393 : Blo 1807605 15455393 := bstep (se 2 (by rfl) ⟨5795772, by rfl⟩ : syracuseStep 15455393 = 11591545) B11591545
theorem B4068539 : Blo 1807605 4068539 := bstep (se 1 (by rfl) ⟨3051404, by rfl⟩ : syracuseStep 4068539 = 6102809) B6102809
theorem B1807975 : Blo 1807605 1807975 := bstep (se 1 (by rfl) ⟨1355981, by rfl⟩ : syracuseStep 1807975 = 2711963) B2711963
theorem B1808127 : Blo 1807605 1808127 := bstep (se 1 (by rfl) ⟨1356095, by rfl⟩ : syracuseStep 1808127 = 2712191) B2712191
theorem B1808155 : Blo 1807605 1808155 := bstep (se 1 (by rfl) ⟨1356116, by rfl⟩ : syracuseStep 1808155 = 2712233) B2712233
theorem B5502761 : Blo 1807605 5502761 := bstep (se 2 (by rfl) ⟨2063535, by rfl⟩ : syracuseStep 5502761 = 4127071) B4127071
theorem B30906683 : Blo 1807605 30906683 := bstep (se 1 (by rfl) ⟨23180012, by rfl⟩ : syracuseStep 30906683 = 46360025) B46360025
theorem B10303847 : Blo 1807605 10303847 := bstep (se 1 (by rfl) ⟨7727885, by rfl⟩ : syracuseStep 10303847 = 15455771) B15455771
theorem B4069943 : Blo 1807605 4069943 := bstep (se 1 (by rfl) ⟨3052457, by rfl⟩ : syracuseStep 4069943 = 6104915) B6104915
theorem B1809103 : Blo 1807605 1809103 := bstep (se 1 (by rfl) ⟨1356827, by rfl⟩ : syracuseStep 1809103 = 2713655) B2713655
theorem B13040603 : Blo 1807605 13040603 := bstep (se 1 (by rfl) ⟨9780452, by rfl⟩ : syracuseStep 13040603 = 19560905) B19560905
theorem B1809567 : Blo 1807605 1809567 := bstep (se 1 (by rfl) ⟨1357175, by rfl⟩ : syracuseStep 1809567 = 2714351) B2714351
theorem B1809575 : Blo 1807605 1809575 := bstep (se 1 (by rfl) ⟨1357181, by rfl⟩ : syracuseStep 1809575 = 2714363) B2714363
theorem B11591009 : Blo 1807605 11591009 := bstep (se 2 (by rfl) ⟨4346628, by rfl⟩ : syracuseStep 11591009 = 8693257) B8693257
theorem B46964717 : Blo 1807605 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B10993967 : Blo 1807605 10993967 := bstep (se 1 (by rfl) ⟨8245475, by rfl⟩ : syracuseStep 10993967 = 16490951) B16490951
theorem B6521327 : Blo 1807605 6521327 := bstep (se 1 (by rfl) ⟨4890995, by rfl⟩ : syracuseStep 6521327 = 9781991) B9781991
theorem B20611745 : Blo 1807605 20611745 := bstep (se 2 (by rfl) ⟨7729404, by rfl⟩ : syracuseStep 20611745 = 15458809) B15458809
theorem B2712359 : Blo 1807605 2712359 := bstep (se 1 (by rfl) ⟨2034269, by rfl⟩ : syracuseStep 2712359 = 4068539) B4068539
theorem B20604455 : Blo 1807605 20604455 := bstep (se 1 (by rfl) ⟨15453341, by rfl⟩ : syracuseStep 20604455 = 30906683) B30906683
theorem B2713295 : Blo 1807605 2713295 := bstep (se 1 (by rfl) ⟨2034971, by rfl⟩ : syracuseStep 2713295 = 4069943) B4069943
theorem B9160451 : Blo 1807605 9160451 := bstep (se 1 (by rfl) ⟨6870338, by rfl⟩ : syracuseStep 9160451 = 13740677) B13740677
theorem B8693735 : Blo 1807605 8693735 := bstep (se 1 (by rfl) ⟨6520301, by rfl⟩ : syracuseStep 8693735 = 13040603) B13040603
theorem B7727339 : Blo 1807605 7727339 := bstep (se 1 (by rfl) ⟨5795504, by rfl⟩ : syracuseStep 7727339 = 11591009) B11591009
theorem B3861217 : Blo 1807605 3861217 := bstep (se 2 (by rfl) ⟨1447956, by rfl⟩ : syracuseStep 3861217 = 2895913) B2895913
theorem B2034427 : Blo 1807605 2034427 := bstep (se 1 (by rfl) ⟨1525820, by rfl⟩ : syracuseStep 2034427 = 3051641) B3051641
theorem B21998623 : Blo 1807605 21998623 := bstep (se 1 (by rfl) ⟨16498967, by rfl⟩ : syracuseStep 21998623 = 32997935) B32997935
theorem B8686703 : Blo 1807605 8686703 := bstep (se 1 (by rfl) ⟨6515027, by rfl⟩ : syracuseStep 8686703 = 13030055) B13030055
theorem B9154295 : Blo 1807605 9154295 := bstep (se 1 (by rfl) ⟨6865721, by rfl⟩ : syracuseStep 9154295 = 13731443) B13731443
theorem B6869231 : Blo 1807605 6869231 := bstep (se 1 (by rfl) ⟨5151923, by rfl⟩ : syracuseStep 6869231 = 10303847) B10303847
theorem B55686487 : Blo 1807605 55686487 := bstep (se 1 (by rfl) ⟨41764865, by rfl⟩ : syracuseStep 55686487 = 83529731) B83529731
theorem B1807775 : Blo 1807605 1807775 := bstep (se 1 (by rfl) ⟨1355831, by rfl⟩ : syracuseStep 1807775 = 2711663) B2711663
theorem B1808063 : Blo 1807605 1808063 := bstep (se 1 (by rfl) ⟨1356047, by rfl⟩ : syracuseStep 1808063 = 2712095) B2712095
theorem B23492327 : Blo 1807605 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B1808475 : Blo 1807605 1808475 := bstep (se 1 (by rfl) ⟨1356356, by rfl⟩ : syracuseStep 1808475 = 2712713) B2712713
theorem B10303595 : Blo 1807605 10303595 := bstep (se 1 (by rfl) ⟨7727696, by rfl⟩ : syracuseStep 10303595 = 15455393) B15455393
theorem B26065061 : Blo 1807605 26065061 := bstep (se 4 (by rfl) ⟨2443599, by rfl⟩ : syracuseStep 26065061 = 4887199) B4887199
theorem B46373147 : Blo 1807605 46373147 := bstep (se 1 (by rfl) ⟨34779860, by rfl⟩ : syracuseStep 46373147 = 69559721) B69559721
theorem B571546115 : Blo 1807605 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B3668507 : Blo 1807605 3668507 := bstep (se 1 (by rfl) ⟨2751380, by rfl⟩ : syracuseStep 3668507 = 5502761) B5502761
theorem B39624187 : Blo 1807605 39624187 := bstep (se 1 (by rfl) ⟨29718140, by rfl⟩ : syracuseStep 39624187 = 59436281) B59436281
theorem B11746889 : Blo 1807605 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B31309811 : Blo 1807605 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B4579487 : Blo 1807605 4579487 := bstep (se 1 (by rfl) ⟨3434615, by rfl⟩ : syracuseStep 4579487 = 6869231) B6869231
theorem B2712569 : Blo 1807605 2712569 := bstep (se 2 (by rfl) ⟨1017213, by rfl⟩ : syracuseStep 2712569 = 2034427) B2034427
theorem B17376707 : Blo 1807605 17376707 := bstep (se 1 (by rfl) ⟨13032530, by rfl⟩ : syracuseStep 17376707 = 26065061) B26065061
theorem B62646205 : Blo 1807605 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B52832249 : Blo 1807605 52832249 := bstep (se 2 (by rfl) ⟨19812093, by rfl⟩ : syracuseStep 52832249 = 39624187) B39624187
theorem B13741163 : Blo 1807605 13741163 := bstep (se 1 (by rfl) ⟨10305872, by rfl⟩ : syracuseStep 13741163 = 20611745) B20611745
theorem B5148289 : Blo 1807605 5148289 := bstep (se 2 (by rfl) ⟨1930608, by rfl⟩ : syracuseStep 5148289 = 3861217) B3861217
theorem B6106967 : Blo 1807605 6106967 := bstep (se 1 (by rfl) ⟨4580225, by rfl⟩ : syracuseStep 6106967 = 9160451) B9160451
theorem B29331497 : Blo 1807605 29331497 := bstep (se 2 (by rfl) ⟨10999311, by rfl⟩ : syracuseStep 29331497 = 21998623) B21998623
theorem B6869063 : Blo 1807605 6869063 := bstep (se 1 (by rfl) ⟨5151797, by rfl⟩ : syracuseStep 6869063 = 10303595) B10303595
theorem B381030743 : Blo 1807605 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B2445671 : Blo 1807605 2445671 := bstep (se 1 (by rfl) ⟨1834253, by rfl⟩ : syracuseStep 2445671 = 3668507) B3668507
theorem B74248649 : Blo 1807605 74248649 := bstep (se 2 (by rfl) ⟨27843243, by rfl⟩ : syracuseStep 74248649 = 55686487) B55686487
theorem B7329311 : Blo 1807605 7329311 := bstep (se 1 (by rfl) ⟨5496983, by rfl⟩ : syracuseStep 7329311 = 10993967) B10993967
theorem B4347551 : Blo 1807605 4347551 := bstep (se 1 (by rfl) ⟨3260663, by rfl⟩ : syracuseStep 4347551 = 6521327) B6521327
theorem B1808239 : Blo 1807605 1808239 := bstep (se 1 (by rfl) ⟨1356179, by rfl⟩ : syracuseStep 1808239 = 2712359) B2712359
theorem B13736303 : Blo 1807605 13736303 := bstep (se 1 (by rfl) ⟨10302227, by rfl⟩ : syracuseStep 13736303 = 20604455) B20604455
theorem B1808863 : Blo 1807605 1808863 := bstep (se 1 (by rfl) ⟨1356647, by rfl⟩ : syracuseStep 1808863 = 2713295) B2713295
theorem B5151559 : Blo 1807605 5151559 := bstep (se 1 (by rfl) ⟨3863669, by rfl⟩ : syracuseStep 5151559 = 7727339) B7727339
theorem B30915431 : Blo 1807605 30915431 := bstep (se 1 (by rfl) ⟨23186573, by rfl⟩ : syracuseStep 30915431 = 46373147) B46373147
theorem B5791135 : Blo 1807605 5791135 := bstep (se 1 (by rfl) ⟨4343351, by rfl⟩ : syracuseStep 5791135 = 8686703) B8686703
theorem B7831259 : Blo 1807605 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B6102863 : Blo 1807605 6102863 := bstep (se 1 (by rfl) ⟨4577147, by rfl⟩ : syracuseStep 6102863 = 9154295) B9154295
theorem B23183293 : Blo 1807605 23183293 := bstep (se 3 (by rfl) ⟨4346867, by rfl⟩ : syracuseStep 23183293 = 8693735) B8693735
theorem B20873207 : Blo 1807605 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B4579375 : Blo 1807605 4579375 := bstep (se 1 (by rfl) ⟨3434531, by rfl⟩ : syracuseStep 4579375 = 6869063) B6869063
theorem B78217325 : Blo 1807605 78217325 := bstep (se 3 (by rfl) ⟨14665748, by rfl⟩ : syracuseStep 78217325 = 29331497) B29331497
theorem B6521789 : Blo 1807605 6521789 := bstep (se 3 (by rfl) ⟨1222835, by rfl⟩ : syracuseStep 6521789 = 2445671) B2445671
theorem B11584471 : Blo 1807605 11584471 := bstep (se 1 (by rfl) ⟨8688353, by rfl⟩ : syracuseStep 11584471 = 17376707) B17376707
theorem B11593469 : Blo 1807605 11593469 := bstep (se 3 (by rfl) ⟨2173775, by rfl⟩ : syracuseStep 11593469 = 4347551) B4347551
theorem B9160775 : Blo 1807605 9160775 := bstep (se 1 (by rfl) ⟨6870581, by rfl⟩ : syracuseStep 9160775 = 13741163) B13741163
theorem B5220839 : Blo 1807605 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B83528273 : Blo 1807605 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B30911057 : Blo 1807605 30911057 := bstep (se 2 (by rfl) ⟨11591646, by rfl⟩ : syracuseStep 30911057 = 23183293) B23183293
theorem B254020495 : Blo 1807605 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B49499099 : Blo 1807605 49499099 := bstep (se 1 (by rfl) ⟨37124324, by rfl⟩ : syracuseStep 49499099 = 74248649) B74248649
theorem B4886207 : Blo 1807605 4886207 := bstep (se 1 (by rfl) ⟨3664655, by rfl⟩ : syracuseStep 4886207 = 7329311) B7329311
theorem B6868745 : Blo 1807605 6868745 := bstep (se 2 (by rfl) ⟨2575779, by rfl⟩ : syracuseStep 6868745 = 5151559) B5151559
theorem B35221499 : Blo 1807605 35221499 := bstep (se 1 (by rfl) ⟨26416124, by rfl⟩ : syracuseStep 35221499 = 52832249) B52832249
theorem B7721513 : Blo 1807605 7721513 := bstep (se 2 (by rfl) ⟨2895567, by rfl⟩ : syracuseStep 7721513 = 5791135) B5791135
theorem B4068575 : Blo 1807605 4068575 := bstep (se 1 (by rfl) ⟨3051431, by rfl⟩ : syracuseStep 4068575 = 6102863) B6102863
theorem B13915471 : Blo 1807605 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B3052991 : Blo 1807605 3052991 := bstep (se 1 (by rfl) ⟨2289743, by rfl⟩ : syracuseStep 3052991 = 4579487) B4579487
theorem B1808379 : Blo 1807605 1808379 := bstep (se 1 (by rfl) ⟨1356284, by rfl⟩ : syracuseStep 1808379 = 2712569) B2712569
theorem B9157535 : Blo 1807605 9157535 := bstep (se 1 (by rfl) ⟨6868151, by rfl⟩ : syracuseStep 9157535 = 13736303) B13736303
theorem B20610287 : Blo 1807605 20610287 := bstep (se 1 (by rfl) ⟨15457715, by rfl⟩ : syracuseStep 20610287 = 30915431) B30915431
theorem B6864385 : Blo 1807605 6864385 := bstep (se 2 (by rfl) ⟨2574144, by rfl⟩ : syracuseStep 6864385 = 5148289) B5148289
theorem B4071311 : Blo 1807605 4071311 := bstep (se 1 (by rfl) ⟨3053483, by rfl⟩ : syracuseStep 4071311 = 6106967) B6106967
theorem B2712383 : Blo 1807605 2712383 := bstep (se 1 (by rfl) ⟨2034287, by rfl⟩ : syracuseStep 2712383 = 4068575) B4068575
theorem B6105023 : Blo 1807605 6105023 := bstep (se 1 (by rfl) ⟨4578767, by rfl⟩ : syracuseStep 6105023 = 9157535) B9157535
theorem B32999399 : Blo 1807605 32999399 := bstep (se 1 (by rfl) ⟨24749549, by rfl⟩ : syracuseStep 32999399 = 49499099) B49499099
theorem B9152513 : Blo 1807605 9152513 := bstep (se 2 (by rfl) ⟨3432192, by rfl⟩ : syracuseStep 9152513 = 6864385) B6864385
theorem B13740191 : Blo 1807605 13740191 := bstep (se 1 (by rfl) ⟨10305143, by rfl⟩ : syracuseStep 13740191 = 20610287) B20610287
theorem B2714207 : Blo 1807605 2714207 := bstep (se 1 (by rfl) ⟨2035655, by rfl⟩ : syracuseStep 2714207 = 4071311) B4071311
theorem B23480999 : Blo 1807605 23480999 := bstep (se 1 (by rfl) ⟨17610749, by rfl⟩ : syracuseStep 23480999 = 35221499) B35221499
theorem B6105833 : Blo 1807605 6105833 := bstep (se 2 (by rfl) ⟨2289687, by rfl⟩ : syracuseStep 6105833 = 4579375) B4579375
theorem B52144883 : Blo 1807605 52144883 := bstep (se 1 (by rfl) ⟨39108662, by rfl⟩ : syracuseStep 52144883 = 78217325) B78217325
theorem B5147675 : Blo 1807605 5147675 := bstep (se 1 (by rfl) ⟨3860756, by rfl⟩ : syracuseStep 5147675 = 7721513) B7721513
theorem B2035327 : Blo 1807605 2035327 := bstep (se 1 (by rfl) ⟨1526495, by rfl⟩ : syracuseStep 2035327 = 3052991) B3052991
theorem B7728979 : Blo 1807605 7728979 := bstep (se 1 (by rfl) ⟨5796734, by rfl⟩ : syracuseStep 7728979 = 11593469) B11593469
theorem B338693993 : Blo 1807605 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B13922237 : Blo 1807605 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B15445961 : Blo 1807605 15445961 := bstep (se 2 (by rfl) ⟨5792235, by rfl⟩ : syracuseStep 15445961 = 11584471) B11584471
theorem B6107183 : Blo 1807605 6107183 := bstep (se 1 (by rfl) ⟨4580387, by rfl⟩ : syracuseStep 6107183 = 9160775) B9160775
theorem B55685515 : Blo 1807605 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B20607371 : Blo 1807605 20607371 := bstep (se 1 (by rfl) ⟨15455528, by rfl⟩ : syracuseStep 20607371 = 30911057) B30911057
theorem B3257471 : Blo 1807605 3257471 := bstep (se 1 (by rfl) ⟨2443103, by rfl⟩ : syracuseStep 3257471 = 4886207) B4886207
theorem B4347859 : Blo 1807605 4347859 := bstep (se 1 (by rfl) ⟨3260894, by rfl⟩ : syracuseStep 4347859 = 6521789) B6521789
theorem B18553961 : Blo 1807605 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B4579163 : Blo 1807605 4579163 := bstep (se 1 (by rfl) ⟨3434372, by rfl⟩ : syracuseStep 4579163 = 6868745) B6868745
theorem B4071455 : Blo 1807605 4071455 := bstep (se 1 (by rfl) ⟨3053591, by rfl⟩ : syracuseStep 4071455 = 6107183) B6107183
theorem B13738247 : Blo 1807605 13738247 := bstep (se 1 (by rfl) ⟨10303685, by rfl⟩ : syracuseStep 13738247 = 20607371) B20607371
theorem B2171647 : Blo 1807605 2171647 := bstep (se 1 (by rfl) ⟨1628735, by rfl⟩ : syracuseStep 2171647 = 3257471) B3257471
theorem B9160127 : Blo 1807605 9160127 := bstep (se 1 (by rfl) ⟨6870095, by rfl⟩ : syracuseStep 9160127 = 13740191) B13740191
theorem B2713769 : Blo 1807605 2713769 := bstep (se 2 (by rfl) ⟨1017663, by rfl⟩ : syracuseStep 2713769 = 2035327) B2035327
theorem B74247353 : Blo 1807605 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B21999599 : Blo 1807605 21999599 := bstep (se 1 (by rfl) ⟨16499699, by rfl⟩ : syracuseStep 21999599 = 32999399) B32999399
theorem B34763255 : Blo 1807605 34763255 := bstep (se 1 (by rfl) ⟨26072441, by rfl⟩ : syracuseStep 34763255 = 52144883) B52144883
theorem B3052775 : Blo 1807605 3052775 := bstep (se 1 (by rfl) ⟨2289581, by rfl⟩ : syracuseStep 3052775 = 4579163) B4579163
theorem B5797145 : Blo 1807605 5797145 := bstep (se 2 (by rfl) ⟨2173929, by rfl⟩ : syracuseStep 5797145 = 4347859) B4347859
theorem B1808255 : Blo 1807605 1808255 := bstep (se 1 (by rfl) ⟨1356191, by rfl⟩ : syracuseStep 1808255 = 2712383) B2712383
theorem B4070015 : Blo 1807605 4070015 := bstep (se 1 (by rfl) ⟨3052511, by rfl⟩ : syracuseStep 4070015 = 6105023) B6105023
theorem B6101675 : Blo 1807605 6101675 := bstep (se 1 (by rfl) ⟨4576256, by rfl⟩ : syracuseStep 6101675 = 9152513) B9152513
theorem B1809471 : Blo 1807605 1809471 := bstep (se 1 (by rfl) ⟨1357103, by rfl⟩ : syracuseStep 1809471 = 2714207) B2714207
theorem B15653999 : Blo 1807605 15653999 := bstep (se 1 (by rfl) ⟨11740499, by rfl⟩ : syracuseStep 15653999 = 23480999) B23480999
theorem B4070555 : Blo 1807605 4070555 := bstep (se 1 (by rfl) ⟨3052916, by rfl⟩ : syracuseStep 4070555 = 6105833) B6105833
theorem B3431783 : Blo 1807605 3431783 := bstep (se 1 (by rfl) ⟨2573837, by rfl⟩ : syracuseStep 3431783 = 5147675) B5147675
theorem B12369307 : Blo 1807605 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B10305305 : Blo 1807605 10305305 := bstep (se 2 (by rfl) ⟨3864489, by rfl⟩ : syracuseStep 10305305 = 7728979) B7728979
theorem B37125965 : Blo 1807605 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B225795995 : Blo 1807605 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B10297307 : Blo 1807605 10297307 := bstep (se 1 (by rfl) ⟨7722980, by rfl⟩ : syracuseStep 10297307 = 15445961) B15445961
theorem B9158831 : Blo 1807605 9158831 := bstep (se 1 (by rfl) ⟨6869123, by rfl⟩ : syracuseStep 9158831 = 13738247) B13738247
theorem B23175503 : Blo 1807605 23175503 := bstep (se 1 (by rfl) ⟨17381627, by rfl⟩ : syracuseStep 23175503 = 34763255) B34763255
theorem B2713343 : Blo 1807605 2713343 := bstep (se 1 (by rfl) ⟨2035007, by rfl⟩ : syracuseStep 2713343 = 4070015) B4070015
theorem B16492409 : Blo 1807605 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B2713703 : Blo 1807605 2713703 := bstep (se 1 (by rfl) ⟨2035277, by rfl⟩ : syracuseStep 2713703 = 4070555) B4070555
theorem B49498235 : Blo 1807605 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B99002573 : Blo 1807605 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B2287855 : Blo 1807605 2287855 := bstep (se 1 (by rfl) ⟨1715891, by rfl⟩ : syracuseStep 2287855 = 3431783) B3431783
theorem B150530663 : Blo 1807605 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B14666399 : Blo 1807605 14666399 := bstep (se 1 (by rfl) ⟨10999799, by rfl⟩ : syracuseStep 14666399 = 21999599) B21999599
theorem B2714303 : Blo 1807605 2714303 := bstep (se 1 (by rfl) ⟨2035727, by rfl⟩ : syracuseStep 2714303 = 4071455) B4071455
theorem B2035183 : Blo 1807605 2035183 := bstep (se 1 (by rfl) ⟨1526387, by rfl⟩ : syracuseStep 2035183 = 3052775) B3052775
theorem B6106751 : Blo 1807605 6106751 := bstep (se 1 (by rfl) ⟨4580063, by rfl⟩ : syracuseStep 6106751 = 9160127) B9160127
theorem B2895529 : Blo 1807605 2895529 := bstep (se 2 (by rfl) ⟨1085823, by rfl⟩ : syracuseStep 2895529 = 2171647) B2171647
theorem B4067783 : Blo 1807605 4067783 := bstep (se 1 (by rfl) ⟨3050837, by rfl⟩ : syracuseStep 4067783 = 6101675) B6101675
theorem B6870203 : Blo 1807605 6870203 := bstep (se 1 (by rfl) ⟨5152652, by rfl⟩ : syracuseStep 6870203 = 10305305) B10305305
theorem B41743997 : Blo 1807605 41743997 := bstep (se 3 (by rfl) ⟨7826999, by rfl⟩ : syracuseStep 41743997 = 15653999) B15653999
theorem B3864763 : Blo 1807605 3864763 := bstep (se 1 (by rfl) ⟨2898572, by rfl⟩ : syracuseStep 3864763 = 5797145) B5797145
theorem B1809179 : Blo 1807605 1809179 := bstep (se 1 (by rfl) ⟨1356884, by rfl⟩ : syracuseStep 1809179 = 2713769) B2713769
theorem B6864871 : Blo 1807605 6864871 := bstep (se 1 (by rfl) ⟨5148653, by rfl⟩ : syracuseStep 6864871 = 10297307) B10297307
theorem B15450335 : Blo 1807605 15450335 := bstep (se 1 (by rfl) ⟨11587751, by rfl⟩ : syracuseStep 15450335 = 23175503) B23175503
theorem B5153017 : Blo 1807605 5153017 := bstep (se 2 (by rfl) ⟨1932381, by rfl⟩ : syracuseStep 5153017 = 3864763) B3864763
theorem B2711855 : Blo 1807605 2711855 := bstep (se 1 (by rfl) ⟨2033891, by rfl⟩ : syracuseStep 2711855 = 4067783) B4067783
theorem B4580135 : Blo 1807605 4580135 := bstep (se 1 (by rfl) ⟨3435101, by rfl⟩ : syracuseStep 4580135 = 6870203) B6870203
theorem B27829331 : Blo 1807605 27829331 := bstep (se 1 (by rfl) ⟨20871998, by rfl⟩ : syracuseStep 27829331 = 41743997) B41743997
theorem B10994939 : Blo 1807605 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B32998823 : Blo 1807605 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B2713577 : Blo 1807605 2713577 := bstep (se 2 (by rfl) ⟨1017591, by rfl⟩ : syracuseStep 2713577 = 2035183) B2035183
theorem B3860705 : Blo 1807605 3860705 := bstep (se 2 (by rfl) ⟨1447764, by rfl⟩ : syracuseStep 3860705 = 2895529) B2895529
theorem B9153161 : Blo 1807605 9153161 := bstep (se 2 (by rfl) ⟨3432435, by rfl⟩ : syracuseStep 9153161 = 6864871) B6864871
theorem B6105887 : Blo 1807605 6105887 := bstep (se 1 (by rfl) ⟨4579415, by rfl⟩ : syracuseStep 6105887 = 9158831) B9158831
theorem B3050473 : Blo 1807605 3050473 := bstep (se 2 (by rfl) ⟨1143927, by rfl⟩ : syracuseStep 3050473 = 2287855) B2287855
theorem B9777599 : Blo 1807605 9777599 := bstep (se 1 (by rfl) ⟨7333199, by rfl⟩ : syracuseStep 9777599 = 14666399) B14666399
theorem B1808895 : Blo 1807605 1808895 := bstep (se 1 (by rfl) ⟨1356671, by rfl⟩ : syracuseStep 1808895 = 2713343) B2713343
theorem B1809135 : Blo 1807605 1809135 := bstep (se 1 (by rfl) ⟨1356851, by rfl⟩ : syracuseStep 1809135 = 2713703) B2713703
theorem B66001715 : Blo 1807605 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B401415101 : Blo 1807605 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B1809535 : Blo 1807605 1809535 := bstep (se 1 (by rfl) ⟨1357151, by rfl⟩ : syracuseStep 1809535 = 2714303) B2714303
theorem B4071167 : Blo 1807605 4071167 := bstep (se 1 (by rfl) ⟨3053375, by rfl⟩ : syracuseStep 4071167 = 6106751) B6106751
theorem B2573803 : Blo 1807605 2573803 := bstep (se 1 (by rfl) ⟨1930352, by rfl⟩ : syracuseStep 2573803 = 3860705) B3860705
theorem B44001143 : Blo 1807605 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B267610067 : Blo 1807605 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B2714111 : Blo 1807605 2714111 := bstep (se 1 (by rfl) ⟨2035583, by rfl⟩ : syracuseStep 2714111 = 4071167) B4071167
theorem B10300223 : Blo 1807605 10300223 := bstep (se 1 (by rfl) ⟨7725167, by rfl⟩ : syracuseStep 10300223 = 15450335) B15450335
theorem B21999215 : Blo 1807605 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B4067297 : Blo 1807605 4067297 := bstep (se 2 (by rfl) ⟨1525236, by rfl⟩ : syracuseStep 4067297 = 3050473) B3050473
theorem B1807903 : Blo 1807605 1807903 := bstep (se 1 (by rfl) ⟨1355927, by rfl⟩ : syracuseStep 1807903 = 2711855) B2711855
theorem B6518399 : Blo 1807605 6518399 := bstep (se 1 (by rfl) ⟨4888799, by rfl⟩ : syracuseStep 6518399 = 9777599) B9777599
theorem B6870689 : Blo 1807605 6870689 := bstep (se 2 (by rfl) ⟨2576508, by rfl⟩ : syracuseStep 6870689 = 5153017) B5153017
theorem B3053423 : Blo 1807605 3053423 := bstep (se 1 (by rfl) ⟨2290067, by rfl⟩ : syracuseStep 3053423 = 4580135) B4580135
theorem B18552887 : Blo 1807605 18552887 := bstep (se 1 (by rfl) ⟨13914665, by rfl⟩ : syracuseStep 18552887 = 27829331) B27829331
theorem B7329959 : Blo 1807605 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B1809051 : Blo 1807605 1809051 := bstep (se 1 (by rfl) ⟨1356788, by rfl⟩ : syracuseStep 1809051 = 2713577) B2713577
theorem B6102107 : Blo 1807605 6102107 := bstep (se 1 (by rfl) ⟨4576580, by rfl⟩ : syracuseStep 6102107 = 9153161) B9153161
theorem B4070591 : Blo 1807605 4070591 := bstep (se 1 (by rfl) ⟨3052943, by rfl⟩ : syracuseStep 4070591 = 6105887) B6105887
theorem B4580459 : Blo 1807605 4580459 := bstep (se 1 (by rfl) ⟨3435344, by rfl⟩ : syracuseStep 4580459 = 6870689) B6870689
theorem B178406711 : Blo 1807605 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B6866815 : Blo 1807605 6866815 := bstep (se 1 (by rfl) ⟨5150111, by rfl⟩ : syracuseStep 6866815 = 10300223) B10300223
theorem B2713727 : Blo 1807605 2713727 := bstep (se 1 (by rfl) ⟨2035295, by rfl⟩ : syracuseStep 2713727 = 4070591) B4070591
theorem B14666143 : Blo 1807605 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B2035615 : Blo 1807605 2035615 := bstep (se 1 (by rfl) ⟨1526711, by rfl⟩ : syracuseStep 2035615 = 3053423) B3053423
theorem B4886639 : Blo 1807605 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B4068071 : Blo 1807605 4068071 := bstep (se 1 (by rfl) ⟨3051053, by rfl⟩ : syracuseStep 4068071 = 6102107) B6102107
theorem B29334095 : Blo 1807605 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B12368591 : Blo 1807605 12368591 := bstep (se 1 (by rfl) ⟨9276443, by rfl⟩ : syracuseStep 12368591 = 18552887) B18552887
theorem B17382397 : Blo 1807605 17382397 := bstep (se 3 (by rfl) ⟨3259199, by rfl⟩ : syracuseStep 17382397 = 6518399) B6518399
theorem B1809407 : Blo 1807605 1809407 := bstep (se 1 (by rfl) ⟨1357055, by rfl⟩ : syracuseStep 1809407 = 2714111) B2714111
theorem B3431737 : Blo 1807605 3431737 := bstep (se 2 (by rfl) ⟨1286901, by rfl⟩ : syracuseStep 3431737 = 2573803) B2573803
theorem B2711531 : Blo 1807605 2711531 := bstep (se 1 (by rfl) ⟨2033648, by rfl⟩ : syracuseStep 2711531 = 4067297) B4067297
theorem B2712047 : Blo 1807605 2712047 := bstep (se 1 (by rfl) ⟨2034035, by rfl⟩ : syracuseStep 2712047 = 4068071) B4068071
theorem B19554857 : Blo 1807605 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B23176529 : Blo 1807605 23176529 := bstep (se 2 (by rfl) ⟨8691198, by rfl⟩ : syracuseStep 23176529 = 17382397) B17382397
theorem B19556063 : Blo 1807605 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B2714153 : Blo 1807605 2714153 := bstep (se 2 (by rfl) ⟨1017807, by rfl⟩ : syracuseStep 2714153 = 2035615) B2035615
theorem B4575649 : Blo 1807605 4575649 := bstep (se 2 (by rfl) ⟨1715868, by rfl⟩ : syracuseStep 4575649 = 3431737) B3431737
theorem B8245727 : Blo 1807605 8245727 := bstep (se 1 (by rfl) ⟨6184295, by rfl⟩ : syracuseStep 8245727 = 12368591) B12368591
theorem B9155753 : Blo 1807605 9155753 := bstep (se 2 (by rfl) ⟨3433407, by rfl⟩ : syracuseStep 9155753 = 6866815) B6866815
theorem B1807687 : Blo 1807605 1807687 := bstep (se 1 (by rfl) ⟨1355765, by rfl⟩ : syracuseStep 1807687 = 2711531) B2711531
theorem B3257759 : Blo 1807605 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B3053639 : Blo 1807605 3053639 := bstep (se 1 (by rfl) ⟨2290229, by rfl⟩ : syracuseStep 3053639 = 4580459) B4580459
theorem B118937807 : Blo 1807605 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B1809151 : Blo 1807605 1809151 := bstep (se 1 (by rfl) ⟨1356863, by rfl⟩ : syracuseStep 1809151 = 2713727) B2713727
theorem B5497151 : Blo 1807605 5497151 := bstep (se 1 (by rfl) ⟨4122863, by rfl⟩ : syracuseStep 5497151 = 8245727) B8245727
theorem B6103835 : Blo 1807605 6103835 := bstep (se 1 (by rfl) ⟨4577876, by rfl⟩ : syracuseStep 6103835 = 9155753) B9155753
theorem B15451019 : Blo 1807605 15451019 := bstep (se 1 (by rfl) ⟨11588264, by rfl⟩ : syracuseStep 15451019 = 23176529) B23176529
theorem B79291871 : Blo 1807605 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B13036571 : Blo 1807605 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B8687357 : Blo 1807605 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B13037375 : Blo 1807605 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B2035759 : Blo 1807605 2035759 := bstep (se 1 (by rfl) ⟨1526819, by rfl⟩ : syracuseStep 2035759 = 3053639) B3053639
theorem B1808031 : Blo 1807605 1808031 := bstep (se 1 (by rfl) ⟨1356023, by rfl⟩ : syracuseStep 1808031 = 2712047) B2712047
theorem B6100865 : Blo 1807605 6100865 := bstep (se 2 (by rfl) ⟨2287824, by rfl⟩ : syracuseStep 6100865 = 4575649) B4575649
theorem B1809435 : Blo 1807605 1809435 := bstep (se 1 (by rfl) ⟨1357076, by rfl⟩ : syracuseStep 1809435 = 2714153) B2714153
theorem B2714345 : Blo 1807605 2714345 := bstep (se 2 (by rfl) ⟨1017879, by rfl⟩ : syracuseStep 2714345 = 2035759) B2035759
theorem B10300679 : Blo 1807605 10300679 := bstep (se 1 (by rfl) ⟨7725509, by rfl⟩ : syracuseStep 10300679 = 15451019) B15451019
theorem B14659069 : Blo 1807605 14659069 := bstep (se 3 (by rfl) ⟨2748575, by rfl⟩ : syracuseStep 14659069 = 5497151) B5497151
theorem B4067243 : Blo 1807605 4067243 := bstep (se 1 (by rfl) ⟨3050432, by rfl⟩ : syracuseStep 4067243 = 6100865) B6100865
theorem B4069223 : Blo 1807605 4069223 := bstep (se 1 (by rfl) ⟨3051917, by rfl⟩ : syracuseStep 4069223 = 6103835) B6103835
theorem B52861247 : Blo 1807605 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B8691047 : Blo 1807605 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B5791571 : Blo 1807605 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B8691583 : Blo 1807605 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B2712815 : Blo 1807605 2712815 := bstep (se 1 (by rfl) ⟨2034611, by rfl⟩ : syracuseStep 2712815 = 4069223) B4069223
theorem B6867119 : Blo 1807605 6867119 := bstep (se 1 (by rfl) ⟨5150339, by rfl⟩ : syracuseStep 6867119 = 10300679) B10300679
theorem B5794031 : Blo 1807605 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B3861047 : Blo 1807605 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B11588777 : Blo 1807605 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B35240831 : Blo 1807605 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B1809563 : Blo 1807605 1809563 := bstep (se 1 (by rfl) ⟨1357172, by rfl⟩ : syracuseStep 1809563 = 2714345) B2714345
theorem B19545425 : Blo 1807605 19545425 := bstep (se 2 (by rfl) ⟨7329534, by rfl⟩ : syracuseStep 19545425 = 14659069) B14659069
theorem B2711495 : Blo 1807605 2711495 := bstep (se 1 (by rfl) ⟨2033621, by rfl⟩ : syracuseStep 2711495 = 4067243) B4067243
theorem B7725851 : Blo 1807605 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B2574031 : Blo 1807605 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B3862687 : Blo 1807605 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B13030283 : Blo 1807605 13030283 := bstep (se 1 (by rfl) ⟨9772712, by rfl⟩ : syracuseStep 13030283 = 19545425) B19545425
theorem B1807663 : Blo 1807605 1807663 := bstep (se 1 (by rfl) ⟨1355747, by rfl⟩ : syracuseStep 1807663 = 2711495) B2711495
theorem B1808543 : Blo 1807605 1808543 := bstep (se 1 (by rfl) ⟨1356407, by rfl⟩ : syracuseStep 1808543 = 2712815) B2712815
theorem B4578079 : Blo 1807605 4578079 := bstep (se 1 (by rfl) ⟨3433559, by rfl⟩ : syracuseStep 4578079 = 6867119) B6867119
theorem B23493887 : Blo 1807605 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B6104105 : Blo 1807605 6104105 := bstep (se 2 (by rfl) ⟨2289039, by rfl⟩ : syracuseStep 6104105 = 4578079) B4578079
theorem B8686855 : Blo 1807605 8686855 := bstep (se 1 (by rfl) ⟨6515141, by rfl⟩ : syracuseStep 8686855 = 13030283) B13030283
theorem B5150249 : Blo 1807605 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B5150567 : Blo 1807605 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B15662591 : Blo 1807605 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B3432041 : Blo 1807605 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B3433499 : Blo 1807605 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B2288027 : Blo 1807605 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B13734845 : Blo 1807605 13734845 := bstep (se 3 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 13734845 = 5150567) B5150567
theorem B10441727 : Blo 1807605 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B4069403 : Blo 1807605 4069403 := bstep (se 1 (by rfl) ⟨3052052, by rfl⟩ : syracuseStep 4069403 = 6104105) B6104105
theorem B11582473 : Blo 1807605 11582473 := bstep (se 2 (by rfl) ⟨4343427, by rfl⟩ : syracuseStep 11582473 = 8686855) B8686855
theorem B15443297 : Blo 1807605 15443297 := bstep (se 2 (by rfl) ⟨5791236, by rfl⟩ : syracuseStep 15443297 = 11582473) B11582473
theorem B2712935 : Blo 1807605 2712935 := bstep (se 1 (by rfl) ⟨2034701, by rfl⟩ : syracuseStep 2712935 = 4069403) B4069403
theorem B2288999 : Blo 1807605 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B9156563 : Blo 1807605 9156563 := bstep (se 1 (by rfl) ⟨6867422, by rfl⟩ : syracuseStep 9156563 = 13734845) B13734845
theorem B6961151 : Blo 1807605 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B6101405 : Blo 1807605 6101405 := bstep (se 3 (by rfl) ⟨1144013, by rfl⟩ : syracuseStep 6101405 = 2288027) B2288027
theorem B6103997 : Blo 1807605 6103997 := bstep (se 3 (by rfl) ⟨1144499, by rfl⟩ : syracuseStep 6103997 = 2288999) B2288999
theorem B6104375 : Blo 1807605 6104375 := bstep (se 1 (by rfl) ⟨4578281, by rfl⟩ : syracuseStep 6104375 = 9156563) B9156563
theorem B4067603 : Blo 1807605 4067603 := bstep (se 1 (by rfl) ⟨3050702, by rfl⟩ : syracuseStep 4067603 = 6101405) B6101405
theorem B10295531 : Blo 1807605 10295531 := bstep (se 1 (by rfl) ⟨7721648, by rfl⟩ : syracuseStep 10295531 = 15443297) B15443297
theorem B1808623 : Blo 1807605 1808623 := bstep (se 1 (by rfl) ⟨1356467, by rfl⟩ : syracuseStep 1808623 = 2712935) B2712935
theorem B18563069 : Blo 1807605 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B2711735 : Blo 1807605 2711735 := bstep (se 1 (by rfl) ⟨2033801, by rfl⟩ : syracuseStep 2711735 = 4067603) B4067603
theorem B12375379 : Blo 1807605 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B4069331 : Blo 1807605 4069331 := bstep (se 1 (by rfl) ⟨3051998, by rfl⟩ : syracuseStep 4069331 = 6103997) B6103997
theorem B4069583 : Blo 1807605 4069583 := bstep (se 1 (by rfl) ⟨3052187, by rfl⟩ : syracuseStep 4069583 = 6104375) B6104375
theorem B6863687 : Blo 1807605 6863687 := bstep (se 1 (by rfl) ⟨5147765, by rfl⟩ : syracuseStep 6863687 = 10295531) B10295531
theorem B2712887 : Blo 1807605 2712887 := bstep (se 1 (by rfl) ⟨2034665, by rfl⟩ : syracuseStep 2712887 = 4069331) B4069331
theorem B2713055 : Blo 1807605 2713055 := bstep (se 1 (by rfl) ⟨2034791, by rfl⟩ : syracuseStep 2713055 = 4069583) B4069583
theorem B16500505 : Blo 1807605 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B4575791 : Blo 1807605 4575791 := bstep (se 1 (by rfl) ⟨3431843, by rfl⟩ : syracuseStep 4575791 = 6863687) B6863687
theorem B1807823 : Blo 1807605 1807823 := bstep (se 1 (by rfl) ⟨1355867, by rfl⟩ : syracuseStep 1807823 = 2711735) B2711735
theorem B3050527 : Blo 1807605 3050527 := bstep (se 1 (by rfl) ⟨2287895, by rfl⟩ : syracuseStep 3050527 = 4575791) B4575791
theorem B22000673 : Blo 1807605 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B1808591 : Blo 1807605 1808591 := bstep (se 1 (by rfl) ⟨1356443, by rfl⟩ : syracuseStep 1808591 = 2712887) B2712887
theorem B1808703 : Blo 1807605 1808703 := bstep (se 1 (by rfl) ⟨1356527, by rfl⟩ : syracuseStep 1808703 = 2713055) B2713055
theorem B4067369 : Blo 1807605 4067369 := bstep (se 2 (by rfl) ⟨1525263, by rfl⟩ : syracuseStep 4067369 = 3050527) B3050527
theorem B58668461 : Blo 1807605 58668461 := bstep (se 3 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 58668461 = 22000673) B22000673
theorem B2711579 : Blo 1807605 2711579 := bstep (se 1 (by rfl) ⟨2033684, by rfl⟩ : syracuseStep 2711579 = 4067369) B4067369
theorem B39112307 : Blo 1807605 39112307 := bstep (se 1 (by rfl) ⟨29334230, by rfl⟩ : syracuseStep 39112307 = 58668461) B58668461
theorem B1807719 : Blo 1807605 1807719 := bstep (se 1 (by rfl) ⟨1355789, by rfl⟩ : syracuseStep 1807719 = 2711579) B2711579
theorem B26074871 : Blo 1807605 26074871 := bstep (se 1 (by rfl) ⟨19556153, by rfl⟩ : syracuseStep 26074871 = 39112307) B39112307
theorem B17383247 : Blo 1807605 17383247 := bstep (se 1 (by rfl) ⟨13037435, by rfl⟩ : syracuseStep 17383247 = 26074871) B26074871
theorem B11588831 : Blo 1807605 11588831 := bstep (se 1 (by rfl) ⟨8691623, by rfl⟩ : syracuseStep 11588831 = 17383247) B17383247
theorem B7725887 : Blo 1807605 7725887 := bstep (se 1 (by rfl) ⟨5794415, by rfl⟩ : syracuseStep 7725887 = 11588831) B11588831
theorem B5150591 : Blo 1807605 5150591 := bstep (se 1 (by rfl) ⟨3862943, by rfl⟩ : syracuseStep 5150591 = 7725887) B7725887
theorem B3433727 : Blo 1807605 3433727 := bstep (se 1 (by rfl) ⟨2575295, by rfl⟩ : syracuseStep 3433727 = 5150591) B5150591
theorem B2289151 : Blo 1807605 2289151 := bstep (se 1 (by rfl) ⟨1716863, by rfl⟩ : syracuseStep 2289151 = 3433727) B3433727
theorem B3052201 : Blo 1807605 3052201 := bstep (se 2 (by rfl) ⟨1144575, by rfl⟩ : syracuseStep 3052201 = 2289151) B2289151
theorem B4069601 : Blo 1807605 4069601 := bstep (se 2 (by rfl) ⟨1526100, by rfl⟩ : syracuseStep 4069601 = 3052201) B3052201
theorem B2713067 : Blo 1807605 2713067 := bstep (se 1 (by rfl) ⟨2034800, by rfl⟩ : syracuseStep 2713067 = 4069601) B4069601
theorem B1808711 : Blo 1807605 1808711 := bstep (se 1 (by rfl) ⟨1356533, by rfl⟩ : syracuseStep 1808711 = 2713067) B2713067

theorem C0 (j : ℕ) (h1 : 451901 ≤ j) (h2 : j ≤ 452400) : Blo 1807605 (4 * j + 3) := by
  interval_cases j
  · exact B1807607
  · exact B1807611
  · exact B1807615
  · exact B1807619
  · exact B1807623
  · exact B1807627
  · exact B1807631
  · exact B1807635
  · exact B1807639
  · exact B1807643
  · exact B1807647
  · exact B1807651
  · exact B1807655
  · exact B1807659
  · exact B1807663
  · exact B1807667
  · exact B1807671
  · exact B1807675
  · exact B1807679
  · exact B1807683
  · exact B1807687
  · exact B1807691
  · exact B1807695
  · exact B1807699
  · exact B1807703
  · exact B1807707
  · exact B1807711
  · exact B1807715
  · exact B1807719
  · exact B1807723
  · exact B1807727
  · exact B1807731
  · exact B1807735
  · exact B1807739
  · exact B1807743
  · exact B1807747
  · exact B1807751
  · exact B1807755
  · exact B1807759
  · exact B1807763
  · exact B1807767
  · exact B1807771
  · exact B1807775
  · exact B1807779
  · exact B1807783
  · exact B1807787
  · exact B1807791
  · exact B1807795
  · exact B1807799
  · exact B1807803
  · exact B1807807
  · exact B1807811
  · exact B1807815
  · exact B1807819
  · exact B1807823
  · exact B1807827
  · exact B1807831
  · exact B1807835
  · exact B1807839
  · exact B1807843
  · exact B1807847
  · exact B1807851
  · exact B1807855
  · exact B1807859
  · exact B1807863
  · exact B1807867
  · exact B1807871
  · exact B1807875
  · exact B1807879
  · exact B1807883
  · exact B1807887
  · exact B1807891
  · exact B1807895
  · exact B1807899
  · exact B1807903
  · exact B1807907
  · exact B1807911
  · exact B1807915
  · exact B1807919
  · exact B1807923
  · exact B1807927
  · exact B1807931
  · exact B1807935
  · exact B1807939
  · exact B1807943
  · exact B1807947
  · exact B1807951
  · exact B1807955
  · exact B1807959
  · exact B1807963
  · exact B1807967
  · exact B1807971
  · exact B1807975
  · exact B1807979
  · exact B1807983
  · exact B1807987
  · exact B1807991
  · exact B1807995
  · exact B1807999
  · exact B1808003
  · exact B1808007
  · exact B1808011
  · exact B1808015
  · exact B1808019
  · exact B1808023
  · exact B1808027
  · exact B1808031
  · exact B1808035
  · exact B1808039
  · exact B1808043
  · exact B1808047
  · exact B1808051
  · exact B1808055
  · exact B1808059
  · exact B1808063
  · exact B1808067
  · exact B1808071
  · exact B1808075
  · exact B1808079
  · exact B1808083
  · exact B1808087
  · exact B1808091
  · exact B1808095
  · exact B1808099
  · exact B1808103
  · exact B1808107
  · exact B1808111
  · exact B1808115
  · exact B1808119
  · exact B1808123
  · exact B1808127
  · exact B1808131
  · exact B1808135
  · exact B1808139
  · exact B1808143
  · exact B1808147
  · exact B1808151
  · exact B1808155
  · exact B1808159
  · exact B1808163
  · exact B1808167
  · exact B1808171
  · exact B1808175
  · exact B1808179
  · exact B1808183
  · exact B1808187
  · exact B1808191
  · exact B1808195
  · exact B1808199
  · exact B1808203
  · exact B1808207
  · exact B1808211
  · exact B1808215
  · exact B1808219
  · exact B1808223
  · exact B1808227
  · exact B1808231
  · exact B1808235
  · exact B1808239
  · exact B1808243
  · exact B1808247
  · exact B1808251
  · exact B1808255
  · exact B1808259
  · exact B1808263
  · exact B1808267
  · exact B1808271
  · exact B1808275
  · exact B1808279
  · exact B1808283
  · exact B1808287
  · exact B1808291
  · exact B1808295
  · exact B1808299
  · exact B1808303
  · exact B1808307
  · exact B1808311
  · exact B1808315
  · exact B1808319
  · exact B1808323
  · exact B1808327
  · exact B1808331
  · exact B1808335
  · exact B1808339
  · exact B1808343
  · exact B1808347
  · exact B1808351
  · exact B1808355
  · exact B1808359
  · exact B1808363
  · exact B1808367
  · exact B1808371
  · exact B1808375
  · exact B1808379
  · exact B1808383
  · exact B1808387
  · exact B1808391
  · exact B1808395
  · exact B1808399
  · exact B1808403
  · exact B1808407
  · exact B1808411
  · exact B1808415
  · exact B1808419
  · exact B1808423
  · exact B1808427
  · exact B1808431
  · exact B1808435
  · exact B1808439
  · exact B1808443
  · exact B1808447
  · exact B1808451
  · exact B1808455
  · exact B1808459
  · exact B1808463
  · exact B1808467
  · exact B1808471
  · exact B1808475
  · exact B1808479
  · exact B1808483
  · exact B1808487
  · exact B1808491
  · exact B1808495
  · exact B1808499
  · exact B1808503
  · exact B1808507
  · exact B1808511
  · exact B1808515
  · exact B1808519
  · exact B1808523
  · exact B1808527
  · exact B1808531
  · exact B1808535
  · exact B1808539
  · exact B1808543
  · exact B1808547
  · exact B1808551
  · exact B1808555
  · exact B1808559
  · exact B1808563
  · exact B1808567
  · exact B1808571
  · exact B1808575
  · exact B1808579
  · exact B1808583
  · exact B1808587
  · exact B1808591
  · exact B1808595
  · exact B1808599
  · exact B1808603
  · exact B1808607
  · exact B1808611
  · exact B1808615
  · exact B1808619
  · exact B1808623
  · exact B1808627
  · exact B1808631
  · exact B1808635
  · exact B1808639
  · exact B1808643
  · exact B1808647
  · exact B1808651
  · exact B1808655
  · exact B1808659
  · exact B1808663
  · exact B1808667
  · exact B1808671
  · exact B1808675
  · exact B1808679
  · exact B1808683
  · exact B1808687
  · exact B1808691
  · exact B1808695
  · exact B1808699
  · exact B1808703
  · exact B1808707
  · exact B1808711
  · exact B1808715
  · exact B1808719
  · exact B1808723
  · exact B1808727
  · exact B1808731
  · exact B1808735
  · exact B1808739
  · exact B1808743
  · exact B1808747
  · exact B1808751
  · exact B1808755
  · exact B1808759
  · exact B1808763
  · exact B1808767
  · exact B1808771
  · exact B1808775
  · exact B1808779
  · exact B1808783
  · exact B1808787
  · exact B1808791
  · exact B1808795
  · exact B1808799
  · exact B1808803
  · exact B1808807
  · exact B1808811
  · exact B1808815
  · exact B1808819
  · exact B1808823
  · exact B1808827
  · exact B1808831
  · exact B1808835
  · exact B1808839
  · exact B1808843
  · exact B1808847
  · exact B1808851
  · exact B1808855
  · exact B1808859
  · exact B1808863
  · exact B1808867
  · exact B1808871
  · exact B1808875
  · exact B1808879
  · exact B1808883
  · exact B1808887
  · exact B1808891
  · exact B1808895
  · exact B1808899
  · exact B1808903
  · exact B1808907
  · exact B1808911
  · exact B1808915
  · exact B1808919
  · exact B1808923
  · exact B1808927
  · exact B1808931
  · exact B1808935
  · exact B1808939
  · exact B1808943
  · exact B1808947
  · exact B1808951
  · exact B1808955
  · exact B1808959
  · exact B1808963
  · exact B1808967
  · exact B1808971
  · exact B1808975
  · exact B1808979
  · exact B1808983
  · exact B1808987
  · exact B1808991
  · exact B1808995
  · exact B1808999
  · exact B1809003
  · exact B1809007
  · exact B1809011
  · exact B1809015
  · exact B1809019
  · exact B1809023
  · exact B1809027
  · exact B1809031
  · exact B1809035
  · exact B1809039
  · exact B1809043
  · exact B1809047
  · exact B1809051
  · exact B1809055
  · exact B1809059
  · exact B1809063
  · exact B1809067
  · exact B1809071
  · exact B1809075
  · exact B1809079
  · exact B1809083
  · exact B1809087
  · exact B1809091
  · exact B1809095
  · exact B1809099
  · exact B1809103
  · exact B1809107
  · exact B1809111
  · exact B1809115
  · exact B1809119
  · exact B1809123
  · exact B1809127
  · exact B1809131
  · exact B1809135
  · exact B1809139
  · exact B1809143
  · exact B1809147
  · exact B1809151
  · exact B1809155
  · exact B1809159
  · exact B1809163
  · exact B1809167
  · exact B1809171
  · exact B1809175
  · exact B1809179
  · exact B1809183
  · exact B1809187
  · exact B1809191
  · exact B1809195
  · exact B1809199
  · exact B1809203
  · exact B1809207
  · exact B1809211
  · exact B1809215
  · exact B1809219
  · exact B1809223
  · exact B1809227
  · exact B1809231
  · exact B1809235
  · exact B1809239
  · exact B1809243
  · exact B1809247
  · exact B1809251
  · exact B1809255
  · exact B1809259
  · exact B1809263
  · exact B1809267
  · exact B1809271
  · exact B1809275
  · exact B1809279
  · exact B1809283
  · exact B1809287
  · exact B1809291
  · exact B1809295
  · exact B1809299
  · exact B1809303
  · exact B1809307
  · exact B1809311
  · exact B1809315
  · exact B1809319
  · exact B1809323
  · exact B1809327
  · exact B1809331
  · exact B1809335
  · exact B1809339
  · exact B1809343
  · exact B1809347
  · exact B1809351
  · exact B1809355
  · exact B1809359
  · exact B1809363
  · exact B1809367
  · exact B1809371
  · exact B1809375
  · exact B1809379
  · exact B1809383
  · exact B1809387
  · exact B1809391
  · exact B1809395
  · exact B1809399
  · exact B1809403
  · exact B1809407
  · exact B1809411
  · exact B1809415
  · exact B1809419
  · exact B1809423
  · exact B1809427
  · exact B1809431
  · exact B1809435
  · exact B1809439
  · exact B1809443
  · exact B1809447
  · exact B1809451
  · exact B1809455
  · exact B1809459
  · exact B1809463
  · exact B1809467
  · exact B1809471
  · exact B1809475
  · exact B1809479
  · exact B1809483
  · exact B1809487
  · exact B1809491
  · exact B1809495
  · exact B1809499
  · exact B1809503
  · exact B1809507
  · exact B1809511
  · exact B1809515
  · exact B1809519
  · exact B1809523
  · exact B1809527
  · exact B1809531
  · exact B1809535
  · exact B1809539
  · exact B1809543
  · exact B1809547
  · exact B1809551
  · exact B1809555
  · exact B1809559
  · exact B1809563
  · exact B1809567
  · exact B1809571
  · exact B1809575
  · exact B1809579
  · exact B1809583
  · exact B1809587
  · exact B1809591
  · exact B1809595
  · exact B1809599
  · exact B1809603

theorem solution (m : ℕ) (hlo : 1807605 ≤ m) (hhi : m ≤ 1809605) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 451901 ≤ j := by omega
    have hj2 : j ≤ 452400 := by omega
    have hb : Blo 1807605 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
