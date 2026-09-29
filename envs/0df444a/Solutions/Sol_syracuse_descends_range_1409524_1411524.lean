-- Prove2me | solution 1 for syracuse_descends_range_1409524_1411524
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:02.840242+00:00
-- url     : https://prove2.me/submissions/4a0e8559-539f-4ad8-815d-33cd32a73171

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


theorem B5357573 : Blo 1409524 5357573 := bbase (se 4 (by rfl) ⟨502272, by rfl⟩ : syracuseStep 5357573 = 1004545) (by norm_num)
theorem B8036405 : Blo 1409524 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B1785989 : Blo 1409524 1785989 := bbase (se 4 (by rfl) ⟨167436, by rfl⟩ : syracuseStep 1785989 = 334873) (by norm_num)
theorem B23175317 : Blo 1409524 23175317 := bbase (se 6 (by rfl) ⟨543171, by rfl⟩ : syracuseStep 23175317 = 1086343) (by norm_num)
theorem B3571877 : Blo 1409524 3571877 := bbase (se 4 (by rfl) ⟨334863, by rfl⟩ : syracuseStep 3571877 = 669727) (by norm_num)
theorem B8028341 : Blo 1409524 8028341 := bbase (se 5 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 8028341 = 752657) (by norm_num)
theorem B1786045 : Blo 1409524 1786045 := bbase (se 3 (by rfl) ⟨334883, by rfl⟩ : syracuseStep 1786045 = 669767) (by norm_num)
theorem B5505221 : Blo 1409524 5505221 := bbase (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) (by norm_num)
theorem B4759829 : Blo 1409524 4759829 := bbase (se 6 (by rfl) ⟨111558, by rfl⟩ : syracuseStep 4759829 = 223117) (by norm_num)
theorem B25747733 : Blo 1409524 25747733 := bbase (se 6 (by rfl) ⟨603462, by rfl⟩ : syracuseStep 25747733 = 1206925) (by norm_num)
theorem B1786141 : Blo 1409524 1786141 := bbase (se 3 (by rfl) ⟨334901, by rfl⟩ : syracuseStep 1786141 = 669803) (by norm_num)
theorem B1589549 : Blo 1409524 1589549 := bbase (se 3 (by rfl) ⟨298040, by rfl⟩ : syracuseStep 1589549 = 596081) (by norm_num)
theorem B26100053 : Blo 1409524 26100053 := bbase (se 10 (by rfl) ⟨38232, by rfl⟩ : syracuseStep 26100053 = 76465) (by norm_num)
theorem B2007461 : Blo 1409524 2007461 := bbase (se 4 (by rfl) ⟨188199, by rfl⟩ : syracuseStep 2007461 = 376399) (by norm_num)
theorem B1786313 : Blo 1409524 1786313 := bbase (se 2 (by rfl) ⟨669867, by rfl⟩ : syracuseStep 1786313 = 1339735) (by norm_num)
theorem B2007541 : Blo 1409524 2007541 := bbase (se 5 (by rfl) ⟨94103, by rfl⟩ : syracuseStep 2007541 = 188207) (by norm_num)
theorem B3572221 : Blo 1409524 3572221 := bbase (se 3 (by rfl) ⟨669791, by rfl⟩ : syracuseStep 3572221 = 1339583) (by norm_num)
theorem B1786369 : Blo 1409524 1786369 := bbase (se 2 (by rfl) ⟨669888, by rfl⟩ : syracuseStep 1786369 = 1339777) (by norm_num)
theorem B6021701 : Blo 1409524 6021701 := bbase (se 4 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 6021701 = 1129069) (by norm_num)
theorem B2540117 : Blo 1409524 2540117 := bbase (se 8 (by rfl) ⟨14883, by rfl⟩ : syracuseStep 2540117 = 29767) (by norm_num)
theorem B7144037 : Blo 1409524 7144037 := bbase (se 4 (by rfl) ⟨669753, by rfl⟩ : syracuseStep 7144037 = 1339507) (by norm_num)
theorem B2007661 : Blo 1409524 2007661 := bbase (se 3 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 2007661 = 752873) (by norm_num)
theorem B3572333 : Blo 1409524 3572333 := bbase (se 3 (by rfl) ⟨669812, by rfl⟩ : syracuseStep 3572333 = 1339625) (by norm_num)
theorem B22872725 : Blo 1409524 22872725 := bbase (se 6 (by rfl) ⟨536079, by rfl⟩ : syracuseStep 22872725 = 1072159) (by norm_num)
theorem B2540197 : Blo 1409524 2540197 := bbase (se 4 (by rfl) ⟨238143, by rfl⟩ : syracuseStep 2540197 = 476287) (by norm_num)
theorem B4760261 : Blo 1409524 4760261 := bbase (se 4 (by rfl) ⟨446274, by rfl⟩ : syracuseStep 4760261 = 892549) (by norm_num)
theorem B2679493 : Blo 1409524 2679493 := bbase (se 4 (by rfl) ⟨251202, by rfl⟩ : syracuseStep 2679493 = 502405) (by norm_num)
theorem B2007757 : Blo 1409524 2007757 := bbase (se 3 (by rfl) ⟨376454, by rfl⟩ : syracuseStep 2007757 = 752909) (by norm_num)
theorem B2114309 : Blo 1409524 2114309 := bbase (se 4 (by rfl) ⟨198216, by rfl⟩ : syracuseStep 2114309 = 396433) (by norm_num)
theorem B3261197 : Blo 1409524 3261197 := bbase (se 3 (by rfl) ⟨611474, by rfl⟩ : syracuseStep 3261197 = 1222949) (by norm_num)
theorem B2114333 : Blo 1409524 2114333 := bbase (se 3 (by rfl) ⟨396437, by rfl⟩ : syracuseStep 2114333 = 792875) (by norm_num)
theorem B3572525 : Blo 1409524 3572525 := bbase (se 3 (by rfl) ⟨669848, by rfl⟩ : syracuseStep 3572525 = 1339697) (by norm_num)
theorem B2114357 : Blo 1409524 2114357 := bbase (se 5 (by rfl) ⟨99110, by rfl⟩ : syracuseStep 2114357 = 198221) (by norm_num)
theorem B6275893 : Blo 1409524 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B2114381 : Blo 1409524 2114381 := bbase (se 3 (by rfl) ⟨396446, by rfl⟩ : syracuseStep 2114381 = 792893) (by norm_num)
theorem B2679637 : Blo 1409524 2679637 := bbase (se 9 (by rfl) ⟨7850, by rfl⟩ : syracuseStep 2679637 = 15701) (by norm_num)
theorem B2859869 : Blo 1409524 2859869 := bbase (se 3 (by rfl) ⟨536225, by rfl⟩ : syracuseStep 2859869 = 1072451) (by norm_num)
theorem B2114405 : Blo 1409524 2114405 := bbase (se 4 (by rfl) ⟨198225, by rfl⟩ : syracuseStep 2114405 = 396451) (by norm_num)
theorem B2114429 : Blo 1409524 2114429 := bbase (se 3 (by rfl) ⟨396455, by rfl⟩ : syracuseStep 2114429 = 792911) (by norm_num)
theorem B2114453 : Blo 1409524 2114453 := bbase (se 6 (by rfl) ⟨49557, by rfl⟩ : syracuseStep 2114453 = 99115) (by norm_num)
theorem B6865829 : Blo 1409524 6865829 := bbase (se 4 (by rfl) ⟨643671, by rfl⟩ : syracuseStep 6865829 = 1287343) (by norm_num)
theorem B2114477 : Blo 1409524 2114477 := bbase (se 3 (by rfl) ⟨396464, by rfl⟩ : syracuseStep 2114477 = 792929) (by norm_num)
theorem B2114501 : Blo 1409524 2114501 := bbase (se 4 (by rfl) ⟨198234, by rfl⟩ : syracuseStep 2114501 = 396469) (by norm_num)
theorem B2114525 : Blo 1409524 2114525 := bbase (se 3 (by rfl) ⟨396473, by rfl⟩ : syracuseStep 2114525 = 792947) (by norm_num)
theorem B6431717 : Blo 1409524 6431717 := bbase (se 4 (by rfl) ⟨602973, by rfl⟩ : syracuseStep 6431717 = 1205947) (by norm_num)
theorem B2114549 : Blo 1409524 2114549 := bbase (se 5 (by rfl) ⟨99119, by rfl⟩ : syracuseStep 2114549 = 198239) (by norm_num)
theorem B7136261 : Blo 1409524 7136261 := bbase (se 4 (by rfl) ⟨669024, by rfl⟩ : syracuseStep 7136261 = 1338049) (by norm_num)
theorem B2114573 : Blo 1409524 2114573 := bbase (se 3 (by rfl) ⟨396482, by rfl⟩ : syracuseStep 2114573 = 792965) (by norm_num)
theorem B2114597 : Blo 1409524 2114597 := bbase (se 4 (by rfl) ⟨198243, by rfl⟩ : syracuseStep 2114597 = 396487) (by norm_num)
theorem B2114621 : Blo 1409524 2114621 := bbase (se 3 (by rfl) ⟨396491, by rfl⟩ : syracuseStep 2114621 = 792983) (by norm_num)
theorem B2114645 : Blo 1409524 2114645 := bbase (se 8 (by rfl) ⟨12390, by rfl⟩ : syracuseStep 2114645 = 24781) (by norm_num)
theorem B3171437 : Blo 1409524 3171437 := bbase (se 3 (by rfl) ⟨594644, by rfl⟩ : syracuseStep 3171437 = 1189289) (by norm_num)
theorem B2114669 : Blo 1409524 2114669 := bbase (se 3 (by rfl) ⟨396500, by rfl⟩ : syracuseStep 2114669 = 793001) (by norm_num)
theorem B5719157 : Blo 1409524 5719157 := bbase (se 5 (by rfl) ⟨268085, by rfl⟩ : syracuseStep 5719157 = 536171) (by norm_num)
theorem B4760693 : Blo 1409524 4760693 := bbase (se 5 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 4760693 = 446315) (by norm_num)
theorem B2114693 : Blo 1409524 2114693 := bbase (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) (by norm_num)
theorem B3572869 : Blo 1409524 3572869 := bbase (se 4 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 3572869 = 669913) (by norm_num)
theorem B2114717 : Blo 1409524 2114717 := bbase (se 3 (by rfl) ⟨396509, by rfl⟩ : syracuseStep 2114717 = 793019) (by norm_num)
theorem B5358757 : Blo 1409524 5358757 := bbase (se 4 (by rfl) ⟨502383, by rfl⟩ : syracuseStep 5358757 = 1004767) (by norm_num)
theorem B3171509 : Blo 1409524 3171509 := bbase (se 5 (by rfl) ⟨148664, by rfl⟩ : syracuseStep 3171509 = 297329) (by norm_num)
theorem B2114741 : Blo 1409524 2114741 := bbase (se 5 (by rfl) ⟨99128, by rfl⟩ : syracuseStep 2114741 = 198257) (by norm_num)
theorem B2008253 : Blo 1409524 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B2114765 : Blo 1409524 2114765 := bbase (se 3 (by rfl) ⟨396518, by rfl⟩ : syracuseStep 2114765 = 793037) (by norm_num)
theorem B8037589 : Blo 1409524 8037589 := bbase (se 7 (by rfl) ⟨94190, by rfl⟩ : syracuseStep 8037589 = 188381) (by norm_num)
theorem B2114789 : Blo 1409524 2114789 := bbase (se 4 (by rfl) ⟨198261, by rfl⟩ : syracuseStep 2114789 = 396523) (by norm_num)
theorem B3171581 : Blo 1409524 3171581 := bbase (se 3 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 3171581 = 1189343) (by norm_num)
theorem B2114813 : Blo 1409524 2114813 := bbase (se 3 (by rfl) ⟨396527, by rfl⟩ : syracuseStep 2114813 = 793055) (by norm_num)
theorem B2114837 : Blo 1409524 2114837 := bbase (se 6 (by rfl) ⟨49566, by rfl⟩ : syracuseStep 2114837 = 99133) (by norm_num)
theorem B2114861 : Blo 1409524 2114861 := bbase (se 3 (by rfl) ⟨396536, by rfl⟩ : syracuseStep 2114861 = 793073) (by norm_num)
theorem B3171653 : Blo 1409524 3171653 := bbase (se 4 (by rfl) ⟨297342, by rfl⟩ : syracuseStep 3171653 = 594685) (by norm_num)
theorem B2114885 : Blo 1409524 2114885 := bbase (se 4 (by rfl) ⟨198270, by rfl⟩ : syracuseStep 2114885 = 396541) (by norm_num)
theorem B2114909 : Blo 1409524 2114909 := bbase (se 3 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 2114909 = 793091) (by norm_num)
theorem B2114933 : Blo 1409524 2114933 := bbase (se 5 (by rfl) ⟨99137, by rfl⟩ : syracuseStep 2114933 = 198275) (by norm_num)
theorem B3171725 : Blo 1409524 3171725 := bbase (se 3 (by rfl) ⟨594698, by rfl⟩ : syracuseStep 3171725 = 1189397) (by norm_num)
theorem B2114957 : Blo 1409524 2114957 := bbase (se 3 (by rfl) ⟨396554, by rfl⟩ : syracuseStep 2114957 = 793109) (by norm_num)
theorem B10855829 : Blo 1409524 10855829 := bbase (se 6 (by rfl) ⟨254433, by rfl⟩ : syracuseStep 10855829 = 508867) (by norm_num)
theorem B2114981 : Blo 1409524 2114981 := bbase (se 4 (by rfl) ⟨198279, by rfl⟩ : syracuseStep 2114981 = 396559) (by norm_num)
theorem B2115005 : Blo 1409524 2115005 := bbase (se 3 (by rfl) ⟨396563, by rfl⟩ : syracuseStep 2115005 = 793127) (by norm_num)
theorem B3171797 : Blo 1409524 3171797 := bbase (se 7 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 3171797 = 74339) (by norm_num)
theorem B2115029 : Blo 1409524 2115029 := bbase (se 7 (by rfl) ⟨24785, by rfl⟩ : syracuseStep 2115029 = 49571) (by norm_num)
theorem B5359061 : Blo 1409524 5359061 := bbase (se 7 (by rfl) ⟨62801, by rfl⟩ : syracuseStep 5359061 = 125603) (by norm_num)
theorem B2115053 : Blo 1409524 2115053 := bbase (se 3 (by rfl) ⟨396572, by rfl⟩ : syracuseStep 2115053 = 793145) (by norm_num)
theorem B2115077 : Blo 1409524 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B3171869 : Blo 1409524 3171869 := bbase (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) (by norm_num)
theorem B2115101 : Blo 1409524 2115101 := bbase (se 3 (by rfl) ⟨396581, by rfl⟩ : syracuseStep 2115101 = 793163) (by norm_num)
theorem B4761125 : Blo 1409524 4761125 := bbase (se 4 (by rfl) ⟨446355, by rfl⟩ : syracuseStep 4761125 = 892711) (by norm_num)
theorem B2115125 : Blo 1409524 2115125 := bbase (se 5 (by rfl) ⟨99146, by rfl⟩ : syracuseStep 2115125 = 198293) (by norm_num)
theorem B2115149 : Blo 1409524 2115149 := bbase (se 3 (by rfl) ⟨396590, by rfl⟩ : syracuseStep 2115149 = 793181) (by norm_num)
theorem B3171941 : Blo 1409524 3171941 := bbase (se 4 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 3171941 = 594739) (by norm_num)
theorem B2115173 : Blo 1409524 2115173 := bbase (se 4 (by rfl) ⟨198297, by rfl⟩ : syracuseStep 2115173 = 396595) (by norm_num)
theorem B2115197 : Blo 1409524 2115197 := bbase (se 3 (by rfl) ⟨396599, by rfl⟩ : syracuseStep 2115197 = 793199) (by norm_num)
theorem B2115221 : Blo 1409524 2115221 := bbase (se 6 (by rfl) ⟨49575, by rfl⟩ : syracuseStep 2115221 = 99151) (by norm_num)
theorem B3172013 : Blo 1409524 3172013 := bbase (se 3 (by rfl) ⟨594752, by rfl⟩ : syracuseStep 3172013 = 1189505) (by norm_num)
theorem B2115245 : Blo 1409524 2115245 := bbase (se 3 (by rfl) ⟨396608, by rfl⟩ : syracuseStep 2115245 = 793217) (by norm_num)
theorem B2115269 : Blo 1409524 2115269 := bbase (se 4 (by rfl) ⟨198306, by rfl⟩ : syracuseStep 2115269 = 396613) (by norm_num)
theorem B2115293 : Blo 1409524 2115293 := bbase (se 3 (by rfl) ⟨396617, by rfl⟩ : syracuseStep 2115293 = 793235) (by norm_num)
theorem B2008805 : Blo 1409524 2008805 := bbase (se 4 (by rfl) ⟨188325, by rfl⟩ : syracuseStep 2008805 = 376651) (by norm_num)
theorem B3172085 : Blo 1409524 3172085 := bbase (se 5 (by rfl) ⟨148691, by rfl⟩ : syracuseStep 3172085 = 297383) (by norm_num)
theorem B2115317 : Blo 1409524 2115317 := bbase (se 5 (by rfl) ⟨99155, by rfl⟩ : syracuseStep 2115317 = 198311) (by norm_num)
theorem B2115341 : Blo 1409524 2115341 := bbase (se 3 (by rfl) ⟨396626, by rfl⟩ : syracuseStep 2115341 = 793253) (by norm_num)
theorem B2115365 : Blo 1409524 2115365 := bbase (se 4 (by rfl) ⟨198315, by rfl⟩ : syracuseStep 2115365 = 396631) (by norm_num)
theorem B4015925 : Blo 1409524 4015925 := bbase (se 5 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 4015925 = 376493) (by norm_num)
theorem B3172157 : Blo 1409524 3172157 := bbase (se 3 (by rfl) ⟨594779, by rfl⟩ : syracuseStep 3172157 = 1189559) (by norm_num)
theorem B2115389 : Blo 1409524 2115389 := bbase (se 3 (by rfl) ⟨396635, by rfl⟩ : syracuseStep 2115389 = 793271) (by norm_num)
theorem B1607509 : Blo 1409524 1607509 := bbase (se 9 (by rfl) ⟨4709, by rfl⟩ : syracuseStep 1607509 = 9419) (by norm_num)
theorem B2115413 : Blo 1409524 2115413 := bbase (se 9 (by rfl) ⟨6197, by rfl⟩ : syracuseStep 2115413 = 12395) (by norm_num)
theorem B2115437 : Blo 1409524 2115437 := bbase (se 3 (by rfl) ⟨396644, by rfl⟩ : syracuseStep 2115437 = 793289) (by norm_num)
theorem B7145333 : Blo 1409524 7145333 := bbase (se 5 (by rfl) ⟨334937, by rfl⟩ : syracuseStep 7145333 = 669875) (by norm_num)
theorem B3172229 : Blo 1409524 3172229 := bbase (se 4 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 3172229 = 594793) (by norm_num)
theorem B2115461 : Blo 1409524 2115461 := bbase (se 4 (by rfl) ⟨198324, by rfl⟩ : syracuseStep 2115461 = 396649) (by norm_num)
theorem B2115485 : Blo 1409524 2115485 := bbase (se 3 (by rfl) ⟨396653, by rfl⟩ : syracuseStep 2115485 = 793307) (by norm_num)
theorem B2115509 : Blo 1409524 2115509 := bbase (se 5 (by rfl) ⟨99164, by rfl⟩ : syracuseStep 2115509 = 198329) (by norm_num)
theorem B3172301 : Blo 1409524 3172301 := bbase (se 3 (by rfl) ⟨594806, by rfl⟩ : syracuseStep 3172301 = 1189613) (by norm_num)
theorem B2115533 : Blo 1409524 2115533 := bbase (se 3 (by rfl) ⟨396662, by rfl⟩ : syracuseStep 2115533 = 793325) (by norm_num)
theorem B4761557 : Blo 1409524 4761557 := bbase (se 7 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 4761557 = 111599) (by norm_num)
theorem B2115557 : Blo 1409524 2115557 := bbase (se 4 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 2115557 = 396667) (by norm_num)
theorem B3303413 : Blo 1409524 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B2115581 : Blo 1409524 2115581 := bbase (se 3 (by rfl) ⟨396671, by rfl⟩ : syracuseStep 2115581 = 793343) (by norm_num)
theorem B3172373 : Blo 1409524 3172373 := bbase (se 6 (by rfl) ⟨74352, by rfl⟩ : syracuseStep 3172373 = 148705) (by norm_num)
theorem B2115605 : Blo 1409524 2115605 := bbase (se 6 (by rfl) ⟨49584, by rfl⟩ : syracuseStep 2115605 = 99169) (by norm_num)
theorem B2115629 : Blo 1409524 2115629 := bbase (se 3 (by rfl) ⟨396680, by rfl⟩ : syracuseStep 2115629 = 793361) (by norm_num)
theorem B2115653 : Blo 1409524 2115653 := bbase (se 4 (by rfl) ⟨198342, by rfl⟩ : syracuseStep 2115653 = 396685) (by norm_num)
theorem B12863573 : Blo 1409524 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B3172445 : Blo 1409524 3172445 := bbase (se 3 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 3172445 = 1189667) (by norm_num)
theorem B2115677 : Blo 1409524 2115677 := bbase (se 3 (by rfl) ⟨396689, by rfl⟩ : syracuseStep 2115677 = 793379) (by norm_num)
theorem B2115701 : Blo 1409524 2115701 := bbase (se 5 (by rfl) ⟨99173, by rfl⟩ : syracuseStep 2115701 = 198347) (by norm_num)
theorem B2115725 : Blo 1409524 2115725 := bbase (se 3 (by rfl) ⟨396698, by rfl⟩ : syracuseStep 2115725 = 793397) (by norm_num)
theorem B3172517 : Blo 1409524 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B2115749 : Blo 1409524 2115749 := bbase (se 4 (by rfl) ⟨198351, by rfl⟩ : syracuseStep 2115749 = 396703) (by norm_num)
theorem B2115773 : Blo 1409524 2115773 := bbase (se 3 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 2115773 = 793415) (by norm_num)
theorem B2115797 : Blo 1409524 2115797 := bbase (se 7 (by rfl) ⟨24794, by rfl⟩ : syracuseStep 2115797 = 49589) (by norm_num)
theorem B3262693 : Blo 1409524 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B3172589 : Blo 1409524 3172589 := bbase (se 3 (by rfl) ⟨594860, by rfl⟩ : syracuseStep 3172589 = 1189721) (by norm_num)
theorem B2115821 : Blo 1409524 2115821 := bbase (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) (by norm_num)
theorem B2115845 : Blo 1409524 2115845 := bbase (se 4 (by rfl) ⟨198360, by rfl⟩ : syracuseStep 2115845 = 396721) (by norm_num)
theorem B7137557 : Blo 1409524 7137557 := bbase (se 6 (by rfl) ⟨167286, by rfl⟩ : syracuseStep 7137557 = 334573) (by norm_num)
theorem B2115869 : Blo 1409524 2115869 := bbase (se 3 (by rfl) ⟨396725, by rfl⟩ : syracuseStep 2115869 = 793451) (by norm_num)
theorem B3172661 : Blo 1409524 3172661 := bbase (se 5 (by rfl) ⟨148718, by rfl⟩ : syracuseStep 3172661 = 297437) (by norm_num)
theorem B6023477 : Blo 1409524 6023477 := bbase (se 5 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 6023477 = 564701) (by norm_num)
theorem B2115893 : Blo 1409524 2115893 := bbase (se 5 (by rfl) ⟨99182, by rfl⟩ : syracuseStep 2115893 = 198365) (by norm_num)
theorem B4286789 : Blo 1409524 4286789 := bbase (se 4 (by rfl) ⟨401886, by rfl⟩ : syracuseStep 4286789 = 803773) (by norm_num)
theorem B2115917 : Blo 1409524 2115917 := bbase (se 3 (by rfl) ⟨396734, by rfl⟩ : syracuseStep 2115917 = 793469) (by norm_num)
theorem B2115941 : Blo 1409524 2115941 := bbase (se 4 (by rfl) ⟨198369, by rfl⟩ : syracuseStep 2115941 = 396739) (by norm_num)
theorem B3172733 : Blo 1409524 3172733 := bbase (se 3 (by rfl) ⟨594887, by rfl⟩ : syracuseStep 3172733 = 1189775) (by norm_num)
theorem B2115965 : Blo 1409524 2115965 := bbase (se 3 (by rfl) ⟨396743, by rfl⟩ : syracuseStep 2115965 = 793487) (by norm_num)
theorem B4761989 : Blo 1409524 4761989 := bbase (se 4 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 4761989 = 892873) (by norm_num)
theorem B2115989 : Blo 1409524 2115989 := bbase (se 6 (by rfl) ⟨49593, by rfl⟩ : syracuseStep 2115989 = 99187) (by norm_num)
theorem B5794213 : Blo 1409524 5794213 := bbase (se 4 (by rfl) ⟨543207, by rfl⟩ : syracuseStep 5794213 = 1086415) (by norm_num)
theorem B2116013 : Blo 1409524 2116013 := bbase (se 3 (by rfl) ⟨396752, by rfl⟩ : syracuseStep 2116013 = 793505) (by norm_num)
theorem B3172805 : Blo 1409524 3172805 := bbase (se 4 (by rfl) ⟨297450, by rfl⟩ : syracuseStep 3172805 = 594901) (by norm_num)
theorem B2116037 : Blo 1409524 2116037 := bbase (se 4 (by rfl) ⟨198378, by rfl⟩ : syracuseStep 2116037 = 396757) (by norm_num)
theorem B2009557 : Blo 1409524 2009557 := bbase (se 7 (by rfl) ⟨23549, by rfl⟩ : syracuseStep 2009557 = 47099) (by norm_num)
theorem B2116061 : Blo 1409524 2116061 := bbase (se 3 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 2116061 = 793523) (by norm_num)
theorem B2116085 : Blo 1409524 2116085 := bbase (se 5 (by rfl) ⟨99191, by rfl⟩ : syracuseStep 2116085 = 198383) (by norm_num)
theorem B3172877 : Blo 1409524 3172877 := bbase (se 3 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 3172877 = 1189829) (by norm_num)
theorem B2116109 : Blo 1409524 2116109 := bbase (se 3 (by rfl) ⟨396770, by rfl⟩ : syracuseStep 2116109 = 793541) (by norm_num)
theorem B6023717 : Blo 1409524 6023717 := bbase (se 4 (by rfl) ⟨564723, by rfl⟩ : syracuseStep 6023717 = 1129447) (by norm_num)
theorem B2116133 : Blo 1409524 2116133 := bbase (se 4 (by rfl) ⟨198387, by rfl⟩ : syracuseStep 2116133 = 396775) (by norm_num)
theorem B2116157 : Blo 1409524 2116157 := bbase (se 3 (by rfl) ⟨396779, by rfl⟩ : syracuseStep 2116157 = 793559) (by norm_num)
theorem B3172949 : Blo 1409524 3172949 := bbase (se 8 (by rfl) ⟨18591, by rfl⟩ : syracuseStep 3172949 = 37183) (by norm_num)
theorem B2116181 : Blo 1409524 2116181 := bbase (se 8 (by rfl) ⟨12399, by rfl⟩ : syracuseStep 2116181 = 24799) (by norm_num)
theorem B2116205 : Blo 1409524 2116205 := bbase (se 3 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 2116205 = 793577) (by norm_num)
theorem B2116229 : Blo 1409524 2116229 := bbase (se 4 (by rfl) ⟨198396, by rfl⟩ : syracuseStep 2116229 = 396793) (by norm_num)
theorem B3173021 : Blo 1409524 3173021 := bbase (se 3 (by rfl) ⟨594941, by rfl⟩ : syracuseStep 3173021 = 1189883) (by norm_num)
theorem B2116253 : Blo 1409524 2116253 := bbase (se 3 (by rfl) ⟨396797, by rfl⟩ : syracuseStep 2116253 = 793595) (by norm_num)
theorem B2116277 : Blo 1409524 2116277 := bbase (se 5 (by rfl) ⟨99200, by rfl⟩ : syracuseStep 2116277 = 198401) (by norm_num)
theorem B1608385 : Blo 1409524 1608385 := bbase (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) (by norm_num)
theorem B2116301 : Blo 1409524 2116301 := bbase (se 3 (by rfl) ⟨396806, by rfl⟩ : syracuseStep 2116301 = 793613) (by norm_num)
theorem B3173093 : Blo 1409524 3173093 := bbase (se 4 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 3173093 = 594955) (by norm_num)
theorem B2116325 : Blo 1409524 2116325 := bbase (se 4 (by rfl) ⟨198405, by rfl⟩ : syracuseStep 2116325 = 396811) (by norm_num)
theorem B2116349 : Blo 1409524 2116349 := bbase (se 3 (by rfl) ⟨396815, by rfl⟩ : syracuseStep 2116349 = 793631) (by norm_num)
theorem B2116373 : Blo 1409524 2116373 := bbase (se 6 (by rfl) ⟨49602, by rfl⟩ : syracuseStep 2116373 = 99205) (by norm_num)
theorem B3173165 : Blo 1409524 3173165 := bbase (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) (by norm_num)
theorem B2116397 : Blo 1409524 2116397 := bbase (se 3 (by rfl) ⟨396824, by rfl⟩ : syracuseStep 2116397 = 793649) (by norm_num)
theorem B4516661 : Blo 1409524 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B4762421 : Blo 1409524 4762421 := bbase (se 5 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 4762421 = 446477) (by norm_num)
theorem B2116421 : Blo 1409524 2116421 := bbase (se 4 (by rfl) ⟨198414, by rfl⟩ : syracuseStep 2116421 = 396829) (by norm_num)
theorem B2116445 : Blo 1409524 2116445 := bbase (se 3 (by rfl) ⟨396833, by rfl⟩ : syracuseStep 2116445 = 793667) (by norm_num)
theorem B2378605 : Blo 1409524 2378605 := bbase (se 3 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 2378605 = 891977) (by norm_num)
theorem B3173237 : Blo 1409524 3173237 := bbase (se 5 (by rfl) ⟨148745, by rfl⟩ : syracuseStep 3173237 = 297491) (by norm_num)
theorem B2116469 : Blo 1409524 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B2116493 : Blo 1409524 2116493 := bbase (se 3 (by rfl) ⟨396842, by rfl⟩ : syracuseStep 2116493 = 793685) (by norm_num)
theorem B6433685 : Blo 1409524 6433685 := bbase (se 6 (by rfl) ⟨150789, by rfl⟩ : syracuseStep 6433685 = 301579) (by norm_num)
theorem B2116517 : Blo 1409524 2116517 := bbase (se 4 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 2116517 = 396847) (by norm_num)
theorem B3173309 : Blo 1409524 3173309 := bbase (se 3 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 3173309 = 1189991) (by norm_num)
theorem B2116541 : Blo 1409524 2116541 := bbase (se 3 (by rfl) ⟨396851, by rfl⟩ : syracuseStep 2116541 = 793703) (by norm_num)
theorem B2378693 : Blo 1409524 2378693 := bbase (se 4 (by rfl) ⟨223002, by rfl⟩ : syracuseStep 2378693 = 446005) (by norm_num)
theorem B4017109 : Blo 1409524 4017109 := bbase (se 7 (by rfl) ⟨47075, by rfl⟩ : syracuseStep 4017109 = 94151) (by norm_num)
theorem B2116565 : Blo 1409524 2116565 := bbase (se 7 (by rfl) ⟨24803, by rfl⟩ : syracuseStep 2116565 = 49607) (by norm_num)
theorem B2116589 : Blo 1409524 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B3173381 : Blo 1409524 3173381 := bbase (se 4 (by rfl) ⟨297504, by rfl⟩ : syracuseStep 3173381 = 595009) (by norm_num)
theorem B2116613 : Blo 1409524 2116613 := bbase (se 4 (by rfl) ⟨198432, by rfl⟩ : syracuseStep 2116613 = 396865) (by norm_num)
theorem B2116637 : Blo 1409524 2116637 := bbase (se 3 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 2116637 = 793739) (by norm_num)
theorem B2116661 : Blo 1409524 2116661 := bbase (se 5 (by rfl) ⟨99218, by rfl⟩ : syracuseStep 2116661 = 198437) (by norm_num)
theorem B2378821 : Blo 1409524 2378821 := bbase (se 4 (by rfl) ⟨223014, by rfl⟩ : syracuseStep 2378821 = 446029) (by norm_num)
theorem B3173453 : Blo 1409524 3173453 := bbase (se 3 (by rfl) ⟨595022, by rfl⟩ : syracuseStep 3173453 = 1190045) (by norm_num)
theorem B2116685 : Blo 1409524 2116685 := bbase (se 3 (by rfl) ⟨396878, by rfl⟩ : syracuseStep 2116685 = 793757) (by norm_num)
theorem B2174045 : Blo 1409524 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B2116709 : Blo 1409524 2116709 := bbase (se 4 (by rfl) ⟨198441, by rfl⟩ : syracuseStep 2116709 = 396883) (by norm_num)
theorem B4017269 : Blo 1409524 4017269 := bbase (se 5 (by rfl) ⟨188309, by rfl⟩ : syracuseStep 4017269 = 376619) (by norm_num)
theorem B2116733 : Blo 1409524 2116733 := bbase (se 3 (by rfl) ⟨396887, by rfl⟩ : syracuseStep 2116733 = 793775) (by norm_num)
theorem B3173525 : Blo 1409524 3173525 := bbase (se 6 (by rfl) ⟨74379, by rfl⟩ : syracuseStep 3173525 = 148759) (by norm_num)
theorem B2116757 : Blo 1409524 2116757 := bbase (se 6 (by rfl) ⟨49611, by rfl⟩ : syracuseStep 2116757 = 99223) (by norm_num)
theorem B2378909 : Blo 1409524 2378909 := bbase (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) (by norm_num)
theorem B2714797 : Blo 1409524 2714797 := bbase (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) (by norm_num)
theorem B2116781 : Blo 1409524 2116781 := bbase (se 3 (by rfl) ⟨396896, by rfl⟩ : syracuseStep 2116781 = 793793) (by norm_num)
theorem B2116805 : Blo 1409524 2116805 := bbase (se 4 (by rfl) ⟨198450, by rfl⟩ : syracuseStep 2116805 = 396901) (by norm_num)
theorem B3173597 : Blo 1409524 3173597 := bbase (se 3 (by rfl) ⟨595049, by rfl⟩ : syracuseStep 3173597 = 1190099) (by norm_num)
theorem B2116829 : Blo 1409524 2116829 := bbase (se 3 (by rfl) ⟨396905, by rfl⟩ : syracuseStep 2116829 = 793811) (by norm_num)
theorem B4762853 : Blo 1409524 4762853 := bbase (se 4 (by rfl) ⟨446517, by rfl⟩ : syracuseStep 4762853 = 893035) (by norm_num)
theorem B2116853 : Blo 1409524 2116853 := bbase (se 5 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 2116853 = 198455) (by norm_num)
theorem B2116877 : Blo 1409524 2116877 := bbase (se 3 (by rfl) ⟨396914, by rfl⟩ : syracuseStep 2116877 = 793829) (by norm_num)
theorem B2379037 : Blo 1409524 2379037 := bbase (se 3 (by rfl) ⟨446069, by rfl⟩ : syracuseStep 2379037 = 892139) (by norm_num)
theorem B3173669 : Blo 1409524 3173669 := bbase (se 4 (by rfl) ⟨297531, by rfl⟩ : syracuseStep 3173669 = 595063) (by norm_num)
theorem B2116901 : Blo 1409524 2116901 := bbase (se 4 (by rfl) ⟨198459, by rfl⟩ : syracuseStep 2116901 = 396919) (by norm_num)
theorem B2116925 : Blo 1409524 2116925 := bbase (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) (by norm_num)
theorem B6778181 : Blo 1409524 6778181 := bbase (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) (by norm_num)
theorem B2116949 : Blo 1409524 2116949 := bbase (se 11 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 2116949 = 3101) (by norm_num)
theorem B4017509 : Blo 1409524 4017509 := bbase (se 4 (by rfl) ⟨376641, by rfl⟩ : syracuseStep 4017509 = 753283) (by norm_num)
theorem B3173741 : Blo 1409524 3173741 := bbase (se 3 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 3173741 = 1190153) (by norm_num)
theorem B2116973 : Blo 1409524 2116973 := bbase (se 3 (by rfl) ⟨396932, by rfl⟩ : syracuseStep 2116973 = 793865) (by norm_num)
theorem B2379125 : Blo 1409524 2379125 := bbase (se 5 (by rfl) ⟨111521, by rfl⟩ : syracuseStep 2379125 = 223043) (by norm_num)
theorem B2116997 : Blo 1409524 2116997 := bbase (se 4 (by rfl) ⟨198468, by rfl⟩ : syracuseStep 2116997 = 396937) (by norm_num)
theorem B2117021 : Blo 1409524 2117021 := bbase (se 3 (by rfl) ⟨396941, by rfl⟩ : syracuseStep 2117021 = 793883) (by norm_num)
theorem B3173813 : Blo 1409524 3173813 := bbase (se 5 (by rfl) ⟨148772, by rfl⟩ : syracuseStep 3173813 = 297545) (by norm_num)
theorem B2117045 : Blo 1409524 2117045 := bbase (se 5 (by rfl) ⟨99236, by rfl⟩ : syracuseStep 2117045 = 198473) (by norm_num)
theorem B2117069 : Blo 1409524 2117069 := bbase (se 3 (by rfl) ⟨396950, by rfl⟩ : syracuseStep 2117069 = 793901) (by norm_num)
theorem B2117093 : Blo 1409524 2117093 := bbase (se 4 (by rfl) ⟨198477, by rfl⟩ : syracuseStep 2117093 = 396955) (by norm_num)
theorem B2379253 : Blo 1409524 2379253 := bbase (se 5 (by rfl) ⟨111527, by rfl⟩ : syracuseStep 2379253 = 223055) (by norm_num)
theorem B3173885 : Blo 1409524 3173885 := bbase (se 3 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 3173885 = 1190207) (by norm_num)
theorem B2117117 : Blo 1409524 2117117 := bbase (se 3 (by rfl) ⟨396959, by rfl⟩ : syracuseStep 2117117 = 793919) (by norm_num)
theorem B2117141 : Blo 1409524 2117141 := bbase (se 6 (by rfl) ⟨49620, by rfl⟩ : syracuseStep 2117141 = 99241) (by norm_num)
theorem B7138853 : Blo 1409524 7138853 := bbase (se 4 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 7138853 = 1338535) (by norm_num)
theorem B4017701 : Blo 1409524 4017701 := bbase (se 4 (by rfl) ⟨376659, by rfl⟩ : syracuseStep 4017701 = 753319) (by norm_num)
theorem B2117165 : Blo 1409524 2117165 := bbase (se 3 (by rfl) ⟨396968, by rfl⟩ : syracuseStep 2117165 = 793937) (by norm_num)
theorem B9653813 : Blo 1409524 9653813 := bbase (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) (by norm_num)
theorem B3173957 : Blo 1409524 3173957 := bbase (se 4 (by rfl) ⟨297558, by rfl⟩ : syracuseStep 3173957 = 595117) (by norm_num)
theorem B2117189 : Blo 1409524 2117189 := bbase (se 4 (by rfl) ⟨198486, by rfl⟩ : syracuseStep 2117189 = 396973) (by norm_num)
theorem B2379341 : Blo 1409524 2379341 := bbase (se 3 (by rfl) ⟨446126, by rfl⟩ : syracuseStep 2379341 = 892253) (by norm_num)
theorem B2117213 : Blo 1409524 2117213 := bbase (se 3 (by rfl) ⟨396977, by rfl⟩ : syracuseStep 2117213 = 793955) (by norm_num)
theorem B2117237 : Blo 1409524 2117237 := bbase (se 5 (by rfl) ⟨99245, by rfl⟩ : syracuseStep 2117237 = 198491) (by norm_num)
theorem B1429121 : Blo 1409524 1429121 := bbase (se 2 (by rfl) ⟨535920, by rfl⟩ : syracuseStep 1429121 = 1071841) (by norm_num)
theorem B3174029 : Blo 1409524 3174029 := bbase (se 3 (by rfl) ⟨595130, by rfl⟩ : syracuseStep 3174029 = 1190261) (by norm_num)
theorem B2117261 : Blo 1409524 2117261 := bbase (se 3 (by rfl) ⟨396986, by rfl⟩ : syracuseStep 2117261 = 793973) (by norm_num)
theorem B4763285 : Blo 1409524 4763285 := bbase (se 6 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 4763285 = 223279) (by norm_num)
theorem B2117285 : Blo 1409524 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B12054197 : Blo 1409524 12054197 := bbase (se 5 (by rfl) ⟨565040, by rfl⟩ : syracuseStep 12054197 = 1130081) (by norm_num)
theorem B2379469 : Blo 1409524 2379469 := bbase (se 3 (by rfl) ⟨446150, by rfl⟩ : syracuseStep 2379469 = 892301) (by norm_num)
theorem B3174101 : Blo 1409524 3174101 := bbase (se 7 (by rfl) ⟨37196, by rfl⟩ : syracuseStep 3174101 = 74393) (by norm_num)
theorem B6434549 : Blo 1409524 6434549 := bbase (se 5 (by rfl) ⟨301619, by rfl⟩ : syracuseStep 6434549 = 603239) (by norm_num)
theorem B1609489 : Blo 1409524 1609489 := bbase (se 2 (by rfl) ⟨603558, by rfl⟩ : syracuseStep 1609489 = 1207117) (by norm_num)
theorem B3174173 : Blo 1409524 3174173 := bbase (se 3 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 3174173 = 1190315) (by norm_num)
theorem B2379557 : Blo 1409524 2379557 := bbase (se 4 (by rfl) ⟨223083, by rfl⟩ : syracuseStep 2379557 = 446167) (by norm_num)
theorem B2289493 : Blo 1409524 2289493 := bbase (se 9 (by rfl) ⟨6707, by rfl⟩ : syracuseStep 2289493 = 13415) (by norm_num)
theorem B3174245 : Blo 1409524 3174245 := bbase (se 4 (by rfl) ⟨297585, by rfl⟩ : syracuseStep 3174245 = 595171) (by norm_num)
theorem B2379685 : Blo 1409524 2379685 := bbase (se 4 (by rfl) ⟨223095, by rfl⟩ : syracuseStep 2379685 = 446191) (by norm_num)
theorem B3174317 : Blo 1409524 3174317 := bbase (se 3 (by rfl) ⟨595184, by rfl⟩ : syracuseStep 3174317 = 1190369) (by norm_num)
theorem B5353397 : Blo 1409524 5353397 := bbase (se 5 (by rfl) ⟨250940, by rfl⟩ : syracuseStep 5353397 = 501881) (by norm_num)
theorem B1429445 : Blo 1409524 1429445 := bbase (se 4 (by rfl) ⟨134010, by rfl⟩ : syracuseStep 1429445 = 268021) (by norm_num)
theorem B3174389 : Blo 1409524 3174389 := bbase (se 5 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 3174389 = 297599) (by norm_num)
theorem B2543605 : Blo 1409524 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B2379773 : Blo 1409524 2379773 := bbase (se 3 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 2379773 = 892415) (by norm_num)
theorem B4288565 : Blo 1409524 4288565 := bbase (se 5 (by rfl) ⟨201026, by rfl⟩ : syracuseStep 4288565 = 402053) (by norm_num)
theorem B3174461 : Blo 1409524 3174461 := bbase (se 3 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 3174461 = 1190423) (by norm_num)
theorem B4763717 : Blo 1409524 4763717 := bbase (se 4 (by rfl) ⟨446598, by rfl⟩ : syracuseStep 4763717 = 893197) (by norm_num)
theorem B3010645 : Blo 1409524 3010645 := bbase (se 8 (by rfl) ⟨17640, by rfl⟩ : syracuseStep 3010645 = 35281) (by norm_num)
theorem B2379901 : Blo 1409524 2379901 := bbase (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) (by norm_num)
theorem B3174533 : Blo 1409524 3174533 := bbase (se 4 (by rfl) ⟨297612, by rfl⟩ : syracuseStep 3174533 = 595225) (by norm_num)
theorem B3010765 : Blo 1409524 3010765 := bbase (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) (by norm_num)
theorem B3174605 : Blo 1409524 3174605 := bbase (se 3 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 3174605 = 1190477) (by norm_num)
theorem B5353685 : Blo 1409524 5353685 := bbase (se 7 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 5353685 = 125477) (by norm_num)
theorem B2379989 : Blo 1409524 2379989 := bbase (se 7 (by rfl) ⟨27890, by rfl⟩ : syracuseStep 2379989 = 55781) (by norm_num)
theorem B2412757 : Blo 1409524 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B3387629 : Blo 1409524 3387629 := bbase (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) (by norm_num)
theorem B3174677 : Blo 1409524 3174677 := bbase (se 6 (by rfl) ⟨74406, by rfl⟩ : syracuseStep 3174677 = 148813) (by norm_num)
theorem B1429805 : Blo 1409524 1429805 := bbase (se 3 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 1429805 = 536177) (by norm_num)
theorem B2380117 : Blo 1409524 2380117 := bbase (se 10 (by rfl) ⟨3486, by rfl⟩ : syracuseStep 2380117 = 6973) (by norm_num)
theorem B3174749 : Blo 1409524 3174749 := bbase (se 3 (by rfl) ⟨595265, by rfl⟩ : syracuseStep 3174749 = 1190531) (by norm_num)
theorem B3567989 : Blo 1409524 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B3174821 : Blo 1409524 3174821 := bbase (se 4 (by rfl) ⟨297639, by rfl⟩ : syracuseStep 3174821 = 595279) (by norm_num)
theorem B2380205 : Blo 1409524 2380205 := bbase (se 3 (by rfl) ⟨446288, by rfl⟩ : syracuseStep 2380205 = 892577) (by norm_num)
theorem B3011021 : Blo 1409524 3011021 := bbase (se 3 (by rfl) ⟨564566, by rfl⟩ : syracuseStep 3011021 = 1129133) (by norm_num)
theorem B3174893 : Blo 1409524 3174893 := bbase (se 3 (by rfl) ⟨595292, by rfl⟩ : syracuseStep 3174893 = 1190585) (by norm_num)
theorem B4018693 : Blo 1409524 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B2380333 : Blo 1409524 2380333 := bbase (se 3 (by rfl) ⟨446312, by rfl⟩ : syracuseStep 2380333 = 892625) (by norm_num)
theorem B3174965 : Blo 1409524 3174965 := bbase (se 5 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 3174965 = 297653) (by norm_num)
theorem B1585741 : Blo 1409524 1585741 := bbase (se 3 (by rfl) ⟨297326, by rfl⟩ : syracuseStep 1585741 = 594653) (by norm_num)
theorem B1585777 : Blo 1409524 1585777 := bbase (se 2 (by rfl) ⟨594666, by rfl⟩ : syracuseStep 1585777 = 1189333) (by norm_num)
theorem B3175037 : Blo 1409524 3175037 := bbase (se 3 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 3175037 = 1190639) (by norm_num)
theorem B2380421 : Blo 1409524 2380421 := bbase (se 4 (by rfl) ⟨223164, by rfl⟩ : syracuseStep 2380421 = 446329) (by norm_num)
theorem B5722757 : Blo 1409524 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B1585813 : Blo 1409524 1585813 := bbase (se 6 (by rfl) ⟨37167, by rfl⟩ : syracuseStep 1585813 = 74335) (by norm_num)
theorem B1585849 : Blo 1409524 1585849 := bbase (se 2 (by rfl) ⟨594693, by rfl⟩ : syracuseStep 1585849 = 1189387) (by norm_num)
theorem B3175109 : Blo 1409524 3175109 := bbase (se 4 (by rfl) ⟨297666, by rfl⟩ : syracuseStep 3175109 = 595333) (by norm_num)
theorem B3568333 : Blo 1409524 3568333 := bbase (se 3 (by rfl) ⟨669062, by rfl⟩ : syracuseStep 3568333 = 1338125) (by norm_num)
theorem B1585885 : Blo 1409524 1585885 := bbase (se 3 (by rfl) ⟨297353, by rfl⟩ : syracuseStep 1585885 = 594707) (by norm_num)
theorem B1585921 : Blo 1409524 1585921 := bbase (se 2 (by rfl) ⟨594720, by rfl⟩ : syracuseStep 1585921 = 1189441) (by norm_num)
theorem B2380549 : Blo 1409524 2380549 := bbase (se 4 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 2380549 = 446353) (by norm_num)
theorem B3175181 : Blo 1409524 3175181 := bbase (se 3 (by rfl) ⟨595346, by rfl⟩ : syracuseStep 3175181 = 1190693) (by norm_num)
theorem B6026005 : Blo 1409524 6026005 := bbase (se 6 (by rfl) ⟨141234, by rfl⟩ : syracuseStep 6026005 = 282469) (by norm_num)
theorem B1585957 : Blo 1409524 1585957 := bbase (se 4 (by rfl) ⟨148683, by rfl⟩ : syracuseStep 1585957 = 297367) (by norm_num)
theorem B7140149 : Blo 1409524 7140149 := bbase (se 5 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 7140149 = 669389) (by norm_num)
theorem B3568445 : Blo 1409524 3568445 := bbase (se 3 (by rfl) ⟨669083, by rfl⟩ : syracuseStep 3568445 = 1338167) (by norm_num)
theorem B1585993 : Blo 1409524 1585993 := bbase (se 2 (by rfl) ⟨594747, by rfl⟩ : syracuseStep 1585993 = 1189495) (by norm_num)
theorem B3175253 : Blo 1409524 3175253 := bbase (se 9 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 3175253 = 18605) (by norm_num)
theorem B2380637 : Blo 1409524 2380637 := bbase (se 3 (by rfl) ⟨446369, by rfl⟩ : syracuseStep 2380637 = 892739) (by norm_num)
theorem B1586029 : Blo 1409524 1586029 := bbase (se 3 (by rfl) ⟨297380, by rfl⟩ : syracuseStep 1586029 = 594761) (by norm_num)
theorem B10711925 : Blo 1409524 10711925 := bbase (se 5 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 10711925 = 1004243) (by norm_num)
theorem B1586065 : Blo 1409524 1586065 := bbase (se 2 (by rfl) ⟨594774, by rfl⟩ : syracuseStep 1586065 = 1189549) (by norm_num)
theorem B3175325 : Blo 1409524 3175325 := bbase (se 3 (by rfl) ⟨595373, by rfl⟩ : syracuseStep 3175325 = 1190747) (by norm_num)
theorem B6607781 : Blo 1409524 6607781 := bbase (se 4 (by rfl) ⟨619479, by rfl⟩ : syracuseStep 6607781 = 1238959) (by norm_num)
theorem B1586101 : Blo 1409524 1586101 := bbase (se 5 (by rfl) ⟨74348, by rfl⟩ : syracuseStep 1586101 = 148697) (by norm_num)
theorem B1586137 : Blo 1409524 1586137 := bbase (se 2 (by rfl) ⟨594801, by rfl⟩ : syracuseStep 1586137 = 1189603) (by norm_num)
theorem B2380765 : Blo 1409524 2380765 := bbase (se 3 (by rfl) ⟨446393, by rfl⟩ : syracuseStep 2380765 = 892787) (by norm_num)
theorem B3175397 : Blo 1409524 3175397 := bbase (se 4 (by rfl) ⟨297693, by rfl⟩ : syracuseStep 3175397 = 595387) (by norm_num)
theorem B3568637 : Blo 1409524 3568637 := bbase (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) (by norm_num)
theorem B1586173 : Blo 1409524 1586173 := bbase (se 3 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 1586173 = 594815) (by norm_num)
theorem B1586209 : Blo 1409524 1586209 := bbase (se 2 (by rfl) ⟨594828, by rfl⟩ : syracuseStep 1586209 = 1189657) (by norm_num)
theorem B2290733 : Blo 1409524 2290733 := bbase (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) (by norm_num)
theorem B3175469 : Blo 1409524 3175469 := bbase (se 3 (by rfl) ⟨595400, by rfl⟩ : syracuseStep 3175469 = 1190801) (by norm_num)
theorem B2380853 : Blo 1409524 2380853 := bbase (se 5 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 2380853 = 223205) (by norm_num)
theorem B1586245 : Blo 1409524 1586245 := bbase (se 4 (by rfl) ⟨148710, by rfl⟩ : syracuseStep 1586245 = 297421) (by norm_num)
theorem B1586281 : Blo 1409524 1586281 := bbase (se 2 (by rfl) ⟨594855, by rfl⟩ : syracuseStep 1586281 = 1189711) (by norm_num)
theorem B3175541 : Blo 1409524 3175541 := bbase (se 5 (by rfl) ⟨148853, by rfl⟩ : syracuseStep 3175541 = 297707) (by norm_num)
theorem B1586317 : Blo 1409524 1586317 := bbase (se 3 (by rfl) ⟨297434, by rfl⟩ : syracuseStep 1586317 = 594869) (by norm_num)
theorem B1586353 : Blo 1409524 1586353 := bbase (se 2 (by rfl) ⟨594882, by rfl⟩ : syracuseStep 1586353 = 1189765) (by norm_num)
theorem B2380981 : Blo 1409524 2380981 := bbase (se 5 (by rfl) ⟨111608, by rfl⟩ : syracuseStep 2380981 = 223217) (by norm_num)
theorem B3175613 : Blo 1409524 3175613 := bbase (se 3 (by rfl) ⟨595427, by rfl⟩ : syracuseStep 3175613 = 1190855) (by norm_num)
theorem B2675909 : Blo 1409524 2675909 := bbase (se 4 (by rfl) ⟨250866, by rfl⟩ : syracuseStep 2675909 = 501733) (by norm_num)
theorem B1586389 : Blo 1409524 1586389 := bbase (se 7 (by rfl) ⟨18590, by rfl⟩ : syracuseStep 1586389 = 37181) (by norm_num)
theorem B1586425 : Blo 1409524 1586425 := bbase (se 2 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 1586425 = 1189819) (by norm_num)
theorem B3175685 : Blo 1409524 3175685 := bbase (se 4 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 3175685 = 595441) (by norm_num)
theorem B3052813 : Blo 1409524 3052813 := bbase (se 3 (by rfl) ⟨572402, by rfl⟩ : syracuseStep 3052813 = 1144805) (by norm_num)
theorem B2381069 : Blo 1409524 2381069 := bbase (se 3 (by rfl) ⟨446450, by rfl⟩ : syracuseStep 2381069 = 892901) (by norm_num)
theorem B10704149 : Blo 1409524 10704149 := bbase (se 6 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 10704149 = 501757) (by norm_num)
theorem B1586461 : Blo 1409524 1586461 := bbase (se 3 (by rfl) ⟨297461, by rfl⟩ : syracuseStep 1586461 = 594923) (by norm_num)
theorem B1586497 : Blo 1409524 1586497 := bbase (se 2 (by rfl) ⟨594936, by rfl⟩ : syracuseStep 1586497 = 1189873) (by norm_num)
theorem B3011909 : Blo 1409524 3011909 := bbase (se 4 (by rfl) ⟨282366, by rfl⟩ : syracuseStep 3011909 = 564733) (by norm_num)
theorem B3175757 : Blo 1409524 3175757 := bbase (se 3 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 3175757 = 1190909) (by norm_num)
theorem B2676053 : Blo 1409524 2676053 := bbase (se 15 (by rfl) ⟨122, by rfl⟩ : syracuseStep 2676053 = 245) (by norm_num)
theorem B3568981 : Blo 1409524 3568981 := bbase (se 13 (by rfl) ⟨653, by rfl⟩ : syracuseStep 3568981 = 1307) (by norm_num)
theorem B1586533 : Blo 1409524 1586533 := bbase (se 4 (by rfl) ⟨148737, by rfl⟩ : syracuseStep 1586533 = 297475) (by norm_num)
theorem B5354869 : Blo 1409524 5354869 := bbase (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) (by norm_num)
theorem B1586569 : Blo 1409524 1586569 := bbase (se 2 (by rfl) ⟨594963, by rfl⟩ : syracuseStep 1586569 = 1189927) (by norm_num)
theorem B2258317 : Blo 1409524 2258317 := bbase (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) (by norm_num)
theorem B2381197 : Blo 1409524 2381197 := bbase (se 3 (by rfl) ⟨446474, by rfl⟩ : syracuseStep 2381197 = 892949) (by norm_num)
theorem B3175829 : Blo 1409524 3175829 := bbase (se 6 (by rfl) ⟨74433, by rfl⟩ : syracuseStep 3175829 = 148867) (by norm_num)
theorem B1586605 : Blo 1409524 1586605 := bbase (se 3 (by rfl) ⟨297488, by rfl⟩ : syracuseStep 1586605 = 594977) (by norm_num)
theorem B3569093 : Blo 1409524 3569093 := bbase (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) (by norm_num)
theorem B1586641 : Blo 1409524 1586641 := bbase (se 2 (by rfl) ⟨594990, by rfl⟩ : syracuseStep 1586641 = 1189981) (by norm_num)
theorem B3175901 : Blo 1409524 3175901 := bbase (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) (by norm_num)
theorem B2381285 : Blo 1409524 2381285 := bbase (se 4 (by rfl) ⟨223245, by rfl⟩ : syracuseStep 2381285 = 446491) (by norm_num)
theorem B1586677 : Blo 1409524 1586677 := bbase (se 5 (by rfl) ⟨74375, by rfl⟩ : syracuseStep 1586677 = 148751) (by norm_num)
theorem B1586713 : Blo 1409524 1586713 := bbase (se 2 (by rfl) ⟨595017, by rfl⟩ : syracuseStep 1586713 = 1190035) (by norm_num)
theorem B3012149 : Blo 1409524 3012149 := bbase (se 5 (by rfl) ⟨141194, by rfl⟩ : syracuseStep 3012149 = 282389) (by norm_num)
theorem B1586749 : Blo 1409524 1586749 := bbase (se 3 (by rfl) ⟨297515, by rfl⟩ : syracuseStep 1586749 = 595031) (by norm_num)
theorem B1586785 : Blo 1409524 1586785 := bbase (se 2 (by rfl) ⟨595044, by rfl⟩ : syracuseStep 1586785 = 1190089) (by norm_num)
theorem B2381413 : Blo 1409524 2381413 := bbase (se 4 (by rfl) ⟨223257, by rfl⟩ : syracuseStep 2381413 = 446515) (by norm_num)
theorem B2676341 : Blo 1409524 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B3389053 : Blo 1409524 3389053 := bbase (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) (by norm_num)
theorem B3569285 : Blo 1409524 3569285 := bbase (se 4 (by rfl) ⟨334620, by rfl⟩ : syracuseStep 3569285 = 669241) (by norm_num)
theorem B1586821 : Blo 1409524 1586821 := bbase (se 4 (by rfl) ⟨148764, by rfl⟩ : syracuseStep 1586821 = 297529) (by norm_num)
theorem B5355173 : Blo 1409524 5355173 := bbase (se 4 (by rfl) ⟨502047, by rfl⟩ : syracuseStep 5355173 = 1004095) (by norm_num)
theorem B1586857 : Blo 1409524 1586857 := bbase (se 2 (by rfl) ⟨595071, by rfl⟩ : syracuseStep 1586857 = 1190143) (by norm_num)
theorem B10303157 : Blo 1409524 10303157 := bbase (se 5 (by rfl) ⟨482960, by rfl⟩ : syracuseStep 10303157 = 965921) (by norm_num)
theorem B2381501 : Blo 1409524 2381501 := bbase (se 3 (by rfl) ⟨446531, by rfl⟩ : syracuseStep 2381501 = 893063) (by norm_num)
theorem B1586893 : Blo 1409524 1586893 := bbase (se 3 (by rfl) ⟨297542, by rfl⟩ : syracuseStep 1586893 = 595085) (by norm_num)
theorem B1586929 : Blo 1409524 1586929 := bbase (se 2 (by rfl) ⟨595098, by rfl⟩ : syracuseStep 1586929 = 1190197) (by norm_num)
theorem B4757237 : Blo 1409524 4757237 := bbase (se 5 (by rfl) ⟨222995, by rfl⟩ : syracuseStep 4757237 = 445991) (by norm_num)
theorem B2676493 : Blo 1409524 2676493 := bbase (se 3 (by rfl) ⟨501842, by rfl⟩ : syracuseStep 2676493 = 1003685) (by norm_num)
theorem B1586965 : Blo 1409524 1586965 := bbase (se 6 (by rfl) ⟨37194, by rfl⟩ : syracuseStep 1586965 = 74389) (by norm_num)
theorem B6108949 : Blo 1409524 6108949 := bbase (se 6 (by rfl) ⟨143178, by rfl⟩ : syracuseStep 6108949 = 286357) (by norm_num)
theorem B2258741 : Blo 1409524 2258741 := bbase (se 5 (by rfl) ⟨105878, by rfl⟩ : syracuseStep 2258741 = 211757) (by norm_num)
theorem B1587001 : Blo 1409524 1587001 := bbase (se 2 (by rfl) ⟨595125, by rfl⟩ : syracuseStep 1587001 = 1190251) (by norm_num)
theorem B2381629 : Blo 1409524 2381629 := bbase (se 3 (by rfl) ⟨446555, by rfl⟩ : syracuseStep 2381629 = 893111) (by norm_num)
theorem B1587037 : Blo 1409524 1587037 := bbase (se 3 (by rfl) ⟨297569, by rfl⟩ : syracuseStep 1587037 = 595139) (by norm_num)
theorem B1587073 : Blo 1409524 1587073 := bbase (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) (by norm_num)
theorem B2381717 : Blo 1409524 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B1587109 : Blo 1409524 1587109 := bbase (se 4 (by rfl) ⟨148791, by rfl⟩ : syracuseStep 1587109 = 297583) (by norm_num)
theorem B2144173 : Blo 1409524 2144173 := bbase (se 3 (by rfl) ⟨402032, by rfl⟩ : syracuseStep 2144173 = 804065) (by norm_num)
theorem B1587145 : Blo 1409524 1587145 := bbase (se 2 (by rfl) ⟨595179, by rfl⟩ : syracuseStep 1587145 = 1190359) (by norm_num)
theorem B1505233 : Blo 1409524 1505233 := bbase (se 2 (by rfl) ⟨564462, by rfl⟩ : syracuseStep 1505233 = 1128925) (by norm_num)
theorem B1505237 : Blo 1409524 1505237 := bbase (se 7 (by rfl) ⟨17639, by rfl⟩ : syracuseStep 1505237 = 35279) (by norm_num)
theorem B1693657 : Blo 1409524 1693657 := bbase (se 2 (by rfl) ⟨635121, by rfl⟩ : syracuseStep 1693657 = 1270243) (by norm_num)
theorem B3569629 : Blo 1409524 3569629 := bbase (se 3 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 3569629 = 1338611) (by norm_num)
theorem B1587181 : Blo 1409524 1587181 := bbase (se 3 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 1587181 = 595193) (by norm_num)
theorem B10172405 : Blo 1409524 10172405 := bbase (se 5 (by rfl) ⟨476831, by rfl⟩ : syracuseStep 10172405 = 953663) (by norm_num)
theorem B1587217 : Blo 1409524 1587217 := bbase (se 2 (by rfl) ⟨595206, by rfl⟩ : syracuseStep 1587217 = 1190413) (by norm_num)
theorem B2381845 : Blo 1409524 2381845 := bbase (se 6 (by rfl) ⟨55824, by rfl⟩ : syracuseStep 2381845 = 111649) (by norm_num)
theorem B3012653 : Blo 1409524 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B3012661 : Blo 1409524 3012661 := bbase (se 5 (by rfl) ⟨141218, by rfl⟩ : syracuseStep 3012661 = 282437) (by norm_num)
theorem B1587253 : Blo 1409524 1587253 := bbase (se 5 (by rfl) ⟨74402, by rfl⟩ : syracuseStep 1587253 = 148805) (by norm_num)
theorem B2676797 : Blo 1409524 2676797 := bbase (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) (by norm_num)
theorem B7141445 : Blo 1409524 7141445 := bbase (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) (by norm_num)
theorem B3569741 : Blo 1409524 3569741 := bbase (se 3 (by rfl) ⟨669326, by rfl⟩ : syracuseStep 3569741 = 1338653) (by norm_num)
theorem B2259029 : Blo 1409524 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B1587289 : Blo 1409524 1587289 := bbase (se 2 (by rfl) ⟨595233, by rfl⟩ : syracuseStep 1587289 = 1190467) (by norm_num)
theorem B2381933 : Blo 1409524 2381933 := bbase (se 3 (by rfl) ⟨446612, by rfl⟩ : syracuseStep 2381933 = 893225) (by norm_num)
theorem B1587325 : Blo 1409524 1587325 := bbase (se 3 (by rfl) ⟨297623, by rfl⟩ : syracuseStep 1587325 = 595247) (by norm_num)
theorem B4520069 : Blo 1409524 4520069 := bbase (se 4 (by rfl) ⟨423756, by rfl⟩ : syracuseStep 4520069 = 847513) (by norm_num)
theorem B1587361 : Blo 1409524 1587361 := bbase (se 2 (by rfl) ⟨595260, by rfl⟩ : syracuseStep 1587361 = 1190521) (by norm_num)
theorem B4757669 : Blo 1409524 4757669 := bbase (se 4 (by rfl) ⟨446031, by rfl⟩ : syracuseStep 4757669 = 892063) (by norm_num)
theorem B1587397 : Blo 1409524 1587397 := bbase (se 4 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 1587397 = 297637) (by norm_num)
theorem B6027493 : Blo 1409524 6027493 := bbase (se 4 (by rfl) ⟨565077, by rfl⟩ : syracuseStep 6027493 = 1130155) (by norm_num)
theorem B1587433 : Blo 1409524 1587433 := bbase (se 2 (by rfl) ⟨595287, by rfl⟩ : syracuseStep 1587433 = 1190575) (by norm_num)
theorem B1784045 : Blo 1409524 1784045 := bbase (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) (by norm_num)
theorem B3217645 : Blo 1409524 3217645 := bbase (se 3 (by rfl) ⟨603308, by rfl⟩ : syracuseStep 3217645 = 1206617) (by norm_num)
theorem B6027509 : Blo 1409524 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B3569933 : Blo 1409524 3569933 := bbase (se 3 (by rfl) ⟨669362, by rfl⟩ : syracuseStep 3569933 = 1338725) (by norm_num)
theorem B1587469 : Blo 1409524 1587469 := bbase (se 3 (by rfl) ⟨297650, by rfl⟩ : syracuseStep 1587469 = 595301) (by norm_num)
theorem B3389725 : Blo 1409524 3389725 := bbase (se 3 (by rfl) ⟨635573, by rfl⟩ : syracuseStep 3389725 = 1271147) (by norm_num)
theorem B1784101 : Blo 1409524 1784101 := bbase (se 4 (by rfl) ⟨167259, by rfl⟩ : syracuseStep 1784101 = 334519) (by norm_num)
theorem B1587505 : Blo 1409524 1587505 := bbase (se 2 (by rfl) ⟨595314, by rfl⟩ : syracuseStep 1587505 = 1190629) (by norm_num)
theorem B19298645 : Blo 1409524 19298645 := bbase (se 10 (by rfl) ⟨28269, by rfl⟩ : syracuseStep 19298645 = 56539) (by norm_num)
theorem B1587541 : Blo 1409524 1587541 := bbase (se 10 (by rfl) ⟨2325, by rfl⟩ : syracuseStep 1587541 = 4651) (by norm_num)
theorem B1587577 : Blo 1409524 1587577 := bbase (se 2 (by rfl) ⟨595341, by rfl⟩ : syracuseStep 1587577 = 1190683) (by norm_num)
theorem B1784197 : Blo 1409524 1784197 := bbase (se 4 (by rfl) ⟨167268, by rfl⟩ : syracuseStep 1784197 = 334537) (by norm_num)
theorem B5151125 : Blo 1409524 5151125 := bbase (se 6 (by rfl) ⟨120729, by rfl⟩ : syracuseStep 5151125 = 241459) (by norm_num)
theorem B6781333 : Blo 1409524 6781333 := bbase (se 6 (by rfl) ⟨158937, by rfl⟩ : syracuseStep 6781333 = 317875) (by norm_num)
theorem B1587613 : Blo 1409524 1587613 := bbase (se 3 (by rfl) ⟨297677, by rfl⟩ : syracuseStep 1587613 = 595355) (by norm_num)
theorem B1587649 : Blo 1409524 1587649 := bbase (se 2 (by rfl) ⟨595368, by rfl⟩ : syracuseStep 1587649 = 1190737) (by norm_num)
theorem B1587685 : Blo 1409524 1587685 := bbase (se 4 (by rfl) ⟨148845, by rfl⟩ : syracuseStep 1587685 = 297691) (by norm_num)
theorem B3389957 : Blo 1409524 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B1505801 : Blo 1409524 1505801 := bbase (se 2 (by rfl) ⟨564675, by rfl⟩ : syracuseStep 1505801 = 1129351) (by norm_num)
theorem B1587721 : Blo 1409524 1587721 := bbase (se 2 (by rfl) ⟨595395, by rfl⟩ : syracuseStep 1587721 = 1190791) (by norm_num)
theorem B11434517 : Blo 1409524 11434517 := bbase (se 6 (by rfl) ⟨267996, by rfl⟩ : syracuseStep 11434517 = 535993) (by norm_num)
theorem B1587757 : Blo 1409524 1587757 := bbase (se 3 (by rfl) ⟨297704, by rfl⟩ : syracuseStep 1587757 = 595409) (by norm_num)
theorem B1784369 : Blo 1409524 1784369 := bbase (se 2 (by rfl) ⟨669138, by rfl⟩ : syracuseStep 1784369 = 1338277) (by norm_num)
theorem B3390005 : Blo 1409524 3390005 := bbase (se 5 (by rfl) ⟨158906, by rfl⟩ : syracuseStep 3390005 = 317813) (by norm_num)
theorem B1587793 : Blo 1409524 1587793 := bbase (se 2 (by rfl) ⟨595422, by rfl⟩ : syracuseStep 1587793 = 1190845) (by norm_num)
theorem B4758101 : Blo 1409524 4758101 := bbase (se 8 (by rfl) ⟨27879, by rfl⟩ : syracuseStep 4758101 = 55759) (by norm_num)
theorem B12057173 : Blo 1409524 12057173 := bbase (se 8 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 12057173 = 141295) (by norm_num)
theorem B3570277 : Blo 1409524 3570277 := bbase (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) (by norm_num)
theorem B1784425 : Blo 1409524 1784425 := bbase (se 2 (by rfl) ⟨669159, by rfl⟩ : syracuseStep 1784425 = 1338319) (by norm_num)
theorem B1587829 : Blo 1409524 1587829 := bbase (se 5 (by rfl) ⟨74429, by rfl⟩ : syracuseStep 1587829 = 148859) (by norm_num)
theorem B1694353 : Blo 1409524 1694353 := bbase (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) (by norm_num)
theorem B1587865 : Blo 1409524 1587865 := bbase (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) (by norm_num)
theorem B1587901 : Blo 1409524 1587901 := bbase (se 3 (by rfl) ⟨297731, by rfl⟩ : syracuseStep 1587901 = 595463) (by norm_num)
theorem B1694401 : Blo 1409524 1694401 := bbase (se 2 (by rfl) ⟨635400, by rfl⟩ : syracuseStep 1694401 = 1270801) (by norm_num)
theorem B1505989 : Blo 1409524 1505989 := bbase (se 4 (by rfl) ⟨141186, by rfl⟩ : syracuseStep 1505989 = 282373) (by norm_num)
theorem B1784521 : Blo 1409524 1784521 := bbase (se 2 (by rfl) ⟨669195, by rfl⟩ : syracuseStep 1784521 = 1338391) (by norm_num)
theorem B3570389 : Blo 1409524 3570389 := bbase (se 7 (by rfl) ⟨41840, by rfl⟩ : syracuseStep 3570389 = 83681) (by norm_num)
theorem B8583893 : Blo 1409524 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B1587937 : Blo 1409524 1587937 := bbase (se 2 (by rfl) ⟨595476, by rfl⟩ : syracuseStep 1587937 = 1190953) (by norm_num)
theorem B9042677 : Blo 1409524 9042677 := bbase (se 5 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 9042677 = 847751) (by norm_num)
theorem B5716757 : Blo 1409524 5716757 := bbase (se 6 (by rfl) ⟨133986, by rfl⟩ : syracuseStep 5716757 = 267973) (by norm_num)
theorem B2677549 : Blo 1409524 2677549 := bbase (se 3 (by rfl) ⟨502040, by rfl⟩ : syracuseStep 2677549 = 1004081) (by norm_num)
theorem B1784693 : Blo 1409524 1784693 := bbase (se 5 (by rfl) ⟨83657, by rfl⟩ : syracuseStep 1784693 = 167315) (by norm_num)
theorem B2259829 : Blo 1409524 2259829 := bbase (se 5 (by rfl) ⟨105929, by rfl⟩ : syracuseStep 2259829 = 211859) (by norm_num)
theorem B11598709 : Blo 1409524 11598709 := bbase (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) (by norm_num)
theorem B3570581 : Blo 1409524 3570581 := bbase (se 6 (by rfl) ⟨83685, by rfl⟩ : syracuseStep 3570581 = 167371) (by norm_num)
theorem B1784749 : Blo 1409524 1784749 := bbase (se 3 (by rfl) ⟨334640, by rfl⟩ : syracuseStep 1784749 = 669281) (by norm_num)
theorem B2677693 : Blo 1409524 2677693 := bbase (se 3 (by rfl) ⟨502067, by rfl⟩ : syracuseStep 2677693 = 1004135) (by norm_num)
theorem B4758533 : Blo 1409524 4758533 := bbase (se 4 (by rfl) ⟨446112, by rfl⟩ : syracuseStep 4758533 = 892225) (by norm_num)
theorem B2898949 : Blo 1409524 2898949 := bbase (se 4 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 2898949 = 543553) (by norm_num)
theorem B1784845 : Blo 1409524 1784845 := bbase (se 3 (by rfl) ⟨334658, by rfl⟩ : syracuseStep 1784845 = 669317) (by norm_num)
theorem B2858005 : Blo 1409524 2858005 := bbase (se 6 (by rfl) ⟨66984, by rfl⟩ : syracuseStep 2858005 = 133969) (by norm_num)
theorem B2858021 : Blo 1409524 2858021 := bbase (se 4 (by rfl) ⟨267939, by rfl⟩ : syracuseStep 2858021 = 535879) (by norm_num)
theorem B2145341 : Blo 1409524 2145341 := bbase (se 3 (by rfl) ⟨402251, by rfl⟩ : syracuseStep 2145341 = 804503) (by norm_num)
theorem B2858053 : Blo 1409524 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B2677853 : Blo 1409524 2677853 := bbase (se 3 (by rfl) ⟨502097, by rfl⟩ : syracuseStep 2677853 = 1004195) (by norm_num)
theorem B3013789 : Blo 1409524 3013789 := bbase (se 3 (by rfl) ⟨565085, by rfl⟩ : syracuseStep 3013789 = 1130171) (by norm_num)
theorem B1785017 : Blo 1409524 1785017 := bbase (se 2 (by rfl) ⟨669381, by rfl⟩ : syracuseStep 1785017 = 1338763) (by norm_num)
theorem B20102357 : Blo 1409524 20102357 := bbase (se 7 (by rfl) ⟨235574, by rfl⟩ : syracuseStep 20102357 = 471149) (by norm_num)
theorem B2677997 : Blo 1409524 2677997 := bbase (se 3 (by rfl) ⟨502124, by rfl⟩ : syracuseStep 2677997 = 1004249) (by norm_num)
theorem B3570925 : Blo 1409524 3570925 := bbase (se 3 (by rfl) ⟨669548, by rfl⟩ : syracuseStep 3570925 = 1339097) (by norm_num)
theorem B1785073 : Blo 1409524 1785073 := bbase (se 2 (by rfl) ⟨669402, by rfl⟩ : syracuseStep 1785073 = 1338805) (by norm_num)
theorem B8142133 : Blo 1409524 8142133 := bbase (se 5 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 8142133 = 763325) (by norm_num)
theorem B1785169 : Blo 1409524 1785169 := bbase (se 2 (by rfl) ⟨669438, by rfl⟩ : syracuseStep 1785169 = 1338877) (by norm_num)
theorem B7142741 : Blo 1409524 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B3571037 : Blo 1409524 3571037 := bbase (se 3 (by rfl) ⟨669569, by rfl⟩ : syracuseStep 3571037 = 1339139) (by norm_num)
theorem B4521349 : Blo 1409524 4521349 := bbase (se 4 (by rfl) ⟨423876, by rfl⟩ : syracuseStep 4521349 = 847753) (by norm_num)
theorem B2260381 : Blo 1409524 2260381 := bbase (se 3 (by rfl) ⟨423821, by rfl⟩ : syracuseStep 2260381 = 847643) (by norm_num)
theorem B4758965 : Blo 1409524 4758965 := bbase (se 5 (by rfl) ⟨223076, by rfl⟩ : syracuseStep 4758965 = 446153) (by norm_num)
theorem B3620285 : Blo 1409524 3620285 := bbase (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) (by norm_num)
theorem B6438341 : Blo 1409524 6438341 := bbase (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) (by norm_num)
theorem B1506809 : Blo 1409524 1506809 := bbase (se 2 (by rfl) ⟨565053, by rfl⟩ : syracuseStep 1506809 = 1130107) (by norm_num)
theorem B1785341 : Blo 1409524 1785341 := bbase (se 3 (by rfl) ⟨334751, by rfl⟩ : syracuseStep 1785341 = 669503) (by norm_num)
theorem B2678285 : Blo 1409524 2678285 := bbase (se 3 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 2678285 = 1004357) (by norm_num)
theorem B3014165 : Blo 1409524 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B3571229 : Blo 1409524 3571229 := bbase (se 3 (by rfl) ⟨669605, by rfl⟩ : syracuseStep 3571229 = 1339211) (by norm_num)
theorem B9035317 : Blo 1409524 9035317 := bbase (se 5 (by rfl) ⟨423530, by rfl⟩ : syracuseStep 9035317 = 847061) (by norm_num)
theorem B1785397 : Blo 1409524 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B1785493 : Blo 1409524 1785493 := bbase (se 6 (by rfl) ⟨41847, by rfl⟩ : syracuseStep 1785493 = 83695) (by norm_num)
theorem B3620501 : Blo 1409524 3620501 := bbase (se 6 (by rfl) ⟨84855, by rfl⟩ : syracuseStep 3620501 = 169711) (by norm_num)
theorem B2260637 : Blo 1409524 2260637 := bbase (se 3 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 2260637 = 847739) (by norm_num)
theorem B2678437 : Blo 1409524 2678437 := bbase (se 4 (by rfl) ⟨251103, by rfl⟩ : syracuseStep 2678437 = 502207) (by norm_num)
theorem B1695449 : Blo 1409524 1695449 := bbase (se 2 (by rfl) ⟨635793, by rfl⟩ : syracuseStep 1695449 = 1271587) (by norm_num)
theorem B5357285 : Blo 1409524 5357285 := bbase (se 4 (by rfl) ⟨502245, by rfl⟩ : syracuseStep 5357285 = 1004491) (by norm_num)
theorem B1785665 : Blo 1409524 1785665 := bbase (se 2 (by rfl) ⟨669624, by rfl⟩ : syracuseStep 1785665 = 1339249) (by norm_num)
theorem B4759397 : Blo 1409524 4759397 := bbase (se 4 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 4759397 = 892387) (by norm_num)
theorem B3571573 : Blo 1409524 3571573 := bbase (se 5 (by rfl) ⟨167417, by rfl⟩ : syracuseStep 3571573 = 334835) (by norm_num)
theorem B1785721 : Blo 1409524 1785721 := bbase (se 2 (by rfl) ⟨669645, by rfl⟩ : syracuseStep 1785721 = 1339291) (by norm_num)
theorem B3391397 : Blo 1409524 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B1449905 : Blo 1409524 1449905 := bbase (se 2 (by rfl) ⟨543714, by rfl⟩ : syracuseStep 1449905 = 1087429) (by norm_num)
theorem B1507253 : Blo 1409524 1507253 := bbase (se 5 (by rfl) ⟨70652, by rfl⟩ : syracuseStep 1507253 = 141305) (by norm_num)
theorem B2678741 : Blo 1409524 2678741 := bbase (se 7 (by rfl) ⟨31391, by rfl⟩ : syracuseStep 2678741 = 62783) (by norm_num)
theorem B1785817 : Blo 1409524 1785817 := bbase (se 2 (by rfl) ⟨669681, by rfl⟩ : syracuseStep 1785817 = 1339363) (by norm_num)
theorem B3571685 : Blo 1409524 3571685 := bbase (se 4 (by rfl) ⟨334845, by rfl⟩ : syracuseStep 3571685 = 669691) (by norm_num)
theorem B3620837 : Blo 1409524 3620837 := bbase (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) (by norm_num)
theorem B3571715 : Blo 1409524 3571715 := bstep (se 1 (by rfl) ⟨2678786, by rfl⟩ : syracuseStep 3571715 = 5357573) B5357573
theorem B5357603 : Blo 1409524 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B15450211 : Blo 1409524 15450211 := bstep (se 1 (by rfl) ⟨11587658, by rfl⟩ : syracuseStep 15450211 = 23175317) B23175317
theorem B4014193 : Blo 1409524 4014193 := bstep (se 2 (by rfl) ⟨1505322, by rfl⟩ : syracuseStep 4014193 = 3010645) B3010645
theorem B3670147 : Blo 1409524 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B11436173 : Blo 1409524 11436173 := bstep (se 3 (by rfl) ⟨2144282, by rfl⟩ : syracuseStep 11436173 = 4288565) B4288565
theorem B17400035 : Blo 1409524 17400035 := bstep (se 1 (by rfl) ⟨13050026, by rfl⟩ : syracuseStep 17400035 = 26100053) B26100053
theorem B4014353 : Blo 1409524 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B8036657 : Blo 1409524 8036657 := bstep (se 2 (by rfl) ⟨3013746, by rfl⟩ : syracuseStep 8036657 = 6027493) B6027493
theorem B4350257 : Blo 1409524 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B2007347 : Blo 1409524 2007347 := bstep (se 1 (by rfl) ⟨1505510, by rfl⟩ : syracuseStep 2007347 = 3011021) B3011021
theorem B4014467 : Blo 1409524 4014467 := bstep (se 1 (by rfl) ⟨3010850, by rfl⟩ : syracuseStep 4014467 = 6021701) B6021701
theorem B4760045 : Blo 1409524 4760045 := bstep (se 3 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 4760045 = 1785017) B1785017
theorem B1409539 : Blo 1409524 1409539 := bstep (se 1 (by rfl) ⟨1057154, by rfl⟩ : syracuseStep 1409539 = 2114309) B2114309
theorem B1409555 : Blo 1409524 1409555 := bstep (se 1 (by rfl) ⟨1057166, by rfl⟩ : syracuseStep 1409555 = 2114333) B2114333
theorem B1409571 : Blo 1409524 1409571 := bstep (se 1 (by rfl) ⟨1057178, by rfl⟩ : syracuseStep 1409571 = 2114357) B2114357
theorem B4760099 : Blo 1409524 4760099 := bstep (se 1 (by rfl) ⟨3570074, by rfl⟩ : syracuseStep 4760099 = 7140149) B7140149
theorem B7725617 : Blo 1409524 7725617 := bstep (se 2 (by rfl) ⟨2897106, by rfl⟩ : syracuseStep 7725617 = 5794213) B5794213
theorem B1409587 : Blo 1409524 1409587 := bstep (se 1 (by rfl) ⟨1057190, by rfl⟩ : syracuseStep 1409587 = 2114381) B2114381
theorem B1409603 : Blo 1409524 1409603 := bstep (se 1 (by rfl) ⟨1057202, by rfl⟩ : syracuseStep 1409603 = 2114405) B2114405
theorem B1409619 : Blo 1409524 1409619 := bstep (se 1 (by rfl) ⟨1057214, by rfl⟩ : syracuseStep 1409619 = 2114429) B2114429
theorem B1409635 : Blo 1409524 1409635 := bstep (se 1 (by rfl) ⟨1057226, by rfl⟩ : syracuseStep 1409635 = 2114453) B2114453
theorem B2679409 : Blo 1409524 2679409 := bstep (se 2 (by rfl) ⟨1004778, by rfl⟩ : syracuseStep 2679409 = 2009557) B2009557
theorem B1409651 : Blo 1409524 1409651 := bstep (se 1 (by rfl) ⟨1057238, by rfl⟩ : syracuseStep 1409651 = 2114477) B2114477
theorem B1409667 : Blo 1409524 1409667 := bstep (se 1 (by rfl) ⟨1057250, by rfl⟩ : syracuseStep 1409667 = 2114501) B2114501
theorem B1409683 : Blo 1409524 1409683 := bstep (se 1 (by rfl) ⟨1057262, by rfl⟩ : syracuseStep 1409683 = 2114525) B2114525
theorem B1409699 : Blo 1409524 1409699 := bstep (se 1 (by rfl) ⟨1057274, by rfl⟩ : syracuseStep 1409699 = 2114549) B2114549
theorem B5358257 : Blo 1409524 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B1409715 : Blo 1409524 1409715 := bstep (se 1 (by rfl) ⟨1057286, by rfl⟩ : syracuseStep 1409715 = 2114573) B2114573
theorem B1409731 : Blo 1409524 1409731 := bstep (se 1 (by rfl) ⟨1057298, by rfl⟩ : syracuseStep 1409731 = 2114597) B2114597
theorem B1409747 : Blo 1409524 1409747 := bstep (se 1 (by rfl) ⟨1057310, by rfl⟩ : syracuseStep 1409747 = 2114621) B2114621
theorem B1409763 : Blo 1409524 1409763 := bstep (se 1 (by rfl) ⟨1057322, by rfl⟩ : syracuseStep 1409763 = 2114645) B2114645
theorem B2114291 : Blo 1409524 2114291 := bstep (se 1 (by rfl) ⟨1585718, by rfl⟩ : syracuseStep 2114291 = 3171437) B3171437
theorem B1409779 : Blo 1409524 1409779 := bstep (se 1 (by rfl) ⟨1057334, by rfl⟩ : syracuseStep 1409779 = 2114669) B2114669
theorem B1409795 : Blo 1409524 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B2114321 : Blo 1409524 2114321 := bstep (se 2 (by rfl) ⟨792870, by rfl⟩ : syracuseStep 2114321 = 1585741) B1585741
theorem B1409811 : Blo 1409524 1409811 := bstep (se 1 (by rfl) ⟨1057358, by rfl⟩ : syracuseStep 1409811 = 2114717) B2114717
theorem B2114339 : Blo 1409524 2114339 := bstep (se 1 (by rfl) ⟨1585754, by rfl⟩ : syracuseStep 2114339 = 3171509) B3171509
theorem B1409827 : Blo 1409524 1409827 := bstep (se 1 (by rfl) ⟨1057370, by rfl⟩ : syracuseStep 1409827 = 2114741) B2114741
theorem B4760369 : Blo 1409524 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B1409843 : Blo 1409524 1409843 := bstep (se 1 (by rfl) ⟨1057382, by rfl⟩ : syracuseStep 1409843 = 2114765) B2114765
theorem B2114369 : Blo 1409524 2114369 := bstep (se 2 (by rfl) ⟨792888, by rfl⟩ : syracuseStep 2114369 = 1585777) B1585777
theorem B1409859 : Blo 1409524 1409859 := bstep (se 1 (by rfl) ⟨1057394, by rfl⟩ : syracuseStep 1409859 = 2114789) B2114789
theorem B2114387 : Blo 1409524 2114387 := bstep (se 1 (by rfl) ⟨1585790, by rfl⟩ : syracuseStep 2114387 = 3171581) B3171581
theorem B1409875 : Blo 1409524 1409875 := bstep (se 1 (by rfl) ⟨1057406, by rfl⟩ : syracuseStep 1409875 = 2114813) B2114813
theorem B7136099 : Blo 1409524 7136099 := bstep (se 1 (by rfl) ⟨5352074, by rfl⟩ : syracuseStep 7136099 = 10704149) B10704149
theorem B1409891 : Blo 1409524 1409891 := bstep (se 1 (by rfl) ⟨1057418, by rfl⟩ : syracuseStep 1409891 = 2114837) B2114837
theorem B2114417 : Blo 1409524 2114417 := bstep (se 2 (by rfl) ⟨792906, by rfl⟩ : syracuseStep 2114417 = 1585813) B1585813
theorem B1409907 : Blo 1409524 1409907 := bstep (se 1 (by rfl) ⟨1057430, by rfl⟩ : syracuseStep 1409907 = 2114861) B2114861
theorem B2114435 : Blo 1409524 2114435 := bstep (se 1 (by rfl) ⟨1585826, by rfl⟩ : syracuseStep 2114435 = 3171653) B3171653
theorem B1409923 : Blo 1409524 1409923 := bstep (se 1 (by rfl) ⟨1057442, by rfl⟩ : syracuseStep 1409923 = 2114885) B2114885
theorem B1409939 : Blo 1409524 1409939 := bstep (se 1 (by rfl) ⟨1057454, by rfl⟩ : syracuseStep 1409939 = 2114909) B2114909
theorem B2114465 : Blo 1409524 2114465 := bstep (se 2 (by rfl) ⟨792924, by rfl⟩ : syracuseStep 2114465 = 1585849) B1585849
theorem B1409955 : Blo 1409524 1409955 := bstep (se 1 (by rfl) ⟨1057466, by rfl⟩ : syracuseStep 1409955 = 2114933) B2114933
theorem B2007985 : Blo 1409524 2007985 := bstep (se 2 (by rfl) ⟨752994, by rfl⟩ : syracuseStep 2007985 = 1505989) B1505989
theorem B3572657 : Blo 1409524 3572657 := bstep (se 2 (by rfl) ⟨1339746, by rfl⟩ : syracuseStep 3572657 = 2679493) B2679493
theorem B2114483 : Blo 1409524 2114483 := bstep (se 1 (by rfl) ⟨1585862, by rfl⟩ : syracuseStep 2114483 = 3171725) B3171725
theorem B1409971 : Blo 1409524 1409971 := bstep (se 1 (by rfl) ⟨1057478, by rfl⟩ : syracuseStep 1409971 = 2114957) B2114957
theorem B1409987 : Blo 1409524 1409987 := bstep (se 1 (by rfl) ⟨1057490, by rfl⟩ : syracuseStep 1409987 = 2114981) B2114981
theorem B2114513 : Blo 1409524 2114513 := bstep (se 2 (by rfl) ⟨792942, by rfl⟩ : syracuseStep 2114513 = 1585885) B1585885
theorem B1410003 : Blo 1409524 1410003 := bstep (se 1 (by rfl) ⟨1057502, by rfl⟩ : syracuseStep 1410003 = 2115005) B2115005
theorem B2114531 : Blo 1409524 2114531 := bstep (se 1 (by rfl) ⟨1585898, by rfl⟩ : syracuseStep 2114531 = 3171797) B3171797
theorem B1410019 : Blo 1409524 1410019 := bstep (se 1 (by rfl) ⟨1057514, by rfl⟩ : syracuseStep 1410019 = 2115029) B2115029
theorem B3572707 : Blo 1409524 3572707 := bstep (se 1 (by rfl) ⟨2679530, by rfl⟩ : syracuseStep 3572707 = 5359061) B5359061
theorem B1410035 : Blo 1409524 1410035 := bstep (se 1 (by rfl) ⟨1057526, by rfl⟩ : syracuseStep 1410035 = 2115053) B2115053
theorem B2114561 : Blo 1409524 2114561 := bstep (se 2 (by rfl) ⟨792960, by rfl⟩ : syracuseStep 2114561 = 1585921) B1585921
theorem B1410051 : Blo 1409524 1410051 := bstep (se 1 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 1410051 = 2115077) B2115077
theorem B9036805 : Blo 1409524 9036805 := bstep (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) B1694401
theorem B2114579 : Blo 1409524 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B1410067 : Blo 1409524 1410067 := bstep (se 1 (by rfl) ⟨1057550, by rfl⟩ : syracuseStep 1410067 = 2115101) B2115101
theorem B1410083 : Blo 1409524 1410083 := bstep (se 1 (by rfl) ⟨1057562, by rfl⟩ : syracuseStep 1410083 = 2115125) B2115125
theorem B2008099 : Blo 1409524 2008099 := bstep (se 1 (by rfl) ⟨1506074, by rfl⟩ : syracuseStep 2008099 = 3012149) B3012149
theorem B2114609 : Blo 1409524 2114609 := bstep (se 2 (by rfl) ⟨792978, by rfl⟩ : syracuseStep 2114609 = 1585957) B1585957
theorem B1410099 : Blo 1409524 1410099 := bstep (se 1 (by rfl) ⟨1057574, by rfl⟩ : syracuseStep 1410099 = 2115149) B2115149
theorem B2114627 : Blo 1409524 2114627 := bstep (se 1 (by rfl) ⟨1585970, by rfl⟩ : syracuseStep 2114627 = 3171941) B3171941
theorem B1410115 : Blo 1409524 1410115 := bstep (se 1 (by rfl) ⟨1057586, by rfl⟩ : syracuseStep 1410115 = 2115173) B2115173
theorem B10708037 : Blo 1409524 10708037 := bstep (se 4 (by rfl) ⟨1003878, by rfl⟩ : syracuseStep 10708037 = 2007757) B2007757
theorem B1410131 : Blo 1409524 1410131 := bstep (se 1 (by rfl) ⟨1057598, by rfl⟩ : syracuseStep 1410131 = 2115197) B2115197
theorem B2114657 : Blo 1409524 2114657 := bstep (se 2 (by rfl) ⟨792996, by rfl⟩ : syracuseStep 2114657 = 1585993) B1585993
theorem B1410147 : Blo 1409524 1410147 := bstep (se 1 (by rfl) ⟨1057610, by rfl⟩ : syracuseStep 1410147 = 2115221) B2115221
theorem B3572849 : Blo 1409524 3572849 := bstep (se 2 (by rfl) ⟨1339818, by rfl⟩ : syracuseStep 3572849 = 2679637) B2679637
theorem B2114675 : Blo 1409524 2114675 := bstep (se 1 (by rfl) ⟨1586006, by rfl⟩ : syracuseStep 2114675 = 3172013) B3172013
theorem B1410163 : Blo 1409524 1410163 := bstep (se 1 (by rfl) ⟨1057622, by rfl⟩ : syracuseStep 1410163 = 2115245) B2115245
theorem B1410179 : Blo 1409524 1410179 := bstep (se 1 (by rfl) ⟨1057634, by rfl⟩ : syracuseStep 1410179 = 2115269) B2115269
theorem B3171473 : Blo 1409524 3171473 := bstep (se 2 (by rfl) ⟨1189302, by rfl⟩ : syracuseStep 3171473 = 2378605) B2378605
theorem B2114705 : Blo 1409524 2114705 := bstep (se 2 (by rfl) ⟨793014, by rfl⟩ : syracuseStep 2114705 = 1586029) B1586029
theorem B1410195 : Blo 1409524 1410195 := bstep (se 1 (by rfl) ⟨1057646, by rfl⟩ : syracuseStep 1410195 = 2115293) B2115293
theorem B3171491 : Blo 1409524 3171491 := bstep (se 1 (by rfl) ⟨2378618, by rfl⟩ : syracuseStep 3171491 = 4757237) B4757237
theorem B2114723 : Blo 1409524 2114723 := bstep (se 1 (by rfl) ⟨1586042, by rfl⟩ : syracuseStep 2114723 = 3172085) B3172085
theorem B1410211 : Blo 1409524 1410211 := bstep (se 1 (by rfl) ⟨1057658, by rfl⟩ : syracuseStep 1410211 = 2115317) B2115317
theorem B1410227 : Blo 1409524 1410227 := bstep (se 1 (by rfl) ⟨1057670, by rfl⟩ : syracuseStep 1410227 = 2115341) B2115341
theorem B2114753 : Blo 1409524 2114753 := bstep (se 2 (by rfl) ⟨793032, by rfl⟩ : syracuseStep 2114753 = 1586065) B1586065
theorem B1410243 : Blo 1409524 1410243 := bstep (se 1 (by rfl) ⟨1057682, by rfl⟩ : syracuseStep 1410243 = 2115365) B2115365
theorem B2114771 : Blo 1409524 2114771 := bstep (se 1 (by rfl) ⟨1586078, by rfl⟩ : syracuseStep 2114771 = 3172157) B3172157
theorem B1410259 : Blo 1409524 1410259 := bstep (se 1 (by rfl) ⟨1057694, by rfl⟩ : syracuseStep 1410259 = 2115389) B2115389
theorem B1410275 : Blo 1409524 1410275 := bstep (se 1 (by rfl) ⟨1057706, by rfl⟩ : syracuseStep 1410275 = 2115413) B2115413
theorem B2114801 : Blo 1409524 2114801 := bstep (se 2 (by rfl) ⟨793050, by rfl⟩ : syracuseStep 2114801 = 1586101) B1586101
theorem B1410291 : Blo 1409524 1410291 := bstep (se 1 (by rfl) ⟨1057718, by rfl⟩ : syracuseStep 1410291 = 2115437) B2115437
theorem B2114819 : Blo 1409524 2114819 := bstep (se 1 (by rfl) ⟨1586114, by rfl⟩ : syracuseStep 2114819 = 3172229) B3172229
theorem B1410307 : Blo 1409524 1410307 := bstep (se 1 (by rfl) ⟨1057730, by rfl⟩ : syracuseStep 1410307 = 2115461) B2115461
theorem B1410323 : Blo 1409524 1410323 := bstep (se 1 (by rfl) ⟨1057742, by rfl⟩ : syracuseStep 1410323 = 2115485) B2115485
theorem B2114849 : Blo 1409524 2114849 := bstep (se 2 (by rfl) ⟨793068, by rfl⟩ : syracuseStep 2114849 = 1586137) B1586137
theorem B1410339 : Blo 1409524 1410339 := bstep (se 1 (by rfl) ⟨1057754, by rfl⟩ : syracuseStep 1410339 = 2115509) B2115509
theorem B2114867 : Blo 1409524 2114867 := bstep (se 1 (by rfl) ⟨1586150, by rfl⟩ : syracuseStep 2114867 = 3172301) B3172301
theorem B1410355 : Blo 1409524 1410355 := bstep (se 1 (by rfl) ⟨1057766, by rfl⟩ : syracuseStep 1410355 = 2115533) B2115533
theorem B1410371 : Blo 1409524 1410371 := bstep (se 1 (by rfl) ⟨1057778, by rfl⟩ : syracuseStep 1410371 = 2115557) B2115557
theorem B4760909 : Blo 1409524 4760909 := bstep (se 3 (by rfl) ⟨892670, by rfl⟩ : syracuseStep 4760909 = 1785341) B1785341
theorem B2114897 : Blo 1409524 2114897 := bstep (se 2 (by rfl) ⟨793086, by rfl⟩ : syracuseStep 2114897 = 1586173) B1586173
theorem B1410387 : Blo 1409524 1410387 := bstep (se 1 (by rfl) ⟨1057790, by rfl⟩ : syracuseStep 1410387 = 2115581) B2115581
theorem B2114915 : Blo 1409524 2114915 := bstep (se 1 (by rfl) ⟨1586186, by rfl⟩ : syracuseStep 2114915 = 3172373) B3172373
theorem B1410403 : Blo 1409524 1410403 := bstep (se 1 (by rfl) ⟨1057802, by rfl⟩ : syracuseStep 1410403 = 2115605) B2115605
theorem B4015469 : Blo 1409524 4015469 := bstep (se 3 (by rfl) ⟨752900, by rfl⟩ : syracuseStep 4015469 = 1505801) B1505801
theorem B3810673 : Blo 1409524 3810673 := bstep (se 2 (by rfl) ⟨1429002, by rfl⟩ : syracuseStep 3810673 = 2858005) B2858005
theorem B1410419 : Blo 1409524 1410419 := bstep (se 1 (by rfl) ⟨1057814, by rfl⟩ : syracuseStep 1410419 = 2115629) B2115629
theorem B2114945 : Blo 1409524 2114945 := bstep (se 2 (by rfl) ⟨793104, by rfl⟩ : syracuseStep 2114945 = 1586209) B1586209
theorem B1410435 : Blo 1409524 1410435 := bstep (se 1 (by rfl) ⟨1057826, by rfl⟩ : syracuseStep 1410435 = 2115653) B2115653
theorem B4760963 : Blo 1409524 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B2114963 : Blo 1409524 2114963 := bstep (se 1 (by rfl) ⟨1586222, by rfl⟩ : syracuseStep 2114963 = 3172445) B3172445
theorem B1410451 : Blo 1409524 1410451 := bstep (se 1 (by rfl) ⟨1057838, by rfl⟩ : syracuseStep 1410451 = 2115677) B2115677
theorem B1410467 : Blo 1409524 1410467 := bstep (se 1 (by rfl) ⟨1057850, by rfl⟩ : syracuseStep 1410467 = 2115701) B2115701
theorem B3171761 : Blo 1409524 3171761 := bstep (se 2 (by rfl) ⟨1189410, by rfl⟩ : syracuseStep 3171761 = 2378821) B2378821
theorem B3810737 : Blo 1409524 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B2114993 : Blo 1409524 2114993 := bstep (se 2 (by rfl) ⟨793122, by rfl⟩ : syracuseStep 2114993 = 1586245) B1586245
theorem B1410483 : Blo 1409524 1410483 := bstep (se 1 (by rfl) ⟨1057862, by rfl⟩ : syracuseStep 1410483 = 2115725) B2115725
theorem B3171779 : Blo 1409524 3171779 := bstep (se 1 (by rfl) ⟨2378834, by rfl⟩ : syracuseStep 3171779 = 4757669) B4757669
theorem B2115011 : Blo 1409524 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B1410499 : Blo 1409524 1410499 := bstep (se 1 (by rfl) ⟨1057874, by rfl⟩ : syracuseStep 1410499 = 2115749) B2115749
theorem B32581061 : Blo 1409524 32581061 := bstep (se 4 (by rfl) ⟨3054474, by rfl⟩ : syracuseStep 32581061 = 6108949) B6108949
theorem B1410515 : Blo 1409524 1410515 := bstep (se 1 (by rfl) ⟨1057886, by rfl⟩ : syracuseStep 1410515 = 2115773) B2115773
theorem B2115041 : Blo 1409524 2115041 := bstep (se 2 (by rfl) ⟨793140, by rfl⟩ : syracuseStep 2115041 = 1586281) B1586281
theorem B1410531 : Blo 1409524 1410531 := bstep (se 1 (by rfl) ⟨1057898, by rfl⟩ : syracuseStep 1410531 = 2115797) B2115797
theorem B2115059 : Blo 1409524 2115059 := bstep (se 1 (by rfl) ⟨1586294, by rfl⟩ : syracuseStep 2115059 = 3172589) B3172589
theorem B1410547 : Blo 1409524 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B1410563 : Blo 1409524 1410563 := bstep (se 1 (by rfl) ⟨1057922, by rfl⟩ : syracuseStep 1410563 = 2115845) B2115845
theorem B2115089 : Blo 1409524 2115089 := bstep (se 2 (by rfl) ⟨793158, by rfl⟩ : syracuseStep 2115089 = 1586317) B1586317
theorem B1410579 : Blo 1409524 1410579 := bstep (se 1 (by rfl) ⟨1057934, by rfl⟩ : syracuseStep 1410579 = 2115869) B2115869
theorem B2115107 : Blo 1409524 2115107 := bstep (se 1 (by rfl) ⟨1586330, by rfl⟩ : syracuseStep 2115107 = 3172661) B3172661
theorem B4015651 : Blo 1409524 4015651 := bstep (se 1 (by rfl) ⟨3011738, by rfl⟩ : syracuseStep 4015651 = 6023477) B6023477
theorem B1410595 : Blo 1409524 1410595 := bstep (se 1 (by rfl) ⟨1057946, by rfl⟩ : syracuseStep 1410595 = 2115893) B2115893
theorem B7145009 : Blo 1409524 7145009 := bstep (se 2 (by rfl) ⟨2679378, by rfl⟩ : syracuseStep 7145009 = 5358757) B5358757
theorem B1410611 : Blo 1409524 1410611 := bstep (se 1 (by rfl) ⟨1057958, by rfl⟩ : syracuseStep 1410611 = 2115917) B2115917
theorem B2115137 : Blo 1409524 2115137 := bstep (se 2 (by rfl) ⟨793176, by rfl⟩ : syracuseStep 2115137 = 1586353) B1586353
theorem B1410627 : Blo 1409524 1410627 := bstep (se 1 (by rfl) ⟨1057970, by rfl⟩ : syracuseStep 1410627 = 2115941) B2115941
theorem B2115155 : Blo 1409524 2115155 := bstep (se 1 (by rfl) ⟨1586366, by rfl⟩ : syracuseStep 2115155 = 3172733) B3172733
theorem B1410643 : Blo 1409524 1410643 := bstep (se 1 (by rfl) ⟨1057982, by rfl⟩ : syracuseStep 1410643 = 2115965) B2115965
theorem B3434083 : Blo 1409524 3434083 := bstep (se 1 (by rfl) ⟨2575562, by rfl⟩ : syracuseStep 3434083 = 5151125) B5151125
theorem B1410659 : Blo 1409524 1410659 := bstep (se 1 (by rfl) ⟨1057994, by rfl⟩ : syracuseStep 1410659 = 2115989) B2115989
theorem B2115185 : Blo 1409524 2115185 := bstep (se 2 (by rfl) ⟨793194, by rfl⟩ : syracuseStep 2115185 = 1586389) B1586389
theorem B10716785 : Blo 1409524 10716785 := bstep (se 2 (by rfl) ⟨4018794, by rfl⟩ : syracuseStep 10716785 = 8037589) B8037589
theorem B1410675 : Blo 1409524 1410675 := bstep (se 1 (by rfl) ⟨1058006, by rfl⟩ : syracuseStep 1410675 = 2116013) B2116013
theorem B2115203 : Blo 1409524 2115203 := bstep (se 1 (by rfl) ⟨1586402, by rfl⟩ : syracuseStep 2115203 = 3172805) B3172805
theorem B1410691 : Blo 1409524 1410691 := bstep (se 1 (by rfl) ⟨1058018, by rfl⟩ : syracuseStep 1410691 = 2116037) B2116037
theorem B7136909 : Blo 1409524 7136909 := bstep (se 3 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 7136909 = 2676341) B2676341
theorem B4761233 : Blo 1409524 4761233 := bstep (se 2 (by rfl) ⟨1785462, by rfl⟩ : syracuseStep 4761233 = 3570925) B3570925
theorem B1410707 : Blo 1409524 1410707 := bstep (se 1 (by rfl) ⟨1058030, by rfl⟩ : syracuseStep 1410707 = 2116061) B2116061
theorem B2115233 : Blo 1409524 2115233 := bstep (se 2 (by rfl) ⟨793212, by rfl⟩ : syracuseStep 2115233 = 1586425) B1586425
theorem B1410723 : Blo 1409524 1410723 := bstep (se 1 (by rfl) ⟨1058042, by rfl⟩ : syracuseStep 1410723 = 2116085) B2116085
theorem B3810989 : Blo 1409524 3810989 := bstep (se 3 (by rfl) ⟨714560, by rfl⟩ : syracuseStep 3810989 = 1429121) B1429121
theorem B2115251 : Blo 1409524 2115251 := bstep (se 1 (by rfl) ⟨1586438, by rfl⟩ : syracuseStep 2115251 = 3172877) B3172877
theorem B1410739 : Blo 1409524 1410739 := bstep (se 1 (by rfl) ⟨1058054, by rfl⟩ : syracuseStep 1410739 = 2116109) B2116109
theorem B4015811 : Blo 1409524 4015811 := bstep (se 1 (by rfl) ⟨3011858, by rfl⟩ : syracuseStep 4015811 = 6023717) B6023717
theorem B1410755 : Blo 1409524 1410755 := bstep (se 1 (by rfl) ⟨1058066, by rfl⟩ : syracuseStep 1410755 = 2116133) B2116133
theorem B3172049 : Blo 1409524 3172049 := bstep (se 2 (by rfl) ⟨1189518, by rfl⟩ : syracuseStep 3172049 = 2379037) B2379037
theorem B2115281 : Blo 1409524 2115281 := bstep (se 2 (by rfl) ⟨793230, by rfl⟩ : syracuseStep 2115281 = 1586461) B1586461
theorem B1410771 : Blo 1409524 1410771 := bstep (se 1 (by rfl) ⟨1058078, by rfl⟩ : syracuseStep 1410771 = 2116157) B2116157
theorem B3172067 : Blo 1409524 3172067 := bstep (se 1 (by rfl) ⟨2379050, by rfl⟩ : syracuseStep 3172067 = 4758101) B4758101
theorem B2115299 : Blo 1409524 2115299 := bstep (se 1 (by rfl) ⟨1586474, by rfl⟩ : syracuseStep 2115299 = 3172949) B3172949
theorem B1410787 : Blo 1409524 1410787 := bstep (se 1 (by rfl) ⟨1058090, by rfl⟩ : syracuseStep 1410787 = 2116181) B2116181
theorem B8038115 : Blo 1409524 8038115 := bstep (se 1 (by rfl) ⟨6028586, by rfl⟩ : syracuseStep 8038115 = 12057173) B12057173
theorem B10856177 : Blo 1409524 10856177 := bstep (se 2 (by rfl) ⟨4071066, by rfl⟩ : syracuseStep 10856177 = 8142133) B8142133
theorem B1410803 : Blo 1409524 1410803 := bstep (se 1 (by rfl) ⟨1058102, by rfl⟩ : syracuseStep 1410803 = 2116205) B2116205
theorem B2115329 : Blo 1409524 2115329 := bstep (se 2 (by rfl) ⟨793248, by rfl⟩ : syracuseStep 2115329 = 1586497) B1586497
theorem B1410819 : Blo 1409524 1410819 := bstep (se 1 (by rfl) ⟨1058114, by rfl⟩ : syracuseStep 1410819 = 2116229) B2116229
theorem B2115347 : Blo 1409524 2115347 := bstep (se 1 (by rfl) ⟨1586510, by rfl⟩ : syracuseStep 2115347 = 3173021) B3173021
theorem B1410835 : Blo 1409524 1410835 := bstep (se 1 (by rfl) ⟨1058126, by rfl⟩ : syracuseStep 1410835 = 2116253) B2116253
theorem B1410851 : Blo 1409524 1410851 := bstep (se 1 (by rfl) ⟨1058138, by rfl⟩ : syracuseStep 1410851 = 2116277) B2116277
theorem B2115377 : Blo 1409524 2115377 := bstep (se 2 (by rfl) ⟨793266, by rfl⟩ : syracuseStep 2115377 = 1586533) B1586533
theorem B1410867 : Blo 1409524 1410867 := bstep (se 1 (by rfl) ⟨1058150, by rfl⟩ : syracuseStep 1410867 = 2116301) B2116301
theorem B2115395 : Blo 1409524 2115395 := bstep (se 1 (by rfl) ⟨1586546, by rfl⟩ : syracuseStep 2115395 = 3173093) B3173093
theorem B1410883 : Blo 1409524 1410883 := bstep (se 1 (by rfl) ⟨1058162, by rfl⟩ : syracuseStep 1410883 = 2116325) B2116325
theorem B1410899 : Blo 1409524 1410899 := bstep (se 1 (by rfl) ⟨1058174, by rfl⟩ : syracuseStep 1410899 = 2116349) B2116349
theorem B2115425 : Blo 1409524 2115425 := bstep (se 2 (by rfl) ⟨793284, by rfl⟩ : syracuseStep 2115425 = 1586569) B1586569
theorem B3811171 : Blo 1409524 3811171 := bstep (se 1 (by rfl) ⟨2858378, by rfl⟩ : syracuseStep 3811171 = 5716757) B5716757
theorem B1410915 : Blo 1409524 1410915 := bstep (se 1 (by rfl) ⟨1058186, by rfl⟩ : syracuseStep 1410915 = 2116373) B2116373
theorem B2115443 : Blo 1409524 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B1410931 : Blo 1409524 1410931 := bstep (se 1 (by rfl) ⟨1058198, by rfl⟩ : syracuseStep 1410931 = 2116397) B2116397
theorem B1410947 : Blo 1409524 1410947 := bstep (se 1 (by rfl) ⟨1058210, by rfl⟩ : syracuseStep 1410947 = 2116421) B2116421
theorem B2115473 : Blo 1409524 2115473 := bstep (se 2 (by rfl) ⟨793302, by rfl⟩ : syracuseStep 2115473 = 1586605) B1586605
theorem B1410963 : Blo 1409524 1410963 := bstep (se 1 (by rfl) ⟨1058222, by rfl⟩ : syracuseStep 1410963 = 2116445) B2116445
theorem B2115491 : Blo 1409524 2115491 := bstep (se 1 (by rfl) ⟨1586618, by rfl⟩ : syracuseStep 2115491 = 3173237) B3173237
theorem B1410979 : Blo 1409524 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B1410995 : Blo 1409524 1410995 := bstep (se 1 (by rfl) ⟨1058246, by rfl⟩ : syracuseStep 1410995 = 2116493) B2116493
theorem B2115521 : Blo 1409524 2115521 := bstep (se 2 (by rfl) ⟨793320, by rfl⟩ : syracuseStep 2115521 = 1586641) B1586641
theorem B1411011 : Blo 1409524 1411011 := bstep (se 1 (by rfl) ⟨1058258, by rfl⟩ : syracuseStep 1411011 = 2116517) B2116517
theorem B12052421 : Blo 1409524 12052421 := bstep (se 4 (by rfl) ⟨1129914, by rfl⟩ : syracuseStep 12052421 = 2259829) B2259829
theorem B2115539 : Blo 1409524 2115539 := bstep (se 1 (by rfl) ⟨1586654, by rfl⟩ : syracuseStep 2115539 = 3173309) B3173309
theorem B1411027 : Blo 1409524 1411027 := bstep (se 1 (by rfl) ⟨1058270, by rfl⟩ : syracuseStep 1411027 = 2116541) B2116541
theorem B1411043 : Blo 1409524 1411043 := bstep (se 1 (by rfl) ⟨1058282, by rfl⟩ : syracuseStep 1411043 = 2116565) B2116565
theorem B3172337 : Blo 1409524 3172337 := bstep (se 2 (by rfl) ⟨1189626, by rfl⟩ : syracuseStep 3172337 = 2379253) B2379253
theorem B2115569 : Blo 1409524 2115569 := bstep (se 2 (by rfl) ⟨793338, by rfl⟩ : syracuseStep 2115569 = 1586677) B1586677
theorem B1411059 : Blo 1409524 1411059 := bstep (se 1 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 1411059 = 2116589) B2116589
theorem B3172355 : Blo 1409524 3172355 := bstep (se 1 (by rfl) ⟨2379266, by rfl⟩ : syracuseStep 3172355 = 4758533) B4758533
theorem B2115587 : Blo 1409524 2115587 := bstep (se 1 (by rfl) ⟨1586690, by rfl⟩ : syracuseStep 2115587 = 3173381) B3173381
theorem B1411075 : Blo 1409524 1411075 := bstep (se 1 (by rfl) ⟨1058306, by rfl⟩ : syracuseStep 1411075 = 2116613) B2116613
theorem B1411091 : Blo 1409524 1411091 := bstep (se 1 (by rfl) ⟨1058318, by rfl⟩ : syracuseStep 1411091 = 2116637) B2116637
theorem B2115617 : Blo 1409524 2115617 := bstep (se 2 (by rfl) ⟨793356, by rfl⟩ : syracuseStep 2115617 = 1586713) B1586713
theorem B1411107 : Blo 1409524 1411107 := bstep (se 1 (by rfl) ⟨1058330, by rfl⟩ : syracuseStep 1411107 = 2116661) B2116661
theorem B2115635 : Blo 1409524 2115635 := bstep (se 1 (by rfl) ⟨1586726, by rfl⟩ : syracuseStep 2115635 = 3173453) B3173453
theorem B1411123 : Blo 1409524 1411123 := bstep (se 1 (by rfl) ⟨1058342, by rfl⟩ : syracuseStep 1411123 = 2116685) B2116685
theorem B1411139 : Blo 1409524 1411139 := bstep (se 1 (by rfl) ⟨1058354, by rfl⟩ : syracuseStep 1411139 = 2116709) B2116709
theorem B2115665 : Blo 1409524 2115665 := bstep (se 2 (by rfl) ⟨793374, by rfl⟩ : syracuseStep 2115665 = 1586749) B1586749
theorem B1411155 : Blo 1409524 1411155 := bstep (se 1 (by rfl) ⟨1058366, by rfl⟩ : syracuseStep 1411155 = 2116733) B2116733
theorem B2115683 : Blo 1409524 2115683 := bstep (se 1 (by rfl) ⟨1586762, by rfl⟩ : syracuseStep 2115683 = 3173525) B3173525
theorem B1411171 : Blo 1409524 1411171 := bstep (se 1 (by rfl) ⟨1058378, by rfl⟩ : syracuseStep 1411171 = 2116757) B2116757
theorem B1411187 : Blo 1409524 1411187 := bstep (se 1 (by rfl) ⟨1058390, by rfl⟩ : syracuseStep 1411187 = 2116781) B2116781
theorem B2115713 : Blo 1409524 2115713 := bstep (se 2 (by rfl) ⟨793392, by rfl⟩ : syracuseStep 2115713 = 1586785) B1586785
theorem B1411203 : Blo 1409524 1411203 := bstep (se 1 (by rfl) ⟨1058402, by rfl⟩ : syracuseStep 1411203 = 2116805) B2116805
theorem B2115731 : Blo 1409524 2115731 := bstep (se 1 (by rfl) ⟨1586798, by rfl⟩ : syracuseStep 2115731 = 3173597) B3173597
theorem B1411219 : Blo 1409524 1411219 := bstep (se 1 (by rfl) ⟨1058414, by rfl⟩ : syracuseStep 1411219 = 2116829) B2116829
theorem B1411235 : Blo 1409524 1411235 := bstep (se 1 (by rfl) ⟨1058426, by rfl⟩ : syracuseStep 1411235 = 2116853) B2116853
theorem B4761773 : Blo 1409524 4761773 := bstep (se 3 (by rfl) ⟨892832, by rfl⟩ : syracuseStep 4761773 = 1785665) B1785665
theorem B2115761 : Blo 1409524 2115761 := bstep (se 2 (by rfl) ⟨793410, by rfl⟩ : syracuseStep 2115761 = 1586821) B1586821
theorem B1411251 : Blo 1409524 1411251 := bstep (se 1 (by rfl) ⟨1058438, by rfl⟩ : syracuseStep 1411251 = 2116877) B2116877
theorem B2115779 : Blo 1409524 2115779 := bstep (se 1 (by rfl) ⟨1586834, by rfl⟩ : syracuseStep 2115779 = 3173669) B3173669
theorem B1411267 : Blo 1409524 1411267 := bstep (se 1 (by rfl) ⟨1058450, by rfl⟩ : syracuseStep 1411267 = 2116901) B2116901
theorem B1411283 : Blo 1409524 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B2115809 : Blo 1409524 2115809 := bstep (se 2 (by rfl) ⟨793428, by rfl⟩ : syracuseStep 2115809 = 1586857) B1586857
theorem B4761827 : Blo 1409524 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B1411299 : Blo 1409524 1411299 := bstep (se 1 (by rfl) ⟨1058474, by rfl⟩ : syracuseStep 1411299 = 2116949) B2116949
theorem B2115827 : Blo 1409524 2115827 := bstep (se 1 (by rfl) ⟨1586870, by rfl⟩ : syracuseStep 2115827 = 3173741) B3173741
theorem B1411315 : Blo 1409524 1411315 := bstep (se 1 (by rfl) ⟨1058486, by rfl⟩ : syracuseStep 1411315 = 2116973) B2116973
theorem B1411331 : Blo 1409524 1411331 := bstep (se 1 (by rfl) ⟨1058498, by rfl⟩ : syracuseStep 1411331 = 2116997) B2116997
theorem B3172625 : Blo 1409524 3172625 := bstep (se 2 (by rfl) ⟨1189734, by rfl⟩ : syracuseStep 3172625 = 2379469) B2379469
theorem B2115857 : Blo 1409524 2115857 := bstep (se 2 (by rfl) ⟨793446, by rfl⟩ : syracuseStep 2115857 = 1586893) B1586893
theorem B1411347 : Blo 1409524 1411347 := bstep (se 1 (by rfl) ⟨1058510, by rfl⟩ : syracuseStep 1411347 = 2117021) B2117021
theorem B3172643 : Blo 1409524 3172643 := bstep (se 1 (by rfl) ⟨2379482, by rfl⟩ : syracuseStep 3172643 = 4758965) B4758965
theorem B2115875 : Blo 1409524 2115875 := bstep (se 1 (by rfl) ⟨1586906, by rfl⟩ : syracuseStep 2115875 = 3173813) B3173813
theorem B1411363 : Blo 1409524 1411363 := bstep (se 1 (by rfl) ⟨1058522, by rfl⟩ : syracuseStep 1411363 = 2117045) B2117045
theorem B1411379 : Blo 1409524 1411379 := bstep (se 1 (by rfl) ⟨1058534, by rfl⟩ : syracuseStep 1411379 = 2117069) B2117069
theorem B2115905 : Blo 1409524 2115905 := bstep (se 2 (by rfl) ⟨793464, by rfl⟩ : syracuseStep 2115905 = 1586929) B1586929
theorem B1411395 : Blo 1409524 1411395 := bstep (se 1 (by rfl) ⟨1058546, by rfl⟩ : syracuseStep 1411395 = 2117093) B2117093
theorem B2115923 : Blo 1409524 2115923 := bstep (se 1 (by rfl) ⟨1586942, by rfl⟩ : syracuseStep 2115923 = 3173885) B3173885
theorem B1411411 : Blo 1409524 1411411 := bstep (se 1 (by rfl) ⟨1058558, by rfl⟩ : syracuseStep 1411411 = 2117117) B2117117
theorem B2009443 : Blo 1409524 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B1411427 : Blo 1409524 1411427 := bstep (se 1 (by rfl) ⟨1058570, by rfl⟩ : syracuseStep 1411427 = 2117141) B2117141
theorem B2115953 : Blo 1409524 2115953 := bstep (se 2 (by rfl) ⟨793482, by rfl⟩ : syracuseStep 2115953 = 1586965) B1586965
theorem B1411443 : Blo 1409524 1411443 := bstep (se 1 (by rfl) ⟨1058582, by rfl⟩ : syracuseStep 1411443 = 2117165) B2117165
theorem B2115971 : Blo 1409524 2115971 := bstep (se 1 (by rfl) ⟨1586978, by rfl⟩ : syracuseStep 2115971 = 3173957) B3173957
theorem B1411459 : Blo 1409524 1411459 := bstep (se 1 (by rfl) ⟨1058594, by rfl⟩ : syracuseStep 1411459 = 2117189) B2117189
theorem B1411475 : Blo 1409524 1411475 := bstep (se 1 (by rfl) ⟨1058606, by rfl⟩ : syracuseStep 1411475 = 2117213) B2117213
theorem B2116001 : Blo 1409524 2116001 := bstep (se 2 (by rfl) ⟨793500, by rfl⟩ : syracuseStep 2116001 = 1587001) B1587001
theorem B1411491 : Blo 1409524 1411491 := bstep (se 1 (by rfl) ⟨1058618, by rfl⟩ : syracuseStep 1411491 = 2117237) B2117237
theorem B2116019 : Blo 1409524 2116019 := bstep (se 1 (by rfl) ⟨1587014, by rfl⟩ : syracuseStep 2116019 = 3174029) B3174029
theorem B1411507 : Blo 1409524 1411507 := bstep (se 1 (by rfl) ⟨1058630, by rfl⟩ : syracuseStep 1411507 = 2117261) B2117261
theorem B1411523 : Blo 1409524 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B2116049 : Blo 1409524 2116049 := bstep (se 2 (by rfl) ⟨793518, by rfl⟩ : syracuseStep 2116049 = 1587037) B1587037
theorem B2116067 : Blo 1409524 2116067 := bstep (se 1 (by rfl) ⟨1587050, by rfl⟩ : syracuseStep 2116067 = 3174101) B3174101
theorem B4762097 : Blo 1409524 4762097 := bstep (se 2 (by rfl) ⟨1785786, by rfl⟩ : syracuseStep 4762097 = 3571573) B3571573
theorem B2116097 : Blo 1409524 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B3811853 : Blo 1409524 3811853 := bstep (se 3 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 3811853 = 1429445) B1429445
theorem B2116115 : Blo 1409524 2116115 := bstep (se 1 (by rfl) ⟨1587086, by rfl⟩ : syracuseStep 2116115 = 3174173) B3174173
theorem B3172913 : Blo 1409524 3172913 := bstep (se 2 (by rfl) ⟨1189842, by rfl⟩ : syracuseStep 3172913 = 2379685) B2379685
theorem B2116145 : Blo 1409524 2116145 := bstep (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) B1587109
theorem B3172931 : Blo 1409524 3172931 := bstep (se 1 (by rfl) ⟨2379698, by rfl⟩ : syracuseStep 3172931 = 4759397) B4759397
theorem B2116163 : Blo 1409524 2116163 := bstep (se 1 (by rfl) ⟨1587122, by rfl⟩ : syracuseStep 2116163 = 3174245) B3174245
theorem B2116193 : Blo 1409524 2116193 := bstep (se 2 (by rfl) ⟨793572, by rfl⟩ : syracuseStep 2116193 = 1587145) B1587145
theorem B2116211 : Blo 1409524 2116211 := bstep (se 1 (by rfl) ⟨1587158, by rfl⟩ : syracuseStep 2116211 = 3174317) B3174317
theorem B2116241 : Blo 1409524 2116241 := bstep (se 2 (by rfl) ⟨793590, by rfl⟩ : syracuseStep 2116241 = 1587181) B1587181
theorem B2116259 : Blo 1409524 2116259 := bstep (se 1 (by rfl) ⟨1587194, by rfl⟩ : syracuseStep 2116259 = 3174389) B3174389
theorem B2116289 : Blo 1409524 2116289 := bstep (se 2 (by rfl) ⟨793608, by rfl⟩ : syracuseStep 2116289 = 1587217) B1587217
theorem B2116307 : Blo 1409524 2116307 := bstep (se 1 (by rfl) ⟨1587230, by rfl⟩ : syracuseStep 2116307 = 3174461) B3174461
theorem B4016881 : Blo 1409524 4016881 := bstep (se 2 (by rfl) ⟨1506330, by rfl⟩ : syracuseStep 4016881 = 3012661) B3012661
theorem B2116337 : Blo 1409524 2116337 := bstep (se 2 (by rfl) ⟨793626, by rfl⟩ : syracuseStep 2116337 = 1587253) B1587253
theorem B2116355 : Blo 1409524 2116355 := bstep (se 1 (by rfl) ⟨1587266, by rfl⟩ : syracuseStep 2116355 = 3174533) B3174533
theorem B2116385 : Blo 1409524 2116385 := bstep (se 2 (by rfl) ⟨793644, by rfl⟩ : syracuseStep 2116385 = 1587289) B1587289
theorem B5352227 : Blo 1409524 5352227 := bstep (se 1 (by rfl) ⟨4014170, by rfl⟩ : syracuseStep 5352227 = 8028341) B8028341
theorem B2116403 : Blo 1409524 2116403 := bstep (se 1 (by rfl) ⟨1587302, by rfl⟩ : syracuseStep 2116403 = 3174605) B3174605
theorem B3173201 : Blo 1409524 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B2116433 : Blo 1409524 2116433 := bstep (se 2 (by rfl) ⟨793662, by rfl⟩ : syracuseStep 2116433 = 1587325) B1587325
theorem B3173219 : Blo 1409524 3173219 := bstep (se 1 (by rfl) ⟨2379914, by rfl⟩ : syracuseStep 3173219 = 4759829) B4759829
theorem B2116451 : Blo 1409524 2116451 := bstep (se 1 (by rfl) ⟨1587338, by rfl⟩ : syracuseStep 2116451 = 3174677) B3174677
theorem B17165155 : Blo 1409524 17165155 := bstep (se 1 (by rfl) ⟨12873866, by rfl⟩ : syracuseStep 17165155 = 25747733) B25747733
theorem B2116481 : Blo 1409524 2116481 := bstep (se 2 (by rfl) ⟨793680, by rfl⟩ : syracuseStep 2116481 = 1587361) B1587361
theorem B6024077 : Blo 1409524 6024077 := bstep (se 3 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 6024077 = 2259029) B2259029
theorem B2116499 : Blo 1409524 2116499 := bstep (se 1 (by rfl) ⟨1587374, by rfl⟩ : syracuseStep 2116499 = 3174749) B3174749
theorem B2378659 : Blo 1409524 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B2116529 : Blo 1409524 2116529 := bstep (se 2 (by rfl) ⟨793698, by rfl⟩ : syracuseStep 2116529 = 1587397) B1587397
theorem B2116547 : Blo 1409524 2116547 := bstep (se 1 (by rfl) ⟨1587410, by rfl⟩ : syracuseStep 2116547 = 3174821) B3174821
theorem B2116577 : Blo 1409524 2116577 := bstep (se 2 (by rfl) ⟨793716, by rfl⟩ : syracuseStep 2116577 = 1587433) B1587433
theorem B2116595 : Blo 1409524 2116595 := bstep (se 1 (by rfl) ⟨1587446, by rfl⟩ : syracuseStep 2116595 = 3174893) B3174893
theorem B4762637 : Blo 1409524 4762637 := bstep (se 3 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 4762637 = 1785989) B1785989
theorem B2116625 : Blo 1409524 2116625 := bstep (se 2 (by rfl) ⟨793734, by rfl⟩ : syracuseStep 2116625 = 1587469) B1587469
theorem B2116643 : Blo 1409524 2116643 := bstep (se 1 (by rfl) ⟨1587482, by rfl⟩ : syracuseStep 2116643 = 3174965) B3174965
theorem B2378801 : Blo 1409524 2378801 := bstep (se 2 (by rfl) ⟨892050, by rfl⟩ : syracuseStep 2378801 = 1784101) B1784101
theorem B2116673 : Blo 1409524 2116673 := bstep (se 2 (by rfl) ⟨793752, by rfl⟩ : syracuseStep 2116673 = 1587505) B1587505
theorem B4762691 : Blo 1409524 4762691 := bstep (se 1 (by rfl) ⟨3572018, by rfl⟩ : syracuseStep 4762691 = 7144037) B7144037
theorem B2116691 : Blo 1409524 2116691 := bstep (se 1 (by rfl) ⟨1587518, by rfl⟩ : syracuseStep 2116691 = 3175037) B3175037
theorem B15248483 : Blo 1409524 15248483 := bstep (se 1 (by rfl) ⟨11436362, by rfl⟩ : syracuseStep 15248483 = 22872725) B22872725
theorem B3173489 : Blo 1409524 3173489 := bstep (se 2 (by rfl) ⟨1190058, by rfl⟩ : syracuseStep 3173489 = 2380117) B2380117
theorem B2116721 : Blo 1409524 2116721 := bstep (se 2 (by rfl) ⟨793770, by rfl⟩ : syracuseStep 2116721 = 1587541) B1587541
theorem B3173507 : Blo 1409524 3173507 := bstep (se 1 (by rfl) ⟨2380130, by rfl⟩ : syracuseStep 3173507 = 4760261) B4760261
theorem B2116739 : Blo 1409524 2116739 := bstep (se 1 (by rfl) ⟨1587554, by rfl⟩ : syracuseStep 2116739 = 3175109) B3175109
theorem B2116769 : Blo 1409524 2116769 := bstep (se 2 (by rfl) ⟨793788, by rfl⟩ : syracuseStep 2116769 = 1587577) B1587577
theorem B2378929 : Blo 1409524 2378929 := bstep (se 2 (by rfl) ⟨892098, by rfl⟩ : syracuseStep 2378929 = 1784197) B1784197
theorem B2174131 : Blo 1409524 2174131 := bstep (se 1 (by rfl) ⟨1630598, by rfl⟩ : syracuseStep 2174131 = 3261197) B3261197
theorem B2116787 : Blo 1409524 2116787 := bstep (se 1 (by rfl) ⟨1587590, by rfl⟩ : syracuseStep 2116787 = 3175181) B3175181
theorem B2116817 : Blo 1409524 2116817 := bstep (se 2 (by rfl) ⟨793806, by rfl⟩ : syracuseStep 2116817 = 1587613) B1587613
theorem B2378963 : Blo 1409524 2378963 := bstep (se 1 (by rfl) ⟨1784222, by rfl⟩ : syracuseStep 2378963 = 3568445) B3568445
theorem B2116835 : Blo 1409524 2116835 := bstep (se 1 (by rfl) ⟨1587626, by rfl⟩ : syracuseStep 2116835 = 3175253) B3175253
theorem B2116865 : Blo 1409524 2116865 := bstep (se 2 (by rfl) ⟨793824, by rfl⟩ : syracuseStep 2116865 = 1587649) B1587649
theorem B2116883 : Blo 1409524 2116883 := bstep (se 1 (by rfl) ⟨1587662, by rfl⟩ : syracuseStep 2116883 = 3175325) B3175325
theorem B2116913 : Blo 1409524 2116913 := bstep (se 2 (by rfl) ⟨793842, by rfl⟩ : syracuseStep 2116913 = 1587685) B1587685
theorem B4287811 : Blo 1409524 4287811 := bstep (se 1 (by rfl) ⟨3215858, by rfl⟩ : syracuseStep 4287811 = 6431717) B6431717
theorem B2116931 : Blo 1409524 2116931 := bstep (se 1 (by rfl) ⟨1587698, by rfl⟩ : syracuseStep 2116931 = 3175397) B3175397
theorem B4762961 : Blo 1409524 4762961 := bstep (se 2 (by rfl) ⟨1786110, by rfl⟩ : syracuseStep 4762961 = 3572221) B3572221
theorem B2379091 : Blo 1409524 2379091 := bstep (se 1 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 2379091 = 3568637) B3568637
theorem B2116961 : Blo 1409524 2116961 := bstep (se 2 (by rfl) ⟨793860, by rfl⟩ : syracuseStep 2116961 = 1587721) B1587721
theorem B1527155 : Blo 1409524 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B2116979 : Blo 1409524 2116979 := bstep (se 1 (by rfl) ⟨1587734, by rfl⟩ : syracuseStep 2116979 = 3175469) B3175469
theorem B3173777 : Blo 1409524 3173777 := bstep (se 2 (by rfl) ⟨1190166, by rfl⟩ : syracuseStep 3173777 = 2380333) B2380333
theorem B2117009 : Blo 1409524 2117009 := bstep (se 2 (by rfl) ⟨793878, by rfl⟩ : syracuseStep 2117009 = 1587757) B1587757
theorem B3812771 : Blo 1409524 3812771 := bstep (se 1 (by rfl) ⟨2859578, by rfl⟩ : syracuseStep 3812771 = 5719157) B5719157
theorem B3173795 : Blo 1409524 3173795 := bstep (se 1 (by rfl) ⟨2380346, by rfl⟩ : syracuseStep 3173795 = 4760693) B4760693
theorem B2117027 : Blo 1409524 2117027 := bstep (se 1 (by rfl) ⟨1587770, by rfl⟩ : syracuseStep 2117027 = 3175541) B3175541
theorem B2117057 : Blo 1409524 2117057 := bstep (se 2 (by rfl) ⟨793896, by rfl⟩ : syracuseStep 2117057 = 1587793) B1587793
theorem B3812813 : Blo 1409524 3812813 := bstep (se 3 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 3812813 = 1429805) B1429805
theorem B2117075 : Blo 1409524 2117075 := bstep (se 1 (by rfl) ⟨1587806, by rfl⟩ : syracuseStep 2117075 = 3175613) B3175613
theorem B2379233 : Blo 1409524 2379233 := bstep (se 2 (by rfl) ⟨892212, by rfl⟩ : syracuseStep 2379233 = 1784425) B1784425
theorem B2117105 : Blo 1409524 2117105 := bstep (se 2 (by rfl) ⟨793914, by rfl⟩ : syracuseStep 2117105 = 1587829) B1587829
theorem B2117123 : Blo 1409524 2117123 := bstep (se 1 (by rfl) ⟨1587842, by rfl⟩ : syracuseStep 2117123 = 3175685) B3175685
theorem B8031757 : Blo 1409524 8031757 := bstep (se 3 (by rfl) ⟨1505954, by rfl⟩ : syracuseStep 8031757 = 3011909) B3011909
theorem B2117153 : Blo 1409524 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B3386929 : Blo 1409524 3386929 := bstep (se 2 (by rfl) ⟨1270098, by rfl⟩ : syracuseStep 3386929 = 2540197) B2540197
theorem B2117171 : Blo 1409524 2117171 := bstep (se 1 (by rfl) ⟨1587878, by rfl⟩ : syracuseStep 2117171 = 3175757) B3175757
theorem B2117201 : Blo 1409524 2117201 := bstep (se 2 (by rfl) ⟨793950, by rfl⟩ : syracuseStep 2117201 = 1587901) B1587901
theorem B2379361 : Blo 1409524 2379361 := bstep (se 2 (by rfl) ⟨892260, by rfl⟩ : syracuseStep 2379361 = 1784521) B1784521
theorem B7237219 : Blo 1409524 7237219 := bstep (se 1 (by rfl) ⟨5427914, by rfl⟩ : syracuseStep 7237219 = 10855829) B10855829
theorem B2117219 : Blo 1409524 2117219 := bstep (se 1 (by rfl) ⟨1587914, by rfl⟩ : syracuseStep 2117219 = 3175829) B3175829
theorem B2117249 : Blo 1409524 2117249 := bstep (se 2 (by rfl) ⟨793968, by rfl⟩ : syracuseStep 2117249 = 1587937) B1587937
theorem B2379395 : Blo 1409524 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B2117267 : Blo 1409524 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B3174065 : Blo 1409524 3174065 := bstep (se 2 (by rfl) ⟨1190274, by rfl⟩ : syracuseStep 3174065 = 2380549) B2380549
theorem B3174083 : Blo 1409524 3174083 := bstep (se 1 (by rfl) ⟨2380562, by rfl⟩ : syracuseStep 3174083 = 4761125) B4761125
theorem B8367857 : Blo 1409524 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B2379523 : Blo 1409524 2379523 := bstep (se 1 (by rfl) ⟨1784642, by rfl⟩ : syracuseStep 2379523 = 3569285) B3569285
theorem B5353229 : Blo 1409524 5353229 := bstep (se 3 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 5353229 = 2007461) B2007461
theorem B4763501 : Blo 1409524 4763501 := bstep (se 3 (by rfl) ⟨893156, by rfl⟩ : syracuseStep 4763501 = 1786313) B1786313
theorem B2379665 : Blo 1409524 2379665 := bstep (se 2 (by rfl) ⟨892374, by rfl⟩ : syracuseStep 2379665 = 1784749) B1784749
theorem B4763555 : Blo 1409524 4763555 := bstep (se 1 (by rfl) ⟨3572666, by rfl⟩ : syracuseStep 4763555 = 7145333) B7145333
theorem B3174353 : Blo 1409524 3174353 := bstep (se 2 (by rfl) ⟨1190382, by rfl⟩ : syracuseStep 3174353 = 2380765) B2380765
theorem B3174371 : Blo 1409524 3174371 := bstep (se 1 (by rfl) ⟨2380778, by rfl⟩ : syracuseStep 3174371 = 4761557) B4761557
theorem B4018157 : Blo 1409524 4018157 := bstep (se 3 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 4018157 = 1506809) B1506809
theorem B2379793 : Blo 1409524 2379793 := bstep (se 2 (by rfl) ⟨892422, by rfl⟩ : syracuseStep 2379793 = 1784845) B1784845
theorem B2379827 : Blo 1409524 2379827 := bstep (se 1 (by rfl) ⟨1784870, by rfl⟩ : syracuseStep 2379827 = 3569741) B3569741
theorem B4018339 : Blo 1409524 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B4763825 : Blo 1409524 4763825 := bstep (se 2 (by rfl) ⟨1786434, by rfl⟩ : syracuseStep 4763825 = 3572869) B3572869
theorem B2379955 : Blo 1409524 2379955 := bstep (se 1 (by rfl) ⟨1784966, by rfl⟩ : syracuseStep 2379955 = 3569933) B3569933
theorem B4018385 : Blo 1409524 4018385 := bstep (se 2 (by rfl) ⟨1506894, by rfl⟩ : syracuseStep 4018385 = 3013789) B3013789
theorem B12865763 : Blo 1409524 12865763 := bstep (se 1 (by rfl) ⟨9649322, by rfl⟩ : syracuseStep 12865763 = 19298645) B19298645
theorem B3174641 : Blo 1409524 3174641 := bstep (se 2 (by rfl) ⟨1190490, by rfl⟩ : syracuseStep 3174641 = 2380981) B2380981
theorem B3174659 : Blo 1409524 3174659 := bstep (se 1 (by rfl) ⟨2380994, by rfl⟩ : syracuseStep 3174659 = 4761989) B4761989
theorem B2380097 : Blo 1409524 2380097 := bstep (se 2 (by rfl) ⟨892536, by rfl⟩ : syracuseStep 2380097 = 1785073) B1785073
theorem B7623011 : Blo 1409524 7623011 := bstep (se 1 (by rfl) ⟨5717258, by rfl⟩ : syracuseStep 7623011 = 11434517) B11434517
theorem B2380225 : Blo 1409524 2380225 := bstep (se 2 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 2380225 = 1785169) B1785169
theorem B2380259 : Blo 1409524 2380259 := bstep (se 1 (by rfl) ⟨1785194, by rfl⟩ : syracuseStep 2380259 = 3570389) B3570389
theorem B5722595 : Blo 1409524 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B7139825 : Blo 1409524 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B3011089 : Blo 1409524 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B3174929 : Blo 1409524 3174929 := bstep (se 2 (by rfl) ⟨1190598, by rfl⟩ : syracuseStep 3174929 = 2381197) B2381197
theorem B3011107 : Blo 1409524 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B3174947 : Blo 1409524 3174947 := bstep (se 1 (by rfl) ⟨2381210, by rfl⟩ : syracuseStep 3174947 = 4762421) B4762421
theorem B16077365 : Blo 1409524 16077365 := bstep (se 5 (by rfl) ⟨753626, by rfl⟩ : syracuseStep 16077365 = 1507253) B1507253
theorem B4289123 : Blo 1409524 4289123 := bstep (se 1 (by rfl) ⟨3216842, by rfl⟩ : syracuseStep 4289123 = 6433685) B6433685
theorem B2380387 : Blo 1409524 2380387 := bstep (se 1 (by rfl) ⟨1785290, by rfl⟩ : syracuseStep 2380387 = 3570581) B3570581
theorem B1585795 : Blo 1409524 1585795 := bstep (se 1 (by rfl) ⟨1189346, by rfl⟩ : syracuseStep 1585795 = 2378693) B2378693
theorem B1905347 : Blo 1409524 1905347 := bstep (se 1 (by rfl) ⟨1429010, by rfl⟩ : syracuseStep 1905347 = 2858021) B2858021
theorem B24113861 : Blo 1409524 24113861 := bstep (se 4 (by rfl) ⟨2260674, by rfl⟩ : syracuseStep 24113861 = 4521349) B4521349
theorem B1430227 : Blo 1409524 1430227 := bstep (se 1 (by rfl) ⟨1072670, by rfl⟩ : syracuseStep 1430227 = 2145341) B2145341
theorem B12047089 : Blo 1409524 12047089 := bstep (se 2 (by rfl) ⟨4517658, by rfl⟩ : syracuseStep 12047089 = 9035317) B9035317
theorem B2380529 : Blo 1409524 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B1585939 : Blo 1409524 1585939 := bstep (se 1 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 1585939 = 2378909) B2378909
theorem B3175217 : Blo 1409524 3175217 := bstep (se 2 (by rfl) ⟨1190706, by rfl⟩ : syracuseStep 3175217 = 2381413) B2381413
theorem B3175235 : Blo 1409524 3175235 := bstep (se 1 (by rfl) ⟨2381426, by rfl⟩ : syracuseStep 3175235 = 4762853) B4762853
theorem B4518737 : Blo 1409524 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B2380657 : Blo 1409524 2380657 := bstep (se 2 (by rfl) ⟨892746, by rfl⟩ : syracuseStep 2380657 = 1785493) B1785493
theorem B4518787 : Blo 1409524 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B2380691 : Blo 1409524 2380691 := bstep (se 1 (by rfl) ⟨1785518, by rfl⟩ : syracuseStep 2380691 = 3571037) B3571037
theorem B1586083 : Blo 1409524 1586083 := bstep (se 1 (by rfl) ⟨1189562, by rfl⟩ : syracuseStep 1586083 = 2379125) B2379125
theorem B2413523 : Blo 1409524 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B3568657 : Blo 1409524 3568657 := bstep (se 2 (by rfl) ⟨1338246, by rfl⟩ : syracuseStep 3568657 = 2676493) B2676493
theorem B2380819 : Blo 1409524 2380819 := bstep (se 1 (by rfl) ⟨1785614, by rfl⟩ : syracuseStep 2380819 = 3571229) B3571229
theorem B6435875 : Blo 1409524 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B1586227 : Blo 1409524 1586227 := bstep (se 1 (by rfl) ⟨1189670, by rfl⟩ : syracuseStep 1586227 = 2379341) B2379341
theorem B3175505 : Blo 1409524 3175505 := bstep (se 2 (by rfl) ⟨1190814, by rfl⟩ : syracuseStep 3175505 = 2381629) B2381629
theorem B2413667 : Blo 1409524 2413667 := bstep (se 1 (by rfl) ⟨1810250, by rfl⟩ : syracuseStep 2413667 = 3620501) B3620501
theorem B3175523 : Blo 1409524 3175523 := bstep (se 1 (by rfl) ⟨2381642, by rfl⟩ : syracuseStep 3175523 = 4763285) B4763285
theorem B2143345 : Blo 1409524 2143345 := bstep (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) B1607509
theorem B3052657 : Blo 1409524 3052657 := bstep (se 2 (by rfl) ⟨1144746, by rfl⟩ : syracuseStep 3052657 = 2289493) B2289493
theorem B2380961 : Blo 1409524 2380961 := bstep (se 2 (by rfl) ⟨892860, by rfl⟩ : syracuseStep 2380961 = 1785721) B1785721
theorem B4289699 : Blo 1409524 4289699 := bstep (se 1 (by rfl) ⟨3217274, by rfl⟩ : syracuseStep 4289699 = 6434549) B6434549
theorem B1586371 : Blo 1409524 1586371 := bstep (se 1 (by rfl) ⟨1189778, by rfl⟩ : syracuseStep 1586371 = 2379557) B2379557
theorem B2258209 : Blo 1409524 2258209 := bstep (se 2 (by rfl) ⟨846828, by rfl⟩ : syracuseStep 2258209 = 1693657) B1693657
theorem B2381089 : Blo 1409524 2381089 := bstep (se 2 (by rfl) ⟨892908, by rfl⟩ : syracuseStep 2381089 = 1785817) B1785817
theorem B3568931 : Blo 1409524 3568931 := bstep (se 1 (by rfl) ⟨2676698, by rfl⟩ : syracuseStep 3568931 = 5353397) B5353397
theorem B2381123 : Blo 1409524 2381123 := bstep (se 1 (by rfl) ⟨1785842, by rfl⟩ : syracuseStep 2381123 = 3571685) B3571685
theorem B2413891 : Blo 1409524 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B1586515 : Blo 1409524 1586515 := bstep (se 1 (by rfl) ⟨1189886, by rfl⟩ : syracuseStep 1586515 = 2379773) B2379773
theorem B3175793 : Blo 1409524 3175793 := bstep (se 2 (by rfl) ⟨1190922, by rfl⟩ : syracuseStep 3175793 = 2381845) B2381845
theorem B3175811 : Blo 1409524 3175811 := bstep (se 1 (by rfl) ⟨2381858, by rfl⟩ : syracuseStep 3175811 = 4763717) B4763717
theorem B2381251 : Blo 1409524 2381251 := bstep (se 1 (by rfl) ⟨1785938, by rfl⟩ : syracuseStep 2381251 = 3571877) B3571877
theorem B8033741 : Blo 1409524 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B3569123 : Blo 1409524 3569123 := bstep (se 1 (by rfl) ⟨2676842, by rfl⟩ : syracuseStep 3569123 = 5353685) B5353685
theorem B1586659 : Blo 1409524 1586659 := bstep (se 1 (by rfl) ⟨1189994, by rfl⟩ : syracuseStep 1586659 = 2379989) B2379989
theorem B5797453 : Blo 1409524 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B2381393 : Blo 1409524 2381393 := bstep (se 2 (by rfl) ⟨893022, by rfl⟩ : syracuseStep 2381393 = 1786045) B1786045
theorem B3217009 : Blo 1409524 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B1586803 : Blo 1409524 1586803 := bstep (se 1 (by rfl) ⟨1190102, by rfl⟩ : syracuseStep 1586803 = 2380205) B2380205
theorem B4290193 : Blo 1409524 4290193 := bstep (se 2 (by rfl) ⟨1608822, by rfl⟩ : syracuseStep 4290193 = 3217645) B3217645
theorem B4519633 : Blo 1409524 4519633 := bstep (se 2 (by rfl) ⟨1694862, by rfl⟩ : syracuseStep 4519633 = 3389725) B3389725
theorem B2381521 : Blo 1409524 2381521 := bstep (se 2 (by rfl) ⟨893070, by rfl⟩ : syracuseStep 2381521 = 1786141) B1786141
theorem B2381555 : Blo 1409524 2381555 := bstep (se 1 (by rfl) ⟨1786166, by rfl⟩ : syracuseStep 2381555 = 3572333) B3572333
theorem B1586947 : Blo 1409524 1586947 := bstep (se 1 (by rfl) ⟨1190210, by rfl⟩ : syracuseStep 1586947 = 2380421) B2380421
theorem B3815171 : Blo 1409524 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B16955189 : Blo 1409524 16955189 := bstep (se 5 (by rfl) ⟨794774, by rfl⟩ : syracuseStep 16955189 = 1589549) B1589549
theorem B5355341 : Blo 1409524 5355341 := bstep (se 3 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 5355341 = 2008253) B2008253
theorem B9041777 : Blo 1409524 9041777 := bstep (se 2 (by rfl) ⟨3390666, by rfl⟩ : syracuseStep 9041777 = 6781333) B6781333
theorem B2381683 : Blo 1409524 2381683 := bstep (se 1 (by rfl) ⟨1786262, by rfl⟩ : syracuseStep 2381683 = 3572525) B3572525
theorem B1587091 : Blo 1409524 1587091 := bstep (se 1 (by rfl) ⟨1190318, by rfl⟩ : syracuseStep 1587091 = 2380637) B2380637
theorem B7141283 : Blo 1409524 7141283 := bstep (se 1 (by rfl) ⟨5355962, by rfl⟩ : syracuseStep 7141283 = 10711925) B10711925
theorem B4577219 : Blo 1409524 4577219 := bstep (se 1 (by rfl) ⟨3432914, by rfl⟩ : syracuseStep 4577219 = 6865829) B6865829
theorem B4405187 : Blo 1409524 4405187 := bstep (se 1 (by rfl) ⟨3303890, by rfl⟩ : syracuseStep 4405187 = 6607781) B6607781
theorem B4757453 : Blo 1409524 4757453 := bstep (se 3 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 4757453 = 1784045) B1784045
theorem B9033677 : Blo 1409524 9033677 := bstep (se 3 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 9033677 = 3387629) B3387629
theorem B2676721 : Blo 1409524 2676721 := bstep (se 2 (by rfl) ⟨1003770, by rfl⟩ : syracuseStep 2676721 = 2007541) B2007541
theorem B2381825 : Blo 1409524 2381825 := bstep (se 2 (by rfl) ⟨893184, by rfl⟩ : syracuseStep 2381825 = 1786369) B1786369
theorem B4757507 : Blo 1409524 4757507 := bstep (se 1 (by rfl) ⟨3568130, by rfl⟩ : syracuseStep 4757507 = 7136261) B7136261
theorem B1587235 : Blo 1409524 1587235 := bstep (se 1 (by rfl) ⟨1190426, by rfl⟩ : syracuseStep 1587235 = 2380853) B2380853
theorem B1783939 : Blo 1409524 1783939 := bstep (se 1 (by rfl) ⟨1337954, by rfl⟩ : syracuseStep 1783939 = 2675909) B2675909
theorem B2676881 : Blo 1409524 2676881 := bstep (se 2 (by rfl) ⟨1003830, by rfl⟩ : syracuseStep 2676881 = 2007661) B2007661
theorem B1587379 : Blo 1409524 1587379 := bstep (se 1 (by rfl) ⟨1190534, by rfl⟩ : syracuseStep 1587379 = 2381069) B2381069
theorem B2259137 : Blo 1409524 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B1784035 : Blo 1409524 1784035 := bstep (se 1 (by rfl) ⟨1338026, by rfl⟩ : syracuseStep 1784035 = 2676053) B2676053
theorem B2144513 : Blo 1409524 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B4757777 : Blo 1409524 4757777 := bstep (se 2 (by rfl) ⟨1784166, by rfl⟩ : syracuseStep 4757777 = 3568333) B3568333
theorem B1587523 : Blo 1409524 1587523 := bstep (se 1 (by rfl) ⟨1190642, by rfl⟩ : syracuseStep 1587523 = 2381285) B2381285
theorem B8034673 : Blo 1409524 8034673 := bstep (se 2 (by rfl) ⟨3013002, by rfl⟩ : syracuseStep 8034673 = 6026005) B6026005
theorem B3570065 : Blo 1409524 3570065 := bstep (se 2 (by rfl) ⟨1338774, by rfl⟩ : syracuseStep 3570065 = 2677549) B2677549
theorem B3570115 : Blo 1409524 3570115 := bstep (se 1 (by rfl) ⟨2677586, by rfl⟩ : syracuseStep 3570115 = 5355173) B5355173
theorem B1587667 : Blo 1409524 1587667 := bstep (se 1 (by rfl) ⟨1190750, by rfl⟩ : syracuseStep 1587667 = 2381501) B2381501
theorem B15464945 : Blo 1409524 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B1505827 : Blo 1409524 1505827 := bstep (se 1 (by rfl) ⟨1129370, by rfl⟩ : syracuseStep 1505827 = 2258741) B2258741
theorem B2677283 : Blo 1409524 2677283 := bstep (se 1 (by rfl) ⟨2007962, by rfl⟩ : syracuseStep 2677283 = 4015925) B4015925
theorem B3570257 : Blo 1409524 3570257 := bstep (se 2 (by rfl) ⟨1338846, by rfl⟩ : syracuseStep 3570257 = 2677693) B2677693
theorem B1587811 : Blo 1409524 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B5356145 : Blo 1409524 5356145 := bstep (se 2 (by rfl) ⟨2008554, by rfl⟩ : syracuseStep 5356145 = 4017109) B4017109
theorem B2202275 : Blo 1409524 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B6781603 : Blo 1409524 6781603 := bstep (se 1 (by rfl) ⟨5086202, by rfl⟩ : syracuseStep 6781603 = 10172405) B10172405
theorem B3865265 : Blo 1409524 3865265 := bstep (se 2 (by rfl) ⟨1449474, by rfl⟩ : syracuseStep 3865265 = 2898949) B2898949
theorem B7142093 : Blo 1409524 7142093 := bstep (se 3 (by rfl) ⟨1339142, by rfl⟩ : syracuseStep 7142093 = 2678285) B2678285
theorem B1784531 : Blo 1409524 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B8575715 : Blo 1409524 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B1587955 : Blo 1409524 1587955 := bstep (se 1 (by rfl) ⟨1190966, by rfl⟩ : syracuseStep 1587955 = 2381933) B2381933
theorem B3013379 : Blo 1409524 3013379 := bstep (se 1 (by rfl) ⟨2260034, by rfl⟩ : syracuseStep 3013379 = 4520069) B4520069
theorem B8583941 : Blo 1409524 8583941 := bstep (se 4 (by rfl) ⟨804744, by rfl⟩ : syracuseStep 8583941 = 1609489) B1609489
theorem B10713869 : Blo 1409524 10713869 := bstep (se 3 (by rfl) ⟨2008850, by rfl⟩ : syracuseStep 10713869 = 4017701) B4017701
theorem B4758317 : Blo 1409524 4758317 := bstep (se 3 (by rfl) ⟨892184, by rfl⟩ : syracuseStep 4758317 = 1784369) B1784369
theorem B4758371 : Blo 1409524 4758371 := bstep (se 1 (by rfl) ⟨3568778, by rfl⟩ : syracuseStep 4758371 = 7137557) B7137557
theorem B2857859 : Blo 1409524 2857859 := bstep (se 1 (by rfl) ⟨2143394, by rfl⟩ : syracuseStep 2857859 = 4286789) B4286789
theorem B6773645 : Blo 1409524 6773645 := bstep (se 3 (by rfl) ⟨1270058, by rfl⟩ : syracuseStep 6773645 = 2540117) B2540117
theorem B3619729 : Blo 1409524 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B2259971 : Blo 1409524 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B4070417 : Blo 1409524 4070417 := bstep (se 2 (by rfl) ⟨1526406, by rfl⟩ : syracuseStep 4070417 = 3052813) B3052813
theorem B2260003 : Blo 1409524 2260003 := bstep (se 1 (by rfl) ⟨1695002, by rfl⟩ : syracuseStep 2260003 = 3390005) B3390005
theorem B4758641 : Blo 1409524 4758641 := bstep (se 2 (by rfl) ⟨1784490, by rfl⟩ : syracuseStep 4758641 = 3568981) B3568981
theorem B27475085 : Blo 1409524 27475085 := bstep (se 3 (by rfl) ⟨5151578, by rfl⟩ : syracuseStep 27475085 = 10303157) B10303157
theorem B6028451 : Blo 1409524 6028451 := bstep (se 1 (by rfl) ⟨4521338, by rfl⟩ : syracuseStep 6028451 = 9042677) B9042677
theorem B15465653 : Blo 1409524 15465653 := bstep (se 5 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 15465653 = 1449905) B1449905
theorem B3013841 : Blo 1409524 3013841 := bstep (se 2 (by rfl) ⟨1130190, by rfl⟩ : syracuseStep 3013841 = 2260381) B2260381
theorem B4521197 : Blo 1409524 4521197 := bstep (se 3 (by rfl) ⟨847724, by rfl⟩ : syracuseStep 4521197 = 1695449) B1695449
theorem B5356813 : Blo 1409524 5356813 := bstep (se 3 (by rfl) ⟨1004402, by rfl⟩ : syracuseStep 5356813 = 2008805) B2008805
theorem B1785235 : Blo 1409524 1785235 := bstep (se 1 (by rfl) ⟨1338926, by rfl⟩ : syracuseStep 1785235 = 2677853) B2677853
theorem B2678179 : Blo 1409524 2678179 := bstep (se 1 (by rfl) ⟨2008634, by rfl⟩ : syracuseStep 2678179 = 4017269) B4017269
theorem B13401571 : Blo 1409524 13401571 := bstep (se 1 (by rfl) ⟨10051178, by rfl⟩ : syracuseStep 13401571 = 20102357) B20102357
theorem B1785331 : Blo 1409524 1785331 := bstep (se 1 (by rfl) ⟨1338998, by rfl⟩ : syracuseStep 1785331 = 2677997) B2677997
theorem B3571249 : Blo 1409524 3571249 := bstep (se 2 (by rfl) ⟨1339218, by rfl⟩ : syracuseStep 3571249 = 2678437) B2678437
theorem B2678339 : Blo 1409524 2678339 := bstep (se 1 (by rfl) ⟨2008754, by rfl⟩ : syracuseStep 2678339 = 4017509) B4017509
theorem B7626317 : Blo 1409524 7626317 := bstep (se 3 (by rfl) ⟨1429934, by rfl⟩ : syracuseStep 7626317 = 2859869) B2859869
theorem B4292227 : Blo 1409524 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B4759181 : Blo 1409524 4759181 := bstep (se 3 (by rfl) ⟨892346, by rfl⟩ : syracuseStep 4759181 = 1784693) B1784693
theorem B4759235 : Blo 1409524 4759235 := bstep (se 1 (by rfl) ⟨3569426, by rfl⟩ : syracuseStep 4759235 = 7138853) B7138853
theorem B8027909 : Blo 1409524 8027909 := bstep (se 4 (by rfl) ⟨752616, by rfl⟩ : syracuseStep 8027909 = 1505233) B1505233
theorem B1507091 : Blo 1409524 1507091 := bstep (se 1 (by rfl) ⟨1130318, by rfl⟩ : syracuseStep 1507091 = 2260637) B2260637
theorem B8036131 : Blo 1409524 8036131 := bstep (se 1 (by rfl) ⟨6027098, by rfl⟩ : syracuseStep 8036131 = 12054197) B12054197
theorem B3571523 : Blo 1409524 3571523 := bstep (se 1 (by rfl) ⟨2678642, by rfl⟩ : syracuseStep 3571523 = 5357285) B5357285
theorem B4013965 : Blo 1409524 4013965 := bstep (se 3 (by rfl) ⟨752618, by rfl⟩ : syracuseStep 4013965 = 1505237) B1505237
theorem B2858897 : Blo 1409524 2858897 := bstep (se 2 (by rfl) ⟨1072086, by rfl⟩ : syracuseStep 2858897 = 2144173) B2144173
theorem B2260931 : Blo 1409524 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B13565893 : Blo 1409524 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B4759505 : Blo 1409524 4759505 := bstep (se 2 (by rfl) ⟨1784814, by rfl⟩ : syracuseStep 4759505 = 3569629) B3569629
theorem B1785827 : Blo 1409524 1785827 := bstep (se 1 (by rfl) ⟨1339370, by rfl⟩ : syracuseStep 1785827 = 2678741) B2678741
theorem B3571735 : Blo 1409524 3571735 := bstep (se 1 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 3571735 = 5357603) B5357603
theorem B2678923 : Blo 1409524 2678923 := bstep (se 1 (by rfl) ⟨2009192, by rfl⟩ : syracuseStep 2678923 = 4018385) B4018385
theorem B8577175 : Blo 1409524 8577175 := bstep (se 1 (by rfl) ⟨6432881, by rfl⟩ : syracuseStep 8577175 = 12865763) B12865763
theorem B11600023 : Blo 1409524 11600023 := bstep (se 1 (by rfl) ⟨8700017, by rfl⟩ : syracuseStep 11600023 = 17400035) B17400035
theorem B43417781 : Blo 1409524 43417781 := bstep (se 5 (by rfl) ⟨2035208, by rfl⟩ : syracuseStep 43417781 = 4070417) B4070417
theorem B5357771 : Blo 1409524 5357771 := bstep (se 1 (by rfl) ⟨4018328, by rfl⟩ : syracuseStep 5357771 = 8036657) B8036657
theorem B2900171 : Blo 1409524 2900171 := bstep (se 1 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 2900171 = 4350257) B4350257
theorem B5357785 : Blo 1409524 5357785 := bstep (se 2 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 5357785 = 4018339) B4018339
theorem B4759883 : Blo 1409524 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B3572171 : Blo 1409524 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B2679257 : Blo 1409524 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B1409527 : Blo 1409524 1409527 := bstep (se 1 (by rfl) ⟨1057145, by rfl⟩ : syracuseStep 1409527 = 2114291) B2114291
theorem B1409547 : Blo 1409524 1409547 := bstep (se 1 (by rfl) ⟨1057160, by rfl⟩ : syracuseStep 1409547 = 2114321) B2114321
theorem B1409559 : Blo 1409524 1409559 := bstep (se 1 (by rfl) ⟨1057169, by rfl⟩ : syracuseStep 1409559 = 2114339) B2114339
theorem B1409579 : Blo 1409524 1409579 := bstep (se 1 (by rfl) ⟨1057184, by rfl⟩ : syracuseStep 1409579 = 2114369) B2114369
theorem B1409591 : Blo 1409524 1409591 := bstep (se 1 (by rfl) ⟨1057193, by rfl⟩ : syracuseStep 1409591 = 2114387) B2114387
theorem B1409611 : Blo 1409524 1409611 := bstep (se 1 (by rfl) ⟨1057208, by rfl⟩ : syracuseStep 1409611 = 2114417) B2114417
theorem B1409623 : Blo 1409524 1409623 := bstep (se 1 (by rfl) ⟨1057217, by rfl⟩ : syracuseStep 1409623 = 2114435) B2114435
theorem B4760153 : Blo 1409524 4760153 := bstep (se 2 (by rfl) ⟨1785057, by rfl⟩ : syracuseStep 4760153 = 3570115) B3570115
theorem B1409643 : Blo 1409524 1409643 := bstep (se 1 (by rfl) ⟨1057232, by rfl⟩ : syracuseStep 1409643 = 2114465) B2114465
theorem B1409655 : Blo 1409524 1409655 := bstep (se 1 (by rfl) ⟨1057241, by rfl⟩ : syracuseStep 1409655 = 2114483) B2114483
theorem B1409675 : Blo 1409524 1409675 := bstep (se 1 (by rfl) ⟨1057256, by rfl⟩ : syracuseStep 1409675 = 2114513) B2114513
theorem B1409687 : Blo 1409524 1409687 := bstep (se 1 (by rfl) ⟨1057265, by rfl⟩ : syracuseStep 1409687 = 2114531) B2114531
theorem B1409707 : Blo 1409524 1409707 := bstep (se 1 (by rfl) ⟨1057280, by rfl⟩ : syracuseStep 1409707 = 2114561) B2114561
theorem B5718701 : Blo 1409524 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B1409719 : Blo 1409524 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B4014785 : Blo 1409524 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B1409739 : Blo 1409524 1409739 := bstep (se 1 (by rfl) ⟨1057304, by rfl⟩ : syracuseStep 1409739 = 2114609) B2114609
theorem B1409751 : Blo 1409524 1409751 := bstep (se 1 (by rfl) ⟨1057313, by rfl⟩ : syracuseStep 1409751 = 2114627) B2114627
theorem B4014809 : Blo 1409524 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B2007769 : Blo 1409524 2007769 := bstep (se 2 (by rfl) ⟨752913, by rfl⟩ : syracuseStep 2007769 = 1505827) B1505827
theorem B1409771 : Blo 1409524 1409771 := bstep (se 1 (by rfl) ⟨1057328, by rfl⟩ : syracuseStep 1409771 = 2114657) B2114657
theorem B1409783 : Blo 1409524 1409783 := bstep (se 1 (by rfl) ⟨1057337, by rfl⟩ : syracuseStep 1409783 = 2114675) B2114675
theorem B2114315 : Blo 1409524 2114315 := bstep (se 1 (by rfl) ⟨1585736, by rfl⟩ : syracuseStep 2114315 = 3171473) B3171473
theorem B1409803 : Blo 1409524 1409803 := bstep (se 1 (by rfl) ⟨1057352, by rfl⟩ : syracuseStep 1409803 = 2114705) B2114705
theorem B2114327 : Blo 1409524 2114327 := bstep (se 1 (by rfl) ⟨1585745, by rfl⟩ : syracuseStep 2114327 = 3171491) B3171491
theorem B1409815 : Blo 1409524 1409815 := bstep (se 1 (by rfl) ⟨1057361, by rfl⟩ : syracuseStep 1409815 = 2114723) B2114723
theorem B2859799 : Blo 1409524 2859799 := bstep (se 1 (by rfl) ⟨2144849, by rfl⟩ : syracuseStep 2859799 = 4289699) B4289699
theorem B1409835 : Blo 1409524 1409835 := bstep (se 1 (by rfl) ⟨1057376, by rfl⟩ : syracuseStep 1409835 = 2114753) B2114753
theorem B1409847 : Blo 1409524 1409847 := bstep (se 1 (by rfl) ⟨1057385, by rfl⟩ : syracuseStep 1409847 = 2114771) B2114771
theorem B3572545 : Blo 1409524 3572545 := bstep (se 2 (by rfl) ⟨1339704, by rfl⟩ : syracuseStep 3572545 = 2679409) B2679409
theorem B1409867 : Blo 1409524 1409867 := bstep (se 1 (by rfl) ⟨1057400, by rfl⟩ : syracuseStep 1409867 = 2114801) B2114801
theorem B1409879 : Blo 1409524 1409879 := bstep (se 1 (by rfl) ⟨1057409, by rfl⟩ : syracuseStep 1409879 = 2114819) B2114819
theorem B2114393 : Blo 1409524 2114393 := bstep (se 2 (by rfl) ⟨792897, by rfl⟩ : syracuseStep 2114393 = 1585795) B1585795
theorem B1409899 : Blo 1409524 1409899 := bstep (se 1 (by rfl) ⟨1057424, by rfl⟩ : syracuseStep 1409899 = 2114849) B2114849
theorem B1409911 : Blo 1409524 1409911 := bstep (se 1 (by rfl) ⟨1057433, by rfl⟩ : syracuseStep 1409911 = 2114867) B2114867
theorem B1409931 : Blo 1409524 1409931 := bstep (se 1 (by rfl) ⟨1057448, by rfl⟩ : syracuseStep 1409931 = 2114897) B2114897
theorem B1409943 : Blo 1409524 1409943 := bstep (se 1 (by rfl) ⟨1057457, by rfl⟩ : syracuseStep 1409943 = 2114915) B2114915
theorem B1409963 : Blo 1409524 1409963 := bstep (se 1 (by rfl) ⟨1057472, by rfl⟩ : syracuseStep 1409963 = 2114945) B2114945
theorem B1409975 : Blo 1409524 1409975 := bstep (se 1 (by rfl) ⟨1057481, by rfl⟩ : syracuseStep 1409975 = 2114963) B2114963
theorem B2114507 : Blo 1409524 2114507 := bstep (se 1 (by rfl) ⟨1585880, by rfl⟩ : syracuseStep 2114507 = 3171761) B3171761
theorem B2540491 : Blo 1409524 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B1409995 : Blo 1409524 1409995 := bstep (se 1 (by rfl) ⟨1057496, by rfl⟩ : syracuseStep 1409995 = 2114993) B2114993
theorem B2114519 : Blo 1409524 2114519 := bstep (se 1 (by rfl) ⟨1585889, by rfl⟩ : syracuseStep 2114519 = 3171779) B3171779
theorem B1410007 : Blo 1409524 1410007 := bstep (se 1 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 1410007 = 2115011) B2115011
theorem B1410027 : Blo 1409524 1410027 := bstep (se 1 (by rfl) ⟨1057520, by rfl⟩ : syracuseStep 1410027 = 2115041) B2115041
theorem B1410039 : Blo 1409524 1410039 := bstep (se 1 (by rfl) ⟨1057529, by rfl⟩ : syracuseStep 1410039 = 2115059) B2115059
theorem B1410059 : Blo 1409524 1410059 := bstep (se 1 (by rfl) ⟨1057544, by rfl⟩ : syracuseStep 1410059 = 2115089) B2115089
theorem B1410071 : Blo 1409524 1410071 := bstep (se 1 (by rfl) ⟨1057553, by rfl⟩ : syracuseStep 1410071 = 2115107) B2115107
theorem B2114585 : Blo 1409524 2114585 := bstep (se 2 (by rfl) ⟨792969, by rfl⟩ : syracuseStep 2114585 = 1585939) B1585939
theorem B1410091 : Blo 1409524 1410091 := bstep (se 1 (by rfl) ⟨1057568, by rfl⟩ : syracuseStep 1410091 = 2115137) B2115137
theorem B1410103 : Blo 1409524 1410103 := bstep (se 1 (by rfl) ⟨1057577, by rfl⟩ : syracuseStep 1410103 = 2115155) B2115155
theorem B1410123 : Blo 1409524 1410123 := bstep (se 1 (by rfl) ⟨1057592, by rfl⟩ : syracuseStep 1410123 = 2115185) B2115185
theorem B7144523 : Blo 1409524 7144523 := bstep (se 1 (by rfl) ⟨5358392, by rfl⟩ : syracuseStep 7144523 = 10716785) B10716785
theorem B1410135 : Blo 1409524 1410135 := bstep (se 1 (by rfl) ⟨1057601, by rfl⟩ : syracuseStep 1410135 = 2115203) B2115203
theorem B7627877 : Blo 1409524 7627877 := bstep (se 4 (by rfl) ⟨715113, by rfl⟩ : syracuseStep 7627877 = 1430227) B1430227
theorem B1410155 : Blo 1409524 1410155 := bstep (se 1 (by rfl) ⟨1057616, by rfl⟩ : syracuseStep 1410155 = 2115233) B2115233
theorem B2540659 : Blo 1409524 2540659 := bstep (se 1 (by rfl) ⟨1905494, by rfl⟩ : syracuseStep 2540659 = 3810989) B3810989
theorem B1410167 : Blo 1409524 1410167 := bstep (se 1 (by rfl) ⟨1057625, by rfl⟩ : syracuseStep 1410167 = 2115251) B2115251
theorem B2114699 : Blo 1409524 2114699 := bstep (se 1 (by rfl) ⟨1586024, by rfl⟩ : syracuseStep 2114699 = 3172049) B3172049
theorem B1410187 : Blo 1409524 1410187 := bstep (se 1 (by rfl) ⟨1057640, by rfl⟩ : syracuseStep 1410187 = 2115281) B2115281
theorem B2114711 : Blo 1409524 2114711 := bstep (se 1 (by rfl) ⟨1586033, by rfl⟩ : syracuseStep 2114711 = 3172067) B3172067
theorem B1410199 : Blo 1409524 1410199 := bstep (se 1 (by rfl) ⟨1057649, by rfl⟩ : syracuseStep 1410199 = 2115299) B2115299
theorem B5358743 : Blo 1409524 5358743 := bstep (se 1 (by rfl) ⟨4019057, by rfl⟩ : syracuseStep 5358743 = 8038115) B8038115
theorem B1410219 : Blo 1409524 1410219 := bstep (se 1 (by rfl) ⟨1057664, by rfl⟩ : syracuseStep 1410219 = 2115329) B2115329
theorem B1410231 : Blo 1409524 1410231 := bstep (se 1 (by rfl) ⟨1057673, by rfl⟩ : syracuseStep 1410231 = 2115347) B2115347
theorem B4826305 : Blo 1409524 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1410251 : Blo 1409524 1410251 := bstep (se 1 (by rfl) ⟨1057688, by rfl⟩ : syracuseStep 1410251 = 2115377) B2115377
theorem B1410263 : Blo 1409524 1410263 := bstep (se 1 (by rfl) ⟨1057697, by rfl⟩ : syracuseStep 1410263 = 2115395) B2115395
theorem B3171545 : Blo 1409524 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B2114777 : Blo 1409524 2114777 := bstep (se 2 (by rfl) ⟨793041, by rfl⟩ : syracuseStep 2114777 = 1586083) B1586083
theorem B1410283 : Blo 1409524 1410283 := bstep (se 1 (by rfl) ⟨1057712, by rfl⟩ : syracuseStep 1410283 = 2115425) B2115425
theorem B1410295 : Blo 1409524 1410295 := bstep (se 1 (by rfl) ⟨1057721, by rfl⟩ : syracuseStep 1410295 = 2115443) B2115443
theorem B1410315 : Blo 1409524 1410315 := bstep (se 1 (by rfl) ⟨1057736, by rfl⟩ : syracuseStep 1410315 = 2115473) B2115473
theorem B1410327 : Blo 1409524 1410327 := bstep (se 1 (by rfl) ⟨1057745, by rfl⟩ : syracuseStep 1410327 = 2115491) B2115491
theorem B4760855 : Blo 1409524 4760855 := bstep (se 1 (by rfl) ⟨3570641, by rfl⟩ : syracuseStep 4760855 = 7141283) B7141283
theorem B1410347 : Blo 1409524 1410347 := bstep (se 1 (by rfl) ⟨1057760, by rfl⟩ : syracuseStep 1410347 = 2115521) B2115521
theorem B3171635 : Blo 1409524 3171635 := bstep (se 1 (by rfl) ⟨2378726, by rfl⟩ : syracuseStep 3171635 = 4757453) B4757453
theorem B6022451 : Blo 1409524 6022451 := bstep (se 1 (by rfl) ⟨4516838, by rfl⟩ : syracuseStep 6022451 = 9033677) B9033677
theorem B1410359 : Blo 1409524 1410359 := bstep (se 1 (by rfl) ⟨1057769, by rfl⟩ : syracuseStep 1410359 = 2115539) B2115539
theorem B2114891 : Blo 1409524 2114891 := bstep (se 1 (by rfl) ⟨1586168, by rfl⟩ : syracuseStep 2114891 = 3172337) B3172337
theorem B1410379 : Blo 1409524 1410379 := bstep (se 1 (by rfl) ⟨1057784, by rfl⟩ : syracuseStep 1410379 = 2115569) B2115569
theorem B3171671 : Blo 1409524 3171671 := bstep (se 1 (by rfl) ⟨2378753, by rfl⟩ : syracuseStep 3171671 = 4757507) B4757507
theorem B2114903 : Blo 1409524 2114903 := bstep (se 1 (by rfl) ⟨1586177, by rfl⟩ : syracuseStep 2114903 = 3172355) B3172355
theorem B1410391 : Blo 1409524 1410391 := bstep (se 1 (by rfl) ⟨1057793, by rfl⟩ : syracuseStep 1410391 = 2115587) B2115587
theorem B1410411 : Blo 1409524 1410411 := bstep (se 1 (by rfl) ⟨1057808, by rfl⟩ : syracuseStep 1410411 = 2115617) B2115617
theorem B1410423 : Blo 1409524 1410423 := bstep (se 1 (by rfl) ⟨1057817, by rfl⟩ : syracuseStep 1410423 = 2115635) B2115635
theorem B1410443 : Blo 1409524 1410443 := bstep (se 1 (by rfl) ⟨1057832, by rfl⟩ : syracuseStep 1410443 = 2115665) B2115665
theorem B1410455 : Blo 1409524 1410455 := bstep (se 1 (by rfl) ⟨1057841, by rfl⟩ : syracuseStep 1410455 = 2115683) B2115683
theorem B2114969 : Blo 1409524 2114969 := bstep (se 2 (by rfl) ⟨793113, by rfl⟩ : syracuseStep 2114969 = 1586227) B1586227
theorem B1410475 : Blo 1409524 1410475 := bstep (se 1 (by rfl) ⟨1057856, by rfl⟩ : syracuseStep 1410475 = 2115713) B2115713
theorem B1410487 : Blo 1409524 1410487 := bstep (se 1 (by rfl) ⟨1057865, by rfl⟩ : syracuseStep 1410487 = 2115731) B2115731
theorem B1410507 : Blo 1409524 1410507 := bstep (se 1 (by rfl) ⟨1057880, by rfl⟩ : syracuseStep 1410507 = 2115761) B2115761
theorem B1410519 : Blo 1409524 1410519 := bstep (se 1 (by rfl) ⟨1057889, by rfl⟩ : syracuseStep 1410519 = 2115779) B2115779
theorem B1410539 : Blo 1409524 1410539 := bstep (se 1 (by rfl) ⟨1057904, by rfl⟩ : syracuseStep 1410539 = 2115809) B2115809
theorem B1410551 : Blo 1409524 1410551 := bstep (se 1 (by rfl) ⟨1057913, by rfl⟩ : syracuseStep 1410551 = 2115827) B2115827
theorem B3171851 : Blo 1409524 3171851 := bstep (se 1 (by rfl) ⟨2378888, by rfl⟩ : syracuseStep 3171851 = 4757777) B4757777
theorem B2115083 : Blo 1409524 2115083 := bstep (se 1 (by rfl) ⟨1586312, by rfl⟩ : syracuseStep 2115083 = 3172625) B3172625
theorem B1410571 : Blo 1409524 1410571 := bstep (se 1 (by rfl) ⟨1057928, by rfl⟩ : syracuseStep 1410571 = 2115857) B2115857
theorem B2115095 : Blo 1409524 2115095 := bstep (se 1 (by rfl) ⟨1586321, by rfl⟩ : syracuseStep 2115095 = 3172643) B3172643
theorem B1410583 : Blo 1409524 1410583 := bstep (se 1 (by rfl) ⟨1057937, by rfl⟩ : syracuseStep 1410583 = 2115875) B2115875
theorem B1410603 : Blo 1409524 1410603 := bstep (se 1 (by rfl) ⟨1057952, by rfl⟩ : syracuseStep 1410603 = 2115905) B2115905
theorem B1410615 : Blo 1409524 1410615 := bstep (se 1 (by rfl) ⟨1057961, by rfl⟩ : syracuseStep 1410615 = 2115923) B2115923
theorem B3171905 : Blo 1409524 3171905 := bstep (se 2 (by rfl) ⟨1189464, by rfl⟩ : syracuseStep 3171905 = 2378929) B2378929
theorem B1410635 : Blo 1409524 1410635 := bstep (se 1 (by rfl) ⟨1057976, by rfl⟩ : syracuseStep 1410635 = 2115953) B2115953
theorem B1410647 : Blo 1409524 1410647 := bstep (se 1 (by rfl) ⟨1057985, by rfl⟩ : syracuseStep 1410647 = 2115971) B2115971
theorem B2115161 : Blo 1409524 2115161 := bstep (se 2 (by rfl) ⟨793185, by rfl⟩ : syracuseStep 2115161 = 1586371) B1586371
theorem B11437661 : Blo 1409524 11437661 := bstep (se 3 (by rfl) ⟨2144561, by rfl⟩ : syracuseStep 11437661 = 4289123) B4289123
theorem B1410667 : Blo 1409524 1410667 := bstep (se 1 (by rfl) ⟨1058000, by rfl⟩ : syracuseStep 1410667 = 2116001) B2116001
theorem B1410679 : Blo 1409524 1410679 := bstep (se 1 (by rfl) ⟨1058009, by rfl⟩ : syracuseStep 1410679 = 2116019) B2116019
theorem B1410699 : Blo 1409524 1410699 := bstep (se 1 (by rfl) ⟨1058024, by rfl⟩ : syracuseStep 1410699 = 2116049) B2116049
theorem B1410711 : Blo 1409524 1410711 := bstep (se 1 (by rfl) ⟨1058033, by rfl⟩ : syracuseStep 1410711 = 2116067) B2116067
theorem B1410731 : Blo 1409524 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B2541235 : Blo 1409524 2541235 := bstep (se 1 (by rfl) ⟨1905926, by rfl⟩ : syracuseStep 2541235 = 3811853) B3811853
theorem B1410743 : Blo 1409524 1410743 := bstep (se 1 (by rfl) ⟨1058057, by rfl⟩ : syracuseStep 1410743 = 2116115) B2116115
theorem B2115275 : Blo 1409524 2115275 := bstep (se 1 (by rfl) ⟨1586456, by rfl⟩ : syracuseStep 2115275 = 3172913) B3172913
theorem B1410763 : Blo 1409524 1410763 := bstep (se 1 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 1410763 = 2116145) B2116145
theorem B2115287 : Blo 1409524 2115287 := bstep (se 1 (by rfl) ⟨1586465, by rfl⟩ : syracuseStep 2115287 = 3172931) B3172931
theorem B1410775 : Blo 1409524 1410775 := bstep (se 1 (by rfl) ⟨1058081, by rfl⟩ : syracuseStep 1410775 = 2116163) B2116163
theorem B1410795 : Blo 1409524 1410795 := bstep (se 1 (by rfl) ⟨1058096, by rfl⟩ : syracuseStep 1410795 = 2116193) B2116193
theorem B1410807 : Blo 1409524 1410807 := bstep (se 1 (by rfl) ⟨1058105, by rfl⟩ : syracuseStep 1410807 = 2116211) B2116211
theorem B1410827 : Blo 1409524 1410827 := bstep (se 1 (by rfl) ⟨1058120, by rfl⟩ : syracuseStep 1410827 = 2116241) B2116241
theorem B1410839 : Blo 1409524 1410839 := bstep (se 1 (by rfl) ⟨1058129, by rfl⟩ : syracuseStep 1410839 = 2116259) B2116259
theorem B3172121 : Blo 1409524 3172121 := bstep (se 2 (by rfl) ⟨1189545, by rfl⟩ : syracuseStep 3172121 = 2379091) B2379091
theorem B2115353 : Blo 1409524 2115353 := bstep (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) B1586515
theorem B1410859 : Blo 1409524 1410859 := bstep (se 1 (by rfl) ⟨1058144, by rfl⟩ : syracuseStep 1410859 = 2116289) B2116289
theorem B4761395 : Blo 1409524 4761395 := bstep (se 1 (by rfl) ⟨3571046, by rfl⟩ : syracuseStep 4761395 = 7142093) B7142093
theorem B1410871 : Blo 1409524 1410871 := bstep (se 1 (by rfl) ⟨1058153, by rfl⟩ : syracuseStep 1410871 = 2116307) B2116307
theorem B5080897 : Blo 1409524 5080897 := bstep (se 2 (by rfl) ⟨1905336, by rfl⟩ : syracuseStep 5080897 = 3810673) B3810673
theorem B1410891 : Blo 1409524 1410891 := bstep (se 1 (by rfl) ⟨1058168, by rfl⟩ : syracuseStep 1410891 = 2116337) B2116337
theorem B1410903 : Blo 1409524 1410903 := bstep (se 1 (by rfl) ⟨1058177, by rfl⟩ : syracuseStep 1410903 = 2116355) B2116355
theorem B2008919 : Blo 1409524 2008919 := bstep (se 1 (by rfl) ⟨1506689, by rfl⟩ : syracuseStep 2008919 = 3013379) B3013379
theorem B5080925 : Blo 1409524 5080925 := bstep (se 3 (by rfl) ⟨952673, by rfl⟩ : syracuseStep 5080925 = 1905347) B1905347
theorem B1410923 : Blo 1409524 1410923 := bstep (se 1 (by rfl) ⟨1058192, by rfl⟩ : syracuseStep 1410923 = 2116385) B2116385
theorem B3172211 : Blo 1409524 3172211 := bstep (se 1 (by rfl) ⟨2379158, by rfl⟩ : syracuseStep 3172211 = 4758317) B4758317
theorem B1410935 : Blo 1409524 1410935 := bstep (se 1 (by rfl) ⟨1058201, by rfl⟩ : syracuseStep 1410935 = 2116403) B2116403
theorem B2115467 : Blo 1409524 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B1410955 : Blo 1409524 1410955 := bstep (se 1 (by rfl) ⟨1058216, by rfl⟩ : syracuseStep 1410955 = 2116433) B2116433
theorem B3172247 : Blo 1409524 3172247 := bstep (se 1 (by rfl) ⟨2379185, by rfl⟩ : syracuseStep 3172247 = 4758371) B4758371
theorem B2115479 : Blo 1409524 2115479 := bstep (se 1 (by rfl) ⟨1586609, by rfl⟩ : syracuseStep 2115479 = 3173219) B3173219
theorem B1410967 : Blo 1409524 1410967 := bstep (se 1 (by rfl) ⟨1058225, by rfl⟩ : syracuseStep 1410967 = 2116451) B2116451
theorem B1410987 : Blo 1409524 1410987 := bstep (se 1 (by rfl) ⟨1058240, by rfl⟩ : syracuseStep 1410987 = 2116481) B2116481
theorem B4515763 : Blo 1409524 4515763 := bstep (se 1 (by rfl) ⟨3386822, by rfl⟩ : syracuseStep 4515763 = 6773645) B6773645
theorem B4016051 : Blo 1409524 4016051 := bstep (se 1 (by rfl) ⟨3012038, by rfl⟩ : syracuseStep 4016051 = 6024077) B6024077
theorem B1410999 : Blo 1409524 1410999 := bstep (se 1 (by rfl) ⟨1058249, by rfl⟩ : syracuseStep 1410999 = 2116499) B2116499
theorem B1411019 : Blo 1409524 1411019 := bstep (se 1 (by rfl) ⟨1058264, by rfl⟩ : syracuseStep 1411019 = 2116529) B2116529
theorem B1411031 : Blo 1409524 1411031 := bstep (se 1 (by rfl) ⟨1058273, by rfl⟩ : syracuseStep 1411031 = 2116547) B2116547
theorem B2115545 : Blo 1409524 2115545 := bstep (se 2 (by rfl) ⟨793329, by rfl⟩ : syracuseStep 2115545 = 1586659) B1586659
theorem B17868761 : Blo 1409524 17868761 := bstep (se 2 (by rfl) ⟨6700785, by rfl⟩ : syracuseStep 17868761 = 13401571) B13401571
theorem B1411051 : Blo 1409524 1411051 := bstep (se 1 (by rfl) ⟨1058288, by rfl⟩ : syracuseStep 1411051 = 2116577) B2116577
theorem B1411063 : Blo 1409524 1411063 := bstep (se 1 (by rfl) ⟨1058297, by rfl⟩ : syracuseStep 1411063 = 2116595) B2116595
theorem B1411083 : Blo 1409524 1411083 := bstep (se 1 (by rfl) ⟨1058312, by rfl⟩ : syracuseStep 1411083 = 2116625) B2116625
theorem B22890509 : Blo 1409524 22890509 := bstep (se 3 (by rfl) ⟨4291970, by rfl⟩ : syracuseStep 22890509 = 8583941) B8583941
theorem B10709009 : Blo 1409524 10709009 := bstep (se 2 (by rfl) ⟨4015878, by rfl⟩ : syracuseStep 10709009 = 8031757) B8031757
theorem B1411095 : Blo 1409524 1411095 := bstep (se 1 (by rfl) ⟨1058321, by rfl⟩ : syracuseStep 1411095 = 2116643) B2116643
theorem B1411115 : Blo 1409524 1411115 := bstep (se 1 (by rfl) ⟨1058336, by rfl⟩ : syracuseStep 1411115 = 2116673) B2116673
theorem B1411127 : Blo 1409524 1411127 := bstep (se 1 (by rfl) ⟨1058345, by rfl⟩ : syracuseStep 1411127 = 2116691) B2116691
theorem B4515905 : Blo 1409524 4515905 := bstep (se 2 (by rfl) ⟨1693464, by rfl⟩ : syracuseStep 4515905 = 3386929) B3386929
theorem B4761665 : Blo 1409524 4761665 := bstep (se 2 (by rfl) ⟨1785624, by rfl⟩ : syracuseStep 4761665 = 3571249) B3571249
theorem B3172427 : Blo 1409524 3172427 := bstep (se 1 (by rfl) ⟨2379320, by rfl⟩ : syracuseStep 3172427 = 4758641) B4758641
theorem B2115659 : Blo 1409524 2115659 := bstep (se 1 (by rfl) ⟨1586744, by rfl⟩ : syracuseStep 2115659 = 3173489) B3173489
theorem B1411147 : Blo 1409524 1411147 := bstep (se 1 (by rfl) ⟨1058360, by rfl⟩ : syracuseStep 1411147 = 2116721) B2116721
theorem B2115671 : Blo 1409524 2115671 := bstep (se 1 (by rfl) ⟨1586753, by rfl⟩ : syracuseStep 2115671 = 3173507) B3173507
theorem B1411159 : Blo 1409524 1411159 := bstep (se 1 (by rfl) ⟨1058369, by rfl⟩ : syracuseStep 1411159 = 2116739) B2116739
theorem B1411179 : Blo 1409524 1411179 := bstep (se 1 (by rfl) ⟨1058384, by rfl⟩ : syracuseStep 1411179 = 2116769) B2116769
theorem B1411191 : Blo 1409524 1411191 := bstep (se 1 (by rfl) ⟨1058393, by rfl⟩ : syracuseStep 1411191 = 2116787) B2116787
theorem B3172481 : Blo 1409524 3172481 := bstep (se 2 (by rfl) ⟨1189680, by rfl⟩ : syracuseStep 3172481 = 2379361) B2379361
theorem B2009227 : Blo 1409524 2009227 := bstep (se 1 (by rfl) ⟨1506920, by rfl⟩ : syracuseStep 2009227 = 3013841) B3013841
theorem B1411211 : Blo 1409524 1411211 := bstep (se 1 (by rfl) ⟨1058408, by rfl⟩ : syracuseStep 1411211 = 2116817) B2116817
theorem B1411223 : Blo 1409524 1411223 := bstep (se 1 (by rfl) ⟨1058417, by rfl⟩ : syracuseStep 1411223 = 2116835) B2116835
theorem B2115737 : Blo 1409524 2115737 := bstep (se 2 (by rfl) ⟨793401, by rfl⟩ : syracuseStep 2115737 = 1586803) B1586803
theorem B1411243 : Blo 1409524 1411243 := bstep (se 1 (by rfl) ⟨1058432, by rfl⟩ : syracuseStep 1411243 = 2116865) B2116865
theorem B1411255 : Blo 1409524 1411255 := bstep (se 1 (by rfl) ⟨1058441, by rfl⟩ : syracuseStep 1411255 = 2116883) B2116883
theorem B5720257 : Blo 1409524 5720257 := bstep (se 2 (by rfl) ⟨2145096, by rfl⟩ : syracuseStep 5720257 = 4290193) B4290193
theorem B1411275 : Blo 1409524 1411275 := bstep (se 1 (by rfl) ⟨1058456, by rfl⟩ : syracuseStep 1411275 = 2116913) B2116913
theorem B1411287 : Blo 1409524 1411287 := bstep (se 1 (by rfl) ⟨1058465, by rfl⟩ : syracuseStep 1411287 = 2116931) B2116931
theorem B1411307 : Blo 1409524 1411307 := bstep (se 1 (by rfl) ⟨1058480, by rfl⟩ : syracuseStep 1411307 = 2116961) B2116961
theorem B1411319 : Blo 1409524 1411319 := bstep (se 1 (by rfl) ⟨1058489, by rfl⟩ : syracuseStep 1411319 = 2116979) B2116979
theorem B2115851 : Blo 1409524 2115851 := bstep (se 1 (by rfl) ⟨1586888, by rfl⟩ : syracuseStep 2115851 = 3173777) B3173777
theorem B1411339 : Blo 1409524 1411339 := bstep (se 1 (by rfl) ⟨1058504, by rfl⟩ : syracuseStep 1411339 = 2117009) B2117009
theorem B2541847 : Blo 1409524 2541847 := bstep (se 1 (by rfl) ⟨1906385, by rfl⟩ : syracuseStep 2541847 = 3812771) B3812771
theorem B2115863 : Blo 1409524 2115863 := bstep (se 1 (by rfl) ⟨1586897, by rfl⟩ : syracuseStep 2115863 = 3173795) B3173795
theorem B1411351 : Blo 1409524 1411351 := bstep (se 1 (by rfl) ⟨1058513, by rfl⟩ : syracuseStep 1411351 = 2117027) B2117027
theorem B1411371 : Blo 1409524 1411371 := bstep (se 1 (by rfl) ⟨1058528, by rfl⟩ : syracuseStep 1411371 = 2117057) B2117057
theorem B2541875 : Blo 1409524 2541875 := bstep (se 1 (by rfl) ⟨1906406, by rfl⟩ : syracuseStep 2541875 = 3812813) B3812813
theorem B1411383 : Blo 1409524 1411383 := bstep (se 1 (by rfl) ⟨1058537, by rfl⟩ : syracuseStep 1411383 = 2117075) B2117075
theorem B1411403 : Blo 1409524 1411403 := bstep (se 1 (by rfl) ⟨1058552, by rfl⟩ : syracuseStep 1411403 = 2117105) B2117105
theorem B1411415 : Blo 1409524 1411415 := bstep (se 1 (by rfl) ⟨1058561, by rfl⟩ : syracuseStep 1411415 = 2117123) B2117123
theorem B3172697 : Blo 1409524 3172697 := bstep (se 2 (by rfl) ⟨1189761, by rfl⟩ : syracuseStep 3172697 = 2379523) B2379523
theorem B2115929 : Blo 1409524 2115929 := bstep (se 2 (by rfl) ⟨793473, by rfl⟩ : syracuseStep 2115929 = 1586947) B1586947
theorem B1411435 : Blo 1409524 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B1411447 : Blo 1409524 1411447 := bstep (se 1 (by rfl) ⟨1058585, by rfl⟩ : syracuseStep 1411447 = 2117171) B2117171
theorem B1411467 : Blo 1409524 1411467 := bstep (se 1 (by rfl) ⟨1058600, by rfl⟩ : syracuseStep 1411467 = 2117201) B2117201
theorem B1411479 : Blo 1409524 1411479 := bstep (se 1 (by rfl) ⟨1058609, by rfl⟩ : syracuseStep 1411479 = 2117219) B2117219
theorem B1411499 : Blo 1409524 1411499 := bstep (se 1 (by rfl) ⟨1058624, by rfl⟩ : syracuseStep 1411499 = 2117249) B2117249
theorem B3172787 : Blo 1409524 3172787 := bstep (se 1 (by rfl) ⟨2379590, by rfl⟩ : syracuseStep 3172787 = 4759181) B4759181
theorem B1411511 : Blo 1409524 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B2116043 : Blo 1409524 2116043 := bstep (se 1 (by rfl) ⟨1587032, by rfl⟩ : syracuseStep 2116043 = 3174065) B3174065
theorem B3172823 : Blo 1409524 3172823 := bstep (se 1 (by rfl) ⟨2379617, by rfl⟩ : syracuseStep 3172823 = 4759235) B4759235
theorem B2116055 : Blo 1409524 2116055 := bstep (se 1 (by rfl) ⟨1587041, by rfl⟩ : syracuseStep 2116055 = 3174083) B3174083
theorem B5081561 : Blo 1409524 5081561 := bstep (se 2 (by rfl) ⟨1905585, by rfl⟩ : syracuseStep 5081561 = 3811171) B3811171
theorem B5351939 : Blo 1409524 5351939 := bstep (se 1 (by rfl) ⟨4013954, by rfl⟩ : syracuseStep 5351939 = 8027909) B8027909
theorem B5351953 : Blo 1409524 5351953 := bstep (se 2 (by rfl) ⟨2006982, by rfl⟩ : syracuseStep 5351953 = 4013965) B4013965
theorem B2116121 : Blo 1409524 2116121 := bstep (se 2 (by rfl) ⟨793545, by rfl⟩ : syracuseStep 2116121 = 1587091) B1587091
theorem B4762205 : Blo 1409524 4762205 := bstep (se 3 (by rfl) ⟨892913, by rfl⟩ : syracuseStep 4762205 = 1785827) B1785827
theorem B3173003 : Blo 1409524 3173003 := bstep (se 1 (by rfl) ⟨2379752, by rfl⟩ : syracuseStep 3173003 = 4759505) B4759505
theorem B2116235 : Blo 1409524 2116235 := bstep (se 1 (by rfl) ⟨1587176, by rfl⟩ : syracuseStep 2116235 = 3174353) B3174353
theorem B2116247 : Blo 1409524 2116247 := bstep (se 1 (by rfl) ⟨1587185, by rfl⟩ : syracuseStep 2116247 = 3174371) B3174371
theorem B3173057 : Blo 1409524 3173057 := bstep (se 2 (by rfl) ⟨1189896, by rfl⟩ : syracuseStep 3173057 = 2379793) B2379793
theorem B2116313 : Blo 1409524 2116313 := bstep (se 2 (by rfl) ⟨793617, by rfl⟩ : syracuseStep 2116313 = 1587235) B1587235
theorem B5352257 : Blo 1409524 5352257 := bstep (se 2 (by rfl) ⟨2007096, by rfl⟩ : syracuseStep 5352257 = 4014193) B4014193
theorem B2116427 : Blo 1409524 2116427 := bstep (se 1 (by rfl) ⟨1587320, by rfl⟩ : syracuseStep 2116427 = 3174641) B3174641
theorem B2116439 : Blo 1409524 2116439 := bstep (se 1 (by rfl) ⟨1587329, by rfl⟩ : syracuseStep 2116439 = 3174659) B3174659
theorem B2378585 : Blo 1409524 2378585 := bstep (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) B1783939
theorem B4893529 : Blo 1409524 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B3173273 : Blo 1409524 3173273 := bstep (se 2 (by rfl) ⟨1189977, by rfl⟩ : syracuseStep 3173273 = 2379955) B2379955
theorem B2116505 : Blo 1409524 2116505 := bstep (se 2 (by rfl) ⟨793689, by rfl⟩ : syracuseStep 2116505 = 1587379) B1587379
theorem B2378713 : Blo 1409524 2378713 := bstep (se 2 (by rfl) ⟨892017, by rfl⟩ : syracuseStep 2378713 = 1784035) B1784035
theorem B3173363 : Blo 1409524 3173363 := bstep (se 1 (by rfl) ⟨2380022, by rfl⟩ : syracuseStep 3173363 = 4760045) B4760045
theorem B2116619 : Blo 1409524 2116619 := bstep (se 1 (by rfl) ⟨1587464, by rfl⟩ : syracuseStep 2116619 = 3174929) B3174929
theorem B3173399 : Blo 1409524 3173399 := bstep (se 1 (by rfl) ⟨2380049, by rfl⟩ : syracuseStep 3173399 = 4760099) B4760099
theorem B2116631 : Blo 1409524 2116631 := bstep (se 1 (by rfl) ⟨1587473, by rfl⟩ : syracuseStep 2116631 = 3174947) B3174947
theorem B10718243 : Blo 1409524 10718243 := bstep (se 1 (by rfl) ⟨8038682, by rfl⟩ : syracuseStep 10718243 = 16077365) B16077365
theorem B2116697 : Blo 1409524 2116697 := bstep (se 2 (by rfl) ⟨793761, by rfl⟩ : syracuseStep 2116697 = 1587523) B1587523
theorem B16075907 : Blo 1409524 16075907 := bstep (se 1 (by rfl) ⟨12056930, by rfl⟩ : syracuseStep 16075907 = 24113861) B24113861
theorem B6024365 : Blo 1409524 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B3173579 : Blo 1409524 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B2116811 : Blo 1409524 2116811 := bstep (se 1 (by rfl) ⟨1587608, by rfl⟩ : syracuseStep 2116811 = 3175217) B3175217
theorem B2116823 : Blo 1409524 2116823 := bstep (se 1 (by rfl) ⟨1587617, by rfl⟩ : syracuseStep 2116823 = 3175235) B3175235
theorem B3173633 : Blo 1409524 3173633 := bstep (se 2 (by rfl) ⟨1190112, by rfl⟩ : syracuseStep 3173633 = 2380225) B2380225
theorem B2116889 : Blo 1409524 2116889 := bstep (se 2 (by rfl) ⟨793833, by rfl⟩ : syracuseStep 2116889 = 1587667) B1587667
theorem B7138691 : Blo 1409524 7138691 := bstep (se 1 (by rfl) ⟨5354018, by rfl⟩ : syracuseStep 7138691 = 10708037) B10708037
theorem B2117003 : Blo 1409524 2117003 := bstep (se 1 (by rfl) ⟨1587752, by rfl⟩ : syracuseStep 2117003 = 3175505) B3175505
theorem B1609111 : Blo 1409524 1609111 := bstep (se 1 (by rfl) ⟨1206833, by rfl⟩ : syracuseStep 1609111 = 2413667) B2413667
theorem B2117015 : Blo 1409524 2117015 := bstep (se 1 (by rfl) ⟨1587761, by rfl⟩ : syracuseStep 2117015 = 3175523) B3175523
theorem B3173849 : Blo 1409524 3173849 := bstep (se 2 (by rfl) ⟨1190193, by rfl⟩ : syracuseStep 3173849 = 2380387) B2380387
theorem B2117081 : Blo 1409524 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B5352925 : Blo 1409524 5352925 := bstep (se 3 (by rfl) ⟨1003673, by rfl⟩ : syracuseStep 5352925 = 2007347) B2007347
theorem B2379287 : Blo 1409524 2379287 := bstep (se 1 (by rfl) ⟨1784465, by rfl⟩ : syracuseStep 2379287 = 3568931) B3568931
theorem B3173939 : Blo 1409524 3173939 := bstep (se 1 (by rfl) ⟨2380454, by rfl⟩ : syracuseStep 3173939 = 4760909) B4760909
theorem B2117195 : Blo 1409524 2117195 := bstep (se 1 (by rfl) ⟨1587896, by rfl⟩ : syracuseStep 2117195 = 3175793) B3175793
theorem B3173975 : Blo 1409524 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B2117207 : Blo 1409524 2117207 := bstep (se 1 (by rfl) ⟨1587905, by rfl⟩ : syracuseStep 2117207 = 3175811) B3175811
theorem B20328029 : Blo 1409524 20328029 := bstep (se 3 (by rfl) ⟨3811505, by rfl⟩ : syracuseStep 20328029 = 7623011) B7623011
theorem B21720707 : Blo 1409524 21720707 := bstep (se 1 (by rfl) ⟨16290530, by rfl⟩ : syracuseStep 21720707 = 32581061) B32581061
theorem B2379415 : Blo 1409524 2379415 := bstep (se 1 (by rfl) ⟨1784561, by rfl⟩ : syracuseStep 2379415 = 3569123) B3569123
theorem B2117273 : Blo 1409524 2117273 := bstep (se 2 (by rfl) ⟨793977, by rfl⟩ : syracuseStep 2117273 = 1587955) B1587955
theorem B4763339 : Blo 1409524 4763339 := bstep (se 1 (by rfl) ⟨3572504, by rfl⟩ : syracuseStep 4763339 = 7145009) B7145009
theorem B3174155 : Blo 1409524 3174155 := bstep (se 1 (by rfl) ⟨2380616, by rfl⟩ : syracuseStep 3174155 = 4761233) B4761233
theorem B3174209 : Blo 1409524 3174209 := bstep (se 2 (by rfl) ⟨1190328, by rfl⟩ : syracuseStep 3174209 = 2380657) B2380657
theorem B7237451 : Blo 1409524 7237451 := bstep (se 1 (by rfl) ⟨5428088, by rfl⟩ : syracuseStep 7237451 = 10856177) B10856177
theorem B2543447 : Blo 1409524 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B6025049 : Blo 1409524 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B3051479 : Blo 1409524 3051479 := bstep (se 1 (by rfl) ⟨2288609, by rfl⟩ : syracuseStep 3051479 = 4577219) B4577219
theorem B2936791 : Blo 1409524 2936791 := bstep (se 1 (by rfl) ⟨2202593, by rfl⟩ : syracuseStep 2936791 = 4405187) B4405187
theorem B4763609 : Blo 1409524 4763609 := bstep (se 2 (by rfl) ⟨1786353, by rfl⟩ : syracuseStep 4763609 = 3572707) B3572707
theorem B3174425 : Blo 1409524 3174425 := bstep (se 2 (by rfl) ⟨1190409, by rfl⟩ : syracuseStep 3174425 = 2380819) B2380819
theorem B3174515 : Blo 1409524 3174515 := bstep (se 1 (by rfl) ⟨2380886, by rfl⟩ : syracuseStep 3174515 = 4761773) B4761773
theorem B3174551 : Blo 1409524 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B20336845 : Blo 1409524 20336845 := bstep (se 3 (by rfl) ⟨3813158, by rfl⟩ : syracuseStep 20336845 = 7626317) B7626317
theorem B2380043 : Blo 1409524 2380043 := bstep (se 1 (by rfl) ⟨1785032, by rfl⟩ : syracuseStep 2380043 = 3570065) B3570065
theorem B3174731 : Blo 1409524 3174731 := bstep (se 1 (by rfl) ⟨2381048, by rfl⟩ : syracuseStep 3174731 = 4762097) B4762097
theorem B10309963 : Blo 1409524 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B12874085 : Blo 1409524 12874085 := bstep (se 4 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 12874085 = 2413891) B2413891
theorem B3010945 : Blo 1409524 3010945 := bstep (se 2 (by rfl) ⟨1129104, by rfl⟩ : syracuseStep 3010945 = 2258209) B2258209
theorem B3174785 : Blo 1409524 3174785 := bstep (se 2 (by rfl) ⟨1190544, by rfl⟩ : syracuseStep 3174785 = 2381089) B2381089
theorem B2380171 : Blo 1409524 2380171 := bstep (se 1 (by rfl) ⟨1785128, by rfl⟩ : syracuseStep 2380171 = 3570257) B3570257
theorem B2576843 : Blo 1409524 2576843 := bstep (se 1 (by rfl) ⟨1932632, by rfl⟩ : syracuseStep 2576843 = 3865265) B3865265
theorem B3568151 : Blo 1409524 3568151 := bstep (se 1 (by rfl) ⟨2676113, by rfl⟩ : syracuseStep 3568151 = 5352227) B5352227
theorem B2380313 : Blo 1409524 2380313 := bstep (se 2 (by rfl) ⟨892617, by rfl⟩ : syracuseStep 2380313 = 1785235) B1785235
theorem B1905239 : Blo 1409524 1905239 := bstep (se 1 (by rfl) ⟨1428929, by rfl⟩ : syracuseStep 1905239 = 2857859) B2857859
theorem B3175001 : Blo 1409524 3175001 := bstep (se 2 (by rfl) ⟨1190625, by rfl⟩ : syracuseStep 3175001 = 2381251) B2381251
theorem B2380441 : Blo 1409524 2380441 := bstep (se 2 (by rfl) ⟨892665, by rfl⟩ : syracuseStep 2380441 = 1785331) B1785331
theorem B3175091 : Blo 1409524 3175091 := bstep (se 1 (by rfl) ⟨2381318, by rfl⟩ : syracuseStep 3175091 = 4762637) B4762637
theorem B1585867 : Blo 1409524 1585867 := bstep (se 1 (by rfl) ⟨1189400, by rfl⟩ : syracuseStep 1585867 = 2378801) B2378801
theorem B3175127 : Blo 1409524 3175127 := bstep (se 1 (by rfl) ⟨2381345, by rfl⟩ : syracuseStep 3175127 = 4762691) B4762691
theorem B5354201 : Blo 1409524 5354201 := bstep (se 2 (by rfl) ⟨2007825, by rfl⟩ : syracuseStep 5354201 = 4015651) B4015651
theorem B4018909 : Blo 1409524 4018909 := bstep (se 3 (by rfl) ⟨753545, by rfl⟩ : syracuseStep 4018909 = 1507091) B1507091
theorem B7729937 : Blo 1409524 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B4018967 : Blo 1409524 4018967 := bstep (se 1 (by rfl) ⟨3014225, by rfl⟩ : syracuseStep 4018967 = 6028451) B6028451
theorem B10310435 : Blo 1409524 10310435 := bstep (se 1 (by rfl) ⟨7732826, by rfl⟩ : syracuseStep 10310435 = 15465653) B15465653
theorem B1585975 : Blo 1409524 1585975 := bstep (se 1 (by rfl) ⟨1189481, by rfl⟩ : syracuseStep 1585975 = 2378963) B2378963
theorem B4289345 : Blo 1409524 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B5722969 : Blo 1409524 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B3175307 : Blo 1409524 3175307 := bstep (se 1 (by rfl) ⟨2381480, by rfl⟩ : syracuseStep 3175307 = 4762961) B4762961
theorem B6026177 : Blo 1409524 6026177 := bstep (se 2 (by rfl) ⟨2259816, by rfl⟩ : syracuseStep 6026177 = 4519633) B4519633
theorem B3175361 : Blo 1409524 3175361 := bstep (se 2 (by rfl) ⟨1190760, by rfl⟩ : syracuseStep 3175361 = 2381521) B2381521
theorem B1586155 : Blo 1409524 1586155 := bstep (se 1 (by rfl) ⟨1189616, by rfl⟩ : syracuseStep 1586155 = 2379233) B2379233
theorem B1586263 : Blo 1409524 1586263 := bstep (se 1 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 1586263 = 2379395) B2379395
theorem B3175577 : Blo 1409524 3175577 := bstep (se 2 (by rfl) ⟨1190841, by rfl⟩ : syracuseStep 3175577 = 2381683) B2381683
theorem B3568819 : Blo 1409524 3568819 := bstep (se 1 (by rfl) ⟨2676614, by rfl⟩ : syracuseStep 3568819 = 5353229) B5353229
theorem B2381015 : Blo 1409524 2381015 := bstep (se 1 (by rfl) ⟨1785761, by rfl⟩ : syracuseStep 2381015 = 3571523) B3571523
theorem B6436061 : Blo 1409524 6436061 := bstep (se 3 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 6436061 = 2413523) B2413523
theorem B3175667 : Blo 1409524 3175667 := bstep (se 1 (by rfl) ⟨2381750, by rfl⟩ : syracuseStep 3175667 = 4763501) B4763501
theorem B1586443 : Blo 1409524 1586443 := bstep (se 1 (by rfl) ⟨1189832, by rfl⟩ : syracuseStep 1586443 = 2379665) B2379665
theorem B1905931 : Blo 1409524 1905931 := bstep (se 1 (by rfl) ⟨1429448, by rfl⟩ : syracuseStep 1905931 = 2858897) B2858897
theorem B3175703 : Blo 1409524 3175703 := bstep (se 1 (by rfl) ⟨2381777, by rfl⟩ : syracuseStep 3175703 = 4763555) B4763555
theorem B3568961 : Blo 1409524 3568961 := bstep (se 2 (by rfl) ⟨1338360, by rfl⟩ : syracuseStep 3568961 = 2676721) B2676721
theorem B2381143 : Blo 1409524 2381143 := bstep (se 1 (by rfl) ⟨1785857, by rfl⟩ : syracuseStep 2381143 = 3571715) B3571715
theorem B1586551 : Blo 1409524 1586551 := bstep (se 1 (by rfl) ⟨1189913, by rfl⟩ : syracuseStep 1586551 = 2379827) B2379827
theorem B7624115 : Blo 1409524 7624115 := bstep (se 1 (by rfl) ⟨5718086, by rfl⟩ : syracuseStep 7624115 = 11436173) B11436173
theorem B3175883 : Blo 1409524 3175883 := bstep (se 1 (by rfl) ⟨2381912, by rfl⟩ : syracuseStep 3175883 = 4763825) B4763825
theorem B20600281 : Blo 1409524 20600281 := bstep (se 2 (by rfl) ⟨7725105, by rfl⟩ : syracuseStep 20600281 = 15450211) B15450211
theorem B2676235 : Blo 1409524 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B1586731 : Blo 1409524 1586731 := bstep (se 1 (by rfl) ⟨1190048, by rfl⟩ : syracuseStep 1586731 = 2380097) B2380097
theorem B2676311 : Blo 1409524 2676311 := bstep (se 1 (by rfl) ⟨2007233, by rfl⟩ : syracuseStep 2676311 = 4014467) B4014467
theorem B1586839 : Blo 1409524 1586839 := bstep (se 1 (by rfl) ⟨1190129, by rfl⟩ : syracuseStep 1586839 = 2380259) B2380259
theorem B3815063 : Blo 1409524 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B5150411 : Blo 1409524 5150411 := bstep (se 1 (by rfl) ⟨3862808, by rfl⟩ : syracuseStep 5150411 = 7725617) B7725617
theorem B73266893 : Blo 1409524 73266893 := bstep (se 3 (by rfl) ⟨13737542, by rfl⟩ : syracuseStep 73266893 = 27475085) B27475085
theorem B10712897 : Blo 1409524 10712897 := bstep (se 2 (by rfl) ⟨4017336, by rfl⟩ : syracuseStep 10712897 = 8034673) B8034673
theorem B1587019 : Blo 1409524 1587019 := bstep (se 1 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 1587019 = 2380529) B2380529
theorem B18315109 : Blo 1409524 18315109 := bstep (se 4 (by rfl) ⟨1717041, by rfl⟩ : syracuseStep 18315109 = 3434083) B3434083
theorem B3012491 : Blo 1409524 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B4757399 : Blo 1409524 4757399 := bstep (se 1 (by rfl) ⟨3568049, by rfl⟩ : syracuseStep 4757399 = 7136099) B7136099
theorem B1587127 : Blo 1409524 1587127 := bstep (se 1 (by rfl) ⟨1190345, by rfl⟩ : syracuseStep 1587127 = 2380691) B2380691
theorem B2381771 : Blo 1409524 2381771 := bstep (se 1 (by rfl) ⟨1786328, by rfl⟩ : syracuseStep 2381771 = 3572657) B3572657
theorem B4290583 : Blo 1409524 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B2381899 : Blo 1409524 2381899 := bstep (se 1 (by rfl) ⟨1786424, by rfl⟩ : syracuseStep 2381899 = 3572849) B3572849
theorem B1587307 : Blo 1409524 1587307 := bstep (se 1 (by rfl) ⟨1190480, by rfl⟩ : syracuseStep 1587307 = 2380961) B2380961
theorem B1587415 : Blo 1409524 1587415 := bstep (se 1 (by rfl) ⟨1190561, by rfl⟩ : syracuseStep 1587415 = 2381123) B2381123
theorem B9042137 : Blo 1409524 9042137 := bstep (se 2 (by rfl) ⟨3390801, by rfl⟩ : syracuseStep 9042137 = 6781603) B6781603
theorem B2676979 : Blo 1409524 2676979 := bstep (se 1 (by rfl) ⟨2007734, by rfl⟩ : syracuseStep 2676979 = 4015469) B4015469
theorem B5355827 : Blo 1409524 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B16062785 : Blo 1409524 16062785 := bstep (se 2 (by rfl) ⟨6023544, by rfl⟩ : syracuseStep 16062785 = 12047089) B12047089
theorem B5355841 : Blo 1409524 5355841 := bstep (se 2 (by rfl) ⟨2008440, by rfl⟩ : syracuseStep 5355841 = 4016881) B4016881
theorem B1587595 : Blo 1409524 1587595 := bstep (se 1 (by rfl) ⟨1190696, by rfl⟩ : syracuseStep 1587595 = 2381393) B2381393
theorem B4757939 : Blo 1409524 4757939 := bstep (se 1 (by rfl) ⟨3568454, by rfl⟩ : syracuseStep 4757939 = 7136909) B7136909
theorem B2677207 : Blo 1409524 2677207 := bstep (se 1 (by rfl) ⟨2007905, by rfl⟩ : syracuseStep 2677207 = 4015811) B4015811
theorem B22886873 : Blo 1409524 22886873 := bstep (se 2 (by rfl) ⟨8582577, by rfl⟩ : syracuseStep 22886873 = 17165155) B17165155
theorem B1587703 : Blo 1409524 1587703 := bstep (se 1 (by rfl) ⟨1190777, by rfl⟩ : syracuseStep 1587703 = 2381555) B2381555
theorem B11303459 : Blo 1409524 11303459 := bstep (se 1 (by rfl) ⟨8477594, by rfl⟩ : syracuseStep 11303459 = 16955189) B16955189
theorem B3570227 : Blo 1409524 3570227 := bstep (se 1 (by rfl) ⟨2677670, by rfl⟩ : syracuseStep 3570227 = 5355341) B5355341
theorem B2677313 : Blo 1409524 2677313 := bstep (se 2 (by rfl) ⟨1003992, by rfl⟩ : syracuseStep 2677313 = 2007985) B2007985
theorem B6027851 : Blo 1409524 6027851 := bstep (se 1 (by rfl) ⟨4520888, by rfl⟩ : syracuseStep 6027851 = 9041777) B9041777
theorem B8034947 : Blo 1409524 8034947 := bstep (se 1 (by rfl) ⟨6026210, by rfl⟩ : syracuseStep 8034947 = 12052421) B12052421
theorem B1587883 : Blo 1409524 1587883 := bstep (se 1 (by rfl) ⟨1190912, by rfl⟩ : syracuseStep 1587883 = 2381825) B2381825
theorem B12049073 : Blo 1409524 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B4758209 : Blo 1409524 4758209 := bstep (se 2 (by rfl) ⟨1784328, by rfl⟩ : syracuseStep 4758209 = 3568657) B3568657
theorem B2677465 : Blo 1409524 2677465 := bstep (se 2 (by rfl) ⟨1004049, by rfl⟩ : syracuseStep 2677465 = 2008099) B2008099
theorem B3013337 : Blo 1409524 3013337 := bstep (se 2 (by rfl) ⟨1130001, by rfl⟩ : syracuseStep 3013337 = 2260003) B2260003
theorem B1784587 : Blo 1409524 1784587 := bstep (se 1 (by rfl) ⟨1338440, by rfl⟩ : syracuseStep 1784587 = 2676881) B2676881
theorem B2857793 : Blo 1409524 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B4070209 : Blo 1409524 4070209 := bstep (se 2 (by rfl) ⟨1526328, by rfl⟩ : syracuseStep 4070209 = 3052657) B3052657
theorem B2898841 : Blo 1409524 2898841 := bstep (se 2 (by rfl) ⟨1087065, by rfl⟩ : syracuseStep 2898841 = 2174131) B2174131
theorem B7142417 : Blo 1409524 7142417 := bstep (se 2 (by rfl) ⟨2678406, by rfl⟩ : syracuseStep 7142417 = 5356813) B5356813
theorem B1784855 : Blo 1409524 1784855 := bstep (se 1 (by rfl) ⟨1338641, by rfl⟩ : syracuseStep 1784855 = 2677283) B2677283
theorem B3570763 : Blo 1409524 3570763 := bstep (se 1 (by rfl) ⟨2678072, by rfl⟩ : syracuseStep 3570763 = 5356145) B5356145
theorem B5717081 : Blo 1409524 5717081 := bstep (se 2 (by rfl) ⟨2143905, by rfl⟩ : syracuseStep 5717081 = 4287811) B4287811
theorem B5872733 : Blo 1409524 5872733 := bstep (se 3 (by rfl) ⟨1101137, by rfl⟩ : syracuseStep 5872733 = 2202275) B2202275
theorem B5717143 : Blo 1409524 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B7142579 : Blo 1409524 7142579 := bstep (se 1 (by rfl) ⟨5356934, by rfl⟩ : syracuseStep 7142579 = 10713869) B10713869
theorem B3570905 : Blo 1409524 3570905 := bstep (se 2 (by rfl) ⟨1339089, by rfl⟩ : syracuseStep 3570905 = 2678179) B2678179
theorem B4758749 : Blo 1409524 4758749 := bstep (se 3 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 4758749 = 1784531) B1784531
theorem B1506647 : Blo 1409524 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B10165655 : Blo 1409524 10165655 := bstep (se 1 (by rfl) ⟨7624241, by rfl⟩ : syracuseStep 10165655 = 15248483) B15248483
theorem B65158613 : Blo 1409524 65158613 := bstep (se 7 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 65158613 = 1527155) B1527155
theorem B9649625 : Blo 1409524 9649625 := bstep (se 2 (by rfl) ⟨3618609, by rfl⟩ : syracuseStep 9649625 = 7237219) B7237219
theorem B3014131 : Blo 1409524 3014131 := bstep (se 1 (by rfl) ⟨2260598, by rfl⟩ : syracuseStep 3014131 = 4521197) B4521197
theorem B1785559 : Blo 1409524 1785559 := bstep (se 1 (by rfl) ⟨1339169, by rfl⟩ : syracuseStep 1785559 = 2678339) B2678339
theorem B10714841 : Blo 1409524 10714841 := bstep (se 2 (by rfl) ⟨4018065, by rfl⟩ : syracuseStep 10714841 = 8036131) B8036131
theorem B5578571 : Blo 1409524 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B6029149 : Blo 1409524 6029149 := bstep (se 3 (by rfl) ⟨1130465, by rfl⟩ : syracuseStep 6029149 = 2260931) B2260931
theorem B18087857 : Blo 1409524 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B2678771 : Blo 1409524 2678771 := bstep (se 1 (by rfl) ⟨2009078, by rfl⟩ : syracuseStep 2678771 = 4018157) B4018157
theorem B4759613 : Blo 1409524 4759613 := bstep (se 3 (by rfl) ⟨892427, by rfl⟩ : syracuseStep 4759613 = 1784855) B1784855
theorem B3571847 : Blo 1409524 3571847 := bstep (se 1 (by rfl) ⟨2678885, by rfl⟩ : syracuseStep 3571847 = 5357771) B5357771
theorem B3571897 : Blo 1409524 3571897 := bstep (se 2 (by rfl) ⟨1339461, by rfl⟩ : syracuseStep 3571897 = 2678923) B2678923
theorem B2678969 : Blo 1409524 2678969 := bstep (se 2 (by rfl) ⟨1004613, by rfl⟩ : syracuseStep 2678969 = 2009227) B2009227
theorem B11436233 : Blo 1409524 11436233 := bstep (se 2 (by rfl) ⟨4288587, by rfl⟩ : syracuseStep 11436233 = 8577175) B8577175
theorem B15466697 : Blo 1409524 15466697 := bstep (se 2 (by rfl) ⟨5800011, by rfl⟩ : syracuseStep 15466697 = 11600023) B11600023
theorem B7627009 : Blo 1409524 7627009 := bstep (se 2 (by rfl) ⟨2860128, by rfl⟩ : syracuseStep 7627009 = 5720257) B5720257
theorem B27115793 : Blo 1409524 27115793 := bstep (se 2 (by rfl) ⟨10168422, by rfl⟩ : syracuseStep 27115793 = 20336845) B20336845
theorem B7143713 : Blo 1409524 7143713 := bstep (se 2 (by rfl) ⟨2678892, by rfl⟩ : syracuseStep 7143713 = 5357785) B5357785
theorem B13746617 : Blo 1409524 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B4014593 : Blo 1409524 4014593 := bstep (se 2 (by rfl) ⟨1505472, by rfl⟩ : syracuseStep 4014593 = 3010945) B3010945
theorem B1409543 : Blo 1409524 1409543 := bstep (se 1 (by rfl) ⟨1057157, by rfl⟩ : syracuseStep 1409543 = 2114315) B2114315
theorem B5153291 : Blo 1409524 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B1409551 : Blo 1409524 1409551 := bstep (se 1 (by rfl) ⟨1057163, by rfl⟩ : syracuseStep 1409551 = 2114327) B2114327
theorem B2679311 : Blo 1409524 2679311 := bstep (se 1 (by rfl) ⟨2009483, by rfl⟩ : syracuseStep 2679311 = 4018967) B4018967
theorem B6873623 : Blo 1409524 6873623 := bstep (se 1 (by rfl) ⟨5155217, by rfl⟩ : syracuseStep 6873623 = 10310435) B10310435
theorem B7733789 : Blo 1409524 7733789 := bstep (se 3 (by rfl) ⟨1450085, by rfl⟩ : syracuseStep 7733789 = 2900171) B2900171
theorem B2859563 : Blo 1409524 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B1409595 : Blo 1409524 1409595 := bstep (se 1 (by rfl) ⟨1057196, by rfl⟩ : syracuseStep 1409595 = 2114393) B2114393
theorem B1409671 : Blo 1409524 1409671 := bstep (se 1 (by rfl) ⟨1057253, by rfl⟩ : syracuseStep 1409671 = 2114507) B2114507
theorem B1409679 : Blo 1409524 1409679 := bstep (se 1 (by rfl) ⟨1057259, by rfl⟩ : syracuseStep 1409679 = 2114519) B2114519
theorem B30483125 : Blo 1409524 30483125 := bstep (se 5 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 30483125 = 2857793) B2857793
theorem B1409723 : Blo 1409524 1409723 := bstep (se 1 (by rfl) ⟨1057292, by rfl⟩ : syracuseStep 1409723 = 2114585) B2114585
theorem B7135937 : Blo 1409524 7135937 := bstep (se 2 (by rfl) ⟨2675976, by rfl⟩ : syracuseStep 7135937 = 5351953) B5351953
theorem B1409799 : Blo 1409524 1409799 := bstep (se 1 (by rfl) ⟨1057349, by rfl⟩ : syracuseStep 1409799 = 2114699) B2114699
theorem B1409807 : Blo 1409524 1409807 := bstep (se 1 (by rfl) ⟨1057355, by rfl⟩ : syracuseStep 1409807 = 2114711) B2114711
theorem B3572495 : Blo 1409524 3572495 := bstep (se 1 (by rfl) ⟨2679371, by rfl⟩ : syracuseStep 3572495 = 5358743) B5358743
theorem B2114363 : Blo 1409524 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B1409851 : Blo 1409524 1409851 := bstep (se 1 (by rfl) ⟨1057388, by rfl⟩ : syracuseStep 1409851 = 2114777) B2114777
theorem B2114423 : Blo 1409524 2114423 := bstep (se 1 (by rfl) ⟨1585817, by rfl⟩ : syracuseStep 2114423 = 3171635) B3171635
theorem B1409927 : Blo 1409524 1409927 := bstep (se 1 (by rfl) ⟨1057445, by rfl⟩ : syracuseStep 1409927 = 2114891) B2114891
theorem B2114447 : Blo 1409524 2114447 := bstep (se 1 (by rfl) ⟨1585835, by rfl⟩ : syracuseStep 2114447 = 3171671) B3171671
theorem B1409935 : Blo 1409524 1409935 := bstep (se 1 (by rfl) ⟨1057451, by rfl⟩ : syracuseStep 1409935 = 2114903) B2114903
theorem B2114489 : Blo 1409524 2114489 := bstep (se 2 (by rfl) ⟨792933, by rfl⟩ : syracuseStep 2114489 = 1585867) B1585867
theorem B1409979 : Blo 1409524 1409979 := bstep (se 1 (by rfl) ⟨1057484, by rfl⟩ : syracuseStep 1409979 = 2114969) B2114969
theorem B5358545 : Blo 1409524 5358545 := bstep (se 2 (by rfl) ⟨2009454, by rfl⟩ : syracuseStep 5358545 = 4018909) B4018909
theorem B2114567 : Blo 1409524 2114567 := bstep (se 1 (by rfl) ⟨1585925, by rfl⟩ : syracuseStep 2114567 = 3171851) B3171851
theorem B1410055 : Blo 1409524 1410055 := bstep (se 1 (by rfl) ⟨1057541, by rfl⟩ : syracuseStep 1410055 = 2115083) B2115083
theorem B1410063 : Blo 1409524 1410063 := bstep (se 1 (by rfl) ⟨1057547, by rfl⟩ : syracuseStep 1410063 = 2115095) B2115095
theorem B2114603 : Blo 1409524 2114603 := bstep (se 1 (by rfl) ⟨1585952, by rfl⟩ : syracuseStep 2114603 = 3171905) B3171905
theorem B1410107 : Blo 1409524 1410107 := bstep (se 1 (by rfl) ⟨1057580, by rfl⟩ : syracuseStep 1410107 = 2115161) B2115161
theorem B2114633 : Blo 1409524 2114633 := bstep (se 2 (by rfl) ⟨792987, by rfl⟩ : syracuseStep 2114633 = 1585975) B1585975
theorem B3433607 : Blo 1409524 3433607 := bstep (se 1 (by rfl) ⟨2575205, by rfl⟩ : syracuseStep 3433607 = 5150411) B5150411
theorem B1410183 : Blo 1409524 1410183 := bstep (se 1 (by rfl) ⟨1057637, by rfl⟩ : syracuseStep 1410183 = 2115275) B2115275
theorem B1410191 : Blo 1409524 1410191 := bstep (se 1 (by rfl) ⟨1057643, by rfl⟩ : syracuseStep 1410191 = 2115287) B2115287
theorem B2114747 : Blo 1409524 2114747 := bstep (se 1 (by rfl) ⟨1586060, by rfl⟩ : syracuseStep 2114747 = 3172121) B3172121
theorem B1410235 : Blo 1409524 1410235 := bstep (se 1 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 1410235 = 2115353) B2115353
theorem B25732333 : Blo 1409524 25732333 := bstep (se 3 (by rfl) ⟨4824812, by rfl⟩ : syracuseStep 25732333 = 9649625) B9649625
theorem B7144685 : Blo 1409524 7144685 := bstep (se 3 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 7144685 = 2679257) B2679257
theorem B2114807 : Blo 1409524 2114807 := bstep (se 1 (by rfl) ⟨1586105, by rfl⟩ : syracuseStep 2114807 = 3172211) B3172211
theorem B1410311 : Blo 1409524 1410311 := bstep (se 1 (by rfl) ⟨1057733, by rfl⟩ : syracuseStep 1410311 = 2115467) B2115467
theorem B2008327 : Blo 1409524 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B3171599 : Blo 1409524 3171599 := bstep (se 1 (by rfl) ⟨2378699, by rfl⟩ : syracuseStep 3171599 = 4757399) B4757399
theorem B2114831 : Blo 1409524 2114831 := bstep (se 1 (by rfl) ⟨1586123, by rfl⟩ : syracuseStep 2114831 = 3172247) B3172247
theorem B1410319 : Blo 1409524 1410319 := bstep (se 1 (by rfl) ⟨1057739, by rfl⟩ : syracuseStep 1410319 = 2115479) B2115479
theorem B3171617 : Blo 1409524 3171617 := bstep (se 2 (by rfl) ⟨1189356, by rfl⟩ : syracuseStep 3171617 = 2378713) B2378713
theorem B2114873 : Blo 1409524 2114873 := bstep (se 2 (by rfl) ⟨793077, by rfl⟩ : syracuseStep 2114873 = 1586155) B1586155
theorem B1410363 : Blo 1409524 1410363 := bstep (se 1 (by rfl) ⟨1057772, by rfl⟩ : syracuseStep 1410363 = 2115545) B2115545
theorem B11912507 : Blo 1409524 11912507 := bstep (se 1 (by rfl) ⟨8934380, by rfl⟩ : syracuseStep 11912507 = 17868761) B17868761
theorem B2114951 : Blo 1409524 2114951 := bstep (se 1 (by rfl) ⟨1586213, by rfl⟩ : syracuseStep 2114951 = 3172427) B3172427
theorem B1410439 : Blo 1409524 1410439 := bstep (se 1 (by rfl) ⟨1057829, by rfl⟩ : syracuseStep 1410439 = 2115659) B2115659
theorem B1410447 : Blo 1409524 1410447 := bstep (se 1 (by rfl) ⟨1057835, by rfl⟩ : syracuseStep 1410447 = 2115671) B2115671
theorem B2114987 : Blo 1409524 2114987 := bstep (se 1 (by rfl) ⟨1586240, by rfl⟩ : syracuseStep 2114987 = 3172481) B3172481
theorem B1410491 : Blo 1409524 1410491 := bstep (se 1 (by rfl) ⟨1057868, by rfl⟩ : syracuseStep 1410491 = 2115737) B2115737
theorem B4761017 : Blo 1409524 4761017 := bstep (se 2 (by rfl) ⟨1785381, by rfl⟩ : syracuseStep 4761017 = 3570763) B3570763
theorem B2115017 : Blo 1409524 2115017 := bstep (se 2 (by rfl) ⟨793131, by rfl⟩ : syracuseStep 2115017 = 1586263) B1586263
theorem B1410567 : Blo 1409524 1410567 := bstep (se 1 (by rfl) ⟨1057925, by rfl⟩ : syracuseStep 1410567 = 2115851) B2115851
theorem B1410575 : Blo 1409524 1410575 := bstep (se 1 (by rfl) ⟨1057931, by rfl⟩ : syracuseStep 1410575 = 2115863) B2115863
theorem B10708523 : Blo 1409524 10708523 := bstep (se 1 (by rfl) ⟨8031392, by rfl⟩ : syracuseStep 10708523 = 16062785) B16062785
theorem B2115131 : Blo 1409524 2115131 := bstep (se 1 (by rfl) ⟨1586348, by rfl⟩ : syracuseStep 2115131 = 3172697) B3172697
theorem B1410619 : Blo 1409524 1410619 := bstep (se 1 (by rfl) ⟨1057964, by rfl⟩ : syracuseStep 1410619 = 2115929) B2115929
theorem B5080637 : Blo 1409524 5080637 := bstep (se 3 (by rfl) ⟨952619, by rfl⟩ : syracuseStep 5080637 = 1905239) B1905239
theorem B3171959 : Blo 1409524 3171959 := bstep (se 1 (by rfl) ⟨2378969, by rfl⟩ : syracuseStep 3171959 = 4757939) B4757939
theorem B2115191 : Blo 1409524 2115191 := bstep (se 1 (by rfl) ⟨1586393, by rfl⟩ : syracuseStep 2115191 = 3172787) B3172787
theorem B1410695 : Blo 1409524 1410695 := bstep (se 1 (by rfl) ⟨1058021, by rfl⟩ : syracuseStep 1410695 = 2116043) B2116043
theorem B2115215 : Blo 1409524 2115215 := bstep (se 1 (by rfl) ⟨1586411, by rfl⟩ : syracuseStep 2115215 = 3172823) B3172823
theorem B1410703 : Blo 1409524 1410703 := bstep (se 1 (by rfl) ⟨1058027, by rfl⟩ : syracuseStep 1410703 = 2116055) B2116055
theorem B2115257 : Blo 1409524 2115257 := bstep (se 2 (by rfl) ⟨793221, by rfl⟩ : syracuseStep 2115257 = 1586443) B1586443
theorem B2541241 : Blo 1409524 2541241 := bstep (se 2 (by rfl) ⟨952965, by rfl⟩ : syracuseStep 2541241 = 1905931) B1905931
theorem B1410747 : Blo 1409524 1410747 := bstep (se 1 (by rfl) ⟨1058060, by rfl⟩ : syracuseStep 1410747 = 2116121) B2116121
theorem B2115335 : Blo 1409524 2115335 := bstep (se 1 (by rfl) ⟨1586501, by rfl⟩ : syracuseStep 2115335 = 3173003) B3173003
theorem B1410823 : Blo 1409524 1410823 := bstep (se 1 (by rfl) ⟨1058117, by rfl⟩ : syracuseStep 1410823 = 2116235) B2116235
theorem B1410831 : Blo 1409524 1410831 := bstep (se 1 (by rfl) ⟨1058123, by rfl⟩ : syracuseStep 1410831 = 2116247) B2116247
theorem B3172139 : Blo 1409524 3172139 := bstep (se 1 (by rfl) ⟨2379104, by rfl⟩ : syracuseStep 3172139 = 4758209) B4758209
theorem B2115371 : Blo 1409524 2115371 := bstep (se 1 (by rfl) ⟨1586528, by rfl⟩ : syracuseStep 2115371 = 3173057) B3173057
theorem B1410875 : Blo 1409524 1410875 := bstep (se 1 (by rfl) ⟨1058156, by rfl⟩ : syracuseStep 1410875 = 2116313) B2116313
theorem B2008891 : Blo 1409524 2008891 := bstep (se 1 (by rfl) ⟨1506668, by rfl⟩ : syracuseStep 2008891 = 3013337) B3013337
theorem B2115401 : Blo 1409524 2115401 := bstep (se 2 (by rfl) ⟨793275, by rfl⟩ : syracuseStep 2115401 = 1586551) B1586551
theorem B1410951 : Blo 1409524 1410951 := bstep (se 1 (by rfl) ⟨1058213, by rfl⟩ : syracuseStep 1410951 = 2116427) B2116427
theorem B1410959 : Blo 1409524 1410959 := bstep (se 1 (by rfl) ⟨1058219, by rfl⟩ : syracuseStep 1410959 = 2116439) B2116439
theorem B2115515 : Blo 1409524 2115515 := bstep (se 1 (by rfl) ⟨1586636, by rfl⟩ : syracuseStep 2115515 = 3173273) B3173273
theorem B1411003 : Blo 1409524 1411003 := bstep (se 1 (by rfl) ⟨1058252, by rfl⟩ : syracuseStep 1411003 = 2116505) B2116505
theorem B7137233 : Blo 1409524 7137233 := bstep (se 2 (by rfl) ⟨2676462, by rfl⟩ : syracuseStep 7137233 = 5352925) B5352925
theorem B2115575 : Blo 1409524 2115575 := bstep (se 1 (by rfl) ⟨1586681, by rfl⟩ : syracuseStep 2115575 = 3173363) B3173363
theorem B1411079 : Blo 1409524 1411079 := bstep (se 1 (by rfl) ⟨1058309, by rfl⟩ : syracuseStep 1411079 = 2116619) B2116619
theorem B4761611 : Blo 1409524 4761611 := bstep (se 1 (by rfl) ⟨3571208, by rfl⟩ : syracuseStep 4761611 = 7142417) B7142417
theorem B2115599 : Blo 1409524 2115599 := bstep (se 1 (by rfl) ⟨1586699, by rfl⟩ : syracuseStep 2115599 = 3173399) B3173399
theorem B1411087 : Blo 1409524 1411087 := bstep (se 1 (by rfl) ⟨1058315, by rfl⟩ : syracuseStep 1411087 = 2116631) B2116631
theorem B7145495 : Blo 1409524 7145495 := bstep (se 1 (by rfl) ⟨5359121, by rfl⟩ : syracuseStep 7145495 = 10718243) B10718243
theorem B2115641 : Blo 1409524 2115641 := bstep (se 2 (by rfl) ⟨793365, by rfl⟩ : syracuseStep 2115641 = 1586731) B1586731
theorem B3811387 : Blo 1409524 3811387 := bstep (se 1 (by rfl) ⟨2858540, by rfl⟩ : syracuseStep 3811387 = 5717081) B5717081
theorem B1411131 : Blo 1409524 1411131 := bstep (se 1 (by rfl) ⟨1058348, by rfl⟩ : syracuseStep 1411131 = 2116697) B2116697
theorem B10717271 : Blo 1409524 10717271 := bstep (se 1 (by rfl) ⟨8037953, by rfl⟩ : syracuseStep 10717271 = 16075907) B16075907
theorem B4016243 : Blo 1409524 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B4761719 : Blo 1409524 4761719 := bstep (se 1 (by rfl) ⟨3571289, by rfl⟩ : syracuseStep 4761719 = 7142579) B7142579
theorem B2115719 : Blo 1409524 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B1411207 : Blo 1409524 1411207 := bstep (se 1 (by rfl) ⟨1058405, by rfl⟩ : syracuseStep 1411207 = 2116811) B2116811
theorem B1411215 : Blo 1409524 1411215 := bstep (se 1 (by rfl) ⟨1058411, by rfl⟩ : syracuseStep 1411215 = 2116823) B2116823
theorem B3172499 : Blo 1409524 3172499 := bstep (se 1 (by rfl) ⟨2379374, by rfl⟩ : syracuseStep 3172499 = 4758749) B4758749
theorem B2115755 : Blo 1409524 2115755 := bstep (se 1 (by rfl) ⟨1586816, by rfl⟩ : syracuseStep 2115755 = 3173633) B3173633
theorem B1411259 : Blo 1409524 1411259 := bstep (se 1 (by rfl) ⟨1058444, by rfl⟩ : syracuseStep 1411259 = 2116889) B2116889
theorem B3172553 : Blo 1409524 3172553 := bstep (se 2 (by rfl) ⟨1189707, by rfl⟩ : syracuseStep 3172553 = 2379415) B2379415
theorem B2115785 : Blo 1409524 2115785 := bstep (se 2 (by rfl) ⟨793419, by rfl⟩ : syracuseStep 2115785 = 1586839) B1586839
theorem B1411335 : Blo 1409524 1411335 := bstep (se 1 (by rfl) ⟨1058501, by rfl⟩ : syracuseStep 1411335 = 2117003) B2117003
theorem B6777103 : Blo 1409524 6777103 := bstep (se 1 (by rfl) ⟨5082827, by rfl⟩ : syracuseStep 6777103 = 10165655) B10165655
theorem B1411343 : Blo 1409524 1411343 := bstep (se 1 (by rfl) ⟨1058507, by rfl⟩ : syracuseStep 1411343 = 2117015) B2117015
theorem B2115899 : Blo 1409524 2115899 := bstep (se 1 (by rfl) ⟨1586924, by rfl⟩ : syracuseStep 2115899 = 3173849) B3173849
theorem B1411387 : Blo 1409524 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B2115959 : Blo 1409524 2115959 := bstep (se 1 (by rfl) ⟨1586969, by rfl⟩ : syracuseStep 2115959 = 3173939) B3173939
theorem B1411463 : Blo 1409524 1411463 := bstep (se 1 (by rfl) ⟨1058597, by rfl⟩ : syracuseStep 1411463 = 2117195) B2117195
theorem B2115983 : Blo 1409524 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B1411471 : Blo 1409524 1411471 := bstep (se 1 (by rfl) ⟨1058603, by rfl⟩ : syracuseStep 1411471 = 2117207) B2117207
theorem B13552019 : Blo 1409524 13552019 := bstep (se 1 (by rfl) ⟨10164014, by rfl⟩ : syracuseStep 13552019 = 20328029) B20328029
theorem B2116025 : Blo 1409524 2116025 := bstep (se 2 (by rfl) ⟨793509, by rfl⟩ : syracuseStep 2116025 = 1587019) B1587019
theorem B1411515 : Blo 1409524 1411515 := bstep (se 1 (by rfl) ⟨1058636, by rfl⟩ : syracuseStep 1411515 = 2117273) B2117273
theorem B8038865 : Blo 1409524 8038865 := bstep (se 2 (by rfl) ⟨3014574, by rfl⟩ : syracuseStep 8038865 = 6029149) B6029149
theorem B2116103 : Blo 1409524 2116103 := bstep (se 1 (by rfl) ⟨1587077, by rfl⟩ : syracuseStep 2116103 = 3174155) B3174155
theorem B2116139 : Blo 1409524 2116139 := bstep (se 1 (by rfl) ⟨1587104, by rfl⟩ : syracuseStep 2116139 = 3174209) B3174209
theorem B4016699 : Blo 1409524 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B2116169 : Blo 1409524 2116169 := bstep (se 2 (by rfl) ⟨793563, by rfl⟩ : syracuseStep 2116169 = 1587127) B1587127
theorem B2034319 : Blo 1409524 2034319 := bstep (se 1 (by rfl) ⟨1525739, by rfl⟩ : syracuseStep 2034319 = 3051479) B3051479
theorem B2116283 : Blo 1409524 2116283 := bstep (se 1 (by rfl) ⟨1587212, by rfl⟩ : syracuseStep 2116283 = 3174425) B3174425
theorem B5720777 : Blo 1409524 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B4762313 : Blo 1409524 4762313 := bstep (se 2 (by rfl) ⟨1785867, by rfl⟩ : syracuseStep 4762313 = 3571735) B3571735
theorem B2116343 : Blo 1409524 2116343 := bstep (se 1 (by rfl) ⟨1587257, by rfl⟩ : syracuseStep 2116343 = 3174515) B3174515
theorem B2116367 : Blo 1409524 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B28945187 : Blo 1409524 28945187 := bstep (se 1 (by rfl) ⟨21708890, by rfl⟩ : syracuseStep 28945187 = 43417781) B43417781
theorem B2116409 : Blo 1409524 2116409 := bstep (se 2 (by rfl) ⟨793653, by rfl⟩ : syracuseStep 2116409 = 1587307) B1587307
theorem B3173255 : Blo 1409524 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B2116487 : Blo 1409524 2116487 := bstep (se 1 (by rfl) ⟨1587365, by rfl⟩ : syracuseStep 2116487 = 3174731) B3174731
theorem B2116523 : Blo 1409524 2116523 := bstep (se 1 (by rfl) ⟨1587392, by rfl⟩ : syracuseStep 2116523 = 3174785) B3174785
theorem B2116553 : Blo 1409524 2116553 := bstep (se 2 (by rfl) ⟨793707, by rfl⟩ : syracuseStep 2116553 = 1587415) B1587415
theorem B2378767 : Blo 1409524 2378767 := bstep (se 1 (by rfl) ⟨1784075, by rfl⟩ : syracuseStep 2378767 = 3568151) B3568151
theorem B3173435 : Blo 1409524 3173435 := bstep (se 1 (by rfl) ⟨2380076, by rfl⟩ : syracuseStep 3173435 = 4760153) B4760153
theorem B2116667 : Blo 1409524 2116667 := bstep (se 1 (by rfl) ⟨1587500, by rfl⟩ : syracuseStep 2116667 = 3175001) B3175001
theorem B2116727 : Blo 1409524 2116727 := bstep (se 1 (by rfl) ⟨1587545, by rfl⟩ : syracuseStep 2116727 = 3175091) B3175091
theorem B2116751 : Blo 1409524 2116751 := bstep (se 1 (by rfl) ⟨1587563, by rfl⟩ : syracuseStep 2116751 = 3175127) B3175127
theorem B3173561 : Blo 1409524 3173561 := bstep (se 2 (by rfl) ⟨1190085, by rfl⟩ : syracuseStep 3173561 = 2380171) B2380171
theorem B2116793 : Blo 1409524 2116793 := bstep (se 2 (by rfl) ⟨793797, by rfl⟩ : syracuseStep 2116793 = 1587595) B1587595
theorem B2116871 : Blo 1409524 2116871 := bstep (se 1 (by rfl) ⟨1587653, by rfl⟩ : syracuseStep 2116871 = 3175307) B3175307
theorem B4017451 : Blo 1409524 4017451 := bstep (se 1 (by rfl) ⟨3013088, by rfl⟩ : syracuseStep 4017451 = 6026177) B6026177
theorem B2116907 : Blo 1409524 2116907 := bstep (se 1 (by rfl) ⟨1587680, by rfl⟩ : syracuseStep 2116907 = 3175361) B3175361
theorem B2116937 : Blo 1409524 2116937 := bstep (se 2 (by rfl) ⟨793851, by rfl⟩ : syracuseStep 2116937 = 1587703) B1587703
theorem B4763015 : Blo 1409524 4763015 := bstep (se 1 (by rfl) ⟨3572261, by rfl⟩ : syracuseStep 4763015 = 7144523) B7144523
theorem B2117051 : Blo 1409524 2117051 := bstep (se 1 (by rfl) ⟨1587788, by rfl⟩ : syracuseStep 2117051 = 3175577) B3175577
theorem B16059869 : Blo 1409524 16059869 := bstep (se 3 (by rfl) ⟨3011225, by rfl⟩ : syracuseStep 16059869 = 6022451) B6022451
theorem B6778333 : Blo 1409524 6778333 := bstep (se 3 (by rfl) ⟨1270937, by rfl⟩ : syracuseStep 6778333 = 2541875) B2541875
theorem B2117111 : Blo 1409524 2117111 := bstep (se 1 (by rfl) ⟨1587833, by rfl⟩ : syracuseStep 2117111 = 3175667) B3175667
theorem B3173903 : Blo 1409524 3173903 := bstep (se 1 (by rfl) ⟨2380427, by rfl⟩ : syracuseStep 3173903 = 4760855) B4760855
theorem B2117135 : Blo 1409524 2117135 := bstep (se 1 (by rfl) ⟨1587851, by rfl⟩ : syracuseStep 2117135 = 3175703) B3175703
theorem B3173921 : Blo 1409524 3173921 := bstep (se 2 (by rfl) ⟨1190220, by rfl⟩ : syracuseStep 3173921 = 2380441) B2380441
theorem B2379307 : Blo 1409524 2379307 := bstep (se 1 (by rfl) ⟨1784480, by rfl⟩ : syracuseStep 2379307 = 3568961) B3568961
theorem B2117177 : Blo 1409524 2117177 := bstep (se 2 (by rfl) ⟨793941, by rfl⟩ : syracuseStep 2117177 = 1587883) B1587883
theorem B4017725 : Blo 1409524 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B5082743 : Blo 1409524 5082743 := bstep (se 1 (by rfl) ⟨3812057, by rfl⟩ : syracuseStep 5082743 = 7624115) B7624115
theorem B2117255 : Blo 1409524 2117255 := bstep (se 1 (by rfl) ⟨1587941, by rfl⟩ : syracuseStep 2117255 = 3175883) B3175883
theorem B2379449 : Blo 1409524 2379449 := bstep (se 2 (by rfl) ⟨892293, by rfl⟩ : syracuseStep 2379449 = 1784587) B1784587
theorem B3813065 : Blo 1409524 3813065 := bstep (se 2 (by rfl) ⟨1429899, by rfl⟩ : syracuseStep 3813065 = 2859799) B2859799
theorem B5426945 : Blo 1409524 5426945 := bstep (se 2 (by rfl) ⟨2035104, by rfl⟩ : syracuseStep 5426945 = 4070209) B4070209
theorem B4763393 : Blo 1409524 4763393 := bstep (se 2 (by rfl) ⟨1786272, by rfl⟩ : syracuseStep 4763393 = 3572545) B3572545
theorem B2543375 : Blo 1409524 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B6524705 : Blo 1409524 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B7630625 : Blo 1409524 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B48844595 : Blo 1409524 48844595 := bstep (se 1 (by rfl) ⟨36633446, by rfl⟩ : syracuseStep 48844595 = 73266893) B73266893
theorem B3174263 : Blo 1409524 3174263 := bstep (se 1 (by rfl) ⟨2380697, by rfl⟩ : syracuseStep 3174263 = 4761395) B4761395
theorem B7139339 : Blo 1409524 7139339 := bstep (se 1 (by rfl) ⟨5354504, by rfl⟩ : syracuseStep 7139339 = 10709009) B10709009
theorem B3010603 : Blo 1409524 3010603 := bstep (se 1 (by rfl) ⟨2257952, by rfl⟩ : syracuseStep 3010603 = 4515905) B4515905
theorem B3174443 : Blo 1409524 3174443 := bstep (se 1 (by rfl) ⟨2380832, by rfl⟩ : syracuseStep 3174443 = 4761665) B4761665
theorem B3387545 : Blo 1409524 3387545 := bstep (se 2 (by rfl) ⟨1270329, by rfl⟩ : syracuseStep 3387545 = 2540659) B2540659
theorem B7139501 : Blo 1409524 7139501 := bstep (se 3 (by rfl) ⟨1338656, by rfl⟩ : syracuseStep 7139501 = 2677313) B2677313
theorem B7622857 : Blo 1409524 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B6435073 : Blo 1409524 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B3387707 : Blo 1409524 3387707 := bstep (se 1 (by rfl) ⟨2540780, by rfl⟩ : syracuseStep 3387707 = 5081561) B5081561
theorem B15257915 : Blo 1409524 15257915 := bstep (se 1 (by rfl) ⟨11443436, by rfl⟩ : syracuseStep 15257915 = 22886873) B22886873
theorem B3567959 : Blo 1409524 3567959 := bstep (se 1 (by rfl) ⟨2675969, by rfl⟩ : syracuseStep 3567959 = 5351939) B5351939
theorem B2380151 : Blo 1409524 2380151 := bstep (se 1 (by rfl) ⟨1785113, by rfl⟩ : syracuseStep 2380151 = 3570227) B3570227
theorem B4018567 : Blo 1409524 4018567 := bstep (se 1 (by rfl) ⟨3013925, by rfl⟩ : syracuseStep 4018567 = 6027851) B6027851
theorem B3174803 : Blo 1409524 3174803 := bstep (se 1 (by rfl) ⟨2381102, by rfl⟩ : syracuseStep 3174803 = 4762205) B4762205
theorem B3174857 : Blo 1409524 3174857 := bstep (se 2 (by rfl) ⟨1190571, by rfl⟩ : syracuseStep 3174857 = 2381143) B2381143
theorem B8032715 : Blo 1409524 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B15249869 : Blo 1409524 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B3568171 : Blo 1409524 3568171 := bstep (se 1 (by rfl) ⟨2676128, by rfl⟩ : syracuseStep 3568171 = 5352257) B5352257
theorem B1585723 : Blo 1409524 1585723 := bstep (se 1 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 1585723 = 2378585) B2378585
theorem B4018841 : Blo 1409524 4018841 := bstep (se 2 (by rfl) ⟨1507065, by rfl⟩ : syracuseStep 4018841 = 3014131) B3014131
theorem B3568313 : Blo 1409524 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B8581925 : Blo 1409524 8581925 := bstep (se 4 (by rfl) ⟨804555, by rfl⟩ : syracuseStep 8581925 = 1609111) B1609111
theorem B2380603 : Blo 1409524 2380603 := bstep (se 1 (by rfl) ⟨1785452, by rfl⟩ : syracuseStep 2380603 = 3570905) B3570905
theorem B3388313 : Blo 1409524 3388313 := bstep (se 2 (by rfl) ⟨1270617, by rfl⟩ : syracuseStep 3388313 = 2541235) B2541235
theorem B2380745 : Blo 1409524 2380745 := bstep (se 2 (by rfl) ⟨892779, by rfl⟩ : syracuseStep 2380745 = 1785559) B1785559
theorem B43439075 : Blo 1409524 43439075 := bstep (se 1 (by rfl) ⟨32579306, by rfl⟩ : syracuseStep 43439075 = 65158613) B65158613
theorem B1586191 : Blo 1409524 1586191 := bstep (se 1 (by rfl) ⟨1189643, by rfl⟩ : syracuseStep 1586191 = 2379287) B2379287
theorem B14480471 : Blo 1409524 14480471 := bstep (se 1 (by rfl) ⟨10860353, by rfl⟩ : syracuseStep 14480471 = 21720707) B21720707
theorem B3175559 : Blo 1409524 3175559 := bstep (se 1 (by rfl) ⟨2381669, by rfl⟩ : syracuseStep 3175559 = 4763339) B4763339
theorem B3175739 : Blo 1409524 3175739 := bstep (se 1 (by rfl) ⟨2381804, by rfl⟩ : syracuseStep 3175739 = 4763609) B4763609
theorem B3175865 : Blo 1409524 3175865 := bstep (se 2 (by rfl) ⟨1190949, by rfl⟩ : syracuseStep 3175865 = 2381899) B2381899
theorem B1586695 : Blo 1409524 1586695 := bstep (se 1 (by rfl) ⟨1190021, by rfl⟩ : syracuseStep 1586695 = 2380043) B2380043
theorem B8582723 : Blo 1409524 8582723 := bstep (se 1 (by rfl) ⟨6437042, by rfl⟩ : syracuseStep 8582723 = 12874085) B12874085
theorem B1717895 : Blo 1409524 1717895 := bstep (se 1 (by rfl) ⟨1288421, by rfl⟩ : syracuseStep 1717895 = 2576843) B2576843
theorem B2381447 : Blo 1409524 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B3569305 : Blo 1409524 3569305 := bstep (se 2 (by rfl) ⟨1338489, by rfl⟩ : syracuseStep 3569305 = 2676979) B2676979
theorem B1586875 : Blo 1409524 1586875 := bstep (se 1 (by rfl) ⟨1190156, by rfl⟩ : syracuseStep 1586875 = 2380313) B2380313
theorem B3389129 : Blo 1409524 3389129 := bstep (se 2 (by rfl) ⟨1270923, by rfl⟩ : syracuseStep 3389129 = 2541847) B2541847
theorem B7141121 : Blo 1409524 7141121 := bstep (se 2 (by rfl) ⟨2677920, by rfl⟩ : syracuseStep 7141121 = 5355841) B5355841
theorem B2676539 : Blo 1409524 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B3569467 : Blo 1409524 3569467 := bstep (se 1 (by rfl) ⟨2677100, by rfl⟩ : syracuseStep 3569467 = 5354201) B5354201
theorem B3569609 : Blo 1409524 3569609 := bstep (se 2 (by rfl) ⟨1338603, by rfl⟩ : syracuseStep 3569609 = 2677207) B2677207
theorem B5085251 : Blo 1409524 5085251 := bstep (se 1 (by rfl) ⟨3813938, by rfl⟩ : syracuseStep 5085251 = 7627877) B7627877
theorem B1587343 : Blo 1409524 1587343 := bstep (se 1 (by rfl) ⟨1190507, by rfl⟩ : syracuseStep 1587343 = 2381015) B2381015
theorem B4290707 : Blo 1409524 4290707 := bstep (se 1 (by rfl) ⟨3218030, by rfl⟩ : syracuseStep 4290707 = 6436061) B6436061
theorem B2677025 : Blo 1409524 2677025 := bstep (se 2 (by rfl) ⟨1003884, by rfl⟩ : syracuseStep 2677025 = 2007769) B2007769
theorem B3569953 : Blo 1409524 3569953 := bstep (se 2 (by rfl) ⟨1338732, by rfl⟩ : syracuseStep 3569953 = 2677465) B2677465
theorem B1784207 : Blo 1409524 1784207 := bstep (se 1 (by rfl) ⟨1338155, by rfl⟩ : syracuseStep 1784207 = 2676311) B2676311
theorem B7625107 : Blo 1409524 7625107 := bstep (se 1 (by rfl) ⟨5718830, by rfl⟩ : syracuseStep 7625107 = 11437661) B11437661
theorem B3865121 : Blo 1409524 3865121 := bstep (se 2 (by rfl) ⟨1449420, by rfl⟩ : syracuseStep 3865121 = 2898841) B2898841
theorem B7141931 : Blo 1409524 7141931 := bstep (se 1 (by rfl) ⟨5356448, by rfl⟩ : syracuseStep 7141931 = 10712897) B10712897
theorem B2677367 : Blo 1409524 2677367 := bstep (se 1 (by rfl) ⟨2008025, by rfl⟩ : syracuseStep 2677367 = 4016051) B4016051
theorem B1587847 : Blo 1409524 1587847 := bstep (se 1 (by rfl) ⟨1190885, by rfl⟩ : syracuseStep 1587847 = 2381771) B2381771
theorem B15260339 : Blo 1409524 15260339 := bstep (se 1 (by rfl) ⟨11445254, by rfl⟩ : syracuseStep 15260339 = 22890509) B22890509
theorem B6028091 : Blo 1409524 6028091 := bstep (se 1 (by rfl) ⟨4521068, by rfl⟩ : syracuseStep 6028091 = 9042137) B9042137
theorem B3570551 : Blo 1409524 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B4758425 : Blo 1409524 4758425 := bstep (se 2 (by rfl) ⟨1784409, by rfl⟩ : syracuseStep 4758425 = 3568819) B3568819
theorem B7535639 : Blo 1409524 7535639 := bstep (se 1 (by rfl) ⟨5651729, by rfl⟩ : syracuseStep 7535639 = 11303459) B11303459
theorem B5356631 : Blo 1409524 5356631 := bstep (se 1 (by rfl) ⟨4017473, by rfl⟩ : syracuseStep 5356631 = 8034947) B8034947
theorem B10706093 : Blo 1409524 10706093 := bstep (se 3 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 10706093 = 4014785) B4014785
theorem B27467041 : Blo 1409524 27467041 := bstep (se 2 (by rfl) ⟨10300140, by rfl⟩ : syracuseStep 27467041 = 20600281) B20600281
theorem B3915155 : Blo 1409524 3915155 := bstep (se 1 (by rfl) ⟨2936366, by rfl⟩ : syracuseStep 3915155 = 5872733) B5872733
theorem B5357117 : Blo 1409524 5357117 := bstep (se 3 (by rfl) ⟨1004459, by rfl⟩ : syracuseStep 5357117 = 2008919) B2008919
theorem B6782525 : Blo 1409524 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B13549133 : Blo 1409524 13549133 := bstep (se 3 (by rfl) ⟨2540462, by rfl⟩ : syracuseStep 13549133 = 5080925) B5080925
theorem B4759127 : Blo 1409524 4759127 := bstep (se 1 (by rfl) ⟨3569345, by rfl⟩ : syracuseStep 4759127 = 7138691) B7138691
theorem B13549285 : Blo 1409524 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B6774529 : Blo 1409524 6774529 := bstep (se 2 (by rfl) ⟨2540448, by rfl⟩ : syracuseStep 6774529 = 5080897) B5080897
theorem B24420145 : Blo 1409524 24420145 := bstep (se 2 (by rfl) ⟨9157554, by rfl⟩ : syracuseStep 24420145 = 18315109) B18315109
theorem B7143227 : Blo 1409524 7143227 := bstep (se 1 (by rfl) ⟨5357420, by rfl⟩ : syracuseStep 7143227 = 10714841) B10714841
theorem B4824967 : Blo 1409524 4824967 := bstep (se 1 (by rfl) ⟨3618725, by rfl⟩ : syracuseStep 4824967 = 7237451) B7237451
theorem B3719047 : Blo 1409524 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B6021017 : Blo 1409524 6021017 := bstep (se 2 (by rfl) ⟨2257881, by rfl⟩ : syracuseStep 6021017 = 4515763) B4515763
theorem B3915721 : Blo 1409524 3915721 := bstep (se 2 (by rfl) ⟨1468395, by rfl⟩ : syracuseStep 3915721 = 2936791) B2936791
theorem B12058571 : Blo 1409524 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B7143389 : Blo 1409524 7143389 := bstep (se 3 (by rfl) ⟨1339385, by rfl⟩ : syracuseStep 7143389 = 2678771) B2678771
theorem B4759559 : Blo 1409524 4759559 := bstep (se 1 (by rfl) ⟨3569669, by rfl⟩ : syracuseStep 4759559 = 7139339) B7139339
theorem B4014137 : Blo 1409524 4014137 := bstep (se 2 (by rfl) ⟨1505301, by rfl⟩ : syracuseStep 4014137 = 3010603) B3010603
theorem B20095037 : Blo 1409524 20095037 := bstep (se 3 (by rfl) ⟨3767819, by rfl⟩ : syracuseStep 20095037 = 7535639) B7535639
theorem B4759667 : Blo 1409524 4759667 := bstep (se 1 (by rfl) ⟨3569750, by rfl⟩ : syracuseStep 4759667 = 7139501) B7139501
theorem B1785979 : Blo 1409524 1785979 := bstep (se 1 (by rfl) ⟨1339484, by rfl⟩ : syracuseStep 1785979 = 2678969) B2678969
theorem B10166579 : Blo 1409524 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B1786207 : Blo 1409524 1786207 := bstep (se 1 (by rfl) ⟨1339655, by rfl⟩ : syracuseStep 1786207 = 2679311) B2679311
theorem B9036137 : Blo 1409524 9036137 := bstep (se 2 (by rfl) ⟨3388551, by rfl⟩ : syracuseStep 9036137 = 6777103) B6777103
theorem B4759937 : Blo 1409524 4759937 := bstep (se 2 (by rfl) ⟨1784976, by rfl⟩ : syracuseStep 4759937 = 3569953) B3569953
theorem B2679227 : Blo 1409524 2679227 := bstep (se 1 (by rfl) ⟨2009420, by rfl⟩ : syracuseStep 2679227 = 4018841) B4018841
theorem B5358089 : Blo 1409524 5358089 := bstep (se 2 (by rfl) ⟨2009283, by rfl⟩ : syracuseStep 5358089 = 4018567) B4018567
theorem B10166809 : Blo 1409524 10166809 := bstep (se 2 (by rfl) ⟨3812553, by rfl⟩ : syracuseStep 10166809 = 7625107) B7625107
theorem B1409575 : Blo 1409524 1409575 := bstep (se 1 (by rfl) ⟨1057181, by rfl⟩ : syracuseStep 1409575 = 2114363) B2114363
theorem B1409615 : Blo 1409524 1409615 := bstep (se 1 (by rfl) ⟨1057211, by rfl⟩ : syracuseStep 1409615 = 2114423) B2114423
theorem B1409631 : Blo 1409524 1409631 := bstep (se 1 (by rfl) ⟨1057223, by rfl⟩ : syracuseStep 1409631 = 2114447) B2114447
theorem B1409659 : Blo 1409524 1409659 := bstep (se 1 (by rfl) ⟨1057244, by rfl⟩ : syracuseStep 1409659 = 2114489) B2114489
theorem B3572363 : Blo 1409524 3572363 := bstep (se 1 (by rfl) ⟨2679272, by rfl⟩ : syracuseStep 3572363 = 5358545) B5358545
theorem B28959383 : Blo 1409524 28959383 := bstep (se 1 (by rfl) ⟨21719537, by rfl⟩ : syracuseStep 28959383 = 43439075) B43439075
theorem B1409711 : Blo 1409524 1409711 := bstep (se 1 (by rfl) ⟨1057283, by rfl⟩ : syracuseStep 1409711 = 2114567) B2114567
theorem B1409735 : Blo 1409524 1409735 := bstep (se 1 (by rfl) ⟨1057301, by rfl⟩ : syracuseStep 1409735 = 2114603) B2114603
theorem B1409755 : Blo 1409524 1409755 := bstep (se 1 (by rfl) ⟨1057316, by rfl⟩ : syracuseStep 1409755 = 2114633) B2114633
theorem B2114297 : Blo 1409524 2114297 := bstep (se 2 (by rfl) ⟨792861, by rfl⟩ : syracuseStep 2114297 = 1585723) B1585723
theorem B1409831 : Blo 1409524 1409831 := bstep (se 1 (by rfl) ⟨1057373, by rfl⟩ : syracuseStep 1409831 = 2114747) B2114747
theorem B1409871 : Blo 1409524 1409871 := bstep (se 1 (by rfl) ⟨1057403, by rfl⟩ : syracuseStep 1409871 = 2114807) B2114807
theorem B2114399 : Blo 1409524 2114399 := bstep (se 1 (by rfl) ⟨1585799, by rfl⟩ : syracuseStep 2114399 = 3171599) B3171599
theorem B1409887 : Blo 1409524 1409887 := bstep (se 1 (by rfl) ⟨1057415, by rfl⟩ : syracuseStep 1409887 = 2114831) B2114831
theorem B2712425 : Blo 1409524 2712425 := bstep (se 2 (by rfl) ⟨1017159, by rfl⟩ : syracuseStep 2712425 = 2034319) B2034319
theorem B2114411 : Blo 1409524 2114411 := bstep (se 1 (by rfl) ⟨1585808, by rfl⟩ : syracuseStep 2114411 = 3171617) B3171617
theorem B1409915 : Blo 1409524 1409915 := bstep (se 1 (by rfl) ⟨1057436, by rfl⟩ : syracuseStep 1409915 = 2114873) B2114873
theorem B1409967 : Blo 1409524 1409967 := bstep (se 1 (by rfl) ⟨1057475, by rfl⟩ : syracuseStep 1409967 = 2114951) B2114951
theorem B1409991 : Blo 1409524 1409991 := bstep (se 1 (by rfl) ⟨1057493, by rfl⟩ : syracuseStep 1409991 = 2114987) B2114987
theorem B1410011 : Blo 1409524 1410011 := bstep (se 1 (by rfl) ⟨1057508, by rfl⟩ : syracuseStep 1410011 = 2115017) B2115017
theorem B1410087 : Blo 1409524 1410087 := bstep (se 1 (by rfl) ⟨1057565, by rfl⟩ : syracuseStep 1410087 = 2115131) B2115131
theorem B2114639 : Blo 1409524 2114639 := bstep (se 1 (by rfl) ⟨1585979, by rfl⟩ : syracuseStep 2114639 = 3171959) B3171959
theorem B1410127 : Blo 1409524 1410127 := bstep (se 1 (by rfl) ⟨1057595, by rfl⟩ : syracuseStep 1410127 = 2115191) B2115191
theorem B1410143 : Blo 1409524 1410143 := bstep (se 1 (by rfl) ⟨1057607, by rfl⟩ : syracuseStep 1410143 = 2115215) B2115215
theorem B1410171 : Blo 1409524 1410171 := bstep (se 1 (by rfl) ⟨1057628, by rfl⟩ : syracuseStep 1410171 = 2115257) B2115257
theorem B4760747 : Blo 1409524 4760747 := bstep (se 1 (by rfl) ⟨3570560, by rfl⟩ : syracuseStep 4760747 = 7141121) B7141121
theorem B1410223 : Blo 1409524 1410223 := bstep (se 1 (by rfl) ⟨1057667, by rfl⟩ : syracuseStep 1410223 = 2115335) B2115335
theorem B2114759 : Blo 1409524 2114759 := bstep (se 1 (by rfl) ⟨1586069, by rfl⟩ : syracuseStep 2114759 = 3172139) B3172139
theorem B1410247 : Blo 1409524 1410247 := bstep (se 1 (by rfl) ⟨1057685, by rfl⟩ : syracuseStep 1410247 = 2115371) B2115371
theorem B1410267 : Blo 1409524 1410267 := bstep (se 1 (by rfl) ⟨1057700, by rfl⟩ : syracuseStep 1410267 = 2115401) B2115401
theorem B1410343 : Blo 1409524 1410343 := bstep (se 1 (by rfl) ⟨1057757, by rfl⟩ : syracuseStep 1410343 = 2115515) B2115515
theorem B1410383 : Blo 1409524 1410383 := bstep (se 1 (by rfl) ⟨1057787, by rfl⟩ : syracuseStep 1410383 = 2115575) B2115575
theorem B1410399 : Blo 1409524 1410399 := bstep (se 1 (by rfl) ⟨1057799, by rfl⟩ : syracuseStep 1410399 = 2115599) B2115599
theorem B3171689 : Blo 1409524 3171689 := bstep (se 2 (by rfl) ⟨1189383, by rfl⟩ : syracuseStep 3171689 = 2378767) B2378767
theorem B2114921 : Blo 1409524 2114921 := bstep (se 2 (by rfl) ⟨793095, by rfl⟩ : syracuseStep 2114921 = 1586191) B1586191
theorem B1410427 : Blo 1409524 1410427 := bstep (se 1 (by rfl) ⟨1057820, by rfl⟩ : syracuseStep 1410427 = 2115641) B2115641
theorem B7144847 : Blo 1409524 7144847 := bstep (se 1 (by rfl) ⟨5358635, by rfl⟩ : syracuseStep 7144847 = 10717271) B10717271
theorem B1410479 : Blo 1409524 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B2114999 : Blo 1409524 2114999 := bstep (se 1 (by rfl) ⟨1586249, by rfl⟩ : syracuseStep 2114999 = 3172499) B3172499
theorem B2860471 : Blo 1409524 2860471 := bstep (se 1 (by rfl) ⟨2145353, by rfl⟩ : syracuseStep 2860471 = 4290707) B4290707
theorem B1410503 : Blo 1409524 1410503 := bstep (se 1 (by rfl) ⟨1057877, by rfl⟩ : syracuseStep 1410503 = 2115755) B2115755
theorem B2115035 : Blo 1409524 2115035 := bstep (se 1 (by rfl) ⟨1586276, by rfl⟩ : syracuseStep 2115035 = 3172553) B3172553
theorem B1410523 : Blo 1409524 1410523 := bstep (se 1 (by rfl) ⟨1057892, by rfl⟩ : syracuseStep 1410523 = 2115785) B2115785
theorem B1410599 : Blo 1409524 1410599 := bstep (se 1 (by rfl) ⟨1057949, by rfl⟩ : syracuseStep 1410599 = 2115899) B2115899
theorem B1410639 : Blo 1409524 1410639 := bstep (se 1 (by rfl) ⟨1057979, by rfl⟩ : syracuseStep 1410639 = 2115959) B2115959
theorem B1410655 : Blo 1409524 1410655 := bstep (se 1 (by rfl) ⟨1057991, by rfl⟩ : syracuseStep 1410655 = 2115983) B2115983
theorem B1410683 : Blo 1409524 1410683 := bstep (se 1 (by rfl) ⟨1058012, by rfl⟩ : syracuseStep 1410683 = 2116025) B2116025
theorem B5359243 : Blo 1409524 5359243 := bstep (se 1 (by rfl) ⟨4019432, by rfl⟩ : syracuseStep 5359243 = 8038865) B8038865
theorem B34309777 : Blo 1409524 34309777 := bstep (se 2 (by rfl) ⟨12866166, by rfl⟩ : syracuseStep 34309777 = 25732333) B25732333
theorem B1410735 : Blo 1409524 1410735 := bstep (se 1 (by rfl) ⟨1058051, by rfl⟩ : syracuseStep 1410735 = 2116103) B2116103
theorem B4581053 : Blo 1409524 4581053 := bstep (se 3 (by rfl) ⟨858947, by rfl⟩ : syracuseStep 4581053 = 1717895) B1717895
theorem B4761287 : Blo 1409524 4761287 := bstep (se 1 (by rfl) ⟨3570965, by rfl⟩ : syracuseStep 4761287 = 7141931) B7141931
theorem B1410759 : Blo 1409524 1410759 := bstep (se 1 (by rfl) ⟨1058069, by rfl⟩ : syracuseStep 1410759 = 2116139) B2116139
theorem B1410779 : Blo 1409524 1410779 := bstep (se 1 (by rfl) ⟨1058084, by rfl⟩ : syracuseStep 1410779 = 2116169) B2116169
theorem B1410855 : Blo 1409524 1410855 := bstep (se 1 (by rfl) ⟨1058141, by rfl⟩ : syracuseStep 1410855 = 2116283) B2116283
theorem B1410895 : Blo 1409524 1410895 := bstep (se 1 (by rfl) ⟨1058171, by rfl⟩ : syracuseStep 1410895 = 2116343) B2116343
theorem B1410911 : Blo 1409524 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B1410939 : Blo 1409524 1410939 := bstep (se 1 (by rfl) ⟨1058204, by rfl⟩ : syracuseStep 1410939 = 2116409) B2116409
theorem B2115503 : Blo 1409524 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B1410991 : Blo 1409524 1410991 := bstep (se 1 (by rfl) ⟨1058243, by rfl⟩ : syracuseStep 1410991 = 2116487) B2116487
theorem B3172283 : Blo 1409524 3172283 := bstep (se 1 (by rfl) ⟨2379212, by rfl⟩ : syracuseStep 3172283 = 4758425) B4758425
theorem B1411015 : Blo 1409524 1411015 := bstep (se 1 (by rfl) ⟨1058261, by rfl⟩ : syracuseStep 1411015 = 2116523) B2116523
theorem B1411035 : Blo 1409524 1411035 := bstep (se 1 (by rfl) ⟨1058276, by rfl⟩ : syracuseStep 1411035 = 2116553) B2116553
theorem B2115593 : Blo 1409524 2115593 := bstep (se 2 (by rfl) ⟨793347, by rfl⟩ : syracuseStep 2115593 = 1586695) B1586695
theorem B2115623 : Blo 1409524 2115623 := bstep (se 1 (by rfl) ⟨1586717, by rfl⟩ : syracuseStep 2115623 = 3173435) B3173435
theorem B1411111 : Blo 1409524 1411111 := bstep (se 1 (by rfl) ⟨1058333, by rfl⟩ : syracuseStep 1411111 = 2116667) B2116667
theorem B3172409 : Blo 1409524 3172409 := bstep (se 2 (by rfl) ⟨1189653, by rfl⟩ : syracuseStep 3172409 = 2379307) B2379307
theorem B1411151 : Blo 1409524 1411151 := bstep (se 1 (by rfl) ⟨1058363, by rfl⟩ : syracuseStep 1411151 = 2116727) B2116727
theorem B1411167 : Blo 1409524 1411167 := bstep (se 1 (by rfl) ⟨1058375, by rfl⟩ : syracuseStep 1411167 = 2116751) B2116751
theorem B7137395 : Blo 1409524 7137395 := bstep (se 1 (by rfl) ⟨5353046, by rfl⟩ : syracuseStep 7137395 = 10706093) B10706093
theorem B2115707 : Blo 1409524 2115707 := bstep (se 1 (by rfl) ⟨1586780, by rfl⟩ : syracuseStep 2115707 = 3173561) B3173561
theorem B1411195 : Blo 1409524 1411195 := bstep (se 1 (by rfl) ⟨1058396, by rfl⟩ : syracuseStep 1411195 = 2116793) B2116793
theorem B1411247 : Blo 1409524 1411247 := bstep (se 1 (by rfl) ⟨1058435, by rfl⟩ : syracuseStep 1411247 = 2116871) B2116871
theorem B1411271 : Blo 1409524 1411271 := bstep (se 1 (by rfl) ⟨1058453, by rfl⟩ : syracuseStep 1411271 = 2116907) B2116907
theorem B1411291 : Blo 1409524 1411291 := bstep (se 1 (by rfl) ⟨1058468, by rfl⟩ : syracuseStep 1411291 = 2116937) B2116937
theorem B2115833 : Blo 1409524 2115833 := bstep (se 2 (by rfl) ⟨793437, by rfl⟩ : syracuseStep 2115833 = 1586875) B1586875
theorem B1411367 : Blo 1409524 1411367 := bstep (se 1 (by rfl) ⟨1058525, by rfl⟩ : syracuseStep 1411367 = 2117051) B2117051
theorem B18065713 : Blo 1409524 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B1411407 : Blo 1409524 1411407 := bstep (se 1 (by rfl) ⟨1058555, by rfl⟩ : syracuseStep 1411407 = 2117111) B2117111
theorem B2115935 : Blo 1409524 2115935 := bstep (se 1 (by rfl) ⟨1586951, by rfl⟩ : syracuseStep 2115935 = 3173903) B3173903
theorem B1411423 : Blo 1409524 1411423 := bstep (se 1 (by rfl) ⟨1058567, by rfl⟩ : syracuseStep 1411423 = 2117135) B2117135
theorem B2115947 : Blo 1409524 2115947 := bstep (se 1 (by rfl) ⟨1586960, by rfl⟩ : syracuseStep 2115947 = 3173921) B3173921
theorem B1411451 : Blo 1409524 1411451 := bstep (se 1 (by rfl) ⟨1058588, by rfl⟩ : syracuseStep 1411451 = 2117177) B2117177
theorem B20883845 : Blo 1409524 20883845 := bstep (se 4 (by rfl) ⟨1957860, by rfl⟩ : syracuseStep 20883845 = 3915721) B3915721
theorem B3172751 : Blo 1409524 3172751 := bstep (se 1 (by rfl) ⟨2379563, by rfl⟩ : syracuseStep 3172751 = 4759127) B4759127
theorem B1411503 : Blo 1409524 1411503 := bstep (se 1 (by rfl) ⟨1058627, by rfl⟩ : syracuseStep 1411503 = 2117255) B2117255
theorem B2542043 : Blo 1409524 2542043 := bstep (se 1 (by rfl) ⟨1906532, by rfl⟩ : syracuseStep 2542043 = 3813065) B3813065
theorem B6433289 : Blo 1409524 6433289 := bstep (se 2 (by rfl) ⟨2412483, by rfl⟩ : syracuseStep 6433289 = 4824967) B4824967
theorem B4958729 : Blo 1409524 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B4762151 : Blo 1409524 4762151 := bstep (se 1 (by rfl) ⟨3571613, by rfl⟩ : syracuseStep 4762151 = 7143227) B7143227
theorem B2116175 : Blo 1409524 2116175 := bstep (se 1 (by rfl) ⟨1587131, by rfl⟩ : syracuseStep 2116175 = 3174263) B3174263
theorem B8039047 : Blo 1409524 8039047 := bstep (se 1 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 8039047 = 12058571) B12058571
theorem B4762259 : Blo 1409524 4762259 := bstep (se 1 (by rfl) ⟨3571694, by rfl⟩ : syracuseStep 4762259 = 7143389) B7143389
theorem B2116295 : Blo 1409524 2116295 := bstep (se 1 (by rfl) ⟨1587221, by rfl⟩ : syracuseStep 2116295 = 3174443) B3174443
theorem B3173075 : Blo 1409524 3173075 := bstep (se 1 (by rfl) ⟨2379806, by rfl⟩ : syracuseStep 3173075 = 4759613) B4759613
theorem B5081849 : Blo 1409524 5081849 := bstep (se 2 (by rfl) ⟨1905693, by rfl⟩ : syracuseStep 5081849 = 3811387) B3811387
theorem B2116457 : Blo 1409524 2116457 := bstep (se 2 (by rfl) ⟨793671, by rfl⟩ : syracuseStep 2116457 = 1587343) B1587343
theorem B4762475 : Blo 1409524 4762475 := bstep (se 1 (by rfl) ⟨3571856, by rfl⟩ : syracuseStep 4762475 = 7143713) B7143713
theorem B2378639 : Blo 1409524 2378639 := bstep (se 1 (by rfl) ⟨1783979, by rfl⟩ : syracuseStep 2378639 = 3567959) B3567959
theorem B4762529 : Blo 1409524 4762529 := bstep (se 2 (by rfl) ⟨1785948, by rfl⟩ : syracuseStep 4762529 = 3571897) B3571897
theorem B2116535 : Blo 1409524 2116535 := bstep (se 1 (by rfl) ⟨1587401, by rfl⟩ : syracuseStep 2116535 = 3174803) B3174803
theorem B2116571 : Blo 1409524 2116571 := bstep (se 1 (by rfl) ⟨1587428, by rfl⟩ : syracuseStep 2116571 = 3174857) B3174857
theorem B10709981 : Blo 1409524 10709981 := bstep (se 3 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 10709981 = 4016243) B4016243
theorem B8580097 : Blo 1409524 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B10169345 : Blo 1409524 10169345 := bstep (se 2 (by rfl) ⟨3813504, by rfl⟩ : syracuseStep 10169345 = 7627009) B7627009
theorem B3435527 : Blo 1409524 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B4582415 : Blo 1409524 4582415 := bstep (se 1 (by rfl) ⟨3436811, by rfl⟩ : syracuseStep 4582415 = 6873623) B6873623
theorem B5155859 : Blo 1409524 5155859 := bstep (se 1 (by rfl) ⟨3866894, by rfl⟩ : syracuseStep 5155859 = 7733789) B7733789
theorem B2378875 : Blo 1409524 2378875 := bstep (se 1 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 2378875 = 3568313) B3568313
theorem B5721283 : Blo 1409524 5721283 := bstep (se 1 (by rfl) ⟨4290962, by rfl⟩ : syracuseStep 5721283 = 8581925) B8581925
theorem B2289071 : Blo 1409524 2289071 := bstep (se 1 (by rfl) ⟨1716803, by rfl⟩ : syracuseStep 2289071 = 3433607) B3433607
theorem B2117039 : Blo 1409524 2117039 := bstep (se 1 (by rfl) ⟨1587779, by rfl⟩ : syracuseStep 2117039 = 3175559) B3175559
theorem B4763123 : Blo 1409524 4763123 := bstep (se 1 (by rfl) ⟨3572342, by rfl⟩ : syracuseStep 4763123 = 7144685) B7144685
theorem B2117129 : Blo 1409524 2117129 := bstep (se 2 (by rfl) ⟨793923, by rfl⟩ : syracuseStep 2117129 = 1587847) B1587847
theorem B7941671 : Blo 1409524 7941671 := bstep (se 1 (by rfl) ⟨5956253, by rfl⟩ : syracuseStep 7941671 = 11912507) B11912507
theorem B2117159 : Blo 1409524 2117159 := bstep (se 1 (by rfl) ⟨1587869, by rfl⟩ : syracuseStep 2117159 = 3175739) B3175739
theorem B3174011 : Blo 1409524 3174011 := bstep (se 1 (by rfl) ⟨2380508, by rfl⟩ : syracuseStep 3174011 = 4761017) B4761017
theorem B2117243 : Blo 1409524 2117243 := bstep (se 1 (by rfl) ⟨1587932, by rfl⟩ : syracuseStep 2117243 = 3175865) B3175865
theorem B7139015 : Blo 1409524 7139015 := bstep (se 1 (by rfl) ⟨5354261, by rfl⟩ : syracuseStep 7139015 = 10708523) B10708523
theorem B3387091 : Blo 1409524 3387091 := bstep (se 1 (by rfl) ⟨2540318, by rfl⟩ : syracuseStep 3387091 = 5080637) B5080637
theorem B5721815 : Blo 1409524 5721815 := bstep (se 1 (by rfl) ⟨4291361, by rfl⟩ : syracuseStep 5721815 = 8582723) B8582723
theorem B3174137 : Blo 1409524 3174137 := bstep (se 2 (by rfl) ⟨1190301, by rfl⟩ : syracuseStep 3174137 = 2380603) B2380603
theorem B2379739 : Blo 1409524 2379739 := bstep (se 1 (by rfl) ⟨1784804, by rfl⟩ : syracuseStep 2379739 = 3569609) B3569609
theorem B3174407 : Blo 1409524 3174407 := bstep (se 1 (by rfl) ⟨2380805, by rfl⟩ : syracuseStep 3174407 = 4761611) B4761611
theorem B4763663 : Blo 1409524 4763663 := bstep (se 1 (by rfl) ⟨3572747, by rfl⟩ : syracuseStep 4763663 = 7145495) B7145495
theorem B3174479 : Blo 1409524 3174479 := bstep (se 1 (by rfl) ⟨2380859, by rfl⟩ : syracuseStep 3174479 = 4761719) B4761719
theorem B2576747 : Blo 1409524 2576747 := bstep (se 1 (by rfl) ⟨1932560, by rfl⟩ : syracuseStep 2576747 = 3865121) B3865121
theorem B36622721 : Blo 1409524 36622721 := bstep (se 2 (by rfl) ⟨13733520, by rfl⟩ : syracuseStep 36622721 = 27467041) B27467041
theorem B3813851 : Blo 1409524 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B3174875 : Blo 1409524 3174875 := bstep (se 1 (by rfl) ⟨2381156, by rfl⟩ : syracuseStep 3174875 = 4762313) B4762313
theorem B19296791 : Blo 1409524 19296791 := bstep (se 1 (by rfl) ⟨14472593, by rfl⟩ : syracuseStep 19296791 = 28945187) B28945187
theorem B4018727 : Blo 1409524 4018727 := bstep (se 1 (by rfl) ⟨3014045, by rfl⟩ : syracuseStep 4018727 = 6028091) B6028091
theorem B2380367 : Blo 1409524 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B3388321 : Blo 1409524 3388321 := bstep (se 2 (by rfl) ⟨1270620, by rfl⟩ : syracuseStep 3388321 = 2541241) B2541241
theorem B3175343 : Blo 1409524 3175343 := bstep (se 1 (by rfl) ⟨2381507, by rfl⟩ : syracuseStep 3175343 = 4763015) B4763015
theorem B2610103 : Blo 1409524 2610103 := bstep (se 1 (by rfl) ⟨1957577, by rfl⟩ : syracuseStep 2610103 = 3915155) B3915155
theorem B9032705 : Blo 1409524 9032705 := bstep (se 2 (by rfl) ⟨3387264, by rfl⟩ : syracuseStep 9032705 = 6774529) B6774529
theorem B9032755 : Blo 1409524 9032755 := bstep (se 1 (by rfl) ⟨6774566, by rfl⟩ : syracuseStep 9032755 = 13549133) B13549133
theorem B32560193 : Blo 1409524 32560193 := bstep (se 2 (by rfl) ⟨12210072, by rfl⟩ : syracuseStep 32560193 = 24420145) B24420145
theorem B3388495 : Blo 1409524 3388495 := bstep (se 1 (by rfl) ⟨2541371, by rfl⟩ : syracuseStep 3388495 = 5082743) B5082743
theorem B1586299 : Blo 1409524 1586299 := bstep (se 1 (by rfl) ⟨1189724, by rfl⟩ : syracuseStep 1586299 = 2379449) B2379449
theorem B3617963 : Blo 1409524 3617963 := bstep (se 1 (by rfl) ⟨2713472, by rfl⟩ : syracuseStep 3617963 = 5426945) B5426945
theorem B3175595 : Blo 1409524 3175595 := bstep (se 1 (by rfl) ⟨2381696, by rfl⟩ : syracuseStep 3175595 = 4763393) B4763393
theorem B2381231 : Blo 1409524 2381231 := bstep (se 1 (by rfl) ⟨1785923, by rfl⟩ : syracuseStep 2381231 = 3571847) B3571847
theorem B2258363 : Blo 1409524 2258363 := bstep (se 1 (by rfl) ⟨1693772, by rfl⟩ : syracuseStep 2258363 = 3387545) B3387545
theorem B10311131 : Blo 1409524 10311131 := bstep (se 1 (by rfl) ⟨7733348, by rfl⟩ : syracuseStep 10311131 = 15466697) B15466697
theorem B18077195 : Blo 1409524 18077195 := bstep (se 1 (by rfl) ⟨13557896, by rfl⟩ : syracuseStep 18077195 = 27115793) B27115793
theorem B2258471 : Blo 1409524 2258471 := bstep (se 1 (by rfl) ⟨1693853, by rfl⟩ : syracuseStep 2258471 = 3387707) B3387707
theorem B10171943 : Blo 1409524 10171943 := bstep (se 1 (by rfl) ⟨7628957, by rfl⟩ : syracuseStep 10171943 = 15257915) B15257915
theorem B38614589 : Blo 1409524 38614589 := bstep (se 3 (by rfl) ⟨7240235, by rfl⟩ : syracuseStep 38614589 = 14480471) B14480471
theorem B1586767 : Blo 1409524 1586767 := bstep (se 1 (by rfl) ⟨1190075, by rfl⟩ : syracuseStep 1586767 = 2380151) B2380151
theorem B10163809 : Blo 1409524 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B9164411 : Blo 1409524 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B5355143 : Blo 1409524 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B2676395 : Blo 1409524 2676395 := bstep (se 1 (by rfl) ⟨2007296, by rfl⟩ : syracuseStep 2676395 = 4014593) B4014593
theorem B20322083 : Blo 1409524 20322083 := bstep (se 1 (by rfl) ⟨15241562, by rfl⟩ : syracuseStep 20322083 = 30483125) B30483125
theorem B4757291 : Blo 1409524 4757291 := bstep (se 1 (by rfl) ⟨3567968, by rfl⟩ : syracuseStep 4757291 = 7135937) B7135937
theorem B2381663 : Blo 1409524 2381663 := bstep (se 1 (by rfl) ⟨1786247, by rfl⟩ : syracuseStep 2381663 = 3572495) B3572495
theorem B30496621 : Blo 1409524 30496621 := bstep (se 3 (by rfl) ⟨5718116, by rfl⟩ : syracuseStep 30496621 = 11436233) B11436233
theorem B2258875 : Blo 1409524 2258875 := bstep (se 1 (by rfl) ⟨1694156, by rfl⟩ : syracuseStep 2258875 = 3388313) B3388313
theorem B1587163 : Blo 1409524 1587163 := bstep (se 1 (by rfl) ⟨1190372, by rfl⟩ : syracuseStep 1587163 = 2380745) B2380745
theorem B4757561 : Blo 1409524 4757561 := bstep (se 2 (by rfl) ⟨1784085, by rfl⟩ : syracuseStep 4757561 = 3568171) B3568171
theorem B4757885 : Blo 1409524 4757885 := bstep (se 3 (by rfl) ⟨892103, by rfl⟩ : syracuseStep 4757885 = 1784207) B1784207
theorem B1587631 : Blo 1409524 1587631 := bstep (se 1 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 1587631 = 2381447) B2381447
theorem B2259419 : Blo 1409524 2259419 := bstep (se 1 (by rfl) ⟨1694564, by rfl⟩ : syracuseStep 2259419 = 3389129) B3389129
theorem B1784359 : Blo 1409524 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B4758155 : Blo 1409524 4758155 := bstep (se 1 (by rfl) ⟨3568616, by rfl⟩ : syracuseStep 4758155 = 7137233) B7137233
theorem B3390167 : Blo 1409524 3390167 := bstep (se 1 (by rfl) ⟨2542625, by rfl⟩ : syracuseStep 3390167 = 5085251) B5085251
theorem B7625501 : Blo 1409524 7625501 := bstep (se 3 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 7625501 = 2859563) B2859563
theorem B1784683 : Blo 1409524 1784683 := bstep (se 1 (by rfl) ⟨1338512, by rfl⟩ : syracuseStep 1784683 = 2677025) B2677025
theorem B9034679 : Blo 1409524 9034679 := bstep (se 1 (by rfl) ⟨6776009, by rfl⟩ : syracuseStep 9034679 = 13552019) B13552019
theorem B2677769 : Blo 1409524 2677769 := bstep (se 2 (by rfl) ⟨1004163, by rfl⟩ : syracuseStep 2677769 = 2008327) B2008327
theorem B2677799 : Blo 1409524 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B5356601 : Blo 1409524 5356601 := bstep (se 2 (by rfl) ⟨2008725, by rfl⟩ : syracuseStep 5356601 = 4017451) B4017451
theorem B1784911 : Blo 1409524 1784911 := bstep (se 1 (by rfl) ⟨1338683, by rfl⟩ : syracuseStep 1784911 = 2677367) B2677367
theorem B10173559 : Blo 1409524 10173559 := bstep (se 1 (by rfl) ⟨7630169, by rfl⟩ : syracuseStep 10173559 = 15260339) B15260339
theorem B3571087 : Blo 1409524 3571087 := bstep (se 1 (by rfl) ⟨2678315, by rfl⟩ : syracuseStep 3571087 = 5356631) B5356631
theorem B4759073 : Blo 1409524 4759073 := bstep (se 2 (by rfl) ⟨1784652, by rfl⟩ : syracuseStep 4759073 = 3569305) B3569305
theorem B10706579 : Blo 1409524 10706579 := bstep (se 1 (by rfl) ⟨8029934, by rfl⟩ : syracuseStep 10706579 = 16059869) B16059869
theorem B2678483 : Blo 1409524 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B3571411 : Blo 1409524 3571411 := bstep (se 1 (by rfl) ⟨2678558, by rfl⟩ : syracuseStep 3571411 = 5357117) B5357117
theorem B4521683 : Blo 1409524 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B4759289 : Blo 1409524 4759289 := bstep (se 2 (by rfl) ⟨1784733, by rfl⟩ : syracuseStep 4759289 = 3569467) B3569467
theorem B2678521 : Blo 1409524 2678521 := bstep (se 2 (by rfl) ⟨1004445, by rfl⟩ : syracuseStep 2678521 = 2008891) B2008891
theorem B36151109 : Blo 1409524 36151109 := bstep (se 4 (by rfl) ⟨3389166, by rfl⟩ : syracuseStep 36151109 = 6778333) B6778333
theorem B1695583 : Blo 1409524 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B4349803 : Blo 1409524 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B5087083 : Blo 1409524 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B32563063 : Blo 1409524 32563063 := bstep (se 1 (by rfl) ⟨24422297, by rfl⟩ : syracuseStep 32563063 = 48844595) B48844595
theorem B4014011 : Blo 1409524 4014011 := bstep (se 1 (by rfl) ⟨3010508, by rfl⟩ : syracuseStep 4014011 = 6021017) B6021017
theorem B1786151 : Blo 1409524 1786151 := bstep (se 1 (by rfl) ⟨1339613, by rfl⟩ : syracuseStep 1786151 = 2679227) B2679227
theorem B3572059 : Blo 1409524 3572059 := bstep (se 1 (by rfl) ⟨2679044, by rfl⟩ : syracuseStep 3572059 = 5358089) B5358089
theorem B2679151 : Blo 1409524 2679151 := bstep (se 1 (by rfl) ⟨2009363, by rfl⟩ : syracuseStep 2679151 = 4018727) B4018727
theorem B1409531 : Blo 1409524 1409531 := bstep (se 1 (by rfl) ⟨1057148, by rfl⟩ : syracuseStep 1409531 = 2114297) B2114297
theorem B54206981 : Blo 1409524 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B1409599 : Blo 1409524 1409599 := bstep (se 1 (by rfl) ⟨1057199, by rfl⟩ : syracuseStep 1409599 = 2114399) B2114399
theorem B1409607 : Blo 1409524 1409607 := bstep (se 1 (by rfl) ⟨1057205, by rfl⟩ : syracuseStep 1409607 = 2114411) B2114411
theorem B6021803 : Blo 1409524 6021803 := bstep (se 1 (by rfl) ⟨4516352, by rfl⟩ : syracuseStep 6021803 = 9032705) B9032705
theorem B1409759 : Blo 1409524 1409759 := bstep (se 1 (by rfl) ⟨1057319, by rfl⟩ : syracuseStep 1409759 = 2114639) B2114639
theorem B1409839 : Blo 1409524 1409839 := bstep (se 1 (by rfl) ⟨1057379, by rfl⟩ : syracuseStep 1409839 = 2114759) B2114759
theorem B2114459 : Blo 1409524 2114459 := bstep (se 1 (by rfl) ⟨1585844, by rfl⟩ : syracuseStep 2114459 = 3171689) B3171689
theorem B1409947 : Blo 1409524 1409947 := bstep (se 1 (by rfl) ⟨1057460, by rfl⟩ : syracuseStep 1409947 = 2114921) B2114921
theorem B1409999 : Blo 1409524 1409999 := bstep (se 1 (by rfl) ⟨1057499, by rfl⟩ : syracuseStep 1409999 = 2114999) B2114999
theorem B1410023 : Blo 1409524 1410023 := bstep (se 1 (by rfl) ⟨1057517, by rfl⟩ : syracuseStep 1410023 = 2115035) B2115035
theorem B6874087 : Blo 1409524 6874087 := bstep (se 1 (by rfl) ⟨5155565, by rfl⟩ : syracuseStep 6874087 = 10311131) B10311131
theorem B12051463 : Blo 1409524 12051463 := bstep (se 1 (by rfl) ⟨9038597, by rfl⟩ : syracuseStep 12051463 = 18077195) B18077195
theorem B3171527 : Blo 1409524 3171527 := bstep (se 1 (by rfl) ⟨2378645, by rfl⟩ : syracuseStep 3171527 = 4757291) B4757291
theorem B1410335 : Blo 1409524 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B2114855 : Blo 1409524 2114855 := bstep (se 1 (by rfl) ⟨1586141, by rfl⟩ : syracuseStep 2114855 = 3172283) B3172283
theorem B1410395 : Blo 1409524 1410395 := bstep (se 1 (by rfl) ⟨1057796, by rfl⟩ : syracuseStep 1410395 = 2115593) B2115593
theorem B1410415 : Blo 1409524 1410415 := bstep (se 1 (by rfl) ⟨1057811, by rfl⟩ : syracuseStep 1410415 = 2115623) B2115623
theorem B3171707 : Blo 1409524 3171707 := bstep (se 1 (by rfl) ⟨2378780, by rfl⟩ : syracuseStep 3171707 = 4757561) B4757561
theorem B2114939 : Blo 1409524 2114939 := bstep (se 1 (by rfl) ⟨1586204, by rfl⟩ : syracuseStep 2114939 = 3172409) B3172409
theorem B12043673 : Blo 1409524 12043673 := bstep (se 2 (by rfl) ⟨4516377, by rfl⟩ : syracuseStep 12043673 = 9032755) B9032755
theorem B1410471 : Blo 1409524 1410471 := bstep (se 1 (by rfl) ⟨1057853, by rfl⟩ : syracuseStep 1410471 = 2115707) B2115707
theorem B3171833 : Blo 1409524 3171833 := bstep (se 2 (by rfl) ⟨1189437, by rfl⟩ : syracuseStep 3171833 = 2378875) B2378875
theorem B2115065 : Blo 1409524 2115065 := bstep (se 2 (by rfl) ⟨793149, by rfl⟩ : syracuseStep 2115065 = 1586299) B1586299
theorem B1410555 : Blo 1409524 1410555 := bstep (se 1 (by rfl) ⟨1057916, by rfl⟩ : syracuseStep 1410555 = 2115833) B2115833
theorem B1410623 : Blo 1409524 1410623 := bstep (se 1 (by rfl) ⟨1057967, by rfl⟩ : syracuseStep 1410623 = 2115935) B2115935
theorem B1410631 : Blo 1409524 1410631 := bstep (se 1 (by rfl) ⟨1057973, by rfl⟩ : syracuseStep 1410631 = 2115947) B2115947
theorem B3171923 : Blo 1409524 3171923 := bstep (se 1 (by rfl) ⟨2378942, by rfl⟩ : syracuseStep 3171923 = 4757885) B4757885
theorem B7628377 : Blo 1409524 7628377 := bstep (se 2 (by rfl) ⟨2860641, by rfl⟩ : syracuseStep 7628377 = 5721283) B5721283
theorem B2115167 : Blo 1409524 2115167 := bstep (se 1 (by rfl) ⟨1586375, by rfl⟩ : syracuseStep 2115167 = 3172751) B3172751
theorem B1410783 : Blo 1409524 1410783 := bstep (se 1 (by rfl) ⟨1058087, by rfl⟩ : syracuseStep 1410783 = 2116175) B2116175
theorem B3172103 : Blo 1409524 3172103 := bstep (se 1 (by rfl) ⟨2379077, by rfl⟩ : syracuseStep 3172103 = 4758155) B4758155
theorem B1410863 : Blo 1409524 1410863 := bstep (se 1 (by rfl) ⟨1058147, by rfl⟩ : syracuseStep 1410863 = 2116295) B2116295
theorem B2115383 : Blo 1409524 2115383 := bstep (se 1 (by rfl) ⟨1586537, by rfl⟩ : syracuseStep 2115383 = 3173075) B3173075
theorem B4761449 : Blo 1409524 4761449 := bstep (se 2 (by rfl) ⟨1785543, by rfl⟩ : syracuseStep 4761449 = 3571087) B3571087
theorem B1410971 : Blo 1409524 1410971 := bstep (se 1 (by rfl) ⟨1058228, by rfl⟩ : syracuseStep 1410971 = 2116457) B2116457
theorem B6023119 : Blo 1409524 6023119 := bstep (se 1 (by rfl) ⟨4517339, by rfl⟩ : syracuseStep 6023119 = 9034679) B9034679
theorem B1411023 : Blo 1409524 1411023 := bstep (se 1 (by rfl) ⟨1058267, by rfl⟩ : syracuseStep 1411023 = 2116535) B2116535
theorem B1411047 : Blo 1409524 1411047 := bstep (se 1 (by rfl) ⟨1058285, by rfl⟩ : syracuseStep 1411047 = 2116571) B2116571
theorem B2115689 : Blo 1409524 2115689 := bstep (se 2 (by rfl) ⟨793383, by rfl⟩ : syracuseStep 2115689 = 1586767) B1586767
theorem B7145657 : Blo 1409524 7145657 := bstep (se 2 (by rfl) ⟨2679621, by rfl⟩ : syracuseStep 7145657 = 5359243) B5359243
theorem B45746369 : Blo 1409524 45746369 := bstep (se 2 (by rfl) ⟨17154888, by rfl⟩ : syracuseStep 45746369 = 34309777) B34309777
theorem B4516121 : Blo 1409524 4516121 := bstep (se 2 (by rfl) ⟨1693545, by rfl⟩ : syracuseStep 4516121 = 3387091) B3387091
theorem B4761881 : Blo 1409524 4761881 := bstep (se 2 (by rfl) ⟨1785705, by rfl⟩ : syracuseStep 4761881 = 3571411) B3571411
theorem B1526047 : Blo 1409524 1526047 := bstep (se 1 (by rfl) ⟨1144535, by rfl⟩ : syracuseStep 1526047 = 2289071) B2289071
theorem B1411359 : Blo 1409524 1411359 := bstep (se 1 (by rfl) ⟨1058519, by rfl⟩ : syracuseStep 1411359 = 2117039) B2117039
theorem B1411419 : Blo 1409524 1411419 := bstep (se 1 (by rfl) ⟨1058564, by rfl⟩ : syracuseStep 1411419 = 2117129) B2117129
theorem B3172715 : Blo 1409524 3172715 := bstep (se 1 (by rfl) ⟨2379536, by rfl⟩ : syracuseStep 3172715 = 4759073) B4759073
theorem B5294447 : Blo 1409524 5294447 := bstep (se 1 (by rfl) ⟨3970835, by rfl⟩ : syracuseStep 5294447 = 7941671) B7941671
theorem B1411439 : Blo 1409524 1411439 := bstep (se 1 (by rfl) ⟨1058579, by rfl⟩ : syracuseStep 1411439 = 2117159) B2117159
theorem B2116007 : Blo 1409524 2116007 := bstep (se 1 (by rfl) ⟨1587005, by rfl⟩ : syracuseStep 2116007 = 3174011) B3174011
theorem B1411495 : Blo 1409524 1411495 := bstep (se 1 (by rfl) ⟨1058621, by rfl⟩ : syracuseStep 1411495 = 2117243) B2117243
theorem B7137719 : Blo 1409524 7137719 := bstep (se 1 (by rfl) ⟨5353289, by rfl⟩ : syracuseStep 7137719 = 10706579) B10706579
theorem B3172859 : Blo 1409524 3172859 := bstep (se 1 (by rfl) ⟨2379644, by rfl⟩ : syracuseStep 3172859 = 4759289) B4759289
theorem B2116091 : Blo 1409524 2116091 := bstep (se 1 (by rfl) ⟨1587068, by rfl⟩ : syracuseStep 2116091 = 3174137) B3174137
theorem B3172985 : Blo 1409524 3172985 := bstep (se 2 (by rfl) ⟨1189869, by rfl⟩ : syracuseStep 3172985 = 2379739) B2379739
theorem B2116217 : Blo 1409524 2116217 := bstep (se 2 (by rfl) ⟨793581, by rfl⟩ : syracuseStep 2116217 = 1587163) B1587163
theorem B27118253 : Blo 1409524 27118253 := bstep (se 3 (by rfl) ⟨5084672, by rfl⟩ : syracuseStep 27118253 = 10169345) B10169345
theorem B3173039 : Blo 1409524 3173039 := bstep (se 1 (by rfl) ⟨2379779, by rfl⟩ : syracuseStep 3173039 = 4759559) B4759559
theorem B2116271 : Blo 1409524 2116271 := bstep (se 1 (by rfl) ⟨1587203, by rfl⟩ : syracuseStep 2116271 = 3174407) B3174407
theorem B13396691 : Blo 1409524 13396691 := bstep (se 1 (by rfl) ⟨10047518, by rfl⟩ : syracuseStep 13396691 = 20095037) B20095037
theorem B2116319 : Blo 1409524 2116319 := bstep (se 1 (by rfl) ⟨1587239, by rfl⟩ : syracuseStep 2116319 = 3174479) B3174479
theorem B3173111 : Blo 1409524 3173111 := bstep (se 1 (by rfl) ⟨2379833, by rfl⟩ : syracuseStep 3173111 = 4759667) B4759667
theorem B6777719 : Blo 1409524 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B24415147 : Blo 1409524 24415147 := bstep (se 1 (by rfl) ⟨18311360, by rfl⟩ : syracuseStep 24415147 = 36622721) B36622721
theorem B3173291 : Blo 1409524 3173291 := bstep (se 1 (by rfl) ⟨2379968, by rfl⟩ : syracuseStep 3173291 = 4759937) B4759937
theorem B2116583 : Blo 1409524 2116583 := bstep (se 1 (by rfl) ⟨1587437, by rfl⟩ : syracuseStep 2116583 = 3174875) B3174875
theorem B12864527 : Blo 1409524 12864527 := bstep (se 1 (by rfl) ⟨9648395, by rfl⟩ : syracuseStep 12864527 = 19296791) B19296791
theorem B24087617 : Blo 1409524 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B2116841 : Blo 1409524 2116841 := bstep (se 2 (by rfl) ⟨793815, by rfl⟩ : syracuseStep 2116841 = 1587631) B1587631
theorem B2116895 : Blo 1409524 2116895 := bstep (se 1 (by rfl) ⟨1587671, by rfl⟩ : syracuseStep 2116895 = 3175343) B3175343
theorem B2379145 : Blo 1409524 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B2411975 : Blo 1409524 2411975 := bstep (se 1 (by rfl) ⟨1808981, by rfl⟩ : syracuseStep 2411975 = 3617963) B3617963
theorem B3173831 : Blo 1409524 3173831 := bstep (se 1 (by rfl) ⟨2380373, by rfl⟩ : syracuseStep 3173831 = 4760747) B4760747
theorem B2117063 : Blo 1409524 2117063 := bstep (se 1 (by rfl) ⟨1587797, by rfl⟩ : syracuseStep 2117063 = 3175595) B3175595
theorem B10718729 : Blo 1409524 10718729 := bstep (se 2 (by rfl) ⟨4019523, by rfl⟩ : syracuseStep 10718729 = 8039047) B8039047
theorem B4763231 : Blo 1409524 4763231 := bstep (se 1 (by rfl) ⟨3572423, by rfl⟩ : syracuseStep 4763231 = 7144847) B7144847
theorem B24096365 : Blo 1409524 24096365 := bstep (se 3 (by rfl) ⟨4518068, by rfl⟩ : syracuseStep 24096365 = 9036137) B9036137
theorem B25743059 : Blo 1409524 25743059 := bstep (se 1 (by rfl) ⟨19307294, by rfl⟩ : syracuseStep 25743059 = 38614589) B38614589
theorem B3174191 : Blo 1409524 3174191 := bstep (se 1 (by rfl) ⟨2380643, by rfl⟩ : syracuseStep 3174191 = 4761287) B4761287
theorem B2379577 : Blo 1409524 2379577 := bstep (se 2 (by rfl) ⟨892341, by rfl⟩ : syracuseStep 2379577 = 1784683) B1784683
theorem B6025117 : Blo 1409524 6025117 := bstep (se 3 (by rfl) ⟨1129709, by rfl⟩ : syracuseStep 6025117 = 2259419) B2259419
theorem B10170269 : Blo 1409524 10170269 := bstep (se 3 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 10170269 = 3813851) B3813851
theorem B11440129 : Blo 1409524 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B4517993 : Blo 1409524 4517993 := bstep (se 2 (by rfl) ⟨1694247, by rfl⟩ : syracuseStep 4517993 = 3388495) B3388495
theorem B2379881 : Blo 1409524 2379881 := bstep (se 2 (by rfl) ⟨892455, by rfl⟩ : syracuseStep 2379881 = 1784911) B1784911
theorem B13922563 : Blo 1409524 13922563 := bstep (se 1 (by rfl) ⟨10441922, by rfl⟩ : syracuseStep 13922563 = 20883845) B20883845
theorem B4288859 : Blo 1409524 4288859 := bstep (se 1 (by rfl) ⟨3216644, by rfl⟩ : syracuseStep 4288859 = 6433289) B6433289
theorem B3305819 : Blo 1409524 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B3174767 : Blo 1409524 3174767 := bstep (se 1 (by rfl) ⟨2381075, by rfl⟩ : syracuseStep 3174767 = 4762151) B4762151
theorem B3174839 : Blo 1409524 3174839 := bstep (se 1 (by rfl) ⟨2381129, by rfl⟩ : syracuseStep 3174839 = 4762259) B4762259
theorem B3387899 : Blo 1409524 3387899 := bstep (se 1 (by rfl) ⟨2540924, by rfl⟩ : syracuseStep 3387899 = 5081849) B5081849
theorem B5083667 : Blo 1409524 5083667 := bstep (se 1 (by rfl) ⟨3812750, by rfl⟩ : syracuseStep 5083667 = 7625501) B7625501
theorem B3174983 : Blo 1409524 3174983 := bstep (se 1 (by rfl) ⟨2381237, by rfl⟩ : syracuseStep 3174983 = 4762475) B4762475
theorem B3813961 : Blo 1409524 3813961 := bstep (se 2 (by rfl) ⟨1430235, by rfl⟩ : syracuseStep 3813961 = 2860471) B2860471
theorem B1585759 : Blo 1409524 1585759 := bstep (se 1 (by rfl) ⟨1189319, by rfl⟩ : syracuseStep 1585759 = 2378639) B2378639
theorem B3175019 : Blo 1409524 3175019 := bstep (se 1 (by rfl) ⟨2381264, by rfl⟩ : syracuseStep 3175019 = 4762529) B4762529
theorem B7139987 : Blo 1409524 7139987 := bstep (se 1 (by rfl) ⟨5354990, by rfl⟩ : syracuseStep 7139987 = 10709981) B10709981
theorem B2290351 : Blo 1409524 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B3437239 : Blo 1409524 3437239 := bstep (se 1 (by rfl) ⟨2577929, by rfl⟩ : syracuseStep 3437239 = 5155859) B5155859
theorem B3175415 : Blo 1409524 3175415 := bstep (se 1 (by rfl) ⟨2381561, by rfl⟩ : syracuseStep 3175415 = 4763123) B4763123
theorem B3814543 : Blo 1409524 3814543 := bstep (se 1 (by rfl) ⟨2860907, by rfl⟩ : syracuseStep 3814543 = 5721815) B5721815
theorem B40662161 : Blo 1409524 40662161 := bstep (se 2 (by rfl) ⟨15248310, by rfl⟩ : syracuseStep 40662161 = 30496621) B30496621
theorem B3011833 : Blo 1409524 3011833 := bstep (se 2 (by rfl) ⟨1129437, by rfl⟩ : syracuseStep 3011833 = 2258875) B2258875
theorem B2676007 : Blo 1409524 2676007 := bstep (se 1 (by rfl) ⟨2007005, by rfl⟩ : syracuseStep 2676007 = 4014011) B4014011
theorem B3175775 : Blo 1409524 3175775 := bstep (se 1 (by rfl) ⟨2381831, by rfl⟩ : syracuseStep 3175775 = 4763663) B4763663
theorem B2676091 : Blo 1409524 2676091 := bstep (se 1 (by rfl) ⟨2007068, by rfl⟩ : syracuseStep 2676091 = 4014137) B4014137
theorem B7140797 : Blo 1409524 7140797 := bstep (se 3 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 7140797 = 2677799) B2677799
theorem B2381305 : Blo 1409524 2381305 := bstep (se 2 (by rfl) ⟨892989, by rfl⟩ : syracuseStep 2381305 = 1785979) B1785979
theorem B1717831 : Blo 1409524 1717831 := bstep (se 1 (by rfl) ⟨1288373, by rfl⟩ : syracuseStep 1717831 = 2576747) B2576747
theorem B1586911 : Blo 1409524 1586911 := bstep (se 1 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 1586911 = 2380367) B2380367
theorem B2381575 : Blo 1409524 2381575 := bstep (se 1 (by rfl) ⟨1786181, by rfl⟩ : syracuseStep 2381575 = 3572363) B3572363
theorem B2381609 : Blo 1409524 2381609 := bstep (se 2 (by rfl) ⟨893103, by rfl⟩ : syracuseStep 2381609 = 1786207) B1786207
theorem B13555745 : Blo 1409524 13555745 := bstep (se 2 (by rfl) ⟨5083404, by rfl⟩ : syracuseStep 13555745 = 10166809) B10166809
theorem B21706795 : Blo 1409524 21706795 := bstep (se 1 (by rfl) ⟨16280096, by rfl⟩ : syracuseStep 21706795 = 32560193) B32560193
theorem B1587487 : Blo 1409524 1587487 := bstep (se 1 (by rfl) ⟨1190615, by rfl⟩ : syracuseStep 1587487 = 2381231) B2381231
theorem B1505575 : Blo 1409524 1505575 := bstep (se 1 (by rfl) ⟨1129181, by rfl⟩ : syracuseStep 1505575 = 2258363) B2258363
theorem B1505647 : Blo 1409524 1505647 := bstep (se 1 (by rfl) ⟨1129235, by rfl⟩ : syracuseStep 1505647 = 2258471) B2258471
theorem B6781295 : Blo 1409524 6781295 := bstep (se 1 (by rfl) ⟨5085971, by rfl⟩ : syracuseStep 6781295 = 10171943) B10171943
theorem B6109607 : Blo 1409524 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B3570095 : Blo 1409524 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B1784263 : Blo 1409524 1784263 := bstep (se 1 (by rfl) ⟨1338197, by rfl⟩ : syracuseStep 1784263 = 2676395) B2676395
theorem B3054035 : Blo 1409524 3054035 := bstep (se 1 (by rfl) ⟨2290526, by rfl⟩ : syracuseStep 3054035 = 4581053) B4581053
theorem B13548055 : Blo 1409524 13548055 := bstep (se 1 (by rfl) ⟨10161041, by rfl⟩ : syracuseStep 13548055 = 20322083) B20322083
theorem B1587775 : Blo 1409524 1587775 := bstep (se 1 (by rfl) ⟨1190831, by rfl⟩ : syracuseStep 1587775 = 2381663) B2381663
theorem B3480137 : Blo 1409524 3480137 := bstep (se 2 (by rfl) ⟨1305051, by rfl⟩ : syracuseStep 3480137 = 2610103) B2610103
theorem B4758263 : Blo 1409524 4758263 := bstep (se 1 (by rfl) ⟨3568697, by rfl⟩ : syracuseStep 4758263 = 7137395) B7137395
theorem B13564745 : Blo 1409524 13564745 := bstep (se 2 (by rfl) ⟨5086779, by rfl⟩ : syracuseStep 13564745 = 10173559) B10173559
theorem B1694695 : Blo 1409524 1694695 := bstep (se 1 (by rfl) ⟨1271021, by rfl⟩ : syracuseStep 1694695 = 2542043) B2542043
theorem B77225021 : Blo 1409524 77225021 := bstep (se 3 (by rfl) ⟨14479691, by rfl⟩ : syracuseStep 77225021 = 28959383) B28959383
theorem B2260111 : Blo 1409524 2260111 := bstep (se 1 (by rfl) ⟨1695083, by rfl⟩ : syracuseStep 2260111 = 3390167) B3390167
theorem B9043109 : Blo 1409524 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B12057821 : Blo 1409524 12057821 := bstep (se 3 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 12057821 = 4521683) B4521683
theorem B1785179 : Blo 1409524 1785179 := bstep (se 1 (by rfl) ⟨1338884, by rfl⟩ : syracuseStep 1785179 = 2677769) B2677769
theorem B3054943 : Blo 1409524 3054943 := bstep (se 1 (by rfl) ⟨2291207, by rfl⟩ : syracuseStep 3054943 = 4582415) B4582415
theorem B3571067 : Blo 1409524 3571067 := bstep (se 1 (by rfl) ⟨2678300, by rfl⟩ : syracuseStep 3571067 = 5356601) B5356601
theorem B18071045 : Blo 1409524 18071045 := bstep (se 4 (by rfl) ⟨1694160, by rfl⟩ : syracuseStep 18071045 = 3388321) B3388321
theorem B7233133 : Blo 1409524 7233133 := bstep (se 3 (by rfl) ⟨1356212, by rfl⟩ : syracuseStep 7233133 = 2712425) B2712425
theorem B3571361 : Blo 1409524 3571361 := bstep (se 2 (by rfl) ⟨1339260, by rfl⟩ : syracuseStep 3571361 = 2678521) B2678521
theorem B4759343 : Blo 1409524 4759343 := bstep (se 1 (by rfl) ⟨3569507, by rfl⟩ : syracuseStep 4759343 = 7139015) B7139015
theorem B1785655 : Blo 1409524 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B5799737 : Blo 1409524 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B6782777 : Blo 1409524 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B43417417 : Blo 1409524 43417417 := bstep (se 2 (by rfl) ⟨16281531, by rfl⟩ : syracuseStep 43417417 = 32563063) B32563063
theorem B24100739 : Blo 1409524 24100739 := bstep (se 1 (by rfl) ⟨18075554, by rfl⟩ : syracuseStep 24100739 = 36151109) B36151109
theorem B15253505 : Blo 1409524 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B28942393 : Blo 1409524 28942393 := bstep (se 2 (by rfl) ⟨10853397, by rfl⟩ : syracuseStep 28942393 = 21706795) B21706795
theorem B2859239 : Blo 1409524 2859239 := bstep (se 1 (by rfl) ⟨2144429, by rfl⟩ : syracuseStep 2859239 = 4288859) B4288859
theorem B18563417 : Blo 1409524 18563417 := bstep (se 2 (by rfl) ⟨6961281, by rfl⟩ : syracuseStep 18563417 = 13922563) B13922563
theorem B2007433 : Blo 1409524 2007433 := bstep (se 2 (by rfl) ⟨752787, by rfl⟩ : syracuseStep 2007433 = 1505575) B1505575
theorem B4759991 : Blo 1409524 4759991 := bstep (se 1 (by rfl) ⟨3569993, by rfl⟩ : syracuseStep 4759991 = 7139987) B7139987
theorem B4014535 : Blo 1409524 4014535 := bstep (se 1 (by rfl) ⟨3010901, by rfl⟩ : syracuseStep 4014535 = 6021803) B6021803
theorem B3572201 : Blo 1409524 3572201 := bstep (se 2 (by rfl) ⟨1339575, by rfl⟩ : syracuseStep 3572201 = 2679151) B2679151
theorem B1409639 : Blo 1409524 1409639 := bstep (se 1 (by rfl) ⟨1057229, by rfl⟩ : syracuseStep 1409639 = 2114459) B2114459
theorem B18064073 : Blo 1409524 18064073 := bstep (se 2 (by rfl) ⟨6774027, by rfl⟩ : syracuseStep 18064073 = 13548055) B13548055
theorem B12042989 : Blo 1409524 12042989 := bstep (se 3 (by rfl) ⟨2258060, by rfl⟩ : syracuseStep 12042989 = 4516121) B4516121
theorem B27108107 : Blo 1409524 27108107 := bstep (se 1 (by rfl) ⟨20331080, by rfl⟩ : syracuseStep 27108107 = 40662161) B40662161
theorem B2114345 : Blo 1409524 2114345 := bstep (se 2 (by rfl) ⟨792879, by rfl⟩ : syracuseStep 2114345 = 1585759) B1585759
theorem B2114351 : Blo 1409524 2114351 := bstep (se 1 (by rfl) ⟨1585763, by rfl⟩ : syracuseStep 2114351 = 3171527) B3171527
theorem B1409903 : Blo 1409524 1409903 := bstep (se 1 (by rfl) ⟨1057427, by rfl⟩ : syracuseStep 1409903 = 2114855) B2114855
theorem B4760477 : Blo 1409524 4760477 := bstep (se 3 (by rfl) ⟨892589, by rfl⟩ : syracuseStep 4760477 = 1785179) B1785179
theorem B8815517 : Blo 1409524 8815517 := bstep (se 3 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 8815517 = 3305819) B3305819
theorem B2114471 : Blo 1409524 2114471 := bstep (se 1 (by rfl) ⟨1585853, by rfl⟩ : syracuseStep 2114471 = 3171707) B3171707
theorem B1409959 : Blo 1409524 1409959 := bstep (se 1 (by rfl) ⟨1057469, by rfl⟩ : syracuseStep 1409959 = 2114939) B2114939
theorem B8029115 : Blo 1409524 8029115 := bstep (se 1 (by rfl) ⟨6021836, by rfl⟩ : syracuseStep 8029115 = 12043673) B12043673
theorem B4760531 : Blo 1409524 4760531 := bstep (se 1 (by rfl) ⟨3570398, by rfl⟩ : syracuseStep 4760531 = 7140797) B7140797
theorem B2114555 : Blo 1409524 2114555 := bstep (se 1 (by rfl) ⟨1585916, by rfl⟩ : syracuseStep 2114555 = 3171833) B3171833
theorem B1410043 : Blo 1409524 1410043 := bstep (se 1 (by rfl) ⟨1057532, by rfl⟩ : syracuseStep 1410043 = 2115065) B2115065
theorem B2114615 : Blo 1409524 2114615 := bstep (se 1 (by rfl) ⟨1585961, by rfl⟩ : syracuseStep 2114615 = 3171923) B3171923
theorem B1410111 : Blo 1409524 1410111 := bstep (se 1 (by rfl) ⟨1057583, by rfl⟩ : syracuseStep 1410111 = 2115167) B2115167
theorem B2114735 : Blo 1409524 2114735 := bstep (se 1 (by rfl) ⟨1586051, by rfl⟩ : syracuseStep 2114735 = 3172103) B3172103
theorem B6431933 : Blo 1409524 6431933 := bstep (se 3 (by rfl) ⟨1205987, by rfl⟩ : syracuseStep 6431933 = 2411975) B2411975
theorem B1410255 : Blo 1409524 1410255 := bstep (se 1 (by rfl) ⟨1057691, by rfl⟩ : syracuseStep 1410255 = 2115383) B2115383
theorem B9037163 : Blo 1409524 9037163 := bstep (se 1 (by rfl) ⟨6777872, by rfl⟩ : syracuseStep 9037163 = 13555745) B13555745
theorem B1410459 : Blo 1409524 1410459 := bstep (se 1 (by rfl) ⟨1057844, by rfl⟩ : syracuseStep 1410459 = 2115689) B2115689
theorem B2115143 : Blo 1409524 2115143 := bstep (se 1 (by rfl) ⟨1586357, by rfl⟩ : syracuseStep 2115143 = 3172715) B3172715
theorem B1410671 : Blo 1409524 1410671 := bstep (se 1 (by rfl) ⟨1058003, by rfl⟩ : syracuseStep 1410671 = 2116007) B2116007
theorem B4015777 : Blo 1409524 4015777 := bstep (se 2 (by rfl) ⟨1505916, by rfl⟩ : syracuseStep 4015777 = 3011833) B3011833
theorem B2115239 : Blo 1409524 2115239 := bstep (se 1 (by rfl) ⟨1586429, by rfl⟩ : syracuseStep 2115239 = 3172859) B3172859
theorem B1410727 : Blo 1409524 1410727 := bstep (se 1 (by rfl) ⟨1058045, by rfl⟩ : syracuseStep 1410727 = 2116091) B2116091
theorem B2320091 : Blo 1409524 2320091 := bstep (se 1 (by rfl) ⟨1740068, by rfl⟩ : syracuseStep 2320091 = 3480137) B3480137
theorem B2115323 : Blo 1409524 2115323 := bstep (se 1 (by rfl) ⟨1586492, by rfl⟩ : syracuseStep 2115323 = 3172985) B3172985
theorem B1410811 : Blo 1409524 1410811 := bstep (se 1 (by rfl) ⟨1058108, by rfl⟩ : syracuseStep 1410811 = 2116217) B2116217
theorem B2115359 : Blo 1409524 2115359 := bstep (se 1 (by rfl) ⟨1586519, by rfl⟩ : syracuseStep 2115359 = 3173039) B3173039
theorem B1410847 : Blo 1409524 1410847 := bstep (se 1 (by rfl) ⟨1058135, by rfl⟩ : syracuseStep 1410847 = 2116271) B2116271
theorem B4073257 : Blo 1409524 4073257 := bstep (se 2 (by rfl) ⟨1527471, by rfl⟩ : syracuseStep 4073257 = 3054943) B3054943
theorem B1410879 : Blo 1409524 1410879 := bstep (se 1 (by rfl) ⟨1058159, by rfl⟩ : syracuseStep 1410879 = 2116319) B2116319
theorem B3172175 : Blo 1409524 3172175 := bstep (se 1 (by rfl) ⟨2379131, by rfl⟩ : syracuseStep 3172175 = 4758263) B4758263
theorem B2115407 : Blo 1409524 2115407 := bstep (se 1 (by rfl) ⟨1586555, by rfl⟩ : syracuseStep 2115407 = 3173111) B3173111
theorem B3172193 : Blo 1409524 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B8030117 : Blo 1409524 8030117 := bstep (se 4 (by rfl) ⟨752823, by rfl⟩ : syracuseStep 8030117 = 1505647) B1505647
theorem B2115527 : Blo 1409524 2115527 := bstep (se 1 (by rfl) ⟨1586645, by rfl⟩ : syracuseStep 2115527 = 3173291) B3173291
theorem B1411055 : Blo 1409524 1411055 := bstep (se 1 (by rfl) ⟨1058291, by rfl⟩ : syracuseStep 1411055 = 2116583) B2116583
theorem B16058411 : Blo 1409524 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B9644177 : Blo 1409524 9644177 := bstep (se 2 (by rfl) ⟨3616566, by rfl⟩ : syracuseStep 9644177 = 7233133) B7233133
theorem B8038547 : Blo 1409524 8038547 := bstep (se 1 (by rfl) ⟨6028910, by rfl⟩ : syracuseStep 8038547 = 12057821) B12057821
theorem B1411227 : Blo 1409524 1411227 := bstep (se 1 (by rfl) ⟨1058420, by rfl⟩ : syracuseStep 1411227 = 2116841) B2116841
theorem B1411263 : Blo 1409524 1411263 := bstep (se 1 (by rfl) ⟨1058447, by rfl⟩ : syracuseStep 1411263 = 2116895) B2116895
theorem B130214117 : Blo 1409524 130214117 := bstep (se 4 (by rfl) ⟨12207573, by rfl⟩ : syracuseStep 130214117 = 24415147) B24415147
theorem B2115881 : Blo 1409524 2115881 := bstep (se 2 (by rfl) ⟨793455, by rfl⟩ : syracuseStep 2115881 = 1586911) B1586911
theorem B2115887 : Blo 1409524 2115887 := bstep (se 1 (by rfl) ⟨1586915, by rfl⟩ : syracuseStep 2115887 = 3173831) B3173831
theorem B1411375 : Blo 1409524 1411375 := bstep (se 1 (by rfl) ⟨1058531, by rfl⟩ : syracuseStep 1411375 = 2117063) B2117063
theorem B7145819 : Blo 1409524 7145819 := bstep (se 1 (by rfl) ⟨5359364, by rfl⟩ : syracuseStep 7145819 = 10718729) B10718729
theorem B3172769 : Blo 1409524 3172769 := bstep (se 2 (by rfl) ⟨1189788, by rfl⟩ : syracuseStep 3172769 = 2379577) B2379577
theorem B3172895 : Blo 1409524 3172895 := bstep (se 1 (by rfl) ⟨2379671, by rfl⟩ : syracuseStep 3172895 = 4759343) B4759343
theorem B2116127 : Blo 1409524 2116127 := bstep (se 1 (by rfl) ⟨1587095, by rfl⟩ : syracuseStep 2116127 = 3174191) B3174191
theorem B16067159 : Blo 1409524 16067159 := bstep (se 1 (by rfl) ⟨12050369, by rfl⟩ : syracuseStep 16067159 = 24100739) B24100739
theorem B8030825 : Blo 1409524 8030825 := bstep (se 2 (by rfl) ⟨3011559, by rfl⟩ : syracuseStep 8030825 = 6023119) B6023119
theorem B2116511 : Blo 1409524 2116511 := bstep (se 1 (by rfl) ⟨1587383, by rfl⟩ : syracuseStep 2116511 = 3174767) B3174767
theorem B2116559 : Blo 1409524 2116559 := bstep (se 1 (by rfl) ⟨1587419, by rfl⟩ : syracuseStep 2116559 = 3174839) B3174839
theorem B36137987 : Blo 1409524 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B9161765 : Blo 1409524 9161765 := bstep (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) B1717831
theorem B2116649 : Blo 1409524 2116649 := bstep (se 2 (by rfl) ⟨793743, by rfl⟩ : syracuseStep 2116649 = 1587487) B1587487
theorem B2116655 : Blo 1409524 2116655 := bstep (se 1 (by rfl) ⟨1587491, by rfl⟩ : syracuseStep 2116655 = 3174983) B3174983
theorem B2116679 : Blo 1409524 2116679 := bstep (se 1 (by rfl) ⟨1587509, by rfl⟩ : syracuseStep 2116679 = 3175019) B3175019
theorem B4762745 : Blo 1409524 4762745 := bstep (se 2 (by rfl) ⟨1786029, by rfl⟩ : syracuseStep 4762745 = 3572059) B3572059
theorem B2379017 : Blo 1409524 2379017 := bstep (se 2 (by rfl) ⟨892131, by rfl⟩ : syracuseStep 2379017 = 1784263) B1784263
theorem B2116943 : Blo 1409524 2116943 := bstep (se 1 (by rfl) ⟨1587707, by rfl⟩ : syracuseStep 2116943 = 3175415) B3175415
theorem B2117033 : Blo 1409524 2117033 := bstep (se 2 (by rfl) ⟨793887, by rfl⟩ : syracuseStep 2117033 = 1587775) B1587775
theorem B4763069 : Blo 1409524 4763069 := bstep (se 3 (by rfl) ⟨893075, by rfl⟩ : syracuseStep 4763069 = 1786151) B1786151
theorem B2117183 : Blo 1409524 2117183 := bstep (se 1 (by rfl) ⟨1587887, by rfl⟩ : syracuseStep 2117183 = 3175775) B3175775
theorem B4582985 : Blo 1409524 4582985 := bstep (se 2 (by rfl) ⟨1718619, by rfl⟩ : syracuseStep 4582985 = 3437239) B3437239
theorem B3174299 : Blo 1409524 3174299 := bstep (se 1 (by rfl) ⟨2380724, by rfl⟩ : syracuseStep 3174299 = 4761449) B4761449
theorem B16068617 : Blo 1409524 16068617 := bstep (se 2 (by rfl) ⟨6025731, by rfl⟩ : syracuseStep 16068617 = 12051463) B12051463
theorem B4763771 : Blo 1409524 4763771 := bstep (se 1 (by rfl) ⟨3572828, by rfl⟩ : syracuseStep 4763771 = 7145657) B7145657
theorem B8138917 : Blo 1409524 8138917 := bstep (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) B1526047
theorem B3174587 : Blo 1409524 3174587 := bstep (se 1 (by rfl) ⟨2380940, by rfl⟩ : syracuseStep 3174587 = 4761881) B4761881
theorem B2380063 : Blo 1409524 2380063 := bstep (se 1 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 2380063 = 3570095) B3570095
theorem B2036023 : Blo 1409524 2036023 := bstep (se 1 (by rfl) ⟨1527017, by rfl⟩ : syracuseStep 2036023 = 3054035) B3054035
theorem B3568009 : Blo 1409524 3568009 := bstep (se 2 (by rfl) ⟨1338003, by rfl⟩ : syracuseStep 3568009 = 2676007) B2676007
theorem B3568121 : Blo 1409524 3568121 := bstep (se 2 (by rfl) ⟨1338045, by rfl⟩ : syracuseStep 3568121 = 2676091) B2676091
theorem B4518479 : Blo 1409524 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B3175073 : Blo 1409524 3175073 := bstep (se 2 (by rfl) ⟨1190652, by rfl⟩ : syracuseStep 3175073 = 2381305) B2381305
theorem B51483347 : Blo 1409524 51483347 := bstep (se 1 (by rfl) ⟨38612510, by rfl⟩ : syracuseStep 51483347 = 77225021) B77225021
theorem B10171169 : Blo 1409524 10171169 := bstep (se 2 (by rfl) ⟨3814188, by rfl⟩ : syracuseStep 10171169 = 7628377) B7628377
theorem B2380711 : Blo 1409524 2380711 := bstep (se 1 (by rfl) ⟨1785533, by rfl⟩ : syracuseStep 2380711 = 3571067) B3571067
theorem B12047363 : Blo 1409524 12047363 := bstep (se 1 (by rfl) ⟨9035522, by rfl⟩ : syracuseStep 12047363 = 18071045) B18071045
theorem B3175433 : Blo 1409524 3175433 := bstep (se 2 (by rfl) ⟨1190787, by rfl⟩ : syracuseStep 3175433 = 2381575) B2381575
theorem B3175487 : Blo 1409524 3175487 := bstep (se 1 (by rfl) ⟨2381615, by rfl⟩ : syracuseStep 3175487 = 4763231) B4763231
theorem B2380873 : Blo 1409524 2380873 := bstep (se 2 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 2380873 = 1785655) B1785655
theorem B57889889 : Blo 1409524 57889889 := bstep (se 2 (by rfl) ⟨21708708, by rfl⟩ : syracuseStep 57889889 = 43417417) B43417417
theorem B2380907 : Blo 1409524 2380907 := bstep (se 1 (by rfl) ⟨1785680, by rfl⟩ : syracuseStep 2380907 = 3571361) B3571361
theorem B8033489 : Blo 1409524 8033489 := bstep (se 2 (by rfl) ⟨3012558, by rfl⟩ : syracuseStep 8033489 = 6025117) B6025117
theorem B6780179 : Blo 1409524 6780179 := bstep (se 1 (by rfl) ⟨5085134, by rfl⟩ : syracuseStep 6780179 = 10170269) B10170269
theorem B3011995 : Blo 1409524 3011995 := bstep (se 1 (by rfl) ⟨2258996, by rfl⟩ : syracuseStep 3011995 = 4517993) B4517993
theorem B1586587 : Blo 1409524 1586587 := bstep (se 1 (by rfl) ⟨1189940, by rfl⟩ : syracuseStep 1586587 = 2379881) B2379881
theorem B2258599 : Blo 1409524 2258599 := bstep (se 1 (by rfl) ⟨1693949, by rfl⟩ : syracuseStep 2258599 = 3387899) B3387899
theorem B3389111 : Blo 1409524 3389111 := bstep (se 1 (by rfl) ⟨2541833, by rfl⟩ : syracuseStep 3389111 = 5083667) B5083667
theorem B5085281 : Blo 1409524 5085281 := bstep (se 2 (by rfl) ⟨1906980, by rfl⟩ : syracuseStep 5085281 = 3813961) B3813961
theorem B3053801 : Blo 1409524 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B16292285 : Blo 1409524 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B1587739 : Blo 1409524 1587739 := bstep (se 1 (by rfl) ⟨1190804, by rfl⟩ : syracuseStep 1587739 = 2381609) B2381609
theorem B2259593 : Blo 1409524 2259593 := bstep (se 2 (by rfl) ⟨847347, by rfl⟩ : syracuseStep 2259593 = 1694695) B1694695
theorem B9165449 : Blo 1409524 9165449 := bstep (se 2 (by rfl) ⟨3437043, by rfl⟩ : syracuseStep 9165449 = 6874087) B6874087
theorem B30497579 : Blo 1409524 30497579 := bstep (se 1 (by rfl) ⟨22873184, by rfl⟩ : syracuseStep 30497579 = 45746369) B45746369
theorem B3013481 : Blo 1409524 3013481 := bstep (se 2 (by rfl) ⟨1130055, by rfl⟩ : syracuseStep 3013481 = 2260111) B2260111
theorem B5086057 : Blo 1409524 5086057 := bstep (se 2 (by rfl) ⟨1907271, by rfl⟩ : syracuseStep 5086057 = 3814543) B3814543
theorem B3529631 : Blo 1409524 3529631 := bstep (se 1 (by rfl) ⟨2647223, by rfl⟩ : syracuseStep 3529631 = 5294447) B5294447
theorem B4520863 : Blo 1409524 4520863 := bstep (se 1 (by rfl) ⟨3390647, by rfl⟩ : syracuseStep 4520863 = 6781295) B6781295
theorem B4758479 : Blo 1409524 4758479 := bstep (se 1 (by rfl) ⟨3568859, by rfl⟩ : syracuseStep 4758479 = 7137719) B7137719
theorem B18078835 : Blo 1409524 18078835 := bstep (se 1 (by rfl) ⟨13559126, by rfl⟩ : syracuseStep 18078835 = 27118253) B27118253
theorem B9043163 : Blo 1409524 9043163 := bstep (se 1 (by rfl) ⟨6782372, by rfl⟩ : syracuseStep 9043163 = 13564745) B13564745
theorem B35724509 : Blo 1409524 35724509 := bstep (se 3 (by rfl) ⟨6698345, by rfl⟩ : syracuseStep 35724509 = 13396691) B13396691
theorem B8576351 : Blo 1409524 8576351 := bstep (se 1 (by rfl) ⟨6432263, by rfl⟩ : syracuseStep 8576351 = 12864527) B12864527
theorem B6028739 : Blo 1409524 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B16064243 : Blo 1409524 16064243 := bstep (se 1 (by rfl) ⟨12048182, by rfl⟩ : syracuseStep 16064243 = 24096365) B24096365
theorem B17162039 : Blo 1409524 17162039 := bstep (se 1 (by rfl) ⟨12871529, by rfl⟩ : syracuseStep 17162039 = 25743059) B25743059
theorem B3866491 : Blo 1409524 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B4521851 : Blo 1409524 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B12042715 : Blo 1409524 12042715 := bstep (se 1 (by rfl) ⟨9032036, by rfl⟩ : syracuseStep 12042715 = 18064073) B18064073
theorem B8028659 : Blo 1409524 8028659 := bstep (se 1 (by rfl) ⟨6021494, by rfl⟩ : syracuseStep 8028659 = 12042989) B12042989
theorem B18072071 : Blo 1409524 18072071 := bstep (se 1 (by rfl) ⟨13554053, by rfl⟩ : syracuseStep 18072071 = 27108107) B27108107
theorem B1409563 : Blo 1409524 1409563 := bstep (se 1 (by rfl) ⟨1057172, by rfl⟩ : syracuseStep 1409563 = 2114345) B2114345
theorem B1409567 : Blo 1409524 1409567 := bstep (se 1 (by rfl) ⟨1057175, by rfl⟩ : syracuseStep 1409567 = 2114351) B2114351
theorem B1409647 : Blo 1409524 1409647 := bstep (se 1 (by rfl) ⟨1057235, by rfl⟩ : syracuseStep 1409647 = 2114471) B2114471
theorem B1409703 : Blo 1409524 1409703 := bstep (se 1 (by rfl) ⟨1057277, by rfl⟩ : syracuseStep 1409703 = 2114555) B2114555
theorem B1409743 : Blo 1409524 1409743 := bstep (se 1 (by rfl) ⟨1057307, by rfl⟩ : syracuseStep 1409743 = 2114615) B2114615
theorem B38593259 : Blo 1409524 38593259 := bstep (se 1 (by rfl) ⟨28944944, by rfl⟩ : syracuseStep 38593259 = 57889889) B57889889
theorem B1409823 : Blo 1409524 1409823 := bstep (se 1 (by rfl) ⟨1057367, by rfl⟩ : syracuseStep 1409823 = 2114735) B2114735
theorem B1410095 : Blo 1409524 1410095 := bstep (se 1 (by rfl) ⟨1057571, by rfl⟩ : syracuseStep 1410095 = 2115143) B2115143
theorem B1410159 : Blo 1409524 1410159 := bstep (se 1 (by rfl) ⟨1057619, by rfl⟩ : syracuseStep 1410159 = 2115239) B2115239
theorem B1410215 : Blo 1409524 1410215 := bstep (se 1 (by rfl) ⟨1057661, by rfl⟩ : syracuseStep 1410215 = 2115323) B2115323
theorem B1410239 : Blo 1409524 1410239 := bstep (se 1 (by rfl) ⟨1057679, by rfl⟩ : syracuseStep 1410239 = 2115359) B2115359
theorem B2114783 : Blo 1409524 2114783 := bstep (se 1 (by rfl) ⟨1586087, by rfl⟩ : syracuseStep 2114783 = 3172175) B3172175
theorem B1410271 : Blo 1409524 1410271 := bstep (se 1 (by rfl) ⟨1057703, by rfl⟩ : syracuseStep 1410271 = 2115407) B2115407
theorem B2114795 : Blo 1409524 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B1410351 : Blo 1409524 1410351 := bstep (se 1 (by rfl) ⟨1057763, by rfl⟩ : syracuseStep 1410351 = 2115527) B2115527
theorem B5359031 : Blo 1409524 5359031 := bstep (se 1 (by rfl) ⟨4019273, by rfl⟩ : syracuseStep 5359031 = 8038547) B8038547
theorem B1410587 : Blo 1409524 1410587 := bstep (se 1 (by rfl) ⟨1057940, by rfl⟩ : syracuseStep 1410587 = 2115881) B2115881
theorem B1410591 : Blo 1409524 1410591 := bstep (se 1 (by rfl) ⟨1057943, by rfl⟩ : syracuseStep 1410591 = 2115887) B2115887
theorem B2115179 : Blo 1409524 2115179 := bstep (se 1 (by rfl) ⟨1586384, by rfl⟩ : syracuseStep 2115179 = 3172769) B3172769
theorem B2115263 : Blo 1409524 2115263 := bstep (se 1 (by rfl) ⟨1586447, by rfl⟩ : syracuseStep 2115263 = 3172895) B3172895
theorem B1410751 : Blo 1409524 1410751 := bstep (se 1 (by rfl) ⟨1058063, by rfl⟩ : syracuseStep 1410751 = 2116127) B2116127
theorem B4015993 : Blo 1409524 4015993 := bstep (se 2 (by rfl) ⟨1505997, by rfl⟩ : syracuseStep 4015993 = 3011995) B3011995
theorem B2115449 : Blo 1409524 2115449 := bstep (se 2 (by rfl) ⟨793293, by rfl⟩ : syracuseStep 2115449 = 1586587) B1586587
theorem B2353087 : Blo 1409524 2353087 := bstep (se 1 (by rfl) ⟨1764815, by rfl⟩ : syracuseStep 2353087 = 3529631) B3529631
theorem B1411007 : Blo 1409524 1411007 := bstep (se 1 (by rfl) ⟨1058255, by rfl⟩ : syracuseStep 1411007 = 2116511) B2116511
theorem B3172319 : Blo 1409524 3172319 := bstep (se 1 (by rfl) ⟨2379239, by rfl⟩ : syracuseStep 3172319 = 4758479) B4758479
theorem B1411039 : Blo 1409524 1411039 := bstep (se 1 (by rfl) ⟨1058279, by rfl⟩ : syracuseStep 1411039 = 2116559) B2116559
theorem B1411099 : Blo 1409524 1411099 := bstep (se 1 (by rfl) ⟨1058324, by rfl⟩ : syracuseStep 1411099 = 2116649) B2116649
theorem B1411103 : Blo 1409524 1411103 := bstep (se 1 (by rfl) ⟨1058327, by rfl⟩ : syracuseStep 1411103 = 2116655) B2116655
theorem B1411119 : Blo 1409524 1411119 := bstep (se 1 (by rfl) ⟨1058339, by rfl⟩ : syracuseStep 1411119 = 2116679) B2116679
theorem B23816339 : Blo 1409524 23816339 := bstep (se 1 (by rfl) ⟨17862254, by rfl⟩ : syracuseStep 23816339 = 35724509) B35724509
theorem B1411295 : Blo 1409524 1411295 := bstep (se 1 (by rfl) ⟨1058471, by rfl⟩ : syracuseStep 1411295 = 2116943) B2116943
theorem B1411355 : Blo 1409524 1411355 := bstep (se 1 (by rfl) ⟨1058516, by rfl⟩ : syracuseStep 1411355 = 2117033) B2117033
theorem B1411455 : Blo 1409524 1411455 := bstep (se 1 (by rfl) ⟨1058591, by rfl⟩ : syracuseStep 1411455 = 2117183) B2117183
theorem B10709495 : Blo 1409524 10709495 := bstep (se 1 (by rfl) ⟨8032121, by rfl⟩ : syracuseStep 10709495 = 16064243) B16064243
theorem B5155321 : Blo 1409524 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B2116199 : Blo 1409524 2116199 := bstep (se 1 (by rfl) ⟨1587149, by rfl⟩ : syracuseStep 2116199 = 3174299) B3174299
theorem B10169003 : Blo 1409524 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B2116391 : Blo 1409524 2116391 := bstep (se 1 (by rfl) ⟨1587293, by rfl⟩ : syracuseStep 2116391 = 3174587) B3174587
theorem B3173327 : Blo 1409524 3173327 := bstep (se 1 (by rfl) ⟨2379995, by rfl⟩ : syracuseStep 3173327 = 4759991) B4759991
theorem B2378747 : Blo 1409524 2378747 := bstep (se 1 (by rfl) ⟨1784060, by rfl⟩ : syracuseStep 2378747 = 3568121) B3568121
theorem B3173417 : Blo 1409524 3173417 := bstep (se 2 (by rfl) ⟨1190031, by rfl⟩ : syracuseStep 3173417 = 2380063) B2380063
theorem B2116715 : Blo 1409524 2116715 := bstep (se 1 (by rfl) ⟨1587536, by rfl⟩ : syracuseStep 2116715 = 3175073) B3175073
theorem B5352713 : Blo 1409524 5352713 := bstep (se 2 (by rfl) ⟨2007267, by rfl⟩ : syracuseStep 5352713 = 4014535) B4014535
theorem B3173651 : Blo 1409524 3173651 := bstep (se 1 (by rfl) ⟨2380238, by rfl⟩ : syracuseStep 3173651 = 4760477) B4760477
theorem B5877011 : Blo 1409524 5877011 := bstep (se 1 (by rfl) ⟨4407758, by rfl⟩ : syracuseStep 5877011 = 8815517) B8815517
theorem B5352743 : Blo 1409524 5352743 := bstep (se 1 (by rfl) ⟨4014557, by rfl⟩ : syracuseStep 5352743 = 8029115) B8029115
theorem B3173687 : Blo 1409524 3173687 := bstep (se 1 (by rfl) ⟨2380265, by rfl⟩ : syracuseStep 3173687 = 4760531) B4760531
theorem B8031575 : Blo 1409524 8031575 := bstep (se 1 (by rfl) ⟨6023681, by rfl⟩ : syracuseStep 8031575 = 12047363) B12047363
theorem B2116955 : Blo 1409524 2116955 := bstep (se 1 (by rfl) ⟨1587716, by rfl⟩ : syracuseStep 2116955 = 3175433) B3175433
theorem B2116985 : Blo 1409524 2116985 := bstep (se 2 (by rfl) ⟨793869, by rfl⟩ : syracuseStep 2116985 = 1587739) B1587739
theorem B2116991 : Blo 1409524 2116991 := bstep (se 1 (by rfl) ⟨1587743, by rfl⟩ : syracuseStep 2116991 = 3175487) B3175487
theorem B6024775 : Blo 1409524 6024775 := bstep (se 1 (by rfl) ⟨4518581, by rfl⟩ : syracuseStep 6024775 = 9037163) B9037163
theorem B3174281 : Blo 1409524 3174281 := bstep (se 2 (by rfl) ⟨1190355, by rfl⟩ : syracuseStep 3174281 = 2380711) B2380711
theorem B5353411 : Blo 1409524 5353411 := bstep (se 1 (by rfl) ⟨4015058, by rfl⟩ : syracuseStep 5353411 = 8030117) B8030117
theorem B3174497 : Blo 1409524 3174497 := bstep (se 2 (by rfl) ⟨1190436, by rfl⟩ : syracuseStep 3174497 = 2380873) B2380873
theorem B24105113 : Blo 1409524 24105113 := bstep (se 2 (by rfl) ⟨9039417, by rfl⟩ : syracuseStep 24105113 = 18078835) B18078835
theorem B2035867 : Blo 1409524 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B4763879 : Blo 1409524 4763879 := bstep (se 1 (by rfl) ⟨3572909, by rfl⟩ : syracuseStep 4763879 = 7145819) B7145819
theorem B10858789 : Blo 1409524 10858789 := bstep (se 4 (by rfl) ⟨1018011, by rfl⟩ : syracuseStep 10858789 = 2036023) B2036023
theorem B10711439 : Blo 1409524 10711439 := bstep (se 1 (by rfl) ⟨8033579, by rfl⟩ : syracuseStep 10711439 = 16067159) B16067159
theorem B5353883 : Blo 1409524 5353883 := bstep (se 1 (by rfl) ⟨4015412, by rfl⟩ : syracuseStep 5353883 = 8030825) B8030825
theorem B6107843 : Blo 1409524 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B3175163 : Blo 1409524 3175163 := bstep (se 1 (by rfl) ⟨2381372, by rfl⟩ : syracuseStep 3175163 = 4762745) B4762745
theorem B1586011 : Blo 1409524 1586011 := bstep (se 1 (by rfl) ⟨1189508, by rfl⟩ : syracuseStep 1586011 = 2379017) B2379017
theorem B5354369 : Blo 1409524 5354369 := bstep (se 2 (by rfl) ⟨2007888, by rfl⟩ : syracuseStep 5354369 = 4015777) B4015777
theorem B3011465 : Blo 1409524 3011465 := bstep (se 2 (by rfl) ⟨1129299, by rfl⟩ : syracuseStep 3011465 = 2258599) B2258599
theorem B3175379 : Blo 1409524 3175379 := bstep (se 1 (by rfl) ⟨2381534, by rfl⟩ : syracuseStep 3175379 = 4763069) B4763069
theorem B4019159 : Blo 1409524 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B11441359 : Blo 1409524 11441359 := bstep (se 1 (by rfl) ⟨8581019, by rfl⟩ : syracuseStep 11441359 = 17162039) B17162039
theorem B10712411 : Blo 1409524 10712411 := bstep (se 1 (by rfl) ⟨8034308, by rfl⟩ : syracuseStep 10712411 = 16068617) B16068617
theorem B38589857 : Blo 1409524 38589857 := bstep (se 2 (by rfl) ⟨14471196, by rfl⟩ : syracuseStep 38589857 = 28942393) B28942393
theorem B3175847 : Blo 1409524 3175847 := bstep (se 1 (by rfl) ⟨2381885, by rfl⟩ : syracuseStep 3175847 = 4763771) B4763771
theorem B1906159 : Blo 1409524 1906159 := bstep (se 1 (by rfl) ⟨1429619, by rfl⟩ : syracuseStep 1906159 = 2859239) B2859239
theorem B10851889 : Blo 1409524 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B12375611 : Blo 1409524 12375611 := bstep (se 1 (by rfl) ⟨9281708, by rfl⟩ : syracuseStep 12375611 = 18563417) B18563417
theorem B2381467 : Blo 1409524 2381467 := bstep (se 1 (by rfl) ⟨1786100, by rfl⟩ : syracuseStep 2381467 = 3572201) B3572201
theorem B3012319 : Blo 1409524 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B34322231 : Blo 1409524 34322231 := bstep (se 1 (by rfl) ⟨25741673, by rfl⟩ : syracuseStep 34322231 = 51483347) B51483347
theorem B17151821 : Blo 1409524 17151821 := bstep (se 3 (by rfl) ⟨3215966, by rfl⟩ : syracuseStep 17151821 = 6431933) B6431933
theorem B4757345 : Blo 1409524 4757345 := bstep (se 2 (by rfl) ⟨1784004, by rfl⟩ : syracuseStep 4757345 = 3568009) B3568009
theorem B2676577 : Blo 1409524 2676577 := bstep (se 2 (by rfl) ⟨1003716, by rfl⟩ : syracuseStep 2676577 = 2007433) B2007433
theorem B6780779 : Blo 1409524 6780779 := bstep (se 1 (by rfl) ⟨5085584, by rfl⟩ : syracuseStep 6780779 = 10171169) B10171169
theorem B1587271 : Blo 1409524 1587271 := bstep (se 1 (by rfl) ⟨1190453, by rfl⟩ : syracuseStep 1587271 = 2380907) B2380907
theorem B5355659 : Blo 1409524 5355659 := bstep (se 1 (by rfl) ⟨4016744, by rfl⟩ : syracuseStep 5355659 = 8033489) B8033489
theorem B4520119 : Blo 1409524 4520119 := bstep (se 1 (by rfl) ⟨3390089, by rfl⟩ : syracuseStep 4520119 = 6780179) B6780179
theorem B2259407 : Blo 1409524 2259407 := bstep (se 1 (by rfl) ⟨1694555, by rfl⟩ : syracuseStep 2259407 = 3389111) B3389111
theorem B6781409 : Blo 1409524 6781409 := bstep (se 2 (by rfl) ⟨2543028, by rfl⟩ : syracuseStep 6781409 = 5086057) B5086057
theorem B1546727 : Blo 1409524 1546727 := bstep (se 1 (by rfl) ⟨1160045, by rfl⟩ : syracuseStep 1546727 = 2320091) B2320091
theorem B6027817 : Blo 1409524 6027817 := bstep (se 2 (by rfl) ⟨2260431, by rfl⟩ : syracuseStep 6027817 = 4520863) B4520863
theorem B10705607 : Blo 1409524 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B3390187 : Blo 1409524 3390187 := bstep (se 1 (by rfl) ⟨2542640, by rfl⟩ : syracuseStep 3390187 = 5085281) B5085281
theorem B6429451 : Blo 1409524 6429451 := bstep (se 1 (by rfl) ⟨4822088, by rfl⟩ : syracuseStep 6429451 = 9644177) B9644177
theorem B86809411 : Blo 1409524 86809411 := bstep (se 1 (by rfl) ⟨65107058, by rfl⟩ : syracuseStep 86809411 = 130214117) B130214117
theorem B12221293 : Blo 1409524 12221293 := bstep (se 3 (by rfl) ⟨2291492, by rfl⟩ : syracuseStep 12221293 = 4582985) B4582985
theorem B21724037 : Blo 1409524 21724037 := bstep (se 4 (by rfl) ⟨2036628, by rfl⟩ : syracuseStep 21724037 = 4073257) B4073257
theorem B10861523 : Blo 1409524 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B1506395 : Blo 1409524 1506395 := bstep (se 1 (by rfl) ⟨1129796, by rfl⟩ : syracuseStep 1506395 = 2259593) B2259593
theorem B6110299 : Blo 1409524 6110299 := bstep (se 1 (by rfl) ⟨4582724, by rfl⟩ : syracuseStep 6110299 = 9165449) B9165449
theorem B20331719 : Blo 1409524 20331719 := bstep (se 1 (by rfl) ⟨15248789, by rfl⟩ : syracuseStep 20331719 = 30497579) B30497579
theorem B24091991 : Blo 1409524 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B6028775 : Blo 1409524 6028775 := bstep (se 1 (by rfl) ⟨4521581, by rfl⟩ : syracuseStep 6028775 = 9043163) B9043163
theorem B5717567 : Blo 1409524 5717567 := bstep (se 1 (by rfl) ⟨4288175, by rfl⟩ : syracuseStep 5717567 = 8576351) B8576351
theorem B8035949 : Blo 1409524 8035949 := bstep (se 3 (by rfl) ⟨1506740, by rfl⟩ : syracuseStep 8035949 = 3013481) B3013481
theorem B3014567 : Blo 1409524 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B16056953 : Blo 1409524 16056953 := bstep (se 2 (by rfl) ⟨6021357, by rfl⟩ : syracuseStep 16056953 = 12042715) B12042715
theorem B6873761 : Blo 1409524 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B8037089 : Blo 1409524 8037089 := bstep (se 2 (by rfl) ⟨3013908, by rfl⟩ : syracuseStep 8037089 = 6027817) B6027817
theorem B1409855 : Blo 1409524 1409855 := bstep (se 1 (by rfl) ⟨1057391, by rfl⟩ : syracuseStep 1409855 = 2114783) B2114783
theorem B1409863 : Blo 1409524 1409863 := bstep (se 1 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 1409863 = 2114795) B2114795
theorem B3572687 : Blo 1409524 3572687 := bstep (se 1 (by rfl) ⟨2679515, by rfl⟩ : syracuseStep 3572687 = 5359031) B5359031
theorem B8250407 : Blo 1409524 8250407 := bstep (se 1 (by rfl) ⟨6187805, by rfl⟩ : syracuseStep 8250407 = 12375611) B12375611
theorem B1410119 : Blo 1409524 1410119 := bstep (se 1 (by rfl) ⟨1057589, by rfl⟩ : syracuseStep 1410119 = 2115179) B2115179
theorem B115745881 : Blo 1409524 115745881 := bstep (se 2 (by rfl) ⟨43404705, by rfl⟩ : syracuseStep 115745881 = 86809411) B86809411
theorem B2114681 : Blo 1409524 2114681 := bstep (se 2 (by rfl) ⟨793005, by rfl⟩ : syracuseStep 2114681 = 1586011) B1586011
theorem B1410175 : Blo 1409524 1410175 := bstep (se 1 (by rfl) ⟨1057631, by rfl⟩ : syracuseStep 1410175 = 2115263) B2115263
theorem B16295057 : Blo 1409524 16295057 := bstep (se 2 (by rfl) ⟨6110646, by rfl⟩ : syracuseStep 16295057 = 12221293) B12221293
theorem B16065701 : Blo 1409524 16065701 := bstep (se 4 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 16065701 = 3012319) B3012319
theorem B3171563 : Blo 1409524 3171563 := bstep (se 1 (by rfl) ⟨2378672, by rfl⟩ : syracuseStep 3171563 = 4757345) B4757345
theorem B1410299 : Blo 1409524 1410299 := bstep (se 1 (by rfl) ⟨1057724, by rfl⟩ : syracuseStep 1410299 = 2115449) B2115449
theorem B2114879 : Blo 1409524 2114879 := bstep (se 1 (by rfl) ⟨1586159, by rfl⟩ : syracuseStep 2114879 = 3172319) B3172319
theorem B15877559 : Blo 1409524 15877559 := bstep (se 1 (by rfl) ⟨11908169, by rfl⟩ : syracuseStep 15877559 = 23816339) B23816339
theorem B15255145 : Blo 1409524 15255145 := bstep (se 2 (by rfl) ⟨5720679, by rfl⟩ : syracuseStep 15255145 = 11441359) B11441359
theorem B1410799 : Blo 1409524 1410799 := bstep (se 1 (by rfl) ⟨1058099, by rfl⟩ : syracuseStep 1410799 = 2116199) B2116199
theorem B7137071 : Blo 1409524 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B16287581 : Blo 1409524 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B1410927 : Blo 1409524 1410927 := bstep (se 1 (by rfl) ⟨1058195, by rfl⟩ : syracuseStep 1410927 = 2116391) B2116391
theorem B2115551 : Blo 1409524 2115551 := bstep (se 1 (by rfl) ⟨1586663, by rfl⟩ : syracuseStep 2115551 = 3173327) B3173327
theorem B2541545 : Blo 1409524 2541545 := bstep (se 2 (by rfl) ⟨953079, by rfl⟩ : syracuseStep 2541545 = 1906159) B1906159
theorem B2115611 : Blo 1409524 2115611 := bstep (se 1 (by rfl) ⟨1586708, by rfl⟩ : syracuseStep 2115611 = 3173417) B3173417
theorem B14469185 : Blo 1409524 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B1411143 : Blo 1409524 1411143 := bstep (se 1 (by rfl) ⟨1058357, by rfl⟩ : syracuseStep 1411143 = 2116715) B2116715
theorem B2115767 : Blo 1409524 2115767 := bstep (se 1 (by rfl) ⟨1586825, by rfl⟩ : syracuseStep 2115767 = 3173651) B3173651
theorem B3918007 : Blo 1409524 3918007 := bstep (se 1 (by rfl) ⟨2938505, by rfl⟩ : syracuseStep 3918007 = 5877011) B5877011
theorem B2115791 : Blo 1409524 2115791 := bstep (se 1 (by rfl) ⟨1586843, by rfl⟩ : syracuseStep 2115791 = 3173687) B3173687
theorem B1411303 : Blo 1409524 1411303 := bstep (se 1 (by rfl) ⟨1058477, by rfl⟩ : syracuseStep 1411303 = 2116955) B2116955
theorem B1411323 : Blo 1409524 1411323 := bstep (se 1 (by rfl) ⟨1058492, by rfl⟩ : syracuseStep 1411323 = 2116985) B2116985
theorem B1411327 : Blo 1409524 1411327 := bstep (se 1 (by rfl) ⟨1058495, by rfl⟩ : syracuseStep 1411327 = 2116991) B2116991
theorem B8030573 : Blo 1409524 8030573 := bstep (se 3 (by rfl) ⟨1505732, by rfl⟩ : syracuseStep 8030573 = 3011465) B3011465
theorem B3811711 : Blo 1409524 3811711 := bstep (se 1 (by rfl) ⟨2858783, by rfl⟩ : syracuseStep 3811711 = 5717567) B5717567
theorem B10717757 : Blo 1409524 10717757 := bstep (se 3 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 10717757 = 4019159) B4019159
theorem B7137881 : Blo 1409524 7137881 := bstep (se 2 (by rfl) ⟨2676705, by rfl⟩ : syracuseStep 7137881 = 5353411) B5353411
theorem B2116187 : Blo 1409524 2116187 := bstep (se 1 (by rfl) ⟨1587140, by rfl⟩ : syracuseStep 2116187 = 3174281) B3174281
theorem B2009711 : Blo 1409524 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B2116331 : Blo 1409524 2116331 := bstep (se 1 (by rfl) ⟨1587248, by rfl⟩ : syracuseStep 2116331 = 3174497) B3174497
theorem B2116361 : Blo 1409524 2116361 := bstep (se 2 (by rfl) ⟨793635, by rfl⟩ : syracuseStep 2116361 = 1587271) B1587271
theorem B2714489 : Blo 1409524 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B4017053 : Blo 1409524 4017053 := bstep (se 3 (by rfl) ⟨753197, by rfl⟩ : syracuseStep 4017053 = 1506395) B1506395
theorem B5352439 : Blo 1409524 5352439 := bstep (se 1 (by rfl) ⟨4014329, by rfl⟩ : syracuseStep 5352439 = 8028659) B8028659
theorem B14478385 : Blo 1409524 14478385 := bstep (se 2 (by rfl) ⟨5429394, by rfl⟩ : syracuseStep 14478385 = 10858789) B10858789
theorem B2116775 : Blo 1409524 2116775 := bstep (se 1 (by rfl) ⟨1587581, by rfl⟩ : syracuseStep 2116775 = 3175163) B3175163
theorem B2116919 : Blo 1409524 2116919 := bstep (se 1 (by rfl) ⟨1587689, by rfl⟩ : syracuseStep 2116919 = 3175379) B3175379
theorem B25726571 : Blo 1409524 25726571 := bstep (se 1 (by rfl) ⟨19294928, by rfl⟩ : syracuseStep 25726571 = 38589857) B38589857
theorem B2117231 : Blo 1409524 2117231 := bstep (se 1 (by rfl) ⟨1587923, by rfl⟩ : syracuseStep 2117231 = 3175847) B3175847
theorem B8572601 : Blo 1409524 8572601 := bstep (se 2 (by rfl) ⟨3214725, by rfl⟩ : syracuseStep 8572601 = 6429451) B6429451
theorem B8147065 : Blo 1409524 8147065 := bstep (se 2 (by rfl) ⟨3055149, by rfl⟩ : syracuseStep 8147065 = 6110299) B6110299
theorem B7139663 : Blo 1409524 7139663 := bstep (se 1 (by rfl) ⟨5354747, by rfl⟩ : syracuseStep 7139663 = 10709495) B10709495
theorem B6779335 : Blo 1409524 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B1585831 : Blo 1409524 1585831 := bstep (se 1 (by rfl) ⟨1189373, by rfl⟩ : syracuseStep 1585831 = 2378747) B2378747
theorem B8033033 : Blo 1409524 8033033 := bstep (se 2 (by rfl) ⟨3012387, by rfl⟩ : syracuseStep 8033033 = 6024775) B6024775
theorem B13554479 : Blo 1409524 13554479 := bstep (se 1 (by rfl) ⟨10165859, by rfl⟩ : syracuseStep 13554479 = 20331719) B20331719
theorem B91525949 : Blo 1409524 91525949 := bstep (se 3 (by rfl) ⟨17161115, by rfl⟩ : syracuseStep 91525949 = 34322231) B34322231
theorem B3568475 : Blo 1409524 3568475 := bstep (se 1 (by rfl) ⟨2676356, by rfl⟩ : syracuseStep 3568475 = 5352713) B5352713
theorem B3568495 : Blo 1409524 3568495 := bstep (se 1 (by rfl) ⟨2676371, by rfl⟩ : syracuseStep 3568495 = 5352743) B5352743
theorem B3175289 : Blo 1409524 3175289 := bstep (se 2 (by rfl) ⟨1190733, by rfl⟩ : syracuseStep 3175289 = 2381467) B2381467
theorem B16061327 : Blo 1409524 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B5354383 : Blo 1409524 5354383 := bstep (se 1 (by rfl) ⟨4015787, by rfl⟩ : syracuseStep 5354383 = 8031575) B8031575
theorem B4019183 : Blo 1409524 4019183 := bstep (se 1 (by rfl) ⟨3014387, by rfl⟩ : syracuseStep 4019183 = 6028775) B6028775
theorem B3568769 : Blo 1409524 3568769 := bstep (se 2 (by rfl) ⟨1338288, by rfl⟩ : syracuseStep 3568769 = 2676577) B2676577
theorem B5354657 : Blo 1409524 5354657 := bstep (se 2 (by rfl) ⟨2007996, by rfl⟩ : syracuseStep 5354657 = 4015993) B4015993
theorem B16070075 : Blo 1409524 16070075 := bstep (se 1 (by rfl) ⟨12052556, by rfl⟩ : syracuseStep 16070075 = 24105113) B24105113
theorem B3175919 : Blo 1409524 3175919 := bstep (se 1 (by rfl) ⟨2381939, by rfl⟩ : syracuseStep 3175919 = 4763879) B4763879
theorem B6026825 : Blo 1409524 6026825 := bstep (se 2 (by rfl) ⟨2260059, by rfl⟩ : syracuseStep 6026825 = 4520119) B4520119
theorem B7140959 : Blo 1409524 7140959 := bstep (se 1 (by rfl) ⟨5355719, by rfl⟩ : syracuseStep 7140959 = 10711439) B10711439
theorem B3569255 : Blo 1409524 3569255 := bstep (se 1 (by rfl) ⟨2676941, by rfl⟩ : syracuseStep 3569255 = 5353883) B5353883
theorem B12048047 : Blo 1409524 12048047 := bstep (se 1 (by rfl) ⟨9036035, by rfl⟩ : syracuseStep 12048047 = 18072071) B18072071
theorem B25728839 : Blo 1409524 25728839 := bstep (se 1 (by rfl) ⟨19296629, by rfl⟩ : syracuseStep 25728839 = 38593259) B38593259
theorem B3569579 : Blo 1409524 3569579 := bstep (se 1 (by rfl) ⟨2677184, by rfl⟩ : syracuseStep 3569579 = 5354369) B5354369
theorem B7141607 : Blo 1409524 7141607 := bstep (se 1 (by rfl) ⟨5356205, by rfl⟩ : syracuseStep 7141607 = 10712411) B10712411
theorem B4520249 : Blo 1409524 4520249 := bstep (se 2 (by rfl) ⟨1695093, by rfl⟩ : syracuseStep 4520249 = 3390187) B3390187
theorem B11434547 : Blo 1409524 11434547 := bstep (se 1 (by rfl) ⟨8575910, by rfl⟩ : syracuseStep 11434547 = 17151821) B17151821
theorem B4520519 : Blo 1409524 4520519 := bstep (se 1 (by rfl) ⟨3390389, by rfl⟩ : syracuseStep 4520519 = 6780779) B6780779
theorem B3570439 : Blo 1409524 3570439 := bstep (se 1 (by rfl) ⟨2677829, by rfl⟩ : syracuseStep 3570439 = 5355659) B5355659
theorem B1506271 : Blo 1409524 1506271 := bstep (se 1 (by rfl) ⟨1129703, by rfl⟩ : syracuseStep 1506271 = 2259407) B2259407
theorem B4520939 : Blo 1409524 4520939 := bstep (se 1 (by rfl) ⟨3390704, by rfl⟩ : syracuseStep 4520939 = 6781409) B6781409
theorem B14482691 : Blo 1409524 14482691 := bstep (se 1 (by rfl) ⟨10862018, by rfl⟩ : syracuseStep 14482691 = 21724037) B21724037
theorem B7241015 : Blo 1409524 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B5357299 : Blo 1409524 5357299 := bstep (se 1 (by rfl) ⟨4017974, by rfl⟩ : syracuseStep 5357299 = 8035949) B8035949
theorem B16498421 : Blo 1409524 16498421 := bstep (se 5 (by rfl) ⟨773363, by rfl⟩ : syracuseStep 16498421 = 1546727) B1546727
theorem B3137449 : Blo 1409524 3137449 := bstep (se 2 (by rfl) ⟨1176543, by rfl⟩ : syracuseStep 3137449 = 2353087) B2353087
theorem B10862753 : Blo 1409524 10862753 := bstep (se 2 (by rfl) ⟨4073532, by rfl⟩ : syracuseStep 10862753 = 8147065) B8147065
theorem B4759775 : Blo 1409524 4759775 := bstep (se 1 (by rfl) ⟨3569831, by rfl⟩ : syracuseStep 4759775 = 7139663) B7139663
theorem B5358059 : Blo 1409524 5358059 := bstep (se 1 (by rfl) ⟨4018544, by rfl⟩ : syracuseStep 5358059 = 8037089) B8037089
theorem B9036319 : Blo 1409524 9036319 := bstep (se 1 (by rfl) ⟨6777239, by rfl⟩ : syracuseStep 9036319 = 13554479) B13554479
theorem B10707551 : Blo 1409524 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B2679455 : Blo 1409524 2679455 := bstep (se 1 (by rfl) ⟨2009591, by rfl⟩ : syracuseStep 2679455 = 4019183) B4019183
theorem B1409787 : Blo 1409524 1409787 := bstep (se 1 (by rfl) ⟨1057340, by rfl⟩ : syracuseStep 1409787 = 2114681) B2114681
theorem B10863371 : Blo 1409524 10863371 := bstep (se 1 (by rfl) ⟨8147528, by rfl⟩ : syracuseStep 10863371 = 16295057) B16295057
theorem B2114375 : Blo 1409524 2114375 := bstep (se 1 (by rfl) ⟨1585781, by rfl⟩ : syracuseStep 2114375 = 3171563) B3171563
theorem B1409919 : Blo 1409524 1409919 := bstep (se 1 (by rfl) ⟨1057439, by rfl⟩ : syracuseStep 1409919 = 2114879) B2114879
theorem B2114441 : Blo 1409524 2114441 := bstep (se 2 (by rfl) ⟨792915, by rfl⟩ : syracuseStep 2114441 = 1585831) B1585831
theorem B10585039 : Blo 1409524 10585039 := bstep (se 1 (by rfl) ⟨7938779, by rfl⟩ : syracuseStep 10585039 = 15877559) B15877559
theorem B4760585 : Blo 1409524 4760585 := bstep (se 2 (by rfl) ⟨1785219, by rfl⟩ : syracuseStep 4760585 = 3570439) B3570439
theorem B4760639 : Blo 1409524 4760639 := bstep (se 1 (by rfl) ⟨3570479, by rfl⟩ : syracuseStep 4760639 = 7140959) B7140959
theorem B2008361 : Blo 1409524 2008361 := bstep (se 2 (by rfl) ⟨753135, by rfl⟩ : syracuseStep 2008361 = 1506271) B1506271
theorem B1410367 : Blo 1409524 1410367 := bstep (se 1 (by rfl) ⟨1057775, by rfl⟩ : syracuseStep 1410367 = 2115551) B2115551
theorem B7136585 : Blo 1409524 7136585 := bstep (se 2 (by rfl) ⟨2676219, by rfl⟩ : syracuseStep 7136585 = 5352439) B5352439
theorem B1410407 : Blo 1409524 1410407 := bstep (se 1 (by rfl) ⟨1057805, by rfl⟩ : syracuseStep 1410407 = 2115611) B2115611
theorem B1410511 : Blo 1409524 1410511 := bstep (se 1 (by rfl) ⟨1057883, by rfl⟩ : syracuseStep 1410511 = 2115767) B2115767
theorem B30492125 : Blo 1409524 30492125 := bstep (se 3 (by rfl) ⟨5717273, by rfl⟩ : syracuseStep 30492125 = 11434547) B11434547
theorem B1410527 : Blo 1409524 1410527 := bstep (se 1 (by rfl) ⟨1057895, by rfl⟩ : syracuseStep 1410527 = 2115791) B2115791
theorem B4761071 : Blo 1409524 4761071 := bstep (se 1 (by rfl) ⟨3570803, by rfl⟩ : syracuseStep 4761071 = 7141607) B7141607
theorem B5359229 : Blo 1409524 5359229 := bstep (se 3 (by rfl) ⟨1004855, by rfl⟩ : syracuseStep 5359229 = 2009711) B2009711
theorem B7145171 : Blo 1409524 7145171 := bstep (se 1 (by rfl) ⟨5358878, by rfl⟩ : syracuseStep 7145171 = 10717757) B10717757
theorem B1410791 : Blo 1409524 1410791 := bstep (se 1 (by rfl) ⟨1058093, by rfl⟩ : syracuseStep 1410791 = 2116187) B2116187
theorem B1410887 : Blo 1409524 1410887 := bstep (se 1 (by rfl) ⟨1058165, by rfl⟩ : syracuseStep 1410887 = 2116331) B2116331
theorem B1410907 : Blo 1409524 1410907 := bstep (se 1 (by rfl) ⟨1058180, by rfl⟩ : syracuseStep 1410907 = 2116361) B2116361
theorem B1411183 : Blo 1409524 1411183 := bstep (se 1 (by rfl) ⟨1058387, by rfl⟩ : syracuseStep 1411183 = 2116775) B2116775
theorem B4827343 : Blo 1409524 4827343 := bstep (se 1 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 4827343 = 7241015) B7241015
theorem B1411279 : Blo 1409524 1411279 := bstep (se 1 (by rfl) ⟨1058459, by rfl⟩ : syracuseStep 1411279 = 2116919) B2116919
theorem B1411487 : Blo 1409524 1411487 := bstep (se 1 (by rfl) ⟨1058615, by rfl⟩ : syracuseStep 1411487 = 2117231) B2117231
theorem B4582507 : Blo 1409524 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B5082281 : Blo 1409524 5082281 := bstep (se 2 (by rfl) ⟨1905855, by rfl⟩ : syracuseStep 5082281 = 3811711) B3811711
theorem B61017299 : Blo 1409524 61017299 := bstep (se 1 (by rfl) ⟨45762974, by rfl⟩ : syracuseStep 61017299 = 91525949) B91525949
theorem B2378983 : Blo 1409524 2378983 := bstep (se 1 (by rfl) ⟨1784237, by rfl⟩ : syracuseStep 2378983 = 3568475) B3568475
theorem B2116859 : Blo 1409524 2116859 := bstep (se 1 (by rfl) ⟨1587644, by rfl⟩ : syracuseStep 2116859 = 3175289) B3175289
theorem B9039113 : Blo 1409524 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B5500271 : Blo 1409524 5500271 := bstep (se 1 (by rfl) ⟨4125203, by rfl⟩ : syracuseStep 5500271 = 8250407) B8250407
theorem B2379179 : Blo 1409524 2379179 := bstep (se 1 (by rfl) ⟨1784384, by rfl⟩ : syracuseStep 2379179 = 3568769) B3568769
theorem B10710467 : Blo 1409524 10710467 := bstep (se 1 (by rfl) ⟨8032850, by rfl⟩ : syracuseStep 10710467 = 16065701) B16065701
theorem B2117279 : Blo 1409524 2117279 := bstep (se 1 (by rfl) ⟨1587959, by rfl⟩ : syracuseStep 2117279 = 3175919) B3175919
theorem B2379503 : Blo 1409524 2379503 := bstep (se 1 (by rfl) ⟨1784627, by rfl⟩ : syracuseStep 2379503 = 3569255) B3569255
theorem B8032031 : Blo 1409524 8032031 := bstep (se 1 (by rfl) ⟨6024023, by rfl⟩ : syracuseStep 8032031 = 12048047) B12048047
theorem B7139177 : Blo 1409524 7139177 := bstep (se 2 (by rfl) ⟨2677191, by rfl⟩ : syracuseStep 7139177 = 5354383) B5354383
theorem B10858387 : Blo 1409524 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B2379719 : Blo 1409524 2379719 := bstep (se 1 (by rfl) ⟨1784789, by rfl⟩ : syracuseStep 2379719 = 3569579) B3569579
theorem B9646123 : Blo 1409524 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B19304513 : Blo 1409524 19304513 := bstep (se 2 (by rfl) ⟨7239192, by rfl⟩ : syracuseStep 19304513 = 14478385) B14478385
theorem B5353715 : Blo 1409524 5353715 := bstep (se 1 (by rfl) ⟨4015286, by rfl⟩ : syracuseStep 5353715 = 8030573) B8030573
theorem B9655127 : Blo 1409524 9655127 := bstep (se 1 (by rfl) ⟨7241345, by rfl⟩ : syracuseStep 9655127 = 14482691) B14482691
theorem B17151047 : Blo 1409524 17151047 := bstep (se 1 (by rfl) ⟨12863285, by rfl⟩ : syracuseStep 17151047 = 25726571) B25726571
theorem B5715067 : Blo 1409524 5715067 := bstep (se 1 (by rfl) ⟨4286300, by rfl⟩ : syracuseStep 5715067 = 8572601) B8572601
theorem B10998947 : Blo 1409524 10998947 := bstep (se 1 (by rfl) ⟨8249210, by rfl⟩ : syracuseStep 10998947 = 16498421) B16498421
theorem B4183265 : Blo 1409524 4183265 := bstep (se 2 (by rfl) ⟨1568724, by rfl⟩ : syracuseStep 4183265 = 3137449) B3137449
theorem B12055837 : Blo 1409524 12055837 := bstep (se 3 (by rfl) ⟨2260469, by rfl⟩ : syracuseStep 12055837 = 4520939) B4520939
theorem B10704635 : Blo 1409524 10704635 := bstep (se 1 (by rfl) ⟨8028476, by rfl⟩ : syracuseStep 10704635 = 16056953) B16056953
theorem B5355355 : Blo 1409524 5355355 := bstep (se 1 (by rfl) ⟨4016516, by rfl⟩ : syracuseStep 5355355 = 8033033) B8033033
theorem B2381791 : Blo 1409524 2381791 := bstep (se 1 (by rfl) ⟨1786343, by rfl⟩ : syracuseStep 2381791 = 3572687) B3572687
theorem B3569771 : Blo 1409524 3569771 := bstep (se 1 (by rfl) ⟨2677328, by rfl⟩ : syracuseStep 3569771 = 5354657) B5354657
theorem B20896037 : Blo 1409524 20896037 := bstep (se 4 (by rfl) ⟨1959003, by rfl⟩ : syracuseStep 20896037 = 3918007) B3918007
theorem B10713383 : Blo 1409524 10713383 := bstep (se 1 (by rfl) ⟨8035037, by rfl⟩ : syracuseStep 10713383 = 16070075) B16070075
theorem B4757993 : Blo 1409524 4757993 := bstep (se 2 (by rfl) ⟨1784247, by rfl⟩ : syracuseStep 4757993 = 3568495) B3568495
theorem B4758047 : Blo 1409524 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B17152559 : Blo 1409524 17152559 := bstep (se 1 (by rfl) ⟨12864419, by rfl⟩ : syracuseStep 17152559 = 25728839) B25728839
theorem B1694363 : Blo 1409524 1694363 := bstep (se 1 (by rfl) ⟨1270772, by rfl⟩ : syracuseStep 1694363 = 2541545) B2541545
theorem B154327841 : Blo 1409524 154327841 := bstep (se 2 (by rfl) ⟨57872940, by rfl⟩ : syracuseStep 154327841 = 115745881) B115745881
theorem B16071533 : Blo 1409524 16071533 := bstep (se 3 (by rfl) ⟨3013412, by rfl⟩ : syracuseStep 16071533 = 6026825) B6026825
theorem B3013499 : Blo 1409524 3013499 := bstep (se 1 (by rfl) ⟨2260124, by rfl⟩ : syracuseStep 3013499 = 4520249) B4520249
theorem B3013679 : Blo 1409524 3013679 := bstep (se 1 (by rfl) ⟨2260259, by rfl⟩ : syracuseStep 3013679 = 4520519) B4520519
theorem B4758587 : Blo 1409524 4758587 := bstep (se 1 (by rfl) ⟨3568940, by rfl⟩ : syracuseStep 4758587 = 7137881) B7137881
theorem B1809659 : Blo 1409524 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B2678035 : Blo 1409524 2678035 := bstep (se 1 (by rfl) ⟨2008526, by rfl⟩ : syracuseStep 2678035 = 4017053) B4017053
theorem B20340193 : Blo 1409524 20340193 := bstep (se 2 (by rfl) ⟨7627572, by rfl⟩ : syracuseStep 20340193 = 15255145) B15255145
theorem B7143065 : Blo 1409524 7143065 := bstep (se 2 (by rfl) ⟨2678649, by rfl⟩ : syracuseStep 7143065 = 5357299) B5357299
theorem B12869675 : Blo 1409524 12869675 := bstep (se 1 (by rfl) ⟨9652256, by rfl⟩ : syracuseStep 12869675 = 19304513) B19304513
theorem B12861497 : Blo 1409524 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B3572039 : Blo 1409524 3572039 := bstep (se 1 (by rfl) ⟨2679029, by rfl⟩ : syracuseStep 3572039 = 5358059) B5358059
theorem B1786303 : Blo 1409524 1786303 := bstep (se 1 (by rfl) ⟨1339727, by rfl⟩ : syracuseStep 1786303 = 2679455) B2679455
theorem B7242247 : Blo 1409524 7242247 := bstep (se 1 (by rfl) ⟨5431685, by rfl⟩ : syracuseStep 7242247 = 10863371) B10863371
theorem B1409583 : Blo 1409524 1409583 := bstep (se 1 (by rfl) ⟨1057187, by rfl⟩ : syracuseStep 1409583 = 2114375) B2114375
theorem B1409627 : Blo 1409524 1409627 := bstep (se 1 (by rfl) ⟨1057220, by rfl⟩ : syracuseStep 1409627 = 2114441) B2114441
theorem B4825757 : Blo 1409524 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B3572819 : Blo 1409524 3572819 := bstep (se 1 (by rfl) ⟨2679614, by rfl⟩ : syracuseStep 3572819 = 5359229) B5359229
theorem B7136423 : Blo 1409524 7136423 := bstep (se 1 (by rfl) ⟨5352317, by rfl⟩ : syracuseStep 7136423 = 10704635) B10704635
theorem B7620089 : Blo 1409524 7620089 := bstep (se 2 (by rfl) ⟨2857533, by rfl⟩ : syracuseStep 7620089 = 5715067) B5715067
theorem B3171977 : Blo 1409524 3171977 := bstep (se 2 (by rfl) ⟨1189491, by rfl⟩ : syracuseStep 3171977 = 2378983) B2378983
theorem B3171995 : Blo 1409524 3171995 := bstep (se 1 (by rfl) ⟨2378996, by rfl⟩ : syracuseStep 3171995 = 4757993) B4757993
theorem B115869365 : Blo 1409524 115869365 := bstep (se 5 (by rfl) ⟨5431376, by rfl⟩ : syracuseStep 115869365 = 10862753) B10862753
theorem B3172031 : Blo 1409524 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B16074449 : Blo 1409524 16074449 := bstep (se 2 (by rfl) ⟨6027918, by rfl⟩ : syracuseStep 16074449 = 12055837) B12055837
theorem B102885227 : Blo 1409524 102885227 := bstep (se 1 (by rfl) ⟨77163920, by rfl⟩ : syracuseStep 102885227 = 154327841) B154327841
theorem B2008999 : Blo 1409524 2008999 := bstep (se 1 (by rfl) ⟨1506749, by rfl⟩ : syracuseStep 2008999 = 3013499) B3013499
theorem B2009119 : Blo 1409524 2009119 := bstep (se 1 (by rfl) ⟨1506839, by rfl⟩ : syracuseStep 2009119 = 3013679) B3013679
theorem B3172391 : Blo 1409524 3172391 := bstep (se 1 (by rfl) ⟨2379293, by rfl⟩ : syracuseStep 3172391 = 4758587) B4758587
theorem B1411239 : Blo 1409524 1411239 := bstep (se 1 (by rfl) ⟨1058429, by rfl⟩ : syracuseStep 1411239 = 2116859) B2116859
theorem B4762043 : Blo 1409524 4762043 := bstep (se 1 (by rfl) ⟨3571532, by rfl⟩ : syracuseStep 4762043 = 7143065) B7143065
theorem B1411519 : Blo 1409524 1411519 := bstep (se 1 (by rfl) ⟨1058639, by rfl⟩ : syracuseStep 1411519 = 2117279) B2117279
theorem B14477849 : Blo 1409524 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B3173183 : Blo 1409524 3173183 := bstep (se 1 (by rfl) ⟨2379887, by rfl⟩ : syracuseStep 3173183 = 4759775) B4759775
theorem B7138367 : Blo 1409524 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B29330525 : Blo 1409524 29330525 := bstep (se 3 (by rfl) ⟨5499473, by rfl⟩ : syracuseStep 29330525 = 10998947) B10998947
theorem B3173723 : Blo 1409524 3173723 := bstep (se 1 (by rfl) ⟨2380292, by rfl⟩ : syracuseStep 3173723 = 4760585) B4760585
theorem B3173759 : Blo 1409524 3173759 := bstep (se 1 (by rfl) ⟨2380319, by rfl⟩ : syracuseStep 3173759 = 4760639) B4760639
theorem B2788843 : Blo 1409524 2788843 := bstep (se 1 (by rfl) ⟨2091632, by rfl⟩ : syracuseStep 2788843 = 4183265) B4183265
theorem B14667389 : Blo 1409524 14667389 := bstep (se 3 (by rfl) ⟨2750135, by rfl⟩ : syracuseStep 14667389 = 5500271) B5500271
theorem B20328083 : Blo 1409524 20328083 := bstep (se 1 (by rfl) ⟨15246062, by rfl⟩ : syracuseStep 20328083 = 30492125) B30492125
theorem B3174047 : Blo 1409524 3174047 := bstep (se 1 (by rfl) ⟨2380535, by rfl⟩ : syracuseStep 3174047 = 4761071) B4761071
theorem B4763447 : Blo 1409524 4763447 := bstep (se 1 (by rfl) ⟨3572585, by rfl⟩ : syracuseStep 4763447 = 7145171) B7145171
theorem B2379847 : Blo 1409524 2379847 := bstep (se 1 (by rfl) ⟨1784885, by rfl⟩ : syracuseStep 2379847 = 3569771) B3569771
theorem B891564245 : Blo 1409524 891564245 := bstep (se 7 (by rfl) ⟨10448018, by rfl⟩ : syracuseStep 891564245 = 20896037) B20896037
theorem B4518301 : Blo 1409524 4518301 := bstep (se 3 (by rfl) ⟨847181, by rfl⟩ : syracuseStep 4518301 = 1694363) B1694363
theorem B27120257 : Blo 1409524 27120257 := bstep (se 2 (by rfl) ⟨10170096, by rfl⟩ : syracuseStep 27120257 = 20340193) B20340193
theorem B3388187 : Blo 1409524 3388187 := bstep (se 1 (by rfl) ⟨2541140, by rfl⟩ : syracuseStep 3388187 = 5082281) B5082281
theorem B40678199 : Blo 1409524 40678199 := bstep (se 1 (by rfl) ⟨30508649, by rfl⟩ : syracuseStep 40678199 = 61017299) B61017299
theorem B6026075 : Blo 1409524 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B1586119 : Blo 1409524 1586119 := bstep (se 1 (by rfl) ⟨1189589, by rfl⟩ : syracuseStep 1586119 = 2379179) B2379179
theorem B7140311 : Blo 1409524 7140311 := bstep (se 1 (by rfl) ⟨5355233, by rfl⟩ : syracuseStep 7140311 = 10710467) B10710467
theorem B7140473 : Blo 1409524 7140473 := bstep (se 2 (by rfl) ⟨2677677, by rfl⟩ : syracuseStep 7140473 = 5355355) B5355355
theorem B1586335 : Blo 1409524 1586335 := bstep (se 1 (by rfl) ⟨1189751, by rfl⟩ : syracuseStep 1586335 = 2379503) B2379503
theorem B5354687 : Blo 1409524 5354687 := bstep (se 1 (by rfl) ⟨4016015, by rfl⟩ : syracuseStep 5354687 = 8032031) B8032031
theorem B3175721 : Blo 1409524 3175721 := bstep (se 2 (by rfl) ⟨1190895, by rfl⟩ : syracuseStep 3175721 = 2381791) B2381791
theorem B1586479 : Blo 1409524 1586479 := bstep (se 1 (by rfl) ⟨1189859, by rfl⟩ : syracuseStep 1586479 = 2379719) B2379719
theorem B3569143 : Blo 1409524 3569143 := bstep (se 1 (by rfl) ⟨2676857, by rfl⟩ : syracuseStep 3569143 = 5353715) B5353715
theorem B6436457 : Blo 1409524 6436457 := bstep (se 2 (by rfl) ⟨2413671, by rfl⟩ : syracuseStep 6436457 = 4827343) B4827343
theorem B6436751 : Blo 1409524 6436751 := bstep (se 1 (by rfl) ⟨4827563, by rfl⟩ : syracuseStep 6436751 = 9655127) B9655127
theorem B12048425 : Blo 1409524 12048425 := bstep (se 2 (by rfl) ⟨4518159, by rfl⟩ : syracuseStep 12048425 = 9036319) B9036319
theorem B11434031 : Blo 1409524 11434031 := bstep (se 1 (by rfl) ⟨8575523, by rfl⟩ : syracuseStep 11434031 = 17151047) B17151047
theorem B5355629 : Blo 1409524 5355629 := bstep (se 3 (by rfl) ⟨1004180, by rfl⟩ : syracuseStep 5355629 = 2008361) B2008361
theorem B4757723 : Blo 1409524 4757723 := bstep (se 1 (by rfl) ⟨3568292, by rfl⟩ : syracuseStep 4757723 = 7136585) B7136585
theorem B14113385 : Blo 1409524 14113385 := bstep (se 2 (by rfl) ⟨5292519, by rfl⟩ : syracuseStep 14113385 = 10585039) B10585039
theorem B6110009 : Blo 1409524 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B7142255 : Blo 1409524 7142255 := bstep (se 1 (by rfl) ⟨5356691, by rfl⟩ : syracuseStep 7142255 = 10713383) B10713383
theorem B3570713 : Blo 1409524 3570713 := bstep (se 2 (by rfl) ⟨1339017, by rfl⟩ : syracuseStep 3570713 = 2678035) B2678035
theorem B11435039 : Blo 1409524 11435039 := bstep (se 1 (by rfl) ⟨8576279, by rfl⟩ : syracuseStep 11435039 = 17152559) B17152559
theorem B10714355 : Blo 1409524 10714355 := bstep (se 1 (by rfl) ⟨8035766, by rfl⟩ : syracuseStep 10714355 = 16071533) B16071533
theorem B4759451 : Blo 1409524 4759451 := bstep (se 1 (by rfl) ⟨3569588, by rfl⟩ : syracuseStep 4759451 = 7139177) B7139177
theorem B2678825 : Blo 1409524 2678825 := bstep (se 2 (by rfl) ⟨1004559, by rfl⟩ : syracuseStep 2678825 = 2009119) B2009119
theorem B18080171 : Blo 1409524 18080171 := bstep (se 1 (by rfl) ⟨13560128, by rfl⟩ : syracuseStep 18080171 = 27120257) B27120257
theorem B4760207 : Blo 1409524 4760207 := bstep (se 1 (by rfl) ⟨3570155, by rfl⟩ : syracuseStep 4760207 = 7140311) B7140311
theorem B4760315 : Blo 1409524 4760315 := bstep (se 1 (by rfl) ⟨3570236, by rfl⟩ : syracuseStep 4760315 = 7140473) B7140473
theorem B2114651 : Blo 1409524 2114651 := bstep (se 1 (by rfl) ⟨1585988, by rfl⟩ : syracuseStep 2114651 = 3171977) B3171977
theorem B2114663 : Blo 1409524 2114663 := bstep (se 1 (by rfl) ⟨1585997, by rfl⟩ : syracuseStep 2114663 = 3171995) B3171995
theorem B2114687 : Blo 1409524 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B10716299 : Blo 1409524 10716299 := bstep (se 1 (by rfl) ⟨8037224, by rfl⟩ : syracuseStep 10716299 = 16074449) B16074449
theorem B2114825 : Blo 1409524 2114825 := bstep (se 2 (by rfl) ⟨793059, by rfl⟩ : syracuseStep 2114825 = 1586119) B1586119
theorem B2114927 : Blo 1409524 2114927 := bstep (se 1 (by rfl) ⟨1586195, by rfl⟩ : syracuseStep 2114927 = 3172391) B3172391
theorem B3171815 : Blo 1409524 3171815 := bstep (se 1 (by rfl) ⟨2378861, by rfl⟩ : syracuseStep 3171815 = 4757723) B4757723
theorem B2115113 : Blo 1409524 2115113 := bstep (se 2 (by rfl) ⟨793167, by rfl⟩ : syracuseStep 2115113 = 1586335) B1586335
theorem B9651899 : Blo 1409524 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B2115305 : Blo 1409524 2115305 := bstep (se 2 (by rfl) ⟨793239, by rfl⟩ : syracuseStep 2115305 = 1586479) B1586479
theorem B4073339 : Blo 1409524 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B2115455 : Blo 1409524 2115455 := bstep (se 1 (by rfl) ⟨1586591, by rfl⟩ : syracuseStep 2115455 = 3173183) B3173183
theorem B4761503 : Blo 1409524 4761503 := bstep (se 1 (by rfl) ⟨3571127, by rfl⟩ : syracuseStep 4761503 = 7142255) B7142255
theorem B2115815 : Blo 1409524 2115815 := bstep (se 1 (by rfl) ⟨1586861, by rfl⟩ : syracuseStep 2115815 = 3173723) B3173723
theorem B2115839 : Blo 1409524 2115839 := bstep (se 1 (by rfl) ⟨1586879, by rfl⟩ : syracuseStep 2115839 = 3173759) B3173759
theorem B17164669 : Blo 1409524 17164669 := bstep (se 3 (by rfl) ⟨3218375, by rfl⟩ : syracuseStep 17164669 = 6436751) B6436751
theorem B13552055 : Blo 1409524 13552055 := bstep (se 1 (by rfl) ⟨10164041, by rfl⟩ : syracuseStep 13552055 = 20328083) B20328083
theorem B2116031 : Blo 1409524 2116031 := bstep (se 1 (by rfl) ⟨1587023, by rfl⟩ : syracuseStep 2116031 = 3174047) B3174047
theorem B3172967 : Blo 1409524 3172967 := bstep (se 1 (by rfl) ⟨2379725, by rfl⟩ : syracuseStep 3172967 = 4759451) B4759451
theorem B8579783 : Blo 1409524 8579783 := bstep (se 1 (by rfl) ⟨6434837, by rfl⟩ : syracuseStep 8579783 = 12869675) B12869675
theorem B3173129 : Blo 1409524 3173129 := bstep (se 2 (by rfl) ⟨1189923, by rfl⟩ : syracuseStep 3173129 = 2379847) B2379847
theorem B27118799 : Blo 1409524 27118799 := bstep (se 1 (by rfl) ⟨20339099, by rfl⟩ : syracuseStep 27118799 = 40678199) B40678199
theorem B6024401 : Blo 1409524 6024401 := bstep (se 2 (by rfl) ⟨2259150, by rfl⟩ : syracuseStep 6024401 = 4518301) B4518301
theorem B4017383 : Blo 1409524 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B2117147 : Blo 1409524 2117147 := bstep (se 1 (by rfl) ⟨1587860, by rfl⟩ : syracuseStep 2117147 = 3175721) B3175721
theorem B77246243 : Blo 1409524 77246243 := bstep (se 1 (by rfl) ⟨57934682, by rfl⟩ : syracuseStep 77246243 = 115869365) B115869365
theorem B20320237 : Blo 1409524 20320237 := bstep (se 3 (by rfl) ⟨3810044, by rfl⟩ : syracuseStep 20320237 = 7620089) B7620089
theorem B8032283 : Blo 1409524 8032283 := bstep (se 1 (by rfl) ⟨6024212, by rfl⟩ : syracuseStep 8032283 = 12048425) B12048425
theorem B7622687 : Blo 1409524 7622687 := bstep (se 1 (by rfl) ⟨5717015, by rfl⟩ : syracuseStep 7622687 = 11434031) B11434031
theorem B3174695 : Blo 1409524 3174695 := bstep (se 1 (by rfl) ⟨2381021, by rfl⟩ : syracuseStep 3174695 = 4762043) B4762043
theorem B9408923 : Blo 1409524 9408923 := bstep (se 1 (by rfl) ⟨7056692, by rfl⟩ : syracuseStep 9408923 = 14113385) B14113385
theorem B2380475 : Blo 1409524 2380475 := bstep (se 1 (by rfl) ⟨1785356, by rfl⟩ : syracuseStep 2380475 = 3570713) B3570713
theorem B7623359 : Blo 1409524 7623359 := bstep (se 1 (by rfl) ⟨5717519, by rfl⟩ : syracuseStep 7623359 = 11435039) B11435039
theorem B9778259 : Blo 1409524 9778259 := bstep (se 1 (by rfl) ⟨7333694, by rfl⟩ : syracuseStep 9778259 = 14667389) B14667389
theorem B3175631 : Blo 1409524 3175631 := bstep (se 1 (by rfl) ⟨2381723, by rfl⟩ : syracuseStep 3175631 = 4763447) B4763447
theorem B8574331 : Blo 1409524 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B594376163 : Blo 1409524 594376163 := bstep (se 1 (by rfl) ⟨445782122, by rfl⟩ : syracuseStep 594376163 = 891564245) B891564245
theorem B2381359 : Blo 1409524 2381359 := bstep (se 1 (by rfl) ⟨1786019, by rfl⟩ : syracuseStep 2381359 = 3572039) B3572039
theorem B2381737 : Blo 1409524 2381737 := bstep (se 2 (by rfl) ⟨893151, by rfl⟩ : syracuseStep 2381737 = 1786303) B1786303
theorem B9656329 : Blo 1409524 9656329 := bstep (se 2 (by rfl) ⟨3621123, by rfl⟩ : syracuseStep 9656329 = 7242247) B7242247
theorem B2381879 : Blo 1409524 2381879 := bstep (se 1 (by rfl) ⟨1786409, by rfl⟩ : syracuseStep 2381879 = 3572819) B3572819
theorem B4757615 : Blo 1409524 4757615 := bstep (se 1 (by rfl) ⟨3568211, by rfl⟩ : syracuseStep 4757615 = 7136423) B7136423
theorem B3569791 : Blo 1409524 3569791 := bstep (se 1 (by rfl) ⟨2677343, by rfl⟩ : syracuseStep 3569791 = 5354687) B5354687
theorem B4290971 : Blo 1409524 4290971 := bstep (se 1 (by rfl) ⟨3218228, by rfl⟩ : syracuseStep 4290971 = 6436457) B6436457
theorem B68590151 : Blo 1409524 68590151 := bstep (se 1 (by rfl) ⟨51442613, by rfl⟩ : syracuseStep 68590151 = 102885227) B102885227
theorem B3570419 : Blo 1409524 3570419 := bstep (se 1 (by rfl) ⟨2677814, by rfl⟩ : syracuseStep 3570419 = 5355629) B5355629
theorem B12868685 : Blo 1409524 12868685 := bstep (se 3 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 12868685 = 4825757) B4825757
theorem B3718457 : Blo 1409524 3718457 := bstep (se 2 (by rfl) ⟨1394421, by rfl⟩ : syracuseStep 3718457 = 2788843) B2788843
theorem B4758857 : Blo 1409524 4758857 := bstep (se 2 (by rfl) ⟨1784571, by rfl⟩ : syracuseStep 4758857 = 3569143) B3569143
theorem B4758911 : Blo 1409524 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B19553683 : Blo 1409524 19553683 := bstep (se 1 (by rfl) ⟨14665262, by rfl⟩ : syracuseStep 19553683 = 29330525) B29330525
theorem B9035165 : Blo 1409524 9035165 := bstep (se 3 (by rfl) ⟨1694093, by rfl⟩ : syracuseStep 9035165 = 3388187) B3388187
theorem B7142903 : Blo 1409524 7142903 := bstep (se 1 (by rfl) ⟨5357177, by rfl⟩ : syracuseStep 7142903 = 10714355) B10714355
theorem B2678665 : Blo 1409524 2678665 := bstep (se 2 (by rfl) ⟨1004499, by rfl⟩ : syracuseStep 2678665 = 2008999) B2008999
theorem B1785883 : Blo 1409524 1785883 := bstep (se 1 (by rfl) ⟨1339412, by rfl⟩ : syracuseStep 1785883 = 2678825) B2678825
theorem B4759721 : Blo 1409524 4759721 := bstep (se 2 (by rfl) ⟨1784895, by rfl⟩ : syracuseStep 4759721 = 3569791) B3569791
theorem B1409767 : Blo 1409524 1409767 := bstep (se 1 (by rfl) ⟨1057325, by rfl⟩ : syracuseStep 1409767 = 2114651) B2114651
theorem B1409775 : Blo 1409524 1409775 := bstep (se 1 (by rfl) ⟨1057331, by rfl⟩ : syracuseStep 1409775 = 2114663) B2114663
theorem B1409791 : Blo 1409524 1409791 := bstep (se 1 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 1409791 = 2114687) B2114687
theorem B7144199 : Blo 1409524 7144199 := bstep (se 1 (by rfl) ⟨5358149, by rfl⟩ : syracuseStep 7144199 = 10716299) B10716299
theorem B1409883 : Blo 1409524 1409883 := bstep (se 1 (by rfl) ⟨1057412, by rfl⟩ : syracuseStep 1409883 = 2114825) B2114825
theorem B1409951 : Blo 1409524 1409951 := bstep (se 1 (by rfl) ⟨1057463, by rfl⟩ : syracuseStep 1409951 = 2114927) B2114927
theorem B2114543 : Blo 1409524 2114543 := bstep (se 1 (by rfl) ⟨1585907, by rfl⟩ : syracuseStep 2114543 = 3171815) B3171815
theorem B1410075 : Blo 1409524 1410075 := bstep (se 1 (by rfl) ⟨1057556, by rfl⟩ : syracuseStep 1410075 = 2115113) B2115113
theorem B1410203 : Blo 1409524 1410203 := bstep (se 1 (by rfl) ⟨1057652, by rfl⟩ : syracuseStep 1410203 = 2115305) B2115305
theorem B1410303 : Blo 1409524 1410303 := bstep (se 1 (by rfl) ⟨1057727, by rfl⟩ : syracuseStep 1410303 = 2115455) B2115455
theorem B3171743 : Blo 1409524 3171743 := bstep (se 1 (by rfl) ⟨2378807, by rfl⟩ : syracuseStep 3171743 = 4757615) B4757615
theorem B1410543 : Blo 1409524 1410543 := bstep (se 1 (by rfl) ⟨1057907, by rfl⟩ : syracuseStep 1410543 = 2115815) B2115815
theorem B1410559 : Blo 1409524 1410559 := bstep (se 1 (by rfl) ⟨1057919, by rfl⟩ : syracuseStep 1410559 = 2115839) B2115839
theorem B1410687 : Blo 1409524 1410687 := bstep (se 1 (by rfl) ⟨1058015, by rfl⟩ : syracuseStep 1410687 = 2116031) B2116031
theorem B2115311 : Blo 1409524 2115311 := bstep (se 1 (by rfl) ⟨1586483, by rfl⟩ : syracuseStep 2115311 = 3172967) B3172967
theorem B5719855 : Blo 1409524 5719855 := bstep (se 1 (by rfl) ⟨4289891, by rfl⟩ : syracuseStep 5719855 = 8579783) B8579783
theorem B2115419 : Blo 1409524 2115419 := bstep (se 1 (by rfl) ⟨1586564, by rfl⟩ : syracuseStep 2115419 = 3173129) B3173129
theorem B8579123 : Blo 1409524 8579123 := bstep (se 1 (by rfl) ⟨6434342, by rfl⟩ : syracuseStep 8579123 = 12868685) B12868685
theorem B4016267 : Blo 1409524 4016267 := bstep (se 1 (by rfl) ⟨3012200, by rfl⟩ : syracuseStep 4016267 = 6024401) B6024401
theorem B3172571 : Blo 1409524 3172571 := bstep (se 1 (by rfl) ⟨2379428, by rfl⟩ : syracuseStep 3172571 = 4758857) B4758857
theorem B3172607 : Blo 1409524 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B6023443 : Blo 1409524 6023443 := bstep (se 1 (by rfl) ⟨4517582, by rfl⟩ : syracuseStep 6023443 = 9035165) B9035165
theorem B4761935 : Blo 1409524 4761935 := bstep (se 1 (by rfl) ⟨3571451, by rfl⟩ : syracuseStep 4761935 = 7142903) B7142903
theorem B1411431 : Blo 1409524 1411431 := bstep (se 1 (by rfl) ⟨1058573, by rfl⟩ : syracuseStep 1411431 = 2117147) B2117147
theorem B51497495 : Blo 1409524 51497495 := bstep (se 1 (by rfl) ⟨38623121, by rfl⟩ : syracuseStep 51497495 = 77246243) B77246243
theorem B27093649 : Blo 1409524 27093649 := bstep (se 2 (by rfl) ⟨10160118, by rfl⟩ : syracuseStep 27093649 = 20320237) B20320237
theorem B5081791 : Blo 1409524 5081791 := bstep (se 1 (by rfl) ⟨3811343, by rfl⟩ : syracuseStep 5081791 = 7622687) B7622687
theorem B2116463 : Blo 1409524 2116463 := bstep (se 1 (by rfl) ⟨1587347, by rfl⟩ : syracuseStep 2116463 = 3174695) B3174695
theorem B12053447 : Blo 1409524 12053447 := bstep (se 1 (by rfl) ⟨9040085, by rfl⟩ : syracuseStep 12053447 = 18080171) B18080171
theorem B3173471 : Blo 1409524 3173471 := bstep (se 1 (by rfl) ⟨2380103, by rfl⟩ : syracuseStep 3173471 = 4760207) B4760207
theorem B5082239 : Blo 1409524 5082239 := bstep (se 1 (by rfl) ⟨3811679, by rfl⟩ : syracuseStep 5082239 = 7623359) B7623359
theorem B3173543 : Blo 1409524 3173543 := bstep (se 1 (by rfl) ⟨2380157, by rfl⟩ : syracuseStep 3173543 = 4760315) B4760315
theorem B2117087 : Blo 1409524 2117087 := bstep (se 1 (by rfl) ⟨1587815, by rfl⟩ : syracuseStep 2117087 = 3175631) B3175631
theorem B396250775 : Blo 1409524 396250775 := bstep (se 1 (by rfl) ⟨297188081, by rfl⟩ : syracuseStep 396250775 = 594376163) B594376163
theorem B6434599 : Blo 1409524 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B3174335 : Blo 1409524 3174335 := bstep (se 1 (by rfl) ⟨2380751, by rfl⟩ : syracuseStep 3174335 = 4761503) B4761503
theorem B2380279 : Blo 1409524 2380279 := bstep (se 1 (by rfl) ⟨1785209, by rfl⟩ : syracuseStep 2380279 = 3570419) B3570419
theorem B11432441 : Blo 1409524 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B26071577 : Blo 1409524 26071577 := bstep (se 2 (by rfl) ⟨9776841, by rfl⟩ : syracuseStep 26071577 = 19553683) B19553683
theorem B3175145 : Blo 1409524 3175145 := bstep (se 2 (by rfl) ⟨1190679, by rfl⟩ : syracuseStep 3175145 = 2381359) B2381359
theorem B2478971 : Blo 1409524 2478971 := bstep (se 1 (by rfl) ⟨1859228, by rfl⟩ : syracuseStep 2478971 = 3718457) B3718457
theorem B3175649 : Blo 1409524 3175649 := bstep (se 2 (by rfl) ⟨1190868, by rfl⟩ : syracuseStep 3175649 = 2381737) B2381737
theorem B12875105 : Blo 1409524 12875105 := bstep (se 2 (by rfl) ⟨4828164, by rfl⟩ : syracuseStep 12875105 = 9656329) B9656329
theorem B5354855 : Blo 1409524 5354855 := bstep (se 1 (by rfl) ⟨4016141, by rfl⟩ : syracuseStep 5354855 = 8032283) B8032283
theorem B6272615 : Blo 1409524 6272615 := bstep (se 1 (by rfl) ⟨4704461, by rfl⟩ : syracuseStep 6272615 = 9408923) B9408923
theorem B1586983 : Blo 1409524 1586983 := bstep (se 1 (by rfl) ⟨1190237, by rfl⟩ : syracuseStep 1586983 = 2380475) B2380475
theorem B22886225 : Blo 1409524 22886225 := bstep (se 2 (by rfl) ⟨8582334, by rfl⟩ : syracuseStep 22886225 = 17164669) B17164669
theorem B6518839 : Blo 1409524 6518839 := bstep (se 1 (by rfl) ⟨4889129, by rfl⟩ : syracuseStep 6518839 = 9778259) B9778259
theorem B11442589 : Blo 1409524 11442589 := bstep (se 3 (by rfl) ⟨2145485, by rfl⟩ : syracuseStep 11442589 = 4290971) B4290971
theorem B1587919 : Blo 1409524 1587919 := bstep (se 1 (by rfl) ⟨1190939, by rfl⟩ : syracuseStep 1587919 = 2381879) B2381879
theorem B9034703 : Blo 1409524 9034703 := bstep (se 1 (by rfl) ⟨6776027, by rfl⟩ : syracuseStep 9034703 = 13552055) B13552055
theorem B45726767 : Blo 1409524 45726767 := bstep (se 1 (by rfl) ⟨34295075, by rfl⟩ : syracuseStep 45726767 = 68590151) B68590151
theorem B18079199 : Blo 1409524 18079199 := bstep (se 1 (by rfl) ⟨13559399, by rfl⟩ : syracuseStep 18079199 = 27118799) B27118799
theorem B2678255 : Blo 1409524 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B10862237 : Blo 1409524 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B3571553 : Blo 1409524 3571553 := bstep (se 2 (by rfl) ⟨1339332, by rfl⟩ : syracuseStep 3571553 = 2678665) B2678665
theorem B8691785 : Blo 1409524 8691785 := bstep (se 2 (by rfl) ⟨3259419, by rfl⟩ : syracuseStep 8691785 = 6518839) B6518839
theorem B1409695 : Blo 1409524 1409695 := bstep (se 1 (by rfl) ⟨1057271, by rfl⟩ : syracuseStep 1409695 = 2114543) B2114543
theorem B6775721 : Blo 1409524 6775721 := bstep (se 2 (by rfl) ⟨2540895, by rfl⟩ : syracuseStep 6775721 = 5081791) B5081791
theorem B2114495 : Blo 1409524 2114495 := bstep (se 1 (by rfl) ⟨1585871, by rfl⟩ : syracuseStep 2114495 = 3171743) B3171743
theorem B1410207 : Blo 1409524 1410207 := bstep (se 1 (by rfl) ⟨1057655, by rfl⟩ : syracuseStep 1410207 = 2115311) B2115311
theorem B1410279 : Blo 1409524 1410279 := bstep (se 1 (by rfl) ⟨1057709, by rfl⟩ : syracuseStep 1410279 = 2115419) B2115419
theorem B5719415 : Blo 1409524 5719415 := bstep (se 1 (by rfl) ⟨4289561, by rfl⟩ : syracuseStep 5719415 = 8579123) B8579123
theorem B2115047 : Blo 1409524 2115047 := bstep (se 1 (by rfl) ⟨1586285, by rfl⟩ : syracuseStep 2115047 = 3172571) B3172571
theorem B2115071 : Blo 1409524 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B1410975 : Blo 1409524 1410975 := bstep (se 1 (by rfl) ⟨1058231, by rfl⟩ : syracuseStep 1410975 = 2116463) B2116463
theorem B6023135 : Blo 1409524 6023135 := bstep (se 1 (by rfl) ⟨4517351, by rfl⟩ : syracuseStep 6023135 = 9034703) B9034703
theorem B30484511 : Blo 1409524 30484511 := bstep (se 1 (by rfl) ⟨22863383, by rfl⟩ : syracuseStep 30484511 = 45726767) B45726767
theorem B2115647 : Blo 1409524 2115647 := bstep (se 1 (by rfl) ⟨1586735, by rfl⟩ : syracuseStep 2115647 = 3173471) B3173471
theorem B2115695 : Blo 1409524 2115695 := bstep (se 1 (by rfl) ⟨1586771, by rfl⟩ : syracuseStep 2115695 = 3173543) B3173543
theorem B12052799 : Blo 1409524 12052799 := bstep (se 1 (by rfl) ⟨9039599, by rfl⟩ : syracuseStep 12052799 = 18079199) B18079199
theorem B1411391 : Blo 1409524 1411391 := bstep (se 1 (by rfl) ⟨1058543, by rfl⟩ : syracuseStep 1411391 = 2117087) B2117087
theorem B2115977 : Blo 1409524 2115977 := bstep (se 2 (by rfl) ⟨793491, by rfl⟩ : syracuseStep 2115977 = 1586983) B1586983
theorem B8579465 : Blo 1409524 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B2116223 : Blo 1409524 2116223 := bstep (se 1 (by rfl) ⟨1587167, by rfl⟩ : syracuseStep 2116223 = 3174335) B3174335
theorem B3173147 : Blo 1409524 3173147 := bstep (se 1 (by rfl) ⟨2379860, by rfl⟩ : syracuseStep 3173147 = 4759721) B4759721
theorem B7621627 : Blo 1409524 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B8031257 : Blo 1409524 8031257 := bstep (se 2 (by rfl) ⟨3011721, by rfl⟩ : syracuseStep 8031257 = 6023443) B6023443
theorem B2116763 : Blo 1409524 2116763 := bstep (se 1 (by rfl) ⟨1587572, by rfl⟩ : syracuseStep 2116763 = 3175145) B3175145
theorem B4762799 : Blo 1409524 4762799 := bstep (se 1 (by rfl) ⟨3572099, by rfl⟩ : syracuseStep 4762799 = 7144199) B7144199
theorem B3173705 : Blo 1409524 3173705 := bstep (se 2 (by rfl) ⟨1190139, by rfl⟩ : syracuseStep 3173705 = 2380279) B2380279
theorem B2117099 : Blo 1409524 2117099 := bstep (se 1 (by rfl) ⟨1587824, by rfl⟩ : syracuseStep 2117099 = 3175649) B3175649
theorem B2117225 : Blo 1409524 2117225 := bstep (se 2 (by rfl) ⟨793959, by rfl⟩ : syracuseStep 2117225 = 1587919) B1587919
theorem B4181743 : Blo 1409524 4181743 := bstep (se 1 (by rfl) ⟨3136307, by rfl⟩ : syracuseStep 4181743 = 6272615) B6272615
theorem B15257483 : Blo 1409524 15257483 := bstep (se 1 (by rfl) ⟨11443112, by rfl⟩ : syracuseStep 15257483 = 22886225) B22886225
theorem B3174623 : Blo 1409524 3174623 := bstep (se 1 (by rfl) ⟨2380967, by rfl⟩ : syracuseStep 3174623 = 4761935) B4761935
theorem B3388159 : Blo 1409524 3388159 := bstep (se 1 (by rfl) ⟨2541119, by rfl⟩ : syracuseStep 3388159 = 5082239) B5082239
theorem B61027141 : Blo 1409524 61027141 := bstep (se 4 (by rfl) ⟨5721294, by rfl⟩ : syracuseStep 61027141 = 11442589) B11442589
theorem B2381035 : Blo 1409524 2381035 := bstep (se 1 (by rfl) ⟨1785776, by rfl⟩ : syracuseStep 2381035 = 3571553) B3571553
theorem B2381177 : Blo 1409524 2381177 := bstep (se 2 (by rfl) ⟨892941, by rfl⟩ : syracuseStep 2381177 = 1785883) B1785883
theorem B17381051 : Blo 1409524 17381051 := bstep (se 1 (by rfl) ⟨13035788, by rfl⟩ : syracuseStep 17381051 = 26071577) B26071577
theorem B1652647 : Blo 1409524 1652647 := bstep (se 1 (by rfl) ⟨1239485, by rfl⟩ : syracuseStep 1652647 = 2478971) B2478971
theorem B36124865 : Blo 1409524 36124865 := bstep (se 2 (by rfl) ⟨13546824, by rfl⟩ : syracuseStep 36124865 = 27093649) B27093649
theorem B8583403 : Blo 1409524 8583403 := bstep (se 1 (by rfl) ⟨6437552, by rfl⟩ : syracuseStep 8583403 = 12875105) B12875105
theorem B3569903 : Blo 1409524 3569903 := bstep (se 1 (by rfl) ⟨2677427, by rfl⟩ : syracuseStep 3569903 = 5354855) B5354855
theorem B2677511 : Blo 1409524 2677511 := bstep (se 1 (by rfl) ⟨2008133, by rfl⟩ : syracuseStep 2677511 = 4016267) B4016267
theorem B34331663 : Blo 1409524 34331663 := bstep (se 1 (by rfl) ⟨25748747, by rfl⟩ : syracuseStep 34331663 = 51497495) B51497495
theorem B8035631 : Blo 1409524 8035631 := bstep (se 1 (by rfl) ⟨6026723, by rfl⟩ : syracuseStep 8035631 = 12053447) B12053447
theorem B1785503 : Blo 1409524 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B7626473 : Blo 1409524 7626473 := bstep (se 2 (by rfl) ⟨2859927, by rfl⟩ : syracuseStep 7626473 = 5719855) B5719855
theorem B264167183 : Blo 1409524 264167183 := bstep (se 1 (by rfl) ⟨198125387, by rfl⟩ : syracuseStep 264167183 = 396250775) B396250775
theorem B7241491 : Blo 1409524 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B11444537 : Blo 1409524 11444537 := bstep (se 2 (by rfl) ⟨4291701, by rfl⟩ : syracuseStep 11444537 = 8583403) B8583403
theorem B1409663 : Blo 1409524 1409663 := bstep (se 1 (by rfl) ⟨1057247, by rfl⟩ : syracuseStep 1409663 = 2114495) B2114495
theorem B1410031 : Blo 1409524 1410031 := bstep (se 1 (by rfl) ⟨1057523, by rfl⟩ : syracuseStep 1410031 = 2115047) B2115047
theorem B1410047 : Blo 1409524 1410047 := bstep (se 1 (by rfl) ⟨1057535, by rfl⟩ : syracuseStep 1410047 = 2115071) B2115071
theorem B4015423 : Blo 1409524 4015423 := bstep (se 1 (by rfl) ⟨3011567, by rfl⟩ : syracuseStep 4015423 = 6023135) B6023135
theorem B1410431 : Blo 1409524 1410431 := bstep (se 1 (by rfl) ⟨1057823, by rfl⟩ : syracuseStep 1410431 = 2115647) B2115647
theorem B1410463 : Blo 1409524 1410463 := bstep (se 1 (by rfl) ⟨1057847, by rfl⟩ : syracuseStep 1410463 = 2115695) B2115695
theorem B1410651 : Blo 1409524 1410651 := bstep (se 1 (by rfl) ⟨1057988, by rfl⟩ : syracuseStep 1410651 = 2115977) B2115977
theorem B5719643 : Blo 1409524 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B4761341 : Blo 1409524 4761341 := bstep (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) B1785503
theorem B1410815 : Blo 1409524 1410815 := bstep (se 1 (by rfl) ⟨1058111, by rfl⟩ : syracuseStep 1410815 = 2116223) B2116223
theorem B2115431 : Blo 1409524 2115431 := bstep (se 1 (by rfl) ⟨1586573, by rfl⟩ : syracuseStep 2115431 = 3173147) B3173147
theorem B1411175 : Blo 1409524 1411175 := bstep (se 1 (by rfl) ⟨1058381, by rfl⟩ : syracuseStep 1411175 = 2116763) B2116763
theorem B2115803 : Blo 1409524 2115803 := bstep (se 1 (by rfl) ⟨1586852, by rfl⟩ : syracuseStep 2115803 = 3173705) B3173705
theorem B1411399 : Blo 1409524 1411399 := bstep (se 1 (by rfl) ⟨1058549, by rfl⟩ : syracuseStep 1411399 = 2117099) B2117099
theorem B1411483 : Blo 1409524 1411483 := bstep (se 1 (by rfl) ⟨1058612, by rfl⟩ : syracuseStep 1411483 = 2117225) B2117225
theorem B5794523 : Blo 1409524 5794523 := bstep (se 1 (by rfl) ⟨4345892, by rfl⟩ : syracuseStep 5794523 = 8691785) B8691785
theorem B2116415 : Blo 1409524 2116415 := bstep (se 1 (by rfl) ⟨1587311, by rfl⟩ : syracuseStep 2116415 = 3174623) B3174623
theorem B4517147 : Blo 1409524 4517147 := bstep (se 1 (by rfl) ⟨3387860, by rfl⟩ : syracuseStep 4517147 = 6775721) B6775721
theorem B4517545 : Blo 1409524 4517545 := bstep (se 2 (by rfl) ⟨1694079, by rfl⟩ : syracuseStep 4517545 = 3388159) B3388159
theorem B11587367 : Blo 1409524 11587367 := bstep (se 1 (by rfl) ⟨8690525, by rfl⟩ : syracuseStep 11587367 = 17381051) B17381051
theorem B10162169 : Blo 1409524 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B2379935 : Blo 1409524 2379935 := bstep (se 1 (by rfl) ⟨1784951, by rfl⟩ : syracuseStep 2379935 = 3569903) B3569903
theorem B3174713 : Blo 1409524 3174713 := bstep (se 2 (by rfl) ⟨1190517, by rfl⟩ : syracuseStep 3174713 = 2381035) B2381035
theorem B5354171 : Blo 1409524 5354171 := bstep (se 1 (by rfl) ⟨4015628, by rfl⟩ : syracuseStep 5354171 = 8031257) B8031257
theorem B3175199 : Blo 1409524 3175199 := bstep (se 1 (by rfl) ⟨2381399, by rfl⟩ : syracuseStep 3175199 = 4762799) B4762799
theorem B5575657 : Blo 1409524 5575657 := bstep (se 2 (by rfl) ⟨2090871, by rfl⟩ : syracuseStep 5575657 = 4181743) B4181743
theorem B9655321 : Blo 1409524 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B5084315 : Blo 1409524 5084315 := bstep (se 1 (by rfl) ⟨3813236, by rfl⟩ : syracuseStep 5084315 = 7626473) B7626473
theorem B10171655 : Blo 1409524 10171655 := bstep (se 1 (by rfl) ⟨7628741, by rfl⟩ : syracuseStep 10171655 = 15257483) B15257483
theorem B1587451 : Blo 1409524 1587451 := bstep (se 1 (by rfl) ⟨1190588, by rfl⟩ : syracuseStep 1587451 = 2381177) B2381177
theorem B15251773 : Blo 1409524 15251773 := bstep (se 3 (by rfl) ⟨2859707, by rfl⟩ : syracuseStep 15251773 = 5719415) B5719415
theorem B81369521 : Blo 1409524 81369521 := bstep (se 2 (by rfl) ⟨30513570, by rfl⟩ : syracuseStep 81369521 = 61027141) B61027141
theorem B20323007 : Blo 1409524 20323007 := bstep (se 1 (by rfl) ⟨15242255, by rfl⟩ : syracuseStep 20323007 = 30484511) B30484511
theorem B24083243 : Blo 1409524 24083243 := bstep (se 1 (by rfl) ⟨18062432, by rfl⟩ : syracuseStep 24083243 = 36124865) B36124865
theorem B8035199 : Blo 1409524 8035199 := bstep (se 1 (by rfl) ⟨6026399, by rfl⟩ : syracuseStep 8035199 = 12052799) B12052799
theorem B1785007 : Blo 1409524 1785007 := bstep (se 1 (by rfl) ⟨1338755, by rfl⟩ : syracuseStep 1785007 = 2677511) B2677511
theorem B22887775 : Blo 1409524 22887775 := bstep (se 1 (by rfl) ⟨17165831, by rfl⟩ : syracuseStep 22887775 = 34331663) B34331663
theorem B5357087 : Blo 1409524 5357087 := bstep (se 1 (by rfl) ⟨4017815, by rfl⟩ : syracuseStep 5357087 = 8035631) B8035631
theorem B176111455 : Blo 1409524 176111455 := bstep (se 1 (by rfl) ⟨132083591, by rfl⟩ : syracuseStep 176111455 = 264167183) B264167183
theorem B2203529 : Blo 1409524 2203529 := bstep (se 2 (by rfl) ⟨826323, by rfl⟩ : syracuseStep 2203529 = 1652647) B1652647
theorem B1410287 : Blo 1409524 1410287 := bstep (se 1 (by rfl) ⟨1057715, by rfl⟩ : syracuseStep 1410287 = 2115431) B2115431
theorem B1410535 : Blo 1409524 1410535 := bstep (se 1 (by rfl) ⟨1057901, by rfl⟩ : syracuseStep 1410535 = 2115803) B2115803
theorem B30517033 : Blo 1409524 30517033 := bstep (se 2 (by rfl) ⟨11443887, by rfl⟩ : syracuseStep 30517033 = 22887775) B22887775
theorem B1410943 : Blo 1409524 1410943 := bstep (se 1 (by rfl) ⟨1058207, by rfl⟩ : syracuseStep 1410943 = 2116415) B2116415
theorem B6023393 : Blo 1409524 6023393 := bstep (se 2 (by rfl) ⟨2258772, by rfl⟩ : syracuseStep 6023393 = 4517545) B4517545
theorem B5876077 : Blo 1409524 5876077 := bstep (se 3 (by rfl) ⟨1101764, by rfl⟩ : syracuseStep 5876077 = 2203529) B2203529
theorem B2116475 : Blo 1409524 2116475 := bstep (se 1 (by rfl) ⟨1587356, by rfl⟩ : syracuseStep 2116475 = 3174713) B3174713
theorem B2116601 : Blo 1409524 2116601 := bstep (se 2 (by rfl) ⟨793725, by rfl⟩ : syracuseStep 2116601 = 1587451) B1587451
theorem B20335697 : Blo 1409524 20335697 := bstep (se 2 (by rfl) ⟨7625886, by rfl⟩ : syracuseStep 20335697 = 15251773) B15251773
theorem B2116799 : Blo 1409524 2116799 := bstep (se 1 (by rfl) ⟨1587599, by rfl⟩ : syracuseStep 2116799 = 3175199) B3175199
theorem B30518765 : Blo 1409524 30518765 := bstep (se 3 (by rfl) ⟨5722268, by rfl⟩ : syracuseStep 30518765 = 11444537) B11444537
theorem B3813095 : Blo 1409524 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B3174227 : Blo 1409524 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B7434209 : Blo 1409524 7434209 := bstep (se 2 (by rfl) ⟨2787828, by rfl⟩ : syracuseStep 7434209 = 5575657) B5575657
theorem B12873761 : Blo 1409524 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B2380009 : Blo 1409524 2380009 := bstep (se 2 (by rfl) ⟨892503, by rfl⟩ : syracuseStep 2380009 = 1785007) B1785007
theorem B5353897 : Blo 1409524 5353897 := bstep (se 2 (by rfl) ⟨2007711, by rfl⟩ : syracuseStep 5353897 = 4015423) B4015423
theorem B3863015 : Blo 1409524 3863015 := bstep (se 1 (by rfl) ⟨2897261, by rfl⟩ : syracuseStep 3863015 = 5794523) B5794523
theorem B3011431 : Blo 1409524 3011431 := bstep (se 1 (by rfl) ⟨2258573, by rfl⟩ : syracuseStep 3011431 = 4517147) B4517147
theorem B1586623 : Blo 1409524 1586623 := bstep (se 1 (by rfl) ⟨1189967, by rfl⟩ : syracuseStep 1586623 = 2379935) B2379935
theorem B3569447 : Blo 1409524 3569447 := bstep (se 1 (by rfl) ⟨2677085, by rfl⟩ : syracuseStep 3569447 = 5354171) B5354171
theorem B3389543 : Blo 1409524 3389543 := bstep (se 1 (by rfl) ⟨2542157, by rfl⟩ : syracuseStep 3389543 = 5084315) B5084315
theorem B6781103 : Blo 1409524 6781103 := bstep (se 1 (by rfl) ⟨5085827, by rfl⟩ : syracuseStep 6781103 = 10171655) B10171655
theorem B54246347 : Blo 1409524 54246347 := bstep (se 1 (by rfl) ⟨40684760, by rfl⟩ : syracuseStep 54246347 = 81369521) B81369521
theorem B13548671 : Blo 1409524 13548671 := bstep (se 1 (by rfl) ⟨10161503, by rfl⟩ : syracuseStep 13548671 = 20323007) B20323007
theorem B16055495 : Blo 1409524 16055495 := bstep (se 1 (by rfl) ⟨12041621, by rfl⟩ : syracuseStep 16055495 = 24083243) B24083243
theorem B5356799 : Blo 1409524 5356799 := bstep (se 1 (by rfl) ⟨4017599, by rfl⟩ : syracuseStep 5356799 = 8035199) B8035199
theorem B30899645 : Blo 1409524 30899645 := bstep (se 3 (by rfl) ⟨5793683, by rfl⟩ : syracuseStep 30899645 = 11587367) B11587367
theorem B3571391 : Blo 1409524 3571391 := bstep (se 1 (by rfl) ⟨2678543, by rfl⟩ : syracuseStep 3571391 = 5357087) B5357087
theorem B234815273 : Blo 1409524 234815273 := bstep (se 2 (by rfl) ⟨88055727, by rfl⟩ : syracuseStep 234815273 = 176111455) B176111455
theorem B6774779 : Blo 1409524 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B4015241 : Blo 1409524 4015241 := bstep (se 2 (by rfl) ⟨1505715, by rfl⟩ : syracuseStep 4015241 = 3011431) B3011431
theorem B4015595 : Blo 1409524 4015595 := bstep (se 1 (by rfl) ⟨3011696, by rfl⟩ : syracuseStep 4015595 = 6023393) B6023393
theorem B1410983 : Blo 1409524 1410983 := bstep (se 1 (by rfl) ⟨1058237, by rfl⟩ : syracuseStep 1410983 = 2116475) B2116475
theorem B2115497 : Blo 1409524 2115497 := bstep (se 2 (by rfl) ⟨793311, by rfl⟩ : syracuseStep 2115497 = 1586623) B1586623
theorem B10168253 : Blo 1409524 10168253 := bstep (se 3 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 10168253 = 3813095) B3813095
theorem B1411067 : Blo 1409524 1411067 := bstep (se 1 (by rfl) ⟨1058300, by rfl⟩ : syracuseStep 1411067 = 2116601) B2116601
theorem B1411199 : Blo 1409524 1411199 := bstep (se 1 (by rfl) ⟨1058399, by rfl⟩ : syracuseStep 1411199 = 2116799) B2116799
theorem B156543515 : Blo 1409524 156543515 := bstep (se 1 (by rfl) ⟨117407636, by rfl⟩ : syracuseStep 156543515 = 234815273) B234815273
theorem B2116151 : Blo 1409524 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B18066077 : Blo 1409524 18066077 := bstep (se 3 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 18066077 = 6774779) B6774779
theorem B3173345 : Blo 1409524 3173345 := bstep (se 2 (by rfl) ⟨1190004, by rfl⟩ : syracuseStep 3173345 = 2380009) B2380009
theorem B2575343 : Blo 1409524 2575343 := bstep (se 1 (by rfl) ⟨1931507, by rfl⟩ : syracuseStep 2575343 = 3863015) B3863015
theorem B7834769 : Blo 1409524 7834769 := bstep (se 2 (by rfl) ⟨2938038, by rfl⟩ : syracuseStep 7834769 = 5876077) B5876077
theorem B7138529 : Blo 1409524 7138529 := bstep (se 2 (by rfl) ⟨2676948, by rfl⟩ : syracuseStep 7138529 = 5353897) B5353897
theorem B2379631 : Blo 1409524 2379631 := bstep (se 1 (by rfl) ⟨1784723, by rfl⟩ : syracuseStep 2379631 = 3569447) B3569447
theorem B36164231 : Blo 1409524 36164231 := bstep (se 1 (by rfl) ⟨27123173, by rfl⟩ : syracuseStep 36164231 = 54246347) B54246347
theorem B9032447 : Blo 1409524 9032447 := bstep (se 1 (by rfl) ⟨6774335, by rfl⟩ : syracuseStep 9032447 = 13548671) B13548671
theorem B10703663 : Blo 1409524 10703663 := bstep (se 1 (by rfl) ⟨8027747, by rfl⟩ : syracuseStep 10703663 = 16055495) B16055495
theorem B20599763 : Blo 1409524 20599763 := bstep (se 1 (by rfl) ⟨15449822, by rfl⟩ : syracuseStep 20599763 = 30899645) B30899645
theorem B20345843 : Blo 1409524 20345843 := bstep (se 1 (by rfl) ⟨15259382, by rfl⟩ : syracuseStep 20345843 = 30518765) B30518765
theorem B2380927 : Blo 1409524 2380927 := bstep (se 1 (by rfl) ⟨1785695, by rfl⟩ : syracuseStep 2380927 = 3571391) B3571391
theorem B8582507 : Blo 1409524 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B317192917 : Blo 1409524 317192917 := bstep (se 7 (by rfl) ⟨3717104, by rfl⟩ : syracuseStep 317192917 = 7434209) B7434209
theorem B2259695 : Blo 1409524 2259695 := bstep (se 1 (by rfl) ⟨1694771, by rfl⟩ : syracuseStep 2259695 = 3389543) B3389543
theorem B4520735 : Blo 1409524 4520735 := bstep (se 1 (by rfl) ⟨3390551, by rfl⟩ : syracuseStep 4520735 = 6781103) B6781103
theorem B13557131 : Blo 1409524 13557131 := bstep (se 1 (by rfl) ⟨10167848, by rfl⟩ : syracuseStep 13557131 = 20335697) B20335697
theorem B3571199 : Blo 1409524 3571199 := bstep (se 1 (by rfl) ⟨2678399, by rfl⟩ : syracuseStep 3571199 = 5356799) B5356799
theorem B40689377 : Blo 1409524 40689377 := bstep (se 2 (by rfl) ⟨15258516, by rfl⟩ : syracuseStep 40689377 = 30517033) B30517033
theorem B24109487 : Blo 1409524 24109487 := bstep (se 1 (by rfl) ⟨18082115, by rfl⟩ : syracuseStep 24109487 = 36164231) B36164231
theorem B6021631 : Blo 1409524 6021631 := bstep (se 1 (by rfl) ⟨4516223, by rfl⟩ : syracuseStep 6021631 = 9032447) B9032447
theorem B7135775 : Blo 1409524 7135775 := bstep (se 1 (by rfl) ⟨5351831, by rfl⟩ : syracuseStep 7135775 = 10703663) B10703663
theorem B1410331 : Blo 1409524 1410331 := bstep (se 1 (by rfl) ⟨1057748, by rfl⟩ : syracuseStep 1410331 = 2115497) B2115497
theorem B1410767 : Blo 1409524 1410767 := bstep (se 1 (by rfl) ⟨1058075, by rfl⟩ : syracuseStep 1410767 = 2116151) B2116151
theorem B12044051 : Blo 1409524 12044051 := bstep (se 1 (by rfl) ⟨9033038, by rfl⟩ : syracuseStep 12044051 = 18066077) B18066077
theorem B2115563 : Blo 1409524 2115563 := bstep (se 1 (by rfl) ⟨1586672, by rfl⟩ : syracuseStep 2115563 = 3173345) B3173345
theorem B9038087 : Blo 1409524 9038087 := bstep (se 1 (by rfl) ⟨6778565, by rfl⟩ : syracuseStep 9038087 = 13557131) B13557131
theorem B3172841 : Blo 1409524 3172841 := bstep (se 2 (by rfl) ⟨1189815, by rfl⟩ : syracuseStep 3172841 = 2379631) B2379631
theorem B27126251 : Blo 1409524 27126251 := bstep (se 1 (by rfl) ⟨20344688, by rfl⟩ : syracuseStep 27126251 = 40689377) B40689377
theorem B5721671 : Blo 1409524 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B422923889 : Blo 1409524 422923889 := bstep (se 2 (by rfl) ⟨158596458, by rfl⟩ : syracuseStep 422923889 = 317192917) B317192917
theorem B6778835 : Blo 1409524 6778835 := bstep (se 1 (by rfl) ⟨5084126, by rfl⟩ : syracuseStep 6778835 = 10168253) B10168253
theorem B3174569 : Blo 1409524 3174569 := bstep (se 2 (by rfl) ⟨1190463, by rfl⟩ : syracuseStep 3174569 = 2380927) B2380927
theorem B104362343 : Blo 1409524 104362343 := bstep (se 1 (by rfl) ⟨78271757, by rfl⟩ : syracuseStep 104362343 = 156543515) B156543515
theorem B6025853 : Blo 1409524 6025853 := bstep (se 3 (by rfl) ⟨1129847, by rfl⟩ : syracuseStep 6025853 = 2259695) B2259695
theorem B1716895 : Blo 1409524 1716895 := bstep (se 1 (by rfl) ⟨1287671, by rfl⟩ : syracuseStep 1716895 = 2575343) B2575343
theorem B5223179 : Blo 1409524 5223179 := bstep (se 1 (by rfl) ⟨3917384, by rfl⟩ : syracuseStep 5223179 = 7834769) B7834769
theorem B2380799 : Blo 1409524 2380799 := bstep (se 1 (by rfl) ⟨1785599, by rfl⟩ : syracuseStep 2380799 = 3571199) B3571199
theorem B54932701 : Blo 1409524 54932701 := bstep (se 3 (by rfl) ⟨10299881, by rfl⟩ : syracuseStep 54932701 = 20599763) B20599763
theorem B13563895 : Blo 1409524 13563895 := bstep (se 1 (by rfl) ⟨10172921, by rfl⟩ : syracuseStep 13563895 = 20345843) B20345843
theorem B2676827 : Blo 1409524 2676827 := bstep (se 1 (by rfl) ⟨2007620, by rfl⟩ : syracuseStep 2676827 = 4015241) B4015241
theorem B2677063 : Blo 1409524 2677063 := bstep (se 1 (by rfl) ⟨2007797, by rfl⟩ : syracuseStep 2677063 = 4015595) B4015595
theorem B3013823 : Blo 1409524 3013823 := bstep (se 1 (by rfl) ⟨2260367, by rfl⟩ : syracuseStep 3013823 = 4520735) B4520735
theorem B4759019 : Blo 1409524 4759019 := bstep (se 1 (by rfl) ⟨3569264, by rfl⟩ : syracuseStep 4759019 = 7138529) B7138529
theorem B69574895 : Blo 1409524 69574895 := bstep (se 1 (by rfl) ⟨52181171, by rfl⟩ : syracuseStep 69574895 = 104362343) B104362343
theorem B16072991 : Blo 1409524 16072991 := bstep (se 1 (by rfl) ⟨12054743, by rfl⟩ : syracuseStep 16072991 = 24109487) B24109487
theorem B3482119 : Blo 1409524 3482119 := bstep (se 1 (by rfl) ⟨2611589, by rfl⟩ : syracuseStep 3482119 = 5223179) B5223179
theorem B8028841 : Blo 1409524 8028841 := bstep (se 2 (by rfl) ⟨3010815, by rfl⟩ : syracuseStep 8028841 = 6021631) B6021631
theorem B8029367 : Blo 1409524 8029367 := bstep (se 1 (by rfl) ⟨6022025, by rfl⟩ : syracuseStep 8029367 = 12044051) B12044051
theorem B1410375 : Blo 1409524 1410375 := bstep (se 1 (by rfl) ⟨1057781, by rfl⟩ : syracuseStep 1410375 = 2115563) B2115563
theorem B2115227 : Blo 1409524 2115227 := bstep (se 1 (by rfl) ⟨1586420, by rfl⟩ : syracuseStep 2115227 = 3172841) B3172841
theorem B2009215 : Blo 1409524 2009215 := bstep (se 1 (by rfl) ⟨1506911, by rfl⟩ : syracuseStep 2009215 = 3013823) B3013823
theorem B3172679 : Blo 1409524 3172679 := bstep (se 1 (by rfl) ⟨2379509, by rfl⟩ : syracuseStep 3172679 = 4759019) B4759019
theorem B2116379 : Blo 1409524 2116379 := bstep (se 1 (by rfl) ⟨1587284, by rfl⟩ : syracuseStep 2116379 = 3174569) B3174569
theorem B7138205 : Blo 1409524 7138205 := bstep (se 3 (by rfl) ⟨1338413, by rfl⟩ : syracuseStep 7138205 = 2676827) B2676827
theorem B4017235 : Blo 1409524 4017235 := bstep (se 1 (by rfl) ⟨3012926, by rfl⟩ : syracuseStep 4017235 = 6025853) B6025853
theorem B6025391 : Blo 1409524 6025391 := bstep (se 1 (by rfl) ⟨4519043, by rfl⟩ : syracuseStep 6025391 = 9038087) B9038087
theorem B18084167 : Blo 1409524 18084167 := bstep (se 1 (by rfl) ⟨13563125, by rfl⟩ : syracuseStep 18084167 = 27126251) B27126251
theorem B3814447 : Blo 1409524 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B281949259 : Blo 1409524 281949259 := bstep (se 1 (by rfl) ⟨211461944, by rfl⟩ : syracuseStep 281949259 = 422923889) B422923889
theorem B4519223 : Blo 1409524 4519223 := bstep (se 1 (by rfl) ⟨3389417, by rfl⟩ : syracuseStep 4519223 = 6778835) B6778835
theorem B18085193 : Blo 1409524 18085193 := bstep (se 2 (by rfl) ⟨6781947, by rfl⟩ : syracuseStep 18085193 = 13563895) B13563895
theorem B4757183 : Blo 1409524 4757183 := bstep (se 1 (by rfl) ⟨3567887, by rfl⟩ : syracuseStep 4757183 = 7135775) B7135775
theorem B3569417 : Blo 1409524 3569417 := bstep (se 2 (by rfl) ⟨1338531, by rfl⟩ : syracuseStep 3569417 = 2677063) B2677063
theorem B1587199 : Blo 1409524 1587199 := bstep (se 1 (by rfl) ⟨1190399, by rfl⟩ : syracuseStep 1587199 = 2380799) B2380799
theorem B9156773 : Blo 1409524 9156773 := bstep (se 4 (by rfl) ⟨858447, by rfl⟩ : syracuseStep 9156773 = 1716895) B1716895
theorem B73243601 : Blo 1409524 73243601 := bstep (se 2 (by rfl) ⟨27466350, by rfl⟩ : syracuseStep 73243601 = 54932701) B54932701
theorem B18571301 : Blo 1409524 18571301 := bstep (se 4 (by rfl) ⟨1741059, by rfl⟩ : syracuseStep 18571301 = 3482119) B3482119
theorem B46383263 : Blo 1409524 46383263 := bstep (se 1 (by rfl) ⟨34787447, by rfl⟩ : syracuseStep 46383263 = 69574895) B69574895
theorem B10715327 : Blo 1409524 10715327 := bstep (se 1 (by rfl) ⟨8036495, by rfl⟩ : syracuseStep 10715327 = 16072991) B16072991
theorem B10715813 : Blo 1409524 10715813 := bstep (se 4 (by rfl) ⟨1004607, by rfl⟩ : syracuseStep 10715813 = 2009215) B2009215
theorem B1410151 : Blo 1409524 1410151 := bstep (se 1 (by rfl) ⟨1057613, by rfl⟩ : syracuseStep 1410151 = 2115227) B2115227
theorem B3171455 : Blo 1409524 3171455 := bstep (se 1 (by rfl) ⟨2378591, by rfl⟩ : syracuseStep 3171455 = 4757183) B4757183
theorem B375932345 : Blo 1409524 375932345 := bstep (se 2 (by rfl) ⟨140974629, by rfl⟩ : syracuseStep 375932345 = 281949259) B281949259
theorem B2115119 : Blo 1409524 2115119 := bstep (se 1 (by rfl) ⟨1586339, by rfl⟩ : syracuseStep 2115119 = 3172679) B3172679
theorem B1410919 : Blo 1409524 1410919 := bstep (se 1 (by rfl) ⟨1058189, by rfl⟩ : syracuseStep 1410919 = 2116379) B2116379
theorem B2116265 : Blo 1409524 2116265 := bstep (se 2 (by rfl) ⟨793599, by rfl⟩ : syracuseStep 2116265 = 1587199) B1587199
theorem B4016927 : Blo 1409524 4016927 := bstep (se 1 (by rfl) ⟨3012695, by rfl⟩ : syracuseStep 4016927 = 6025391) B6025391
theorem B5352911 : Blo 1409524 5352911 := bstep (se 1 (by rfl) ⟨4014683, by rfl⟩ : syracuseStep 5352911 = 8029367) B8029367
theorem B2379611 : Blo 1409524 2379611 := bstep (se 1 (by rfl) ⟨1784708, by rfl⟩ : syracuseStep 2379611 = 3569417) B3569417
theorem B48829067 : Blo 1409524 48829067 := bstep (se 1 (by rfl) ⟨36621800, by rfl⟩ : syracuseStep 48829067 = 73243601) B73243601
theorem B12056111 : Blo 1409524 12056111 := bstep (se 1 (by rfl) ⟨9042083, by rfl⟩ : syracuseStep 12056111 = 18084167) B18084167
theorem B24418061 : Blo 1409524 24418061 := bstep (se 3 (by rfl) ⟨4578386, by rfl⟩ : syracuseStep 24418061 = 9156773) B9156773
theorem B3012815 : Blo 1409524 3012815 := bstep (se 1 (by rfl) ⟨2259611, by rfl⟩ : syracuseStep 3012815 = 4519223) B4519223
theorem B12056795 : Blo 1409524 12056795 := bstep (se 1 (by rfl) ⟨9042596, by rfl⟩ : syracuseStep 12056795 = 18085193) B18085193
theorem B10705121 : Blo 1409524 10705121 := bstep (se 2 (by rfl) ⟨4014420, by rfl⟩ : syracuseStep 10705121 = 8028841) B8028841
theorem B5085929 : Blo 1409524 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B5356313 : Blo 1409524 5356313 := bstep (se 2 (by rfl) ⟨2008617, by rfl⟩ : syracuseStep 5356313 = 4017235) B4017235
theorem B4758803 : Blo 1409524 4758803 := bstep (se 1 (by rfl) ⟨3569102, by rfl⟩ : syracuseStep 4758803 = 7138205) B7138205
theorem B7143551 : Blo 1409524 7143551 := bstep (se 1 (by rfl) ⟨5357663, by rfl⟩ : syracuseStep 7143551 = 10715327) B10715327
theorem B7143875 : Blo 1409524 7143875 := bstep (se 1 (by rfl) ⟨5357906, by rfl⟩ : syracuseStep 7143875 = 10715813) B10715813
theorem B2114303 : Blo 1409524 2114303 := bstep (se 1 (by rfl) ⟨1585727, by rfl⟩ : syracuseStep 2114303 = 3171455) B3171455
theorem B1410079 : Blo 1409524 1410079 := bstep (se 1 (by rfl) ⟨1057559, by rfl⟩ : syracuseStep 1410079 = 2115119) B2115119
theorem B8037407 : Blo 1409524 8037407 := bstep (se 1 (by rfl) ⟨6028055, by rfl⟩ : syracuseStep 8037407 = 12056111) B12056111
theorem B16278707 : Blo 1409524 16278707 := bstep (se 1 (by rfl) ⟨12209030, by rfl⟩ : syracuseStep 16278707 = 24418061) B24418061
theorem B8037863 : Blo 1409524 8037863 := bstep (se 1 (by rfl) ⟨6028397, by rfl⟩ : syracuseStep 8037863 = 12056795) B12056795
theorem B7136747 : Blo 1409524 7136747 := bstep (se 1 (by rfl) ⟨5352560, by rfl⟩ : syracuseStep 7136747 = 10705121) B10705121
theorem B1410843 : Blo 1409524 1410843 := bstep (se 1 (by rfl) ⟨1058132, by rfl⟩ : syracuseStep 1410843 = 2116265) B2116265
theorem B3172535 : Blo 1409524 3172535 := bstep (se 1 (by rfl) ⟨2379401, by rfl⟩ : syracuseStep 3172535 = 4758803) B4758803
theorem B12380867 : Blo 1409524 12380867 := bstep (se 1 (by rfl) ⟨9285650, by rfl⟩ : syracuseStep 12380867 = 18571301) B18571301
theorem B13562477 : Blo 1409524 13562477 := bstep (se 3 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 13562477 = 5085929) B5085929
theorem B3568607 : Blo 1409524 3568607 := bstep (se 1 (by rfl) ⟨2676455, by rfl⟩ : syracuseStep 3568607 = 5352911) B5352911
theorem B1586407 : Blo 1409524 1586407 := bstep (se 1 (by rfl) ⟨1189805, by rfl⟩ : syracuseStep 1586407 = 2379611) B2379611
theorem B30922175 : Blo 1409524 30922175 := bstep (se 1 (by rfl) ⟨23191631, by rfl⟩ : syracuseStep 30922175 = 46383263) B46383263
theorem B32552711 : Blo 1409524 32552711 := bstep (se 1 (by rfl) ⟨24414533, by rfl⟩ : syracuseStep 32552711 = 48829067) B48829067
theorem B8034173 : Blo 1409524 8034173 := bstep (se 3 (by rfl) ⟨1506407, by rfl⟩ : syracuseStep 8034173 = 3012815) B3012815
theorem B1002486253 : Blo 1409524 1002486253 := bstep (se 3 (by rfl) ⟨187966172, by rfl⟩ : syracuseStep 1002486253 = 375932345) B375932345
theorem B3570875 : Blo 1409524 3570875 := bstep (se 1 (by rfl) ⟨2678156, by rfl⟩ : syracuseStep 3570875 = 5356313) B5356313
theorem B2677951 : Blo 1409524 2677951 := bstep (se 1 (by rfl) ⟨2008463, by rfl⟩ : syracuseStep 2677951 = 4016927) B4016927
theorem B1409535 : Blo 1409524 1409535 := bstep (se 1 (by rfl) ⟨1057151, by rfl⟩ : syracuseStep 1409535 = 2114303) B2114303
theorem B1336648337 : Blo 1409524 1336648337 := bstep (se 2 (by rfl) ⟨501243126, by rfl⟩ : syracuseStep 1336648337 = 1002486253) B1002486253
theorem B5358271 : Blo 1409524 5358271 := bstep (se 1 (by rfl) ⟨4018703, by rfl⟩ : syracuseStep 5358271 = 8037407) B8037407
theorem B5358575 : Blo 1409524 5358575 := bstep (se 1 (by rfl) ⟨4018931, by rfl⟩ : syracuseStep 5358575 = 8037863) B8037863
theorem B21701807 : Blo 1409524 21701807 := bstep (se 1 (by rfl) ⟨16276355, by rfl⟩ : syracuseStep 21701807 = 32552711) B32552711
theorem B2115023 : Blo 1409524 2115023 := bstep (se 1 (by rfl) ⟨1586267, by rfl⟩ : syracuseStep 2115023 = 3172535) B3172535
theorem B2115209 : Blo 1409524 2115209 := bstep (se 2 (by rfl) ⟨793203, by rfl⟩ : syracuseStep 2115209 = 1586407) B1586407
theorem B4762367 : Blo 1409524 4762367 := bstep (se 1 (by rfl) ⟨3571775, by rfl⟩ : syracuseStep 4762367 = 7143551) B7143551
theorem B4762583 : Blo 1409524 4762583 := bstep (se 1 (by rfl) ⟨3571937, by rfl⟩ : syracuseStep 4762583 = 7143875) B7143875
theorem B2379071 : Blo 1409524 2379071 := bstep (se 1 (by rfl) ⟨1784303, by rfl⟩ : syracuseStep 2379071 = 3568607) B3568607
theorem B20614783 : Blo 1409524 20614783 := bstep (se 1 (by rfl) ⟨15461087, by rfl⟩ : syracuseStep 20614783 = 30922175) B30922175
theorem B8253911 : Blo 1409524 8253911 := bstep (se 1 (by rfl) ⟨6190433, by rfl⟩ : syracuseStep 8253911 = 12380867) B12380867
theorem B2380583 : Blo 1409524 2380583 := bstep (se 1 (by rfl) ⟨1785437, by rfl⟩ : syracuseStep 2380583 = 3570875) B3570875
theorem B9041651 : Blo 1409524 9041651 := bstep (se 1 (by rfl) ⟨6781238, by rfl⟩ : syracuseStep 9041651 = 13562477) B13562477
theorem B10852471 : Blo 1409524 10852471 := bstep (se 1 (by rfl) ⟨8139353, by rfl⟩ : syracuseStep 10852471 = 16278707) B16278707
theorem B4757831 : Blo 1409524 4757831 := bstep (se 1 (by rfl) ⟨3568373, by rfl⟩ : syracuseStep 4757831 = 7136747) B7136747
theorem B5356115 : Blo 1409524 5356115 := bstep (se 1 (by rfl) ⟨4017086, by rfl⟩ : syracuseStep 5356115 = 8034173) B8034173
theorem B3570601 : Blo 1409524 3570601 := bstep (se 2 (by rfl) ⟨1338975, by rfl⟩ : syracuseStep 3570601 = 2677951) B2677951
theorem B3572383 : Blo 1409524 3572383 := bstep (se 1 (by rfl) ⟨2679287, by rfl⟩ : syracuseStep 3572383 = 5358575) B5358575
theorem B14467871 : Blo 1409524 14467871 := bstep (se 1 (by rfl) ⟨10850903, by rfl⟩ : syracuseStep 14467871 = 21701807) B21701807
theorem B7144361 : Blo 1409524 7144361 := bstep (se 2 (by rfl) ⟨2679135, by rfl⟩ : syracuseStep 7144361 = 5358271) B5358271
theorem B1410015 : Blo 1409524 1410015 := bstep (se 1 (by rfl) ⟨1057511, by rfl⟩ : syracuseStep 1410015 = 2115023) B2115023
theorem B1410139 : Blo 1409524 1410139 := bstep (se 1 (by rfl) ⟨1057604, by rfl⟩ : syracuseStep 1410139 = 2115209) B2115209
theorem B4760801 : Blo 1409524 4760801 := bstep (se 2 (by rfl) ⟨1785300, by rfl⟩ : syracuseStep 4760801 = 3570601) B3570601
theorem B3171887 : Blo 1409524 3171887 := bstep (se 1 (by rfl) ⟨2378915, by rfl⟩ : syracuseStep 3171887 = 4757831) B4757831
theorem B27486377 : Blo 1409524 27486377 := bstep (se 2 (by rfl) ⟨10307391, by rfl⟩ : syracuseStep 27486377 = 20614783) B20614783
theorem B57879845 : Blo 1409524 57879845 := bstep (se 4 (by rfl) ⟨5426235, by rfl⟩ : syracuseStep 57879845 = 10852471) B10852471
theorem B3174911 : Blo 1409524 3174911 := bstep (se 1 (by rfl) ⟨2381183, by rfl⟩ : syracuseStep 3174911 = 4762367) B4762367
theorem B3175055 : Blo 1409524 3175055 := bstep (se 1 (by rfl) ⟨2381291, by rfl⟩ : syracuseStep 3175055 = 4762583) B4762583
theorem B1586047 : Blo 1409524 1586047 := bstep (se 1 (by rfl) ⟨1189535, by rfl⟩ : syracuseStep 1586047 = 2379071) B2379071
theorem B891098891 : Blo 1409524 891098891 := bstep (se 1 (by rfl) ⟨668324168, by rfl⟩ : syracuseStep 891098891 = 1336648337) B1336648337
theorem B1587055 : Blo 1409524 1587055 := bstep (se 1 (by rfl) ⟨1190291, by rfl⟩ : syracuseStep 1587055 = 2380583) B2380583
theorem B6027767 : Blo 1409524 6027767 := bstep (se 1 (by rfl) ⟨4520825, by rfl⟩ : syracuseStep 6027767 = 9041651) B9041651
theorem B22010429 : Blo 1409524 22010429 := bstep (se 3 (by rfl) ⟨4126955, by rfl⟩ : syracuseStep 22010429 = 8253911) B8253911
theorem B3570743 : Blo 1409524 3570743 := bstep (se 1 (by rfl) ⟨2678057, by rfl⟩ : syracuseStep 3570743 = 5356115) B5356115
theorem B2114591 : Blo 1409524 2114591 := bstep (se 1 (by rfl) ⟨1585943, by rfl⟩ : syracuseStep 2114591 = 3171887) B3171887
theorem B2114729 : Blo 1409524 2114729 := bstep (se 2 (by rfl) ⟨793023, by rfl⟩ : syracuseStep 2114729 = 1586047) B1586047
theorem B14673619 : Blo 1409524 14673619 := bstep (se 1 (by rfl) ⟨11005214, by rfl⟩ : syracuseStep 14673619 = 22010429) B22010429
theorem B38586563 : Blo 1409524 38586563 := bstep (se 1 (by rfl) ⟨28939922, by rfl⟩ : syracuseStep 38586563 = 57879845) B57879845
theorem B2116073 : Blo 1409524 2116073 := bstep (se 2 (by rfl) ⟨793527, by rfl⟩ : syracuseStep 2116073 = 1587055) B1587055
theorem B2116607 : Blo 1409524 2116607 := bstep (se 1 (by rfl) ⟨1587455, by rfl⟩ : syracuseStep 2116607 = 3174911) B3174911
theorem B2116703 : Blo 1409524 2116703 := bstep (se 1 (by rfl) ⟨1587527, by rfl⟩ : syracuseStep 2116703 = 3175055) B3175055
theorem B9645247 : Blo 1409524 9645247 := bstep (se 1 (by rfl) ⟨7233935, by rfl⟩ : syracuseStep 9645247 = 14467871) B14467871
theorem B4762907 : Blo 1409524 4762907 := bstep (se 1 (by rfl) ⟨3572180, by rfl⟩ : syracuseStep 4762907 = 7144361) B7144361
theorem B3173867 : Blo 1409524 3173867 := bstep (se 1 (by rfl) ⟨2380400, by rfl⟩ : syracuseStep 3173867 = 4760801) B4760801
theorem B4763177 : Blo 1409524 4763177 := bstep (se 2 (by rfl) ⟨1786191, by rfl⟩ : syracuseStep 4763177 = 3572383) B3572383
theorem B4018511 : Blo 1409524 4018511 := bstep (se 1 (by rfl) ⟨3013883, by rfl⟩ : syracuseStep 4018511 = 6027767) B6027767
theorem B2380495 : Blo 1409524 2380495 := bstep (se 1 (by rfl) ⟨1785371, by rfl⟩ : syracuseStep 2380495 = 3570743) B3570743
theorem B594065927 : Blo 1409524 594065927 := bstep (se 1 (by rfl) ⟨445549445, by rfl⟩ : syracuseStep 594065927 = 891098891) B891098891
theorem B18324251 : Blo 1409524 18324251 := bstep (se 1 (by rfl) ⟨13743188, by rfl⟩ : syracuseStep 18324251 = 27486377) B27486377
theorem B2679007 : Blo 1409524 2679007 := bstep (se 1 (by rfl) ⟨2009255, by rfl⟩ : syracuseStep 2679007 = 4018511) B4018511
theorem B1409727 : Blo 1409524 1409727 := bstep (se 1 (by rfl) ⟨1057295, by rfl⟩ : syracuseStep 1409727 = 2114591) B2114591
theorem B1409819 : Blo 1409524 1409819 := bstep (se 1 (by rfl) ⟨1057364, by rfl⟩ : syracuseStep 1409819 = 2114729) B2114729
theorem B78259301 : Blo 1409524 78259301 := bstep (se 4 (by rfl) ⟨7336809, by rfl⟩ : syracuseStep 78259301 = 14673619) B14673619
theorem B25724375 : Blo 1409524 25724375 := bstep (se 1 (by rfl) ⟨19293281, by rfl⟩ : syracuseStep 25724375 = 38586563) B38586563
theorem B1410715 : Blo 1409524 1410715 := bstep (se 1 (by rfl) ⟨1058036, by rfl⟩ : syracuseStep 1410715 = 2116073) B2116073
theorem B396043951 : Blo 1409524 396043951 := bstep (se 1 (by rfl) ⟨297032963, by rfl⟩ : syracuseStep 396043951 = 594065927) B594065927
theorem B12216167 : Blo 1409524 12216167 := bstep (se 1 (by rfl) ⟨9162125, by rfl⟩ : syracuseStep 12216167 = 18324251) B18324251
theorem B1411071 : Blo 1409524 1411071 := bstep (se 1 (by rfl) ⟨1058303, by rfl⟩ : syracuseStep 1411071 = 2116607) B2116607
theorem B1411135 : Blo 1409524 1411135 := bstep (se 1 (by rfl) ⟨1058351, by rfl⟩ : syracuseStep 1411135 = 2116703) B2116703
theorem B2115911 : Blo 1409524 2115911 := bstep (se 1 (by rfl) ⟨1586933, by rfl⟩ : syracuseStep 2115911 = 3173867) B3173867
theorem B3173993 : Blo 1409524 3173993 := bstep (se 2 (by rfl) ⟨1190247, by rfl⟩ : syracuseStep 3173993 = 2380495) B2380495
theorem B51441317 : Blo 1409524 51441317 := bstep (se 4 (by rfl) ⟨4822623, by rfl⟩ : syracuseStep 51441317 = 9645247) B9645247
theorem B3175271 : Blo 1409524 3175271 := bstep (se 1 (by rfl) ⟨2381453, by rfl⟩ : syracuseStep 3175271 = 4762907) B4762907
theorem B3175451 : Blo 1409524 3175451 := bstep (se 1 (by rfl) ⟨2381588, by rfl⟩ : syracuseStep 3175451 = 4763177) B4763177
theorem B3572009 : Blo 1409524 3572009 := bstep (se 2 (by rfl) ⟨1339503, by rfl⟩ : syracuseStep 3572009 = 2679007) B2679007
theorem B8144111 : Blo 1409524 8144111 := bstep (se 1 (by rfl) ⟨6108083, by rfl⟩ : syracuseStep 8144111 = 12216167) B12216167
theorem B1410607 : Blo 1409524 1410607 := bstep (se 1 (by rfl) ⟨1057955, by rfl⟩ : syracuseStep 1410607 = 2115911) B2115911
theorem B528058601 : Blo 1409524 528058601 := bstep (se 2 (by rfl) ⟨198021975, by rfl⟩ : syracuseStep 528058601 = 396043951) B396043951
theorem B2115995 : Blo 1409524 2115995 := bstep (se 1 (by rfl) ⟨1586996, by rfl⟩ : syracuseStep 2115995 = 3173993) B3173993
theorem B34294211 : Blo 1409524 34294211 := bstep (se 1 (by rfl) ⟨25720658, by rfl⟩ : syracuseStep 34294211 = 51441317) B51441317
theorem B2116847 : Blo 1409524 2116847 := bstep (se 1 (by rfl) ⟨1587635, by rfl⟩ : syracuseStep 2116847 = 3175271) B3175271
theorem B2116967 : Blo 1409524 2116967 := bstep (se 1 (by rfl) ⟨1587725, by rfl⟩ : syracuseStep 2116967 = 3175451) B3175451
theorem B17149583 : Blo 1409524 17149583 := bstep (se 1 (by rfl) ⟨12862187, by rfl⟩ : syracuseStep 17149583 = 25724375) B25724375
theorem B52172867 : Blo 1409524 52172867 := bstep (se 1 (by rfl) ⟨39129650, by rfl⟩ : syracuseStep 52172867 = 78259301) B78259301
theorem B21717629 : Blo 1409524 21717629 := bstep (se 3 (by rfl) ⟨4072055, by rfl⟩ : syracuseStep 21717629 = 8144111) B8144111
theorem B1410663 : Blo 1409524 1410663 := bstep (se 1 (by rfl) ⟨1057997, by rfl⟩ : syracuseStep 1410663 = 2115995) B2115995
theorem B1411231 : Blo 1409524 1411231 := bstep (se 1 (by rfl) ⟨1058423, by rfl⟩ : syracuseStep 1411231 = 2116847) B2116847
theorem B1411311 : Blo 1409524 1411311 := bstep (se 1 (by rfl) ⟨1058483, by rfl⟩ : syracuseStep 1411311 = 2116967) B2116967
theorem B139127645 : Blo 1409524 139127645 := bstep (se 3 (by rfl) ⟨26086433, by rfl⟩ : syracuseStep 139127645 = 52172867) B52172867
theorem B352039067 : Blo 1409524 352039067 := bstep (se 1 (by rfl) ⟨264029300, by rfl⟩ : syracuseStep 352039067 = 528058601) B528058601
theorem B45732221 : Blo 1409524 45732221 := bstep (se 3 (by rfl) ⟨8574791, by rfl⟩ : syracuseStep 45732221 = 17149583) B17149583
theorem B2381339 : Blo 1409524 2381339 := bstep (se 1 (by rfl) ⟨1786004, by rfl⟩ : syracuseStep 2381339 = 3572009) B3572009
theorem B22862807 : Blo 1409524 22862807 := bstep (se 1 (by rfl) ⟨17147105, by rfl⟩ : syracuseStep 22862807 = 34294211) B34294211
theorem B234692711 : Blo 1409524 234692711 := bstep (se 1 (by rfl) ⟨176019533, by rfl⟩ : syracuseStep 234692711 = 352039067) B352039067
theorem B92751763 : Blo 1409524 92751763 := bstep (se 1 (by rfl) ⟨69563822, by rfl⟩ : syracuseStep 92751763 = 139127645) B139127645
theorem B14478419 : Blo 1409524 14478419 := bstep (se 1 (by rfl) ⟨10858814, by rfl⟩ : syracuseStep 14478419 = 21717629) B21717629
theorem B15241871 : Blo 1409524 15241871 := bstep (se 1 (by rfl) ⟨11431403, by rfl⟩ : syracuseStep 15241871 = 22862807) B22862807
theorem B30488147 : Blo 1409524 30488147 := bstep (se 1 (by rfl) ⟨22866110, by rfl⟩ : syracuseStep 30488147 = 45732221) B45732221
theorem B1587559 : Blo 1409524 1587559 := bstep (se 1 (by rfl) ⟨1190669, by rfl⟩ : syracuseStep 1587559 = 2381339) B2381339
theorem B20325431 : Blo 1409524 20325431 := bstep (se 1 (by rfl) ⟨15244073, by rfl⟩ : syracuseStep 20325431 = 30488147) B30488147
theorem B9652279 : Blo 1409524 9652279 := bstep (se 1 (by rfl) ⟨7239209, by rfl⟩ : syracuseStep 9652279 = 14478419) B14478419
theorem B123669017 : Blo 1409524 123669017 := bstep (se 2 (by rfl) ⟨46375881, by rfl⟩ : syracuseStep 123669017 = 92751763) B92751763
theorem B156461807 : Blo 1409524 156461807 := bstep (se 1 (by rfl) ⟨117346355, by rfl⟩ : syracuseStep 156461807 = 234692711) B234692711
theorem B10161247 : Blo 1409524 10161247 := bstep (se 1 (by rfl) ⟨7620935, by rfl⟩ : syracuseStep 10161247 = 15241871) B15241871
theorem B2116745 : Blo 1409524 2116745 := bstep (se 2 (by rfl) ⟨793779, by rfl⟩ : syracuseStep 2116745 = 1587559) B1587559
theorem B12869705 : Blo 1409524 12869705 := bstep (se 2 (by rfl) ⟨4826139, by rfl⟩ : syracuseStep 12869705 = 9652279) B9652279
theorem B13550287 : Blo 1409524 13550287 := bstep (se 1 (by rfl) ⟨10162715, by rfl⟩ : syracuseStep 13550287 = 20325431) B20325431
theorem B82446011 : Blo 1409524 82446011 := bstep (se 1 (by rfl) ⟨61834508, by rfl⟩ : syracuseStep 82446011 = 123669017) B123669017
theorem B1411163 : Blo 1409524 1411163 := bstep (se 1 (by rfl) ⟨1058372, by rfl⟩ : syracuseStep 1411163 = 2116745) B2116745
theorem B13548329 : Blo 1409524 13548329 := bstep (se 2 (by rfl) ⟨5080623, by rfl⟩ : syracuseStep 13548329 = 10161247) B10161247
theorem B104307871 : Blo 1409524 104307871 := bstep (se 1 (by rfl) ⟨78230903, by rfl⟩ : syracuseStep 104307871 = 156461807) B156461807
theorem B139077161 : Blo 1409524 139077161 := bstep (se 2 (by rfl) ⟨52153935, by rfl⟩ : syracuseStep 139077161 = 104307871) B104307871
theorem B8579803 : Blo 1409524 8579803 := bstep (se 1 (by rfl) ⟨6434852, by rfl⟩ : syracuseStep 8579803 = 12869705) B12869705
theorem B18067049 : Blo 1409524 18067049 := bstep (se 2 (by rfl) ⟨6775143, by rfl⟩ : syracuseStep 18067049 = 13550287) B13550287
theorem B54964007 : Blo 1409524 54964007 := bstep (se 1 (by rfl) ⟨41223005, by rfl⟩ : syracuseStep 54964007 = 82446011) B82446011
theorem B9032219 : Blo 1409524 9032219 := bstep (se 1 (by rfl) ⟨6774164, by rfl⟩ : syracuseStep 9032219 = 13548329) B13548329
theorem B6021479 : Blo 1409524 6021479 := bstep (se 1 (by rfl) ⟨4516109, by rfl⟩ : syracuseStep 6021479 = 9032219) B9032219
theorem B92718107 : Blo 1409524 92718107 := bstep (se 1 (by rfl) ⟨69538580, by rfl⟩ : syracuseStep 92718107 = 139077161) B139077161
theorem B12044699 : Blo 1409524 12044699 := bstep (se 1 (by rfl) ⟨9033524, by rfl⟩ : syracuseStep 12044699 = 18067049) B18067049
theorem B11439737 : Blo 1409524 11439737 := bstep (se 2 (by rfl) ⟨4289901, by rfl⟩ : syracuseStep 11439737 = 8579803) B8579803
theorem B36642671 : Blo 1409524 36642671 := bstep (se 1 (by rfl) ⟨27482003, by rfl⟩ : syracuseStep 36642671 = 54964007) B54964007
theorem B4014319 : Blo 1409524 4014319 := bstep (se 1 (by rfl) ⟨3010739, by rfl⟩ : syracuseStep 4014319 = 6021479) B6021479
theorem B8029799 : Blo 1409524 8029799 := bstep (se 1 (by rfl) ⟨6022349, by rfl⟩ : syracuseStep 8029799 = 12044699) B12044699
theorem B61812071 : Blo 1409524 61812071 := bstep (se 1 (by rfl) ⟨46359053, by rfl⟩ : syracuseStep 61812071 = 92718107) B92718107
theorem B7626491 : Blo 1409524 7626491 := bstep (se 1 (by rfl) ⟨5719868, by rfl⟩ : syracuseStep 7626491 = 11439737) B11439737
theorem B24428447 : Blo 1409524 24428447 := bstep (se 1 (by rfl) ⟨18321335, by rfl⟩ : syracuseStep 24428447 = 36642671) B36642671
theorem B41208047 : Blo 1409524 41208047 := bstep (se 1 (by rfl) ⟨30906035, by rfl⟩ : syracuseStep 41208047 = 61812071) B61812071
theorem B5352425 : Blo 1409524 5352425 := bstep (se 2 (by rfl) ⟨2007159, by rfl⟩ : syracuseStep 5352425 = 4014319) B4014319
theorem B5353199 : Blo 1409524 5353199 := bstep (se 1 (by rfl) ⟨4014899, by rfl⟩ : syracuseStep 5353199 = 8029799) B8029799
theorem B5084327 : Blo 1409524 5084327 := bstep (se 1 (by rfl) ⟨3813245, by rfl⟩ : syracuseStep 5084327 = 7626491) B7626491
theorem B16285631 : Blo 1409524 16285631 := bstep (se 1 (by rfl) ⟨12214223, by rfl⟩ : syracuseStep 16285631 = 24428447) B24428447
theorem B13558205 : Blo 1409524 13558205 := bstep (se 3 (by rfl) ⟨2542163, by rfl⟩ : syracuseStep 13558205 = 5084327) B5084327
theorem B43428349 : Blo 1409524 43428349 := bstep (se 3 (by rfl) ⟨8142815, by rfl⟩ : syracuseStep 43428349 = 16285631) B16285631
theorem B27472031 : Blo 1409524 27472031 := bstep (se 1 (by rfl) ⟨20604023, by rfl⟩ : syracuseStep 27472031 = 41208047) B41208047
theorem B3568283 : Blo 1409524 3568283 := bstep (se 1 (by rfl) ⟨2676212, by rfl⟩ : syracuseStep 3568283 = 5352425) B5352425
theorem B3568799 : Blo 1409524 3568799 := bstep (se 1 (by rfl) ⟨2676599, by rfl⟩ : syracuseStep 3568799 = 5353199) B5353199
theorem B9038803 : Blo 1409524 9038803 := bstep (se 1 (by rfl) ⟨6779102, by rfl⟩ : syracuseStep 9038803 = 13558205) B13558205
theorem B2378855 : Blo 1409524 2378855 := bstep (se 1 (by rfl) ⟨1784141, by rfl⟩ : syracuseStep 2378855 = 3568283) B3568283
theorem B57904465 : Blo 1409524 57904465 := bstep (se 2 (by rfl) ⟨21714174, by rfl⟩ : syracuseStep 57904465 = 43428349) B43428349
theorem B2379199 : Blo 1409524 2379199 := bstep (se 1 (by rfl) ⟨1784399, by rfl⟩ : syracuseStep 2379199 = 3568799) B3568799
theorem B18314687 : Blo 1409524 18314687 := bstep (se 1 (by rfl) ⟨13736015, by rfl⟩ : syracuseStep 18314687 = 27472031) B27472031
theorem B12051737 : Blo 1409524 12051737 := bstep (se 2 (by rfl) ⟨4519401, by rfl⟩ : syracuseStep 12051737 = 9038803) B9038803
theorem B3172265 : Blo 1409524 3172265 := bstep (se 2 (by rfl) ⟨1189599, by rfl⟩ : syracuseStep 3172265 = 2379199) B2379199
theorem B12209791 : Blo 1409524 12209791 := bstep (se 1 (by rfl) ⟨9157343, by rfl⟩ : syracuseStep 12209791 = 18314687) B18314687
theorem B77205953 : Blo 1409524 77205953 := bstep (se 2 (by rfl) ⟨28952232, by rfl⟩ : syracuseStep 77205953 = 57904465) B57904465
theorem B1585903 : Blo 1409524 1585903 := bstep (se 1 (by rfl) ⟨1189427, by rfl⟩ : syracuseStep 1585903 = 2378855) B2378855
theorem B51470635 : Blo 1409524 51470635 := bstep (se 1 (by rfl) ⟨38602976, by rfl⟩ : syracuseStep 51470635 = 77205953) B77205953
theorem B2114537 : Blo 1409524 2114537 := bstep (se 2 (by rfl) ⟨792951, by rfl⟩ : syracuseStep 2114537 = 1585903) B1585903
theorem B2114843 : Blo 1409524 2114843 := bstep (se 1 (by rfl) ⟨1586132, by rfl⟩ : syracuseStep 2114843 = 3172265) B3172265
theorem B16279721 : Blo 1409524 16279721 := bstep (se 2 (by rfl) ⟨6104895, by rfl⟩ : syracuseStep 16279721 = 12209791) B12209791
theorem B8034491 : Blo 1409524 8034491 := bstep (se 1 (by rfl) ⟨6025868, by rfl⟩ : syracuseStep 8034491 = 12051737) B12051737
theorem B1409691 : Blo 1409524 1409691 := bstep (se 1 (by rfl) ⟨1057268, by rfl⟩ : syracuseStep 1409691 = 2114537) B2114537
theorem B1409895 : Blo 1409524 1409895 := bstep (se 1 (by rfl) ⟨1057421, by rfl⟩ : syracuseStep 1409895 = 2114843) B2114843
theorem B68627513 : Blo 1409524 68627513 := bstep (se 2 (by rfl) ⟨25735317, by rfl⟩ : syracuseStep 68627513 = 51470635) B51470635
theorem B10853147 : Blo 1409524 10853147 := bstep (se 1 (by rfl) ⟨8139860, by rfl⟩ : syracuseStep 10853147 = 16279721) B16279721
theorem B5356327 : Blo 1409524 5356327 := bstep (se 1 (by rfl) ⟨4017245, by rfl⟩ : syracuseStep 5356327 = 8034491) B8034491
theorem B7141769 : Blo 1409524 7141769 := bstep (se 2 (by rfl) ⟨2678163, by rfl⟩ : syracuseStep 7141769 = 5356327) B5356327
theorem B45751675 : Blo 1409524 45751675 := bstep (se 1 (by rfl) ⟨34313756, by rfl⟩ : syracuseStep 45751675 = 68627513) B68627513
theorem B28941725 : Blo 1409524 28941725 := bstep (se 3 (by rfl) ⟨5426573, by rfl⟩ : syracuseStep 28941725 = 10853147) B10853147
theorem B77177933 : Blo 1409524 77177933 := bstep (se 3 (by rfl) ⟨14470862, by rfl⟩ : syracuseStep 77177933 = 28941725) B28941725
theorem B4761179 : Blo 1409524 4761179 := bstep (se 1 (by rfl) ⟨3570884, by rfl⟩ : syracuseStep 4761179 = 7141769) B7141769
theorem B61002233 : Blo 1409524 61002233 := bstep (se 2 (by rfl) ⟨22875837, by rfl⟩ : syracuseStep 61002233 = 45751675) B45751675
theorem B40668155 : Blo 1409524 40668155 := bstep (se 1 (by rfl) ⟨30501116, by rfl⟩ : syracuseStep 40668155 = 61002233) B61002233
theorem B3174119 : Blo 1409524 3174119 := bstep (se 1 (by rfl) ⟨2380589, by rfl⟩ : syracuseStep 3174119 = 4761179) B4761179
theorem B51451955 : Blo 1409524 51451955 := bstep (se 1 (by rfl) ⟨38588966, by rfl⟩ : syracuseStep 51451955 = 77177933) B77177933
theorem B34301303 : Blo 1409524 34301303 := bstep (se 1 (by rfl) ⟨25725977, by rfl⟩ : syracuseStep 34301303 = 51451955) B51451955
theorem B2116079 : Blo 1409524 2116079 := bstep (se 1 (by rfl) ⟨1587059, by rfl⟩ : syracuseStep 2116079 = 3174119) B3174119
theorem B27112103 : Blo 1409524 27112103 := bstep (se 1 (by rfl) ⟨20334077, by rfl⟩ : syracuseStep 27112103 = 40668155) B40668155
theorem B1410719 : Blo 1409524 1410719 := bstep (se 1 (by rfl) ⟨1058039, by rfl⟩ : syracuseStep 1410719 = 2116079) B2116079
theorem B18074735 : Blo 1409524 18074735 := bstep (se 1 (by rfl) ⟨13556051, by rfl⟩ : syracuseStep 18074735 = 27112103) B27112103
theorem B22867535 : Blo 1409524 22867535 := bstep (se 1 (by rfl) ⟨17150651, by rfl⟩ : syracuseStep 22867535 = 34301303) B34301303
theorem B12049823 : Blo 1409524 12049823 := bstep (se 1 (by rfl) ⟨9037367, by rfl⟩ : syracuseStep 12049823 = 18074735) B18074735
theorem B15245023 : Blo 1409524 15245023 := bstep (se 1 (by rfl) ⟨11433767, by rfl⟩ : syracuseStep 15245023 = 22867535) B22867535
theorem B20326697 : Blo 1409524 20326697 := bstep (se 2 (by rfl) ⟨7622511, by rfl⟩ : syracuseStep 20326697 = 15245023) B15245023
theorem B8033215 : Blo 1409524 8033215 := bstep (se 1 (by rfl) ⟨6024911, by rfl⟩ : syracuseStep 8033215 = 12049823) B12049823
theorem B13551131 : Blo 1409524 13551131 := bstep (se 1 (by rfl) ⟨10163348, by rfl⟩ : syracuseStep 13551131 = 20326697) B20326697
theorem B10710953 : Blo 1409524 10710953 := bstep (se 2 (by rfl) ⟨4016607, by rfl⟩ : syracuseStep 10710953 = 8033215) B8033215
theorem B7140635 : Blo 1409524 7140635 := bstep (se 1 (by rfl) ⟨5355476, by rfl⟩ : syracuseStep 7140635 = 10710953) B10710953
theorem B9034087 : Blo 1409524 9034087 := bstep (se 1 (by rfl) ⟨6775565, by rfl⟩ : syracuseStep 9034087 = 13551131) B13551131
theorem B4760423 : Blo 1409524 4760423 := bstep (se 1 (by rfl) ⟨3570317, by rfl⟩ : syracuseStep 4760423 = 7140635) B7140635
theorem B12045449 : Blo 1409524 12045449 := bstep (se 2 (by rfl) ⟨4517043, by rfl⟩ : syracuseStep 12045449 = 9034087) B9034087
theorem B8030299 : Blo 1409524 8030299 := bstep (se 1 (by rfl) ⟨6022724, by rfl⟩ : syracuseStep 8030299 = 12045449) B12045449
theorem B3173615 : Blo 1409524 3173615 := bstep (se 1 (by rfl) ⟨2380211, by rfl⟩ : syracuseStep 3173615 = 4760423) B4760423
theorem B10707065 : Blo 1409524 10707065 := bstep (se 2 (by rfl) ⟨4015149, by rfl⟩ : syracuseStep 10707065 = 8030299) B8030299
theorem B2115743 : Blo 1409524 2115743 := bstep (se 1 (by rfl) ⟨1586807, by rfl⟩ : syracuseStep 2115743 = 3173615) B3173615
theorem B1410495 : Blo 1409524 1410495 := bstep (se 1 (by rfl) ⟨1057871, by rfl⟩ : syracuseStep 1410495 = 2115743) B2115743
theorem B7138043 : Blo 1409524 7138043 := bstep (se 1 (by rfl) ⟨5353532, by rfl⟩ : syracuseStep 7138043 = 10707065) B10707065
theorem B4758695 : Blo 1409524 4758695 := bstep (se 1 (by rfl) ⟨3569021, by rfl⟩ : syracuseStep 4758695 = 7138043) B7138043
theorem B3172463 : Blo 1409524 3172463 := bstep (se 1 (by rfl) ⟨2379347, by rfl⟩ : syracuseStep 3172463 = 4758695) B4758695
theorem B2114975 : Blo 1409524 2114975 := bstep (se 1 (by rfl) ⟨1586231, by rfl⟩ : syracuseStep 2114975 = 3172463) B3172463
theorem B1409983 : Blo 1409524 1409983 := bstep (se 1 (by rfl) ⟨1057487, by rfl⟩ : syracuseStep 1409983 = 2114975) B2114975

theorem C0 (j : ℕ) (h1 : 352381 ≤ j) (h2 : j ≤ 352880) : Blo 1409524 (4 * j + 3) := by
  interval_cases j
  · exact B1409527
  · exact B1409531
  · exact B1409535
  · exact B1409539
  · exact B1409543
  · exact B1409547
  · exact B1409551
  · exact B1409555
  · exact B1409559
  · exact B1409563
  · exact B1409567
  · exact B1409571
  · exact B1409575
  · exact B1409579
  · exact B1409583
  · exact B1409587
  · exact B1409591
  · exact B1409595
  · exact B1409599
  · exact B1409603
  · exact B1409607
  · exact B1409611
  · exact B1409615
  · exact B1409619
  · exact B1409623
  · exact B1409627
  · exact B1409631
  · exact B1409635
  · exact B1409639
  · exact B1409643
  · exact B1409647
  · exact B1409651
  · exact B1409655
  · exact B1409659
  · exact B1409663
  · exact B1409667
  · exact B1409671
  · exact B1409675
  · exact B1409679
  · exact B1409683
  · exact B1409687
  · exact B1409691
  · exact B1409695
  · exact B1409699
  · exact B1409703
  · exact B1409707
  · exact B1409711
  · exact B1409715
  · exact B1409719
  · exact B1409723
  · exact B1409727
  · exact B1409731
  · exact B1409735
  · exact B1409739
  · exact B1409743
  · exact B1409747
  · exact B1409751
  · exact B1409755
  · exact B1409759
  · exact B1409763
  · exact B1409767
  · exact B1409771
  · exact B1409775
  · exact B1409779
  · exact B1409783
  · exact B1409787
  · exact B1409791
  · exact B1409795
  · exact B1409799
  · exact B1409803
  · exact B1409807
  · exact B1409811
  · exact B1409815
  · exact B1409819
  · exact B1409823
  · exact B1409827
  · exact B1409831
  · exact B1409835
  · exact B1409839
  · exact B1409843
  · exact B1409847
  · exact B1409851
  · exact B1409855
  · exact B1409859
  · exact B1409863
  · exact B1409867
  · exact B1409871
  · exact B1409875
  · exact B1409879
  · exact B1409883
  · exact B1409887
  · exact B1409891
  · exact B1409895
  · exact B1409899
  · exact B1409903
  · exact B1409907
  · exact B1409911
  · exact B1409915
  · exact B1409919
  · exact B1409923
  · exact B1409927
  · exact B1409931
  · exact B1409935
  · exact B1409939
  · exact B1409943
  · exact B1409947
  · exact B1409951
  · exact B1409955
  · exact B1409959
  · exact B1409963
  · exact B1409967
  · exact B1409971
  · exact B1409975
  · exact B1409979
  · exact B1409983
  · exact B1409987
  · exact B1409991
  · exact B1409995
  · exact B1409999
  · exact B1410003
  · exact B1410007
  · exact B1410011
  · exact B1410015
  · exact B1410019
  · exact B1410023
  · exact B1410027
  · exact B1410031
  · exact B1410035
  · exact B1410039
  · exact B1410043
  · exact B1410047
  · exact B1410051
  · exact B1410055
  · exact B1410059
  · exact B1410063
  · exact B1410067
  · exact B1410071
  · exact B1410075
  · exact B1410079
  · exact B1410083
  · exact B1410087
  · exact B1410091
  · exact B1410095
  · exact B1410099
  · exact B1410103
  · exact B1410107
  · exact B1410111
  · exact B1410115
  · exact B1410119
  · exact B1410123
  · exact B1410127
  · exact B1410131
  · exact B1410135
  · exact B1410139
  · exact B1410143
  · exact B1410147
  · exact B1410151
  · exact B1410155
  · exact B1410159
  · exact B1410163
  · exact B1410167
  · exact B1410171
  · exact B1410175
  · exact B1410179
  · exact B1410183
  · exact B1410187
  · exact B1410191
  · exact B1410195
  · exact B1410199
  · exact B1410203
  · exact B1410207
  · exact B1410211
  · exact B1410215
  · exact B1410219
  · exact B1410223
  · exact B1410227
  · exact B1410231
  · exact B1410235
  · exact B1410239
  · exact B1410243
  · exact B1410247
  · exact B1410251
  · exact B1410255
  · exact B1410259
  · exact B1410263
  · exact B1410267
  · exact B1410271
  · exact B1410275
  · exact B1410279
  · exact B1410283
  · exact B1410287
  · exact B1410291
  · exact B1410295
  · exact B1410299
  · exact B1410303
  · exact B1410307
  · exact B1410311
  · exact B1410315
  · exact B1410319
  · exact B1410323
  · exact B1410327
  · exact B1410331
  · exact B1410335
  · exact B1410339
  · exact B1410343
  · exact B1410347
  · exact B1410351
  · exact B1410355
  · exact B1410359
  · exact B1410363
  · exact B1410367
  · exact B1410371
  · exact B1410375
  · exact B1410379
  · exact B1410383
  · exact B1410387
  · exact B1410391
  · exact B1410395
  · exact B1410399
  · exact B1410403
  · exact B1410407
  · exact B1410411
  · exact B1410415
  · exact B1410419
  · exact B1410423
  · exact B1410427
  · exact B1410431
  · exact B1410435
  · exact B1410439
  · exact B1410443
  · exact B1410447
  · exact B1410451
  · exact B1410455
  · exact B1410459
  · exact B1410463
  · exact B1410467
  · exact B1410471
  · exact B1410475
  · exact B1410479
  · exact B1410483
  · exact B1410487
  · exact B1410491
  · exact B1410495
  · exact B1410499
  · exact B1410503
  · exact B1410507
  · exact B1410511
  · exact B1410515
  · exact B1410519
  · exact B1410523
  · exact B1410527
  · exact B1410531
  · exact B1410535
  · exact B1410539
  · exact B1410543
  · exact B1410547
  · exact B1410551
  · exact B1410555
  · exact B1410559
  · exact B1410563
  · exact B1410567
  · exact B1410571
  · exact B1410575
  · exact B1410579
  · exact B1410583
  · exact B1410587
  · exact B1410591
  · exact B1410595
  · exact B1410599
  · exact B1410603
  · exact B1410607
  · exact B1410611
  · exact B1410615
  · exact B1410619
  · exact B1410623
  · exact B1410627
  · exact B1410631
  · exact B1410635
  · exact B1410639
  · exact B1410643
  · exact B1410647
  · exact B1410651
  · exact B1410655
  · exact B1410659
  · exact B1410663
  · exact B1410667
  · exact B1410671
  · exact B1410675
  · exact B1410679
  · exact B1410683
  · exact B1410687
  · exact B1410691
  · exact B1410695
  · exact B1410699
  · exact B1410703
  · exact B1410707
  · exact B1410711
  · exact B1410715
  · exact B1410719
  · exact B1410723
  · exact B1410727
  · exact B1410731
  · exact B1410735
  · exact B1410739
  · exact B1410743
  · exact B1410747
  · exact B1410751
  · exact B1410755
  · exact B1410759
  · exact B1410763
  · exact B1410767
  · exact B1410771
  · exact B1410775
  · exact B1410779
  · exact B1410783
  · exact B1410787
  · exact B1410791
  · exact B1410795
  · exact B1410799
  · exact B1410803
  · exact B1410807
  · exact B1410811
  · exact B1410815
  · exact B1410819
  · exact B1410823
  · exact B1410827
  · exact B1410831
  · exact B1410835
  · exact B1410839
  · exact B1410843
  · exact B1410847
  · exact B1410851
  · exact B1410855
  · exact B1410859
  · exact B1410863
  · exact B1410867
  · exact B1410871
  · exact B1410875
  · exact B1410879
  · exact B1410883
  · exact B1410887
  · exact B1410891
  · exact B1410895
  · exact B1410899
  · exact B1410903
  · exact B1410907
  · exact B1410911
  · exact B1410915
  · exact B1410919
  · exact B1410923
  · exact B1410927
  · exact B1410931
  · exact B1410935
  · exact B1410939
  · exact B1410943
  · exact B1410947
  · exact B1410951
  · exact B1410955
  · exact B1410959
  · exact B1410963
  · exact B1410967
  · exact B1410971
  · exact B1410975
  · exact B1410979
  · exact B1410983
  · exact B1410987
  · exact B1410991
  · exact B1410995
  · exact B1410999
  · exact B1411003
  · exact B1411007
  · exact B1411011
  · exact B1411015
  · exact B1411019
  · exact B1411023
  · exact B1411027
  · exact B1411031
  · exact B1411035
  · exact B1411039
  · exact B1411043
  · exact B1411047
  · exact B1411051
  · exact B1411055
  · exact B1411059
  · exact B1411063
  · exact B1411067
  · exact B1411071
  · exact B1411075
  · exact B1411079
  · exact B1411083
  · exact B1411087
  · exact B1411091
  · exact B1411095
  · exact B1411099
  · exact B1411103
  · exact B1411107
  · exact B1411111
  · exact B1411115
  · exact B1411119
  · exact B1411123
  · exact B1411127
  · exact B1411131
  · exact B1411135
  · exact B1411139
  · exact B1411143
  · exact B1411147
  · exact B1411151
  · exact B1411155
  · exact B1411159
  · exact B1411163
  · exact B1411167
  · exact B1411171
  · exact B1411175
  · exact B1411179
  · exact B1411183
  · exact B1411187
  · exact B1411191
  · exact B1411195
  · exact B1411199
  · exact B1411203
  · exact B1411207
  · exact B1411211
  · exact B1411215
  · exact B1411219
  · exact B1411223
  · exact B1411227
  · exact B1411231
  · exact B1411235
  · exact B1411239
  · exact B1411243
  · exact B1411247
  · exact B1411251
  · exact B1411255
  · exact B1411259
  · exact B1411263
  · exact B1411267
  · exact B1411271
  · exact B1411275
  · exact B1411279
  · exact B1411283
  · exact B1411287
  · exact B1411291
  · exact B1411295
  · exact B1411299
  · exact B1411303
  · exact B1411307
  · exact B1411311
  · exact B1411315
  · exact B1411319
  · exact B1411323
  · exact B1411327
  · exact B1411331
  · exact B1411335
  · exact B1411339
  · exact B1411343
  · exact B1411347
  · exact B1411351
  · exact B1411355
  · exact B1411359
  · exact B1411363
  · exact B1411367
  · exact B1411371
  · exact B1411375
  · exact B1411379
  · exact B1411383
  · exact B1411387
  · exact B1411391
  · exact B1411395
  · exact B1411399
  · exact B1411403
  · exact B1411407
  · exact B1411411
  · exact B1411415
  · exact B1411419
  · exact B1411423
  · exact B1411427
  · exact B1411431
  · exact B1411435
  · exact B1411439
  · exact B1411443
  · exact B1411447
  · exact B1411451
  · exact B1411455
  · exact B1411459
  · exact B1411463
  · exact B1411467
  · exact B1411471
  · exact B1411475
  · exact B1411479
  · exact B1411483
  · exact B1411487
  · exact B1411491
  · exact B1411495
  · exact B1411499
  · exact B1411503
  · exact B1411507
  · exact B1411511
  · exact B1411515
  · exact B1411519
  · exact B1411523

theorem solution (m : ℕ) (hlo : 1409524 ≤ m) (hhi : m ≤ 1411524) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 352381 ≤ j := by omega
    have hj2 : j ≤ 352880 := by omega
    have hb : Blo 1409524 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
