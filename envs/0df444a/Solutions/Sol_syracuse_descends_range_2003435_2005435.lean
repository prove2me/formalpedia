-- Prove2me | solution 1 for syracuse_descends_range_2003435_2005435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:35.841877+00:00
-- url     : https://prove2.me/submissions/5e622edb-3e16-49ff-afc1-83d19d4f9a5a

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

theorem B2253865 : Blo 2003435 2253865 := bbase (se 2 (by rfl) ⟨845199, by rfl⟩ : syracuseStep 2253865 = 1690399) (by norm_num)
theorem B3005153 : Blo 2003435 3005153 := bstep (se 2 (by rfl) ⟨1126932, by rfl⟩ : syracuseStep 3005153 = 2253865) B2253865
theorem B2003435 : Blo 2003435 2003435 := bstep (se 1 (by rfl) ⟨1502576, by rfl⟩ : syracuseStep 2003435 = 3005153) B3005153
theorem B5140397 : Blo 2003435 5140397 := bbase (se 3 (by rfl) ⟨963824, by rfl⟩ : syracuseStep 5140397 = 1927649) (by norm_num)
theorem B3426931 : Blo 2003435 3426931 := bstep (se 1 (by rfl) ⟨2570198, by rfl⟩ : syracuseStep 3426931 = 5140397) B5140397
theorem B18276965 : Blo 2003435 18276965 := bstep (se 4 (by rfl) ⟨1713465, by rfl⟩ : syracuseStep 18276965 = 3426931) B3426931
theorem B12184643 : Blo 2003435 12184643 := bstep (se 1 (by rfl) ⟨9138482, by rfl⟩ : syracuseStep 12184643 = 18276965) B18276965
theorem B8123095 : Blo 2003435 8123095 := bstep (se 1 (by rfl) ⟨6092321, by rfl⟩ : syracuseStep 8123095 = 12184643) B12184643
theorem B43323173 : Blo 2003435 43323173 := bstep (se 4 (by rfl) ⟨4061547, by rfl⟩ : syracuseStep 43323173 = 8123095) B8123095
theorem B28882115 : Blo 2003435 28882115 := bstep (se 1 (by rfl) ⟨21661586, by rfl⟩ : syracuseStep 28882115 = 43323173) B43323173
theorem B19254743 : Blo 2003435 19254743 := bstep (se 1 (by rfl) ⟨14441057, by rfl⟩ : syracuseStep 19254743 = 28882115) B28882115
theorem B12836495 : Blo 2003435 12836495 := bstep (se 1 (by rfl) ⟨9627371, by rfl⟩ : syracuseStep 12836495 = 19254743) B19254743
theorem B8557663 : Blo 2003435 8557663 := bstep (se 1 (by rfl) ⟨6418247, by rfl⟩ : syracuseStep 8557663 = 12836495) B12836495
theorem B11410217 : Blo 2003435 11410217 := bstep (se 2 (by rfl) ⟨4278831, by rfl⟩ : syracuseStep 11410217 = 8557663) B8557663
theorem B7606811 : Blo 2003435 7606811 := bstep (se 1 (by rfl) ⟨5705108, by rfl⟩ : syracuseStep 7606811 = 11410217) B11410217
theorem B5071207 : Blo 2003435 5071207 := bstep (se 1 (by rfl) ⟨3803405, by rfl⟩ : syracuseStep 5071207 = 7606811) B7606811
theorem B6761609 : Blo 2003435 6761609 := bstep (se 2 (by rfl) ⟨2535603, by rfl⟩ : syracuseStep 6761609 = 5071207) B5071207
theorem B4507739 : Blo 2003435 4507739 := bstep (se 1 (by rfl) ⟨3380804, by rfl⟩ : syracuseStep 4507739 = 6761609) B6761609
theorem B3005159 : Blo 2003435 3005159 := bstep (se 1 (by rfl) ⟨2253869, by rfl⟩ : syracuseStep 3005159 = 4507739) B4507739
theorem B2003439 : Blo 2003435 2003439 := bstep (se 1 (by rfl) ⟨1502579, by rfl⟩ : syracuseStep 2003439 = 3005159) B3005159
theorem B3005165 : Blo 2003435 3005165 := bbase (se 3 (by rfl) ⟨563468, by rfl⟩ : syracuseStep 3005165 = 1126937) (by norm_num)
theorem B2003443 : Blo 2003435 2003443 := bstep (se 1 (by rfl) ⟨1502582, by rfl⟩ : syracuseStep 2003443 = 3005165) B3005165
theorem B4507757 : Blo 2003435 4507757 := bbase (se 3 (by rfl) ⟨845204, by rfl⟩ : syracuseStep 4507757 = 1690409) (by norm_num)
theorem B3005171 : Blo 2003435 3005171 := bstep (se 1 (by rfl) ⟨2253878, by rfl⟩ : syracuseStep 3005171 = 4507757) B4507757
theorem B2003447 : Blo 2003435 2003447 := bstep (se 1 (by rfl) ⟨1502585, by rfl⟩ : syracuseStep 2003447 = 3005171) B3005171
theorem B3803429 : Blo 2003435 3803429 := bbase (se 4 (by rfl) ⟨356571, by rfl⟩ : syracuseStep 3803429 = 713143) (by norm_num)
theorem B2535619 : Blo 2003435 2535619 := bstep (se 1 (by rfl) ⟨1901714, by rfl⟩ : syracuseStep 2535619 = 3803429) B3803429
theorem B3380825 : Blo 2003435 3380825 := bstep (se 2 (by rfl) ⟨1267809, by rfl⟩ : syracuseStep 3380825 = 2535619) B2535619
theorem B2253883 : Blo 2003435 2253883 := bstep (se 1 (by rfl) ⟨1690412, by rfl⟩ : syracuseStep 2253883 = 3380825) B3380825
theorem B3005177 : Blo 2003435 3005177 := bstep (se 2 (by rfl) ⟨1126941, by rfl⟩ : syracuseStep 3005177 = 2253883) B2253883
theorem B2003451 : Blo 2003435 2003451 := bstep (se 1 (by rfl) ⟨1502588, by rfl⟩ : syracuseStep 2003451 = 3005177) B3005177
theorem B18277109 : Blo 2003435 18277109 := bbase (se 5 (by rfl) ⟨856739, by rfl⟩ : syracuseStep 18277109 = 1713479) (by norm_num)
theorem B12184739 : Blo 2003435 12184739 := bstep (se 1 (by rfl) ⟨9138554, by rfl⟩ : syracuseStep 12184739 = 18277109) B18277109
theorem B8123159 : Blo 2003435 8123159 := bstep (se 1 (by rfl) ⟨6092369, by rfl⟩ : syracuseStep 8123159 = 12184739) B12184739
theorem B21661757 : Blo 2003435 21661757 := bstep (se 3 (by rfl) ⟨4061579, by rfl⟩ : syracuseStep 21661757 = 8123159) B8123159
theorem B14441171 : Blo 2003435 14441171 := bstep (se 1 (by rfl) ⟨10830878, by rfl⟩ : syracuseStep 14441171 = 21661757) B21661757
theorem B38509789 : Blo 2003435 38509789 := bstep (se 3 (by rfl) ⟨7220585, by rfl⟩ : syracuseStep 38509789 = 14441171) B14441171
theorem B51346385 : Blo 2003435 51346385 := bstep (se 2 (by rfl) ⟨19254894, by rfl⟩ : syracuseStep 51346385 = 38509789) B38509789
theorem B34230923 : Blo 2003435 34230923 := bstep (se 1 (by rfl) ⟨25673192, by rfl⟩ : syracuseStep 34230923 = 51346385) B51346385
theorem B22820615 : Blo 2003435 22820615 := bstep (se 1 (by rfl) ⟨17115461, by rfl⟩ : syracuseStep 22820615 = 34230923) B34230923
theorem B15213743 : Blo 2003435 15213743 := bstep (se 1 (by rfl) ⟨11410307, by rfl⟩ : syracuseStep 15213743 = 22820615) B22820615
theorem B10142495 : Blo 2003435 10142495 := bstep (se 1 (by rfl) ⟨7606871, by rfl⟩ : syracuseStep 10142495 = 15213743) B15213743
theorem B6761663 : Blo 2003435 6761663 := bstep (se 1 (by rfl) ⟨5071247, by rfl⟩ : syracuseStep 6761663 = 10142495) B10142495
theorem B4507775 : Blo 2003435 4507775 := bstep (se 1 (by rfl) ⟨3380831, by rfl⟩ : syracuseStep 4507775 = 6761663) B6761663
theorem B3005183 : Blo 2003435 3005183 := bstep (se 1 (by rfl) ⟨2253887, by rfl⟩ : syracuseStep 3005183 = 4507775) B4507775
theorem B2003455 : Blo 2003435 2003455 := bstep (se 1 (by rfl) ⟨1502591, by rfl⟩ : syracuseStep 2003455 = 3005183) B3005183
theorem B3005189 : Blo 2003435 3005189 := bbase (se 4 (by rfl) ⟨281736, by rfl⟩ : syracuseStep 3005189 = 563473) (by norm_num)
theorem B2003459 : Blo 2003435 2003459 := bstep (se 1 (by rfl) ⟨1502594, by rfl⟩ : syracuseStep 2003459 = 3005189) B3005189
theorem B3380845 : Blo 2003435 3380845 := bbase (se 3 (by rfl) ⟨633908, by rfl⟩ : syracuseStep 3380845 = 1267817) (by norm_num)
theorem B4507793 : Blo 2003435 4507793 := bstep (se 2 (by rfl) ⟨1690422, by rfl⟩ : syracuseStep 4507793 = 3380845) B3380845
theorem B3005195 : Blo 2003435 3005195 := bstep (se 1 (by rfl) ⟨2253896, by rfl⟩ : syracuseStep 3005195 = 4507793) B4507793
theorem B2003463 : Blo 2003435 2003463 := bstep (se 1 (by rfl) ⟨1502597, by rfl⟩ : syracuseStep 2003463 = 3005195) B3005195
theorem B2253901 : Blo 2003435 2253901 := bbase (se 3 (by rfl) ⟨422606, by rfl⟩ : syracuseStep 2253901 = 845213) (by norm_num)
theorem B3005201 : Blo 2003435 3005201 := bstep (se 2 (by rfl) ⟨1126950, by rfl⟩ : syracuseStep 3005201 = 2253901) B2253901
theorem B2003467 : Blo 2003435 2003467 := bstep (se 1 (by rfl) ⟨1502600, by rfl⟩ : syracuseStep 2003467 = 3005201) B3005201
theorem B6761717 : Blo 2003435 6761717 := bbase (se 5 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 6761717 = 633911) (by norm_num)
theorem B4507811 : Blo 2003435 4507811 := bstep (se 1 (by rfl) ⟨3380858, by rfl⟩ : syracuseStep 4507811 = 6761717) B6761717
theorem B3005207 : Blo 2003435 3005207 := bstep (se 1 (by rfl) ⟨2253905, by rfl⟩ : syracuseStep 3005207 = 4507811) B4507811
theorem B2003471 : Blo 2003435 2003471 := bstep (se 1 (by rfl) ⟨1502603, by rfl⟩ : syracuseStep 2003471 = 3005207) B3005207
theorem B3005213 : Blo 2003435 3005213 := bbase (se 3 (by rfl) ⟨563477, by rfl⟩ : syracuseStep 3005213 = 1126955) (by norm_num)
theorem B2003475 : Blo 2003435 2003475 := bstep (se 1 (by rfl) ⟨1502606, by rfl⟩ : syracuseStep 2003475 = 3005213) B3005213
theorem B4507829 : Blo 2003435 4507829 := bbase (se 5 (by rfl) ⟨211304, by rfl⟩ : syracuseStep 4507829 = 422609) (by norm_num)
theorem B3005219 : Blo 2003435 3005219 := bstep (se 1 (by rfl) ⟨2253914, by rfl⟩ : syracuseStep 3005219 = 4507829) B4507829
theorem B2003479 : Blo 2003435 2003479 := bstep (se 1 (by rfl) ⟨1502609, by rfl⟩ : syracuseStep 2003479 = 3005219) B3005219
theorem B4337309 : Blo 2003435 4337309 := bbase (se 3 (by rfl) ⟨813245, by rfl⟩ : syracuseStep 4337309 = 1626491) (by norm_num)
theorem B2891539 : Blo 2003435 2891539 := bstep (se 1 (by rfl) ⟨2168654, by rfl⟩ : syracuseStep 2891539 = 4337309) B4337309
theorem B3855385 : Blo 2003435 3855385 := bstep (se 2 (by rfl) ⟨1445769, by rfl⟩ : syracuseStep 3855385 = 2891539) B2891539
theorem B5140513 : Blo 2003435 5140513 := bstep (se 2 (by rfl) ⟨1927692, by rfl⟩ : syracuseStep 5140513 = 3855385) B3855385
theorem B6854017 : Blo 2003435 6854017 := bstep (se 2 (by rfl) ⟨2570256, by rfl⟩ : syracuseStep 6854017 = 5140513) B5140513
theorem B9138689 : Blo 2003435 9138689 := bstep (se 2 (by rfl) ⟨3427008, by rfl⟩ : syracuseStep 9138689 = 6854017) B6854017
theorem B6092459 : Blo 2003435 6092459 := bstep (se 1 (by rfl) ⟨4569344, by rfl⟩ : syracuseStep 6092459 = 9138689) B9138689
theorem B4061639 : Blo 2003435 4061639 := bstep (se 1 (by rfl) ⟨3046229, by rfl⟩ : syracuseStep 4061639 = 6092459) B6092459
theorem B2707759 : Blo 2003435 2707759 := bstep (se 1 (by rfl) ⟨2030819, by rfl⟩ : syracuseStep 2707759 = 4061639) B4061639
theorem B3610345 : Blo 2003435 3610345 := bstep (se 2 (by rfl) ⟨1353879, by rfl⟩ : syracuseStep 3610345 = 2707759) B2707759
theorem B4813793 : Blo 2003435 4813793 := bstep (se 2 (by rfl) ⟨1805172, by rfl⟩ : syracuseStep 4813793 = 3610345) B3610345
theorem B3209195 : Blo 2003435 3209195 := bstep (se 1 (by rfl) ⟨2406896, by rfl⟩ : syracuseStep 3209195 = 4813793) B4813793
theorem B2139463 : Blo 2003435 2139463 := bstep (se 1 (by rfl) ⟨1604597, by rfl⟩ : syracuseStep 2139463 = 3209195) B3209195
theorem B11410469 : Blo 2003435 11410469 := bstep (se 4 (by rfl) ⟨1069731, by rfl⟩ : syracuseStep 11410469 = 2139463) B2139463
theorem B7606979 : Blo 2003435 7606979 := bstep (se 1 (by rfl) ⟨5705234, by rfl⟩ : syracuseStep 7606979 = 11410469) B11410469
theorem B5071319 : Blo 2003435 5071319 := bstep (se 1 (by rfl) ⟨3803489, by rfl⟩ : syracuseStep 5071319 = 7606979) B7606979
theorem B3380879 : Blo 2003435 3380879 := bstep (se 1 (by rfl) ⟨2535659, by rfl⟩ : syracuseStep 3380879 = 5071319) B5071319
theorem B2253919 : Blo 2003435 2253919 := bstep (se 1 (by rfl) ⟨1690439, by rfl⟩ : syracuseStep 2253919 = 3380879) B3380879
theorem B3005225 : Blo 2003435 3005225 := bstep (se 2 (by rfl) ⟨1126959, by rfl⟩ : syracuseStep 3005225 = 2253919) B2253919
theorem B2003483 : Blo 2003435 2003483 := bstep (se 1 (by rfl) ⟨1502612, by rfl⟩ : syracuseStep 2003483 = 3005225) B3005225
theorem B2406901 : Blo 2003435 2406901 := bbase (se 5 (by rfl) ⟨112823, by rfl⟩ : syracuseStep 2406901 = 225647) (by norm_num)
theorem B3209201 : Blo 2003435 3209201 := bstep (se 2 (by rfl) ⟨1203450, by rfl⟩ : syracuseStep 3209201 = 2406901) B2406901
theorem B2139467 : Blo 2003435 2139467 := bstep (se 1 (by rfl) ⟨1604600, by rfl⟩ : syracuseStep 2139467 = 3209201) B3209201
theorem B5705245 : Blo 2003435 5705245 := bstep (se 3 (by rfl) ⟨1069733, by rfl⟩ : syracuseStep 5705245 = 2139467) B2139467
theorem B7606993 : Blo 2003435 7606993 := bstep (se 2 (by rfl) ⟨2852622, by rfl⟩ : syracuseStep 7606993 = 5705245) B5705245
theorem B10142657 : Blo 2003435 10142657 := bstep (se 2 (by rfl) ⟨3803496, by rfl⟩ : syracuseStep 10142657 = 7606993) B7606993
theorem B6761771 : Blo 2003435 6761771 := bstep (se 1 (by rfl) ⟨5071328, by rfl⟩ : syracuseStep 6761771 = 10142657) B10142657
theorem B4507847 : Blo 2003435 4507847 := bstep (se 1 (by rfl) ⟨3380885, by rfl⟩ : syracuseStep 4507847 = 6761771) B6761771
theorem B3005231 : Blo 2003435 3005231 := bstep (se 1 (by rfl) ⟨2253923, by rfl⟩ : syracuseStep 3005231 = 4507847) B4507847
theorem B2003487 : Blo 2003435 2003487 := bstep (se 1 (by rfl) ⟨1502615, by rfl⟩ : syracuseStep 2003487 = 3005231) B3005231
theorem B3005237 : Blo 2003435 3005237 := bbase (se 5 (by rfl) ⟨140870, by rfl⟩ : syracuseStep 3005237 = 281741) (by norm_num)
theorem B2003491 : Blo 2003435 2003491 := bstep (se 1 (by rfl) ⟨1502618, by rfl⟩ : syracuseStep 2003491 = 3005237) B3005237
theorem B5071349 : Blo 2003435 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B3380899 : Blo 2003435 3380899 := bstep (se 1 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 3380899 = 5071349) B5071349
theorem B4507865 : Blo 2003435 4507865 := bstep (se 2 (by rfl) ⟨1690449, by rfl⟩ : syracuseStep 4507865 = 3380899) B3380899
theorem B3005243 : Blo 2003435 3005243 := bstep (se 1 (by rfl) ⟨2253932, by rfl⟩ : syracuseStep 3005243 = 4507865) B4507865
theorem B2003495 : Blo 2003435 2003495 := bstep (se 1 (by rfl) ⟨1502621, by rfl⟩ : syracuseStep 2003495 = 3005243) B3005243
theorem B2253937 : Blo 2003435 2253937 := bbase (se 2 (by rfl) ⟨845226, by rfl⟩ : syracuseStep 2253937 = 1690453) (by norm_num)
theorem B3005249 : Blo 2003435 3005249 := bstep (se 2 (by rfl) ⟨1126968, by rfl⟩ : syracuseStep 3005249 = 2253937) B2253937
theorem B2003499 : Blo 2003435 2003499 := bstep (se 1 (by rfl) ⟨1502624, by rfl⟩ : syracuseStep 2003499 = 3005249) B3005249
theorem B6418453 : Blo 2003435 6418453 := bbase (se 6 (by rfl) ⟨150432, by rfl⟩ : syracuseStep 6418453 = 300865) (by norm_num)
theorem B8557937 : Blo 2003435 8557937 := bstep (se 2 (by rfl) ⟨3209226, by rfl⟩ : syracuseStep 8557937 = 6418453) B6418453
theorem B5705291 : Blo 2003435 5705291 := bstep (se 1 (by rfl) ⟨4278968, by rfl⟩ : syracuseStep 5705291 = 8557937) B8557937
theorem B3803527 : Blo 2003435 3803527 := bstep (se 1 (by rfl) ⟨2852645, by rfl⟩ : syracuseStep 3803527 = 5705291) B5705291
theorem B5071369 : Blo 2003435 5071369 := bstep (se 2 (by rfl) ⟨1901763, by rfl⟩ : syracuseStep 5071369 = 3803527) B3803527
theorem B6761825 : Blo 2003435 6761825 := bstep (se 2 (by rfl) ⟨2535684, by rfl⟩ : syracuseStep 6761825 = 5071369) B5071369
theorem B4507883 : Blo 2003435 4507883 := bstep (se 1 (by rfl) ⟨3380912, by rfl⟩ : syracuseStep 4507883 = 6761825) B6761825
theorem B3005255 : Blo 2003435 3005255 := bstep (se 1 (by rfl) ⟨2253941, by rfl⟩ : syracuseStep 3005255 = 4507883) B4507883
theorem B2003503 : Blo 2003435 2003503 := bstep (se 1 (by rfl) ⟨1502627, by rfl⟩ : syracuseStep 2003503 = 3005255) B3005255
theorem B3005261 : Blo 2003435 3005261 := bbase (se 3 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 3005261 = 1126973) (by norm_num)
theorem B2003507 : Blo 2003435 2003507 := bstep (se 1 (by rfl) ⟨1502630, by rfl⟩ : syracuseStep 2003507 = 3005261) B3005261
theorem B4507901 : Blo 2003435 4507901 := bbase (se 3 (by rfl) ⟨845231, by rfl⟩ : syracuseStep 4507901 = 1690463) (by norm_num)
theorem B3005267 : Blo 2003435 3005267 := bstep (se 1 (by rfl) ⟨2253950, by rfl⟩ : syracuseStep 3005267 = 4507901) B4507901
theorem B2003511 : Blo 2003435 2003511 := bstep (se 1 (by rfl) ⟨1502633, by rfl⟩ : syracuseStep 2003511 = 3005267) B3005267
theorem B3380933 : Blo 2003435 3380933 := bbase (se 4 (by rfl) ⟨316962, by rfl⟩ : syracuseStep 3380933 = 633925) (by norm_num)
theorem B2253955 : Blo 2003435 2253955 := bstep (se 1 (by rfl) ⟨1690466, by rfl⟩ : syracuseStep 2253955 = 3380933) B3380933
theorem B3005273 : Blo 2003435 3005273 := bstep (se 2 (by rfl) ⟨1126977, by rfl⟩ : syracuseStep 3005273 = 2253955) B2253955
theorem B2003515 : Blo 2003435 2003515 := bstep (se 1 (by rfl) ⟨1502636, by rfl⟩ : syracuseStep 2003515 = 3005273) B3005273
theorem B15214229 : Blo 2003435 15214229 := bbase (se 6 (by rfl) ⟨356583, by rfl⟩ : syracuseStep 15214229 = 713167) (by norm_num)
theorem B10142819 : Blo 2003435 10142819 := bstep (se 1 (by rfl) ⟨7607114, by rfl⟩ : syracuseStep 10142819 = 15214229) B15214229
theorem B6761879 : Blo 2003435 6761879 := bstep (se 1 (by rfl) ⟨5071409, by rfl⟩ : syracuseStep 6761879 = 10142819) B10142819
theorem B4507919 : Blo 2003435 4507919 := bstep (se 1 (by rfl) ⟨3380939, by rfl⟩ : syracuseStep 4507919 = 6761879) B6761879
theorem B3005279 : Blo 2003435 3005279 := bstep (se 1 (by rfl) ⟨2253959, by rfl⟩ : syracuseStep 3005279 = 4507919) B4507919
theorem B2003519 : Blo 2003435 2003519 := bstep (se 1 (by rfl) ⟨1502639, by rfl⟩ : syracuseStep 2003519 = 3005279) B3005279
theorem B3005285 : Blo 2003435 3005285 := bbase (se 4 (by rfl) ⟨281745, by rfl⟩ : syracuseStep 3005285 = 563491) (by norm_num)
theorem B2003523 : Blo 2003435 2003523 := bstep (se 1 (by rfl) ⟨1502642, by rfl⟩ : syracuseStep 2003523 = 3005285) B3005285
theorem B3803573 : Blo 2003435 3803573 := bbase (se 5 (by rfl) ⟨178292, by rfl⟩ : syracuseStep 3803573 = 356585) (by norm_num)
theorem B2535715 : Blo 2003435 2535715 := bstep (se 1 (by rfl) ⟨1901786, by rfl⟩ : syracuseStep 2535715 = 3803573) B3803573
theorem B3380953 : Blo 2003435 3380953 := bstep (se 2 (by rfl) ⟨1267857, by rfl⟩ : syracuseStep 3380953 = 2535715) B2535715
theorem B4507937 : Blo 2003435 4507937 := bstep (se 2 (by rfl) ⟨1690476, by rfl⟩ : syracuseStep 4507937 = 3380953) B3380953
theorem B3005291 : Blo 2003435 3005291 := bstep (se 1 (by rfl) ⟨2253968, by rfl⟩ : syracuseStep 3005291 = 4507937) B4507937
theorem B2003527 : Blo 2003435 2003527 := bstep (se 1 (by rfl) ⟨1502645, by rfl⟩ : syracuseStep 2003527 = 3005291) B3005291
theorem B2253973 : Blo 2003435 2253973 := bbase (se 6 (by rfl) ⟨52827, by rfl⟩ : syracuseStep 2253973 = 105655) (by norm_num)
theorem B3005297 : Blo 2003435 3005297 := bstep (se 2 (by rfl) ⟨1126986, by rfl⟩ : syracuseStep 3005297 = 2253973) B2253973
theorem B2003531 : Blo 2003435 2003531 := bstep (se 1 (by rfl) ⟨1502648, by rfl⟩ : syracuseStep 2003531 = 3005297) B3005297
theorem B2535725 : Blo 2003435 2535725 := bbase (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) (by norm_num)
theorem B6761933 : Blo 2003435 6761933 := bstep (se 3 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 6761933 = 2535725) B2535725
theorem B4507955 : Blo 2003435 4507955 := bstep (se 1 (by rfl) ⟨3380966, by rfl⟩ : syracuseStep 4507955 = 6761933) B6761933
theorem B3005303 : Blo 2003435 3005303 := bstep (se 1 (by rfl) ⟨2253977, by rfl⟩ : syracuseStep 3005303 = 4507955) B4507955
theorem B2003535 : Blo 2003435 2003535 := bstep (se 1 (by rfl) ⟨1502651, by rfl⟩ : syracuseStep 2003535 = 3005303) B3005303
theorem B3005309 : Blo 2003435 3005309 := bbase (se 3 (by rfl) ⟨563495, by rfl⟩ : syracuseStep 3005309 = 1126991) (by norm_num)
theorem B2003539 : Blo 2003435 2003539 := bstep (se 1 (by rfl) ⟨1502654, by rfl⟩ : syracuseStep 2003539 = 3005309) B3005309
theorem B4507973 : Blo 2003435 4507973 := bbase (se 4 (by rfl) ⟨422622, by rfl⟩ : syracuseStep 4507973 = 845245) (by norm_num)
theorem B3005315 : Blo 2003435 3005315 := bstep (se 1 (by rfl) ⟨2253986, by rfl⟩ : syracuseStep 3005315 = 4507973) B4507973
theorem B2003543 : Blo 2003435 2003543 := bstep (se 1 (by rfl) ⟨1502657, by rfl⟩ : syracuseStep 2003543 = 3005315) B3005315
theorem B9627893 : Blo 2003435 9627893 := bbase (se 5 (by rfl) ⟨451307, by rfl⟩ : syracuseStep 9627893 = 902615) (by norm_num)
theorem B6418595 : Blo 2003435 6418595 := bstep (se 1 (by rfl) ⟨4813946, by rfl⟩ : syracuseStep 6418595 = 9627893) B9627893
theorem B4279063 : Blo 2003435 4279063 := bstep (se 1 (by rfl) ⟨3209297, by rfl⟩ : syracuseStep 4279063 = 6418595) B6418595
theorem B5705417 : Blo 2003435 5705417 := bstep (se 2 (by rfl) ⟨2139531, by rfl⟩ : syracuseStep 5705417 = 4279063) B4279063
theorem B3803611 : Blo 2003435 3803611 := bstep (se 1 (by rfl) ⟨2852708, by rfl⟩ : syracuseStep 3803611 = 5705417) B5705417
theorem B5071481 : Blo 2003435 5071481 := bstep (se 2 (by rfl) ⟨1901805, by rfl⟩ : syracuseStep 5071481 = 3803611) B3803611
theorem B3380987 : Blo 2003435 3380987 := bstep (se 1 (by rfl) ⟨2535740, by rfl⟩ : syracuseStep 3380987 = 5071481) B5071481
theorem B2253991 : Blo 2003435 2253991 := bstep (se 1 (by rfl) ⟨1690493, by rfl⟩ : syracuseStep 2253991 = 3380987) B3380987
theorem B3005321 : Blo 2003435 3005321 := bstep (se 2 (by rfl) ⟨1126995, by rfl⟩ : syracuseStep 3005321 = 2253991) B2253991
theorem B2003547 : Blo 2003435 2003547 := bstep (se 1 (by rfl) ⟨1502660, by rfl⟩ : syracuseStep 2003547 = 3005321) B3005321
theorem B10142981 : Blo 2003435 10142981 := bbase (se 4 (by rfl) ⟨950904, by rfl⟩ : syracuseStep 10142981 = 1901809) (by norm_num)
theorem B6761987 : Blo 2003435 6761987 := bstep (se 1 (by rfl) ⟨5071490, by rfl⟩ : syracuseStep 6761987 = 10142981) B10142981
theorem B4507991 : Blo 2003435 4507991 := bstep (se 1 (by rfl) ⟨3380993, by rfl⟩ : syracuseStep 4507991 = 6761987) B6761987
theorem B3005327 : Blo 2003435 3005327 := bstep (se 1 (by rfl) ⟨2253995, by rfl⟩ : syracuseStep 3005327 = 4507991) B4507991
theorem B2003551 : Blo 2003435 2003551 := bstep (se 1 (by rfl) ⟨1502663, by rfl⟩ : syracuseStep 2003551 = 3005327) B3005327
theorem B3005333 : Blo 2003435 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B2003555 : Blo 2003435 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B11410901 : Blo 2003435 11410901 := bbase (se 7 (by rfl) ⟨133721, by rfl⟩ : syracuseStep 11410901 = 267443) (by norm_num)
theorem B7607267 : Blo 2003435 7607267 := bstep (se 1 (by rfl) ⟨5705450, by rfl⟩ : syracuseStep 7607267 = 11410901) B11410901
theorem B5071511 : Blo 2003435 5071511 := bstep (se 1 (by rfl) ⟨3803633, by rfl⟩ : syracuseStep 5071511 = 7607267) B7607267
theorem B3381007 : Blo 2003435 3381007 := bstep (se 1 (by rfl) ⟨2535755, by rfl⟩ : syracuseStep 3381007 = 5071511) B5071511
theorem B4508009 : Blo 2003435 4508009 := bstep (se 2 (by rfl) ⟨1690503, by rfl⟩ : syracuseStep 4508009 = 3381007) B3381007
theorem B3005339 : Blo 2003435 3005339 := bstep (se 1 (by rfl) ⟨2254004, by rfl⟩ : syracuseStep 3005339 = 4508009) B4508009
theorem B2003559 : Blo 2003435 2003559 := bstep (se 1 (by rfl) ⟨1502669, by rfl⟩ : syracuseStep 2003559 = 3005339) B3005339
theorem B2254009 : Blo 2003435 2254009 := bbase (se 2 (by rfl) ⟨845253, by rfl⟩ : syracuseStep 2254009 = 1690507) (by norm_num)
theorem B3005345 : Blo 2003435 3005345 := bstep (se 2 (by rfl) ⟨1127004, by rfl⟩ : syracuseStep 3005345 = 2254009) B2254009
theorem B2003563 : Blo 2003435 2003563 := bstep (se 1 (by rfl) ⟨1502672, by rfl⟩ : syracuseStep 2003563 = 3005345) B3005345
theorem B2406997 : Blo 2003435 2406997 := bbase (se 8 (by rfl) ⟨14103, by rfl⟩ : syracuseStep 2406997 = 28207) (by norm_num)
theorem B3209329 : Blo 2003435 3209329 := bstep (se 2 (by rfl) ⟨1203498, by rfl⟩ : syracuseStep 3209329 = 2406997) B2406997
theorem B4279105 : Blo 2003435 4279105 := bstep (se 2 (by rfl) ⟨1604664, by rfl⟩ : syracuseStep 4279105 = 3209329) B3209329
theorem B5705473 : Blo 2003435 5705473 := bstep (se 2 (by rfl) ⟨2139552, by rfl⟩ : syracuseStep 5705473 = 4279105) B4279105
theorem B7607297 : Blo 2003435 7607297 := bstep (se 2 (by rfl) ⟨2852736, by rfl⟩ : syracuseStep 7607297 = 5705473) B5705473
theorem B5071531 : Blo 2003435 5071531 := bstep (se 1 (by rfl) ⟨3803648, by rfl⟩ : syracuseStep 5071531 = 7607297) B7607297
theorem B6762041 : Blo 2003435 6762041 := bstep (se 2 (by rfl) ⟨2535765, by rfl⟩ : syracuseStep 6762041 = 5071531) B5071531
theorem B4508027 : Blo 2003435 4508027 := bstep (se 1 (by rfl) ⟨3381020, by rfl⟩ : syracuseStep 4508027 = 6762041) B6762041
theorem B3005351 : Blo 2003435 3005351 := bstep (se 1 (by rfl) ⟨2254013, by rfl⟩ : syracuseStep 3005351 = 4508027) B4508027
theorem B2003567 : Blo 2003435 2003567 := bstep (se 1 (by rfl) ⟨1502675, by rfl⟩ : syracuseStep 2003567 = 3005351) B3005351
theorem B3005357 : Blo 2003435 3005357 := bbase (se 3 (by rfl) ⟨563504, by rfl⟩ : syracuseStep 3005357 = 1127009) (by norm_num)
theorem B2003571 : Blo 2003435 2003571 := bstep (se 1 (by rfl) ⟨1502678, by rfl⟩ : syracuseStep 2003571 = 3005357) B3005357
theorem B4508045 : Blo 2003435 4508045 := bbase (se 3 (by rfl) ⟨845258, by rfl⟩ : syracuseStep 4508045 = 1690517) (by norm_num)
theorem B3005363 : Blo 2003435 3005363 := bstep (se 1 (by rfl) ⟨2254022, by rfl⟩ : syracuseStep 3005363 = 4508045) B4508045
theorem B2003575 : Blo 2003435 2003575 := bstep (se 1 (by rfl) ⟨1502681, by rfl⟩ : syracuseStep 2003575 = 3005363) B3005363
theorem B2535781 : Blo 2003435 2535781 := bbase (se 4 (by rfl) ⟨237729, by rfl⟩ : syracuseStep 2535781 = 475459) (by norm_num)
theorem B3381041 : Blo 2003435 3381041 := bstep (se 2 (by rfl) ⟨1267890, by rfl⟩ : syracuseStep 3381041 = 2535781) B2535781
theorem B2254027 : Blo 2003435 2254027 := bstep (se 1 (by rfl) ⟨1690520, by rfl⟩ : syracuseStep 2254027 = 3381041) B3381041
theorem B3005369 : Blo 2003435 3005369 := bstep (se 2 (by rfl) ⟨1127013, by rfl⟩ : syracuseStep 3005369 = 2254027) B2254027
theorem B2003579 : Blo 2003435 2003579 := bstep (se 1 (by rfl) ⟨1502684, by rfl⟩ : syracuseStep 2003579 = 3005369) B3005369
theorem B8675045 : Blo 2003435 8675045 := bbase (se 4 (by rfl) ⟨813285, by rfl⟩ : syracuseStep 8675045 = 1626571) (by norm_num)
theorem B5783363 : Blo 2003435 5783363 := bstep (se 1 (by rfl) ⟨4337522, by rfl⟩ : syracuseStep 5783363 = 8675045) B8675045
theorem B3855575 : Blo 2003435 3855575 := bstep (se 1 (by rfl) ⟨2891681, by rfl⟩ : syracuseStep 3855575 = 5783363) B5783363
theorem B2570383 : Blo 2003435 2570383 := bstep (se 1 (by rfl) ⟨1927787, by rfl⟩ : syracuseStep 2570383 = 3855575) B3855575
theorem B13708709 : Blo 2003435 13708709 := bstep (se 4 (by rfl) ⟨1285191, by rfl⟩ : syracuseStep 13708709 = 2570383) B2570383
theorem B9139139 : Blo 2003435 9139139 := bstep (se 1 (by rfl) ⟨6854354, by rfl⟩ : syracuseStep 9139139 = 13708709) B13708709
theorem B6092759 : Blo 2003435 6092759 := bstep (se 1 (by rfl) ⟨4569569, by rfl⟩ : syracuseStep 6092759 = 9139139) B9139139
theorem B16247357 : Blo 2003435 16247357 := bstep (se 3 (by rfl) ⟨3046379, by rfl⟩ : syracuseStep 16247357 = 6092759) B6092759
theorem B10831571 : Blo 2003435 10831571 := bstep (se 1 (by rfl) ⟨8123678, by rfl⟩ : syracuseStep 10831571 = 16247357) B16247357
theorem B7221047 : Blo 2003435 7221047 := bstep (se 1 (by rfl) ⟨5415785, by rfl⟩ : syracuseStep 7221047 = 10831571) B10831571
theorem B19256125 : Blo 2003435 19256125 := bstep (se 3 (by rfl) ⟨3610523, by rfl⟩ : syracuseStep 19256125 = 7221047) B7221047
theorem B25674833 : Blo 2003435 25674833 := bstep (se 2 (by rfl) ⟨9628062, by rfl⟩ : syracuseStep 25674833 = 19256125) B19256125
theorem B17116555 : Blo 2003435 17116555 := bstep (se 1 (by rfl) ⟨12837416, by rfl⟩ : syracuseStep 17116555 = 25674833) B25674833
theorem B22822073 : Blo 2003435 22822073 := bstep (se 2 (by rfl) ⟨8558277, by rfl⟩ : syracuseStep 22822073 = 17116555) B17116555
theorem B15214715 : Blo 2003435 15214715 := bstep (se 1 (by rfl) ⟨11411036, by rfl⟩ : syracuseStep 15214715 = 22822073) B22822073
theorem B10143143 : Blo 2003435 10143143 := bstep (se 1 (by rfl) ⟨7607357, by rfl⟩ : syracuseStep 10143143 = 15214715) B15214715
theorem B6762095 : Blo 2003435 6762095 := bstep (se 1 (by rfl) ⟨5071571, by rfl⟩ : syracuseStep 6762095 = 10143143) B10143143
theorem B4508063 : Blo 2003435 4508063 := bstep (se 1 (by rfl) ⟨3381047, by rfl⟩ : syracuseStep 4508063 = 6762095) B6762095
theorem B3005375 : Blo 2003435 3005375 := bstep (se 1 (by rfl) ⟨2254031, by rfl⟩ : syracuseStep 3005375 = 4508063) B4508063
theorem B2003583 : Blo 2003435 2003583 := bstep (se 1 (by rfl) ⟨1502687, by rfl⟩ : syracuseStep 2003583 = 3005375) B3005375
theorem B3005381 : Blo 2003435 3005381 := bbase (se 4 (by rfl) ⟨281754, by rfl⟩ : syracuseStep 3005381 = 563509) (by norm_num)
theorem B2003587 : Blo 2003435 2003587 := bstep (se 1 (by rfl) ⟨1502690, by rfl⟩ : syracuseStep 2003587 = 3005381) B3005381
theorem B3381061 : Blo 2003435 3381061 := bbase (se 4 (by rfl) ⟨316974, by rfl⟩ : syracuseStep 3381061 = 633949) (by norm_num)
theorem B4508081 : Blo 2003435 4508081 := bstep (se 2 (by rfl) ⟨1690530, by rfl⟩ : syracuseStep 4508081 = 3381061) B3381061
theorem B3005387 : Blo 2003435 3005387 := bstep (se 1 (by rfl) ⟨2254040, by rfl⟩ : syracuseStep 3005387 = 4508081) B4508081
theorem B2003591 : Blo 2003435 2003591 := bstep (se 1 (by rfl) ⟨1502693, by rfl⟩ : syracuseStep 2003591 = 3005387) B3005387
theorem B2254045 : Blo 2003435 2254045 := bbase (se 3 (by rfl) ⟨422633, by rfl⟩ : syracuseStep 2254045 = 845267) (by norm_num)
theorem B3005393 : Blo 2003435 3005393 := bstep (se 2 (by rfl) ⟨1127022, by rfl⟩ : syracuseStep 3005393 = 2254045) B2254045
theorem B2003595 : Blo 2003435 2003595 := bstep (se 1 (by rfl) ⟨1502696, by rfl⟩ : syracuseStep 2003595 = 3005393) B3005393
theorem B6762149 : Blo 2003435 6762149 := bbase (se 4 (by rfl) ⟨633951, by rfl⟩ : syracuseStep 6762149 = 1267903) (by norm_num)
theorem B4508099 : Blo 2003435 4508099 := bstep (se 1 (by rfl) ⟨3381074, by rfl⟩ : syracuseStep 4508099 = 6762149) B6762149
theorem B3005399 : Blo 2003435 3005399 := bstep (se 1 (by rfl) ⟨2254049, by rfl⟩ : syracuseStep 3005399 = 4508099) B4508099
theorem B2003599 : Blo 2003435 2003599 := bstep (se 1 (by rfl) ⟨1502699, by rfl⟩ : syracuseStep 2003599 = 3005399) B3005399
theorem B3005405 : Blo 2003435 3005405 := bbase (se 3 (by rfl) ⟨563513, by rfl⟩ : syracuseStep 3005405 = 1127027) (by norm_num)
theorem B2003603 : Blo 2003435 2003603 := bstep (se 1 (by rfl) ⟨1502702, by rfl⟩ : syracuseStep 2003603 = 3005405) B3005405
theorem B4508117 : Blo 2003435 4508117 := bbase (se 7 (by rfl) ⟨52829, by rfl⟩ : syracuseStep 4508117 = 105659) (by norm_num)
theorem B3005411 : Blo 2003435 3005411 := bstep (se 1 (by rfl) ⟨2254058, by rfl⟩ : syracuseStep 3005411 = 4508117) B4508117
theorem B2003607 : Blo 2003435 2003607 := bstep (se 1 (by rfl) ⟨1502705, by rfl⟩ : syracuseStep 2003607 = 3005411) B3005411
theorem B2284817 : Blo 2003435 2284817 := bbase (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) (by norm_num)
theorem B24371381 : Blo 2003435 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B64990349 : Blo 2003435 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B43326899 : Blo 2003435 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B28884599 : Blo 2003435 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B19256399 : Blo 2003435 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B12837599 : Blo 2003435 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B8558399 : Blo 2003435 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B5705599 : Blo 2003435 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B7607465 : Blo 2003435 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B5071643 : Blo 2003435 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B3381095 : Blo 2003435 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B2254063 : Blo 2003435 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B3005417 : Blo 2003435 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B2003611 : Blo 2003435 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B3855637 : Blo 2003435 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B5140849 : Blo 2003435 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B6854465 : Blo 2003435 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B4569643 : Blo 2003435 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B6092857 : Blo 2003435 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B8123809 : Blo 2003435 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B10831745 : Blo 2003435 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B7221163 : Blo 2003435 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B9628217 : Blo 2003435 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B6418811 : Blo 2003435 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B17116829 : Blo 2003435 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B11411219 : Blo 2003435 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B7607479 : Blo 2003435 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B10143305 : Blo 2003435 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B6762203 : Blo 2003435 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B4508135 : Blo 2003435 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B3005423 : Blo 2003435 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B2003615 : Blo 2003435 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B3005429 : Blo 2003435 3005429 := bbase (se 5 (by rfl) ⟨140879, by rfl⟩ : syracuseStep 3005429 = 281759) (by norm_num)
theorem B2003619 : Blo 2003435 2003619 := bstep (se 1 (by rfl) ⟨1502714, by rfl⟩ : syracuseStep 2003619 = 3005429) B3005429
theorem B3610597 : Blo 2003435 3610597 := bbase (se 4 (by rfl) ⟨338493, by rfl⟩ : syracuseStep 3610597 = 676987) (by norm_num)
theorem B4814129 : Blo 2003435 4814129 := bstep (se 2 (by rfl) ⟨1805298, by rfl⟩ : syracuseStep 4814129 = 3610597) B3610597
theorem B3209419 : Blo 2003435 3209419 := bstep (se 1 (by rfl) ⟨2407064, by rfl⟩ : syracuseStep 3209419 = 4814129) B4814129
theorem B4279225 : Blo 2003435 4279225 := bstep (se 2 (by rfl) ⟨1604709, by rfl⟩ : syracuseStep 4279225 = 3209419) B3209419
theorem B5705633 : Blo 2003435 5705633 := bstep (se 2 (by rfl) ⟨2139612, by rfl⟩ : syracuseStep 5705633 = 4279225) B4279225
theorem B3803755 : Blo 2003435 3803755 := bstep (se 1 (by rfl) ⟨2852816, by rfl⟩ : syracuseStep 3803755 = 5705633) B5705633
theorem B5071673 : Blo 2003435 5071673 := bstep (se 2 (by rfl) ⟨1901877, by rfl⟩ : syracuseStep 5071673 = 3803755) B3803755
theorem B3381115 : Blo 2003435 3381115 := bstep (se 1 (by rfl) ⟨2535836, by rfl⟩ : syracuseStep 3381115 = 5071673) B5071673
theorem B4508153 : Blo 2003435 4508153 := bstep (se 2 (by rfl) ⟨1690557, by rfl⟩ : syracuseStep 4508153 = 3381115) B3381115
theorem B3005435 : Blo 2003435 3005435 := bstep (se 1 (by rfl) ⟨2254076, by rfl⟩ : syracuseStep 3005435 = 4508153) B4508153
theorem B2003623 : Blo 2003435 2003623 := bstep (se 1 (by rfl) ⟨1502717, by rfl⟩ : syracuseStep 2003623 = 3005435) B3005435
theorem B2254081 : Blo 2003435 2254081 := bbase (se 2 (by rfl) ⟨845280, by rfl⟩ : syracuseStep 2254081 = 1690561) (by norm_num)
theorem B3005441 : Blo 2003435 3005441 := bstep (se 2 (by rfl) ⟨1127040, by rfl⟩ : syracuseStep 3005441 = 2254081) B2254081
theorem B2003627 : Blo 2003435 2003627 := bstep (se 1 (by rfl) ⟨1502720, by rfl⟩ : syracuseStep 2003627 = 3005441) B3005441
theorem B5071693 : Blo 2003435 5071693 := bbase (se 3 (by rfl) ⟨950942, by rfl⟩ : syracuseStep 5071693 = 1901885) (by norm_num)
theorem B6762257 : Blo 2003435 6762257 := bstep (se 2 (by rfl) ⟨2535846, by rfl⟩ : syracuseStep 6762257 = 5071693) B5071693
theorem B4508171 : Blo 2003435 4508171 := bstep (se 1 (by rfl) ⟨3381128, by rfl⟩ : syracuseStep 4508171 = 6762257) B6762257
theorem B3005447 : Blo 2003435 3005447 := bstep (se 1 (by rfl) ⟨2254085, by rfl⟩ : syracuseStep 3005447 = 4508171) B4508171
theorem B2003631 : Blo 2003435 2003631 := bstep (se 1 (by rfl) ⟨1502723, by rfl⟩ : syracuseStep 2003631 = 3005447) B3005447
theorem B3005453 : Blo 2003435 3005453 := bbase (se 3 (by rfl) ⟨563522, by rfl⟩ : syracuseStep 3005453 = 1127045) (by norm_num)
theorem B2003635 : Blo 2003435 2003635 := bstep (se 1 (by rfl) ⟨1502726, by rfl⟩ : syracuseStep 2003635 = 3005453) B3005453
theorem B4508189 : Blo 2003435 4508189 := bbase (se 3 (by rfl) ⟨845285, by rfl⟩ : syracuseStep 4508189 = 1690571) (by norm_num)
theorem B3005459 : Blo 2003435 3005459 := bstep (se 1 (by rfl) ⟨2254094, by rfl⟩ : syracuseStep 3005459 = 4508189) B4508189
theorem B2003639 : Blo 2003435 2003639 := bstep (se 1 (by rfl) ⟨1502729, by rfl⟩ : syracuseStep 2003639 = 3005459) B3005459
theorem B3381149 : Blo 2003435 3381149 := bbase (se 3 (by rfl) ⟨633965, by rfl⟩ : syracuseStep 3381149 = 1267931) (by norm_num)
theorem B2254099 : Blo 2003435 2254099 := bstep (se 1 (by rfl) ⟨1690574, by rfl⟩ : syracuseStep 2254099 = 3381149) B3381149
theorem B3005465 : Blo 2003435 3005465 := bstep (se 2 (by rfl) ⟨1127049, by rfl⟩ : syracuseStep 3005465 = 2254099) B2254099
theorem B2003643 : Blo 2003435 2003643 := bstep (se 1 (by rfl) ⟨1502732, by rfl⟩ : syracuseStep 2003643 = 3005465) B3005465
theorem B12185909 : Blo 2003435 12185909 := bbase (se 5 (by rfl) ⟨571214, by rfl⟩ : syracuseStep 12185909 = 1142429) (by norm_num)
theorem B8123939 : Blo 2003435 8123939 := bstep (se 1 (by rfl) ⟨6092954, by rfl⟩ : syracuseStep 8123939 = 12185909) B12185909
theorem B5415959 : Blo 2003435 5415959 := bstep (se 1 (by rfl) ⟨4061969, by rfl⟩ : syracuseStep 5415959 = 8123939) B8123939
theorem B3610639 : Blo 2003435 3610639 := bstep (se 1 (by rfl) ⟨2707979, by rfl⟩ : syracuseStep 3610639 = 5415959) B5415959
theorem B19256741 : Blo 2003435 19256741 := bstep (se 4 (by rfl) ⟨1805319, by rfl⟩ : syracuseStep 19256741 = 3610639) B3610639
theorem B12837827 : Blo 2003435 12837827 := bstep (se 1 (by rfl) ⟨9628370, by rfl⟩ : syracuseStep 12837827 = 19256741) B19256741
theorem B8558551 : Blo 2003435 8558551 := bstep (se 1 (by rfl) ⟨6418913, by rfl⟩ : syracuseStep 8558551 = 12837827) B12837827
theorem B11411401 : Blo 2003435 11411401 := bstep (se 2 (by rfl) ⟨4279275, by rfl⟩ : syracuseStep 11411401 = 8558551) B8558551
theorem B15215201 : Blo 2003435 15215201 := bstep (se 2 (by rfl) ⟨5705700, by rfl⟩ : syracuseStep 15215201 = 11411401) B11411401
theorem B10143467 : Blo 2003435 10143467 := bstep (se 1 (by rfl) ⟨7607600, by rfl⟩ : syracuseStep 10143467 = 15215201) B15215201
theorem B6762311 : Blo 2003435 6762311 := bstep (se 1 (by rfl) ⟨5071733, by rfl⟩ : syracuseStep 6762311 = 10143467) B10143467
theorem B4508207 : Blo 2003435 4508207 := bstep (se 1 (by rfl) ⟨3381155, by rfl⟩ : syracuseStep 4508207 = 6762311) B6762311
theorem B3005471 : Blo 2003435 3005471 := bstep (se 1 (by rfl) ⟨2254103, by rfl⟩ : syracuseStep 3005471 = 4508207) B4508207
theorem B2003647 : Blo 2003435 2003647 := bstep (se 1 (by rfl) ⟨1502735, by rfl⟩ : syracuseStep 2003647 = 3005471) B3005471
theorem B3005477 : Blo 2003435 3005477 := bbase (se 4 (by rfl) ⟨281763, by rfl⟩ : syracuseStep 3005477 = 563527) (by norm_num)
theorem B2003651 : Blo 2003435 2003651 := bstep (se 1 (by rfl) ⟨1502738, by rfl⟩ : syracuseStep 2003651 = 3005477) B3005477
theorem B2535877 : Blo 2003435 2535877 := bbase (se 4 (by rfl) ⟨237738, by rfl⟩ : syracuseStep 2535877 = 475477) (by norm_num)
theorem B3381169 : Blo 2003435 3381169 := bstep (se 2 (by rfl) ⟨1267938, by rfl⟩ : syracuseStep 3381169 = 2535877) B2535877
theorem B4508225 : Blo 2003435 4508225 := bstep (se 2 (by rfl) ⟨1690584, by rfl⟩ : syracuseStep 4508225 = 3381169) B3381169
theorem B3005483 : Blo 2003435 3005483 := bstep (se 1 (by rfl) ⟨2254112, by rfl⟩ : syracuseStep 3005483 = 4508225) B4508225
theorem B2003655 : Blo 2003435 2003655 := bstep (se 1 (by rfl) ⟨1502741, by rfl⟩ : syracuseStep 2003655 = 3005483) B3005483
theorem B2254117 : Blo 2003435 2254117 := bbase (se 4 (by rfl) ⟨211323, by rfl⟩ : syracuseStep 2254117 = 422647) (by norm_num)
theorem B3005489 : Blo 2003435 3005489 := bstep (se 2 (by rfl) ⟨1127058, by rfl⟩ : syracuseStep 3005489 = 2254117) B2254117
theorem B2003659 : Blo 2003435 2003659 := bstep (se 1 (by rfl) ⟨1502744, by rfl⟩ : syracuseStep 2003659 = 3005489) B3005489
theorem B3610669 : Blo 2003435 3610669 := bbase (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) (by norm_num)
theorem B4814225 : Blo 2003435 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B3209483 : Blo 2003435 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B8558621 : Blo 2003435 8558621 := bstep (se 3 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 8558621 = 3209483) B3209483
theorem B5705747 : Blo 2003435 5705747 := bstep (se 1 (by rfl) ⟨4279310, by rfl⟩ : syracuseStep 5705747 = 8558621) B8558621
theorem B3803831 : Blo 2003435 3803831 := bstep (se 1 (by rfl) ⟨2852873, by rfl⟩ : syracuseStep 3803831 = 5705747) B5705747
theorem B2535887 : Blo 2003435 2535887 := bstep (se 1 (by rfl) ⟨1901915, by rfl⟩ : syracuseStep 2535887 = 3803831) B3803831
theorem B6762365 : Blo 2003435 6762365 := bstep (se 3 (by rfl) ⟨1267943, by rfl⟩ : syracuseStep 6762365 = 2535887) B2535887
theorem B4508243 : Blo 2003435 4508243 := bstep (se 1 (by rfl) ⟨3381182, by rfl⟩ : syracuseStep 4508243 = 6762365) B6762365
theorem B3005495 : Blo 2003435 3005495 := bstep (se 1 (by rfl) ⟨2254121, by rfl⟩ : syracuseStep 3005495 = 4508243) B4508243
theorem B2003663 : Blo 2003435 2003663 := bstep (se 1 (by rfl) ⟨1502747, by rfl⟩ : syracuseStep 2003663 = 3005495) B3005495
theorem B3005501 : Blo 2003435 3005501 := bbase (se 3 (by rfl) ⟨563531, by rfl⟩ : syracuseStep 3005501 = 1127063) (by norm_num)
theorem B2003667 : Blo 2003435 2003667 := bstep (se 1 (by rfl) ⟨1502750, by rfl⟩ : syracuseStep 2003667 = 3005501) B3005501
theorem B4508261 : Blo 2003435 4508261 := bbase (se 4 (by rfl) ⟨422649, by rfl⟩ : syracuseStep 4508261 = 845299) (by norm_num)
theorem B3005507 : Blo 2003435 3005507 := bstep (se 1 (by rfl) ⟨2254130, by rfl⟩ : syracuseStep 3005507 = 4508261) B4508261
theorem B2003671 : Blo 2003435 2003671 := bstep (se 1 (by rfl) ⟨1502753, by rfl⟩ : syracuseStep 2003671 = 3005507) B3005507
theorem B5071805 : Blo 2003435 5071805 := bbase (se 3 (by rfl) ⟨950963, by rfl⟩ : syracuseStep 5071805 = 1901927) (by norm_num)
theorem B3381203 : Blo 2003435 3381203 := bstep (se 1 (by rfl) ⟨2535902, by rfl⟩ : syracuseStep 3381203 = 5071805) B5071805
theorem B2254135 : Blo 2003435 2254135 := bstep (se 1 (by rfl) ⟨1690601, by rfl⟩ : syracuseStep 2254135 = 3381203) B3381203
theorem B3005513 : Blo 2003435 3005513 := bstep (se 2 (by rfl) ⟨1127067, by rfl⟩ : syracuseStep 3005513 = 2254135) B2254135
theorem B2003675 : Blo 2003435 2003675 := bstep (se 1 (by rfl) ⟨1502756, by rfl⟩ : syracuseStep 2003675 = 3005513) B3005513
theorem B3803861 : Blo 2003435 3803861 := bbase (se 7 (by rfl) ⟨44576, by rfl⟩ : syracuseStep 3803861 = 89153) (by norm_num)
theorem B10143629 : Blo 2003435 10143629 := bstep (se 3 (by rfl) ⟨1901930, by rfl⟩ : syracuseStep 10143629 = 3803861) B3803861
theorem B6762419 : Blo 2003435 6762419 := bstep (se 1 (by rfl) ⟨5071814, by rfl⟩ : syracuseStep 6762419 = 10143629) B10143629
theorem B4508279 : Blo 2003435 4508279 := bstep (se 1 (by rfl) ⟨3381209, by rfl⟩ : syracuseStep 4508279 = 6762419) B6762419
theorem B3005519 : Blo 2003435 3005519 := bstep (se 1 (by rfl) ⟨2254139, by rfl⟩ : syracuseStep 3005519 = 4508279) B4508279
theorem B2003679 : Blo 2003435 2003679 := bstep (se 1 (by rfl) ⟨1502759, by rfl⟩ : syracuseStep 2003679 = 3005519) B3005519
theorem B3005525 : Blo 2003435 3005525 := bbase (se 8 (by rfl) ⟨17610, by rfl⟩ : syracuseStep 3005525 = 35221) (by norm_num)
theorem B2003683 : Blo 2003435 2003683 := bstep (se 1 (by rfl) ⟨1502762, by rfl⟩ : syracuseStep 2003683 = 3005525) B3005525
theorem B2407141 : Blo 2003435 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B12838085 : Blo 2003435 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B8558723 : Blo 2003435 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B5705815 : Blo 2003435 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B7607753 : Blo 2003435 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B5071835 : Blo 2003435 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B3381223 : Blo 2003435 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B4508297 : Blo 2003435 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B3005531 : Blo 2003435 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B2003687 : Blo 2003435 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B2254153 : Blo 2003435 2254153 := bbase (se 2 (by rfl) ⟨845307, by rfl⟩ : syracuseStep 2254153 = 1690615) (by norm_num)
theorem B3005537 : Blo 2003435 3005537 := bstep (se 2 (by rfl) ⟨1127076, by rfl⟩ : syracuseStep 3005537 = 2254153) B2254153
theorem B2003691 : Blo 2003435 2003691 := bstep (se 1 (by rfl) ⟨1502768, by rfl⟩ : syracuseStep 2003691 = 3005537) B3005537
theorem B8124133 : Blo 2003435 8124133 := bbase (se 4 (by rfl) ⟨761637, by rfl⟩ : syracuseStep 8124133 = 1523275) (by norm_num)
theorem B10832177 : Blo 2003435 10832177 := bstep (se 2 (by rfl) ⟨4062066, by rfl⟩ : syracuseStep 10832177 = 8124133) B8124133
theorem B28885805 : Blo 2003435 28885805 := bstep (se 3 (by rfl) ⟨5416088, by rfl⟩ : syracuseStep 28885805 = 10832177) B10832177
theorem B19257203 : Blo 2003435 19257203 := bstep (se 1 (by rfl) ⟨14442902, by rfl⟩ : syracuseStep 19257203 = 28885805) B28885805
theorem B12838135 : Blo 2003435 12838135 := bstep (se 1 (by rfl) ⟨9628601, by rfl⟩ : syracuseStep 12838135 = 19257203) B19257203
theorem B17117513 : Blo 2003435 17117513 := bstep (se 2 (by rfl) ⟨6419067, by rfl⟩ : syracuseStep 17117513 = 12838135) B12838135
theorem B11411675 : Blo 2003435 11411675 := bstep (se 1 (by rfl) ⟨8558756, by rfl⟩ : syracuseStep 11411675 = 17117513) B17117513
theorem B7607783 : Blo 2003435 7607783 := bstep (se 1 (by rfl) ⟨5705837, by rfl⟩ : syracuseStep 7607783 = 11411675) B11411675
theorem B5071855 : Blo 2003435 5071855 := bstep (se 1 (by rfl) ⟨3803891, by rfl⟩ : syracuseStep 5071855 = 7607783) B7607783
theorem B6762473 : Blo 2003435 6762473 := bstep (se 2 (by rfl) ⟨2535927, by rfl⟩ : syracuseStep 6762473 = 5071855) B5071855
theorem B4508315 : Blo 2003435 4508315 := bstep (se 1 (by rfl) ⟨3381236, by rfl⟩ : syracuseStep 4508315 = 6762473) B6762473
theorem B3005543 : Blo 2003435 3005543 := bstep (se 1 (by rfl) ⟨2254157, by rfl⟩ : syracuseStep 3005543 = 4508315) B4508315
theorem B2003695 : Blo 2003435 2003695 := bstep (se 1 (by rfl) ⟨1502771, by rfl⟩ : syracuseStep 2003695 = 3005543) B3005543
theorem B3005549 : Blo 2003435 3005549 := bbase (se 3 (by rfl) ⟨563540, by rfl⟩ : syracuseStep 3005549 = 1127081) (by norm_num)
theorem B2003699 : Blo 2003435 2003699 := bstep (se 1 (by rfl) ⟨1502774, by rfl⟩ : syracuseStep 2003699 = 3005549) B3005549
theorem B4508333 : Blo 2003435 4508333 := bbase (se 3 (by rfl) ⟨845312, by rfl⟩ : syracuseStep 4508333 = 1690625) (by norm_num)
theorem B3005555 : Blo 2003435 3005555 := bstep (se 1 (by rfl) ⟨2254166, by rfl⟩ : syracuseStep 3005555 = 4508333) B4508333
theorem B2003703 : Blo 2003435 2003703 := bstep (se 1 (by rfl) ⟨1502777, by rfl⟩ : syracuseStep 2003703 = 3005555) B3005555
theorem B4279405 : Blo 2003435 4279405 := bbase (se 3 (by rfl) ⟨802388, by rfl⟩ : syracuseStep 4279405 = 1604777) (by norm_num)
theorem B5705873 : Blo 2003435 5705873 := bstep (se 2 (by rfl) ⟨2139702, by rfl⟩ : syracuseStep 5705873 = 4279405) B4279405
theorem B3803915 : Blo 2003435 3803915 := bstep (se 1 (by rfl) ⟨2852936, by rfl⟩ : syracuseStep 3803915 = 5705873) B5705873
theorem B2535943 : Blo 2003435 2535943 := bstep (se 1 (by rfl) ⟨1901957, by rfl⟩ : syracuseStep 2535943 = 3803915) B3803915
theorem B3381257 : Blo 2003435 3381257 := bstep (se 2 (by rfl) ⟨1267971, by rfl⟩ : syracuseStep 3381257 = 2535943) B2535943
theorem B2254171 : Blo 2003435 2254171 := bstep (se 1 (by rfl) ⟨1690628, by rfl⟩ : syracuseStep 2254171 = 3381257) B3381257
theorem B3005561 : Blo 2003435 3005561 := bstep (se 2 (by rfl) ⟨1127085, by rfl⟩ : syracuseStep 3005561 = 2254171) B2254171
theorem B2003707 : Blo 2003435 2003707 := bstep (se 1 (by rfl) ⟨1502780, by rfl⟩ : syracuseStep 2003707 = 3005561) B3005561
theorem B8124197 : Blo 2003435 8124197 := bbase (se 4 (by rfl) ⟨761643, by rfl⟩ : syracuseStep 8124197 = 1523287) (by norm_num)
theorem B21664525 : Blo 2003435 21664525 := bstep (se 3 (by rfl) ⟨4062098, by rfl⟩ : syracuseStep 21664525 = 8124197) B8124197
theorem B28886033 : Blo 2003435 28886033 := bstep (se 2 (by rfl) ⟨10832262, by rfl⟩ : syracuseStep 28886033 = 21664525) B21664525
theorem B19257355 : Blo 2003435 19257355 := bstep (se 1 (by rfl) ⟨14443016, by rfl⟩ : syracuseStep 19257355 = 28886033) B28886033
theorem B25676473 : Blo 2003435 25676473 := bstep (se 2 (by rfl) ⟨9628677, by rfl⟩ : syracuseStep 25676473 = 19257355) B19257355
theorem B34235297 : Blo 2003435 34235297 := bstep (se 2 (by rfl) ⟨12838236, by rfl⟩ : syracuseStep 34235297 = 25676473) B25676473
theorem B22823531 : Blo 2003435 22823531 := bstep (se 1 (by rfl) ⟨17117648, by rfl⟩ : syracuseStep 22823531 = 34235297) B34235297
theorem B15215687 : Blo 2003435 15215687 := bstep (se 1 (by rfl) ⟨11411765, by rfl⟩ : syracuseStep 15215687 = 22823531) B22823531
theorem B10143791 : Blo 2003435 10143791 := bstep (se 1 (by rfl) ⟨7607843, by rfl⟩ : syracuseStep 10143791 = 15215687) B15215687
theorem B6762527 : Blo 2003435 6762527 := bstep (se 1 (by rfl) ⟨5071895, by rfl⟩ : syracuseStep 6762527 = 10143791) B10143791
theorem B4508351 : Blo 2003435 4508351 := bstep (se 1 (by rfl) ⟨3381263, by rfl⟩ : syracuseStep 4508351 = 6762527) B6762527
theorem B3005567 : Blo 2003435 3005567 := bstep (se 1 (by rfl) ⟨2254175, by rfl⟩ : syracuseStep 3005567 = 4508351) B4508351
theorem B2003711 : Blo 2003435 2003711 := bstep (se 1 (by rfl) ⟨1502783, by rfl⟩ : syracuseStep 2003711 = 3005567) B3005567
theorem B3005573 : Blo 2003435 3005573 := bbase (se 4 (by rfl) ⟨281772, by rfl⟩ : syracuseStep 3005573 = 563545) (by norm_num)
theorem B2003715 : Blo 2003435 2003715 := bstep (se 1 (by rfl) ⟨1502786, by rfl⟩ : syracuseStep 2003715 = 3005573) B3005573
theorem B3381277 : Blo 2003435 3381277 := bbase (se 3 (by rfl) ⟨633989, by rfl⟩ : syracuseStep 3381277 = 1267979) (by norm_num)
theorem B4508369 : Blo 2003435 4508369 := bstep (se 2 (by rfl) ⟨1690638, by rfl⟩ : syracuseStep 4508369 = 3381277) B3381277
theorem B3005579 : Blo 2003435 3005579 := bstep (se 1 (by rfl) ⟨2254184, by rfl⟩ : syracuseStep 3005579 = 4508369) B4508369
theorem B2003719 : Blo 2003435 2003719 := bstep (se 1 (by rfl) ⟨1502789, by rfl⟩ : syracuseStep 2003719 = 3005579) B3005579
theorem B2254189 : Blo 2003435 2254189 := bbase (se 3 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 2254189 = 845321) (by norm_num)
theorem B3005585 : Blo 2003435 3005585 := bstep (se 2 (by rfl) ⟨1127094, by rfl⟩ : syracuseStep 3005585 = 2254189) B2254189
theorem B2003723 : Blo 2003435 2003723 := bstep (se 1 (by rfl) ⟨1502792, by rfl⟩ : syracuseStep 2003723 = 3005585) B3005585
theorem B6762581 : Blo 2003435 6762581 := bbase (se 8 (by rfl) ⟨39624, by rfl⟩ : syracuseStep 6762581 = 79249) (by norm_num)
theorem B4508387 : Blo 2003435 4508387 := bstep (se 1 (by rfl) ⟨3381290, by rfl⟩ : syracuseStep 4508387 = 6762581) B6762581
theorem B3005591 : Blo 2003435 3005591 := bstep (se 1 (by rfl) ⟨2254193, by rfl⟩ : syracuseStep 3005591 = 4508387) B4508387
theorem B2003727 : Blo 2003435 2003727 := bstep (se 1 (by rfl) ⟨1502795, by rfl⟩ : syracuseStep 2003727 = 3005591) B3005591
theorem B3005597 : Blo 2003435 3005597 := bbase (se 3 (by rfl) ⟨563549, by rfl⟩ : syracuseStep 3005597 = 1127099) (by norm_num)
theorem B2003731 : Blo 2003435 2003731 := bstep (se 1 (by rfl) ⟨1502798, by rfl⟩ : syracuseStep 2003731 = 3005597) B3005597
theorem B4508405 : Blo 2003435 4508405 := bbase (se 5 (by rfl) ⟨211331, by rfl⟩ : syracuseStep 4508405 = 422663) (by norm_num)
theorem B3005603 : Blo 2003435 3005603 := bstep (se 1 (by rfl) ⟨2254202, by rfl⟩ : syracuseStep 3005603 = 4508405) B4508405
theorem B2003735 : Blo 2003435 2003735 := bstep (se 1 (by rfl) ⟨1502801, by rfl⟩ : syracuseStep 2003735 = 3005603) B3005603
theorem B3427445 : Blo 2003435 3427445 := bbase (se 5 (by rfl) ⟨160661, by rfl⟩ : syracuseStep 3427445 = 321323) (by norm_num)
theorem B9139853 : Blo 2003435 9139853 := bstep (se 3 (by rfl) ⟨1713722, by rfl⟩ : syracuseStep 9139853 = 3427445) B3427445
theorem B6093235 : Blo 2003435 6093235 := bstep (se 1 (by rfl) ⟨4569926, by rfl⟩ : syracuseStep 6093235 = 9139853) B9139853
theorem B8124313 : Blo 2003435 8124313 := bstep (se 2 (by rfl) ⟨3046617, by rfl⟩ : syracuseStep 8124313 = 6093235) B6093235
theorem B10832417 : Blo 2003435 10832417 := bstep (se 2 (by rfl) ⟨4062156, by rfl⟩ : syracuseStep 10832417 = 8124313) B8124313
theorem B7221611 : Blo 2003435 7221611 := bstep (se 1 (by rfl) ⟨5416208, by rfl⟩ : syracuseStep 7221611 = 10832417) B10832417
theorem B4814407 : Blo 2003435 4814407 := bstep (se 1 (by rfl) ⟨3610805, by rfl⟩ : syracuseStep 4814407 = 7221611) B7221611
theorem B25676837 : Blo 2003435 25676837 := bstep (se 4 (by rfl) ⟨2407203, by rfl⟩ : syracuseStep 25676837 = 4814407) B4814407
theorem B17117891 : Blo 2003435 17117891 := bstep (se 1 (by rfl) ⟨12838418, by rfl⟩ : syracuseStep 17117891 = 25676837) B25676837
theorem B11411927 : Blo 2003435 11411927 := bstep (se 1 (by rfl) ⟨8558945, by rfl⟩ : syracuseStep 11411927 = 17117891) B17117891
theorem B7607951 : Blo 2003435 7607951 := bstep (se 1 (by rfl) ⟨5705963, by rfl⟩ : syracuseStep 7607951 = 11411927) B11411927
theorem B5071967 : Blo 2003435 5071967 := bstep (se 1 (by rfl) ⟨3803975, by rfl⟩ : syracuseStep 5071967 = 7607951) B7607951
theorem B3381311 : Blo 2003435 3381311 := bstep (se 1 (by rfl) ⟨2535983, by rfl⟩ : syracuseStep 3381311 = 5071967) B5071967
theorem B2254207 : Blo 2003435 2254207 := bstep (se 1 (by rfl) ⟨1690655, by rfl⟩ : syracuseStep 2254207 = 3381311) B3381311
theorem B3005609 : Blo 2003435 3005609 := bstep (se 2 (by rfl) ⟨1127103, by rfl⟩ : syracuseStep 3005609 = 2254207) B2254207
theorem B2003739 : Blo 2003435 2003739 := bstep (se 1 (by rfl) ⟨1502804, by rfl⟩ : syracuseStep 2003739 = 3005609) B3005609
theorem B3610813 : Blo 2003435 3610813 := bbase (se 3 (by rfl) ⟨677027, by rfl⟩ : syracuseStep 3610813 = 1354055) (by norm_num)
theorem B4814417 : Blo 2003435 4814417 := bstep (se 2 (by rfl) ⟨1805406, by rfl⟩ : syracuseStep 4814417 = 3610813) B3610813
theorem B3209611 : Blo 2003435 3209611 := bstep (se 1 (by rfl) ⟨2407208, by rfl⟩ : syracuseStep 3209611 = 4814417) B4814417
theorem B4279481 : Blo 2003435 4279481 := bstep (se 2 (by rfl) ⟨1604805, by rfl⟩ : syracuseStep 4279481 = 3209611) B3209611
theorem B2852987 : Blo 2003435 2852987 := bstep (se 1 (by rfl) ⟨2139740, by rfl⟩ : syracuseStep 2852987 = 4279481) B4279481
theorem B7607965 : Blo 2003435 7607965 := bstep (se 3 (by rfl) ⟨1426493, by rfl⟩ : syracuseStep 7607965 = 2852987) B2852987
theorem B10143953 : Blo 2003435 10143953 := bstep (se 2 (by rfl) ⟨3803982, by rfl⟩ : syracuseStep 10143953 = 7607965) B7607965
theorem B6762635 : Blo 2003435 6762635 := bstep (se 1 (by rfl) ⟨5071976, by rfl⟩ : syracuseStep 6762635 = 10143953) B10143953
theorem B4508423 : Blo 2003435 4508423 := bstep (se 1 (by rfl) ⟨3381317, by rfl⟩ : syracuseStep 4508423 = 6762635) B6762635
theorem B3005615 : Blo 2003435 3005615 := bstep (se 1 (by rfl) ⟨2254211, by rfl⟩ : syracuseStep 3005615 = 4508423) B4508423
theorem B2003743 : Blo 2003435 2003743 := bstep (se 1 (by rfl) ⟨1502807, by rfl⟩ : syracuseStep 2003743 = 3005615) B3005615
theorem B3005621 : Blo 2003435 3005621 := bbase (se 5 (by rfl) ⟨140888, by rfl⟩ : syracuseStep 3005621 = 281777) (by norm_num)
theorem B2003747 : Blo 2003435 2003747 := bstep (se 1 (by rfl) ⟨1502810, by rfl⟩ : syracuseStep 2003747 = 3005621) B3005621
theorem B5071997 : Blo 2003435 5071997 := bbase (se 3 (by rfl) ⟨950999, by rfl⟩ : syracuseStep 5071997 = 1901999) (by norm_num)
theorem B3381331 : Blo 2003435 3381331 := bstep (se 1 (by rfl) ⟨2535998, by rfl⟩ : syracuseStep 3381331 = 5071997) B5071997
theorem B4508441 : Blo 2003435 4508441 := bstep (se 2 (by rfl) ⟨1690665, by rfl⟩ : syracuseStep 4508441 = 3381331) B3381331
theorem B3005627 : Blo 2003435 3005627 := bstep (se 1 (by rfl) ⟨2254220, by rfl⟩ : syracuseStep 3005627 = 4508441) B4508441
theorem B2003751 : Blo 2003435 2003751 := bstep (se 1 (by rfl) ⟨1502813, by rfl⟩ : syracuseStep 2003751 = 3005627) B3005627
theorem B2254225 : Blo 2003435 2254225 := bbase (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) (by norm_num)
theorem B3005633 : Blo 2003435 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B2003755 : Blo 2003435 2003755 := bstep (se 1 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 2003755 = 3005633) B3005633
theorem B3804013 : Blo 2003435 3804013 := bbase (se 3 (by rfl) ⟨713252, by rfl⟩ : syracuseStep 3804013 = 1426505) (by norm_num)
theorem B5072017 : Blo 2003435 5072017 := bstep (se 2 (by rfl) ⟨1902006, by rfl⟩ : syracuseStep 5072017 = 3804013) B3804013
theorem B6762689 : Blo 2003435 6762689 := bstep (se 2 (by rfl) ⟨2536008, by rfl⟩ : syracuseStep 6762689 = 5072017) B5072017
theorem B4508459 : Blo 2003435 4508459 := bstep (se 1 (by rfl) ⟨3381344, by rfl⟩ : syracuseStep 4508459 = 6762689) B6762689
theorem B3005639 : Blo 2003435 3005639 := bstep (se 1 (by rfl) ⟨2254229, by rfl⟩ : syracuseStep 3005639 = 4508459) B4508459
theorem B2003759 : Blo 2003435 2003759 := bstep (se 1 (by rfl) ⟨1502819, by rfl⟩ : syracuseStep 2003759 = 3005639) B3005639
theorem B3005645 : Blo 2003435 3005645 := bbase (se 3 (by rfl) ⟨563558, by rfl⟩ : syracuseStep 3005645 = 1127117) (by norm_num)
theorem B2003763 : Blo 2003435 2003763 := bstep (se 1 (by rfl) ⟨1502822, by rfl⟩ : syracuseStep 2003763 = 3005645) B3005645
theorem B4508477 : Blo 2003435 4508477 := bbase (se 3 (by rfl) ⟨845339, by rfl⟩ : syracuseStep 4508477 = 1690679) (by norm_num)
theorem B3005651 : Blo 2003435 3005651 := bstep (se 1 (by rfl) ⟨2254238, by rfl⟩ : syracuseStep 3005651 = 4508477) B4508477
theorem B2003767 : Blo 2003435 2003767 := bstep (se 1 (by rfl) ⟨1502825, by rfl⟩ : syracuseStep 2003767 = 3005651) B3005651
theorem B3381365 : Blo 2003435 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B2254243 : Blo 2003435 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B3005657 : Blo 2003435 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B2003771 : Blo 2003435 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B4279549 : Blo 2003435 4279549 := bbase (se 3 (by rfl) ⟨802415, by rfl⟩ : syracuseStep 4279549 = 1604831) (by norm_num)
theorem B5706065 : Blo 2003435 5706065 := bstep (se 2 (by rfl) ⟨2139774, by rfl⟩ : syracuseStep 5706065 = 4279549) B4279549
theorem B15216173 : Blo 2003435 15216173 := bstep (se 3 (by rfl) ⟨2853032, by rfl⟩ : syracuseStep 15216173 = 5706065) B5706065
theorem B10144115 : Blo 2003435 10144115 := bstep (se 1 (by rfl) ⟨7608086, by rfl⟩ : syracuseStep 10144115 = 15216173) B15216173
theorem B6762743 : Blo 2003435 6762743 := bstep (se 1 (by rfl) ⟨5072057, by rfl⟩ : syracuseStep 6762743 = 10144115) B10144115
theorem B4508495 : Blo 2003435 4508495 := bstep (se 1 (by rfl) ⟨3381371, by rfl⟩ : syracuseStep 4508495 = 6762743) B6762743
theorem B3005663 : Blo 2003435 3005663 := bstep (se 1 (by rfl) ⟨2254247, by rfl⟩ : syracuseStep 3005663 = 4508495) B4508495
theorem B2003775 : Blo 2003435 2003775 := bstep (se 1 (by rfl) ⟨1502831, by rfl⟩ : syracuseStep 2003775 = 3005663) B3005663
theorem B3005669 : Blo 2003435 3005669 := bbase (se 4 (by rfl) ⟨281781, by rfl⟩ : syracuseStep 3005669 = 563563) (by norm_num)
theorem B2003779 : Blo 2003435 2003779 := bstep (se 1 (by rfl) ⟨1502834, by rfl⟩ : syracuseStep 2003779 = 3005669) B3005669
theorem B14443541 : Blo 2003435 14443541 := bbase (se 6 (by rfl) ⟨338520, by rfl⟩ : syracuseStep 14443541 = 677041) (by norm_num)
theorem B9629027 : Blo 2003435 9629027 := bstep (se 1 (by rfl) ⟨7221770, by rfl⟩ : syracuseStep 9629027 = 14443541) B14443541
theorem B6419351 : Blo 2003435 6419351 := bstep (se 1 (by rfl) ⟨4814513, by rfl⟩ : syracuseStep 6419351 = 9629027) B9629027
theorem B4279567 : Blo 2003435 4279567 := bstep (se 1 (by rfl) ⟨3209675, by rfl⟩ : syracuseStep 4279567 = 6419351) B6419351
theorem B5706089 : Blo 2003435 5706089 := bstep (se 2 (by rfl) ⟨2139783, by rfl⟩ : syracuseStep 5706089 = 4279567) B4279567
theorem B3804059 : Blo 2003435 3804059 := bstep (se 1 (by rfl) ⟨2853044, by rfl⟩ : syracuseStep 3804059 = 5706089) B5706089
theorem B2536039 : Blo 2003435 2536039 := bstep (se 1 (by rfl) ⟨1902029, by rfl⟩ : syracuseStep 2536039 = 3804059) B3804059
theorem B3381385 : Blo 2003435 3381385 := bstep (se 2 (by rfl) ⟨1268019, by rfl⟩ : syracuseStep 3381385 = 2536039) B2536039
theorem B4508513 : Blo 2003435 4508513 := bstep (se 2 (by rfl) ⟨1690692, by rfl⟩ : syracuseStep 4508513 = 3381385) B3381385
theorem B3005675 : Blo 2003435 3005675 := bstep (se 1 (by rfl) ⟨2254256, by rfl⟩ : syracuseStep 3005675 = 4508513) B4508513
theorem B2003783 : Blo 2003435 2003783 := bstep (se 1 (by rfl) ⟨1502837, by rfl⟩ : syracuseStep 2003783 = 3005675) B3005675
theorem B2254261 : Blo 2003435 2254261 := bbase (se 5 (by rfl) ⟨105668, by rfl⟩ : syracuseStep 2254261 = 211337) (by norm_num)
theorem B3005681 : Blo 2003435 3005681 := bstep (se 2 (by rfl) ⟨1127130, by rfl⟩ : syracuseStep 3005681 = 2254261) B2254261
theorem B2003787 : Blo 2003435 2003787 := bstep (se 1 (by rfl) ⟨1502840, by rfl⟩ : syracuseStep 2003787 = 3005681) B3005681
theorem B2536049 : Blo 2003435 2536049 := bbase (se 2 (by rfl) ⟨951018, by rfl⟩ : syracuseStep 2536049 = 1902037) (by norm_num)
theorem B6762797 : Blo 2003435 6762797 := bstep (se 3 (by rfl) ⟨1268024, by rfl⟩ : syracuseStep 6762797 = 2536049) B2536049
theorem B4508531 : Blo 2003435 4508531 := bstep (se 1 (by rfl) ⟨3381398, by rfl⟩ : syracuseStep 4508531 = 6762797) B6762797
theorem B3005687 : Blo 2003435 3005687 := bstep (se 1 (by rfl) ⟨2254265, by rfl⟩ : syracuseStep 3005687 = 4508531) B4508531
theorem B2003791 : Blo 2003435 2003791 := bstep (se 1 (by rfl) ⟨1502843, by rfl⟩ : syracuseStep 2003791 = 3005687) B3005687
theorem B3005693 : Blo 2003435 3005693 := bbase (se 3 (by rfl) ⟨563567, by rfl⟩ : syracuseStep 3005693 = 1127135) (by norm_num)
theorem B2003795 : Blo 2003435 2003795 := bstep (se 1 (by rfl) ⟨1502846, by rfl⟩ : syracuseStep 2003795 = 3005693) B3005693
theorem B4508549 : Blo 2003435 4508549 := bbase (se 4 (by rfl) ⟨422676, by rfl⟩ : syracuseStep 4508549 = 845353) (by norm_num)
theorem B3005699 : Blo 2003435 3005699 := bstep (se 1 (by rfl) ⟨2254274, by rfl⟩ : syracuseStep 3005699 = 4508549) B4508549
theorem B2003799 : Blo 2003435 2003799 := bstep (se 1 (by rfl) ⟨1502849, by rfl⟩ : syracuseStep 2003799 = 3005699) B3005699
theorem B2139805 : Blo 2003435 2139805 := bbase (se 3 (by rfl) ⟨401213, by rfl⟩ : syracuseStep 2139805 = 802427) (by norm_num)
theorem B2853073 : Blo 2003435 2853073 := bstep (se 2 (by rfl) ⟨1069902, by rfl⟩ : syracuseStep 2853073 = 2139805) B2139805
theorem B3804097 : Blo 2003435 3804097 := bstep (se 2 (by rfl) ⟨1426536, by rfl⟩ : syracuseStep 3804097 = 2853073) B2853073
theorem B5072129 : Blo 2003435 5072129 := bstep (se 2 (by rfl) ⟨1902048, by rfl⟩ : syracuseStep 5072129 = 3804097) B3804097
theorem B3381419 : Blo 2003435 3381419 := bstep (se 1 (by rfl) ⟨2536064, by rfl⟩ : syracuseStep 3381419 = 5072129) B5072129
theorem B2254279 : Blo 2003435 2254279 := bstep (se 1 (by rfl) ⟨1690709, by rfl⟩ : syracuseStep 2254279 = 3381419) B3381419
theorem B3005705 : Blo 2003435 3005705 := bstep (se 2 (by rfl) ⟨1127139, by rfl⟩ : syracuseStep 3005705 = 2254279) B2254279
theorem B2003803 : Blo 2003435 2003803 := bstep (se 1 (by rfl) ⟨1502852, by rfl⟩ : syracuseStep 2003803 = 3005705) B3005705
theorem B10144277 : Blo 2003435 10144277 := bbase (se 6 (by rfl) ⟨237756, by rfl⟩ : syracuseStep 10144277 = 475513) (by norm_num)
theorem B6762851 : Blo 2003435 6762851 := bstep (se 1 (by rfl) ⟨5072138, by rfl⟩ : syracuseStep 6762851 = 10144277) B10144277
theorem B4508567 : Blo 2003435 4508567 := bstep (se 1 (by rfl) ⟨3381425, by rfl⟩ : syracuseStep 4508567 = 6762851) B6762851
theorem B3005711 : Blo 2003435 3005711 := bstep (se 1 (by rfl) ⟨2254283, by rfl⟩ : syracuseStep 3005711 = 4508567) B4508567
theorem B2003807 : Blo 2003435 2003807 := bstep (se 1 (by rfl) ⟨1502855, by rfl⟩ : syracuseStep 2003807 = 3005711) B3005711
theorem B3005717 : Blo 2003435 3005717 := bbase (se 6 (by rfl) ⟨70446, by rfl⟩ : syracuseStep 3005717 = 140893) (by norm_num)
theorem B2003811 : Blo 2003435 2003811 := bstep (se 1 (by rfl) ⟨1502858, by rfl⟩ : syracuseStep 2003811 = 3005717) B3005717
theorem B19258357 : Blo 2003435 19258357 := bbase (se 5 (by rfl) ⟨902735, by rfl⟩ : syracuseStep 19258357 = 1805471) (by norm_num)
theorem B25677809 : Blo 2003435 25677809 := bstep (se 2 (by rfl) ⟨9629178, by rfl⟩ : syracuseStep 25677809 = 19258357) B19258357
theorem B17118539 : Blo 2003435 17118539 := bstep (se 1 (by rfl) ⟨12838904, by rfl⟩ : syracuseStep 17118539 = 25677809) B25677809
theorem B11412359 : Blo 2003435 11412359 := bstep (se 1 (by rfl) ⟨8559269, by rfl⟩ : syracuseStep 11412359 = 17118539) B17118539
theorem B7608239 : Blo 2003435 7608239 := bstep (se 1 (by rfl) ⟨5706179, by rfl⟩ : syracuseStep 7608239 = 11412359) B11412359
theorem B5072159 : Blo 2003435 5072159 := bstep (se 1 (by rfl) ⟨3804119, by rfl⟩ : syracuseStep 5072159 = 7608239) B7608239
theorem B3381439 : Blo 2003435 3381439 := bstep (se 1 (by rfl) ⟨2536079, by rfl⟩ : syracuseStep 3381439 = 5072159) B5072159
theorem B4508585 : Blo 2003435 4508585 := bstep (se 2 (by rfl) ⟨1690719, by rfl⟩ : syracuseStep 4508585 = 3381439) B3381439
theorem B3005723 : Blo 2003435 3005723 := bstep (se 1 (by rfl) ⟨2254292, by rfl⟩ : syracuseStep 3005723 = 4508585) B4508585
theorem B2003815 : Blo 2003435 2003815 := bstep (se 1 (by rfl) ⟨1502861, by rfl⟩ : syracuseStep 2003815 = 3005723) B3005723
theorem B2254297 : Blo 2003435 2254297 := bbase (se 2 (by rfl) ⟨845361, by rfl⟩ : syracuseStep 2254297 = 1690723) (by norm_num)
theorem B3005729 : Blo 2003435 3005729 := bstep (se 2 (by rfl) ⟨1127148, by rfl⟩ : syracuseStep 3005729 = 2254297) B2254297
theorem B2003819 : Blo 2003435 2003819 := bstep (se 1 (by rfl) ⟨1502864, by rfl⟩ : syracuseStep 2003819 = 3005729) B3005729
theorem B2853101 : Blo 2003435 2853101 := bbase (se 3 (by rfl) ⟨534956, by rfl⟩ : syracuseStep 2853101 = 1069913) (by norm_num)
theorem B7608269 : Blo 2003435 7608269 := bstep (se 3 (by rfl) ⟨1426550, by rfl⟩ : syracuseStep 7608269 = 2853101) B2853101
theorem B5072179 : Blo 2003435 5072179 := bstep (se 1 (by rfl) ⟨3804134, by rfl⟩ : syracuseStep 5072179 = 7608269) B7608269
theorem B6762905 : Blo 2003435 6762905 := bstep (se 2 (by rfl) ⟨2536089, by rfl⟩ : syracuseStep 6762905 = 5072179) B5072179
theorem B4508603 : Blo 2003435 4508603 := bstep (se 1 (by rfl) ⟨3381452, by rfl⟩ : syracuseStep 4508603 = 6762905) B6762905
theorem B3005735 : Blo 2003435 3005735 := bstep (se 1 (by rfl) ⟨2254301, by rfl⟩ : syracuseStep 3005735 = 4508603) B4508603
theorem B2003823 : Blo 2003435 2003823 := bstep (se 1 (by rfl) ⟨1502867, by rfl⟩ : syracuseStep 2003823 = 3005735) B3005735
theorem B3005741 : Blo 2003435 3005741 := bbase (se 3 (by rfl) ⟨563576, by rfl⟩ : syracuseStep 3005741 = 1127153) (by norm_num)
theorem B2003827 : Blo 2003435 2003827 := bstep (se 1 (by rfl) ⟨1502870, by rfl⟩ : syracuseStep 2003827 = 3005741) B3005741
theorem B4508621 : Blo 2003435 4508621 := bbase (se 3 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 4508621 = 1690733) (by norm_num)
theorem B3005747 : Blo 2003435 3005747 := bstep (se 1 (by rfl) ⟨2254310, by rfl⟩ : syracuseStep 3005747 = 4508621) B4508621
theorem B2003831 : Blo 2003435 2003831 := bstep (se 1 (by rfl) ⟨1502873, by rfl⟩ : syracuseStep 2003831 = 3005747) B3005747
theorem B2536105 : Blo 2003435 2536105 := bbase (se 2 (by rfl) ⟨951039, by rfl⟩ : syracuseStep 2536105 = 1902079) (by norm_num)
theorem B3381473 : Blo 2003435 3381473 := bstep (se 2 (by rfl) ⟨1268052, by rfl⟩ : syracuseStep 3381473 = 2536105) B2536105
theorem B2254315 : Blo 2003435 2254315 := bstep (se 1 (by rfl) ⟨1690736, by rfl⟩ : syracuseStep 2254315 = 3381473) B3381473
theorem B3005753 : Blo 2003435 3005753 := bstep (se 2 (by rfl) ⟨1127157, by rfl⟩ : syracuseStep 3005753 = 2254315) B2254315
theorem B2003835 : Blo 2003435 2003835 := bstep (se 1 (by rfl) ⟨1502876, by rfl⟩ : syracuseStep 2003835 = 3005753) B3005753
theorem B9140309 : Blo 2003435 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B6093539 : Blo 2003435 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B4062359 : Blo 2003435 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B2708239 : Blo 2003435 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B3610985 : Blo 2003435 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B9629293 : Blo 2003435 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B12839057 : Blo 2003435 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B8559371 : Blo 2003435 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B22824989 : Blo 2003435 22824989 := bstep (se 3 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 22824989 = 8559371) B8559371
theorem B15216659 : Blo 2003435 15216659 := bstep (se 1 (by rfl) ⟨11412494, by rfl⟩ : syracuseStep 15216659 = 22824989) B22824989
theorem B10144439 : Blo 2003435 10144439 := bstep (se 1 (by rfl) ⟨7608329, by rfl⟩ : syracuseStep 10144439 = 15216659) B15216659
theorem B6762959 : Blo 2003435 6762959 := bstep (se 1 (by rfl) ⟨5072219, by rfl⟩ : syracuseStep 6762959 = 10144439) B10144439
theorem B4508639 : Blo 2003435 4508639 := bstep (se 1 (by rfl) ⟨3381479, by rfl⟩ : syracuseStep 4508639 = 6762959) B6762959
theorem B3005759 : Blo 2003435 3005759 := bstep (se 1 (by rfl) ⟨2254319, by rfl⟩ : syracuseStep 3005759 = 4508639) B4508639
theorem B2003839 : Blo 2003435 2003839 := bstep (se 1 (by rfl) ⟨1502879, by rfl⟩ : syracuseStep 2003839 = 3005759) B3005759
theorem B3005765 : Blo 2003435 3005765 := bbase (se 4 (by rfl) ⟨281790, by rfl⟩ : syracuseStep 3005765 = 563581) (by norm_num)
theorem B2003843 : Blo 2003435 2003843 := bstep (se 1 (by rfl) ⟨1502882, by rfl⟩ : syracuseStep 2003843 = 3005765) B3005765
theorem B3381493 : Blo 2003435 3381493 := bbase (se 5 (by rfl) ⟨158507, by rfl⟩ : syracuseStep 3381493 = 317015) (by norm_num)
theorem B4508657 : Blo 2003435 4508657 := bstep (se 2 (by rfl) ⟨1690746, by rfl⟩ : syracuseStep 4508657 = 3381493) B3381493
theorem B3005771 : Blo 2003435 3005771 := bstep (se 1 (by rfl) ⟨2254328, by rfl⟩ : syracuseStep 3005771 = 4508657) B4508657
theorem B2003847 : Blo 2003435 2003847 := bstep (se 1 (by rfl) ⟨1502885, by rfl⟩ : syracuseStep 2003847 = 3005771) B3005771
theorem B2254333 : Blo 2003435 2254333 := bbase (se 3 (by rfl) ⟨422687, by rfl⟩ : syracuseStep 2254333 = 845375) (by norm_num)
theorem B3005777 : Blo 2003435 3005777 := bstep (se 2 (by rfl) ⟨1127166, by rfl⟩ : syracuseStep 3005777 = 2254333) B2254333
theorem B2003851 : Blo 2003435 2003851 := bstep (se 1 (by rfl) ⟨1502888, by rfl⟩ : syracuseStep 2003851 = 3005777) B3005777
theorem B6763013 : Blo 2003435 6763013 := bbase (se 4 (by rfl) ⟨634032, by rfl⟩ : syracuseStep 6763013 = 1268065) (by norm_num)
theorem B4508675 : Blo 2003435 4508675 := bstep (se 1 (by rfl) ⟨3381506, by rfl⟩ : syracuseStep 4508675 = 6763013) B6763013
theorem B3005783 : Blo 2003435 3005783 := bstep (se 1 (by rfl) ⟨2254337, by rfl⟩ : syracuseStep 3005783 = 4508675) B4508675
theorem B2003855 : Blo 2003435 2003855 := bstep (se 1 (by rfl) ⟨1502891, by rfl⟩ : syracuseStep 2003855 = 3005783) B3005783
theorem B3005789 : Blo 2003435 3005789 := bbase (se 3 (by rfl) ⟨563585, by rfl⟩ : syracuseStep 3005789 = 1127171) (by norm_num)
theorem B2003859 : Blo 2003435 2003859 := bstep (se 1 (by rfl) ⟨1502894, by rfl⟩ : syracuseStep 2003859 = 3005789) B3005789
theorem B4508693 : Blo 2003435 4508693 := bbase (se 6 (by rfl) ⟨105672, by rfl⟩ : syracuseStep 4508693 = 211345) (by norm_num)
theorem B3005795 : Blo 2003435 3005795 := bstep (se 1 (by rfl) ⟨2254346, by rfl⟩ : syracuseStep 3005795 = 4508693) B4508693
theorem B2003863 : Blo 2003435 2003863 := bstep (se 1 (by rfl) ⟨1502897, by rfl⟩ : syracuseStep 2003863 = 3005795) B3005795
theorem B7608437 : Blo 2003435 7608437 := bbase (se 5 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 7608437 = 713291) (by norm_num)
theorem B5072291 : Blo 2003435 5072291 := bstep (se 1 (by rfl) ⟨3804218, by rfl⟩ : syracuseStep 5072291 = 7608437) B7608437
theorem B3381527 : Blo 2003435 3381527 := bstep (se 1 (by rfl) ⟨2536145, by rfl⟩ : syracuseStep 3381527 = 5072291) B5072291
theorem B2254351 : Blo 2003435 2254351 := bstep (se 1 (by rfl) ⟨1690763, by rfl⟩ : syracuseStep 2254351 = 3381527) B3381527
theorem B3005801 : Blo 2003435 3005801 := bstep (se 2 (by rfl) ⟨1127175, by rfl⟩ : syracuseStep 3005801 = 2254351) B2254351
theorem B2003867 : Blo 2003435 2003867 := bstep (se 1 (by rfl) ⟨1502900, by rfl⟩ : syracuseStep 2003867 = 3005801) B3005801
theorem B2139877 : Blo 2003435 2139877 := bbase (se 4 (by rfl) ⟨200613, by rfl⟩ : syracuseStep 2139877 = 401227) (by norm_num)
theorem B11412677 : Blo 2003435 11412677 := bstep (se 4 (by rfl) ⟨1069938, by rfl⟩ : syracuseStep 11412677 = 2139877) B2139877
theorem B7608451 : Blo 2003435 7608451 := bstep (se 1 (by rfl) ⟨5706338, by rfl⟩ : syracuseStep 7608451 = 11412677) B11412677
theorem B10144601 : Blo 2003435 10144601 := bstep (se 2 (by rfl) ⟨3804225, by rfl⟩ : syracuseStep 10144601 = 7608451) B7608451
theorem B6763067 : Blo 2003435 6763067 := bstep (se 1 (by rfl) ⟨5072300, by rfl⟩ : syracuseStep 6763067 = 10144601) B10144601
theorem B4508711 : Blo 2003435 4508711 := bstep (se 1 (by rfl) ⟨3381533, by rfl⟩ : syracuseStep 4508711 = 6763067) B6763067
theorem B3005807 : Blo 2003435 3005807 := bstep (se 1 (by rfl) ⟨2254355, by rfl⟩ : syracuseStep 3005807 = 4508711) B4508711
theorem B2003871 : Blo 2003435 2003871 := bstep (se 1 (by rfl) ⟨1502903, by rfl⟩ : syracuseStep 2003871 = 3005807) B3005807
theorem B3005813 : Blo 2003435 3005813 := bbase (se 5 (by rfl) ⟨140897, by rfl⟩ : syracuseStep 3005813 = 281795) (by norm_num)
theorem B2003875 : Blo 2003435 2003875 := bstep (se 1 (by rfl) ⟨1502906, by rfl⟩ : syracuseStep 2003875 = 3005813) B3005813
theorem B2853181 : Blo 2003435 2853181 := bbase (se 3 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 2853181 = 1069943) (by norm_num)
theorem B3804241 : Blo 2003435 3804241 := bstep (se 2 (by rfl) ⟨1426590, by rfl⟩ : syracuseStep 3804241 = 2853181) B2853181
theorem B5072321 : Blo 2003435 5072321 := bstep (se 2 (by rfl) ⟨1902120, by rfl⟩ : syracuseStep 5072321 = 3804241) B3804241
theorem B3381547 : Blo 2003435 3381547 := bstep (se 1 (by rfl) ⟨2536160, by rfl⟩ : syracuseStep 3381547 = 5072321) B5072321
theorem B4508729 : Blo 2003435 4508729 := bstep (se 2 (by rfl) ⟨1690773, by rfl⟩ : syracuseStep 4508729 = 3381547) B3381547
theorem B3005819 : Blo 2003435 3005819 := bstep (se 1 (by rfl) ⟨2254364, by rfl⟩ : syracuseStep 3005819 = 4508729) B4508729
theorem B2003879 : Blo 2003435 2003879 := bstep (se 1 (by rfl) ⟨1502909, by rfl⟩ : syracuseStep 2003879 = 3005819) B3005819
theorem B2254369 : Blo 2003435 2254369 := bbase (se 2 (by rfl) ⟨845388, by rfl⟩ : syracuseStep 2254369 = 1690777) (by norm_num)
theorem B3005825 : Blo 2003435 3005825 := bstep (se 2 (by rfl) ⟨1127184, by rfl⟩ : syracuseStep 3005825 = 2254369) B2254369
theorem B2003883 : Blo 2003435 2003883 := bstep (se 1 (by rfl) ⟨1502912, by rfl⟩ : syracuseStep 2003883 = 3005825) B3005825
theorem B5072341 : Blo 2003435 5072341 := bbase (se 7 (by rfl) ⟨59441, by rfl⟩ : syracuseStep 5072341 = 118883) (by norm_num)
theorem B6763121 : Blo 2003435 6763121 := bstep (se 2 (by rfl) ⟨2536170, by rfl⟩ : syracuseStep 6763121 = 5072341) B5072341
theorem B4508747 : Blo 2003435 4508747 := bstep (se 1 (by rfl) ⟨3381560, by rfl⟩ : syracuseStep 4508747 = 6763121) B6763121
theorem B3005831 : Blo 2003435 3005831 := bstep (se 1 (by rfl) ⟨2254373, by rfl⟩ : syracuseStep 3005831 = 4508747) B4508747
theorem B2003887 : Blo 2003435 2003887 := bstep (se 1 (by rfl) ⟨1502915, by rfl⟩ : syracuseStep 2003887 = 3005831) B3005831
theorem B3005837 : Blo 2003435 3005837 := bbase (se 3 (by rfl) ⟨563594, by rfl⟩ : syracuseStep 3005837 = 1127189) (by norm_num)
theorem B2003891 : Blo 2003435 2003891 := bstep (se 1 (by rfl) ⟨1502918, by rfl⟩ : syracuseStep 2003891 = 3005837) B3005837
theorem B4508765 : Blo 2003435 4508765 := bbase (se 3 (by rfl) ⟨845393, by rfl⟩ : syracuseStep 4508765 = 1690787) (by norm_num)
theorem B3005843 : Blo 2003435 3005843 := bstep (se 1 (by rfl) ⟨2254382, by rfl⟩ : syracuseStep 3005843 = 4508765) B4508765
theorem B2003895 : Blo 2003435 2003895 := bstep (se 1 (by rfl) ⟨1502921, by rfl⟩ : syracuseStep 2003895 = 3005843) B3005843
theorem B3381581 : Blo 2003435 3381581 := bbase (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) (by norm_num)
theorem B2254387 : Blo 2003435 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B3005849 : Blo 2003435 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B2003899 : Blo 2003435 2003899 := bstep (se 1 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 2003899 = 3005849) B3005849
theorem B10833301 : Blo 2003435 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B14444401 : Blo 2003435 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B19259201 : Blo 2003435 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B12839467 : Blo 2003435 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B17119289 : Blo 2003435 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B11412859 : Blo 2003435 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B15217145 : Blo 2003435 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B10144763 : Blo 2003435 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B6763175 : Blo 2003435 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B4508783 : Blo 2003435 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B3005855 : Blo 2003435 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B2003903 : Blo 2003435 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B3005861 : Blo 2003435 3005861 := bbase (se 4 (by rfl) ⟨281799, by rfl⟩ : syracuseStep 3005861 = 563599) (by norm_num)
theorem B2003907 : Blo 2003435 2003907 := bstep (se 1 (by rfl) ⟨1502930, by rfl⟩ : syracuseStep 2003907 = 3005861) B3005861
theorem B2536201 : Blo 2003435 2536201 := bbase (se 2 (by rfl) ⟨951075, by rfl⟩ : syracuseStep 2536201 = 1902151) (by norm_num)
theorem B3381601 : Blo 2003435 3381601 := bstep (se 2 (by rfl) ⟨1268100, by rfl⟩ : syracuseStep 3381601 = 2536201) B2536201
theorem B4508801 : Blo 2003435 4508801 := bstep (se 2 (by rfl) ⟨1690800, by rfl⟩ : syracuseStep 4508801 = 3381601) B3381601
theorem B3005867 : Blo 2003435 3005867 := bstep (se 1 (by rfl) ⟨2254400, by rfl⟩ : syracuseStep 3005867 = 4508801) B4508801
theorem B2003911 : Blo 2003435 2003911 := bstep (se 1 (by rfl) ⟨1502933, by rfl⟩ : syracuseStep 2003911 = 3005867) B3005867
theorem B2254405 : Blo 2003435 2254405 := bbase (se 4 (by rfl) ⟨211350, by rfl⟩ : syracuseStep 2254405 = 422701) (by norm_num)
theorem B3005873 : Blo 2003435 3005873 := bstep (se 2 (by rfl) ⟨1127202, by rfl⟩ : syracuseStep 3005873 = 2254405) B2254405
theorem B2003915 : Blo 2003435 2003915 := bstep (se 1 (by rfl) ⟨1502936, by rfl⟩ : syracuseStep 2003915 = 3005873) B3005873
theorem B3804317 : Blo 2003435 3804317 := bbase (se 3 (by rfl) ⟨713309, by rfl⟩ : syracuseStep 3804317 = 1426619) (by norm_num)
theorem B2536211 : Blo 2003435 2536211 := bstep (se 1 (by rfl) ⟨1902158, by rfl⟩ : syracuseStep 2536211 = 3804317) B3804317
theorem B6763229 : Blo 2003435 6763229 := bstep (se 3 (by rfl) ⟨1268105, by rfl⟩ : syracuseStep 6763229 = 2536211) B2536211
theorem B4508819 : Blo 2003435 4508819 := bstep (se 1 (by rfl) ⟨3381614, by rfl⟩ : syracuseStep 4508819 = 6763229) B6763229
theorem B3005879 : Blo 2003435 3005879 := bstep (se 1 (by rfl) ⟨2254409, by rfl⟩ : syracuseStep 3005879 = 4508819) B4508819
theorem B2003919 : Blo 2003435 2003919 := bstep (se 1 (by rfl) ⟨1502939, by rfl⟩ : syracuseStep 2003919 = 3005879) B3005879
theorem B3005885 : Blo 2003435 3005885 := bbase (se 3 (by rfl) ⟨563603, by rfl⟩ : syracuseStep 3005885 = 1127207) (by norm_num)
theorem B2003923 : Blo 2003435 2003923 := bstep (se 1 (by rfl) ⟨1502942, by rfl⟩ : syracuseStep 2003923 = 3005885) B3005885
theorem B4508837 : Blo 2003435 4508837 := bbase (se 4 (by rfl) ⟨422703, by rfl⟩ : syracuseStep 4508837 = 845407) (by norm_num)
theorem B3005891 : Blo 2003435 3005891 := bstep (se 1 (by rfl) ⟨2254418, by rfl⟩ : syracuseStep 3005891 = 4508837) B4508837
theorem B2003927 : Blo 2003435 2003927 := bstep (se 1 (by rfl) ⟨1502945, by rfl⟩ : syracuseStep 2003927 = 3005891) B3005891
theorem B5072453 : Blo 2003435 5072453 := bbase (se 4 (by rfl) ⟨475542, by rfl⟩ : syracuseStep 5072453 = 951085) (by norm_num)
theorem B3381635 : Blo 2003435 3381635 := bstep (se 1 (by rfl) ⟨2536226, by rfl⟩ : syracuseStep 3381635 = 5072453) B5072453
theorem B2254423 : Blo 2003435 2254423 := bstep (se 1 (by rfl) ⟨1690817, by rfl⟩ : syracuseStep 2254423 = 3381635) B3381635
theorem B3005897 : Blo 2003435 3005897 := bstep (se 2 (by rfl) ⟨1127211, by rfl⟩ : syracuseStep 3005897 = 2254423) B2254423
theorem B2003931 : Blo 2003435 2003931 := bstep (se 1 (by rfl) ⟨1502948, by rfl⟩ : syracuseStep 2003931 = 3005897) B3005897
theorem B8125109 : Blo 2003435 8125109 := bbase (se 5 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 8125109 = 761729) (by norm_num)
theorem B5416739 : Blo 2003435 5416739 := bstep (se 1 (by rfl) ⟨4062554, by rfl⟩ : syracuseStep 5416739 = 8125109) B8125109
theorem B3611159 : Blo 2003435 3611159 := bstep (se 1 (by rfl) ⟨2708369, by rfl⟩ : syracuseStep 3611159 = 5416739) B5416739
theorem B2407439 : Blo 2003435 2407439 := bstep (se 1 (by rfl) ⟨1805579, by rfl⟩ : syracuseStep 2407439 = 3611159) B3611159
theorem B6419837 : Blo 2003435 6419837 := bstep (se 3 (by rfl) ⟨1203719, by rfl⟩ : syracuseStep 6419837 = 2407439) B2407439
theorem B4279891 : Blo 2003435 4279891 := bstep (se 1 (by rfl) ⟨3209918, by rfl⟩ : syracuseStep 4279891 = 6419837) B6419837
theorem B5706521 : Blo 2003435 5706521 := bstep (se 2 (by rfl) ⟨2139945, by rfl⟩ : syracuseStep 5706521 = 4279891) B4279891
theorem B3804347 : Blo 2003435 3804347 := bstep (se 1 (by rfl) ⟨2853260, by rfl⟩ : syracuseStep 3804347 = 5706521) B5706521
theorem B10144925 : Blo 2003435 10144925 := bstep (se 3 (by rfl) ⟨1902173, by rfl⟩ : syracuseStep 10144925 = 3804347) B3804347
theorem B6763283 : Blo 2003435 6763283 := bstep (se 1 (by rfl) ⟨5072462, by rfl⟩ : syracuseStep 6763283 = 10144925) B10144925
theorem B4508855 : Blo 2003435 4508855 := bstep (se 1 (by rfl) ⟨3381641, by rfl⟩ : syracuseStep 4508855 = 6763283) B6763283
theorem B3005903 : Blo 2003435 3005903 := bstep (se 1 (by rfl) ⟨2254427, by rfl⟩ : syracuseStep 3005903 = 4508855) B4508855
theorem B2003935 : Blo 2003435 2003935 := bstep (se 1 (by rfl) ⟨1502951, by rfl⟩ : syracuseStep 2003935 = 3005903) B3005903
theorem B3005909 : Blo 2003435 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B2003939 : Blo 2003435 2003939 := bstep (se 1 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 2003939 = 3005909) B3005909
theorem B7608725 : Blo 2003435 7608725 := bbase (se 6 (by rfl) ⟨178329, by rfl⟩ : syracuseStep 7608725 = 356659) (by norm_num)
theorem B5072483 : Blo 2003435 5072483 := bstep (se 1 (by rfl) ⟨3804362, by rfl⟩ : syracuseStep 5072483 = 7608725) B7608725
theorem B3381655 : Blo 2003435 3381655 := bstep (se 1 (by rfl) ⟨2536241, by rfl⟩ : syracuseStep 3381655 = 5072483) B5072483
theorem B4508873 : Blo 2003435 4508873 := bstep (se 2 (by rfl) ⟨1690827, by rfl⟩ : syracuseStep 4508873 = 3381655) B3381655
theorem B3005915 : Blo 2003435 3005915 := bstep (se 1 (by rfl) ⟨2254436, by rfl⟩ : syracuseStep 3005915 = 4508873) B4508873
theorem B2003943 : Blo 2003435 2003943 := bstep (se 1 (by rfl) ⟨1502957, by rfl⟩ : syracuseStep 2003943 = 3005915) B3005915
theorem B2254441 : Blo 2003435 2254441 := bbase (se 2 (by rfl) ⟨845415, by rfl⟩ : syracuseStep 2254441 = 1690831) (by norm_num)
theorem B3005921 : Blo 2003435 3005921 := bstep (se 2 (by rfl) ⟨1127220, by rfl⟩ : syracuseStep 3005921 = 2254441) B2254441
theorem B2003947 : Blo 2003435 2003947 := bstep (se 1 (by rfl) ⟨1502960, by rfl⟩ : syracuseStep 2003947 = 3005921) B3005921
theorem B4279925 : Blo 2003435 4279925 := bbase (se 5 (by rfl) ⟨200621, by rfl⟩ : syracuseStep 4279925 = 401243) (by norm_num)
theorem B11413133 : Blo 2003435 11413133 := bstep (se 3 (by rfl) ⟨2139962, by rfl⟩ : syracuseStep 11413133 = 4279925) B4279925
theorem B7608755 : Blo 2003435 7608755 := bstep (se 1 (by rfl) ⟨5706566, by rfl⟩ : syracuseStep 7608755 = 11413133) B11413133
theorem B5072503 : Blo 2003435 5072503 := bstep (se 1 (by rfl) ⟨3804377, by rfl⟩ : syracuseStep 5072503 = 7608755) B7608755
theorem B6763337 : Blo 2003435 6763337 := bstep (se 2 (by rfl) ⟨2536251, by rfl⟩ : syracuseStep 6763337 = 5072503) B5072503
theorem B4508891 : Blo 2003435 4508891 := bstep (se 1 (by rfl) ⟨3381668, by rfl⟩ : syracuseStep 4508891 = 6763337) B6763337
theorem B3005927 : Blo 2003435 3005927 := bstep (se 1 (by rfl) ⟨2254445, by rfl⟩ : syracuseStep 3005927 = 4508891) B4508891
theorem B2003951 : Blo 2003435 2003951 := bstep (se 1 (by rfl) ⟨1502963, by rfl⟩ : syracuseStep 2003951 = 3005927) B3005927
theorem B3005933 : Blo 2003435 3005933 := bbase (se 3 (by rfl) ⟨563612, by rfl⟩ : syracuseStep 3005933 = 1127225) (by norm_num)
theorem B2003955 : Blo 2003435 2003955 := bstep (se 1 (by rfl) ⟨1502966, by rfl⟩ : syracuseStep 2003955 = 3005933) B3005933
theorem B4508909 : Blo 2003435 4508909 := bbase (se 3 (by rfl) ⟨845420, by rfl⟩ : syracuseStep 4508909 = 1690841) (by norm_num)
theorem B3005939 : Blo 2003435 3005939 := bstep (se 1 (by rfl) ⟨2254454, by rfl⟩ : syracuseStep 3005939 = 4508909) B4508909
theorem B2003959 : Blo 2003435 2003959 := bstep (se 1 (by rfl) ⟨1502969, by rfl⟩ : syracuseStep 2003959 = 3005939) B3005939
theorem B2853301 : Blo 2003435 2853301 := bbase (se 5 (by rfl) ⟨133748, by rfl⟩ : syracuseStep 2853301 = 267497) (by norm_num)
theorem B3804401 : Blo 2003435 3804401 := bstep (se 2 (by rfl) ⟨1426650, by rfl⟩ : syracuseStep 3804401 = 2853301) B2853301
theorem B2536267 : Blo 2003435 2536267 := bstep (se 1 (by rfl) ⟨1902200, by rfl⟩ : syracuseStep 2536267 = 3804401) B3804401
theorem B3381689 : Blo 2003435 3381689 := bstep (se 2 (by rfl) ⟨1268133, by rfl⟩ : syracuseStep 3381689 = 2536267) B2536267
theorem B2254459 : Blo 2003435 2254459 := bstep (se 1 (by rfl) ⟨1690844, by rfl⟩ : syracuseStep 2254459 = 3381689) B3381689
theorem B3005945 : Blo 2003435 3005945 := bstep (se 2 (by rfl) ⟨1127229, by rfl⟩ : syracuseStep 3005945 = 2254459) B2254459
theorem B2003963 : Blo 2003435 2003963 := bstep (se 1 (by rfl) ⟨1502972, by rfl⟩ : syracuseStep 2003963 = 3005945) B3005945
theorem B3253765 : Blo 2003435 3253765 := bbase (se 4 (by rfl) ⟨305040, by rfl⟩ : syracuseStep 3253765 = 610081) (by norm_num)
theorem B4338353 : Blo 2003435 4338353 := bstep (se 2 (by rfl) ⟨1626882, by rfl⟩ : syracuseStep 4338353 = 3253765) B3253765
theorem B2892235 : Blo 2003435 2892235 := bstep (se 1 (by rfl) ⟨2169176, by rfl⟩ : syracuseStep 2892235 = 4338353) B4338353
theorem B3856313 : Blo 2003435 3856313 := bstep (se 2 (by rfl) ⟨1446117, by rfl⟩ : syracuseStep 3856313 = 2892235) B2892235
theorem B10283501 : Blo 2003435 10283501 := bstep (se 3 (by rfl) ⟨1928156, by rfl⟩ : syracuseStep 10283501 = 3856313) B3856313
theorem B6855667 : Blo 2003435 6855667 := bstep (se 1 (by rfl) ⟨5141750, by rfl⟩ : syracuseStep 6855667 = 10283501) B10283501
theorem B36563557 : Blo 2003435 36563557 := bstep (se 4 (by rfl) ⟨3427833, by rfl⟩ : syracuseStep 36563557 = 6855667) B6855667
theorem B48751409 : Blo 2003435 48751409 := bstep (se 2 (by rfl) ⟨18281778, by rfl⟩ : syracuseStep 48751409 = 36563557) B36563557
theorem B32500939 : Blo 2003435 32500939 := bstep (se 1 (by rfl) ⟨24375704, by rfl⟩ : syracuseStep 32500939 = 48751409) B48751409
theorem B43334585 : Blo 2003435 43334585 := bstep (se 2 (by rfl) ⟨16250469, by rfl⟩ : syracuseStep 43334585 = 32500939) B32500939
theorem B28889723 : Blo 2003435 28889723 := bstep (se 1 (by rfl) ⟨21667292, by rfl⟩ : syracuseStep 28889723 = 43334585) B43334585
theorem B77039261 : Blo 2003435 77039261 := bstep (se 3 (by rfl) ⟨14444861, by rfl⟩ : syracuseStep 77039261 = 28889723) B28889723
theorem B51359507 : Blo 2003435 51359507 := bstep (se 1 (by rfl) ⟨38519630, by rfl⟩ : syracuseStep 51359507 = 77039261) B77039261
theorem B34239671 : Blo 2003435 34239671 := bstep (se 1 (by rfl) ⟨25679753, by rfl⟩ : syracuseStep 34239671 = 51359507) B51359507
theorem B22826447 : Blo 2003435 22826447 := bstep (se 1 (by rfl) ⟨17119835, by rfl⟩ : syracuseStep 22826447 = 34239671) B34239671
theorem B15217631 : Blo 2003435 15217631 := bstep (se 1 (by rfl) ⟨11413223, by rfl⟩ : syracuseStep 15217631 = 22826447) B22826447
theorem B10145087 : Blo 2003435 10145087 := bstep (se 1 (by rfl) ⟨7608815, by rfl⟩ : syracuseStep 10145087 = 15217631) B15217631
theorem B6763391 : Blo 2003435 6763391 := bstep (se 1 (by rfl) ⟨5072543, by rfl⟩ : syracuseStep 6763391 = 10145087) B10145087
theorem B4508927 : Blo 2003435 4508927 := bstep (se 1 (by rfl) ⟨3381695, by rfl⟩ : syracuseStep 4508927 = 6763391) B6763391
theorem B3005951 : Blo 2003435 3005951 := bstep (se 1 (by rfl) ⟨2254463, by rfl⟩ : syracuseStep 3005951 = 4508927) B4508927
theorem B2003967 : Blo 2003435 2003967 := bstep (se 1 (by rfl) ⟨1502975, by rfl⟩ : syracuseStep 2003967 = 3005951) B3005951
theorem B3005957 : Blo 2003435 3005957 := bbase (se 4 (by rfl) ⟨281808, by rfl⟩ : syracuseStep 3005957 = 563617) (by norm_num)
theorem B2003971 : Blo 2003435 2003971 := bstep (se 1 (by rfl) ⟨1502978, by rfl⟩ : syracuseStep 2003971 = 3005957) B3005957
theorem B3381709 : Blo 2003435 3381709 := bbase (se 3 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 3381709 = 1268141) (by norm_num)
theorem B4508945 : Blo 2003435 4508945 := bstep (se 2 (by rfl) ⟨1690854, by rfl⟩ : syracuseStep 4508945 = 3381709) B3381709
theorem B3005963 : Blo 2003435 3005963 := bstep (se 1 (by rfl) ⟨2254472, by rfl⟩ : syracuseStep 3005963 = 4508945) B4508945
theorem B2003975 : Blo 2003435 2003975 := bstep (se 1 (by rfl) ⟨1502981, by rfl⟩ : syracuseStep 2003975 = 3005963) B3005963
theorem B2254477 : Blo 2003435 2254477 := bbase (se 3 (by rfl) ⟨422714, by rfl⟩ : syracuseStep 2254477 = 845429) (by norm_num)
theorem B3005969 : Blo 2003435 3005969 := bstep (se 2 (by rfl) ⟨1127238, by rfl⟩ : syracuseStep 3005969 = 2254477) B2254477
theorem B2003979 : Blo 2003435 2003979 := bstep (se 1 (by rfl) ⟨1502984, by rfl⟩ : syracuseStep 2003979 = 3005969) B3005969
theorem B6763445 : Blo 2003435 6763445 := bbase (se 5 (by rfl) ⟨317036, by rfl⟩ : syracuseStep 6763445 = 634073) (by norm_num)
theorem B4508963 : Blo 2003435 4508963 := bstep (se 1 (by rfl) ⟨3381722, by rfl⟩ : syracuseStep 4508963 = 6763445) B6763445
theorem B3005975 : Blo 2003435 3005975 := bstep (se 1 (by rfl) ⟨2254481, by rfl⟩ : syracuseStep 3005975 = 4508963) B4508963
theorem B2003983 : Blo 2003435 2003983 := bstep (se 1 (by rfl) ⟨1502987, by rfl⟩ : syracuseStep 2003983 = 3005975) B3005975
theorem B3005981 : Blo 2003435 3005981 := bbase (se 3 (by rfl) ⟨563621, by rfl⟩ : syracuseStep 3005981 = 1127243) (by norm_num)
theorem B2003987 : Blo 2003435 2003987 := bstep (se 1 (by rfl) ⟨1502990, by rfl⟩ : syracuseStep 2003987 = 3005981) B3005981
theorem B4508981 : Blo 2003435 4508981 := bbase (se 5 (by rfl) ⟨211358, by rfl⟩ : syracuseStep 4508981 = 422717) (by norm_num)
theorem B3005987 : Blo 2003435 3005987 := bstep (se 1 (by rfl) ⟨2254490, by rfl⟩ : syracuseStep 3005987 = 4508981) B4508981
theorem B2003991 : Blo 2003435 2003991 := bstep (se 1 (by rfl) ⟨1502993, by rfl⟩ : syracuseStep 2003991 = 3005987) B3005987
theorem B2892277 : Blo 2003435 2892277 := bbase (se 5 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 2892277 = 271151) (by norm_num)
theorem B3856369 : Blo 2003435 3856369 := bstep (se 2 (by rfl) ⟨1446138, by rfl⟩ : syracuseStep 3856369 = 2892277) B2892277
theorem B5141825 : Blo 2003435 5141825 := bstep (se 2 (by rfl) ⟨1928184, by rfl⟩ : syracuseStep 5141825 = 3856369) B3856369
theorem B3427883 : Blo 2003435 3427883 := bstep (se 1 (by rfl) ⟨2570912, by rfl⟩ : syracuseStep 3427883 = 5141825) B5141825
theorem B2285255 : Blo 2003435 2285255 := bstep (se 1 (by rfl) ⟨1713941, by rfl⟩ : syracuseStep 2285255 = 3427883) B3427883
theorem B6094013 : Blo 2003435 6094013 := bstep (se 3 (by rfl) ⟨1142627, by rfl⟩ : syracuseStep 6094013 = 2285255) B2285255
theorem B16250701 : Blo 2003435 16250701 := bstep (se 3 (by rfl) ⟨3047006, by rfl⟩ : syracuseStep 16250701 = 6094013) B6094013
theorem B21667601 : Blo 2003435 21667601 := bstep (se 2 (by rfl) ⟨8125350, by rfl⟩ : syracuseStep 21667601 = 16250701) B16250701
theorem B14445067 : Blo 2003435 14445067 := bstep (se 1 (by rfl) ⟨10833800, by rfl⟩ : syracuseStep 14445067 = 21667601) B21667601
theorem B19260089 : Blo 2003435 19260089 := bstep (se 2 (by rfl) ⟨7222533, by rfl⟩ : syracuseStep 19260089 = 14445067) B14445067
theorem B12840059 : Blo 2003435 12840059 := bstep (se 1 (by rfl) ⟨9630044, by rfl⟩ : syracuseStep 12840059 = 19260089) B19260089
theorem B8560039 : Blo 2003435 8560039 := bstep (se 1 (by rfl) ⟨6420029, by rfl⟩ : syracuseStep 8560039 = 12840059) B12840059
theorem B11413385 : Blo 2003435 11413385 := bstep (se 2 (by rfl) ⟨4280019, by rfl⟩ : syracuseStep 11413385 = 8560039) B8560039
theorem B7608923 : Blo 2003435 7608923 := bstep (se 1 (by rfl) ⟨5706692, by rfl⟩ : syracuseStep 7608923 = 11413385) B11413385
theorem B5072615 : Blo 2003435 5072615 := bstep (se 1 (by rfl) ⟨3804461, by rfl⟩ : syracuseStep 5072615 = 7608923) B7608923
theorem B3381743 : Blo 2003435 3381743 := bstep (se 1 (by rfl) ⟨2536307, by rfl⟩ : syracuseStep 3381743 = 5072615) B5072615
theorem B2254495 : Blo 2003435 2254495 := bstep (se 1 (by rfl) ⟨1690871, by rfl⟩ : syracuseStep 2254495 = 3381743) B3381743
theorem B3005993 : Blo 2003435 3005993 := bstep (se 2 (by rfl) ⟨1127247, by rfl⟩ : syracuseStep 3005993 = 2254495) B2254495
theorem B2003995 : Blo 2003435 2003995 := bstep (se 1 (by rfl) ⟨1502996, by rfl⟩ : syracuseStep 2003995 = 3005993) B3005993
theorem B10283669 : Blo 2003435 10283669 := bbase (se 6 (by rfl) ⟨241023, by rfl⟩ : syracuseStep 10283669 = 482047) (by norm_num)
theorem B6855779 : Blo 2003435 6855779 := bstep (se 1 (by rfl) ⟨5141834, by rfl⟩ : syracuseStep 6855779 = 10283669) B10283669
theorem B4570519 : Blo 2003435 4570519 := bstep (se 1 (by rfl) ⟨3427889, by rfl⟩ : syracuseStep 4570519 = 6855779) B6855779
theorem B6094025 : Blo 2003435 6094025 := bstep (se 2 (by rfl) ⟨2285259, by rfl⟩ : syracuseStep 6094025 = 4570519) B4570519
theorem B4062683 : Blo 2003435 4062683 := bstep (se 1 (by rfl) ⟨3047012, by rfl⟩ : syracuseStep 4062683 = 6094025) B6094025
theorem B10833821 : Blo 2003435 10833821 := bstep (se 3 (by rfl) ⟨2031341, by rfl⟩ : syracuseStep 10833821 = 4062683) B4062683
theorem B7222547 : Blo 2003435 7222547 := bstep (se 1 (by rfl) ⟨5416910, by rfl⟩ : syracuseStep 7222547 = 10833821) B10833821
theorem B19260125 : Blo 2003435 19260125 := bstep (se 3 (by rfl) ⟨3611273, by rfl⟩ : syracuseStep 19260125 = 7222547) B7222547
theorem B12840083 : Blo 2003435 12840083 := bstep (se 1 (by rfl) ⟨9630062, by rfl⟩ : syracuseStep 12840083 = 19260125) B19260125
theorem B8560055 : Blo 2003435 8560055 := bstep (se 1 (by rfl) ⟨6420041, by rfl⟩ : syracuseStep 8560055 = 12840083) B12840083
theorem B5706703 : Blo 2003435 5706703 := bstep (se 1 (by rfl) ⟨4280027, by rfl⟩ : syracuseStep 5706703 = 8560055) B8560055
theorem B7608937 : Blo 2003435 7608937 := bstep (se 2 (by rfl) ⟨2853351, by rfl⟩ : syracuseStep 7608937 = 5706703) B5706703
theorem B10145249 : Blo 2003435 10145249 := bstep (se 2 (by rfl) ⟨3804468, by rfl⟩ : syracuseStep 10145249 = 7608937) B7608937
theorem B6763499 : Blo 2003435 6763499 := bstep (se 1 (by rfl) ⟨5072624, by rfl⟩ : syracuseStep 6763499 = 10145249) B10145249
theorem B4508999 : Blo 2003435 4508999 := bstep (se 1 (by rfl) ⟨3381749, by rfl⟩ : syracuseStep 4508999 = 6763499) B6763499
theorem B3005999 : Blo 2003435 3005999 := bstep (se 1 (by rfl) ⟨2254499, by rfl⟩ : syracuseStep 3005999 = 4508999) B4508999
theorem B2003999 : Blo 2003435 2003999 := bstep (se 1 (by rfl) ⟨1502999, by rfl⟩ : syracuseStep 2003999 = 3005999) B3005999
theorem B3006005 : Blo 2003435 3006005 := bbase (se 5 (by rfl) ⟨140906, by rfl⟩ : syracuseStep 3006005 = 281813) (by norm_num)
theorem B2004003 : Blo 2003435 2004003 := bstep (se 1 (by rfl) ⟨1503002, by rfl⟩ : syracuseStep 2004003 = 3006005) B3006005
theorem B5072645 : Blo 2003435 5072645 := bbase (se 4 (by rfl) ⟨475560, by rfl⟩ : syracuseStep 5072645 = 951121) (by norm_num)
theorem B3381763 : Blo 2003435 3381763 := bstep (se 1 (by rfl) ⟨2536322, by rfl⟩ : syracuseStep 3381763 = 5072645) B5072645
theorem B4509017 : Blo 2003435 4509017 := bstep (se 2 (by rfl) ⟨1690881, by rfl⟩ : syracuseStep 4509017 = 3381763) B3381763
theorem B3006011 : Blo 2003435 3006011 := bstep (se 1 (by rfl) ⟨2254508, by rfl⟩ : syracuseStep 3006011 = 4509017) B4509017
theorem B2004007 : Blo 2003435 2004007 := bstep (se 1 (by rfl) ⟨1503005, by rfl⟩ : syracuseStep 2004007 = 3006011) B3006011
theorem B2254513 : Blo 2003435 2254513 := bbase (se 2 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 2254513 = 1690885) (by norm_num)
theorem B3006017 : Blo 2003435 3006017 := bstep (se 2 (by rfl) ⟨1127256, by rfl⟩ : syracuseStep 3006017 = 2254513) B2254513
theorem B2004011 : Blo 2003435 2004011 := bstep (se 1 (by rfl) ⟨1503008, by rfl⟩ : syracuseStep 2004011 = 3006017) B3006017
theorem B2507429 : Blo 2003435 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B6686477 : Blo 2003435 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B4457651 : Blo 2003435 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B11887069 : Blo 2003435 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B15849425 : Blo 2003435 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B10566283 : Blo 2003435 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B14088377 : Blo 2003435 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B37569005 : Blo 2003435 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B25046003 : Blo 2003435 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B16697335 : Blo 2003435 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B22263113 : Blo 2003435 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B14842075 : Blo 2003435 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B19789433 : Blo 2003435 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B13192955 : Blo 2003435 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B8795303 : Blo 2003435 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B5863535 : Blo 2003435 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B3909023 : Blo 2003435 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B2606015 : Blo 2003435 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B6949373 : Blo 2003435 6949373 := bstep (se 3 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 6949373 = 2606015) B2606015
theorem B18531661 : Blo 2003435 18531661 := bstep (se 3 (by rfl) ⟨3474686, by rfl⟩ : syracuseStep 18531661 = 6949373) B6949373
theorem B24708881 : Blo 2003435 24708881 := bstep (se 2 (by rfl) ⟨9265830, by rfl⟩ : syracuseStep 24708881 = 18531661) B18531661
theorem B16472587 : Blo 2003435 16472587 := bstep (se 1 (by rfl) ⟨12354440, by rfl⟩ : syracuseStep 16472587 = 24708881) B24708881
theorem B21963449 : Blo 2003435 21963449 := bstep (se 2 (by rfl) ⟨8236293, by rfl⟩ : syracuseStep 21963449 = 16472587) B16472587
theorem B14642299 : Blo 2003435 14642299 := bstep (se 1 (by rfl) ⟨10981724, by rfl⟩ : syracuseStep 14642299 = 21963449) B21963449
theorem B19523065 : Blo 2003435 19523065 := bstep (se 2 (by rfl) ⟨7321149, by rfl⟩ : syracuseStep 19523065 = 14642299) B14642299
theorem B26030753 : Blo 2003435 26030753 := bstep (se 2 (by rfl) ⟨9761532, by rfl⟩ : syracuseStep 26030753 = 19523065) B19523065
theorem B17353835 : Blo 2003435 17353835 := bstep (se 1 (by rfl) ⟨13015376, by rfl⟩ : syracuseStep 17353835 = 26030753) B26030753
theorem B11569223 : Blo 2003435 11569223 := bstep (se 1 (by rfl) ⟨8676917, by rfl⟩ : syracuseStep 11569223 = 17353835) B17353835
theorem B7712815 : Blo 2003435 7712815 := bstep (se 1 (by rfl) ⟨5784611, by rfl⟩ : syracuseStep 7712815 = 11569223) B11569223
theorem B10283753 : Blo 2003435 10283753 := bstep (se 2 (by rfl) ⟨3856407, by rfl⟩ : syracuseStep 10283753 = 7712815) B7712815
theorem B6855835 : Blo 2003435 6855835 := bstep (se 1 (by rfl) ⟨5141876, by rfl⟩ : syracuseStep 6855835 = 10283753) B10283753
theorem B9141113 : Blo 2003435 9141113 := bstep (se 2 (by rfl) ⟨3427917, by rfl⟩ : syracuseStep 9141113 = 6855835) B6855835
theorem B24376301 : Blo 2003435 24376301 := bstep (se 3 (by rfl) ⟨4570556, by rfl⟩ : syracuseStep 24376301 = 9141113) B9141113
theorem B16250867 : Blo 2003435 16250867 := bstep (se 1 (by rfl) ⟨12188150, by rfl⟩ : syracuseStep 16250867 = 24376301) B24376301
theorem B10833911 : Blo 2003435 10833911 := bstep (se 1 (by rfl) ⟨8125433, by rfl⟩ : syracuseStep 10833911 = 16250867) B16250867
theorem B7222607 : Blo 2003435 7222607 := bstep (se 1 (by rfl) ⟨5416955, by rfl⟩ : syracuseStep 7222607 = 10833911) B10833911
theorem B4815071 : Blo 2003435 4815071 := bstep (se 1 (by rfl) ⟨3611303, by rfl⟩ : syracuseStep 4815071 = 7222607) B7222607
theorem B3210047 : Blo 2003435 3210047 := bstep (se 1 (by rfl) ⟨2407535, by rfl⟩ : syracuseStep 3210047 = 4815071) B4815071
theorem B2140031 : Blo 2003435 2140031 := bstep (se 1 (by rfl) ⟨1605023, by rfl⟩ : syracuseStep 2140031 = 3210047) B3210047
theorem B5706749 : Blo 2003435 5706749 := bstep (se 3 (by rfl) ⟨1070015, by rfl⟩ : syracuseStep 5706749 = 2140031) B2140031
theorem B3804499 : Blo 2003435 3804499 := bstep (se 1 (by rfl) ⟨2853374, by rfl⟩ : syracuseStep 3804499 = 5706749) B5706749
theorem B5072665 : Blo 2003435 5072665 := bstep (se 2 (by rfl) ⟨1902249, by rfl⟩ : syracuseStep 5072665 = 3804499) B3804499
theorem B6763553 : Blo 2003435 6763553 := bstep (se 2 (by rfl) ⟨2536332, by rfl⟩ : syracuseStep 6763553 = 5072665) B5072665
theorem B4509035 : Blo 2003435 4509035 := bstep (se 1 (by rfl) ⟨3381776, by rfl⟩ : syracuseStep 4509035 = 6763553) B6763553
theorem B3006023 : Blo 2003435 3006023 := bstep (se 1 (by rfl) ⟨2254517, by rfl⟩ : syracuseStep 3006023 = 4509035) B4509035
theorem B2004015 : Blo 2003435 2004015 := bstep (se 1 (by rfl) ⟨1503011, by rfl⟩ : syracuseStep 2004015 = 3006023) B3006023
theorem B3006029 : Blo 2003435 3006029 := bbase (se 3 (by rfl) ⟨563630, by rfl⟩ : syracuseStep 3006029 = 1127261) (by norm_num)
theorem B2004019 : Blo 2003435 2004019 := bstep (se 1 (by rfl) ⟨1503014, by rfl⟩ : syracuseStep 2004019 = 3006029) B3006029
theorem B4509053 : Blo 2003435 4509053 := bbase (se 3 (by rfl) ⟨845447, by rfl⟩ : syracuseStep 4509053 = 1690895) (by norm_num)
theorem B3006035 : Blo 2003435 3006035 := bstep (se 1 (by rfl) ⟨2254526, by rfl⟩ : syracuseStep 3006035 = 4509053) B4509053
theorem B2004023 : Blo 2003435 2004023 := bstep (se 1 (by rfl) ⟨1503017, by rfl⟩ : syracuseStep 2004023 = 3006035) B3006035
theorem B3381797 : Blo 2003435 3381797 := bbase (se 4 (by rfl) ⟨317043, by rfl⟩ : syracuseStep 3381797 = 634087) (by norm_num)
theorem B2254531 : Blo 2003435 2254531 := bstep (se 1 (by rfl) ⟨1690898, by rfl⟩ : syracuseStep 2254531 = 3381797) B3381797
theorem B3006041 : Blo 2003435 3006041 := bstep (se 2 (by rfl) ⟨1127265, by rfl⟩ : syracuseStep 3006041 = 2254531) B2254531
theorem B2004027 : Blo 2003435 2004027 := bstep (se 1 (by rfl) ⟨1503020, by rfl⟩ : syracuseStep 2004027 = 3006041) B3006041
theorem B2853397 : Blo 2003435 2853397 := bbase (se 6 (by rfl) ⟨66876, by rfl⟩ : syracuseStep 2853397 = 133753) (by norm_num)
theorem B15218117 : Blo 2003435 15218117 := bstep (se 4 (by rfl) ⟨1426698, by rfl⟩ : syracuseStep 15218117 = 2853397) B2853397
theorem B10145411 : Blo 2003435 10145411 := bstep (se 1 (by rfl) ⟨7609058, by rfl⟩ : syracuseStep 10145411 = 15218117) B15218117
theorem B6763607 : Blo 2003435 6763607 := bstep (se 1 (by rfl) ⟨5072705, by rfl⟩ : syracuseStep 6763607 = 10145411) B10145411
theorem B4509071 : Blo 2003435 4509071 := bstep (se 1 (by rfl) ⟨3381803, by rfl⟩ : syracuseStep 4509071 = 6763607) B6763607
theorem B3006047 : Blo 2003435 3006047 := bstep (se 1 (by rfl) ⟨2254535, by rfl⟩ : syracuseStep 3006047 = 4509071) B4509071
theorem B2004031 : Blo 2003435 2004031 := bstep (se 1 (by rfl) ⟨1503023, by rfl⟩ : syracuseStep 2004031 = 3006047) B3006047
theorem B3006053 : Blo 2003435 3006053 := bbase (se 4 (by rfl) ⟨281817, by rfl⟩ : syracuseStep 3006053 = 563635) (by norm_num)
theorem B2004035 : Blo 2003435 2004035 := bstep (se 1 (by rfl) ⟨1503026, by rfl⟩ : syracuseStep 2004035 = 3006053) B3006053
theorem B2140057 : Blo 2003435 2140057 := bbase (se 2 (by rfl) ⟨802521, by rfl⟩ : syracuseStep 2140057 = 1605043) (by norm_num)
theorem B2853409 : Blo 2003435 2853409 := bstep (se 2 (by rfl) ⟨1070028, by rfl⟩ : syracuseStep 2853409 = 2140057) B2140057
theorem B3804545 : Blo 2003435 3804545 := bstep (se 2 (by rfl) ⟨1426704, by rfl⟩ : syracuseStep 3804545 = 2853409) B2853409
theorem B2536363 : Blo 2003435 2536363 := bstep (se 1 (by rfl) ⟨1902272, by rfl⟩ : syracuseStep 2536363 = 3804545) B3804545
theorem B3381817 : Blo 2003435 3381817 := bstep (se 2 (by rfl) ⟨1268181, by rfl⟩ : syracuseStep 3381817 = 2536363) B2536363
theorem B4509089 : Blo 2003435 4509089 := bstep (se 2 (by rfl) ⟨1690908, by rfl⟩ : syracuseStep 4509089 = 3381817) B3381817
theorem B3006059 : Blo 2003435 3006059 := bstep (se 1 (by rfl) ⟨2254544, by rfl⟩ : syracuseStep 3006059 = 4509089) B4509089
theorem B2004039 : Blo 2003435 2004039 := bstep (se 1 (by rfl) ⟨1503029, by rfl⟩ : syracuseStep 2004039 = 3006059) B3006059
theorem B2254549 : Blo 2003435 2254549 := bbase (se 7 (by rfl) ⟨26420, by rfl⟩ : syracuseStep 2254549 = 52841) (by norm_num)
theorem B3006065 : Blo 2003435 3006065 := bstep (se 2 (by rfl) ⟨1127274, by rfl⟩ : syracuseStep 3006065 = 2254549) B2254549
theorem B2004043 : Blo 2003435 2004043 := bstep (se 1 (by rfl) ⟨1503032, by rfl⟩ : syracuseStep 2004043 = 3006065) B3006065
theorem B2536373 : Blo 2003435 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B6763661 : Blo 2003435 6763661 := bstep (se 3 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 6763661 = 2536373) B2536373
theorem B4509107 : Blo 2003435 4509107 := bstep (se 1 (by rfl) ⟨3381830, by rfl⟩ : syracuseStep 4509107 = 6763661) B6763661
theorem B3006071 : Blo 2003435 3006071 := bstep (se 1 (by rfl) ⟨2254553, by rfl⟩ : syracuseStep 3006071 = 4509107) B4509107
theorem B2004047 : Blo 2003435 2004047 := bstep (se 1 (by rfl) ⟨1503035, by rfl⟩ : syracuseStep 2004047 = 3006071) B3006071
theorem B3006077 : Blo 2003435 3006077 := bbase (se 3 (by rfl) ⟨563639, by rfl⟩ : syracuseStep 3006077 = 1127279) (by norm_num)
theorem B2004051 : Blo 2003435 2004051 := bstep (se 1 (by rfl) ⟨1503038, by rfl⟩ : syracuseStep 2004051 = 3006077) B3006077
theorem B4509125 : Blo 2003435 4509125 := bbase (se 4 (by rfl) ⟨422730, by rfl⟩ : syracuseStep 4509125 = 845461) (by norm_num)
theorem B3006083 : Blo 2003435 3006083 := bstep (se 1 (by rfl) ⟨2254562, by rfl⟩ : syracuseStep 3006083 = 4509125) B4509125
theorem B2004055 : Blo 2003435 2004055 := bstep (se 1 (by rfl) ⟨1503041, by rfl⟩ : syracuseStep 2004055 = 3006083) B3006083
theorem B2285329 : Blo 2003435 2285329 := bbase (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) (by norm_num)
theorem B3047105 : Blo 2003435 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B2031403 : Blo 2003435 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B2708537 : Blo 2003435 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B7222765 : Blo 2003435 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B9630353 : Blo 2003435 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B6420235 : Blo 2003435 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B8560313 : Blo 2003435 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B5706875 : Blo 2003435 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B3804583 : Blo 2003435 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B5072777 : Blo 2003435 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B3381851 : Blo 2003435 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B2254567 : Blo 2003435 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B3006089 : Blo 2003435 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B2004059 : Blo 2003435 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B10145573 : Blo 2003435 10145573 := bbase (se 4 (by rfl) ⟨951147, by rfl⟩ : syracuseStep 10145573 = 1902295) (by norm_num)
theorem B6763715 : Blo 2003435 6763715 := bstep (se 1 (by rfl) ⟨5072786, by rfl⟩ : syracuseStep 6763715 = 10145573) B10145573
theorem B4509143 : Blo 2003435 4509143 := bstep (se 1 (by rfl) ⟨3381857, by rfl⟩ : syracuseStep 4509143 = 6763715) B6763715
theorem B3006095 : Blo 2003435 3006095 := bstep (se 1 (by rfl) ⟨2254571, by rfl⟩ : syracuseStep 3006095 = 4509143) B4509143
theorem B2004063 : Blo 2003435 2004063 := bstep (se 1 (by rfl) ⟨1503047, by rfl⟩ : syracuseStep 2004063 = 3006095) B3006095
theorem B3006101 : Blo 2003435 3006101 := bbase (se 6 (by rfl) ⟨70455, by rfl⟩ : syracuseStep 3006101 = 140911) (by norm_num)
theorem B2004067 : Blo 2003435 2004067 := bstep (se 1 (by rfl) ⟨1503050, by rfl⟩ : syracuseStep 2004067 = 3006101) B3006101
theorem B16251317 : Blo 2003435 16251317 := bbase (se 5 (by rfl) ⟨761780, by rfl⟩ : syracuseStep 16251317 = 1523561) (by norm_num)
theorem B10834211 : Blo 2003435 10834211 := bstep (se 1 (by rfl) ⟨8125658, by rfl⟩ : syracuseStep 10834211 = 16251317) B16251317
theorem B7222807 : Blo 2003435 7222807 := bstep (se 1 (by rfl) ⟨5417105, by rfl⟩ : syracuseStep 7222807 = 10834211) B10834211
theorem B9630409 : Blo 2003435 9630409 := bstep (se 2 (by rfl) ⟨3611403, by rfl⟩ : syracuseStep 9630409 = 7222807) B7222807
theorem B12840545 : Blo 2003435 12840545 := bstep (se 2 (by rfl) ⟨4815204, by rfl⟩ : syracuseStep 12840545 = 9630409) B9630409
theorem B8560363 : Blo 2003435 8560363 := bstep (se 1 (by rfl) ⟨6420272, by rfl⟩ : syracuseStep 8560363 = 12840545) B12840545
theorem B11413817 : Blo 2003435 11413817 := bstep (se 2 (by rfl) ⟨4280181, by rfl⟩ : syracuseStep 11413817 = 8560363) B8560363
theorem B7609211 : Blo 2003435 7609211 := bstep (se 1 (by rfl) ⟨5706908, by rfl⟩ : syracuseStep 7609211 = 11413817) B11413817
theorem B5072807 : Blo 2003435 5072807 := bstep (se 1 (by rfl) ⟨3804605, by rfl⟩ : syracuseStep 5072807 = 7609211) B7609211
theorem B3381871 : Blo 2003435 3381871 := bstep (se 1 (by rfl) ⟨2536403, by rfl⟩ : syracuseStep 3381871 = 5072807) B5072807
theorem B4509161 : Blo 2003435 4509161 := bstep (se 2 (by rfl) ⟨1690935, by rfl⟩ : syracuseStep 4509161 = 3381871) B3381871
theorem B3006107 : Blo 2003435 3006107 := bstep (se 1 (by rfl) ⟨2254580, by rfl⟩ : syracuseStep 3006107 = 4509161) B4509161
theorem B2004071 : Blo 2003435 2004071 := bstep (se 1 (by rfl) ⟨1503053, by rfl⟩ : syracuseStep 2004071 = 3006107) B3006107
theorem B2254585 : Blo 2003435 2254585 := bbase (se 2 (by rfl) ⟨845469, by rfl⟩ : syracuseStep 2254585 = 1690939) (by norm_num)
theorem B3006113 : Blo 2003435 3006113 := bstep (se 2 (by rfl) ⟨1127292, by rfl⟩ : syracuseStep 3006113 = 2254585) B2254585
theorem B2004075 : Blo 2003435 2004075 := bstep (se 1 (by rfl) ⟨1503056, by rfl⟩ : syracuseStep 2004075 = 3006113) B3006113
theorem B3210149 : Blo 2003435 3210149 := bbase (se 4 (by rfl) ⟨300951, by rfl⟩ : syracuseStep 3210149 = 601903) (by norm_num)
theorem B8560397 : Blo 2003435 8560397 := bstep (se 3 (by rfl) ⟨1605074, by rfl⟩ : syracuseStep 8560397 = 3210149) B3210149
theorem B5706931 : Blo 2003435 5706931 := bstep (se 1 (by rfl) ⟨4280198, by rfl⟩ : syracuseStep 5706931 = 8560397) B8560397
theorem B7609241 : Blo 2003435 7609241 := bstep (se 2 (by rfl) ⟨2853465, by rfl⟩ : syracuseStep 7609241 = 5706931) B5706931
theorem B5072827 : Blo 2003435 5072827 := bstep (se 1 (by rfl) ⟨3804620, by rfl⟩ : syracuseStep 5072827 = 7609241) B7609241
theorem B6763769 : Blo 2003435 6763769 := bstep (se 2 (by rfl) ⟨2536413, by rfl⟩ : syracuseStep 6763769 = 5072827) B5072827
theorem B4509179 : Blo 2003435 4509179 := bstep (se 1 (by rfl) ⟨3381884, by rfl⟩ : syracuseStep 4509179 = 6763769) B6763769
theorem B3006119 : Blo 2003435 3006119 := bstep (se 1 (by rfl) ⟨2254589, by rfl⟩ : syracuseStep 3006119 = 4509179) B4509179
theorem B2004079 : Blo 2003435 2004079 := bstep (se 1 (by rfl) ⟨1503059, by rfl⟩ : syracuseStep 2004079 = 3006119) B3006119
theorem B3006125 : Blo 2003435 3006125 := bbase (se 3 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 3006125 = 1127297) (by norm_num)
theorem B2004083 : Blo 2003435 2004083 := bstep (se 1 (by rfl) ⟨1503062, by rfl⟩ : syracuseStep 2004083 = 3006125) B3006125
theorem B4509197 : Blo 2003435 4509197 := bbase (se 3 (by rfl) ⟨845474, by rfl⟩ : syracuseStep 4509197 = 1690949) (by norm_num)
theorem B3006131 : Blo 2003435 3006131 := bstep (se 1 (by rfl) ⟨2254598, by rfl⟩ : syracuseStep 3006131 = 4509197) B4509197
theorem B2004087 : Blo 2003435 2004087 := bstep (se 1 (by rfl) ⟨1503065, by rfl⟩ : syracuseStep 2004087 = 3006131) B3006131
theorem B2536429 : Blo 2003435 2536429 := bbase (se 3 (by rfl) ⟨475580, by rfl⟩ : syracuseStep 2536429 = 951161) (by norm_num)
theorem B3381905 : Blo 2003435 3381905 := bstep (se 2 (by rfl) ⟨1268214, by rfl⟩ : syracuseStep 3381905 = 2536429) B2536429
theorem B2254603 : Blo 2003435 2254603 := bstep (se 1 (by rfl) ⟨1690952, by rfl⟩ : syracuseStep 2254603 = 3381905) B3381905
theorem B3006137 : Blo 2003435 3006137 := bstep (se 2 (by rfl) ⟨1127301, by rfl⟩ : syracuseStep 3006137 = 2254603) B2254603
theorem B2004091 : Blo 2003435 2004091 := bstep (se 1 (by rfl) ⟨1503068, by rfl⟩ : syracuseStep 2004091 = 3006137) B3006137
theorem B16251509 : Blo 2003435 16251509 := bbase (se 5 (by rfl) ⟨761789, by rfl⟩ : syracuseStep 16251509 = 1523579) (by norm_num)
theorem B10834339 : Blo 2003435 10834339 := bstep (se 1 (by rfl) ⟨8125754, by rfl⟩ : syracuseStep 10834339 = 16251509) B16251509
theorem B14445785 : Blo 2003435 14445785 := bstep (se 2 (by rfl) ⟨5417169, by rfl⟩ : syracuseStep 14445785 = 10834339) B10834339
theorem B9630523 : Blo 2003435 9630523 := bstep (se 1 (by rfl) ⟨7222892, by rfl⟩ : syracuseStep 9630523 = 14445785) B14445785
theorem B12840697 : Blo 2003435 12840697 := bstep (se 2 (by rfl) ⟨4815261, by rfl⟩ : syracuseStep 12840697 = 9630523) B9630523
theorem B17120929 : Blo 2003435 17120929 := bstep (se 2 (by rfl) ⟨6420348, by rfl⟩ : syracuseStep 17120929 = 12840697) B12840697
theorem B22827905 : Blo 2003435 22827905 := bstep (se 2 (by rfl) ⟨8560464, by rfl⟩ : syracuseStep 22827905 = 17120929) B17120929
theorem B15218603 : Blo 2003435 15218603 := bstep (se 1 (by rfl) ⟨11413952, by rfl⟩ : syracuseStep 15218603 = 22827905) B22827905
theorem B10145735 : Blo 2003435 10145735 := bstep (se 1 (by rfl) ⟨7609301, by rfl⟩ : syracuseStep 10145735 = 15218603) B15218603
theorem B6763823 : Blo 2003435 6763823 := bstep (se 1 (by rfl) ⟨5072867, by rfl⟩ : syracuseStep 6763823 = 10145735) B10145735
theorem B4509215 : Blo 2003435 4509215 := bstep (se 1 (by rfl) ⟨3381911, by rfl⟩ : syracuseStep 4509215 = 6763823) B6763823
theorem B3006143 : Blo 2003435 3006143 := bstep (se 1 (by rfl) ⟨2254607, by rfl⟩ : syracuseStep 3006143 = 4509215) B4509215
theorem B2004095 : Blo 2003435 2004095 := bstep (se 1 (by rfl) ⟨1503071, by rfl⟩ : syracuseStep 2004095 = 3006143) B3006143
theorem B3006149 : Blo 2003435 3006149 := bbase (se 4 (by rfl) ⟨281826, by rfl⟩ : syracuseStep 3006149 = 563653) (by norm_num)
theorem B2004099 : Blo 2003435 2004099 := bstep (se 1 (by rfl) ⟨1503074, by rfl⟩ : syracuseStep 2004099 = 3006149) B3006149
theorem B3381925 : Blo 2003435 3381925 := bbase (se 4 (by rfl) ⟨317055, by rfl⟩ : syracuseStep 3381925 = 634111) (by norm_num)
theorem B4509233 : Blo 2003435 4509233 := bstep (se 2 (by rfl) ⟨1690962, by rfl⟩ : syracuseStep 4509233 = 3381925) B3381925
theorem B3006155 : Blo 2003435 3006155 := bstep (se 1 (by rfl) ⟨2254616, by rfl⟩ : syracuseStep 3006155 = 4509233) B4509233
theorem B2004103 : Blo 2003435 2004103 := bstep (se 1 (by rfl) ⟨1503077, by rfl⟩ : syracuseStep 2004103 = 3006155) B3006155
theorem B2254621 : Blo 2003435 2254621 := bbase (se 3 (by rfl) ⟨422741, by rfl⟩ : syracuseStep 2254621 = 845483) (by norm_num)
theorem B3006161 : Blo 2003435 3006161 := bstep (se 2 (by rfl) ⟨1127310, by rfl⟩ : syracuseStep 3006161 = 2254621) B2254621
theorem B2004107 : Blo 2003435 2004107 := bstep (se 1 (by rfl) ⟨1503080, by rfl⟩ : syracuseStep 2004107 = 3006161) B3006161
theorem B6763877 : Blo 2003435 6763877 := bbase (se 4 (by rfl) ⟨634113, by rfl⟩ : syracuseStep 6763877 = 1268227) (by norm_num)
theorem B4509251 : Blo 2003435 4509251 := bstep (se 1 (by rfl) ⟨3381938, by rfl⟩ : syracuseStep 4509251 = 6763877) B6763877
theorem B3006167 : Blo 2003435 3006167 := bstep (se 1 (by rfl) ⟨2254625, by rfl⟩ : syracuseStep 3006167 = 4509251) B4509251
theorem B2004111 : Blo 2003435 2004111 := bstep (se 1 (by rfl) ⟨1503083, by rfl⟩ : syracuseStep 2004111 = 3006167) B3006167
theorem B3006173 : Blo 2003435 3006173 := bbase (se 3 (by rfl) ⟨563657, by rfl⟩ : syracuseStep 3006173 = 1127315) (by norm_num)
theorem B2004115 : Blo 2003435 2004115 := bstep (se 1 (by rfl) ⟨1503086, by rfl⟩ : syracuseStep 2004115 = 3006173) B3006173
theorem B4509269 : Blo 2003435 4509269 := bbase (se 8 (by rfl) ⟨26421, by rfl⟩ : syracuseStep 4509269 = 52843) (by norm_num)
theorem B3006179 : Blo 2003435 3006179 := bstep (se 1 (by rfl) ⟨2254634, by rfl⟩ : syracuseStep 3006179 = 4509269) B4509269
theorem B2004119 : Blo 2003435 2004119 := bstep (se 1 (by rfl) ⟨1503089, by rfl⟩ : syracuseStep 2004119 = 3006179) B3006179
theorem B4280293 : Blo 2003435 4280293 := bbase (se 4 (by rfl) ⟨401277, by rfl⟩ : syracuseStep 4280293 = 802555) (by norm_num)
theorem B5707057 : Blo 2003435 5707057 := bstep (se 2 (by rfl) ⟨2140146, by rfl⟩ : syracuseStep 5707057 = 4280293) B4280293
theorem B7609409 : Blo 2003435 7609409 := bstep (se 2 (by rfl) ⟨2853528, by rfl⟩ : syracuseStep 7609409 = 5707057) B5707057
theorem B5072939 : Blo 2003435 5072939 := bstep (se 1 (by rfl) ⟨3804704, by rfl⟩ : syracuseStep 5072939 = 7609409) B7609409
theorem B3381959 : Blo 2003435 3381959 := bstep (se 1 (by rfl) ⟨2536469, by rfl⟩ : syracuseStep 3381959 = 5072939) B5072939
theorem B2254639 : Blo 2003435 2254639 := bstep (se 1 (by rfl) ⟨1690979, by rfl⟩ : syracuseStep 2254639 = 3381959) B3381959
theorem B3006185 : Blo 2003435 3006185 := bstep (se 2 (by rfl) ⟨1127319, by rfl⟩ : syracuseStep 3006185 = 2254639) B2254639
theorem B2004123 : Blo 2003435 2004123 := bstep (se 1 (by rfl) ⟨1503092, by rfl⟩ : syracuseStep 2004123 = 3006185) B3006185
theorem B9630677 : Blo 2003435 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B25681805 : Blo 2003435 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B17121203 : Blo 2003435 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B11414135 : Blo 2003435 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B7609423 : Blo 2003435 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B10145897 : Blo 2003435 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B6763931 : Blo 2003435 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B4509287 : Blo 2003435 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B3006191 : Blo 2003435 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B2004127 : Blo 2003435 2004127 := bstep (se 1 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 2004127 = 3006191) B3006191
theorem B3006197 : Blo 2003435 3006197 := bbase (se 5 (by rfl) ⟨140915, by rfl⟩ : syracuseStep 3006197 = 281831) (by norm_num)
theorem B2004131 : Blo 2003435 2004131 := bstep (se 1 (by rfl) ⟨1503098, by rfl⟩ : syracuseStep 2004131 = 3006197) B3006197
theorem B6261877 : Blo 2003435 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B8349169 : Blo 2003435 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B11132225 : Blo 2003435 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B7421483 : Blo 2003435 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B4947655 : Blo 2003435 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B6596873 : Blo 2003435 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B4397915 : Blo 2003435 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B11727773 : Blo 2003435 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B7818515 : Blo 2003435 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B5212343 : Blo 2003435 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B3474895 : Blo 2003435 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B4633193 : Blo 2003435 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B3088795 : Blo 2003435 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B4118393 : Blo 2003435 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2745595 : Blo 2003435 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B3660793 : Blo 2003435 3660793 := bstep (se 2 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 3660793 = 2745595) B2745595
theorem B19524229 : Blo 2003435 19524229 := bstep (se 4 (by rfl) ⟨1830396, by rfl⟩ : syracuseStep 19524229 = 3660793) B3660793
theorem B104129221 : Blo 2003435 104129221 := bstep (se 4 (by rfl) ⟨9762114, by rfl⟩ : syracuseStep 104129221 = 19524229) B19524229
theorem B138838961 : Blo 2003435 138838961 := bstep (se 2 (by rfl) ⟨52064610, by rfl⟩ : syracuseStep 138838961 = 104129221) B104129221
theorem B92559307 : Blo 2003435 92559307 := bstep (se 1 (by rfl) ⟨69419480, by rfl⟩ : syracuseStep 92559307 = 138838961) B138838961
theorem B123412409 : Blo 2003435 123412409 := bstep (se 2 (by rfl) ⟨46279653, by rfl⟩ : syracuseStep 123412409 = 92559307) B92559307
theorem B82274939 : Blo 2003435 82274939 := bstep (se 1 (by rfl) ⟨61706204, by rfl⟩ : syracuseStep 82274939 = 123412409) B123412409
theorem B54849959 : Blo 2003435 54849959 := bstep (se 1 (by rfl) ⟨41137469, by rfl⟩ : syracuseStep 54849959 = 82274939) B82274939
theorem B36566639 : Blo 2003435 36566639 := bstep (se 1 (by rfl) ⟨27424979, by rfl⟩ : syracuseStep 36566639 = 54849959) B54849959
theorem B24377759 : Blo 2003435 24377759 := bstep (se 1 (by rfl) ⟨18283319, by rfl⟩ : syracuseStep 24377759 = 36566639) B36566639
theorem B16251839 : Blo 2003435 16251839 := bstep (se 1 (by rfl) ⟨12188879, by rfl⟩ : syracuseStep 16251839 = 24377759) B24377759
theorem B10834559 : Blo 2003435 10834559 := bstep (se 1 (by rfl) ⟨8125919, by rfl⟩ : syracuseStep 10834559 = 16251839) B16251839
theorem B7223039 : Blo 2003435 7223039 := bstep (se 1 (by rfl) ⟨5417279, by rfl⟩ : syracuseStep 7223039 = 10834559) B10834559
theorem B4815359 : Blo 2003435 4815359 := bstep (se 1 (by rfl) ⟨3611519, by rfl⟩ : syracuseStep 4815359 = 7223039) B7223039
theorem B3210239 : Blo 2003435 3210239 := bstep (se 1 (by rfl) ⟨2407679, by rfl⟩ : syracuseStep 3210239 = 4815359) B4815359
theorem B8560637 : Blo 2003435 8560637 := bstep (se 3 (by rfl) ⟨1605119, by rfl⟩ : syracuseStep 8560637 = 3210239) B3210239
theorem B5707091 : Blo 2003435 5707091 := bstep (se 1 (by rfl) ⟨4280318, by rfl⟩ : syracuseStep 5707091 = 8560637) B8560637
theorem B3804727 : Blo 2003435 3804727 := bstep (se 1 (by rfl) ⟨2853545, by rfl⟩ : syracuseStep 3804727 = 5707091) B5707091
theorem B5072969 : Blo 2003435 5072969 := bstep (se 2 (by rfl) ⟨1902363, by rfl⟩ : syracuseStep 5072969 = 3804727) B3804727
theorem B3381979 : Blo 2003435 3381979 := bstep (se 1 (by rfl) ⟨2536484, by rfl⟩ : syracuseStep 3381979 = 5072969) B5072969
theorem B4509305 : Blo 2003435 4509305 := bstep (se 2 (by rfl) ⟨1690989, by rfl⟩ : syracuseStep 4509305 = 3381979) B3381979
theorem B3006203 : Blo 2003435 3006203 := bstep (se 1 (by rfl) ⟨2254652, by rfl⟩ : syracuseStep 3006203 = 4509305) B4509305
theorem B2004135 : Blo 2003435 2004135 := bstep (se 1 (by rfl) ⟨1503101, by rfl⟩ : syracuseStep 2004135 = 3006203) B3006203
theorem B2254657 : Blo 2003435 2254657 := bbase (se 2 (by rfl) ⟨845496, by rfl⟩ : syracuseStep 2254657 = 1690993) (by norm_num)
theorem B3006209 : Blo 2003435 3006209 := bstep (se 2 (by rfl) ⟨1127328, by rfl⟩ : syracuseStep 3006209 = 2254657) B2254657
theorem B2004139 : Blo 2003435 2004139 := bstep (se 1 (by rfl) ⟨1503104, by rfl⟩ : syracuseStep 2004139 = 3006209) B3006209
theorem B5072989 : Blo 2003435 5072989 := bbase (se 3 (by rfl) ⟨951185, by rfl⟩ : syracuseStep 5072989 = 1902371) (by norm_num)
theorem B6763985 : Blo 2003435 6763985 := bstep (se 2 (by rfl) ⟨2536494, by rfl⟩ : syracuseStep 6763985 = 5072989) B5072989
theorem B4509323 : Blo 2003435 4509323 := bstep (se 1 (by rfl) ⟨3381992, by rfl⟩ : syracuseStep 4509323 = 6763985) B6763985
theorem B3006215 : Blo 2003435 3006215 := bstep (se 1 (by rfl) ⟨2254661, by rfl⟩ : syracuseStep 3006215 = 4509323) B4509323
theorem B2004143 : Blo 2003435 2004143 := bstep (se 1 (by rfl) ⟨1503107, by rfl⟩ : syracuseStep 2004143 = 3006215) B3006215
theorem B3006221 : Blo 2003435 3006221 := bbase (se 3 (by rfl) ⟨563666, by rfl⟩ : syracuseStep 3006221 = 1127333) (by norm_num)
theorem B2004147 : Blo 2003435 2004147 := bstep (se 1 (by rfl) ⟨1503110, by rfl⟩ : syracuseStep 2004147 = 3006221) B3006221
theorem B4509341 : Blo 2003435 4509341 := bbase (se 3 (by rfl) ⟨845501, by rfl⟩ : syracuseStep 4509341 = 1691003) (by norm_num)
theorem B3006227 : Blo 2003435 3006227 := bstep (se 1 (by rfl) ⟨2254670, by rfl⟩ : syracuseStep 3006227 = 4509341) B4509341
theorem B2004151 : Blo 2003435 2004151 := bstep (se 1 (by rfl) ⟨1503113, by rfl⟩ : syracuseStep 2004151 = 3006227) B3006227
theorem B3382013 : Blo 2003435 3382013 := bbase (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) (by norm_num)
theorem B2254675 : Blo 2003435 2254675 := bstep (se 1 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 2254675 = 3382013) B3382013
theorem B3006233 : Blo 2003435 3006233 := bstep (se 2 (by rfl) ⟨1127337, by rfl⟩ : syracuseStep 3006233 = 2254675) B2254675
theorem B2004155 : Blo 2003435 2004155 := bstep (se 1 (by rfl) ⟨1503116, by rfl⟩ : syracuseStep 2004155 = 3006233) B3006233
theorem B3210277 : Blo 2003435 3210277 := bbase (se 4 (by rfl) ⟨300963, by rfl⟩ : syracuseStep 3210277 = 601927) (by norm_num)
theorem B4280369 : Blo 2003435 4280369 := bstep (se 2 (by rfl) ⟨1605138, by rfl⟩ : syracuseStep 4280369 = 3210277) B3210277
theorem B11414317 : Blo 2003435 11414317 := bstep (se 3 (by rfl) ⟨2140184, by rfl⟩ : syracuseStep 11414317 = 4280369) B4280369
theorem B15219089 : Blo 2003435 15219089 := bstep (se 2 (by rfl) ⟨5707158, by rfl⟩ : syracuseStep 15219089 = 11414317) B11414317
theorem B10146059 : Blo 2003435 10146059 := bstep (se 1 (by rfl) ⟨7609544, by rfl⟩ : syracuseStep 10146059 = 15219089) B15219089
theorem B6764039 : Blo 2003435 6764039 := bstep (se 1 (by rfl) ⟨5073029, by rfl⟩ : syracuseStep 6764039 = 10146059) B10146059
theorem B4509359 : Blo 2003435 4509359 := bstep (se 1 (by rfl) ⟨3382019, by rfl⟩ : syracuseStep 4509359 = 6764039) B6764039
theorem B3006239 : Blo 2003435 3006239 := bstep (se 1 (by rfl) ⟨2254679, by rfl⟩ : syracuseStep 3006239 = 4509359) B4509359
theorem B2004159 : Blo 2003435 2004159 := bstep (se 1 (by rfl) ⟨1503119, by rfl⟩ : syracuseStep 2004159 = 3006239) B3006239
theorem B3006245 : Blo 2003435 3006245 := bbase (se 4 (by rfl) ⟨281835, by rfl⟩ : syracuseStep 3006245 = 563671) (by norm_num)
theorem B2004163 : Blo 2003435 2004163 := bstep (se 1 (by rfl) ⟨1503122, by rfl⟩ : syracuseStep 2004163 = 3006245) B3006245
theorem B2536525 : Blo 2003435 2536525 := bbase (se 3 (by rfl) ⟨475598, by rfl⟩ : syracuseStep 2536525 = 951197) (by norm_num)
theorem B3382033 : Blo 2003435 3382033 := bstep (se 2 (by rfl) ⟨1268262, by rfl⟩ : syracuseStep 3382033 = 2536525) B2536525
theorem B4509377 : Blo 2003435 4509377 := bstep (se 2 (by rfl) ⟨1691016, by rfl⟩ : syracuseStep 4509377 = 3382033) B3382033
theorem B3006251 : Blo 2003435 3006251 := bstep (se 1 (by rfl) ⟨2254688, by rfl⟩ : syracuseStep 3006251 = 4509377) B4509377
theorem B2004167 : Blo 2003435 2004167 := bstep (se 1 (by rfl) ⟨1503125, by rfl⟩ : syracuseStep 2004167 = 3006251) B3006251
theorem B2254693 : Blo 2003435 2254693 := bbase (se 4 (by rfl) ⟨211377, by rfl⟩ : syracuseStep 2254693 = 422755) (by norm_num)
theorem B3006257 : Blo 2003435 3006257 := bstep (se 2 (by rfl) ⟨1127346, by rfl⟩ : syracuseStep 3006257 = 2254693) B2254693
theorem B2004171 : Blo 2003435 2004171 := bstep (se 1 (by rfl) ⟨1503128, by rfl⟩ : syracuseStep 2004171 = 3006257) B3006257
theorem B5707205 : Blo 2003435 5707205 := bbase (se 4 (by rfl) ⟨535050, by rfl⟩ : syracuseStep 5707205 = 1070101) (by norm_num)
theorem B3804803 : Blo 2003435 3804803 := bstep (se 1 (by rfl) ⟨2853602, by rfl⟩ : syracuseStep 3804803 = 5707205) B5707205
theorem B2536535 : Blo 2003435 2536535 := bstep (se 1 (by rfl) ⟨1902401, by rfl⟩ : syracuseStep 2536535 = 3804803) B3804803
theorem B6764093 : Blo 2003435 6764093 := bstep (se 3 (by rfl) ⟨1268267, by rfl⟩ : syracuseStep 6764093 = 2536535) B2536535
theorem B4509395 : Blo 2003435 4509395 := bstep (se 1 (by rfl) ⟨3382046, by rfl⟩ : syracuseStep 4509395 = 6764093) B6764093
theorem B3006263 : Blo 2003435 3006263 := bstep (se 1 (by rfl) ⟨2254697, by rfl⟩ : syracuseStep 3006263 = 4509395) B4509395
theorem B2004175 : Blo 2003435 2004175 := bstep (se 1 (by rfl) ⟨1503131, by rfl⟩ : syracuseStep 2004175 = 3006263) B3006263
theorem B3006269 : Blo 2003435 3006269 := bbase (se 3 (by rfl) ⟨563675, by rfl⟩ : syracuseStep 3006269 = 1127351) (by norm_num)
theorem B2004179 : Blo 2003435 2004179 := bstep (se 1 (by rfl) ⟨1503134, by rfl⟩ : syracuseStep 2004179 = 3006269) B3006269
theorem B4509413 : Blo 2003435 4509413 := bbase (se 4 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 4509413 = 845515) (by norm_num)
theorem B3006275 : Blo 2003435 3006275 := bstep (se 1 (by rfl) ⟨2254706, by rfl⟩ : syracuseStep 3006275 = 4509413) B4509413
theorem B2004183 : Blo 2003435 2004183 := bstep (se 1 (by rfl) ⟨1503137, by rfl⟩ : syracuseStep 2004183 = 3006275) B3006275
theorem B5073101 : Blo 2003435 5073101 := bbase (se 3 (by rfl) ⟨951206, by rfl⟩ : syracuseStep 5073101 = 1902413) (by norm_num)
theorem B3382067 : Blo 2003435 3382067 := bstep (se 1 (by rfl) ⟨2536550, by rfl⟩ : syracuseStep 3382067 = 5073101) B5073101
theorem B2254711 : Blo 2003435 2254711 := bstep (se 1 (by rfl) ⟨1691033, by rfl⟩ : syracuseStep 2254711 = 3382067) B3382067
theorem B3006281 : Blo 2003435 3006281 := bstep (se 2 (by rfl) ⟨1127355, by rfl⟩ : syracuseStep 3006281 = 2254711) B2254711
theorem B2004187 : Blo 2003435 2004187 := bstep (se 1 (by rfl) ⟨1503140, by rfl⟩ : syracuseStep 2004187 = 3006281) B3006281
theorem B3611621 : Blo 2003435 3611621 := bbase (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) (by norm_num)
theorem B2407747 : Blo 2003435 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B3210329 : Blo 2003435 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B2140219 : Blo 2003435 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B2853625 : Blo 2003435 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B3804833 : Blo 2003435 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B10146221 : Blo 2003435 10146221 := bstep (se 3 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 10146221 = 3804833) B3804833
theorem B6764147 : Blo 2003435 6764147 := bstep (se 1 (by rfl) ⟨5073110, by rfl⟩ : syracuseStep 6764147 = 10146221) B10146221
theorem B4509431 : Blo 2003435 4509431 := bstep (se 1 (by rfl) ⟨3382073, by rfl⟩ : syracuseStep 4509431 = 6764147) B6764147
theorem B3006287 : Blo 2003435 3006287 := bstep (se 1 (by rfl) ⟨2254715, by rfl⟩ : syracuseStep 3006287 = 4509431) B4509431
theorem B2004191 : Blo 2003435 2004191 := bstep (se 1 (by rfl) ⟨1503143, by rfl⟩ : syracuseStep 2004191 = 3006287) B3006287
theorem B3006293 : Blo 2003435 3006293 := bbase (se 9 (by rfl) ⟨8807, by rfl⟩ : syracuseStep 3006293 = 17615) (by norm_num)
theorem B2004195 : Blo 2003435 2004195 := bstep (se 1 (by rfl) ⟨1503146, by rfl⟩ : syracuseStep 2004195 = 3006293) B3006293
theorem B7223269 : Blo 2003435 7223269 := bbase (se 4 (by rfl) ⟨677181, by rfl⟩ : syracuseStep 7223269 = 1354363) (by norm_num)
theorem B9631025 : Blo 2003435 9631025 := bstep (se 2 (by rfl) ⟨3611634, by rfl⟩ : syracuseStep 9631025 = 7223269) B7223269
theorem B6420683 : Blo 2003435 6420683 := bstep (se 1 (by rfl) ⟨4815512, by rfl⟩ : syracuseStep 6420683 = 9631025) B9631025
theorem B4280455 : Blo 2003435 4280455 := bstep (se 1 (by rfl) ⟨3210341, by rfl⟩ : syracuseStep 4280455 = 6420683) B6420683
theorem B5707273 : Blo 2003435 5707273 := bstep (se 2 (by rfl) ⟨2140227, by rfl⟩ : syracuseStep 5707273 = 4280455) B4280455
theorem B7609697 : Blo 2003435 7609697 := bstep (se 2 (by rfl) ⟨2853636, by rfl⟩ : syracuseStep 7609697 = 5707273) B5707273
theorem B5073131 : Blo 2003435 5073131 := bstep (se 1 (by rfl) ⟨3804848, by rfl⟩ : syracuseStep 5073131 = 7609697) B7609697
theorem B3382087 : Blo 2003435 3382087 := bstep (se 1 (by rfl) ⟨2536565, by rfl⟩ : syracuseStep 3382087 = 5073131) B5073131
theorem B4509449 : Blo 2003435 4509449 := bstep (se 2 (by rfl) ⟨1691043, by rfl⟩ : syracuseStep 4509449 = 3382087) B3382087
theorem B3006299 : Blo 2003435 3006299 := bstep (se 1 (by rfl) ⟨2254724, by rfl⟩ : syracuseStep 3006299 = 4509449) B4509449
theorem B2004199 : Blo 2003435 2004199 := bstep (se 1 (by rfl) ⟨1503149, by rfl⟩ : syracuseStep 2004199 = 3006299) B3006299
theorem B2254729 : Blo 2003435 2254729 := bbase (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) (by norm_num)
theorem B3006305 : Blo 2003435 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B2004203 : Blo 2003435 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B26033237 : Blo 2003435 26033237 := bbase (se 8 (by rfl) ⟨152538, by rfl⟩ : syracuseStep 26033237 = 305077) (by norm_num)
theorem B17355491 : Blo 2003435 17355491 := bstep (se 1 (by rfl) ⟨13016618, by rfl⟩ : syracuseStep 17355491 = 26033237) B26033237
theorem B11570327 : Blo 2003435 11570327 := bstep (se 1 (by rfl) ⟨8677745, by rfl⟩ : syracuseStep 11570327 = 17355491) B17355491
theorem B7713551 : Blo 2003435 7713551 := bstep (se 1 (by rfl) ⟨5785163, by rfl⟩ : syracuseStep 7713551 = 11570327) B11570327
theorem B5142367 : Blo 2003435 5142367 := bstep (se 1 (by rfl) ⟨3856775, by rfl⟩ : syracuseStep 5142367 = 7713551) B7713551
theorem B6856489 : Blo 2003435 6856489 := bstep (se 2 (by rfl) ⟨2571183, by rfl⟩ : syracuseStep 6856489 = 5142367) B5142367
theorem B9141985 : Blo 2003435 9141985 := bstep (se 2 (by rfl) ⟨3428244, by rfl⟩ : syracuseStep 9141985 = 6856489) B6856489
theorem B12189313 : Blo 2003435 12189313 := bstep (se 2 (by rfl) ⟨4570992, by rfl⟩ : syracuseStep 12189313 = 9141985) B9141985
theorem B16252417 : Blo 2003435 16252417 := bstep (se 2 (by rfl) ⟨6094656, by rfl⟩ : syracuseStep 16252417 = 12189313) B12189313
theorem B86679557 : Blo 2003435 86679557 := bstep (se 4 (by rfl) ⟨8126208, by rfl⟩ : syracuseStep 86679557 = 16252417) B16252417
theorem B57786371 : Blo 2003435 57786371 := bstep (se 1 (by rfl) ⟨43339778, by rfl⟩ : syracuseStep 57786371 = 86679557) B86679557
theorem B38524247 : Blo 2003435 38524247 := bstep (se 1 (by rfl) ⟨28893185, by rfl⟩ : syracuseStep 38524247 = 57786371) B57786371
theorem B25682831 : Blo 2003435 25682831 := bstep (se 1 (by rfl) ⟨19262123, by rfl⟩ : syracuseStep 25682831 = 38524247) B38524247
theorem B17121887 : Blo 2003435 17121887 := bstep (se 1 (by rfl) ⟨12841415, by rfl⟩ : syracuseStep 17121887 = 25682831) B25682831
theorem B11414591 : Blo 2003435 11414591 := bstep (se 1 (by rfl) ⟨8560943, by rfl⟩ : syracuseStep 11414591 = 17121887) B17121887
theorem B7609727 : Blo 2003435 7609727 := bstep (se 1 (by rfl) ⟨5707295, by rfl⟩ : syracuseStep 7609727 = 11414591) B11414591
theorem B5073151 : Blo 2003435 5073151 := bstep (se 1 (by rfl) ⟨3804863, by rfl⟩ : syracuseStep 5073151 = 7609727) B7609727
theorem B6764201 : Blo 2003435 6764201 := bstep (se 2 (by rfl) ⟨2536575, by rfl⟩ : syracuseStep 6764201 = 5073151) B5073151
theorem B4509467 : Blo 2003435 4509467 := bstep (se 1 (by rfl) ⟨3382100, by rfl⟩ : syracuseStep 4509467 = 6764201) B6764201
theorem B3006311 : Blo 2003435 3006311 := bstep (se 1 (by rfl) ⟨2254733, by rfl⟩ : syracuseStep 3006311 = 4509467) B4509467
theorem B2004207 : Blo 2003435 2004207 := bstep (se 1 (by rfl) ⟨1503155, by rfl⟩ : syracuseStep 2004207 = 3006311) B3006311
theorem B3006317 : Blo 2003435 3006317 := bbase (se 3 (by rfl) ⟨563684, by rfl⟩ : syracuseStep 3006317 = 1127369) (by norm_num)
theorem B2004211 : Blo 2003435 2004211 := bstep (se 1 (by rfl) ⟨1503158, by rfl⟩ : syracuseStep 2004211 = 3006317) B3006317
theorem B4509485 : Blo 2003435 4509485 := bbase (se 3 (by rfl) ⟨845528, by rfl⟩ : syracuseStep 4509485 = 1691057) (by norm_num)
theorem B3006323 : Blo 2003435 3006323 := bstep (se 1 (by rfl) ⟨2254742, by rfl⟩ : syracuseStep 3006323 = 4509485) B4509485
theorem B2004215 : Blo 2003435 2004215 := bstep (se 1 (by rfl) ⟨1503161, by rfl⟩ : syracuseStep 2004215 = 3006323) B3006323
theorem B8560997 : Blo 2003435 8560997 := bbase (se 4 (by rfl) ⟨802593, by rfl⟩ : syracuseStep 8560997 = 1605187) (by norm_num)
theorem B5707331 : Blo 2003435 5707331 := bstep (se 1 (by rfl) ⟨4280498, by rfl⟩ : syracuseStep 5707331 = 8560997) B8560997
theorem B3804887 : Blo 2003435 3804887 := bstep (se 1 (by rfl) ⟨2853665, by rfl⟩ : syracuseStep 3804887 = 5707331) B5707331
theorem B2536591 : Blo 2003435 2536591 := bstep (se 1 (by rfl) ⟨1902443, by rfl⟩ : syracuseStep 2536591 = 3804887) B3804887
theorem B3382121 : Blo 2003435 3382121 := bstep (se 2 (by rfl) ⟨1268295, by rfl⟩ : syracuseStep 3382121 = 2536591) B2536591
theorem B2254747 : Blo 2003435 2254747 := bstep (se 1 (by rfl) ⟨1691060, by rfl⟩ : syracuseStep 2254747 = 3382121) B3382121
theorem B3006329 : Blo 2003435 3006329 := bstep (se 2 (by rfl) ⟨1127373, by rfl⟩ : syracuseStep 3006329 = 2254747) B2254747
theorem B2004219 : Blo 2003435 2004219 := bstep (se 1 (by rfl) ⟨1503164, by rfl⟩ : syracuseStep 2004219 = 3006329) B3006329
theorem B3611677 : Blo 2003435 3611677 := bbase (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) (by norm_num)
theorem B4815569 : Blo 2003435 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B12841517 : Blo 2003435 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B34244045 : Blo 2003435 34244045 := bstep (se 3 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 34244045 = 12841517) B12841517
theorem B22829363 : Blo 2003435 22829363 := bstep (se 1 (by rfl) ⟨17122022, by rfl⟩ : syracuseStep 22829363 = 34244045) B34244045
theorem B15219575 : Blo 2003435 15219575 := bstep (se 1 (by rfl) ⟨11414681, by rfl⟩ : syracuseStep 15219575 = 22829363) B22829363
theorem B10146383 : Blo 2003435 10146383 := bstep (se 1 (by rfl) ⟨7609787, by rfl⟩ : syracuseStep 10146383 = 15219575) B15219575
theorem B6764255 : Blo 2003435 6764255 := bstep (se 1 (by rfl) ⟨5073191, by rfl⟩ : syracuseStep 6764255 = 10146383) B10146383
theorem B4509503 : Blo 2003435 4509503 := bstep (se 1 (by rfl) ⟨3382127, by rfl⟩ : syracuseStep 4509503 = 6764255) B6764255
theorem B3006335 : Blo 2003435 3006335 := bstep (se 1 (by rfl) ⟨2254751, by rfl⟩ : syracuseStep 3006335 = 4509503) B4509503
theorem B2004223 : Blo 2003435 2004223 := bstep (se 1 (by rfl) ⟨1503167, by rfl⟩ : syracuseStep 2004223 = 3006335) B3006335
theorem B3006341 : Blo 2003435 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B2004227 : Blo 2003435 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B3382141 : Blo 2003435 3382141 := bbase (se 3 (by rfl) ⟨634151, by rfl⟩ : syracuseStep 3382141 = 1268303) (by norm_num)
theorem B4509521 : Blo 2003435 4509521 := bstep (se 2 (by rfl) ⟨1691070, by rfl⟩ : syracuseStep 4509521 = 3382141) B3382141
theorem B3006347 : Blo 2003435 3006347 := bstep (se 1 (by rfl) ⟨2254760, by rfl⟩ : syracuseStep 3006347 = 4509521) B4509521
theorem B2004231 : Blo 2003435 2004231 := bstep (se 1 (by rfl) ⟨1503173, by rfl⟩ : syracuseStep 2004231 = 3006347) B3006347
theorem B2254765 : Blo 2003435 2254765 := bbase (se 3 (by rfl) ⟨422768, by rfl⟩ : syracuseStep 2254765 = 845537) (by norm_num)
theorem B3006353 : Blo 2003435 3006353 := bstep (se 2 (by rfl) ⟨1127382, by rfl⟩ : syracuseStep 3006353 = 2254765) B2254765
theorem B2004235 : Blo 2003435 2004235 := bstep (se 1 (by rfl) ⟨1503176, by rfl⟩ : syracuseStep 2004235 = 3006353) B3006353
theorem B6764309 : Blo 2003435 6764309 := bbase (se 6 (by rfl) ⟨158538, by rfl⟩ : syracuseStep 6764309 = 317077) (by norm_num)
theorem B4509539 : Blo 2003435 4509539 := bstep (se 1 (by rfl) ⟨3382154, by rfl⟩ : syracuseStep 4509539 = 6764309) B6764309
theorem B3006359 : Blo 2003435 3006359 := bstep (se 1 (by rfl) ⟨2254769, by rfl⟩ : syracuseStep 3006359 = 4509539) B4509539
theorem B2004239 : Blo 2003435 2004239 := bstep (se 1 (by rfl) ⟨1503179, by rfl⟩ : syracuseStep 2004239 = 3006359) B3006359
theorem B3006365 : Blo 2003435 3006365 := bbase (se 3 (by rfl) ⟨563693, by rfl⟩ : syracuseStep 3006365 = 1127387) (by norm_num)
theorem B2004243 : Blo 2003435 2004243 := bstep (se 1 (by rfl) ⟨1503182, by rfl⟩ : syracuseStep 2004243 = 3006365) B3006365
theorem B4509557 : Blo 2003435 4509557 := bbase (se 5 (by rfl) ⟨211385, by rfl⟩ : syracuseStep 4509557 = 422771) (by norm_num)
theorem B3006371 : Blo 2003435 3006371 := bstep (se 1 (by rfl) ⟨2254778, by rfl⟩ : syracuseStep 3006371 = 4509557) B4509557
theorem B2004247 : Blo 2003435 2004247 := bstep (se 1 (by rfl) ⟨1503185, by rfl⟩ : syracuseStep 2004247 = 3006371) B3006371
theorem B19262549 : Blo 2003435 19262549 := bbase (se 8 (by rfl) ⟨112866, by rfl⟩ : syracuseStep 19262549 = 225733) (by norm_num)
theorem B12841699 : Blo 2003435 12841699 := bstep (se 1 (by rfl) ⟨9631274, by rfl⟩ : syracuseStep 12841699 = 19262549) B19262549
theorem B17122265 : Blo 2003435 17122265 := bstep (se 2 (by rfl) ⟨6420849, by rfl⟩ : syracuseStep 17122265 = 12841699) B12841699
theorem B11414843 : Blo 2003435 11414843 := bstep (se 1 (by rfl) ⟨8561132, by rfl⟩ : syracuseStep 11414843 = 17122265) B17122265
theorem B7609895 : Blo 2003435 7609895 := bstep (se 1 (by rfl) ⟨5707421, by rfl⟩ : syracuseStep 7609895 = 11414843) B11414843
theorem B5073263 : Blo 2003435 5073263 := bstep (se 1 (by rfl) ⟨3804947, by rfl⟩ : syracuseStep 5073263 = 7609895) B7609895
theorem B3382175 : Blo 2003435 3382175 := bstep (se 1 (by rfl) ⟨2536631, by rfl⟩ : syracuseStep 3382175 = 5073263) B5073263
theorem B2254783 : Blo 2003435 2254783 := bstep (se 1 (by rfl) ⟨1691087, by rfl⟩ : syracuseStep 2254783 = 3382175) B3382175
theorem B3006377 : Blo 2003435 3006377 := bstep (se 2 (by rfl) ⟨1127391, by rfl⟩ : syracuseStep 3006377 = 2254783) B2254783
theorem B2004251 : Blo 2003435 2004251 := bstep (se 1 (by rfl) ⟨1503188, by rfl⟩ : syracuseStep 2004251 = 3006377) B3006377
theorem B7609909 : Blo 2003435 7609909 := bbase (se 5 (by rfl) ⟨356714, by rfl⟩ : syracuseStep 7609909 = 713429) (by norm_num)
theorem B10146545 : Blo 2003435 10146545 := bstep (se 2 (by rfl) ⟨3804954, by rfl⟩ : syracuseStep 10146545 = 7609909) B7609909
theorem B6764363 : Blo 2003435 6764363 := bstep (se 1 (by rfl) ⟨5073272, by rfl⟩ : syracuseStep 6764363 = 10146545) B10146545
theorem B4509575 : Blo 2003435 4509575 := bstep (se 1 (by rfl) ⟨3382181, by rfl⟩ : syracuseStep 4509575 = 6764363) B6764363
theorem B3006383 : Blo 2003435 3006383 := bstep (se 1 (by rfl) ⟨2254787, by rfl⟩ : syracuseStep 3006383 = 4509575) B4509575
theorem B2004255 : Blo 2003435 2004255 := bstep (se 1 (by rfl) ⟨1503191, by rfl⟩ : syracuseStep 2004255 = 3006383) B3006383
theorem B3006389 : Blo 2003435 3006389 := bbase (se 5 (by rfl) ⟨140924, by rfl⟩ : syracuseStep 3006389 = 281849) (by norm_num)
theorem B2004259 : Blo 2003435 2004259 := bstep (se 1 (by rfl) ⟨1503194, by rfl⟩ : syracuseStep 2004259 = 3006389) B3006389
theorem B5073293 : Blo 2003435 5073293 := bbase (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) (by norm_num)
theorem B3382195 : Blo 2003435 3382195 := bstep (se 1 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 3382195 = 5073293) B5073293
theorem B4509593 : Blo 2003435 4509593 := bstep (se 2 (by rfl) ⟨1691097, by rfl⟩ : syracuseStep 4509593 = 3382195) B3382195
theorem B3006395 : Blo 2003435 3006395 := bstep (se 1 (by rfl) ⟨2254796, by rfl⟩ : syracuseStep 3006395 = 4509593) B4509593
theorem B2004263 : Blo 2003435 2004263 := bstep (se 1 (by rfl) ⟨1503197, by rfl⟩ : syracuseStep 2004263 = 3006395) B3006395
theorem B2254801 : Blo 2003435 2254801 := bbase (se 2 (by rfl) ⟨845550, by rfl⟩ : syracuseStep 2254801 = 1691101) (by norm_num)
theorem B3006401 : Blo 2003435 3006401 := bstep (se 2 (by rfl) ⟨1127400, by rfl⟩ : syracuseStep 3006401 = 2254801) B2254801
theorem B2004267 : Blo 2003435 2004267 := bstep (se 1 (by rfl) ⟨1503200, by rfl⟩ : syracuseStep 2004267 = 3006401) B3006401
theorem B3611765 : Blo 2003435 3611765 := bbase (se 5 (by rfl) ⟨169301, by rfl⟩ : syracuseStep 3611765 = 338603) (by norm_num)
theorem B2407843 : Blo 2003435 2407843 := bstep (se 1 (by rfl) ⟨1805882, by rfl⟩ : syracuseStep 2407843 = 3611765) B3611765
theorem B3210457 : Blo 2003435 3210457 := bstep (se 2 (by rfl) ⟨1203921, by rfl⟩ : syracuseStep 3210457 = 2407843) B2407843
theorem B4280609 : Blo 2003435 4280609 := bstep (se 2 (by rfl) ⟨1605228, by rfl⟩ : syracuseStep 4280609 = 3210457) B3210457
theorem B2853739 : Blo 2003435 2853739 := bstep (se 1 (by rfl) ⟨2140304, by rfl⟩ : syracuseStep 2853739 = 4280609) B4280609
theorem B3804985 : Blo 2003435 3804985 := bstep (se 2 (by rfl) ⟨1426869, by rfl⟩ : syracuseStep 3804985 = 2853739) B2853739
theorem B5073313 : Blo 2003435 5073313 := bstep (se 2 (by rfl) ⟨1902492, by rfl⟩ : syracuseStep 5073313 = 3804985) B3804985
theorem B6764417 : Blo 2003435 6764417 := bstep (se 2 (by rfl) ⟨2536656, by rfl⟩ : syracuseStep 6764417 = 5073313) B5073313
theorem B4509611 : Blo 2003435 4509611 := bstep (se 1 (by rfl) ⟨3382208, by rfl⟩ : syracuseStep 4509611 = 6764417) B6764417
theorem B3006407 : Blo 2003435 3006407 := bstep (se 1 (by rfl) ⟨2254805, by rfl⟩ : syracuseStep 3006407 = 4509611) B4509611
theorem B2004271 : Blo 2003435 2004271 := bstep (se 1 (by rfl) ⟨1503203, by rfl⟩ : syracuseStep 2004271 = 3006407) B3006407
theorem B3006413 : Blo 2003435 3006413 := bbase (se 3 (by rfl) ⟨563702, by rfl⟩ : syracuseStep 3006413 = 1127405) (by norm_num)
theorem B2004275 : Blo 2003435 2004275 := bstep (se 1 (by rfl) ⟨1503206, by rfl⟩ : syracuseStep 2004275 = 3006413) B3006413
theorem B4509629 : Blo 2003435 4509629 := bbase (se 3 (by rfl) ⟨845555, by rfl⟩ : syracuseStep 4509629 = 1691111) (by norm_num)
theorem B3006419 : Blo 2003435 3006419 := bstep (se 1 (by rfl) ⟨2254814, by rfl⟩ : syracuseStep 3006419 = 4509629) B4509629
theorem B2004279 : Blo 2003435 2004279 := bstep (se 1 (by rfl) ⟨1503209, by rfl⟩ : syracuseStep 2004279 = 3006419) B3006419
theorem B3382229 : Blo 2003435 3382229 := bbase (se 7 (by rfl) ⟨39635, by rfl⟩ : syracuseStep 3382229 = 79271) (by norm_num)
theorem B2254819 : Blo 2003435 2254819 := bstep (se 1 (by rfl) ⟨1691114, by rfl⟩ : syracuseStep 2254819 = 3382229) B3382229
theorem B3006425 : Blo 2003435 3006425 := bstep (se 2 (by rfl) ⟨1127409, by rfl⟩ : syracuseStep 3006425 = 2254819) B2254819
theorem B2004283 : Blo 2003435 2004283 := bstep (se 1 (by rfl) ⟨1503212, by rfl⟩ : syracuseStep 2004283 = 3006425) B3006425
theorem B8561285 : Blo 2003435 8561285 := bbase (se 4 (by rfl) ⟨802620, by rfl⟩ : syracuseStep 8561285 = 1605241) (by norm_num)
theorem B5707523 : Blo 2003435 5707523 := bstep (se 1 (by rfl) ⟨4280642, by rfl⟩ : syracuseStep 5707523 = 8561285) B8561285
theorem B15220061 : Blo 2003435 15220061 := bstep (se 3 (by rfl) ⟨2853761, by rfl⟩ : syracuseStep 15220061 = 5707523) B5707523
theorem B10146707 : Blo 2003435 10146707 := bstep (se 1 (by rfl) ⟨7610030, by rfl⟩ : syracuseStep 10146707 = 15220061) B15220061
theorem B6764471 : Blo 2003435 6764471 := bstep (se 1 (by rfl) ⟨5073353, by rfl⟩ : syracuseStep 6764471 = 10146707) B10146707
theorem B4509647 : Blo 2003435 4509647 := bstep (se 1 (by rfl) ⟨3382235, by rfl⟩ : syracuseStep 4509647 = 6764471) B6764471
theorem B3006431 : Blo 2003435 3006431 := bstep (se 1 (by rfl) ⟨2254823, by rfl⟩ : syracuseStep 3006431 = 4509647) B4509647
theorem B2004287 : Blo 2003435 2004287 := bstep (se 1 (by rfl) ⟨1503215, by rfl⟩ : syracuseStep 2004287 = 3006431) B3006431
theorem B3006437 : Blo 2003435 3006437 := bbase (se 4 (by rfl) ⟨281853, by rfl⟩ : syracuseStep 3006437 = 563707) (by norm_num)
theorem B2004291 : Blo 2003435 2004291 := bstep (se 1 (by rfl) ⟨1503218, by rfl⟩ : syracuseStep 2004291 = 3006437) B3006437
theorem B3661085 : Blo 2003435 3661085 := bbase (se 3 (by rfl) ⟨686453, by rfl⟩ : syracuseStep 3661085 = 1372907) (by norm_num)
theorem B9762893 : Blo 2003435 9762893 := bstep (se 3 (by rfl) ⟨1830542, by rfl⟩ : syracuseStep 9762893 = 3661085) B3661085
theorem B104137525 : Blo 2003435 104137525 := bstep (se 5 (by rfl) ⟨4881446, by rfl⟩ : syracuseStep 104137525 = 9762893) B9762893
theorem B138850033 : Blo 2003435 138850033 := bstep (se 2 (by rfl) ⟨52068762, by rfl⟩ : syracuseStep 138850033 = 104137525) B104137525
theorem B185133377 : Blo 2003435 185133377 := bstep (se 2 (by rfl) ⟨69425016, by rfl⟩ : syracuseStep 185133377 = 138850033) B138850033
theorem B123422251 : Blo 2003435 123422251 := bstep (se 1 (by rfl) ⟨92566688, by rfl⟩ : syracuseStep 123422251 = 185133377) B185133377
theorem B164563001 : Blo 2003435 164563001 := bstep (se 2 (by rfl) ⟨61711125, by rfl⟩ : syracuseStep 164563001 = 123422251) B123422251
theorem B109708667 : Blo 2003435 109708667 := bstep (se 1 (by rfl) ⟨82281500, by rfl⟩ : syracuseStep 109708667 = 164563001) B164563001
theorem B73139111 : Blo 2003435 73139111 := bstep (se 1 (by rfl) ⟨54854333, by rfl⟩ : syracuseStep 73139111 = 109708667) B109708667
theorem B48759407 : Blo 2003435 48759407 := bstep (se 1 (by rfl) ⟨36569555, by rfl⟩ : syracuseStep 48759407 = 73139111) B73139111
theorem B32506271 : Blo 2003435 32506271 := bstep (se 1 (by rfl) ⟨24379703, by rfl⟩ : syracuseStep 32506271 = 48759407) B48759407
theorem B21670847 : Blo 2003435 21670847 := bstep (se 1 (by rfl) ⟨16253135, by rfl⟩ : syracuseStep 21670847 = 32506271) B32506271
theorem B14447231 : Blo 2003435 14447231 := bstep (se 1 (by rfl) ⟨10835423, by rfl⟩ : syracuseStep 14447231 = 21670847) B21670847
theorem B9631487 : Blo 2003435 9631487 := bstep (se 1 (by rfl) ⟨7223615, by rfl⟩ : syracuseStep 9631487 = 14447231) B14447231
theorem B6420991 : Blo 2003435 6420991 := bstep (se 1 (by rfl) ⟨4815743, by rfl⟩ : syracuseStep 6420991 = 9631487) B9631487
theorem B8561321 : Blo 2003435 8561321 := bstep (se 2 (by rfl) ⟨3210495, by rfl⟩ : syracuseStep 8561321 = 6420991) B6420991
theorem B5707547 : Blo 2003435 5707547 := bstep (se 1 (by rfl) ⟨4280660, by rfl⟩ : syracuseStep 5707547 = 8561321) B8561321
theorem B3805031 : Blo 2003435 3805031 := bstep (se 1 (by rfl) ⟨2853773, by rfl⟩ : syracuseStep 3805031 = 5707547) B5707547
theorem B2536687 : Blo 2003435 2536687 := bstep (se 1 (by rfl) ⟨1902515, by rfl⟩ : syracuseStep 2536687 = 3805031) B3805031
theorem B3382249 : Blo 2003435 3382249 := bstep (se 2 (by rfl) ⟨1268343, by rfl⟩ : syracuseStep 3382249 = 2536687) B2536687
theorem B4509665 : Blo 2003435 4509665 := bstep (se 2 (by rfl) ⟨1691124, by rfl⟩ : syracuseStep 4509665 = 3382249) B3382249
theorem B3006443 : Blo 2003435 3006443 := bstep (se 1 (by rfl) ⟨2254832, by rfl⟩ : syracuseStep 3006443 = 4509665) B4509665
theorem B2004295 : Blo 2003435 2004295 := bstep (se 1 (by rfl) ⟨1503221, by rfl⟩ : syracuseStep 2004295 = 3006443) B3006443
theorem B2254837 : Blo 2003435 2254837 := bbase (se 5 (by rfl) ⟨105695, by rfl⟩ : syracuseStep 2254837 = 211391) (by norm_num)
theorem B3006449 : Blo 2003435 3006449 := bstep (se 2 (by rfl) ⟨1127418, by rfl⟩ : syracuseStep 3006449 = 2254837) B2254837
theorem B2004299 : Blo 2003435 2004299 := bstep (se 1 (by rfl) ⟨1503224, by rfl⟩ : syracuseStep 2004299 = 3006449) B3006449
theorem B2536697 : Blo 2003435 2536697 := bbase (se 2 (by rfl) ⟨951261, by rfl⟩ : syracuseStep 2536697 = 1902523) (by norm_num)
theorem B6764525 : Blo 2003435 6764525 := bstep (se 3 (by rfl) ⟨1268348, by rfl⟩ : syracuseStep 6764525 = 2536697) B2536697
theorem B4509683 : Blo 2003435 4509683 := bstep (se 1 (by rfl) ⟨3382262, by rfl⟩ : syracuseStep 4509683 = 6764525) B6764525
theorem B3006455 : Blo 2003435 3006455 := bstep (se 1 (by rfl) ⟨2254841, by rfl⟩ : syracuseStep 3006455 = 4509683) B4509683
theorem B2004303 : Blo 2003435 2004303 := bstep (se 1 (by rfl) ⟨1503227, by rfl⟩ : syracuseStep 2004303 = 3006455) B3006455
theorem B3006461 : Blo 2003435 3006461 := bbase (se 3 (by rfl) ⟨563711, by rfl⟩ : syracuseStep 3006461 = 1127423) (by norm_num)
theorem B2004307 : Blo 2003435 2004307 := bstep (se 1 (by rfl) ⟨1503230, by rfl⟩ : syracuseStep 2004307 = 3006461) B3006461
theorem B4509701 : Blo 2003435 4509701 := bbase (se 4 (by rfl) ⟨422784, by rfl⟩ : syracuseStep 4509701 = 845569) (by norm_num)
theorem B3006467 : Blo 2003435 3006467 := bstep (se 1 (by rfl) ⟨2254850, by rfl⟩ : syracuseStep 3006467 = 4509701) B4509701
theorem B2004311 : Blo 2003435 2004311 := bstep (se 1 (by rfl) ⟨1503233, by rfl⟩ : syracuseStep 2004311 = 3006467) B3006467
theorem B3805069 : Blo 2003435 3805069 := bbase (se 3 (by rfl) ⟨713450, by rfl⟩ : syracuseStep 3805069 = 1426901) (by norm_num)
theorem B5073425 : Blo 2003435 5073425 := bstep (se 2 (by rfl) ⟨1902534, by rfl⟩ : syracuseStep 5073425 = 3805069) B3805069
theorem B3382283 : Blo 2003435 3382283 := bstep (se 1 (by rfl) ⟨2536712, by rfl⟩ : syracuseStep 3382283 = 5073425) B5073425
theorem B2254855 : Blo 2003435 2254855 := bstep (se 1 (by rfl) ⟨1691141, by rfl⟩ : syracuseStep 2254855 = 3382283) B3382283
theorem B3006473 : Blo 2003435 3006473 := bstep (se 2 (by rfl) ⟨1127427, by rfl⟩ : syracuseStep 3006473 = 2254855) B2254855
theorem B2004315 : Blo 2003435 2004315 := bstep (se 1 (by rfl) ⟨1503236, by rfl⟩ : syracuseStep 2004315 = 3006473) B3006473
theorem B10146869 : Blo 2003435 10146869 := bbase (se 5 (by rfl) ⟨475634, by rfl⟩ : syracuseStep 10146869 = 951269) (by norm_num)
theorem B6764579 : Blo 2003435 6764579 := bstep (se 1 (by rfl) ⟨5073434, by rfl⟩ : syracuseStep 6764579 = 10146869) B10146869
theorem B4509719 : Blo 2003435 4509719 := bstep (se 1 (by rfl) ⟨3382289, by rfl⟩ : syracuseStep 4509719 = 6764579) B6764579
theorem B3006479 : Blo 2003435 3006479 := bstep (se 1 (by rfl) ⟨2254859, by rfl⟩ : syracuseStep 3006479 = 4509719) B4509719
theorem B2004319 : Blo 2003435 2004319 := bstep (se 1 (by rfl) ⟨1503239, by rfl⟩ : syracuseStep 2004319 = 3006479) B3006479
theorem B3006485 : Blo 2003435 3006485 := bbase (se 6 (by rfl) ⟨70464, by rfl⟩ : syracuseStep 3006485 = 140929) (by norm_num)
theorem B2004323 : Blo 2003435 2004323 := bstep (se 1 (by rfl) ⟨1503242, by rfl⟩ : syracuseStep 2004323 = 3006485) B3006485
theorem B21671189 : Blo 2003435 21671189 := bbase (se 6 (by rfl) ⟨507918, by rfl⟩ : syracuseStep 21671189 = 1015837) (by norm_num)
theorem B14447459 : Blo 2003435 14447459 := bstep (se 1 (by rfl) ⟨10835594, by rfl⟩ : syracuseStep 14447459 = 21671189) B21671189
theorem B9631639 : Blo 2003435 9631639 := bstep (se 1 (by rfl) ⟨7223729, by rfl⟩ : syracuseStep 9631639 = 14447459) B14447459
theorem B12842185 : Blo 2003435 12842185 := bstep (se 2 (by rfl) ⟨4815819, by rfl⟩ : syracuseStep 12842185 = 9631639) B9631639
theorem B17122913 : Blo 2003435 17122913 := bstep (se 2 (by rfl) ⟨6421092, by rfl⟩ : syracuseStep 17122913 = 12842185) B12842185
theorem B11415275 : Blo 2003435 11415275 := bstep (se 1 (by rfl) ⟨8561456, by rfl⟩ : syracuseStep 11415275 = 17122913) B17122913
theorem B7610183 : Blo 2003435 7610183 := bstep (se 1 (by rfl) ⟨5707637, by rfl⟩ : syracuseStep 7610183 = 11415275) B11415275
theorem B5073455 : Blo 2003435 5073455 := bstep (se 1 (by rfl) ⟨3805091, by rfl⟩ : syracuseStep 5073455 = 7610183) B7610183
theorem B3382303 : Blo 2003435 3382303 := bstep (se 1 (by rfl) ⟨2536727, by rfl⟩ : syracuseStep 3382303 = 5073455) B5073455
theorem B4509737 : Blo 2003435 4509737 := bstep (se 2 (by rfl) ⟨1691151, by rfl⟩ : syracuseStep 4509737 = 3382303) B3382303
theorem B3006491 : Blo 2003435 3006491 := bstep (se 1 (by rfl) ⟨2254868, by rfl⟩ : syracuseStep 3006491 = 4509737) B4509737
theorem B2004327 : Blo 2003435 2004327 := bstep (se 1 (by rfl) ⟨1503245, by rfl⟩ : syracuseStep 2004327 = 3006491) B3006491
theorem B2254873 : Blo 2003435 2254873 := bbase (se 2 (by rfl) ⟨845577, by rfl⟩ : syracuseStep 2254873 = 1691155) (by norm_num)
theorem B3006497 : Blo 2003435 3006497 := bstep (se 2 (by rfl) ⟨1127436, by rfl⟩ : syracuseStep 3006497 = 2254873) B2254873
theorem B2004331 : Blo 2003435 2004331 := bstep (se 1 (by rfl) ⟨1503248, by rfl⟩ : syracuseStep 2004331 = 3006497) B3006497
theorem B7610213 : Blo 2003435 7610213 := bbase (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) (by norm_num)
theorem B5073475 : Blo 2003435 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B6764633 : Blo 2003435 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B4509755 : Blo 2003435 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B3006503 : Blo 2003435 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B2004335 : Blo 2003435 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B3006509 : Blo 2003435 3006509 := bbase (se 3 (by rfl) ⟨563720, by rfl⟩ : syracuseStep 3006509 = 1127441) (by norm_num)
theorem B2004339 : Blo 2003435 2004339 := bstep (se 1 (by rfl) ⟨1503254, by rfl⟩ : syracuseStep 2004339 = 3006509) B3006509
theorem B4509773 : Blo 2003435 4509773 := bbase (se 3 (by rfl) ⟨845582, by rfl⟩ : syracuseStep 4509773 = 1691165) (by norm_num)
theorem B3006515 : Blo 2003435 3006515 := bstep (se 1 (by rfl) ⟨2254886, by rfl⟩ : syracuseStep 3006515 = 4509773) B4509773
theorem B2004343 : Blo 2003435 2004343 := bstep (se 1 (by rfl) ⟨1503257, by rfl⟩ : syracuseStep 2004343 = 3006515) B3006515
theorem B2536753 : Blo 2003435 2536753 := bbase (se 2 (by rfl) ⟨951282, by rfl⟩ : syracuseStep 2536753 = 1902565) (by norm_num)
theorem B3382337 : Blo 2003435 3382337 := bstep (se 2 (by rfl) ⟨1268376, by rfl⟩ : syracuseStep 3382337 = 2536753) B2536753
theorem B2254891 : Blo 2003435 2254891 := bstep (se 1 (by rfl) ⟨1691168, by rfl⟩ : syracuseStep 2254891 = 3382337) B3382337
theorem B3006521 : Blo 2003435 3006521 := bstep (se 2 (by rfl) ⟨1127445, by rfl⟩ : syracuseStep 3006521 = 2254891) B2254891
theorem B2004347 : Blo 2003435 2004347 := bstep (se 1 (by rfl) ⟨1503260, by rfl⟩ : syracuseStep 2004347 = 3006521) B3006521
theorem B4815877 : Blo 2003435 4815877 := bbase (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) (by norm_num)
theorem B6421169 : Blo 2003435 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B4280779 : Blo 2003435 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B22830821 : Blo 2003435 22830821 := bstep (se 4 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 22830821 = 4280779) B4280779
theorem B15220547 : Blo 2003435 15220547 := bstep (se 1 (by rfl) ⟨11415410, by rfl⟩ : syracuseStep 15220547 = 22830821) B22830821
theorem B10147031 : Blo 2003435 10147031 := bstep (se 1 (by rfl) ⟨7610273, by rfl⟩ : syracuseStep 10147031 = 15220547) B15220547
theorem B6764687 : Blo 2003435 6764687 := bstep (se 1 (by rfl) ⟨5073515, by rfl⟩ : syracuseStep 6764687 = 10147031) B10147031
theorem B4509791 : Blo 2003435 4509791 := bstep (se 1 (by rfl) ⟨3382343, by rfl⟩ : syracuseStep 4509791 = 6764687) B6764687
theorem B3006527 : Blo 2003435 3006527 := bstep (se 1 (by rfl) ⟨2254895, by rfl⟩ : syracuseStep 3006527 = 4509791) B4509791
theorem B2004351 : Blo 2003435 2004351 := bstep (se 1 (by rfl) ⟨1503263, by rfl⟩ : syracuseStep 2004351 = 3006527) B3006527
theorem B3006533 : Blo 2003435 3006533 := bbase (se 4 (by rfl) ⟨281862, by rfl⟩ : syracuseStep 3006533 = 563725) (by norm_num)
theorem B2004355 : Blo 2003435 2004355 := bstep (se 1 (by rfl) ⟨1503266, by rfl⟩ : syracuseStep 2004355 = 3006533) B3006533
theorem B3382357 : Blo 2003435 3382357 := bbase (se 8 (by rfl) ⟨19818, by rfl⟩ : syracuseStep 3382357 = 39637) (by norm_num)
theorem B4509809 : Blo 2003435 4509809 := bstep (se 2 (by rfl) ⟨1691178, by rfl⟩ : syracuseStep 4509809 = 3382357) B3382357
theorem B3006539 : Blo 2003435 3006539 := bstep (se 1 (by rfl) ⟨2254904, by rfl⟩ : syracuseStep 3006539 = 4509809) B4509809
theorem B2004359 : Blo 2003435 2004359 := bstep (se 1 (by rfl) ⟨1503269, by rfl⟩ : syracuseStep 2004359 = 3006539) B3006539
theorem B2254909 : Blo 2003435 2254909 := bbase (se 3 (by rfl) ⟨422795, by rfl⟩ : syracuseStep 2254909 = 845591) (by norm_num)
theorem B3006545 : Blo 2003435 3006545 := bstep (se 2 (by rfl) ⟨1127454, by rfl⟩ : syracuseStep 3006545 = 2254909) B2254909
theorem B2004363 : Blo 2003435 2004363 := bstep (se 1 (by rfl) ⟨1503272, by rfl⟩ : syracuseStep 2004363 = 3006545) B3006545
theorem B6764741 : Blo 2003435 6764741 := bbase (se 4 (by rfl) ⟨634194, by rfl⟩ : syracuseStep 6764741 = 1268389) (by norm_num)
theorem B4509827 : Blo 2003435 4509827 := bstep (se 1 (by rfl) ⟨3382370, by rfl⟩ : syracuseStep 4509827 = 6764741) B6764741
theorem B3006551 : Blo 2003435 3006551 := bstep (se 1 (by rfl) ⟨2254913, by rfl⟩ : syracuseStep 3006551 = 4509827) B4509827
theorem B2004367 : Blo 2003435 2004367 := bstep (se 1 (by rfl) ⟨1503275, by rfl⟩ : syracuseStep 2004367 = 3006551) B3006551
theorem B3006557 : Blo 2003435 3006557 := bbase (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) (by norm_num)
theorem B2004371 : Blo 2003435 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B4509845 : Blo 2003435 4509845 := bbase (se 6 (by rfl) ⟨105699, by rfl⟩ : syracuseStep 4509845 = 211399) (by norm_num)
theorem B3006563 : Blo 2003435 3006563 := bstep (se 1 (by rfl) ⟨2254922, by rfl⟩ : syracuseStep 3006563 = 4509845) B4509845
theorem B2004375 : Blo 2003435 2004375 := bstep (se 1 (by rfl) ⟨1503281, by rfl⟩ : syracuseStep 2004375 = 3006563) B3006563
theorem B2853893 : Blo 2003435 2853893 := bbase (se 4 (by rfl) ⟨267552, by rfl⟩ : syracuseStep 2853893 = 535105) (by norm_num)
theorem B7610381 : Blo 2003435 7610381 := bstep (se 3 (by rfl) ⟨1426946, by rfl⟩ : syracuseStep 7610381 = 2853893) B2853893
theorem B5073587 : Blo 2003435 5073587 := bstep (se 1 (by rfl) ⟨3805190, by rfl⟩ : syracuseStep 5073587 = 7610381) B7610381
theorem B3382391 : Blo 2003435 3382391 := bstep (se 1 (by rfl) ⟨2536793, by rfl⟩ : syracuseStep 3382391 = 5073587) B5073587
theorem B2254927 : Blo 2003435 2254927 := bstep (se 1 (by rfl) ⟨1691195, by rfl⟩ : syracuseStep 2254927 = 3382391) B3382391
theorem B3006569 : Blo 2003435 3006569 := bstep (se 2 (by rfl) ⟨1127463, by rfl⟩ : syracuseStep 3006569 = 2254927) B2254927
theorem B2004379 : Blo 2003435 2004379 := bstep (se 1 (by rfl) ⟨1503284, by rfl⟩ : syracuseStep 2004379 = 3006569) B3006569
theorem B4339253 : Blo 2003435 4339253 := bbase (se 5 (by rfl) ⟨203402, by rfl⟩ : syracuseStep 4339253 = 406805) (by norm_num)
theorem B11571341 : Blo 2003435 11571341 := bstep (se 3 (by rfl) ⟨2169626, by rfl⟩ : syracuseStep 11571341 = 4339253) B4339253
theorem B123427637 : Blo 2003435 123427637 := bstep (se 5 (by rfl) ⟨5785670, by rfl⟩ : syracuseStep 123427637 = 11571341) B11571341
theorem B82285091 : Blo 2003435 82285091 := bstep (se 1 (by rfl) ⟨61713818, by rfl⟩ : syracuseStep 82285091 = 123427637) B123427637
theorem B54856727 : Blo 2003435 54856727 := bstep (se 1 (by rfl) ⟨41142545, by rfl⟩ : syracuseStep 54856727 = 82285091) B82285091
theorem B36571151 : Blo 2003435 36571151 := bstep (se 1 (by rfl) ⟨27428363, by rfl⟩ : syracuseStep 36571151 = 54856727) B54856727
theorem B24380767 : Blo 2003435 24380767 := bstep (se 1 (by rfl) ⟨18285575, by rfl⟩ : syracuseStep 24380767 = 36571151) B36571151
theorem B32507689 : Blo 2003435 32507689 := bstep (se 2 (by rfl) ⟨12190383, by rfl⟩ : syracuseStep 32507689 = 24380767) B24380767
theorem B43343585 : Blo 2003435 43343585 := bstep (se 2 (by rfl) ⟨16253844, by rfl⟩ : syracuseStep 43343585 = 32507689) B32507689
theorem B28895723 : Blo 2003435 28895723 := bstep (se 1 (by rfl) ⟨21671792, by rfl⟩ : syracuseStep 28895723 = 43343585) B43343585
theorem B19263815 : Blo 2003435 19263815 := bstep (se 1 (by rfl) ⟨14447861, by rfl⟩ : syracuseStep 19263815 = 28895723) B28895723
theorem B12842543 : Blo 2003435 12842543 := bstep (se 1 (by rfl) ⟨9631907, by rfl⟩ : syracuseStep 12842543 = 19263815) B19263815
theorem B8561695 : Blo 2003435 8561695 := bstep (se 1 (by rfl) ⟨6421271, by rfl⟩ : syracuseStep 8561695 = 12842543) B12842543
theorem B11415593 : Blo 2003435 11415593 := bstep (se 2 (by rfl) ⟨4280847, by rfl⟩ : syracuseStep 11415593 = 8561695) B8561695
theorem B7610395 : Blo 2003435 7610395 := bstep (se 1 (by rfl) ⟨5707796, by rfl⟩ : syracuseStep 7610395 = 11415593) B11415593
theorem B10147193 : Blo 2003435 10147193 := bstep (se 2 (by rfl) ⟨3805197, by rfl⟩ : syracuseStep 10147193 = 7610395) B7610395
theorem B6764795 : Blo 2003435 6764795 := bstep (se 1 (by rfl) ⟨5073596, by rfl⟩ : syracuseStep 6764795 = 10147193) B10147193
theorem B4509863 : Blo 2003435 4509863 := bstep (se 1 (by rfl) ⟨3382397, by rfl⟩ : syracuseStep 4509863 = 6764795) B6764795
theorem B3006575 : Blo 2003435 3006575 := bstep (se 1 (by rfl) ⟨2254931, by rfl⟩ : syracuseStep 3006575 = 4509863) B4509863
theorem B2004383 : Blo 2003435 2004383 := bstep (se 1 (by rfl) ⟨1503287, by rfl⟩ : syracuseStep 2004383 = 3006575) B3006575
theorem B3006581 : Blo 2003435 3006581 := bbase (se 5 (by rfl) ⟨140933, by rfl⟩ : syracuseStep 3006581 = 281867) (by norm_num)
theorem B2004387 : Blo 2003435 2004387 := bstep (se 1 (by rfl) ⟨1503290, by rfl⟩ : syracuseStep 2004387 = 3006581) B3006581
theorem B3805213 : Blo 2003435 3805213 := bbase (se 3 (by rfl) ⟨713477, by rfl⟩ : syracuseStep 3805213 = 1426955) (by norm_num)
theorem B5073617 : Blo 2003435 5073617 := bstep (se 2 (by rfl) ⟨1902606, by rfl⟩ : syracuseStep 5073617 = 3805213) B3805213
theorem B3382411 : Blo 2003435 3382411 := bstep (se 1 (by rfl) ⟨2536808, by rfl⟩ : syracuseStep 3382411 = 5073617) B5073617
theorem B4509881 : Blo 2003435 4509881 := bstep (se 2 (by rfl) ⟨1691205, by rfl⟩ : syracuseStep 4509881 = 3382411) B3382411
theorem B3006587 : Blo 2003435 3006587 := bstep (se 1 (by rfl) ⟨2254940, by rfl⟩ : syracuseStep 3006587 = 4509881) B4509881
theorem B2004391 : Blo 2003435 2004391 := bstep (se 1 (by rfl) ⟨1503293, by rfl⟩ : syracuseStep 2004391 = 3006587) B3006587
theorem B2254945 : Blo 2003435 2254945 := bbase (se 2 (by rfl) ⟨845604, by rfl⟩ : syracuseStep 2254945 = 1691209) (by norm_num)
theorem B3006593 : Blo 2003435 3006593 := bstep (se 2 (by rfl) ⟨1127472, by rfl⟩ : syracuseStep 3006593 = 2254945) B2254945
theorem B2004395 : Blo 2003435 2004395 := bstep (se 1 (by rfl) ⟨1503296, by rfl⟩ : syracuseStep 2004395 = 3006593) B3006593
theorem B5073637 : Blo 2003435 5073637 := bbase (se 4 (by rfl) ⟨475653, by rfl⟩ : syracuseStep 5073637 = 951307) (by norm_num)
theorem B6764849 : Blo 2003435 6764849 := bstep (se 2 (by rfl) ⟨2536818, by rfl⟩ : syracuseStep 6764849 = 5073637) B5073637
theorem B4509899 : Blo 2003435 4509899 := bstep (se 1 (by rfl) ⟨3382424, by rfl⟩ : syracuseStep 4509899 = 6764849) B6764849
theorem B3006599 : Blo 2003435 3006599 := bstep (se 1 (by rfl) ⟨2254949, by rfl⟩ : syracuseStep 3006599 = 4509899) B4509899
theorem B2004399 : Blo 2003435 2004399 := bstep (se 1 (by rfl) ⟨1503299, by rfl⟩ : syracuseStep 2004399 = 3006599) B3006599
theorem B3006605 : Blo 2003435 3006605 := bbase (se 3 (by rfl) ⟨563738, by rfl⟩ : syracuseStep 3006605 = 1127477) (by norm_num)
theorem B2004403 : Blo 2003435 2004403 := bstep (se 1 (by rfl) ⟨1503302, by rfl⟩ : syracuseStep 2004403 = 3006605) B3006605
theorem B4509917 : Blo 2003435 4509917 := bbase (se 3 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 4509917 = 1691219) (by norm_num)
theorem B3006611 : Blo 2003435 3006611 := bstep (se 1 (by rfl) ⟨2254958, by rfl⟩ : syracuseStep 3006611 = 4509917) B4509917
theorem B2004407 : Blo 2003435 2004407 := bstep (se 1 (by rfl) ⟨1503305, by rfl⟩ : syracuseStep 2004407 = 3006611) B3006611
theorem B3382445 : Blo 2003435 3382445 := bbase (se 3 (by rfl) ⟨634208, by rfl⟩ : syracuseStep 3382445 = 1268417) (by norm_num)
theorem B2254963 : Blo 2003435 2254963 := bstep (se 1 (by rfl) ⟨1691222, by rfl⟩ : syracuseStep 2254963 = 3382445) B3382445
theorem B3006617 : Blo 2003435 3006617 := bstep (se 2 (by rfl) ⟨1127481, by rfl⟩ : syracuseStep 3006617 = 2254963) B2254963
theorem B2004411 : Blo 2003435 2004411 := bstep (se 1 (by rfl) ⟨1503308, by rfl⟩ : syracuseStep 2004411 = 3006617) B3006617
theorem B36571733 : Blo 2003435 36571733 := bbase (se 8 (by rfl) ⟨214287, by rfl⟩ : syracuseStep 36571733 = 428575) (by norm_num)
theorem B24381155 : Blo 2003435 24381155 := bstep (se 1 (by rfl) ⟨18285866, by rfl⟩ : syracuseStep 24381155 = 36571733) B36571733
theorem B16254103 : Blo 2003435 16254103 := bstep (se 1 (by rfl) ⟨12190577, by rfl⟩ : syracuseStep 16254103 = 24381155) B24381155
theorem B21672137 : Blo 2003435 21672137 := bstep (se 2 (by rfl) ⟨8127051, by rfl⟩ : syracuseStep 21672137 = 16254103) B16254103
theorem B57792365 : Blo 2003435 57792365 := bstep (se 3 (by rfl) ⟨10836068, by rfl⟩ : syracuseStep 57792365 = 21672137) B21672137
theorem B38528243 : Blo 2003435 38528243 := bstep (se 1 (by rfl) ⟨28896182, by rfl⟩ : syracuseStep 38528243 = 57792365) B57792365
theorem B25685495 : Blo 2003435 25685495 := bstep (se 1 (by rfl) ⟨19264121, by rfl⟩ : syracuseStep 25685495 = 38528243) B38528243
theorem B17123663 : Blo 2003435 17123663 := bstep (se 1 (by rfl) ⟨12842747, by rfl⟩ : syracuseStep 17123663 = 25685495) B25685495
theorem B11415775 : Blo 2003435 11415775 := bstep (se 1 (by rfl) ⟨8561831, by rfl⟩ : syracuseStep 11415775 = 17123663) B17123663
theorem B15221033 : Blo 2003435 15221033 := bstep (se 2 (by rfl) ⟨5707887, by rfl⟩ : syracuseStep 15221033 = 11415775) B11415775
theorem B10147355 : Blo 2003435 10147355 := bstep (se 1 (by rfl) ⟨7610516, by rfl⟩ : syracuseStep 10147355 = 15221033) B15221033
theorem B6764903 : Blo 2003435 6764903 := bstep (se 1 (by rfl) ⟨5073677, by rfl⟩ : syracuseStep 6764903 = 10147355) B10147355
theorem B4509935 : Blo 2003435 4509935 := bstep (se 1 (by rfl) ⟨3382451, by rfl⟩ : syracuseStep 4509935 = 6764903) B6764903
theorem B3006623 : Blo 2003435 3006623 := bstep (se 1 (by rfl) ⟨2254967, by rfl⟩ : syracuseStep 3006623 = 4509935) B4509935
theorem B2004415 : Blo 2003435 2004415 := bstep (se 1 (by rfl) ⟨1503311, by rfl⟩ : syracuseStep 2004415 = 3006623) B3006623
theorem B3006629 : Blo 2003435 3006629 := bbase (se 4 (by rfl) ⟨281871, by rfl⟩ : syracuseStep 3006629 = 563743) (by norm_num)
theorem B2004419 : Blo 2003435 2004419 := bstep (se 1 (by rfl) ⟨1503314, by rfl⟩ : syracuseStep 2004419 = 3006629) B3006629
theorem B2536849 : Blo 2003435 2536849 := bbase (se 2 (by rfl) ⟨951318, by rfl⟩ : syracuseStep 2536849 = 1902637) (by norm_num)
theorem B3382465 : Blo 2003435 3382465 := bstep (se 2 (by rfl) ⟨1268424, by rfl⟩ : syracuseStep 3382465 = 2536849) B2536849
theorem B4509953 : Blo 2003435 4509953 := bstep (se 2 (by rfl) ⟨1691232, by rfl⟩ : syracuseStep 4509953 = 3382465) B3382465
theorem B3006635 : Blo 2003435 3006635 := bstep (se 1 (by rfl) ⟨2254976, by rfl⟩ : syracuseStep 3006635 = 4509953) B4509953
theorem B2004423 : Blo 2003435 2004423 := bstep (se 1 (by rfl) ⟨1503317, by rfl⟩ : syracuseStep 2004423 = 3006635) B3006635
theorem B2254981 : Blo 2003435 2254981 := bbase (se 4 (by rfl) ⟨211404, by rfl⟩ : syracuseStep 2254981 = 422809) (by norm_num)
theorem B3006641 : Blo 2003435 3006641 := bstep (se 2 (by rfl) ⟨1127490, by rfl⟩ : syracuseStep 3006641 = 2254981) B2254981
theorem B2004427 : Blo 2003435 2004427 := bstep (se 1 (by rfl) ⟨1503320, by rfl⟩ : syracuseStep 2004427 = 3006641) B3006641
theorem B3612053 : Blo 2003435 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B9632141 : Blo 2003435 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B6421427 : Blo 2003435 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B4280951 : Blo 2003435 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B2853967 : Blo 2003435 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B3805289 : Blo 2003435 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B2536859 : Blo 2003435 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B6764957 : Blo 2003435 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B4509971 : Blo 2003435 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B3006647 : Blo 2003435 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B2004431 : Blo 2003435 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B3006653 : Blo 2003435 3006653 := bbase (se 3 (by rfl) ⟨563747, by rfl⟩ : syracuseStep 3006653 = 1127495) (by norm_num)
theorem B2004435 : Blo 2003435 2004435 := bstep (se 1 (by rfl) ⟨1503326, by rfl⟩ : syracuseStep 2004435 = 3006653) B3006653
theorem B4509989 : Blo 2003435 4509989 := bbase (se 4 (by rfl) ⟨422811, by rfl⟩ : syracuseStep 4509989 = 845623) (by norm_num)
theorem B3006659 : Blo 2003435 3006659 := bstep (se 1 (by rfl) ⟨2254994, by rfl⟩ : syracuseStep 3006659 = 4509989) B4509989
theorem B2004439 : Blo 2003435 2004439 := bstep (se 1 (by rfl) ⟨1503329, by rfl⟩ : syracuseStep 2004439 = 3006659) B3006659
theorem B5073749 : Blo 2003435 5073749 := bbase (se 9 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 5073749 = 29729) (by norm_num)
theorem B3382499 : Blo 2003435 3382499 := bstep (se 1 (by rfl) ⟨2536874, by rfl⟩ : syracuseStep 3382499 = 5073749) B5073749
theorem B2254999 : Blo 2003435 2254999 := bstep (se 1 (by rfl) ⟨1691249, by rfl⟩ : syracuseStep 2254999 = 3382499) B3382499
theorem B3006665 : Blo 2003435 3006665 := bstep (se 2 (by rfl) ⟨1127499, by rfl⟩ : syracuseStep 3006665 = 2254999) B2254999
theorem B2004443 : Blo 2003435 2004443 := bstep (se 1 (by rfl) ⟨1503332, by rfl⟩ : syracuseStep 2004443 = 3006665) B3006665
theorem B6421477 : Blo 2003435 6421477 := bbase (se 4 (by rfl) ⟨602013, by rfl⟩ : syracuseStep 6421477 = 1204027) (by norm_num)
theorem B8561969 : Blo 2003435 8561969 := bstep (se 2 (by rfl) ⟨3210738, by rfl⟩ : syracuseStep 8561969 = 6421477) B6421477
theorem B5707979 : Blo 2003435 5707979 := bstep (se 1 (by rfl) ⟨4280984, by rfl⟩ : syracuseStep 5707979 = 8561969) B8561969
theorem B3805319 : Blo 2003435 3805319 := bstep (se 1 (by rfl) ⟨2853989, by rfl⟩ : syracuseStep 3805319 = 5707979) B5707979
theorem B10147517 : Blo 2003435 10147517 := bstep (se 3 (by rfl) ⟨1902659, by rfl⟩ : syracuseStep 10147517 = 3805319) B3805319
theorem B6765011 : Blo 2003435 6765011 := bstep (se 1 (by rfl) ⟨5073758, by rfl⟩ : syracuseStep 6765011 = 10147517) B10147517
theorem B4510007 : Blo 2003435 4510007 := bstep (se 1 (by rfl) ⟨3382505, by rfl⟩ : syracuseStep 4510007 = 6765011) B6765011
theorem B3006671 : Blo 2003435 3006671 := bstep (se 1 (by rfl) ⟨2255003, by rfl⟩ : syracuseStep 3006671 = 4510007) B4510007
theorem B2004447 : Blo 2003435 2004447 := bstep (se 1 (by rfl) ⟨1503335, by rfl⟩ : syracuseStep 2004447 = 3006671) B3006671
theorem B3006677 : Blo 2003435 3006677 := bbase (se 7 (by rfl) ⟨35234, by rfl⟩ : syracuseStep 3006677 = 70469) (by norm_num)
theorem B2004451 : Blo 2003435 2004451 := bstep (se 1 (by rfl) ⟨1503338, by rfl⟩ : syracuseStep 2004451 = 3006677) B3006677
theorem B2140501 : Blo 2003435 2140501 := bbase (se 10 (by rfl) ⟨3135, by rfl⟩ : syracuseStep 2140501 = 6271) (by norm_num)
theorem B2854001 : Blo 2003435 2854001 := bstep (se 2 (by rfl) ⟨1070250, by rfl⟩ : syracuseStep 2854001 = 2140501) B2140501
theorem B7610669 : Blo 2003435 7610669 := bstep (se 3 (by rfl) ⟨1427000, by rfl⟩ : syracuseStep 7610669 = 2854001) B2854001
theorem B5073779 : Blo 2003435 5073779 := bstep (se 1 (by rfl) ⟨3805334, by rfl⟩ : syracuseStep 5073779 = 7610669) B7610669
theorem B3382519 : Blo 2003435 3382519 := bstep (se 1 (by rfl) ⟨2536889, by rfl⟩ : syracuseStep 3382519 = 5073779) B5073779
theorem B4510025 : Blo 2003435 4510025 := bstep (se 2 (by rfl) ⟨1691259, by rfl⟩ : syracuseStep 4510025 = 3382519) B3382519
theorem B3006683 : Blo 2003435 3006683 := bstep (se 1 (by rfl) ⟨2255012, by rfl⟩ : syracuseStep 3006683 = 4510025) B4510025
theorem B2004455 : Blo 2003435 2004455 := bstep (se 1 (by rfl) ⟨1503341, by rfl⟩ : syracuseStep 2004455 = 3006683) B3006683
theorem B2255017 : Blo 2003435 2255017 := bbase (se 2 (by rfl) ⟨845631, by rfl⟩ : syracuseStep 2255017 = 1691263) (by norm_num)
theorem B3006689 : Blo 2003435 3006689 := bstep (se 2 (by rfl) ⟨1127508, by rfl⟩ : syracuseStep 3006689 = 2255017) B2255017
theorem B2004459 : Blo 2003435 2004459 := bstep (se 1 (by rfl) ⟨1503344, by rfl⟩ : syracuseStep 2004459 = 3006689) B3006689
theorem B8562037 : Blo 2003435 8562037 := bbase (se 5 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 8562037 = 802691) (by norm_num)
theorem B11416049 : Blo 2003435 11416049 := bstep (se 2 (by rfl) ⟨4281018, by rfl⟩ : syracuseStep 11416049 = 8562037) B8562037
theorem B7610699 : Blo 2003435 7610699 := bstep (se 1 (by rfl) ⟨5708024, by rfl⟩ : syracuseStep 7610699 = 11416049) B11416049
theorem B5073799 : Blo 2003435 5073799 := bstep (se 1 (by rfl) ⟨3805349, by rfl⟩ : syracuseStep 5073799 = 7610699) B7610699
theorem B6765065 : Blo 2003435 6765065 := bstep (se 2 (by rfl) ⟨2536899, by rfl⟩ : syracuseStep 6765065 = 5073799) B5073799
theorem B4510043 : Blo 2003435 4510043 := bstep (se 1 (by rfl) ⟨3382532, by rfl⟩ : syracuseStep 4510043 = 6765065) B6765065
theorem B3006695 : Blo 2003435 3006695 := bstep (se 1 (by rfl) ⟨2255021, by rfl⟩ : syracuseStep 3006695 = 4510043) B4510043
theorem B2004463 : Blo 2003435 2004463 := bstep (se 1 (by rfl) ⟨1503347, by rfl⟩ : syracuseStep 2004463 = 3006695) B3006695
theorem B3006701 : Blo 2003435 3006701 := bbase (se 3 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 3006701 = 1127513) (by norm_num)
theorem B2004467 : Blo 2003435 2004467 := bstep (se 1 (by rfl) ⟨1503350, by rfl⟩ : syracuseStep 2004467 = 3006701) B3006701
theorem B4510061 : Blo 2003435 4510061 := bbase (se 3 (by rfl) ⟨845636, by rfl⟩ : syracuseStep 4510061 = 1691273) (by norm_num)
theorem B3006707 : Blo 2003435 3006707 := bstep (se 1 (by rfl) ⟨2255030, by rfl⟩ : syracuseStep 3006707 = 4510061) B4510061
theorem B2004471 : Blo 2003435 2004471 := bstep (se 1 (by rfl) ⟨1503353, by rfl⟩ : syracuseStep 2004471 = 3006707) B3006707
theorem B3805373 : Blo 2003435 3805373 := bbase (se 3 (by rfl) ⟨713507, by rfl⟩ : syracuseStep 3805373 = 1427015) (by norm_num)
theorem B2536915 : Blo 2003435 2536915 := bstep (se 1 (by rfl) ⟨1902686, by rfl⟩ : syracuseStep 2536915 = 3805373) B3805373
theorem B3382553 : Blo 2003435 3382553 := bstep (se 2 (by rfl) ⟨1268457, by rfl⟩ : syracuseStep 3382553 = 2536915) B2536915
theorem B2255035 : Blo 2003435 2255035 := bstep (se 1 (by rfl) ⟨1691276, by rfl⟩ : syracuseStep 2255035 = 3382553) B3382553
theorem B3006713 : Blo 2003435 3006713 := bstep (se 2 (by rfl) ⟨1127517, by rfl⟩ : syracuseStep 3006713 = 2255035) B2255035
theorem B2004475 : Blo 2003435 2004475 := bstep (se 1 (by rfl) ⟨1503356, by rfl⟩ : syracuseStep 2004475 = 3006713) B3006713
theorem B51372629 : Blo 2003435 51372629 := bbase (se 8 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 51372629 = 602023) (by norm_num)
theorem B34248419 : Blo 2003435 34248419 := bstep (se 1 (by rfl) ⟨25686314, by rfl⟩ : syracuseStep 34248419 = 51372629) B51372629
theorem B22832279 : Blo 2003435 22832279 := bstep (se 1 (by rfl) ⟨17124209, by rfl⟩ : syracuseStep 22832279 = 34248419) B34248419
theorem B15221519 : Blo 2003435 15221519 := bstep (se 1 (by rfl) ⟨11416139, by rfl⟩ : syracuseStep 15221519 = 22832279) B22832279
theorem B10147679 : Blo 2003435 10147679 := bstep (se 1 (by rfl) ⟨7610759, by rfl⟩ : syracuseStep 10147679 = 15221519) B15221519
theorem B6765119 : Blo 2003435 6765119 := bstep (se 1 (by rfl) ⟨5073839, by rfl⟩ : syracuseStep 6765119 = 10147679) B10147679
theorem B4510079 : Blo 2003435 4510079 := bstep (se 1 (by rfl) ⟨3382559, by rfl⟩ : syracuseStep 4510079 = 6765119) B6765119
theorem B3006719 : Blo 2003435 3006719 := bstep (se 1 (by rfl) ⟨2255039, by rfl⟩ : syracuseStep 3006719 = 4510079) B4510079
theorem B2004479 : Blo 2003435 2004479 := bstep (se 1 (by rfl) ⟨1503359, by rfl⟩ : syracuseStep 2004479 = 3006719) B3006719
theorem B3006725 : Blo 2003435 3006725 := bbase (se 4 (by rfl) ⟨281880, by rfl⟩ : syracuseStep 3006725 = 563761) (by norm_num)
theorem B2004483 : Blo 2003435 2004483 := bstep (se 1 (by rfl) ⟨1503362, by rfl⟩ : syracuseStep 2004483 = 3006725) B3006725
theorem B3382573 : Blo 2003435 3382573 := bbase (se 3 (by rfl) ⟨634232, by rfl⟩ : syracuseStep 3382573 = 1268465) (by norm_num)
theorem B4510097 : Blo 2003435 4510097 := bstep (se 2 (by rfl) ⟨1691286, by rfl⟩ : syracuseStep 4510097 = 3382573) B3382573
theorem B3006731 : Blo 2003435 3006731 := bstep (se 1 (by rfl) ⟨2255048, by rfl⟩ : syracuseStep 3006731 = 4510097) B4510097
theorem B2004487 : Blo 2003435 2004487 := bstep (se 1 (by rfl) ⟨1503365, by rfl⟩ : syracuseStep 2004487 = 3006731) B3006731
theorem B2255053 : Blo 2003435 2255053 := bbase (se 3 (by rfl) ⟨422822, by rfl⟩ : syracuseStep 2255053 = 845645) (by norm_num)
theorem B3006737 : Blo 2003435 3006737 := bstep (se 2 (by rfl) ⟨1127526, by rfl⟩ : syracuseStep 3006737 = 2255053) B2255053
theorem B2004491 : Blo 2003435 2004491 := bstep (se 1 (by rfl) ⟨1503368, by rfl⟩ : syracuseStep 2004491 = 3006737) B3006737
theorem B6765173 : Blo 2003435 6765173 := bbase (se 5 (by rfl) ⟨317117, by rfl⟩ : syracuseStep 6765173 = 634235) (by norm_num)
theorem B4510115 : Blo 2003435 4510115 := bstep (se 1 (by rfl) ⟨3382586, by rfl⟩ : syracuseStep 4510115 = 6765173) B6765173
theorem B3006743 : Blo 2003435 3006743 := bstep (se 1 (by rfl) ⟨2255057, by rfl⟩ : syracuseStep 3006743 = 4510115) B4510115
theorem B2004495 : Blo 2003435 2004495 := bstep (se 1 (by rfl) ⟨1503371, by rfl⟩ : syracuseStep 2004495 = 3006743) B3006743
theorem B3006749 : Blo 2003435 3006749 := bbase (se 3 (by rfl) ⟨563765, by rfl⟩ : syracuseStep 3006749 = 1127531) (by norm_num)
theorem B2004499 : Blo 2003435 2004499 := bstep (se 1 (by rfl) ⟨1503374, by rfl⟩ : syracuseStep 2004499 = 3006749) B3006749
theorem B4510133 : Blo 2003435 4510133 := bbase (se 5 (by rfl) ⟨211412, by rfl⟩ : syracuseStep 4510133 = 422825) (by norm_num)
theorem B3006755 : Blo 2003435 3006755 := bstep (se 1 (by rfl) ⟨2255066, by rfl⟩ : syracuseStep 3006755 = 4510133) B4510133
theorem B2004503 : Blo 2003435 2004503 := bstep (se 1 (by rfl) ⟨1503377, by rfl⟩ : syracuseStep 2004503 = 3006755) B3006755
theorem B4816253 : Blo 2003435 4816253 := bbase (se 3 (by rfl) ⟨903047, by rfl⟩ : syracuseStep 4816253 = 1806095) (by norm_num)
theorem B3210835 : Blo 2003435 3210835 := bstep (se 1 (by rfl) ⟨2408126, by rfl⟩ : syracuseStep 3210835 = 4816253) B4816253
theorem B4281113 : Blo 2003435 4281113 := bstep (se 2 (by rfl) ⟨1605417, by rfl⟩ : syracuseStep 4281113 = 3210835) B3210835
theorem B11416301 : Blo 2003435 11416301 := bstep (se 3 (by rfl) ⟨2140556, by rfl⟩ : syracuseStep 11416301 = 4281113) B4281113
theorem B7610867 : Blo 2003435 7610867 := bstep (se 1 (by rfl) ⟨5708150, by rfl⟩ : syracuseStep 7610867 = 11416301) B11416301
theorem B5073911 : Blo 2003435 5073911 := bstep (se 1 (by rfl) ⟨3805433, by rfl⟩ : syracuseStep 5073911 = 7610867) B7610867
theorem B3382607 : Blo 2003435 3382607 := bstep (se 1 (by rfl) ⟨2536955, by rfl⟩ : syracuseStep 3382607 = 5073911) B5073911
theorem B2255071 : Blo 2003435 2255071 := bstep (se 1 (by rfl) ⟨1691303, by rfl⟩ : syracuseStep 2255071 = 3382607) B3382607
theorem B3006761 : Blo 2003435 3006761 := bstep (se 2 (by rfl) ⟨1127535, by rfl⟩ : syracuseStep 3006761 = 2255071) B2255071
theorem B2004507 : Blo 2003435 2004507 := bstep (se 1 (by rfl) ⟨1503380, by rfl⟩ : syracuseStep 2004507 = 3006761) B3006761
theorem B3612197 : Blo 2003435 3612197 := bbase (se 4 (by rfl) ⟨338643, by rfl⟩ : syracuseStep 3612197 = 677287) (by norm_num)
theorem B2408131 : Blo 2003435 2408131 := bstep (se 1 (by rfl) ⟨1806098, by rfl⟩ : syracuseStep 2408131 = 3612197) B3612197
theorem B3210841 : Blo 2003435 3210841 := bstep (se 2 (by rfl) ⟨1204065, by rfl⟩ : syracuseStep 3210841 = 2408131) B2408131
theorem B4281121 : Blo 2003435 4281121 := bstep (se 2 (by rfl) ⟨1605420, by rfl⟩ : syracuseStep 4281121 = 3210841) B3210841
theorem B5708161 : Blo 2003435 5708161 := bstep (se 2 (by rfl) ⟨2140560, by rfl⟩ : syracuseStep 5708161 = 4281121) B4281121
theorem B7610881 : Blo 2003435 7610881 := bstep (se 2 (by rfl) ⟨2854080, by rfl⟩ : syracuseStep 7610881 = 5708161) B5708161
theorem B10147841 : Blo 2003435 10147841 := bstep (se 2 (by rfl) ⟨3805440, by rfl⟩ : syracuseStep 10147841 = 7610881) B7610881
theorem B6765227 : Blo 2003435 6765227 := bstep (se 1 (by rfl) ⟨5073920, by rfl⟩ : syracuseStep 6765227 = 10147841) B10147841
theorem B4510151 : Blo 2003435 4510151 := bstep (se 1 (by rfl) ⟨3382613, by rfl⟩ : syracuseStep 4510151 = 6765227) B6765227
theorem B3006767 : Blo 2003435 3006767 := bstep (se 1 (by rfl) ⟨2255075, by rfl⟩ : syracuseStep 3006767 = 4510151) B4510151
theorem B2004511 : Blo 2003435 2004511 := bstep (se 1 (by rfl) ⟨1503383, by rfl⟩ : syracuseStep 2004511 = 3006767) B3006767
theorem B3006773 : Blo 2003435 3006773 := bbase (se 5 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 3006773 = 281885) (by norm_num)
theorem B2004515 : Blo 2003435 2004515 := bstep (se 1 (by rfl) ⟨1503386, by rfl⟩ : syracuseStep 2004515 = 3006773) B3006773
theorem B5073941 : Blo 2003435 5073941 := bbase (se 6 (by rfl) ⟨118920, by rfl⟩ : syracuseStep 5073941 = 237841) (by norm_num)
theorem B3382627 : Blo 2003435 3382627 := bstep (se 1 (by rfl) ⟨2536970, by rfl⟩ : syracuseStep 3382627 = 5073941) B5073941
theorem B4510169 : Blo 2003435 4510169 := bstep (se 2 (by rfl) ⟨1691313, by rfl⟩ : syracuseStep 4510169 = 3382627) B3382627
theorem B3006779 : Blo 2003435 3006779 := bstep (se 1 (by rfl) ⟨2255084, by rfl⟩ : syracuseStep 3006779 = 4510169) B4510169
theorem B2004519 : Blo 2003435 2004519 := bstep (se 1 (by rfl) ⟨1503389, by rfl⟩ : syracuseStep 2004519 = 3006779) B3006779
theorem B2255089 : Blo 2003435 2255089 := bbase (se 2 (by rfl) ⟨845658, by rfl⟩ : syracuseStep 2255089 = 1691317) (by norm_num)
theorem B3006785 : Blo 2003435 3006785 := bstep (se 2 (by rfl) ⟨1127544, by rfl⟩ : syracuseStep 3006785 = 2255089) B2255089
theorem B2004523 : Blo 2003435 2004523 := bstep (se 1 (by rfl) ⟨1503392, by rfl⟩ : syracuseStep 2004523 = 3006785) B3006785
theorem B2031877 : Blo 2003435 2031877 := bbase (se 4 (by rfl) ⟨190488, by rfl⟩ : syracuseStep 2031877 = 380977) (by norm_num)
theorem B2709169 : Blo 2003435 2709169 := bstep (se 2 (by rfl) ⟨1015938, by rfl⟩ : syracuseStep 2709169 = 2031877) B2031877
theorem B14448901 : Blo 2003435 14448901 := bstep (se 4 (by rfl) ⟨1354584, by rfl⟩ : syracuseStep 14448901 = 2709169) B2709169
theorem B19265201 : Blo 2003435 19265201 := bstep (se 2 (by rfl) ⟨7224450, by rfl⟩ : syracuseStep 19265201 = 14448901) B14448901
theorem B12843467 : Blo 2003435 12843467 := bstep (se 1 (by rfl) ⟨9632600, by rfl⟩ : syracuseStep 12843467 = 19265201) B19265201
theorem B8562311 : Blo 2003435 8562311 := bstep (se 1 (by rfl) ⟨6421733, by rfl⟩ : syracuseStep 8562311 = 12843467) B12843467
theorem B5708207 : Blo 2003435 5708207 := bstep (se 1 (by rfl) ⟨4281155, by rfl⟩ : syracuseStep 5708207 = 8562311) B8562311
theorem B3805471 : Blo 2003435 3805471 := bstep (se 1 (by rfl) ⟨2854103, by rfl⟩ : syracuseStep 3805471 = 5708207) B5708207
theorem B5073961 : Blo 2003435 5073961 := bstep (se 2 (by rfl) ⟨1902735, by rfl⟩ : syracuseStep 5073961 = 3805471) B3805471
theorem B6765281 : Blo 2003435 6765281 := bstep (se 2 (by rfl) ⟨2536980, by rfl⟩ : syracuseStep 6765281 = 5073961) B5073961
theorem B4510187 : Blo 2003435 4510187 := bstep (se 1 (by rfl) ⟨3382640, by rfl⟩ : syracuseStep 4510187 = 6765281) B6765281
theorem B3006791 : Blo 2003435 3006791 := bstep (se 1 (by rfl) ⟨2255093, by rfl⟩ : syracuseStep 3006791 = 4510187) B4510187
theorem B2004527 : Blo 2003435 2004527 := bstep (se 1 (by rfl) ⟨1503395, by rfl⟩ : syracuseStep 2004527 = 3006791) B3006791
theorem B3006797 : Blo 2003435 3006797 := bbase (se 3 (by rfl) ⟨563774, by rfl⟩ : syracuseStep 3006797 = 1127549) (by norm_num)
theorem B2004531 : Blo 2003435 2004531 := bstep (se 1 (by rfl) ⟨1503398, by rfl⟩ : syracuseStep 2004531 = 3006797) B3006797
theorem B4510205 : Blo 2003435 4510205 := bbase (se 3 (by rfl) ⟨845663, by rfl⟩ : syracuseStep 4510205 = 1691327) (by norm_num)
theorem B3006803 : Blo 2003435 3006803 := bstep (se 1 (by rfl) ⟨2255102, by rfl⟩ : syracuseStep 3006803 = 4510205) B4510205
theorem B2004535 : Blo 2003435 2004535 := bstep (se 1 (by rfl) ⟨1503401, by rfl⟩ : syracuseStep 2004535 = 3006803) B3006803
theorem B3382661 : Blo 2003435 3382661 := bbase (se 4 (by rfl) ⟨317124, by rfl⟩ : syracuseStep 3382661 = 634249) (by norm_num)
theorem B2255107 : Blo 2003435 2255107 := bstep (se 1 (by rfl) ⟨1691330, by rfl⟩ : syracuseStep 2255107 = 3382661) B3382661
theorem B3006809 : Blo 2003435 3006809 := bstep (se 2 (by rfl) ⟨1127553, by rfl⟩ : syracuseStep 3006809 = 2255107) B2255107
theorem B2004539 : Blo 2003435 2004539 := bstep (se 1 (by rfl) ⟨1503404, by rfl⟩ : syracuseStep 2004539 = 3006809) B3006809
theorem B15222005 : Blo 2003435 15222005 := bbase (se 5 (by rfl) ⟨713531, by rfl⟩ : syracuseStep 15222005 = 1427063) (by norm_num)
theorem B10148003 : Blo 2003435 10148003 := bstep (se 1 (by rfl) ⟨7611002, by rfl⟩ : syracuseStep 10148003 = 15222005) B15222005
theorem B6765335 : Blo 2003435 6765335 := bstep (se 1 (by rfl) ⟨5074001, by rfl⟩ : syracuseStep 6765335 = 10148003) B10148003
theorem B4510223 : Blo 2003435 4510223 := bstep (se 1 (by rfl) ⟨3382667, by rfl⟩ : syracuseStep 4510223 = 6765335) B6765335
theorem B3006815 : Blo 2003435 3006815 := bstep (se 1 (by rfl) ⟨2255111, by rfl⟩ : syracuseStep 3006815 = 4510223) B4510223
theorem B2004543 : Blo 2003435 2004543 := bstep (se 1 (by rfl) ⟨1503407, by rfl⟩ : syracuseStep 2004543 = 3006815) B3006815
theorem B3006821 : Blo 2003435 3006821 := bbase (se 4 (by rfl) ⟨281889, by rfl⟩ : syracuseStep 3006821 = 563779) (by norm_num)
theorem B2004547 : Blo 2003435 2004547 := bstep (se 1 (by rfl) ⟨1503410, by rfl⟩ : syracuseStep 2004547 = 3006821) B3006821
theorem B3805517 : Blo 2003435 3805517 := bbase (se 3 (by rfl) ⟨713534, by rfl⟩ : syracuseStep 3805517 = 1427069) (by norm_num)
theorem B2537011 : Blo 2003435 2537011 := bstep (se 1 (by rfl) ⟨1902758, by rfl⟩ : syracuseStep 2537011 = 3805517) B3805517
theorem B3382681 : Blo 2003435 3382681 := bstep (se 2 (by rfl) ⟨1268505, by rfl⟩ : syracuseStep 3382681 = 2537011) B2537011
theorem B4510241 : Blo 2003435 4510241 := bstep (se 2 (by rfl) ⟨1691340, by rfl⟩ : syracuseStep 4510241 = 3382681) B3382681
theorem B3006827 : Blo 2003435 3006827 := bstep (se 1 (by rfl) ⟨2255120, by rfl⟩ : syracuseStep 3006827 = 4510241) B4510241
theorem B2004551 : Blo 2003435 2004551 := bstep (se 1 (by rfl) ⟨1503413, by rfl⟩ : syracuseStep 2004551 = 3006827) B3006827
theorem B2255125 : Blo 2003435 2255125 := bbase (se 6 (by rfl) ⟨52854, by rfl⟩ : syracuseStep 2255125 = 105709) (by norm_num)
theorem B3006833 : Blo 2003435 3006833 := bstep (se 2 (by rfl) ⟨1127562, by rfl⟩ : syracuseStep 3006833 = 2255125) B2255125
theorem B2004555 : Blo 2003435 2004555 := bstep (se 1 (by rfl) ⟨1503416, by rfl⟩ : syracuseStep 2004555 = 3006833) B3006833
theorem B2537021 : Blo 2003435 2537021 := bbase (se 3 (by rfl) ⟨475691, by rfl⟩ : syracuseStep 2537021 = 951383) (by norm_num)
theorem B6765389 : Blo 2003435 6765389 := bstep (se 3 (by rfl) ⟨1268510, by rfl⟩ : syracuseStep 6765389 = 2537021) B2537021
theorem B4510259 : Blo 2003435 4510259 := bstep (se 1 (by rfl) ⟨3382694, by rfl⟩ : syracuseStep 4510259 = 6765389) B6765389
theorem B3006839 : Blo 2003435 3006839 := bstep (se 1 (by rfl) ⟨2255129, by rfl⟩ : syracuseStep 3006839 = 4510259) B4510259
theorem B2004559 : Blo 2003435 2004559 := bstep (se 1 (by rfl) ⟨1503419, by rfl⟩ : syracuseStep 2004559 = 3006839) B3006839
theorem B3006845 : Blo 2003435 3006845 := bbase (se 3 (by rfl) ⟨563783, by rfl⟩ : syracuseStep 3006845 = 1127567) (by norm_num)
theorem B2004563 : Blo 2003435 2004563 := bstep (se 1 (by rfl) ⟨1503422, by rfl⟩ : syracuseStep 2004563 = 3006845) B3006845
theorem B4510277 : Blo 2003435 4510277 := bbase (se 4 (by rfl) ⟨422838, by rfl⟩ : syracuseStep 4510277 = 845677) (by norm_num)
theorem B3006851 : Blo 2003435 3006851 := bstep (se 1 (by rfl) ⟨2255138, by rfl⟩ : syracuseStep 3006851 = 4510277) B4510277
theorem B2004567 : Blo 2003435 2004567 := bstep (se 1 (by rfl) ⟨1503425, by rfl⟩ : syracuseStep 2004567 = 3006851) B3006851
theorem B2140625 : Blo 2003435 2140625 := bbase (se 2 (by rfl) ⟨802734, by rfl⟩ : syracuseStep 2140625 = 1605469) (by norm_num)
theorem B5708333 : Blo 2003435 5708333 := bstep (se 3 (by rfl) ⟨1070312, by rfl⟩ : syracuseStep 5708333 = 2140625) B2140625
theorem B3805555 : Blo 2003435 3805555 := bstep (se 1 (by rfl) ⟨2854166, by rfl⟩ : syracuseStep 3805555 = 5708333) B5708333
theorem B5074073 : Blo 2003435 5074073 := bstep (se 2 (by rfl) ⟨1902777, by rfl⟩ : syracuseStep 5074073 = 3805555) B3805555
theorem B3382715 : Blo 2003435 3382715 := bstep (se 1 (by rfl) ⟨2537036, by rfl⟩ : syracuseStep 3382715 = 5074073) B5074073
theorem B2255143 : Blo 2003435 2255143 := bstep (se 1 (by rfl) ⟨1691357, by rfl⟩ : syracuseStep 2255143 = 3382715) B3382715
theorem B3006857 : Blo 2003435 3006857 := bstep (se 2 (by rfl) ⟨1127571, by rfl⟩ : syracuseStep 3006857 = 2255143) B2255143
theorem B2004571 : Blo 2003435 2004571 := bstep (se 1 (by rfl) ⟨1503428, by rfl⟩ : syracuseStep 2004571 = 3006857) B3006857
theorem B10148165 : Blo 2003435 10148165 := bbase (se 4 (by rfl) ⟨951390, by rfl⟩ : syracuseStep 10148165 = 1902781) (by norm_num)
theorem B6765443 : Blo 2003435 6765443 := bstep (se 1 (by rfl) ⟨5074082, by rfl⟩ : syracuseStep 6765443 = 10148165) B10148165
theorem B4510295 : Blo 2003435 4510295 := bstep (se 1 (by rfl) ⟨3382721, by rfl⟩ : syracuseStep 4510295 = 6765443) B6765443
theorem B3006863 : Blo 2003435 3006863 := bstep (se 1 (by rfl) ⟨2255147, by rfl⟩ : syracuseStep 3006863 = 4510295) B4510295
theorem B2004575 : Blo 2003435 2004575 := bstep (se 1 (by rfl) ⟨1503431, by rfl⟩ : syracuseStep 2004575 = 3006863) B3006863
theorem B3006869 : Blo 2003435 3006869 := bbase (se 6 (by rfl) ⟨70473, by rfl⟩ : syracuseStep 3006869 = 140947) (by norm_num)
theorem B2004579 : Blo 2003435 2004579 := bstep (se 1 (by rfl) ⟨1503434, by rfl⟩ : syracuseStep 2004579 = 3006869) B3006869
theorem B2709245 : Blo 2003435 2709245 := bbase (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) (by norm_num)
theorem B7224653 : Blo 2003435 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B4816435 : Blo 2003435 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B6421913 : Blo 2003435 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B4281275 : Blo 2003435 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B11416733 : Blo 2003435 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B7611155 : Blo 2003435 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B5074103 : Blo 2003435 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B3382735 : Blo 2003435 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B4510313 : Blo 2003435 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B3006875 : Blo 2003435 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B2004583 : Blo 2003435 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B2255161 : Blo 2003435 2255161 := bbase (se 2 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 2255161 = 1691371) (by norm_num)
theorem B3006881 : Blo 2003435 3006881 := bstep (se 2 (by rfl) ⟨1127580, by rfl⟩ : syracuseStep 3006881 = 2255161) B2255161
theorem B2004587 : Blo 2003435 2004587 := bstep (se 1 (by rfl) ⟨1503440, by rfl⟩ : syracuseStep 2004587 = 3006881) B3006881
theorem B5708389 : Blo 2003435 5708389 := bbase (se 4 (by rfl) ⟨535161, by rfl⟩ : syracuseStep 5708389 = 1070323) (by norm_num)
theorem B7611185 : Blo 2003435 7611185 := bstep (se 2 (by rfl) ⟨2854194, by rfl⟩ : syracuseStep 7611185 = 5708389) B5708389
theorem B5074123 : Blo 2003435 5074123 := bstep (se 1 (by rfl) ⟨3805592, by rfl⟩ : syracuseStep 5074123 = 7611185) B7611185
theorem B6765497 : Blo 2003435 6765497 := bstep (se 2 (by rfl) ⟨2537061, by rfl⟩ : syracuseStep 6765497 = 5074123) B5074123
theorem B4510331 : Blo 2003435 4510331 := bstep (se 1 (by rfl) ⟨3382748, by rfl⟩ : syracuseStep 4510331 = 6765497) B6765497
theorem B3006887 : Blo 2003435 3006887 := bstep (se 1 (by rfl) ⟨2255165, by rfl⟩ : syracuseStep 3006887 = 4510331) B4510331
theorem B2004591 : Blo 2003435 2004591 := bstep (se 1 (by rfl) ⟨1503443, by rfl⟩ : syracuseStep 2004591 = 3006887) B3006887
theorem B3006893 : Blo 2003435 3006893 := bbase (se 3 (by rfl) ⟨563792, by rfl⟩ : syracuseStep 3006893 = 1127585) (by norm_num)
theorem B2004595 : Blo 2003435 2004595 := bstep (se 1 (by rfl) ⟨1503446, by rfl⟩ : syracuseStep 2004595 = 3006893) B3006893
theorem B4510349 : Blo 2003435 4510349 := bbase (se 3 (by rfl) ⟨845690, by rfl⟩ : syracuseStep 4510349 = 1691381) (by norm_num)
theorem B3006899 : Blo 2003435 3006899 := bstep (se 1 (by rfl) ⟨2255174, by rfl⟩ : syracuseStep 3006899 = 4510349) B4510349
theorem B2004599 : Blo 2003435 2004599 := bstep (se 1 (by rfl) ⟨1503449, by rfl⟩ : syracuseStep 2004599 = 3006899) B3006899
theorem B2537077 : Blo 2003435 2537077 := bbase (se 5 (by rfl) ⟨118925, by rfl⟩ : syracuseStep 2537077 = 237851) (by norm_num)
theorem B3382769 : Blo 2003435 3382769 := bstep (se 2 (by rfl) ⟨1268538, by rfl⟩ : syracuseStep 3382769 = 2537077) B2537077
theorem B2255179 : Blo 2003435 2255179 := bstep (se 1 (by rfl) ⟨1691384, by rfl⟩ : syracuseStep 2255179 = 3382769) B3382769
theorem B3006905 : Blo 2003435 3006905 := bstep (se 2 (by rfl) ⟨1127589, by rfl⟩ : syracuseStep 3006905 = 2255179) B2255179
theorem B2004603 : Blo 2003435 2004603 := bstep (se 1 (by rfl) ⟨1503452, by rfl⟩ : syracuseStep 2004603 = 3006905) B3006905
theorem B2571697 : Blo 2003435 2571697 := bbase (se 2 (by rfl) ⟨964386, by rfl⟩ : syracuseStep 2571697 = 1928773) (by norm_num)
theorem B3428929 : Blo 2003435 3428929 := bstep (se 2 (by rfl) ⟨1285848, by rfl⟩ : syracuseStep 3428929 = 2571697) B2571697
theorem B4571905 : Blo 2003435 4571905 := bstep (se 2 (by rfl) ⟨1714464, by rfl⟩ : syracuseStep 4571905 = 3428929) B3428929
theorem B6095873 : Blo 2003435 6095873 := bstep (se 2 (by rfl) ⟨2285952, by rfl⟩ : syracuseStep 6095873 = 4571905) B4571905
theorem B4063915 : Blo 2003435 4063915 := bstep (se 1 (by rfl) ⟨3047936, by rfl⟩ : syracuseStep 4063915 = 6095873) B6095873
theorem B21674213 : Blo 2003435 21674213 := bstep (se 4 (by rfl) ⟨2031957, by rfl⟩ : syracuseStep 21674213 = 4063915) B4063915
theorem B14449475 : Blo 2003435 14449475 := bstep (se 1 (by rfl) ⟨10837106, by rfl⟩ : syracuseStep 14449475 = 21674213) B21674213
theorem B38531933 : Blo 2003435 38531933 := bstep (se 3 (by rfl) ⟨7224737, by rfl⟩ : syracuseStep 38531933 = 14449475) B14449475
theorem B25687955 : Blo 2003435 25687955 := bstep (se 1 (by rfl) ⟨19265966, by rfl⟩ : syracuseStep 25687955 = 38531933) B38531933
theorem B17125303 : Blo 2003435 17125303 := bstep (se 1 (by rfl) ⟨12843977, by rfl⟩ : syracuseStep 17125303 = 25687955) B25687955
theorem B22833737 : Blo 2003435 22833737 := bstep (se 2 (by rfl) ⟨8562651, by rfl⟩ : syracuseStep 22833737 = 17125303) B17125303
theorem B15222491 : Blo 2003435 15222491 := bstep (se 1 (by rfl) ⟨11416868, by rfl⟩ : syracuseStep 15222491 = 22833737) B22833737
theorem B10148327 : Blo 2003435 10148327 := bstep (se 1 (by rfl) ⟨7611245, by rfl⟩ : syracuseStep 10148327 = 15222491) B15222491
theorem B6765551 : Blo 2003435 6765551 := bstep (se 1 (by rfl) ⟨5074163, by rfl⟩ : syracuseStep 6765551 = 10148327) B10148327
theorem B4510367 : Blo 2003435 4510367 := bstep (se 1 (by rfl) ⟨3382775, by rfl⟩ : syracuseStep 4510367 = 6765551) B6765551
theorem B3006911 : Blo 2003435 3006911 := bstep (se 1 (by rfl) ⟨2255183, by rfl⟩ : syracuseStep 3006911 = 4510367) B4510367
theorem B2004607 : Blo 2003435 2004607 := bstep (se 1 (by rfl) ⟨1503455, by rfl⟩ : syracuseStep 2004607 = 3006911) B3006911
theorem B3006917 : Blo 2003435 3006917 := bbase (se 4 (by rfl) ⟨281898, by rfl⟩ : syracuseStep 3006917 = 563797) (by norm_num)
theorem B2004611 : Blo 2003435 2004611 := bstep (se 1 (by rfl) ⟨1503458, by rfl⟩ : syracuseStep 2004611 = 3006917) B3006917
theorem B3382789 : Blo 2003435 3382789 := bbase (se 4 (by rfl) ⟨317136, by rfl⟩ : syracuseStep 3382789 = 634273) (by norm_num)
theorem B4510385 : Blo 2003435 4510385 := bstep (se 2 (by rfl) ⟨1691394, by rfl⟩ : syracuseStep 4510385 = 3382789) B3382789
theorem B3006923 : Blo 2003435 3006923 := bstep (se 1 (by rfl) ⟨2255192, by rfl⟩ : syracuseStep 3006923 = 4510385) B4510385
theorem B2004615 : Blo 2003435 2004615 := bstep (se 1 (by rfl) ⟨1503461, by rfl⟩ : syracuseStep 2004615 = 3006923) B3006923
theorem B2255197 : Blo 2003435 2255197 := bbase (se 3 (by rfl) ⟨422849, by rfl⟩ : syracuseStep 2255197 = 845699) (by norm_num)
theorem B3006929 : Blo 2003435 3006929 := bstep (se 2 (by rfl) ⟨1127598, by rfl⟩ : syracuseStep 3006929 = 2255197) B2255197
theorem B2004619 : Blo 2003435 2004619 := bstep (se 1 (by rfl) ⟨1503464, by rfl⟩ : syracuseStep 2004619 = 3006929) B3006929
theorem B6765605 : Blo 2003435 6765605 := bbase (se 4 (by rfl) ⟨634275, by rfl⟩ : syracuseStep 6765605 = 1268551) (by norm_num)
theorem B4510403 : Blo 2003435 4510403 := bstep (se 1 (by rfl) ⟨3382802, by rfl⟩ : syracuseStep 4510403 = 6765605) B6765605
theorem B3006935 : Blo 2003435 3006935 := bstep (se 1 (by rfl) ⟨2255201, by rfl⟩ : syracuseStep 3006935 = 4510403) B4510403
theorem B2004623 : Blo 2003435 2004623 := bstep (se 1 (by rfl) ⟨1503467, by rfl⟩ : syracuseStep 2004623 = 3006935) B3006935
theorem B3006941 : Blo 2003435 3006941 := bbase (se 3 (by rfl) ⟨563801, by rfl⟩ : syracuseStep 3006941 = 1127603) (by norm_num)
theorem B2004627 : Blo 2003435 2004627 := bstep (se 1 (by rfl) ⟨1503470, by rfl⟩ : syracuseStep 2004627 = 3006941) B3006941
theorem B4510421 : Blo 2003435 4510421 := bbase (se 7 (by rfl) ⟨52856, by rfl⟩ : syracuseStep 4510421 = 105713) (by norm_num)
theorem B3006947 : Blo 2003435 3006947 := bstep (se 1 (by rfl) ⟨2255210, by rfl⟩ : syracuseStep 3006947 = 4510421) B4510421
theorem B2004631 : Blo 2003435 2004631 := bstep (se 1 (by rfl) ⟨1503473, by rfl⟩ : syracuseStep 2004631 = 3006947) B3006947
theorem B8562773 : Blo 2003435 8562773 := bbase (se 8 (by rfl) ⟨50172, by rfl⟩ : syracuseStep 8562773 = 100345) (by norm_num)
theorem B5708515 : Blo 2003435 5708515 := bstep (se 1 (by rfl) ⟨4281386, by rfl⟩ : syracuseStep 5708515 = 8562773) B8562773
theorem B7611353 : Blo 2003435 7611353 := bstep (se 2 (by rfl) ⟨2854257, by rfl⟩ : syracuseStep 7611353 = 5708515) B5708515
theorem B5074235 : Blo 2003435 5074235 := bstep (se 1 (by rfl) ⟨3805676, by rfl⟩ : syracuseStep 5074235 = 7611353) B7611353
theorem B3382823 : Blo 2003435 3382823 := bstep (se 1 (by rfl) ⟨2537117, by rfl⟩ : syracuseStep 3382823 = 5074235) B5074235
theorem B2255215 : Blo 2003435 2255215 := bstep (se 1 (by rfl) ⟨1691411, by rfl⟩ : syracuseStep 2255215 = 3382823) B3382823
theorem B3006953 : Blo 2003435 3006953 := bstep (se 2 (by rfl) ⟨1127607, by rfl⟩ : syracuseStep 3006953 = 2255215) B2255215
theorem B2004635 : Blo 2003435 2004635 := bstep (se 1 (by rfl) ⟨1503476, by rfl⟩ : syracuseStep 2004635 = 3006953) B3006953
theorem B28899413 : Blo 2003435 28899413 := bbase (se 8 (by rfl) ⟨169332, by rfl⟩ : syracuseStep 28899413 = 338665) (by norm_num)
theorem B19266275 : Blo 2003435 19266275 := bstep (se 1 (by rfl) ⟨14449706, by rfl⟩ : syracuseStep 19266275 = 28899413) B28899413
theorem B12844183 : Blo 2003435 12844183 := bstep (se 1 (by rfl) ⟨9633137, by rfl⟩ : syracuseStep 12844183 = 19266275) B19266275
theorem B17125577 : Blo 2003435 17125577 := bstep (se 2 (by rfl) ⟨6422091, by rfl⟩ : syracuseStep 17125577 = 12844183) B12844183
theorem B11417051 : Blo 2003435 11417051 := bstep (se 1 (by rfl) ⟨8562788, by rfl⟩ : syracuseStep 11417051 = 17125577) B17125577
theorem B7611367 : Blo 2003435 7611367 := bstep (se 1 (by rfl) ⟨5708525, by rfl⟩ : syracuseStep 7611367 = 11417051) B11417051
theorem B10148489 : Blo 2003435 10148489 := bstep (se 2 (by rfl) ⟨3805683, by rfl⟩ : syracuseStep 10148489 = 7611367) B7611367
theorem B6765659 : Blo 2003435 6765659 := bstep (se 1 (by rfl) ⟨5074244, by rfl⟩ : syracuseStep 6765659 = 10148489) B10148489
theorem B4510439 : Blo 2003435 4510439 := bstep (se 1 (by rfl) ⟨3382829, by rfl⟩ : syracuseStep 4510439 = 6765659) B6765659
theorem B3006959 : Blo 2003435 3006959 := bstep (se 1 (by rfl) ⟨2255219, by rfl⟩ : syracuseStep 3006959 = 4510439) B4510439
theorem B2004639 : Blo 2003435 2004639 := bstep (se 1 (by rfl) ⟨1503479, by rfl⟩ : syracuseStep 2004639 = 3006959) B3006959
theorem B3006965 : Blo 2003435 3006965 := bbase (se 5 (by rfl) ⟨140951, by rfl⟩ : syracuseStep 3006965 = 281903) (by norm_num)
theorem B2004643 : Blo 2003435 2004643 := bstep (se 1 (by rfl) ⟨1503482, by rfl⟩ : syracuseStep 2004643 = 3006965) B3006965
theorem B5708549 : Blo 2003435 5708549 := bbase (se 4 (by rfl) ⟨535176, by rfl⟩ : syracuseStep 5708549 = 1070353) (by norm_num)
theorem B3805699 : Blo 2003435 3805699 := bstep (se 1 (by rfl) ⟨2854274, by rfl⟩ : syracuseStep 3805699 = 5708549) B5708549
theorem B5074265 : Blo 2003435 5074265 := bstep (se 2 (by rfl) ⟨1902849, by rfl⟩ : syracuseStep 5074265 = 3805699) B3805699
theorem B3382843 : Blo 2003435 3382843 := bstep (se 1 (by rfl) ⟨2537132, by rfl⟩ : syracuseStep 3382843 = 5074265) B5074265
theorem B4510457 : Blo 2003435 4510457 := bstep (se 2 (by rfl) ⟨1691421, by rfl⟩ : syracuseStep 4510457 = 3382843) B3382843
theorem B3006971 : Blo 2003435 3006971 := bstep (se 1 (by rfl) ⟨2255228, by rfl⟩ : syracuseStep 3006971 = 4510457) B4510457
theorem B2004647 : Blo 2003435 2004647 := bstep (se 1 (by rfl) ⟨1503485, by rfl⟩ : syracuseStep 2004647 = 3006971) B3006971
theorem B2255233 : Blo 2003435 2255233 := bbase (se 2 (by rfl) ⟨845712, by rfl⟩ : syracuseStep 2255233 = 1691425) (by norm_num)
theorem B3006977 : Blo 2003435 3006977 := bstep (se 2 (by rfl) ⟨1127616, by rfl⟩ : syracuseStep 3006977 = 2255233) B2255233
theorem B2004651 : Blo 2003435 2004651 := bstep (se 1 (by rfl) ⟨1503488, by rfl⟩ : syracuseStep 2004651 = 3006977) B3006977
theorem B5074285 : Blo 2003435 5074285 := bbase (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) (by norm_num)
theorem B6765713 : Blo 2003435 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B4510475 : Blo 2003435 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B3006983 : Blo 2003435 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B2004655 : Blo 2003435 2004655 := bstep (se 1 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 2004655 = 3006983) B3006983
theorem B3006989 : Blo 2003435 3006989 := bbase (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) (by norm_num)
theorem B2004659 : Blo 2003435 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B4510493 : Blo 2003435 4510493 := bbase (se 3 (by rfl) ⟨845717, by rfl⟩ : syracuseStep 4510493 = 1691435) (by norm_num)
theorem B3006995 : Blo 2003435 3006995 := bstep (se 1 (by rfl) ⟨2255246, by rfl⟩ : syracuseStep 3006995 = 4510493) B4510493
theorem B2004663 : Blo 2003435 2004663 := bstep (se 1 (by rfl) ⟨1503497, by rfl⟩ : syracuseStep 2004663 = 3006995) B3006995
theorem B3382877 : Blo 2003435 3382877 := bbase (se 3 (by rfl) ⟨634289, by rfl⟩ : syracuseStep 3382877 = 1268579) (by norm_num)
theorem B2255251 : Blo 2003435 2255251 := bstep (se 1 (by rfl) ⟨1691438, by rfl⟩ : syracuseStep 2255251 = 3382877) B3382877
theorem B3007001 : Blo 2003435 3007001 := bstep (se 2 (by rfl) ⟨1127625, by rfl⟩ : syracuseStep 3007001 = 2255251) B2255251
theorem B2004667 : Blo 2003435 2004667 := bstep (se 1 (by rfl) ⟨1503500, by rfl⟩ : syracuseStep 2004667 = 3007001) B3007001
theorem B3612485 : Blo 2003435 3612485 := bbase (se 4 (by rfl) ⟨338670, by rfl⟩ : syracuseStep 3612485 = 677341) (by norm_num)
theorem B2408323 : Blo 2003435 2408323 := bstep (se 1 (by rfl) ⟨1806242, by rfl⟩ : syracuseStep 2408323 = 3612485) B3612485
theorem B3211097 : Blo 2003435 3211097 := bstep (se 2 (by rfl) ⟨1204161, by rfl⟩ : syracuseStep 3211097 = 2408323) B2408323
theorem B8562925 : Blo 2003435 8562925 := bstep (se 3 (by rfl) ⟨1605548, by rfl⟩ : syracuseStep 8562925 = 3211097) B3211097
theorem B11417233 : Blo 2003435 11417233 := bstep (se 2 (by rfl) ⟨4281462, by rfl⟩ : syracuseStep 11417233 = 8562925) B8562925
theorem B15222977 : Blo 2003435 15222977 := bstep (se 2 (by rfl) ⟨5708616, by rfl⟩ : syracuseStep 15222977 = 11417233) B11417233
theorem B10148651 : Blo 2003435 10148651 := bstep (se 1 (by rfl) ⟨7611488, by rfl⟩ : syracuseStep 10148651 = 15222977) B15222977
theorem B6765767 : Blo 2003435 6765767 := bstep (se 1 (by rfl) ⟨5074325, by rfl⟩ : syracuseStep 6765767 = 10148651) B10148651
theorem B4510511 : Blo 2003435 4510511 := bstep (se 1 (by rfl) ⟨3382883, by rfl⟩ : syracuseStep 4510511 = 6765767) B6765767
theorem B3007007 : Blo 2003435 3007007 := bstep (se 1 (by rfl) ⟨2255255, by rfl⟩ : syracuseStep 3007007 = 4510511) B4510511
theorem B2004671 : Blo 2003435 2004671 := bstep (se 1 (by rfl) ⟨1503503, by rfl⟩ : syracuseStep 2004671 = 3007007) B3007007
theorem B3007013 : Blo 2003435 3007013 := bbase (se 4 (by rfl) ⟨281907, by rfl⟩ : syracuseStep 3007013 = 563815) (by norm_num)
theorem B2004675 : Blo 2003435 2004675 := bstep (se 1 (by rfl) ⟨1503506, by rfl⟩ : syracuseStep 2004675 = 3007013) B3007013
theorem B2537173 : Blo 2003435 2537173 := bbase (se 7 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 2537173 = 59465) (by norm_num)
theorem B3382897 : Blo 2003435 3382897 := bstep (se 2 (by rfl) ⟨1268586, by rfl⟩ : syracuseStep 3382897 = 2537173) B2537173
theorem B4510529 : Blo 2003435 4510529 := bstep (se 2 (by rfl) ⟨1691448, by rfl⟩ : syracuseStep 4510529 = 3382897) B3382897
theorem B3007019 : Blo 2003435 3007019 := bstep (se 1 (by rfl) ⟨2255264, by rfl⟩ : syracuseStep 3007019 = 4510529) B4510529
theorem B2004679 : Blo 2003435 2004679 := bstep (se 1 (by rfl) ⟨1503509, by rfl⟩ : syracuseStep 2004679 = 3007019) B3007019
theorem B2255269 : Blo 2003435 2255269 := bbase (se 4 (by rfl) ⟨211431, by rfl⟩ : syracuseStep 2255269 = 422863) (by norm_num)
theorem B3007025 : Blo 2003435 3007025 := bstep (se 2 (by rfl) ⟨1127634, by rfl⟩ : syracuseStep 3007025 = 2255269) B2255269
theorem B2004683 : Blo 2003435 2004683 := bstep (se 1 (by rfl) ⟨1503512, by rfl⟩ : syracuseStep 2004683 = 3007025) B3007025
theorem B4816685 : Blo 2003435 4816685 := bbase (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) (by norm_num)
theorem B12844493 : Blo 2003435 12844493 := bstep (se 3 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 12844493 = 4816685) B4816685
theorem B8562995 : Blo 2003435 8562995 := bstep (se 1 (by rfl) ⟨6422246, by rfl⟩ : syracuseStep 8562995 = 12844493) B12844493
theorem B5708663 : Blo 2003435 5708663 := bstep (se 1 (by rfl) ⟨4281497, by rfl⟩ : syracuseStep 5708663 = 8562995) B8562995
theorem B3805775 : Blo 2003435 3805775 := bstep (se 1 (by rfl) ⟨2854331, by rfl⟩ : syracuseStep 3805775 = 5708663) B5708663
theorem B2537183 : Blo 2003435 2537183 := bstep (se 1 (by rfl) ⟨1902887, by rfl⟩ : syracuseStep 2537183 = 3805775) B3805775
theorem B6765821 : Blo 2003435 6765821 := bstep (se 3 (by rfl) ⟨1268591, by rfl⟩ : syracuseStep 6765821 = 2537183) B2537183
theorem B4510547 : Blo 2003435 4510547 := bstep (se 1 (by rfl) ⟨3382910, by rfl⟩ : syracuseStep 4510547 = 6765821) B6765821
theorem B3007031 : Blo 2003435 3007031 := bstep (se 1 (by rfl) ⟨2255273, by rfl⟩ : syracuseStep 3007031 = 4510547) B4510547
theorem B2004687 : Blo 2003435 2004687 := bstep (se 1 (by rfl) ⟨1503515, by rfl⟩ : syracuseStep 2004687 = 3007031) B3007031
theorem B3007037 : Blo 2003435 3007037 := bbase (se 3 (by rfl) ⟨563819, by rfl⟩ : syracuseStep 3007037 = 1127639) (by norm_num)
theorem B2004691 : Blo 2003435 2004691 := bstep (se 1 (by rfl) ⟨1503518, by rfl⟩ : syracuseStep 2004691 = 3007037) B3007037
theorem B4510565 : Blo 2003435 4510565 := bbase (se 4 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 4510565 = 845731) (by norm_num)
theorem B3007043 : Blo 2003435 3007043 := bstep (se 1 (by rfl) ⟨2255282, by rfl⟩ : syracuseStep 3007043 = 4510565) B4510565
theorem B2004695 : Blo 2003435 2004695 := bstep (se 1 (by rfl) ⟨1503521, by rfl⟩ : syracuseStep 2004695 = 3007043) B3007043
theorem B5074397 : Blo 2003435 5074397 := bbase (se 3 (by rfl) ⟨951449, by rfl⟩ : syracuseStep 5074397 = 1902899) (by norm_num)
theorem B3382931 : Blo 2003435 3382931 := bstep (se 1 (by rfl) ⟨2537198, by rfl⟩ : syracuseStep 3382931 = 5074397) B5074397
theorem B2255287 : Blo 2003435 2255287 := bstep (se 1 (by rfl) ⟨1691465, by rfl⟩ : syracuseStep 2255287 = 3382931) B3382931
theorem B3007049 : Blo 2003435 3007049 := bstep (se 2 (by rfl) ⟨1127643, by rfl⟩ : syracuseStep 3007049 = 2255287) B2255287
theorem B2004699 : Blo 2003435 2004699 := bstep (se 1 (by rfl) ⟨1503524, by rfl⟩ : syracuseStep 2004699 = 3007049) B3007049
theorem B3805805 : Blo 2003435 3805805 := bbase (se 3 (by rfl) ⟨713588, by rfl⟩ : syracuseStep 3805805 = 1427177) (by norm_num)
theorem B10148813 : Blo 2003435 10148813 := bstep (se 3 (by rfl) ⟨1902902, by rfl⟩ : syracuseStep 10148813 = 3805805) B3805805
theorem B6765875 : Blo 2003435 6765875 := bstep (se 1 (by rfl) ⟨5074406, by rfl⟩ : syracuseStep 6765875 = 10148813) B10148813
theorem B4510583 : Blo 2003435 4510583 := bstep (se 1 (by rfl) ⟨3382937, by rfl⟩ : syracuseStep 4510583 = 6765875) B6765875
theorem B3007055 : Blo 2003435 3007055 := bstep (se 1 (by rfl) ⟨2255291, by rfl⟩ : syracuseStep 3007055 = 4510583) B4510583
theorem B2004703 : Blo 2003435 2004703 := bstep (se 1 (by rfl) ⟨1503527, by rfl⟩ : syracuseStep 2004703 = 3007055) B3007055
theorem B3007061 : Blo 2003435 3007061 := bbase (se 8 (by rfl) ⟨17619, by rfl⟩ : syracuseStep 3007061 = 35239) (by norm_num)
theorem B2004707 : Blo 2003435 2004707 := bstep (se 1 (by rfl) ⟨1503530, by rfl⟩ : syracuseStep 2004707 = 3007061) B3007061
theorem B3612557 : Blo 2003435 3612557 := bbase (se 3 (by rfl) ⟨677354, by rfl⟩ : syracuseStep 3612557 = 1354709) (by norm_num)
theorem B9633485 : Blo 2003435 9633485 := bstep (se 3 (by rfl) ⟨1806278, by rfl⟩ : syracuseStep 9633485 = 3612557) B3612557
theorem B6422323 : Blo 2003435 6422323 := bstep (se 1 (by rfl) ⟨4816742, by rfl⟩ : syracuseStep 6422323 = 9633485) B9633485
theorem B8563097 : Blo 2003435 8563097 := bstep (se 2 (by rfl) ⟨3211161, by rfl⟩ : syracuseStep 8563097 = 6422323) B6422323
theorem B5708731 : Blo 2003435 5708731 := bstep (se 1 (by rfl) ⟨4281548, by rfl⟩ : syracuseStep 5708731 = 8563097) B8563097
theorem B7611641 : Blo 2003435 7611641 := bstep (se 2 (by rfl) ⟨2854365, by rfl⟩ : syracuseStep 7611641 = 5708731) B5708731
theorem B5074427 : Blo 2003435 5074427 := bstep (se 1 (by rfl) ⟨3805820, by rfl⟩ : syracuseStep 5074427 = 7611641) B7611641
theorem B3382951 : Blo 2003435 3382951 := bstep (se 1 (by rfl) ⟨2537213, by rfl⟩ : syracuseStep 3382951 = 5074427) B5074427
theorem B4510601 : Blo 2003435 4510601 := bstep (se 2 (by rfl) ⟨1691475, by rfl⟩ : syracuseStep 4510601 = 3382951) B3382951
theorem B3007067 : Blo 2003435 3007067 := bstep (se 1 (by rfl) ⟨2255300, by rfl⟩ : syracuseStep 3007067 = 4510601) B4510601
theorem B2004711 : Blo 2003435 2004711 := bstep (se 1 (by rfl) ⟨1503533, by rfl⟩ : syracuseStep 2004711 = 3007067) B3007067
theorem B2255305 : Blo 2003435 2255305 := bbase (se 2 (by rfl) ⟨845739, by rfl⟩ : syracuseStep 2255305 = 1691479) (by norm_num)
theorem B3007073 : Blo 2003435 3007073 := bstep (se 2 (by rfl) ⟨1127652, by rfl⟩ : syracuseStep 3007073 = 2255305) B2255305
theorem B2004715 : Blo 2003435 2004715 := bstep (se 1 (by rfl) ⟨1503536, by rfl⟩ : syracuseStep 2004715 = 3007073) B3007073
theorem B17126261 : Blo 2003435 17126261 := bbase (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) (by norm_num)
theorem B11417507 : Blo 2003435 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B7611671 : Blo 2003435 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B5074447 : Blo 2003435 5074447 := bstep (se 1 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 5074447 = 7611671) B7611671
theorem B6765929 : Blo 2003435 6765929 := bstep (se 2 (by rfl) ⟨2537223, by rfl⟩ : syracuseStep 6765929 = 5074447) B5074447
theorem B4510619 : Blo 2003435 4510619 := bstep (se 1 (by rfl) ⟨3382964, by rfl⟩ : syracuseStep 4510619 = 6765929) B6765929
theorem B3007079 : Blo 2003435 3007079 := bstep (se 1 (by rfl) ⟨2255309, by rfl⟩ : syracuseStep 3007079 = 4510619) B4510619
theorem B2004719 : Blo 2003435 2004719 := bstep (se 1 (by rfl) ⟨1503539, by rfl⟩ : syracuseStep 2004719 = 3007079) B3007079
theorem B3007085 : Blo 2003435 3007085 := bbase (se 3 (by rfl) ⟨563828, by rfl⟩ : syracuseStep 3007085 = 1127657) (by norm_num)
theorem B2004723 : Blo 2003435 2004723 := bstep (se 1 (by rfl) ⟨1503542, by rfl⟩ : syracuseStep 2004723 = 3007085) B3007085
theorem B4510637 : Blo 2003435 4510637 := bbase (se 3 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 4510637 = 1691489) (by norm_num)
theorem B3007091 : Blo 2003435 3007091 := bstep (se 1 (by rfl) ⟨2255318, by rfl⟩ : syracuseStep 3007091 = 4510637) B4510637
theorem B2004727 : Blo 2003435 2004727 := bstep (se 1 (by rfl) ⟨1503545, by rfl⟩ : syracuseStep 2004727 = 3007091) B3007091
theorem B5708789 : Blo 2003435 5708789 := bbase (se 5 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 5708789 = 535199) (by norm_num)
theorem B3805859 : Blo 2003435 3805859 := bstep (se 1 (by rfl) ⟨2854394, by rfl⟩ : syracuseStep 3805859 = 5708789) B5708789
theorem B2537239 : Blo 2003435 2537239 := bstep (se 1 (by rfl) ⟨1902929, by rfl⟩ : syracuseStep 2537239 = 3805859) B3805859
theorem B3382985 : Blo 2003435 3382985 := bstep (se 2 (by rfl) ⟨1268619, by rfl⟩ : syracuseStep 3382985 = 2537239) B2537239
theorem B2255323 : Blo 2003435 2255323 := bstep (se 1 (by rfl) ⟨1691492, by rfl⟩ : syracuseStep 2255323 = 3382985) B3382985
theorem B3007097 : Blo 2003435 3007097 := bstep (se 2 (by rfl) ⟨1127661, by rfl⟩ : syracuseStep 3007097 = 2255323) B2255323
theorem B2004731 : Blo 2003435 2004731 := bstep (se 1 (by rfl) ⟨1503548, by rfl⟩ : syracuseStep 2004731 = 3007097) B3007097
theorem B2317289 : Blo 2003435 2317289 := bbase (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) (by norm_num)
theorem B6179437 : Blo 2003435 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B8239249 : Blo 2003435 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B43942661 : Blo 2003435 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B29295107 : Blo 2003435 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B19530071 : Blo 2003435 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B13020047 : Blo 2003435 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B8680031 : Blo 2003435 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B5786687 : Blo 2003435 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B3857791 : Blo 2003435 3857791 := bstep (se 1 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 3857791 = 5786687) B5786687
theorem B5143721 : Blo 2003435 5143721 := bstep (se 2 (by rfl) ⟨1928895, by rfl⟩ : syracuseStep 5143721 = 3857791) B3857791
theorem B13716589 : Blo 2003435 13716589 := bstep (se 3 (by rfl) ⟨2571860, by rfl⟩ : syracuseStep 13716589 = 5143721) B5143721
theorem B18288785 : Blo 2003435 18288785 := bstep (se 2 (by rfl) ⟨6858294, by rfl⟩ : syracuseStep 18288785 = 13716589) B13716589
theorem B48770093 : Blo 2003435 48770093 := bstep (se 3 (by rfl) ⟨9144392, by rfl⟩ : syracuseStep 48770093 = 18288785) B18288785
theorem B32513395 : Blo 2003435 32513395 := bstep (se 1 (by rfl) ⟨24385046, by rfl⟩ : syracuseStep 32513395 = 48770093) B48770093
theorem B43351193 : Blo 2003435 43351193 := bstep (se 2 (by rfl) ⟨16256697, by rfl⟩ : syracuseStep 43351193 = 32513395) B32513395
theorem B28900795 : Blo 2003435 28900795 := bstep (se 1 (by rfl) ⟨21675596, by rfl⟩ : syracuseStep 28900795 = 43351193) B43351193
theorem B38534393 : Blo 2003435 38534393 := bstep (se 2 (by rfl) ⟨14450397, by rfl⟩ : syracuseStep 38534393 = 28900795) B28900795
theorem B25689595 : Blo 2003435 25689595 := bstep (se 1 (by rfl) ⟨19267196, by rfl⟩ : syracuseStep 25689595 = 38534393) B38534393
theorem B34252793 : Blo 2003435 34252793 := bstep (se 2 (by rfl) ⟨12844797, by rfl⟩ : syracuseStep 34252793 = 25689595) B25689595
theorem B22835195 : Blo 2003435 22835195 := bstep (se 1 (by rfl) ⟨17126396, by rfl⟩ : syracuseStep 22835195 = 34252793) B34252793
theorem B15223463 : Blo 2003435 15223463 := bstep (se 1 (by rfl) ⟨11417597, by rfl⟩ : syracuseStep 15223463 = 22835195) B22835195
theorem B10148975 : Blo 2003435 10148975 := bstep (se 1 (by rfl) ⟨7611731, by rfl⟩ : syracuseStep 10148975 = 15223463) B15223463
theorem B6765983 : Blo 2003435 6765983 := bstep (se 1 (by rfl) ⟨5074487, by rfl⟩ : syracuseStep 6765983 = 10148975) B10148975
theorem B4510655 : Blo 2003435 4510655 := bstep (se 1 (by rfl) ⟨3382991, by rfl⟩ : syracuseStep 4510655 = 6765983) B6765983
theorem B3007103 : Blo 2003435 3007103 := bstep (se 1 (by rfl) ⟨2255327, by rfl⟩ : syracuseStep 3007103 = 4510655) B4510655
theorem B2004735 : Blo 2003435 2004735 := bstep (se 1 (by rfl) ⟨1503551, by rfl⟩ : syracuseStep 2004735 = 3007103) B3007103
theorem B3007109 : Blo 2003435 3007109 := bbase (se 4 (by rfl) ⟨281916, by rfl⟩ : syracuseStep 3007109 = 563833) (by norm_num)
theorem B2004739 : Blo 2003435 2004739 := bstep (se 1 (by rfl) ⟨1503554, by rfl⟩ : syracuseStep 2004739 = 3007109) B3007109
theorem B3383005 : Blo 2003435 3383005 := bbase (se 3 (by rfl) ⟨634313, by rfl⟩ : syracuseStep 3383005 = 1268627) (by norm_num)
theorem B4510673 : Blo 2003435 4510673 := bstep (se 2 (by rfl) ⟨1691502, by rfl⟩ : syracuseStep 4510673 = 3383005) B3383005
theorem B3007115 : Blo 2003435 3007115 := bstep (se 1 (by rfl) ⟨2255336, by rfl⟩ : syracuseStep 3007115 = 4510673) B4510673
theorem B2004743 : Blo 2003435 2004743 := bstep (se 1 (by rfl) ⟨1503557, by rfl⟩ : syracuseStep 2004743 = 3007115) B3007115
theorem B2255341 : Blo 2003435 2255341 := bbase (se 3 (by rfl) ⟨422876, by rfl⟩ : syracuseStep 2255341 = 845753) (by norm_num)
theorem B3007121 : Blo 2003435 3007121 := bstep (se 2 (by rfl) ⟨1127670, by rfl⟩ : syracuseStep 3007121 = 2255341) B2255341
theorem B2004747 : Blo 2003435 2004747 := bstep (se 1 (by rfl) ⟨1503560, by rfl⟩ : syracuseStep 2004747 = 3007121) B3007121
theorem B6766037 : Blo 2003435 6766037 := bbase (se 7 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 6766037 = 158579) (by norm_num)
theorem B4510691 : Blo 2003435 4510691 := bstep (se 1 (by rfl) ⟨3383018, by rfl⟩ : syracuseStep 4510691 = 6766037) B6766037
theorem B3007127 : Blo 2003435 3007127 := bstep (se 1 (by rfl) ⟨2255345, by rfl⟩ : syracuseStep 3007127 = 4510691) B4510691
theorem B2004751 : Blo 2003435 2004751 := bstep (se 1 (by rfl) ⟨1503563, by rfl⟩ : syracuseStep 2004751 = 3007127) B3007127
theorem B3007133 : Blo 2003435 3007133 := bbase (se 3 (by rfl) ⟨563837, by rfl⟩ : syracuseStep 3007133 = 1127675) (by norm_num)
theorem B2004755 : Blo 2003435 2004755 := bstep (se 1 (by rfl) ⟨1503566, by rfl⟩ : syracuseStep 2004755 = 3007133) B3007133
theorem B4510709 : Blo 2003435 4510709 := bbase (se 5 (by rfl) ⟨211439, by rfl⟩ : syracuseStep 4510709 = 422879) (by norm_num)
theorem B3007139 : Blo 2003435 3007139 := bstep (se 1 (by rfl) ⟨2255354, by rfl⟩ : syracuseStep 3007139 = 4510709) B4510709
theorem B2004759 : Blo 2003435 2004759 := bstep (se 1 (by rfl) ⟨1503569, by rfl⟩ : syracuseStep 2004759 = 3007139) B3007139
theorem B26395733 : Blo 2003435 26395733 := bbase (se 8 (by rfl) ⟨154662, by rfl⟩ : syracuseStep 26395733 = 309325) (by norm_num)
theorem B17597155 : Blo 2003435 17597155 := bstep (se 1 (by rfl) ⟨13197866, by rfl⟩ : syracuseStep 17597155 = 26395733) B26395733
theorem B23462873 : Blo 2003435 23462873 := bstep (se 2 (by rfl) ⟨8798577, by rfl⟩ : syracuseStep 23462873 = 17597155) B17597155
theorem B1001082581 : Blo 2003435 1001082581 := bstep (se 7 (by rfl) ⟨11731436, by rfl⟩ : syracuseStep 1001082581 = 23462873) B23462873
theorem B667388387 : Blo 2003435 667388387 := bstep (se 1 (by rfl) ⟨500541290, by rfl⟩ : syracuseStep 667388387 = 1001082581) B1001082581
theorem B444925591 : Blo 2003435 444925591 := bstep (se 1 (by rfl) ⟨333694193, by rfl⟩ : syracuseStep 444925591 = 667388387) B667388387
theorem B2372936485 : Blo 2003435 2372936485 := bstep (se 4 (by rfl) ⟨222462795, by rfl⟩ : syracuseStep 2372936485 = 444925591) B444925591
theorem B3163915313 : Blo 2003435 3163915313 := bstep (se 2 (by rfl) ⟨1186468242, by rfl⟩ : syracuseStep 3163915313 = 2372936485) B2372936485
theorem B2109276875 : Blo 2003435 2109276875 := bstep (se 1 (by rfl) ⟨1581957656, by rfl⟩ : syracuseStep 2109276875 = 3163915313) B3163915313
theorem B1406184583 : Blo 2003435 1406184583 := bstep (se 1 (by rfl) ⟨1054638437, by rfl⟩ : syracuseStep 1406184583 = 2109276875) B2109276875
theorem B1874912777 : Blo 2003435 1874912777 := bstep (se 2 (by rfl) ⟨703092291, by rfl⟩ : syracuseStep 1874912777 = 1406184583) B1406184583
theorem B1249941851 : Blo 2003435 1249941851 := bstep (se 1 (by rfl) ⟨937456388, by rfl⟩ : syracuseStep 1249941851 = 1874912777) B1874912777
theorem B833294567 : Blo 2003435 833294567 := bstep (se 1 (by rfl) ⟨624970925, by rfl⟩ : syracuseStep 833294567 = 1249941851) B1249941851
theorem B555529711 : Blo 2003435 555529711 := bstep (se 1 (by rfl) ⟨416647283, by rfl⟩ : syracuseStep 555529711 = 833294567) B833294567
theorem B740706281 : Blo 2003435 740706281 := bstep (se 2 (by rfl) ⟨277764855, by rfl⟩ : syracuseStep 740706281 = 555529711) B555529711
theorem B493804187 : Blo 2003435 493804187 := bstep (se 1 (by rfl) ⟨370353140, by rfl⟩ : syracuseStep 493804187 = 740706281) B740706281
theorem B329202791 : Blo 2003435 329202791 := bstep (se 1 (by rfl) ⟨246902093, by rfl⟩ : syracuseStep 329202791 = 493804187) B493804187
theorem B219468527 : Blo 2003435 219468527 := bstep (se 1 (by rfl) ⟨164601395, by rfl⟩ : syracuseStep 219468527 = 329202791) B329202791
theorem B146312351 : Blo 2003435 146312351 := bstep (se 1 (by rfl) ⟨109734263, by rfl⟩ : syracuseStep 146312351 = 219468527) B219468527
theorem B97541567 : Blo 2003435 97541567 := bstep (se 1 (by rfl) ⟨73156175, by rfl⟩ : syracuseStep 97541567 = 146312351) B146312351
theorem B65027711 : Blo 2003435 65027711 := bstep (se 1 (by rfl) ⟨48770783, by rfl⟩ : syracuseStep 65027711 = 97541567) B97541567
theorem B43351807 : Blo 2003435 43351807 := bstep (se 1 (by rfl) ⟨32513855, by rfl⟩ : syracuseStep 43351807 = 65027711) B65027711
theorem B57802409 : Blo 2003435 57802409 := bstep (se 2 (by rfl) ⟨21675903, by rfl⟩ : syracuseStep 57802409 = 43351807) B43351807
theorem B38534939 : Blo 2003435 38534939 := bstep (se 1 (by rfl) ⟨28901204, by rfl⟩ : syracuseStep 38534939 = 57802409) B57802409
theorem B25689959 : Blo 2003435 25689959 := bstep (se 1 (by rfl) ⟨19267469, by rfl⟩ : syracuseStep 25689959 = 38534939) B38534939
theorem B17126639 : Blo 2003435 17126639 := bstep (se 1 (by rfl) ⟨12844979, by rfl⟩ : syracuseStep 17126639 = 25689959) B25689959
theorem B11417759 : Blo 2003435 11417759 := bstep (se 1 (by rfl) ⟨8563319, by rfl⟩ : syracuseStep 11417759 = 17126639) B17126639
theorem B7611839 : Blo 2003435 7611839 := bstep (se 1 (by rfl) ⟨5708879, by rfl⟩ : syracuseStep 7611839 = 11417759) B11417759
theorem B5074559 : Blo 2003435 5074559 := bstep (se 1 (by rfl) ⟨3805919, by rfl⟩ : syracuseStep 5074559 = 7611839) B7611839
theorem B3383039 : Blo 2003435 3383039 := bstep (se 1 (by rfl) ⟨2537279, by rfl⟩ : syracuseStep 3383039 = 5074559) B5074559
theorem B2255359 : Blo 2003435 2255359 := bstep (se 1 (by rfl) ⟨1691519, by rfl⟩ : syracuseStep 2255359 = 3383039) B3383039
theorem B3007145 : Blo 2003435 3007145 := bstep (se 2 (by rfl) ⟨1127679, by rfl⟩ : syracuseStep 3007145 = 2255359) B2255359
theorem B2004763 : Blo 2003435 2004763 := bstep (se 1 (by rfl) ⟨1503572, by rfl⟩ : syracuseStep 2004763 = 3007145) B3007145
theorem B2854445 : Blo 2003435 2854445 := bbase (se 3 (by rfl) ⟨535208, by rfl⟩ : syracuseStep 2854445 = 1070417) (by norm_num)
theorem B7611853 : Blo 2003435 7611853 := bstep (se 3 (by rfl) ⟨1427222, by rfl⟩ : syracuseStep 7611853 = 2854445) B2854445
theorem B10149137 : Blo 2003435 10149137 := bstep (se 2 (by rfl) ⟨3805926, by rfl⟩ : syracuseStep 10149137 = 7611853) B7611853
theorem B6766091 : Blo 2003435 6766091 := bstep (se 1 (by rfl) ⟨5074568, by rfl⟩ : syracuseStep 6766091 = 10149137) B10149137
theorem B4510727 : Blo 2003435 4510727 := bstep (se 1 (by rfl) ⟨3383045, by rfl⟩ : syracuseStep 4510727 = 6766091) B6766091
theorem B3007151 : Blo 2003435 3007151 := bstep (se 1 (by rfl) ⟨2255363, by rfl⟩ : syracuseStep 3007151 = 4510727) B4510727
theorem B2004767 : Blo 2003435 2004767 := bstep (se 1 (by rfl) ⟨1503575, by rfl⟩ : syracuseStep 2004767 = 3007151) B3007151
theorem B3007157 : Blo 2003435 3007157 := bbase (se 5 (by rfl) ⟨140960, by rfl⟩ : syracuseStep 3007157 = 281921) (by norm_num)
theorem B2004771 : Blo 2003435 2004771 := bstep (se 1 (by rfl) ⟨1503578, by rfl⟩ : syracuseStep 2004771 = 3007157) B3007157
theorem B5074589 : Blo 2003435 5074589 := bbase (se 3 (by rfl) ⟨951485, by rfl⟩ : syracuseStep 5074589 = 1902971) (by norm_num)
theorem B3383059 : Blo 2003435 3383059 := bstep (se 1 (by rfl) ⟨2537294, by rfl⟩ : syracuseStep 3383059 = 5074589) B5074589
theorem B4510745 : Blo 2003435 4510745 := bstep (se 2 (by rfl) ⟨1691529, by rfl⟩ : syracuseStep 4510745 = 3383059) B3383059
theorem B3007163 : Blo 2003435 3007163 := bstep (se 1 (by rfl) ⟨2255372, by rfl⟩ : syracuseStep 3007163 = 4510745) B4510745
theorem B2004775 : Blo 2003435 2004775 := bstep (se 1 (by rfl) ⟨1503581, by rfl⟩ : syracuseStep 2004775 = 3007163) B3007163
theorem B2255377 : Blo 2003435 2255377 := bbase (se 2 (by rfl) ⟨845766, by rfl⟩ : syracuseStep 2255377 = 1691533) (by norm_num)
theorem B3007169 : Blo 2003435 3007169 := bstep (se 2 (by rfl) ⟨1127688, by rfl⟩ : syracuseStep 3007169 = 2255377) B2255377
theorem B2004779 : Blo 2003435 2004779 := bstep (se 1 (by rfl) ⟨1503584, by rfl⟩ : syracuseStep 2004779 = 3007169) B3007169
theorem B3805957 : Blo 2003435 3805957 := bbase (se 4 (by rfl) ⟨356808, by rfl⟩ : syracuseStep 3805957 = 713617) (by norm_num)
theorem B5074609 : Blo 2003435 5074609 := bstep (se 2 (by rfl) ⟨1902978, by rfl⟩ : syracuseStep 5074609 = 3805957) B3805957
theorem B6766145 : Blo 2003435 6766145 := bstep (se 2 (by rfl) ⟨2537304, by rfl⟩ : syracuseStep 6766145 = 5074609) B5074609
theorem B4510763 : Blo 2003435 4510763 := bstep (se 1 (by rfl) ⟨3383072, by rfl⟩ : syracuseStep 4510763 = 6766145) B6766145
theorem B3007175 : Blo 2003435 3007175 := bstep (se 1 (by rfl) ⟨2255381, by rfl⟩ : syracuseStep 3007175 = 4510763) B4510763
theorem B2004783 : Blo 2003435 2004783 := bstep (se 1 (by rfl) ⟨1503587, by rfl⟩ : syracuseStep 2004783 = 3007175) B3007175
theorem B3007181 : Blo 2003435 3007181 := bbase (se 3 (by rfl) ⟨563846, by rfl⟩ : syracuseStep 3007181 = 1127693) (by norm_num)
theorem B2004787 : Blo 2003435 2004787 := bstep (se 1 (by rfl) ⟨1503590, by rfl⟩ : syracuseStep 2004787 = 3007181) B3007181
theorem B4510781 : Blo 2003435 4510781 := bbase (se 3 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 4510781 = 1691543) (by norm_num)
theorem B3007187 : Blo 2003435 3007187 := bstep (se 1 (by rfl) ⟨2255390, by rfl⟩ : syracuseStep 3007187 = 4510781) B4510781
theorem B2004791 : Blo 2003435 2004791 := bstep (se 1 (by rfl) ⟨1503593, by rfl⟩ : syracuseStep 2004791 = 3007187) B3007187
theorem B3383093 : Blo 2003435 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B2255395 : Blo 2003435 2255395 := bstep (se 1 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 2255395 = 3383093) B3383093
theorem B3007193 : Blo 2003435 3007193 := bstep (se 2 (by rfl) ⟨1127697, by rfl⟩ : syracuseStep 3007193 = 2255395) B2255395
theorem B2004795 : Blo 2003435 2004795 := bstep (se 1 (by rfl) ⟨1503596, by rfl⟩ : syracuseStep 2004795 = 3007193) B3007193
theorem B5708981 : Blo 2003435 5708981 := bbase (se 5 (by rfl) ⟨267608, by rfl⟩ : syracuseStep 5708981 = 535217) (by norm_num)
theorem B15223949 : Blo 2003435 15223949 := bstep (se 3 (by rfl) ⟨2854490, by rfl⟩ : syracuseStep 15223949 = 5708981) B5708981
theorem B10149299 : Blo 2003435 10149299 := bstep (se 1 (by rfl) ⟨7611974, by rfl⟩ : syracuseStep 10149299 = 15223949) B15223949
theorem B6766199 : Blo 2003435 6766199 := bstep (se 1 (by rfl) ⟨5074649, by rfl⟩ : syracuseStep 6766199 = 10149299) B10149299
theorem B4510799 : Blo 2003435 4510799 := bstep (se 1 (by rfl) ⟨3383099, by rfl⟩ : syracuseStep 4510799 = 6766199) B6766199
theorem B3007199 : Blo 2003435 3007199 := bstep (se 1 (by rfl) ⟨2255399, by rfl⟩ : syracuseStep 3007199 = 4510799) B4510799
theorem B2004799 : Blo 2003435 2004799 := bstep (se 1 (by rfl) ⟨1503599, by rfl⟩ : syracuseStep 2004799 = 3007199) B3007199
theorem B3007205 : Blo 2003435 3007205 := bbase (se 4 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 3007205 = 563851) (by norm_num)
theorem B2004803 : Blo 2003435 2004803 := bstep (se 1 (by rfl) ⟨1503602, by rfl⟩ : syracuseStep 2004803 = 3007205) B3007205
theorem B2140877 : Blo 2003435 2140877 := bbase (se 3 (by rfl) ⟨401414, by rfl⟩ : syracuseStep 2140877 = 802829) (by norm_num)
theorem B5709005 : Blo 2003435 5709005 := bstep (se 3 (by rfl) ⟨1070438, by rfl⟩ : syracuseStep 5709005 = 2140877) B2140877
theorem B3806003 : Blo 2003435 3806003 := bstep (se 1 (by rfl) ⟨2854502, by rfl⟩ : syracuseStep 3806003 = 5709005) B5709005
theorem B2537335 : Blo 2003435 2537335 := bstep (se 1 (by rfl) ⟨1903001, by rfl⟩ : syracuseStep 2537335 = 3806003) B3806003
theorem B3383113 : Blo 2003435 3383113 := bstep (se 2 (by rfl) ⟨1268667, by rfl⟩ : syracuseStep 3383113 = 2537335) B2537335
theorem B4510817 : Blo 2003435 4510817 := bstep (se 2 (by rfl) ⟨1691556, by rfl⟩ : syracuseStep 4510817 = 3383113) B3383113
theorem B3007211 : Blo 2003435 3007211 := bstep (se 1 (by rfl) ⟨2255408, by rfl⟩ : syracuseStep 3007211 = 4510817) B4510817
theorem B2004807 : Blo 2003435 2004807 := bstep (se 1 (by rfl) ⟨1503605, by rfl⟩ : syracuseStep 2004807 = 3007211) B3007211
theorem B2255413 : Blo 2003435 2255413 := bbase (se 5 (by rfl) ⟨105722, by rfl⟩ : syracuseStep 2255413 = 211445) (by norm_num)
theorem B3007217 : Blo 2003435 3007217 := bstep (se 2 (by rfl) ⟨1127706, by rfl⟩ : syracuseStep 3007217 = 2255413) B2255413
theorem B2004811 : Blo 2003435 2004811 := bstep (se 1 (by rfl) ⟨1503608, by rfl⟩ : syracuseStep 2004811 = 3007217) B3007217
theorem B2537345 : Blo 2003435 2537345 := bbase (se 2 (by rfl) ⟨951504, by rfl⟩ : syracuseStep 2537345 = 1903009) (by norm_num)
theorem B6766253 : Blo 2003435 6766253 := bstep (se 3 (by rfl) ⟨1268672, by rfl⟩ : syracuseStep 6766253 = 2537345) B2537345
theorem B4510835 : Blo 2003435 4510835 := bstep (se 1 (by rfl) ⟨3383126, by rfl⟩ : syracuseStep 4510835 = 6766253) B6766253
theorem B3007223 : Blo 2003435 3007223 := bstep (se 1 (by rfl) ⟨2255417, by rfl⟩ : syracuseStep 3007223 = 4510835) B4510835
theorem B2004815 : Blo 2003435 2004815 := bstep (se 1 (by rfl) ⟨1503611, by rfl⟩ : syracuseStep 2004815 = 3007223) B3007223
theorem B3007229 : Blo 2003435 3007229 := bbase (se 3 (by rfl) ⟨563855, by rfl⟩ : syracuseStep 3007229 = 1127711) (by norm_num)
theorem B2004819 : Blo 2003435 2004819 := bstep (se 1 (by rfl) ⟨1503614, by rfl⟩ : syracuseStep 2004819 = 3007229) B3007229
theorem B4510853 : Blo 2003435 4510853 := bbase (se 4 (by rfl) ⟨422892, by rfl⟩ : syracuseStep 4510853 = 845785) (by norm_num)
theorem B3007235 : Blo 2003435 3007235 := bstep (se 1 (by rfl) ⟨2255426, by rfl⟩ : syracuseStep 3007235 = 4510853) B4510853
theorem B2004823 : Blo 2003435 2004823 := bstep (se 1 (by rfl) ⟨1503617, by rfl⟩ : syracuseStep 2004823 = 3007235) B3007235
theorem B4281797 : Blo 2003435 4281797 := bbase (se 4 (by rfl) ⟨401418, by rfl⟩ : syracuseStep 4281797 = 802837) (by norm_num)
theorem B2854531 : Blo 2003435 2854531 := bstep (se 1 (by rfl) ⟨2140898, by rfl⟩ : syracuseStep 2854531 = 4281797) B4281797
theorem B3806041 : Blo 2003435 3806041 := bstep (se 2 (by rfl) ⟨1427265, by rfl⟩ : syracuseStep 3806041 = 2854531) B2854531
theorem B5074721 : Blo 2003435 5074721 := bstep (se 2 (by rfl) ⟨1903020, by rfl⟩ : syracuseStep 5074721 = 3806041) B3806041
theorem B3383147 : Blo 2003435 3383147 := bstep (se 1 (by rfl) ⟨2537360, by rfl⟩ : syracuseStep 3383147 = 5074721) B5074721
theorem B2255431 : Blo 2003435 2255431 := bstep (se 1 (by rfl) ⟨1691573, by rfl⟩ : syracuseStep 2255431 = 3383147) B3383147
theorem B3007241 : Blo 2003435 3007241 := bstep (se 2 (by rfl) ⟨1127715, by rfl⟩ : syracuseStep 3007241 = 2255431) B2255431
theorem B2004827 : Blo 2003435 2004827 := bstep (se 1 (by rfl) ⟨1503620, by rfl⟩ : syracuseStep 2004827 = 3007241) B3007241
theorem B10149461 : Blo 2003435 10149461 := bbase (se 8 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 10149461 = 118939) (by norm_num)
theorem B6766307 : Blo 2003435 6766307 := bstep (se 1 (by rfl) ⟨5074730, by rfl⟩ : syracuseStep 6766307 = 10149461) B10149461
theorem B4510871 : Blo 2003435 4510871 := bstep (se 1 (by rfl) ⟨3383153, by rfl⟩ : syracuseStep 4510871 = 6766307) B6766307
theorem B3007247 : Blo 2003435 3007247 := bstep (se 1 (by rfl) ⟨2255435, by rfl⟩ : syracuseStep 3007247 = 4510871) B4510871
theorem B2004831 : Blo 2003435 2004831 := bstep (se 1 (by rfl) ⟨1503623, by rfl⟩ : syracuseStep 2004831 = 3007247) B3007247
theorem B3007253 : Blo 2003435 3007253 := bbase (se 6 (by rfl) ⟨70482, by rfl⟩ : syracuseStep 3007253 = 140965) (by norm_num)
theorem B2004835 : Blo 2003435 2004835 := bstep (se 1 (by rfl) ⟨1503626, by rfl⟩ : syracuseStep 2004835 = 3007253) B3007253
theorem B2032193 : Blo 2003435 2032193 := bbase (se 2 (by rfl) ⟨762072, by rfl⟩ : syracuseStep 2032193 = 1524145) (by norm_num)
theorem B5419181 : Blo 2003435 5419181 := bstep (se 3 (by rfl) ⟨1016096, by rfl⟩ : syracuseStep 5419181 = 2032193) B2032193
theorem B14451149 : Blo 2003435 14451149 := bstep (se 3 (by rfl) ⟨2709590, by rfl⟩ : syracuseStep 14451149 = 5419181) B5419181
theorem B38536397 : Blo 2003435 38536397 := bstep (se 3 (by rfl) ⟨7225574, by rfl⟩ : syracuseStep 38536397 = 14451149) B14451149
theorem B25690931 : Blo 2003435 25690931 := bstep (se 1 (by rfl) ⟨19268198, by rfl⟩ : syracuseStep 25690931 = 38536397) B38536397
theorem B17127287 : Blo 2003435 17127287 := bstep (se 1 (by rfl) ⟨12845465, by rfl⟩ : syracuseStep 17127287 = 25690931) B25690931
theorem B11418191 : Blo 2003435 11418191 := bstep (se 1 (by rfl) ⟨8563643, by rfl⟩ : syracuseStep 11418191 = 17127287) B17127287
theorem B7612127 : Blo 2003435 7612127 := bstep (se 1 (by rfl) ⟨5709095, by rfl⟩ : syracuseStep 7612127 = 11418191) B11418191
theorem B5074751 : Blo 2003435 5074751 := bstep (se 1 (by rfl) ⟨3806063, by rfl⟩ : syracuseStep 5074751 = 7612127) B7612127
theorem B3383167 : Blo 2003435 3383167 := bstep (se 1 (by rfl) ⟨2537375, by rfl⟩ : syracuseStep 3383167 = 5074751) B5074751
theorem B4510889 : Blo 2003435 4510889 := bstep (se 2 (by rfl) ⟨1691583, by rfl⟩ : syracuseStep 4510889 = 3383167) B3383167
theorem B3007259 : Blo 2003435 3007259 := bstep (se 1 (by rfl) ⟨2255444, by rfl⟩ : syracuseStep 3007259 = 4510889) B4510889
theorem B2004839 : Blo 2003435 2004839 := bstep (se 1 (by rfl) ⟨1503629, by rfl⟩ : syracuseStep 2004839 = 3007259) B3007259
theorem B2255449 : Blo 2003435 2255449 := bbase (se 2 (by rfl) ⟨845793, by rfl⟩ : syracuseStep 2255449 = 1691587) (by norm_num)
theorem B3007265 : Blo 2003435 3007265 := bstep (se 2 (by rfl) ⟨1127724, by rfl⟩ : syracuseStep 3007265 = 2255449) B2255449
theorem B2004843 : Blo 2003435 2004843 := bstep (se 1 (by rfl) ⟨1503632, by rfl⟩ : syracuseStep 2004843 = 3007265) B3007265
theorem B18289813 : Blo 2003435 18289813 := bbase (se 6 (by rfl) ⟨428667, by rfl⟩ : syracuseStep 18289813 = 857335) (by norm_num)
theorem B24386417 : Blo 2003435 24386417 := bstep (se 2 (by rfl) ⟨9144906, by rfl⟩ : syracuseStep 24386417 = 18289813) B18289813
theorem B16257611 : Blo 2003435 16257611 := bstep (se 1 (by rfl) ⟨12193208, by rfl⟩ : syracuseStep 16257611 = 24386417) B24386417
theorem B10838407 : Blo 2003435 10838407 := bstep (se 1 (by rfl) ⟨8128805, by rfl⟩ : syracuseStep 10838407 = 16257611) B16257611
theorem B14451209 : Blo 2003435 14451209 := bstep (se 2 (by rfl) ⟨5419203, by rfl⟩ : syracuseStep 14451209 = 10838407) B10838407
theorem B9634139 : Blo 2003435 9634139 := bstep (se 1 (by rfl) ⟨7225604, by rfl⟩ : syracuseStep 9634139 = 14451209) B14451209
theorem B6422759 : Blo 2003435 6422759 := bstep (se 1 (by rfl) ⟨4817069, by rfl⟩ : syracuseStep 6422759 = 9634139) B9634139
theorem B4281839 : Blo 2003435 4281839 := bstep (se 1 (by rfl) ⟨3211379, by rfl⟩ : syracuseStep 4281839 = 6422759) B6422759
theorem B2854559 : Blo 2003435 2854559 := bstep (se 1 (by rfl) ⟨2140919, by rfl⟩ : syracuseStep 2854559 = 4281839) B4281839
theorem B7612157 : Blo 2003435 7612157 := bstep (se 3 (by rfl) ⟨1427279, by rfl⟩ : syracuseStep 7612157 = 2854559) B2854559
theorem B5074771 : Blo 2003435 5074771 := bstep (se 1 (by rfl) ⟨3806078, by rfl⟩ : syracuseStep 5074771 = 7612157) B7612157
theorem B6766361 : Blo 2003435 6766361 := bstep (se 2 (by rfl) ⟨2537385, by rfl⟩ : syracuseStep 6766361 = 5074771) B5074771
theorem B4510907 : Blo 2003435 4510907 := bstep (se 1 (by rfl) ⟨3383180, by rfl⟩ : syracuseStep 4510907 = 6766361) B6766361
theorem B3007271 : Blo 2003435 3007271 := bstep (se 1 (by rfl) ⟨2255453, by rfl⟩ : syracuseStep 3007271 = 4510907) B4510907
theorem B2004847 : Blo 2003435 2004847 := bstep (se 1 (by rfl) ⟨1503635, by rfl⟩ : syracuseStep 2004847 = 3007271) B3007271
theorem B3007277 : Blo 2003435 3007277 := bbase (se 3 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 3007277 = 1127729) (by norm_num)
theorem B2004851 : Blo 2003435 2004851 := bstep (se 1 (by rfl) ⟨1503638, by rfl⟩ : syracuseStep 2004851 = 3007277) B3007277
theorem B4510925 : Blo 2003435 4510925 := bbase (se 3 (by rfl) ⟨845798, by rfl⟩ : syracuseStep 4510925 = 1691597) (by norm_num)
theorem B3007283 : Blo 2003435 3007283 := bstep (se 1 (by rfl) ⟨2255462, by rfl⟩ : syracuseStep 3007283 = 4510925) B4510925
theorem B2004855 : Blo 2003435 2004855 := bstep (se 1 (by rfl) ⟨1503641, by rfl⟩ : syracuseStep 2004855 = 3007283) B3007283
theorem B2537401 : Blo 2003435 2537401 := bbase (se 2 (by rfl) ⟨951525, by rfl⟩ : syracuseStep 2537401 = 1903051) (by norm_num)
theorem B3383201 : Blo 2003435 3383201 := bstep (se 2 (by rfl) ⟨1268700, by rfl⟩ : syracuseStep 3383201 = 2537401) B2537401
theorem B2255467 : Blo 2003435 2255467 := bstep (se 1 (by rfl) ⟨1691600, by rfl⟩ : syracuseStep 2255467 = 3383201) B3383201
theorem B3007289 : Blo 2003435 3007289 := bstep (se 2 (by rfl) ⟨1127733, by rfl⟩ : syracuseStep 3007289 = 2255467) B2255467
theorem B2004859 : Blo 2003435 2004859 := bstep (se 1 (by rfl) ⟨1503644, by rfl⟩ : syracuseStep 2004859 = 3007289) B3007289
theorem B2286245 : Blo 2003435 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B6096653 : Blo 2003435 6096653 := bstep (se 3 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 6096653 = 2286245) B2286245
theorem B4064435 : Blo 2003435 4064435 := bstep (se 1 (by rfl) ⟨3048326, by rfl⟩ : syracuseStep 4064435 = 6096653) B6096653
theorem B2709623 : Blo 2003435 2709623 := bstep (se 1 (by rfl) ⟨2032217, by rfl⟩ : syracuseStep 2709623 = 4064435) B4064435
theorem B7225661 : Blo 2003435 7225661 := bstep (se 3 (by rfl) ⟨1354811, by rfl⟩ : syracuseStep 7225661 = 2709623) B2709623
theorem B4817107 : Blo 2003435 4817107 := bstep (se 1 (by rfl) ⟨3612830, by rfl⟩ : syracuseStep 4817107 = 7225661) B7225661
theorem B6422809 : Blo 2003435 6422809 := bstep (se 2 (by rfl) ⟨2408553, by rfl⟩ : syracuseStep 6422809 = 4817107) B4817107
theorem B8563745 : Blo 2003435 8563745 := bstep (se 2 (by rfl) ⟨3211404, by rfl⟩ : syracuseStep 8563745 = 6422809) B6422809
theorem B22836653 : Blo 2003435 22836653 := bstep (se 3 (by rfl) ⟨4281872, by rfl⟩ : syracuseStep 22836653 = 8563745) B8563745
theorem B15224435 : Blo 2003435 15224435 := bstep (se 1 (by rfl) ⟨11418326, by rfl⟩ : syracuseStep 15224435 = 22836653) B22836653
theorem B10149623 : Blo 2003435 10149623 := bstep (se 1 (by rfl) ⟨7612217, by rfl⟩ : syracuseStep 10149623 = 15224435) B15224435
theorem B6766415 : Blo 2003435 6766415 := bstep (se 1 (by rfl) ⟨5074811, by rfl⟩ : syracuseStep 6766415 = 10149623) B10149623
theorem B4510943 : Blo 2003435 4510943 := bstep (se 1 (by rfl) ⟨3383207, by rfl⟩ : syracuseStep 4510943 = 6766415) B6766415
theorem B3007295 : Blo 2003435 3007295 := bstep (se 1 (by rfl) ⟨2255471, by rfl⟩ : syracuseStep 3007295 = 4510943) B4510943
theorem B2004863 : Blo 2003435 2004863 := bstep (se 1 (by rfl) ⟨1503647, by rfl⟩ : syracuseStep 2004863 = 3007295) B3007295
theorem B3007301 : Blo 2003435 3007301 := bbase (se 4 (by rfl) ⟨281934, by rfl⟩ : syracuseStep 3007301 = 563869) (by norm_num)
theorem B2004867 : Blo 2003435 2004867 := bstep (se 1 (by rfl) ⟨1503650, by rfl⟩ : syracuseStep 2004867 = 3007301) B3007301
theorem B3383221 : Blo 2003435 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B4510961 : Blo 2003435 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B3007307 : Blo 2003435 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B2004871 : Blo 2003435 2004871 := bstep (se 1 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 2004871 = 3007307) B3007307
theorem B2255485 : Blo 2003435 2255485 := bbase (se 3 (by rfl) ⟨422903, by rfl⟩ : syracuseStep 2255485 = 845807) (by norm_num)
theorem B3007313 : Blo 2003435 3007313 := bstep (se 2 (by rfl) ⟨1127742, by rfl⟩ : syracuseStep 3007313 = 2255485) B2255485
theorem B2004875 : Blo 2003435 2004875 := bstep (se 1 (by rfl) ⟨1503656, by rfl⟩ : syracuseStep 2004875 = 3007313) B3007313
theorem B6766469 : Blo 2003435 6766469 := bbase (se 4 (by rfl) ⟨634356, by rfl⟩ : syracuseStep 6766469 = 1268713) (by norm_num)
theorem B4510979 : Blo 2003435 4510979 := bstep (se 1 (by rfl) ⟨3383234, by rfl⟩ : syracuseStep 4510979 = 6766469) B6766469
theorem B3007319 : Blo 2003435 3007319 := bstep (se 1 (by rfl) ⟨2255489, by rfl⟩ : syracuseStep 3007319 = 4510979) B4510979
theorem B2004879 : Blo 2003435 2004879 := bstep (se 1 (by rfl) ⟨1503659, by rfl⟩ : syracuseStep 2004879 = 3007319) B3007319
theorem B3007325 : Blo 2003435 3007325 := bbase (se 3 (by rfl) ⟨563873, by rfl⟩ : syracuseStep 3007325 = 1127747) (by norm_num)
theorem B2004883 : Blo 2003435 2004883 := bstep (se 1 (by rfl) ⟨1503662, by rfl⟩ : syracuseStep 2004883 = 3007325) B3007325
theorem B4510997 : Blo 2003435 4510997 := bbase (se 6 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 4510997 = 211453) (by norm_num)
theorem B3007331 : Blo 2003435 3007331 := bstep (se 1 (by rfl) ⟨2255498, by rfl⟩ : syracuseStep 3007331 = 4510997) B4510997
theorem B2004887 : Blo 2003435 2004887 := bstep (se 1 (by rfl) ⟨1503665, by rfl⟩ : syracuseStep 2004887 = 3007331) B3007331
theorem B7612325 : Blo 2003435 7612325 := bbase (se 4 (by rfl) ⟨713655, by rfl⟩ : syracuseStep 7612325 = 1427311) (by norm_num)
theorem B5074883 : Blo 2003435 5074883 := bstep (se 1 (by rfl) ⟨3806162, by rfl⟩ : syracuseStep 5074883 = 7612325) B7612325
theorem B3383255 : Blo 2003435 3383255 := bstep (se 1 (by rfl) ⟨2537441, by rfl⟩ : syracuseStep 3383255 = 5074883) B5074883
theorem B2255503 : Blo 2003435 2255503 := bstep (se 1 (by rfl) ⟨1691627, by rfl⟩ : syracuseStep 2255503 = 3383255) B3383255
theorem B3007337 : Blo 2003435 3007337 := bstep (se 2 (by rfl) ⟨1127751, by rfl⟩ : syracuseStep 3007337 = 2255503) B2255503
theorem B2004891 : Blo 2003435 2004891 := bstep (se 1 (by rfl) ⟨1503668, by rfl⟩ : syracuseStep 2004891 = 3007337) B3007337
theorem B4281941 : Blo 2003435 4281941 := bbase (se 8 (by rfl) ⟨25089, by rfl⟩ : syracuseStep 4281941 = 50179) (by norm_num)
theorem B11418509 : Blo 2003435 11418509 := bstep (se 3 (by rfl) ⟨2140970, by rfl⟩ : syracuseStep 11418509 = 4281941) B4281941
theorem B7612339 : Blo 2003435 7612339 := bstep (se 1 (by rfl) ⟨5709254, by rfl⟩ : syracuseStep 7612339 = 11418509) B11418509
theorem B10149785 : Blo 2003435 10149785 := bstep (se 2 (by rfl) ⟨3806169, by rfl⟩ : syracuseStep 10149785 = 7612339) B7612339
theorem B6766523 : Blo 2003435 6766523 := bstep (se 1 (by rfl) ⟨5074892, by rfl⟩ : syracuseStep 6766523 = 10149785) B10149785
theorem B4511015 : Blo 2003435 4511015 := bstep (se 1 (by rfl) ⟨3383261, by rfl⟩ : syracuseStep 4511015 = 6766523) B6766523
theorem B3007343 : Blo 2003435 3007343 := bstep (se 1 (by rfl) ⟨2255507, by rfl⟩ : syracuseStep 3007343 = 4511015) B4511015
theorem B2004895 : Blo 2003435 2004895 := bstep (se 1 (by rfl) ⟨1503671, by rfl⟩ : syracuseStep 2004895 = 3007343) B3007343
theorem B3007349 : Blo 2003435 3007349 := bbase (se 5 (by rfl) ⟨140969, by rfl⟩ : syracuseStep 3007349 = 281939) (by norm_num)
theorem B2004899 : Blo 2003435 2004899 := bstep (se 1 (by rfl) ⟨1503674, by rfl⟩ : syracuseStep 2004899 = 3007349) B3007349
theorem B10288309 : Blo 2003435 10288309 := bbase (se 5 (by rfl) ⟨482264, by rfl⟩ : syracuseStep 10288309 = 964529) (by norm_num)
theorem B13717745 : Blo 2003435 13717745 := bstep (se 2 (by rfl) ⟨5144154, by rfl⟩ : syracuseStep 13717745 = 10288309) B10288309
theorem B9145163 : Blo 2003435 9145163 := bstep (se 1 (by rfl) ⟨6858872, by rfl⟩ : syracuseStep 9145163 = 13717745) B13717745
theorem B24387101 : Blo 2003435 24387101 := bstep (se 3 (by rfl) ⟨4572581, by rfl⟩ : syracuseStep 24387101 = 9145163) B9145163
theorem B16258067 : Blo 2003435 16258067 := bstep (se 1 (by rfl) ⟨12193550, by rfl⟩ : syracuseStep 16258067 = 24387101) B24387101
theorem B10838711 : Blo 2003435 10838711 := bstep (se 1 (by rfl) ⟨8129033, by rfl⟩ : syracuseStep 10838711 = 16258067) B16258067
theorem B7225807 : Blo 2003435 7225807 := bstep (se 1 (by rfl) ⟨5419355, by rfl⟩ : syracuseStep 7225807 = 10838711) B10838711
theorem B9634409 : Blo 2003435 9634409 := bstep (se 2 (by rfl) ⟨3612903, by rfl⟩ : syracuseStep 9634409 = 7225807) B7225807
theorem B6422939 : Blo 2003435 6422939 := bstep (se 1 (by rfl) ⟨4817204, by rfl⟩ : syracuseStep 6422939 = 9634409) B9634409
theorem B4281959 : Blo 2003435 4281959 := bstep (se 1 (by rfl) ⟨3211469, by rfl⟩ : syracuseStep 4281959 = 6422939) B6422939
theorem B2854639 : Blo 2003435 2854639 := bstep (se 1 (by rfl) ⟨2140979, by rfl⟩ : syracuseStep 2854639 = 4281959) B4281959
theorem B3806185 : Blo 2003435 3806185 := bstep (se 2 (by rfl) ⟨1427319, by rfl⟩ : syracuseStep 3806185 = 2854639) B2854639
theorem B5074913 : Blo 2003435 5074913 := bstep (se 2 (by rfl) ⟨1903092, by rfl⟩ : syracuseStep 5074913 = 3806185) B3806185
theorem B3383275 : Blo 2003435 3383275 := bstep (se 1 (by rfl) ⟨2537456, by rfl⟩ : syracuseStep 3383275 = 5074913) B5074913
theorem B4511033 : Blo 2003435 4511033 := bstep (se 2 (by rfl) ⟨1691637, by rfl⟩ : syracuseStep 4511033 = 3383275) B3383275
theorem B3007355 : Blo 2003435 3007355 := bstep (se 1 (by rfl) ⟨2255516, by rfl⟩ : syracuseStep 3007355 = 4511033) B4511033
theorem B2004903 : Blo 2003435 2004903 := bstep (se 1 (by rfl) ⟨1503677, by rfl⟩ : syracuseStep 2004903 = 3007355) B3007355
theorem B2255521 : Blo 2003435 2255521 := bbase (se 2 (by rfl) ⟨845820, by rfl⟩ : syracuseStep 2255521 = 1691641) (by norm_num)
theorem B3007361 : Blo 2003435 3007361 := bstep (se 2 (by rfl) ⟨1127760, by rfl⟩ : syracuseStep 3007361 = 2255521) B2255521
theorem B2004907 : Blo 2003435 2004907 := bstep (se 1 (by rfl) ⟨1503680, by rfl⟩ : syracuseStep 2004907 = 3007361) B3007361
theorem B5074933 : Blo 2003435 5074933 := bbase (se 5 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 5074933 = 475775) (by norm_num)
theorem B6766577 : Blo 2003435 6766577 := bstep (se 2 (by rfl) ⟨2537466, by rfl⟩ : syracuseStep 6766577 = 5074933) B5074933
theorem B4511051 : Blo 2003435 4511051 := bstep (se 1 (by rfl) ⟨3383288, by rfl⟩ : syracuseStep 4511051 = 6766577) B6766577
theorem B3007367 : Blo 2003435 3007367 := bstep (se 1 (by rfl) ⟨2255525, by rfl⟩ : syracuseStep 3007367 = 4511051) B4511051
theorem B2004911 : Blo 2003435 2004911 := bstep (se 1 (by rfl) ⟨1503683, by rfl⟩ : syracuseStep 2004911 = 3007367) B3007367
theorem B3007373 : Blo 2003435 3007373 := bbase (se 3 (by rfl) ⟨563882, by rfl⟩ : syracuseStep 3007373 = 1127765) (by norm_num)
theorem B2004915 : Blo 2003435 2004915 := bstep (se 1 (by rfl) ⟨1503686, by rfl⟩ : syracuseStep 2004915 = 3007373) B3007373
theorem B4511069 : Blo 2003435 4511069 := bbase (se 3 (by rfl) ⟨845825, by rfl⟩ : syracuseStep 4511069 = 1691651) (by norm_num)
theorem B3007379 : Blo 2003435 3007379 := bstep (se 1 (by rfl) ⟨2255534, by rfl⟩ : syracuseStep 3007379 = 4511069) B4511069
theorem B2004919 : Blo 2003435 2004919 := bstep (se 1 (by rfl) ⟨1503689, by rfl⟩ : syracuseStep 2004919 = 3007379) B3007379
theorem B3383309 : Blo 2003435 3383309 := bbase (se 3 (by rfl) ⟨634370, by rfl⟩ : syracuseStep 3383309 = 1268741) (by norm_num)
theorem B2255539 : Blo 2003435 2255539 := bstep (se 1 (by rfl) ⟨1691654, by rfl⟩ : syracuseStep 2255539 = 3383309) B3383309
theorem B3007385 : Blo 2003435 3007385 := bstep (se 2 (by rfl) ⟨1127769, by rfl⟩ : syracuseStep 3007385 = 2255539) B2255539
theorem B2004923 : Blo 2003435 2004923 := bstep (se 1 (by rfl) ⟨1503692, by rfl⟩ : syracuseStep 2004923 = 3007385) B3007385
theorem B4817261 : Blo 2003435 4817261 := bbase (se 3 (by rfl) ⟨903236, by rfl⟩ : syracuseStep 4817261 = 1806473) (by norm_num)
theorem B3211507 : Blo 2003435 3211507 := bstep (se 1 (by rfl) ⟨2408630, by rfl⟩ : syracuseStep 3211507 = 4817261) B4817261
theorem B17128037 : Blo 2003435 17128037 := bstep (se 4 (by rfl) ⟨1605753, by rfl⟩ : syracuseStep 17128037 = 3211507) B3211507
theorem B11418691 : Blo 2003435 11418691 := bstep (se 1 (by rfl) ⟨8564018, by rfl⟩ : syracuseStep 11418691 = 17128037) B17128037
theorem B15224921 : Blo 2003435 15224921 := bstep (se 2 (by rfl) ⟨5709345, by rfl⟩ : syracuseStep 15224921 = 11418691) B11418691
theorem B10149947 : Blo 2003435 10149947 := bstep (se 1 (by rfl) ⟨7612460, by rfl⟩ : syracuseStep 10149947 = 15224921) B15224921
theorem B6766631 : Blo 2003435 6766631 := bstep (se 1 (by rfl) ⟨5074973, by rfl⟩ : syracuseStep 6766631 = 10149947) B10149947
theorem B4511087 : Blo 2003435 4511087 := bstep (se 1 (by rfl) ⟨3383315, by rfl⟩ : syracuseStep 4511087 = 6766631) B6766631
theorem B3007391 : Blo 2003435 3007391 := bstep (se 1 (by rfl) ⟨2255543, by rfl⟩ : syracuseStep 3007391 = 4511087) B4511087
theorem B2004927 : Blo 2003435 2004927 := bstep (se 1 (by rfl) ⟨1503695, by rfl⟩ : syracuseStep 2004927 = 3007391) B3007391
theorem B3007397 : Blo 2003435 3007397 := bbase (se 4 (by rfl) ⟨281943, by rfl⟩ : syracuseStep 3007397 = 563887) (by norm_num)
theorem B2004931 : Blo 2003435 2004931 := bstep (se 1 (by rfl) ⟨1503698, by rfl⟩ : syracuseStep 2004931 = 3007397) B3007397
theorem B2537497 : Blo 2003435 2537497 := bbase (se 2 (by rfl) ⟨951561, by rfl⟩ : syracuseStep 2537497 = 1903123) (by norm_num)
theorem B3383329 : Blo 2003435 3383329 := bstep (se 2 (by rfl) ⟨1268748, by rfl⟩ : syracuseStep 3383329 = 2537497) B2537497
theorem B4511105 : Blo 2003435 4511105 := bstep (se 2 (by rfl) ⟨1691664, by rfl⟩ : syracuseStep 4511105 = 3383329) B3383329
theorem B3007403 : Blo 2003435 3007403 := bstep (se 1 (by rfl) ⟨2255552, by rfl⟩ : syracuseStep 3007403 = 4511105) B4511105
theorem B2004935 : Blo 2003435 2004935 := bstep (se 1 (by rfl) ⟨1503701, by rfl⟩ : syracuseStep 2004935 = 3007403) B3007403
theorem B2255557 : Blo 2003435 2255557 := bbase (se 4 (by rfl) ⟨211458, by rfl⟩ : syracuseStep 2255557 = 422917) (by norm_num)
theorem B3007409 : Blo 2003435 3007409 := bstep (se 2 (by rfl) ⟨1127778, by rfl⟩ : syracuseStep 3007409 = 2255557) B2255557
theorem B2004939 : Blo 2003435 2004939 := bstep (se 1 (by rfl) ⟨1503704, by rfl⟩ : syracuseStep 2004939 = 3007409) B3007409
theorem B3806261 : Blo 2003435 3806261 := bbase (se 5 (by rfl) ⟨178418, by rfl⟩ : syracuseStep 3806261 = 356837) (by norm_num)
theorem B2537507 : Blo 2003435 2537507 := bstep (se 1 (by rfl) ⟨1903130, by rfl⟩ : syracuseStep 2537507 = 3806261) B3806261
theorem B6766685 : Blo 2003435 6766685 := bstep (se 3 (by rfl) ⟨1268753, by rfl⟩ : syracuseStep 6766685 = 2537507) B2537507
theorem B4511123 : Blo 2003435 4511123 := bstep (se 1 (by rfl) ⟨3383342, by rfl⟩ : syracuseStep 4511123 = 6766685) B6766685
theorem B3007415 : Blo 2003435 3007415 := bstep (se 1 (by rfl) ⟨2255561, by rfl⟩ : syracuseStep 3007415 = 4511123) B4511123
theorem B2004943 : Blo 2003435 2004943 := bstep (se 1 (by rfl) ⟨1503707, by rfl⟩ : syracuseStep 2004943 = 3007415) B3007415
theorem B3007421 : Blo 2003435 3007421 := bbase (se 3 (by rfl) ⟨563891, by rfl⟩ : syracuseStep 3007421 = 1127783) (by norm_num)
theorem B2004947 : Blo 2003435 2004947 := bstep (se 1 (by rfl) ⟨1503710, by rfl⟩ : syracuseStep 2004947 = 3007421) B3007421
theorem B4511141 : Blo 2003435 4511141 := bbase (se 4 (by rfl) ⟨422919, by rfl⟩ : syracuseStep 4511141 = 845839) (by norm_num)
theorem B3007427 : Blo 2003435 3007427 := bstep (se 1 (by rfl) ⟨2255570, by rfl⟩ : syracuseStep 3007427 = 4511141) B4511141
theorem B2004951 : Blo 2003435 2004951 := bstep (se 1 (by rfl) ⟨1503713, by rfl⟩ : syracuseStep 2004951 = 3007427) B3007427
theorem B5075045 : Blo 2003435 5075045 := bbase (se 4 (by rfl) ⟨475785, by rfl⟩ : syracuseStep 5075045 = 951571) (by norm_num)
theorem B3383363 : Blo 2003435 3383363 := bstep (se 1 (by rfl) ⟨2537522, by rfl⟩ : syracuseStep 3383363 = 5075045) B5075045
theorem B2255575 : Blo 2003435 2255575 := bstep (se 1 (by rfl) ⟨1691681, by rfl⟩ : syracuseStep 2255575 = 3383363) B3383363
theorem B3007433 : Blo 2003435 3007433 := bstep (se 2 (by rfl) ⟨1127787, by rfl⟩ : syracuseStep 3007433 = 2255575) B2255575
theorem B2004955 : Blo 2003435 2004955 := bstep (se 1 (by rfl) ⟨1503716, by rfl⟩ : syracuseStep 2004955 = 3007433) B3007433
theorem B3429533 : Blo 2003435 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B2286355 : Blo 2003435 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B3048473 : Blo 2003435 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B8129261 : Blo 2003435 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B5419507 : Blo 2003435 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B7226009 : Blo 2003435 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B4817339 : Blo 2003435 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B3211559 : Blo 2003435 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B2141039 : Blo 2003435 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B5709437 : Blo 2003435 5709437 := bstep (se 3 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 5709437 = 2141039) B2141039
theorem B3806291 : Blo 2003435 3806291 := bstep (se 1 (by rfl) ⟨2854718, by rfl⟩ : syracuseStep 3806291 = 5709437) B5709437
theorem B10150109 : Blo 2003435 10150109 := bstep (se 3 (by rfl) ⟨1903145, by rfl⟩ : syracuseStep 10150109 = 3806291) B3806291
theorem B6766739 : Blo 2003435 6766739 := bstep (se 1 (by rfl) ⟨5075054, by rfl⟩ : syracuseStep 6766739 = 10150109) B10150109
theorem B4511159 : Blo 2003435 4511159 := bstep (se 1 (by rfl) ⟨3383369, by rfl⟩ : syracuseStep 4511159 = 6766739) B6766739
theorem B3007439 : Blo 2003435 3007439 := bstep (se 1 (by rfl) ⟨2255579, by rfl⟩ : syracuseStep 3007439 = 4511159) B4511159
theorem B2004959 : Blo 2003435 2004959 := bstep (se 1 (by rfl) ⟨1503719, by rfl⟩ : syracuseStep 2004959 = 3007439) B3007439
theorem B3007445 : Blo 2003435 3007445 := bbase (se 7 (by rfl) ⟨35243, by rfl⟩ : syracuseStep 3007445 = 70487) (by norm_num)
theorem B2004963 : Blo 2003435 2004963 := bstep (se 1 (by rfl) ⟨1503722, by rfl⟩ : syracuseStep 2004963 = 3007445) B3007445
theorem B7612613 : Blo 2003435 7612613 := bbase (se 4 (by rfl) ⟨713682, by rfl⟩ : syracuseStep 7612613 = 1427365) (by norm_num)
theorem B5075075 : Blo 2003435 5075075 := bstep (se 1 (by rfl) ⟨3806306, by rfl⟩ : syracuseStep 5075075 = 7612613) B7612613
theorem B3383383 : Blo 2003435 3383383 := bstep (se 1 (by rfl) ⟨2537537, by rfl⟩ : syracuseStep 3383383 = 5075075) B5075075
theorem B4511177 : Blo 2003435 4511177 := bstep (se 2 (by rfl) ⟨1691691, by rfl⟩ : syracuseStep 4511177 = 3383383) B3383383
theorem B3007451 : Blo 2003435 3007451 := bstep (se 1 (by rfl) ⟨2255588, by rfl⟩ : syracuseStep 3007451 = 4511177) B4511177
theorem B2004967 : Blo 2003435 2004967 := bstep (se 1 (by rfl) ⟨1503725, by rfl⟩ : syracuseStep 2004967 = 3007451) B3007451
theorem B2255593 : Blo 2003435 2255593 := bbase (se 2 (by rfl) ⟨845847, by rfl⟩ : syracuseStep 2255593 = 1691695) (by norm_num)
theorem B3007457 : Blo 2003435 3007457 := bstep (se 2 (by rfl) ⟨1127796, by rfl⟩ : syracuseStep 3007457 = 2255593) B2255593
theorem B2004971 : Blo 2003435 2004971 := bstep (se 1 (by rfl) ⟨1503728, by rfl⟩ : syracuseStep 2004971 = 3007457) B3007457
theorem B11418965 : Blo 2003435 11418965 := bbase (se 11 (by rfl) ⟨8363, by rfl⟩ : syracuseStep 11418965 = 16727) (by norm_num)
theorem B7612643 : Blo 2003435 7612643 := bstep (se 1 (by rfl) ⟨5709482, by rfl⟩ : syracuseStep 7612643 = 11418965) B11418965
theorem B5075095 : Blo 2003435 5075095 := bstep (se 1 (by rfl) ⟨3806321, by rfl⟩ : syracuseStep 5075095 = 7612643) B7612643
theorem B6766793 : Blo 2003435 6766793 := bstep (se 2 (by rfl) ⟨2537547, by rfl⟩ : syracuseStep 6766793 = 5075095) B5075095
theorem B4511195 : Blo 2003435 4511195 := bstep (se 1 (by rfl) ⟨3383396, by rfl⟩ : syracuseStep 4511195 = 6766793) B6766793
theorem B3007463 : Blo 2003435 3007463 := bstep (se 1 (by rfl) ⟨2255597, by rfl⟩ : syracuseStep 3007463 = 4511195) B4511195
theorem B2004975 : Blo 2003435 2004975 := bstep (se 1 (by rfl) ⟨1503731, by rfl⟩ : syracuseStep 2004975 = 3007463) B3007463
theorem B3007469 : Blo 2003435 3007469 := bbase (se 3 (by rfl) ⟨563900, by rfl⟩ : syracuseStep 3007469 = 1127801) (by norm_num)
theorem B2004979 : Blo 2003435 2004979 := bstep (se 1 (by rfl) ⟨1503734, by rfl⟩ : syracuseStep 2004979 = 3007469) B3007469
theorem B4511213 : Blo 2003435 4511213 := bbase (se 3 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 4511213 = 1691705) (by norm_num)
theorem B3007475 : Blo 2003435 3007475 := bstep (se 1 (by rfl) ⟨2255606, by rfl⟩ : syracuseStep 3007475 = 4511213) B4511213
theorem B2004983 : Blo 2003435 2004983 := bstep (se 1 (by rfl) ⟨1503737, by rfl⟩ : syracuseStep 2004983 = 3007475) B3007475
theorem B19532533 : Blo 2003435 19532533 := bbase (se 5 (by rfl) ⟨915587, by rfl⟩ : syracuseStep 19532533 = 1831175) (by norm_num)
theorem B26043377 : Blo 2003435 26043377 := bstep (se 2 (by rfl) ⟨9766266, by rfl⟩ : syracuseStep 26043377 = 19532533) B19532533
theorem B69449005 : Blo 2003435 69449005 := bstep (se 3 (by rfl) ⟨13021688, by rfl⟩ : syracuseStep 69449005 = 26043377) B26043377
theorem B92598673 : Blo 2003435 92598673 := bstep (se 2 (by rfl) ⟨34724502, by rfl⟩ : syracuseStep 92598673 = 69449005) B69449005
theorem B123464897 : Blo 2003435 123464897 := bstep (se 2 (by rfl) ⟨46299336, by rfl⟩ : syracuseStep 123464897 = 92598673) B92598673
theorem B82309931 : Blo 2003435 82309931 := bstep (se 1 (by rfl) ⟨61732448, by rfl⟩ : syracuseStep 82309931 = 123464897) B123464897
theorem B54873287 : Blo 2003435 54873287 := bstep (se 1 (by rfl) ⟨41154965, by rfl⟩ : syracuseStep 54873287 = 82309931) B82309931
theorem B36582191 : Blo 2003435 36582191 := bstep (se 1 (by rfl) ⟨27436643, by rfl⟩ : syracuseStep 36582191 = 54873287) B54873287
theorem B24388127 : Blo 2003435 24388127 := bstep (se 1 (by rfl) ⟨18291095, by rfl⟩ : syracuseStep 24388127 = 36582191) B36582191
theorem B16258751 : Blo 2003435 16258751 := bstep (se 1 (by rfl) ⟨12194063, by rfl⟩ : syracuseStep 16258751 = 24388127) B24388127
theorem B10839167 : Blo 2003435 10839167 := bstep (se 1 (by rfl) ⟨8129375, by rfl⟩ : syracuseStep 10839167 = 16258751) B16258751
theorem B7226111 : Blo 2003435 7226111 := bstep (se 1 (by rfl) ⟨5419583, by rfl⟩ : syracuseStep 7226111 = 10839167) B10839167
theorem B4817407 : Blo 2003435 4817407 := bstep (se 1 (by rfl) ⟨3613055, by rfl⟩ : syracuseStep 4817407 = 7226111) B7226111
theorem B6423209 : Blo 2003435 6423209 := bstep (se 2 (by rfl) ⟨2408703, by rfl⟩ : syracuseStep 6423209 = 4817407) B4817407
theorem B4282139 : Blo 2003435 4282139 := bstep (se 1 (by rfl) ⟨3211604, by rfl⟩ : syracuseStep 4282139 = 6423209) B6423209
theorem B2854759 : Blo 2003435 2854759 := bstep (se 1 (by rfl) ⟨2141069, by rfl⟩ : syracuseStep 2854759 = 4282139) B4282139
theorem B3806345 : Blo 2003435 3806345 := bstep (se 2 (by rfl) ⟨1427379, by rfl⟩ : syracuseStep 3806345 = 2854759) B2854759
theorem B2537563 : Blo 2003435 2537563 := bstep (se 1 (by rfl) ⟨1903172, by rfl⟩ : syracuseStep 2537563 = 3806345) B3806345
theorem B3383417 : Blo 2003435 3383417 := bstep (se 2 (by rfl) ⟨1268781, by rfl⟩ : syracuseStep 3383417 = 2537563) B2537563
theorem B2255611 : Blo 2003435 2255611 := bstep (se 1 (by rfl) ⟨1691708, by rfl⟩ : syracuseStep 2255611 = 3383417) B3383417
theorem B3007481 : Blo 2003435 3007481 := bstep (se 2 (by rfl) ⟨1127805, by rfl⟩ : syracuseStep 3007481 = 2255611) B2255611
theorem B2004987 : Blo 2003435 2004987 := bstep (se 1 (by rfl) ⟨1503740, by rfl⟩ : syracuseStep 2004987 = 3007481) B3007481
theorem B10288757 : Blo 2003435 10288757 := bbase (se 5 (by rfl) ⟨482285, by rfl⟩ : syracuseStep 10288757 = 964571) (by norm_num)
theorem B6859171 : Blo 2003435 6859171 := bstep (se 1 (by rfl) ⟨5144378, by rfl⟩ : syracuseStep 6859171 = 10288757) B10288757
theorem B9145561 : Blo 2003435 9145561 := bstep (se 2 (by rfl) ⟨3429585, by rfl⟩ : syracuseStep 9145561 = 6859171) B6859171
theorem B12194081 : Blo 2003435 12194081 := bstep (se 2 (by rfl) ⟨4572780, by rfl⟩ : syracuseStep 12194081 = 9145561) B9145561
theorem B8129387 : Blo 2003435 8129387 := bstep (se 1 (by rfl) ⟨6097040, by rfl⟩ : syracuseStep 8129387 = 12194081) B12194081
theorem B5419591 : Blo 2003435 5419591 := bstep (se 1 (by rfl) ⟨4064693, by rfl⟩ : syracuseStep 5419591 = 8129387) B8129387
theorem B115617941 : Blo 2003435 115617941 := bstep (se 6 (by rfl) ⟨2709795, by rfl⟩ : syracuseStep 115617941 = 5419591) B5419591
theorem B77078627 : Blo 2003435 77078627 := bstep (se 1 (by rfl) ⟨57808970, by rfl⟩ : syracuseStep 77078627 = 115617941) B115617941
theorem B51385751 : Blo 2003435 51385751 := bstep (se 1 (by rfl) ⟨38539313, by rfl⟩ : syracuseStep 51385751 = 77078627) B77078627
theorem B34257167 : Blo 2003435 34257167 := bstep (se 1 (by rfl) ⟨25692875, by rfl⟩ : syracuseStep 34257167 = 51385751) B51385751
theorem B22838111 : Blo 2003435 22838111 := bstep (se 1 (by rfl) ⟨17128583, by rfl⟩ : syracuseStep 22838111 = 34257167) B34257167
theorem B15225407 : Blo 2003435 15225407 := bstep (se 1 (by rfl) ⟨11419055, by rfl⟩ : syracuseStep 15225407 = 22838111) B22838111
theorem B10150271 : Blo 2003435 10150271 := bstep (se 1 (by rfl) ⟨7612703, by rfl⟩ : syracuseStep 10150271 = 15225407) B15225407
theorem B6766847 : Blo 2003435 6766847 := bstep (se 1 (by rfl) ⟨5075135, by rfl⟩ : syracuseStep 6766847 = 10150271) B10150271
theorem B4511231 : Blo 2003435 4511231 := bstep (se 1 (by rfl) ⟨3383423, by rfl⟩ : syracuseStep 4511231 = 6766847) B6766847
theorem B3007487 : Blo 2003435 3007487 := bstep (se 1 (by rfl) ⟨2255615, by rfl⟩ : syracuseStep 3007487 = 4511231) B4511231
theorem B2004991 : Blo 2003435 2004991 := bstep (se 1 (by rfl) ⟨1503743, by rfl⟩ : syracuseStep 2004991 = 3007487) B3007487
theorem B3007493 : Blo 2003435 3007493 := bbase (se 4 (by rfl) ⟨281952, by rfl⟩ : syracuseStep 3007493 = 563905) (by norm_num)
theorem B2004995 : Blo 2003435 2004995 := bstep (se 1 (by rfl) ⟨1503746, by rfl⟩ : syracuseStep 2004995 = 3007493) B3007493
theorem B3383437 : Blo 2003435 3383437 := bbase (se 3 (by rfl) ⟨634394, by rfl⟩ : syracuseStep 3383437 = 1268789) (by norm_num)
theorem B4511249 : Blo 2003435 4511249 := bstep (se 2 (by rfl) ⟨1691718, by rfl⟩ : syracuseStep 4511249 = 3383437) B3383437
theorem B3007499 : Blo 2003435 3007499 := bstep (se 1 (by rfl) ⟨2255624, by rfl⟩ : syracuseStep 3007499 = 4511249) B4511249
theorem B2004999 : Blo 2003435 2004999 := bstep (se 1 (by rfl) ⟨1503749, by rfl⟩ : syracuseStep 2004999 = 3007499) B3007499
theorem B2255629 : Blo 2003435 2255629 := bbase (se 3 (by rfl) ⟨422930, by rfl⟩ : syracuseStep 2255629 = 845861) (by norm_num)
theorem B3007505 : Blo 2003435 3007505 := bstep (se 2 (by rfl) ⟨1127814, by rfl⟩ : syracuseStep 3007505 = 2255629) B2255629
theorem B2005003 : Blo 2003435 2005003 := bstep (se 1 (by rfl) ⟨1503752, by rfl⟩ : syracuseStep 2005003 = 3007505) B3007505
theorem B6766901 : Blo 2003435 6766901 := bbase (se 5 (by rfl) ⟨317198, by rfl⟩ : syracuseStep 6766901 = 634397) (by norm_num)
theorem B4511267 : Blo 2003435 4511267 := bstep (se 1 (by rfl) ⟨3383450, by rfl⟩ : syracuseStep 4511267 = 6766901) B6766901
theorem B3007511 : Blo 2003435 3007511 := bstep (se 1 (by rfl) ⟨2255633, by rfl⟩ : syracuseStep 3007511 = 4511267) B4511267
theorem B2005007 : Blo 2003435 2005007 := bstep (se 1 (by rfl) ⟨1503755, by rfl⟩ : syracuseStep 2005007 = 3007511) B3007511
theorem B3007517 : Blo 2003435 3007517 := bbase (se 3 (by rfl) ⟨563909, by rfl⟩ : syracuseStep 3007517 = 1127819) (by norm_num)
theorem B2005011 : Blo 2003435 2005011 := bstep (se 1 (by rfl) ⟨1503758, by rfl⟩ : syracuseStep 2005011 = 3007517) B3007517
theorem B4511285 : Blo 2003435 4511285 := bbase (se 5 (by rfl) ⟨211466, by rfl⟩ : syracuseStep 4511285 = 422933) (by norm_num)
theorem B3007523 : Blo 2003435 3007523 := bstep (se 1 (by rfl) ⟨2255642, by rfl⟩ : syracuseStep 3007523 = 4511285) B4511285
theorem B2005015 : Blo 2003435 2005015 := bstep (se 1 (by rfl) ⟨1503761, by rfl⟩ : syracuseStep 2005015 = 3007523) B3007523
theorem B5419669 : Blo 2003435 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B7226225 : Blo 2003435 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B4817483 : Blo 2003435 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B3211655 : Blo 2003435 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B8564413 : Blo 2003435 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B11419217 : Blo 2003435 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B7612811 : Blo 2003435 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B5075207 : Blo 2003435 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B3383471 : Blo 2003435 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B2255647 : Blo 2003435 2255647 := bstep (se 1 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 2255647 = 3383471) B3383471
theorem B3007529 : Blo 2003435 3007529 := bstep (se 2 (by rfl) ⟨1127823, by rfl⟩ : syracuseStep 3007529 = 2255647) B2255647
theorem B2005019 : Blo 2003435 2005019 := bstep (se 1 (by rfl) ⟨1503764, by rfl⟩ : syracuseStep 2005019 = 3007529) B3007529
theorem B3211661 : Blo 2003435 3211661 := bbase (se 3 (by rfl) ⟨602186, by rfl⟩ : syracuseStep 3211661 = 1204373) (by norm_num)
theorem B8564429 : Blo 2003435 8564429 := bstep (se 3 (by rfl) ⟨1605830, by rfl⟩ : syracuseStep 8564429 = 3211661) B3211661
theorem B5709619 : Blo 2003435 5709619 := bstep (se 1 (by rfl) ⟨4282214, by rfl⟩ : syracuseStep 5709619 = 8564429) B8564429
theorem B7612825 : Blo 2003435 7612825 := bstep (se 2 (by rfl) ⟨2854809, by rfl⟩ : syracuseStep 7612825 = 5709619) B5709619
theorem B10150433 : Blo 2003435 10150433 := bstep (se 2 (by rfl) ⟨3806412, by rfl⟩ : syracuseStep 10150433 = 7612825) B7612825
theorem B6766955 : Blo 2003435 6766955 := bstep (se 1 (by rfl) ⟨5075216, by rfl⟩ : syracuseStep 6766955 = 10150433) B10150433
theorem B4511303 : Blo 2003435 4511303 := bstep (se 1 (by rfl) ⟨3383477, by rfl⟩ : syracuseStep 4511303 = 6766955) B6766955
theorem B3007535 : Blo 2003435 3007535 := bstep (se 1 (by rfl) ⟨2255651, by rfl⟩ : syracuseStep 3007535 = 4511303) B4511303
theorem B2005023 : Blo 2003435 2005023 := bstep (se 1 (by rfl) ⟨1503767, by rfl⟩ : syracuseStep 2005023 = 3007535) B3007535
theorem B3007541 : Blo 2003435 3007541 := bbase (se 5 (by rfl) ⟨140978, by rfl⟩ : syracuseStep 3007541 = 281957) (by norm_num)
theorem B2005027 : Blo 2003435 2005027 := bstep (se 1 (by rfl) ⟨1503770, by rfl⟩ : syracuseStep 2005027 = 3007541) B3007541
theorem B5075237 : Blo 2003435 5075237 := bbase (se 4 (by rfl) ⟨475803, by rfl⟩ : syracuseStep 5075237 = 951607) (by norm_num)
theorem B3383491 : Blo 2003435 3383491 := bstep (se 1 (by rfl) ⟨2537618, by rfl⟩ : syracuseStep 3383491 = 5075237) B5075237
theorem B4511321 : Blo 2003435 4511321 := bstep (se 2 (by rfl) ⟨1691745, by rfl⟩ : syracuseStep 4511321 = 3383491) B3383491
theorem B3007547 : Blo 2003435 3007547 := bstep (se 1 (by rfl) ⟨2255660, by rfl⟩ : syracuseStep 3007547 = 4511321) B4511321
theorem B2005031 : Blo 2003435 2005031 := bstep (se 1 (by rfl) ⟨1503773, by rfl⟩ : syracuseStep 2005031 = 3007547) B3007547
theorem B2255665 : Blo 2003435 2255665 := bbase (se 2 (by rfl) ⟨845874, by rfl⟩ : syracuseStep 2255665 = 1691749) (by norm_num)
theorem B3007553 : Blo 2003435 3007553 := bstep (se 2 (by rfl) ⟨1127832, by rfl⟩ : syracuseStep 3007553 = 2255665) B2255665
theorem B2005035 : Blo 2003435 2005035 := bstep (se 1 (by rfl) ⟨1503776, by rfl⟩ : syracuseStep 2005035 = 3007553) B3007553
theorem B6097189 : Blo 2003435 6097189 := bbase (se 4 (by rfl) ⟨571611, by rfl⟩ : syracuseStep 6097189 = 1143223) (by norm_num)
theorem B8129585 : Blo 2003435 8129585 := bstep (se 2 (by rfl) ⟨3048594, by rfl⟩ : syracuseStep 8129585 = 6097189) B6097189
theorem B5419723 : Blo 2003435 5419723 := bstep (se 1 (by rfl) ⟨4064792, by rfl⟩ : syracuseStep 5419723 = 8129585) B8129585
theorem B7226297 : Blo 2003435 7226297 := bstep (se 2 (by rfl) ⟨2709861, by rfl⟩ : syracuseStep 7226297 = 5419723) B5419723
theorem B4817531 : Blo 2003435 4817531 := bstep (se 1 (by rfl) ⟨3613148, by rfl⟩ : syracuseStep 4817531 = 7226297) B7226297
theorem B3211687 : Blo 2003435 3211687 := bstep (se 1 (by rfl) ⟨2408765, by rfl⟩ : syracuseStep 3211687 = 4817531) B4817531
theorem B4282249 : Blo 2003435 4282249 := bstep (se 2 (by rfl) ⟨1605843, by rfl⟩ : syracuseStep 4282249 = 3211687) B3211687
theorem B5709665 : Blo 2003435 5709665 := bstep (se 2 (by rfl) ⟨2141124, by rfl⟩ : syracuseStep 5709665 = 4282249) B4282249
theorem B3806443 : Blo 2003435 3806443 := bstep (se 1 (by rfl) ⟨2854832, by rfl⟩ : syracuseStep 3806443 = 5709665) B5709665
theorem B5075257 : Blo 2003435 5075257 := bstep (se 2 (by rfl) ⟨1903221, by rfl⟩ : syracuseStep 5075257 = 3806443) B3806443
theorem B6767009 : Blo 2003435 6767009 := bstep (se 2 (by rfl) ⟨2537628, by rfl⟩ : syracuseStep 6767009 = 5075257) B5075257
theorem B4511339 : Blo 2003435 4511339 := bstep (se 1 (by rfl) ⟨3383504, by rfl⟩ : syracuseStep 4511339 = 6767009) B6767009
theorem B3007559 : Blo 2003435 3007559 := bstep (se 1 (by rfl) ⟨2255669, by rfl⟩ : syracuseStep 3007559 = 4511339) B4511339
theorem B2005039 : Blo 2003435 2005039 := bstep (se 1 (by rfl) ⟨1503779, by rfl⟩ : syracuseStep 2005039 = 3007559) B3007559
theorem B3007565 : Blo 2003435 3007565 := bbase (se 3 (by rfl) ⟨563918, by rfl⟩ : syracuseStep 3007565 = 1127837) (by norm_num)
theorem B2005043 : Blo 2003435 2005043 := bstep (se 1 (by rfl) ⟨1503782, by rfl⟩ : syracuseStep 2005043 = 3007565) B3007565
theorem B4511357 : Blo 2003435 4511357 := bbase (se 3 (by rfl) ⟨845879, by rfl⟩ : syracuseStep 4511357 = 1691759) (by norm_num)
theorem B3007571 : Blo 2003435 3007571 := bstep (se 1 (by rfl) ⟨2255678, by rfl⟩ : syracuseStep 3007571 = 4511357) B4511357
theorem B2005047 : Blo 2003435 2005047 := bstep (se 1 (by rfl) ⟨1503785, by rfl⟩ : syracuseStep 2005047 = 3007571) B3007571
theorem B3383525 : Blo 2003435 3383525 := bbase (se 4 (by rfl) ⟨317205, by rfl⟩ : syracuseStep 3383525 = 634411) (by norm_num)
theorem B2255683 : Blo 2003435 2255683 := bstep (se 1 (by rfl) ⟨1691762, by rfl⟩ : syracuseStep 2255683 = 3383525) B3383525
theorem B3007577 : Blo 2003435 3007577 := bstep (se 2 (by rfl) ⟨1127841, by rfl⟩ : syracuseStep 3007577 = 2255683) B2255683
theorem B2005051 : Blo 2003435 2005051 := bstep (se 1 (by rfl) ⟨1503788, by rfl⟩ : syracuseStep 2005051 = 3007577) B3007577
theorem B2572273 : Blo 2003435 2572273 := bbase (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) (by norm_num)
theorem B3429697 : Blo 2003435 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B4572929 : Blo 2003435 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B3048619 : Blo 2003435 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B4064825 : Blo 2003435 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B2709883 : Blo 2003435 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B3613177 : Blo 2003435 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B4817569 : Blo 2003435 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B6423425 : Blo 2003435 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B4282283 : Blo 2003435 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B2854855 : Blo 2003435 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B15225893 : Blo 2003435 15225893 := bstep (se 4 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 15225893 = 2854855) B2854855
theorem B10150595 : Blo 2003435 10150595 := bstep (se 1 (by rfl) ⟨7612946, by rfl⟩ : syracuseStep 10150595 = 15225893) B15225893
theorem B6767063 : Blo 2003435 6767063 := bstep (se 1 (by rfl) ⟨5075297, by rfl⟩ : syracuseStep 6767063 = 10150595) B10150595
theorem B4511375 : Blo 2003435 4511375 := bstep (se 1 (by rfl) ⟨3383531, by rfl⟩ : syracuseStep 4511375 = 6767063) B6767063
theorem B3007583 : Blo 2003435 3007583 := bstep (se 1 (by rfl) ⟨2255687, by rfl⟩ : syracuseStep 3007583 = 4511375) B4511375
theorem B2005055 : Blo 2003435 2005055 := bstep (se 1 (by rfl) ⟨1503791, by rfl⟩ : syracuseStep 2005055 = 3007583) B3007583
theorem B3007589 : Blo 2003435 3007589 := bbase (se 4 (by rfl) ⟨281961, by rfl⟩ : syracuseStep 3007589 = 563923) (by norm_num)
theorem B2005059 : Blo 2003435 2005059 := bstep (se 1 (by rfl) ⟨1503794, by rfl⟩ : syracuseStep 2005059 = 3007589) B3007589
theorem B4282301 : Blo 2003435 4282301 := bbase (se 3 (by rfl) ⟨802931, by rfl⟩ : syracuseStep 4282301 = 1605863) (by norm_num)
theorem B2854867 : Blo 2003435 2854867 := bstep (se 1 (by rfl) ⟨2141150, by rfl⟩ : syracuseStep 2854867 = 4282301) B4282301
theorem B3806489 : Blo 2003435 3806489 := bstep (se 2 (by rfl) ⟨1427433, by rfl⟩ : syracuseStep 3806489 = 2854867) B2854867
theorem B2537659 : Blo 2003435 2537659 := bstep (se 1 (by rfl) ⟨1903244, by rfl⟩ : syracuseStep 2537659 = 3806489) B3806489
theorem B3383545 : Blo 2003435 3383545 := bstep (se 2 (by rfl) ⟨1268829, by rfl⟩ : syracuseStep 3383545 = 2537659) B2537659
theorem B4511393 : Blo 2003435 4511393 := bstep (se 2 (by rfl) ⟨1691772, by rfl⟩ : syracuseStep 4511393 = 3383545) B3383545
theorem B3007595 : Blo 2003435 3007595 := bstep (se 1 (by rfl) ⟨2255696, by rfl⟩ : syracuseStep 3007595 = 4511393) B4511393
theorem B2005063 : Blo 2003435 2005063 := bstep (se 1 (by rfl) ⟨1503797, by rfl⟩ : syracuseStep 2005063 = 3007595) B3007595
theorem B2255701 : Blo 2003435 2255701 := bbase (se 9 (by rfl) ⟨6608, by rfl⟩ : syracuseStep 2255701 = 13217) (by norm_num)
theorem B3007601 : Blo 2003435 3007601 := bstep (se 2 (by rfl) ⟨1127850, by rfl⟩ : syracuseStep 3007601 = 2255701) B2255701
theorem B2005067 : Blo 2003435 2005067 := bstep (se 1 (by rfl) ⟨1503800, by rfl⟩ : syracuseStep 2005067 = 3007601) B3007601
theorem B2537669 : Blo 2003435 2537669 := bbase (se 4 (by rfl) ⟨237906, by rfl⟩ : syracuseStep 2537669 = 475813) (by norm_num)
theorem B6767117 : Blo 2003435 6767117 := bstep (se 3 (by rfl) ⟨1268834, by rfl⟩ : syracuseStep 6767117 = 2537669) B2537669
theorem B4511411 : Blo 2003435 4511411 := bstep (se 1 (by rfl) ⟨3383558, by rfl⟩ : syracuseStep 4511411 = 6767117) B6767117
theorem B3007607 : Blo 2003435 3007607 := bstep (se 1 (by rfl) ⟨2255705, by rfl⟩ : syracuseStep 3007607 = 4511411) B4511411
theorem B2005071 : Blo 2003435 2005071 := bstep (se 1 (by rfl) ⟨1503803, by rfl⟩ : syracuseStep 2005071 = 3007607) B3007607
theorem B3007613 : Blo 2003435 3007613 := bbase (se 3 (by rfl) ⟨563927, by rfl⟩ : syracuseStep 3007613 = 1127855) (by norm_num)
theorem B2005075 : Blo 2003435 2005075 := bstep (se 1 (by rfl) ⟨1503806, by rfl⟩ : syracuseStep 2005075 = 3007613) B3007613
theorem B4511429 : Blo 2003435 4511429 := bbase (se 4 (by rfl) ⟨422946, by rfl⟩ : syracuseStep 4511429 = 845893) (by norm_num)
theorem B3007619 : Blo 2003435 3007619 := bstep (se 1 (by rfl) ⟨2255714, by rfl⟩ : syracuseStep 3007619 = 4511429) B4511429
theorem B2005079 : Blo 2003435 2005079 := bstep (se 1 (by rfl) ⟨1503809, by rfl⟩ : syracuseStep 2005079 = 3007619) B3007619
theorem B3048661 : Blo 2003435 3048661 := bbase (se 7 (by rfl) ⟨35726, by rfl⟩ : syracuseStep 3048661 = 71453) (by norm_num)
theorem B16259525 : Blo 2003435 16259525 := bstep (se 4 (by rfl) ⟨1524330, by rfl⟩ : syracuseStep 16259525 = 3048661) B3048661
theorem B10839683 : Blo 2003435 10839683 := bstep (se 1 (by rfl) ⟨8129762, by rfl⟩ : syracuseStep 10839683 = 16259525) B16259525
theorem B28905821 : Blo 2003435 28905821 := bstep (se 3 (by rfl) ⟨5419841, by rfl⟩ : syracuseStep 28905821 = 10839683) B10839683
theorem B19270547 : Blo 2003435 19270547 := bstep (se 1 (by rfl) ⟨14452910, by rfl⟩ : syracuseStep 19270547 = 28905821) B28905821
theorem B12847031 : Blo 2003435 12847031 := bstep (se 1 (by rfl) ⟨9635273, by rfl⟩ : syracuseStep 12847031 = 19270547) B19270547
theorem B8564687 : Blo 2003435 8564687 := bstep (se 1 (by rfl) ⟨6423515, by rfl⟩ : syracuseStep 8564687 = 12847031) B12847031
theorem B5709791 : Blo 2003435 5709791 := bstep (se 1 (by rfl) ⟨4282343, by rfl⟩ : syracuseStep 5709791 = 8564687) B8564687
theorem B3806527 : Blo 2003435 3806527 := bstep (se 1 (by rfl) ⟨2854895, by rfl⟩ : syracuseStep 3806527 = 5709791) B5709791
theorem B5075369 : Blo 2003435 5075369 := bstep (se 2 (by rfl) ⟨1903263, by rfl⟩ : syracuseStep 5075369 = 3806527) B3806527
theorem B3383579 : Blo 2003435 3383579 := bstep (se 1 (by rfl) ⟨2537684, by rfl⟩ : syracuseStep 3383579 = 5075369) B5075369
theorem B2255719 : Blo 2003435 2255719 := bstep (se 1 (by rfl) ⟨1691789, by rfl⟩ : syracuseStep 2255719 = 3383579) B3383579
theorem B3007625 : Blo 2003435 3007625 := bstep (se 2 (by rfl) ⟨1127859, by rfl⟩ : syracuseStep 3007625 = 2255719) B2255719
theorem B2005083 : Blo 2003435 2005083 := bstep (se 1 (by rfl) ⟨1503812, by rfl⟩ : syracuseStep 2005083 = 3007625) B3007625
theorem B10150757 : Blo 2003435 10150757 := bbase (se 4 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 10150757 = 1903267) (by norm_num)
theorem B6767171 : Blo 2003435 6767171 := bstep (se 1 (by rfl) ⟨5075378, by rfl⟩ : syracuseStep 6767171 = 10150757) B10150757
theorem B4511447 : Blo 2003435 4511447 := bstep (se 1 (by rfl) ⟨3383585, by rfl⟩ : syracuseStep 4511447 = 6767171) B6767171
theorem B3007631 : Blo 2003435 3007631 := bstep (se 1 (by rfl) ⟨2255723, by rfl⟩ : syracuseStep 3007631 = 4511447) B4511447
theorem B2005087 : Blo 2003435 2005087 := bstep (se 1 (by rfl) ⟨1503815, by rfl⟩ : syracuseStep 2005087 = 3007631) B3007631
theorem B3007637 : Blo 2003435 3007637 := bbase (se 6 (by rfl) ⟨70491, by rfl⟩ : syracuseStep 3007637 = 140983) (by norm_num)
theorem B2005091 : Blo 2003435 2005091 := bstep (se 1 (by rfl) ⟨1503818, by rfl⟩ : syracuseStep 2005091 = 3007637) B3007637
theorem B2032453 : Blo 2003435 2032453 := bbase (se 4 (by rfl) ⟨190542, by rfl⟩ : syracuseStep 2032453 = 381085) (by norm_num)
theorem B2709937 : Blo 2003435 2709937 := bstep (se 2 (by rfl) ⟨1016226, by rfl⟩ : syracuseStep 2709937 = 2032453) B2032453
theorem B3613249 : Blo 2003435 3613249 := bstep (se 2 (by rfl) ⟨1354968, by rfl⟩ : syracuseStep 3613249 = 2709937) B2709937
theorem B4817665 : Blo 2003435 4817665 := bstep (se 2 (by rfl) ⟨1806624, by rfl⟩ : syracuseStep 4817665 = 3613249) B3613249
theorem B6423553 : Blo 2003435 6423553 := bstep (se 2 (by rfl) ⟨2408832, by rfl⟩ : syracuseStep 6423553 = 4817665) B4817665
theorem B8564737 : Blo 2003435 8564737 := bstep (se 2 (by rfl) ⟨3211776, by rfl⟩ : syracuseStep 8564737 = 6423553) B6423553
theorem B11419649 : Blo 2003435 11419649 := bstep (se 2 (by rfl) ⟨4282368, by rfl⟩ : syracuseStep 11419649 = 8564737) B8564737
theorem B7613099 : Blo 2003435 7613099 := bstep (se 1 (by rfl) ⟨5709824, by rfl⟩ : syracuseStep 7613099 = 11419649) B11419649
theorem B5075399 : Blo 2003435 5075399 := bstep (se 1 (by rfl) ⟨3806549, by rfl⟩ : syracuseStep 5075399 = 7613099) B7613099
theorem B3383599 : Blo 2003435 3383599 := bstep (se 1 (by rfl) ⟨2537699, by rfl⟩ : syracuseStep 3383599 = 5075399) B5075399
theorem B4511465 : Blo 2003435 4511465 := bstep (se 2 (by rfl) ⟨1691799, by rfl⟩ : syracuseStep 4511465 = 3383599) B3383599
theorem B3007643 : Blo 2003435 3007643 := bstep (se 1 (by rfl) ⟨2255732, by rfl⟩ : syracuseStep 3007643 = 4511465) B4511465
theorem B2005095 : Blo 2003435 2005095 := bstep (se 1 (by rfl) ⟨1503821, by rfl⟩ : syracuseStep 2005095 = 3007643) B3007643
theorem B2255737 : Blo 2003435 2255737 := bbase (se 2 (by rfl) ⟨845901, by rfl⟩ : syracuseStep 2255737 = 1691803) (by norm_num)
theorem B3007649 : Blo 2003435 3007649 := bstep (se 2 (by rfl) ⟨1127868, by rfl⟩ : syracuseStep 3007649 = 2255737) B2255737
theorem B2005099 : Blo 2003435 2005099 := bstep (se 1 (by rfl) ⟨1503824, by rfl⟩ : syracuseStep 2005099 = 3007649) B3007649
theorem B12847157 : Blo 2003435 12847157 := bbase (se 5 (by rfl) ⟨602210, by rfl⟩ : syracuseStep 12847157 = 1204421) (by norm_num)
theorem B8564771 : Blo 2003435 8564771 := bstep (se 1 (by rfl) ⟨6423578, by rfl⟩ : syracuseStep 8564771 = 12847157) B12847157
theorem B5709847 : Blo 2003435 5709847 := bstep (se 1 (by rfl) ⟨4282385, by rfl⟩ : syracuseStep 5709847 = 8564771) B8564771
theorem B7613129 : Blo 2003435 7613129 := bstep (se 2 (by rfl) ⟨2854923, by rfl⟩ : syracuseStep 7613129 = 5709847) B5709847
theorem B5075419 : Blo 2003435 5075419 := bstep (se 1 (by rfl) ⟨3806564, by rfl⟩ : syracuseStep 5075419 = 7613129) B7613129
theorem B6767225 : Blo 2003435 6767225 := bstep (se 2 (by rfl) ⟨2537709, by rfl⟩ : syracuseStep 6767225 = 5075419) B5075419
theorem B4511483 : Blo 2003435 4511483 := bstep (se 1 (by rfl) ⟨3383612, by rfl⟩ : syracuseStep 4511483 = 6767225) B6767225
theorem B3007655 : Blo 2003435 3007655 := bstep (se 1 (by rfl) ⟨2255741, by rfl⟩ : syracuseStep 3007655 = 4511483) B4511483
theorem B2005103 : Blo 2003435 2005103 := bstep (se 1 (by rfl) ⟨1503827, by rfl⟩ : syracuseStep 2005103 = 3007655) B3007655
theorem B3007661 : Blo 2003435 3007661 := bbase (se 3 (by rfl) ⟨563936, by rfl⟩ : syracuseStep 3007661 = 1127873) (by norm_num)
theorem B2005107 : Blo 2003435 2005107 := bstep (se 1 (by rfl) ⟨1503830, by rfl⟩ : syracuseStep 2005107 = 3007661) B3007661
theorem B4511501 : Blo 2003435 4511501 := bbase (se 3 (by rfl) ⟨845906, by rfl⟩ : syracuseStep 4511501 = 1691813) (by norm_num)
theorem B3007667 : Blo 2003435 3007667 := bstep (se 1 (by rfl) ⟨2255750, by rfl⟩ : syracuseStep 3007667 = 4511501) B4511501
theorem B2005111 : Blo 2003435 2005111 := bstep (se 1 (by rfl) ⟨1503833, by rfl⟩ : syracuseStep 2005111 = 3007667) B3007667
theorem B2537725 : Blo 2003435 2537725 := bbase (se 3 (by rfl) ⟨475823, by rfl⟩ : syracuseStep 2537725 = 951647) (by norm_num)
theorem B3383633 : Blo 2003435 3383633 := bstep (se 2 (by rfl) ⟨1268862, by rfl⟩ : syracuseStep 3383633 = 2537725) B2537725
theorem B2255755 : Blo 2003435 2255755 := bstep (se 1 (by rfl) ⟨1691816, by rfl⟩ : syracuseStep 2255755 = 3383633) B3383633
theorem B3007673 : Blo 2003435 3007673 := bstep (se 2 (by rfl) ⟨1127877, by rfl⟩ : syracuseStep 3007673 = 2255755) B2255755
theorem B2005115 : Blo 2003435 2005115 := bstep (se 1 (by rfl) ⟨1503836, by rfl⟩ : syracuseStep 2005115 = 3007673) B3007673
theorem B2408861 : Blo 2003435 2408861 := bbase (se 3 (by rfl) ⟨451661, by rfl⟩ : syracuseStep 2408861 = 903323) (by norm_num)
theorem B6423629 : Blo 2003435 6423629 := bstep (se 3 (by rfl) ⟨1204430, by rfl⟩ : syracuseStep 6423629 = 2408861) B2408861
theorem B17129677 : Blo 2003435 17129677 := bstep (se 3 (by rfl) ⟨3211814, by rfl⟩ : syracuseStep 17129677 = 6423629) B6423629
theorem B22839569 : Blo 2003435 22839569 := bstep (se 2 (by rfl) ⟨8564838, by rfl⟩ : syracuseStep 22839569 = 17129677) B17129677
theorem B15226379 : Blo 2003435 15226379 := bstep (se 1 (by rfl) ⟨11419784, by rfl⟩ : syracuseStep 15226379 = 22839569) B22839569
theorem B10150919 : Blo 2003435 10150919 := bstep (se 1 (by rfl) ⟨7613189, by rfl⟩ : syracuseStep 10150919 = 15226379) B15226379
theorem B6767279 : Blo 2003435 6767279 := bstep (se 1 (by rfl) ⟨5075459, by rfl⟩ : syracuseStep 6767279 = 10150919) B10150919
theorem B4511519 : Blo 2003435 4511519 := bstep (se 1 (by rfl) ⟨3383639, by rfl⟩ : syracuseStep 4511519 = 6767279) B6767279
theorem B3007679 : Blo 2003435 3007679 := bstep (se 1 (by rfl) ⟨2255759, by rfl⟩ : syracuseStep 3007679 = 4511519) B4511519
theorem B2005119 : Blo 2003435 2005119 := bstep (se 1 (by rfl) ⟨1503839, by rfl⟩ : syracuseStep 2005119 = 3007679) B3007679
theorem B3007685 : Blo 2003435 3007685 := bbase (se 4 (by rfl) ⟨281970, by rfl⟩ : syracuseStep 3007685 = 563941) (by norm_num)
theorem B2005123 : Blo 2003435 2005123 := bstep (se 1 (by rfl) ⟨1503842, by rfl⟩ : syracuseStep 2005123 = 3007685) B3007685
theorem B3383653 : Blo 2003435 3383653 := bbase (se 4 (by rfl) ⟨317217, by rfl⟩ : syracuseStep 3383653 = 634435) (by norm_num)
theorem B4511537 : Blo 2003435 4511537 := bstep (se 2 (by rfl) ⟨1691826, by rfl⟩ : syracuseStep 4511537 = 3383653) B3383653
theorem B3007691 : Blo 2003435 3007691 := bstep (se 1 (by rfl) ⟨2255768, by rfl⟩ : syracuseStep 3007691 = 4511537) B4511537
theorem B2005127 : Blo 2003435 2005127 := bstep (se 1 (by rfl) ⟨1503845, by rfl⟩ : syracuseStep 2005127 = 3007691) B3007691
theorem B2255773 : Blo 2003435 2255773 := bbase (se 3 (by rfl) ⟨422957, by rfl⟩ : syracuseStep 2255773 = 845915) (by norm_num)
theorem B3007697 : Blo 2003435 3007697 := bstep (se 2 (by rfl) ⟨1127886, by rfl⟩ : syracuseStep 3007697 = 2255773) B2255773
theorem B2005131 : Blo 2003435 2005131 := bstep (se 1 (by rfl) ⟨1503848, by rfl⟩ : syracuseStep 2005131 = 3007697) B3007697
theorem B6767333 : Blo 2003435 6767333 := bbase (se 4 (by rfl) ⟨634437, by rfl⟩ : syracuseStep 6767333 = 1268875) (by norm_num)
theorem B4511555 : Blo 2003435 4511555 := bstep (se 1 (by rfl) ⟨3383666, by rfl⟩ : syracuseStep 4511555 = 6767333) B6767333
theorem B3007703 : Blo 2003435 3007703 := bstep (se 1 (by rfl) ⟨2255777, by rfl⟩ : syracuseStep 3007703 = 4511555) B4511555
theorem B2005135 : Blo 2003435 2005135 := bstep (se 1 (by rfl) ⟨1503851, by rfl⟩ : syracuseStep 2005135 = 3007703) B3007703
theorem B3007709 : Blo 2003435 3007709 := bbase (se 3 (by rfl) ⟨563945, by rfl⟩ : syracuseStep 3007709 = 1127891) (by norm_num)
theorem B2005139 : Blo 2003435 2005139 := bstep (se 1 (by rfl) ⟨1503854, by rfl⟩ : syracuseStep 2005139 = 3007709) B3007709
theorem B4511573 : Blo 2003435 4511573 := bbase (se 9 (by rfl) ⟨13217, by rfl⟩ : syracuseStep 4511573 = 26435) (by norm_num)
theorem B3007715 : Blo 2003435 3007715 := bstep (se 1 (by rfl) ⟨2255786, by rfl⟩ : syracuseStep 3007715 = 4511573) B4511573
theorem B2005143 : Blo 2003435 2005143 := bstep (se 1 (by rfl) ⟨1503857, by rfl⟩ : syracuseStep 2005143 = 3007715) B3007715
theorem B5709973 : Blo 2003435 5709973 := bbase (se 6 (by rfl) ⟨133827, by rfl⟩ : syracuseStep 5709973 = 267655) (by norm_num)
theorem B7613297 : Blo 2003435 7613297 := bstep (se 2 (by rfl) ⟨2854986, by rfl⟩ : syracuseStep 7613297 = 5709973) B5709973
theorem B5075531 : Blo 2003435 5075531 := bstep (se 1 (by rfl) ⟨3806648, by rfl⟩ : syracuseStep 5075531 = 7613297) B7613297
theorem B3383687 : Blo 2003435 3383687 := bstep (se 1 (by rfl) ⟨2537765, by rfl⟩ : syracuseStep 3383687 = 5075531) B5075531
theorem B2255791 : Blo 2003435 2255791 := bstep (se 1 (by rfl) ⟨1691843, by rfl⟩ : syracuseStep 2255791 = 3383687) B3383687
theorem B3007721 : Blo 2003435 3007721 := bstep (se 2 (by rfl) ⟨1127895, by rfl⟩ : syracuseStep 3007721 = 2255791) B2255791
theorem B2005147 : Blo 2003435 2005147 := bstep (se 1 (by rfl) ⟨1503860, by rfl⟩ : syracuseStep 2005147 = 3007721) B3007721
theorem B20859925 : Blo 2003435 20859925 := bbase (se 6 (by rfl) ⟨488904, by rfl⟩ : syracuseStep 20859925 = 977809) (by norm_num)
theorem B27813233 : Blo 2003435 27813233 := bstep (se 2 (by rfl) ⟨10429962, by rfl⟩ : syracuseStep 27813233 = 20859925) B20859925
theorem B74168621 : Blo 2003435 74168621 := bstep (se 3 (by rfl) ⟨13906616, by rfl⟩ : syracuseStep 74168621 = 27813233) B27813233
theorem B49445747 : Blo 2003435 49445747 := bstep (se 1 (by rfl) ⟨37084310, by rfl⟩ : syracuseStep 49445747 = 74168621) B74168621
theorem B32963831 : Blo 2003435 32963831 := bstep (se 1 (by rfl) ⟨24722873, by rfl⟩ : syracuseStep 32963831 = 49445747) B49445747
theorem B21975887 : Blo 2003435 21975887 := bstep (se 1 (by rfl) ⟨16481915, by rfl⟩ : syracuseStep 21975887 = 32963831) B32963831
theorem B14650591 : Blo 2003435 14650591 := bstep (se 1 (by rfl) ⟨10987943, by rfl⟩ : syracuseStep 14650591 = 21975887) B21975887
theorem B19534121 : Blo 2003435 19534121 := bstep (se 2 (by rfl) ⟨7325295, by rfl⟩ : syracuseStep 19534121 = 14650591) B14650591
theorem B13022747 : Blo 2003435 13022747 := bstep (se 1 (by rfl) ⟨9767060, by rfl⟩ : syracuseStep 13022747 = 19534121) B19534121
theorem B8681831 : Blo 2003435 8681831 := bstep (se 1 (by rfl) ⟨6511373, by rfl⟩ : syracuseStep 8681831 = 13022747) B13022747
theorem B5787887 : Blo 2003435 5787887 := bstep (se 1 (by rfl) ⟨4340915, by rfl⟩ : syracuseStep 5787887 = 8681831) B8681831
theorem B61737461 : Blo 2003435 61737461 := bstep (se 5 (by rfl) ⟨2893943, by rfl⟩ : syracuseStep 61737461 = 5787887) B5787887
theorem B41158307 : Blo 2003435 41158307 := bstep (se 1 (by rfl) ⟨30868730, by rfl⟩ : syracuseStep 41158307 = 61737461) B61737461
theorem B109755485 : Blo 2003435 109755485 := bstep (se 3 (by rfl) ⟨20579153, by rfl⟩ : syracuseStep 109755485 = 41158307) B41158307
theorem B73170323 : Blo 2003435 73170323 := bstep (se 1 (by rfl) ⟨54877742, by rfl⟩ : syracuseStep 73170323 = 109755485) B109755485
theorem B48780215 : Blo 2003435 48780215 := bstep (se 1 (by rfl) ⟨36585161, by rfl⟩ : syracuseStep 48780215 = 73170323) B73170323
theorem B32520143 : Blo 2003435 32520143 := bstep (se 1 (by rfl) ⟨24390107, by rfl⟩ : syracuseStep 32520143 = 48780215) B48780215
theorem B86720381 : Blo 2003435 86720381 := bstep (se 3 (by rfl) ⟨16260071, by rfl⟩ : syracuseStep 86720381 = 32520143) B32520143
theorem B57813587 : Blo 2003435 57813587 := bstep (se 1 (by rfl) ⟨43360190, by rfl⟩ : syracuseStep 57813587 = 86720381) B86720381
theorem B38542391 : Blo 2003435 38542391 := bstep (se 1 (by rfl) ⟨28906793, by rfl⟩ : syracuseStep 38542391 = 57813587) B57813587
theorem B25694927 : Blo 2003435 25694927 := bstep (se 1 (by rfl) ⟨19271195, by rfl⟩ : syracuseStep 25694927 = 38542391) B38542391
theorem B17129951 : Blo 2003435 17129951 := bstep (se 1 (by rfl) ⟨12847463, by rfl⟩ : syracuseStep 17129951 = 25694927) B25694927
theorem B11419967 : Blo 2003435 11419967 := bstep (se 1 (by rfl) ⟨8564975, by rfl⟩ : syracuseStep 11419967 = 17129951) B17129951
theorem B7613311 : Blo 2003435 7613311 := bstep (se 1 (by rfl) ⟨5709983, by rfl⟩ : syracuseStep 7613311 = 11419967) B11419967
theorem B10151081 : Blo 2003435 10151081 := bstep (se 2 (by rfl) ⟨3806655, by rfl⟩ : syracuseStep 10151081 = 7613311) B7613311
theorem B6767387 : Blo 2003435 6767387 := bstep (se 1 (by rfl) ⟨5075540, by rfl⟩ : syracuseStep 6767387 = 10151081) B10151081
theorem B4511591 : Blo 2003435 4511591 := bstep (se 1 (by rfl) ⟨3383693, by rfl⟩ : syracuseStep 4511591 = 6767387) B6767387
theorem B3007727 : Blo 2003435 3007727 := bstep (se 1 (by rfl) ⟨2255795, by rfl⟩ : syracuseStep 3007727 = 4511591) B4511591
theorem B2005151 : Blo 2003435 2005151 := bstep (se 1 (by rfl) ⟨1503863, by rfl⟩ : syracuseStep 2005151 = 3007727) B3007727
theorem B3007733 : Blo 2003435 3007733 := bbase (se 5 (by rfl) ⟨140987, by rfl⟩ : syracuseStep 3007733 = 281975) (by norm_num)
theorem B2005155 : Blo 2003435 2005155 := bstep (se 1 (by rfl) ⟨1503866, by rfl⟩ : syracuseStep 2005155 = 3007733) B3007733
theorem B18292661 : Blo 2003435 18292661 := bbase (se 5 (by rfl) ⟨857468, by rfl⟩ : syracuseStep 18292661 = 1714937) (by norm_num)
theorem B12195107 : Blo 2003435 12195107 := bstep (se 1 (by rfl) ⟨9146330, by rfl⟩ : syracuseStep 12195107 = 18292661) B18292661
theorem B8130071 : Blo 2003435 8130071 := bstep (se 1 (by rfl) ⟨6097553, by rfl⟩ : syracuseStep 8130071 = 12195107) B12195107
theorem B5420047 : Blo 2003435 5420047 := bstep (se 1 (by rfl) ⟨4065035, by rfl⟩ : syracuseStep 5420047 = 8130071) B8130071
theorem B7226729 : Blo 2003435 7226729 := bstep (se 2 (by rfl) ⟨2710023, by rfl⟩ : syracuseStep 7226729 = 5420047) B5420047
theorem B4817819 : Blo 2003435 4817819 := bstep (se 1 (by rfl) ⟨3613364, by rfl⟩ : syracuseStep 4817819 = 7226729) B7226729
theorem B12847517 : Blo 2003435 12847517 := bstep (se 3 (by rfl) ⟨2408909, by rfl⟩ : syracuseStep 12847517 = 4817819) B4817819
theorem B8565011 : Blo 2003435 8565011 := bstep (se 1 (by rfl) ⟨6423758, by rfl⟩ : syracuseStep 8565011 = 12847517) B12847517
theorem B5710007 : Blo 2003435 5710007 := bstep (se 1 (by rfl) ⟨4282505, by rfl⟩ : syracuseStep 5710007 = 8565011) B8565011
theorem B3806671 : Blo 2003435 3806671 := bstep (se 1 (by rfl) ⟨2855003, by rfl⟩ : syracuseStep 3806671 = 5710007) B5710007
theorem B5075561 : Blo 2003435 5075561 := bstep (se 2 (by rfl) ⟨1903335, by rfl⟩ : syracuseStep 5075561 = 3806671) B3806671
theorem B3383707 : Blo 2003435 3383707 := bstep (se 1 (by rfl) ⟨2537780, by rfl⟩ : syracuseStep 3383707 = 5075561) B5075561
theorem B4511609 : Blo 2003435 4511609 := bstep (se 2 (by rfl) ⟨1691853, by rfl⟩ : syracuseStep 4511609 = 3383707) B3383707
theorem B3007739 : Blo 2003435 3007739 := bstep (se 1 (by rfl) ⟨2255804, by rfl⟩ : syracuseStep 3007739 = 4511609) B4511609
theorem B2005159 : Blo 2003435 2005159 := bstep (se 1 (by rfl) ⟨1503869, by rfl⟩ : syracuseStep 2005159 = 3007739) B3007739
theorem B2255809 : Blo 2003435 2255809 := bbase (se 2 (by rfl) ⟨845928, by rfl⟩ : syracuseStep 2255809 = 1691857) (by norm_num)
theorem B3007745 : Blo 2003435 3007745 := bstep (se 2 (by rfl) ⟨1127904, by rfl⟩ : syracuseStep 3007745 = 2255809) B2255809
theorem B2005163 : Blo 2003435 2005163 := bstep (se 1 (by rfl) ⟨1503872, by rfl⟩ : syracuseStep 2005163 = 3007745) B3007745
theorem B5075581 : Blo 2003435 5075581 := bbase (se 3 (by rfl) ⟨951671, by rfl⟩ : syracuseStep 5075581 = 1903343) (by norm_num)
theorem B6767441 : Blo 2003435 6767441 := bstep (se 2 (by rfl) ⟨2537790, by rfl⟩ : syracuseStep 6767441 = 5075581) B5075581
theorem B4511627 : Blo 2003435 4511627 := bstep (se 1 (by rfl) ⟨3383720, by rfl⟩ : syracuseStep 4511627 = 6767441) B6767441
theorem B3007751 : Blo 2003435 3007751 := bstep (se 1 (by rfl) ⟨2255813, by rfl⟩ : syracuseStep 3007751 = 4511627) B4511627
theorem B2005167 : Blo 2003435 2005167 := bstep (se 1 (by rfl) ⟨1503875, by rfl⟩ : syracuseStep 2005167 = 3007751) B3007751
theorem B3007757 : Blo 2003435 3007757 := bbase (se 3 (by rfl) ⟨563954, by rfl⟩ : syracuseStep 3007757 = 1127909) (by norm_num)
theorem B2005171 : Blo 2003435 2005171 := bstep (se 1 (by rfl) ⟨1503878, by rfl⟩ : syracuseStep 2005171 = 3007757) B3007757
theorem B4511645 : Blo 2003435 4511645 := bbase (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) (by norm_num)
theorem B3007763 : Blo 2003435 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B2005175 : Blo 2003435 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B3383741 : Blo 2003435 3383741 := bbase (se 3 (by rfl) ⟨634451, by rfl⟩ : syracuseStep 3383741 = 1268903) (by norm_num)
theorem B2255827 : Blo 2003435 2255827 := bstep (se 1 (by rfl) ⟨1691870, by rfl⟩ : syracuseStep 2255827 = 3383741) B3383741
theorem B3007769 : Blo 2003435 3007769 := bstep (se 2 (by rfl) ⟨1127913, by rfl⟩ : syracuseStep 3007769 = 2255827) B2255827
theorem B2005179 : Blo 2003435 2005179 := bstep (se 1 (by rfl) ⟨1503884, by rfl⟩ : syracuseStep 2005179 = 3007769) B3007769
theorem B11420149 : Blo 2003435 11420149 := bbase (se 5 (by rfl) ⟨535319, by rfl⟩ : syracuseStep 11420149 = 1070639) (by norm_num)
theorem B15226865 : Blo 2003435 15226865 := bstep (se 2 (by rfl) ⟨5710074, by rfl⟩ : syracuseStep 15226865 = 11420149) B11420149
theorem B10151243 : Blo 2003435 10151243 := bstep (se 1 (by rfl) ⟨7613432, by rfl⟩ : syracuseStep 10151243 = 15226865) B15226865
theorem B6767495 : Blo 2003435 6767495 := bstep (se 1 (by rfl) ⟨5075621, by rfl⟩ : syracuseStep 6767495 = 10151243) B10151243
theorem B4511663 : Blo 2003435 4511663 := bstep (se 1 (by rfl) ⟨3383747, by rfl⟩ : syracuseStep 4511663 = 6767495) B6767495
theorem B3007775 : Blo 2003435 3007775 := bstep (se 1 (by rfl) ⟨2255831, by rfl⟩ : syracuseStep 3007775 = 4511663) B4511663
theorem B2005183 : Blo 2003435 2005183 := bstep (se 1 (by rfl) ⟨1503887, by rfl⟩ : syracuseStep 2005183 = 3007775) B3007775
theorem B3007781 : Blo 2003435 3007781 := bbase (se 4 (by rfl) ⟨281979, by rfl⟩ : syracuseStep 3007781 = 563959) (by norm_num)
theorem B2005187 : Blo 2003435 2005187 := bstep (se 1 (by rfl) ⟨1503890, by rfl⟩ : syracuseStep 2005187 = 3007781) B3007781
theorem B2537821 : Blo 2003435 2537821 := bbase (se 3 (by rfl) ⟨475841, by rfl⟩ : syracuseStep 2537821 = 951683) (by norm_num)
theorem B3383761 : Blo 2003435 3383761 := bstep (se 2 (by rfl) ⟨1268910, by rfl⟩ : syracuseStep 3383761 = 2537821) B2537821
theorem B4511681 : Blo 2003435 4511681 := bstep (se 2 (by rfl) ⟨1691880, by rfl⟩ : syracuseStep 4511681 = 3383761) B3383761
theorem B3007787 : Blo 2003435 3007787 := bstep (se 1 (by rfl) ⟨2255840, by rfl⟩ : syracuseStep 3007787 = 4511681) B4511681
theorem B2005191 : Blo 2003435 2005191 := bstep (se 1 (by rfl) ⟨1503893, by rfl⟩ : syracuseStep 2005191 = 3007787) B3007787
theorem B2255845 : Blo 2003435 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B3007793 : Blo 2003435 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B2005195 : Blo 2003435 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B2572457 : Blo 2003435 2572457 := bbase (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) (by norm_num)
theorem B6859885 : Blo 2003435 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B9146513 : Blo 2003435 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B6097675 : Blo 2003435 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B8130233 : Blo 2003435 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B21680621 : Blo 2003435 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B14453747 : Blo 2003435 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B9635831 : Blo 2003435 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B6423887 : Blo 2003435 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B4282591 : Blo 2003435 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B5710121 : Blo 2003435 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B3806747 : Blo 2003435 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B2537831 : Blo 2003435 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B6767549 : Blo 2003435 6767549 := bstep (se 3 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 6767549 = 2537831) B2537831
theorem B4511699 : Blo 2003435 4511699 := bstep (se 1 (by rfl) ⟨3383774, by rfl⟩ : syracuseStep 4511699 = 6767549) B6767549
theorem B3007799 : Blo 2003435 3007799 := bstep (se 1 (by rfl) ⟨2255849, by rfl⟩ : syracuseStep 3007799 = 4511699) B4511699
theorem B2005199 : Blo 2003435 2005199 := bstep (se 1 (by rfl) ⟨1503899, by rfl⟩ : syracuseStep 2005199 = 3007799) B3007799
theorem B3007805 : Blo 2003435 3007805 := bbase (se 3 (by rfl) ⟨563963, by rfl⟩ : syracuseStep 3007805 = 1127927) (by norm_num)
theorem B2005203 : Blo 2003435 2005203 := bstep (se 1 (by rfl) ⟨1503902, by rfl⟩ : syracuseStep 2005203 = 3007805) B3007805
theorem B4511717 : Blo 2003435 4511717 := bbase (se 4 (by rfl) ⟨422973, by rfl⟩ : syracuseStep 4511717 = 845947) (by norm_num)
theorem B3007811 : Blo 2003435 3007811 := bstep (se 1 (by rfl) ⟨2255858, by rfl⟩ : syracuseStep 3007811 = 4511717) B4511717
theorem B2005207 : Blo 2003435 2005207 := bstep (se 1 (by rfl) ⟨1503905, by rfl⟩ : syracuseStep 2005207 = 3007811) B3007811
theorem B5075693 : Blo 2003435 5075693 := bbase (se 3 (by rfl) ⟨951692, by rfl⟩ : syracuseStep 5075693 = 1903385) (by norm_num)
theorem B3383795 : Blo 2003435 3383795 := bstep (se 1 (by rfl) ⟨2537846, by rfl⟩ : syracuseStep 3383795 = 5075693) B5075693
theorem B2255863 : Blo 2003435 2255863 := bstep (se 1 (by rfl) ⟨1691897, by rfl⟩ : syracuseStep 2255863 = 3383795) B3383795
theorem B3007817 : Blo 2003435 3007817 := bstep (se 2 (by rfl) ⟨1127931, by rfl⟩ : syracuseStep 3007817 = 2255863) B2255863
theorem B2005211 : Blo 2003435 2005211 := bstep (se 1 (by rfl) ⟨1503908, by rfl⟩ : syracuseStep 2005211 = 3007817) B3007817
theorem B2408977 : Blo 2003435 2408977 := bbase (se 2 (by rfl) ⟨903366, by rfl⟩ : syracuseStep 2408977 = 1806733) (by norm_num)
theorem B3211969 : Blo 2003435 3211969 := bstep (se 2 (by rfl) ⟨1204488, by rfl⟩ : syracuseStep 3211969 = 2408977) B2408977
theorem B4282625 : Blo 2003435 4282625 := bstep (se 2 (by rfl) ⟨1605984, by rfl⟩ : syracuseStep 4282625 = 3211969) B3211969
theorem B2855083 : Blo 2003435 2855083 := bstep (se 1 (by rfl) ⟨2141312, by rfl⟩ : syracuseStep 2855083 = 4282625) B4282625
theorem B3806777 : Blo 2003435 3806777 := bstep (se 2 (by rfl) ⟨1427541, by rfl⟩ : syracuseStep 3806777 = 2855083) B2855083
theorem B10151405 : Blo 2003435 10151405 := bstep (se 3 (by rfl) ⟨1903388, by rfl⟩ : syracuseStep 10151405 = 3806777) B3806777
theorem B6767603 : Blo 2003435 6767603 := bstep (se 1 (by rfl) ⟨5075702, by rfl⟩ : syracuseStep 6767603 = 10151405) B10151405
theorem B4511735 : Blo 2003435 4511735 := bstep (se 1 (by rfl) ⟨3383801, by rfl⟩ : syracuseStep 4511735 = 6767603) B6767603
theorem B3007823 : Blo 2003435 3007823 := bstep (se 1 (by rfl) ⟨2255867, by rfl⟩ : syracuseStep 3007823 = 4511735) B4511735
theorem B2005215 : Blo 2003435 2005215 := bstep (se 1 (by rfl) ⟨1503911, by rfl⟩ : syracuseStep 2005215 = 3007823) B3007823
theorem B3007829 : Blo 2003435 3007829 := bbase (se 12 (by rfl) ⟨1101, by rfl⟩ : syracuseStep 3007829 = 2203) (by norm_num)
theorem B2005219 : Blo 2003435 2005219 := bstep (se 1 (by rfl) ⟨1503914, by rfl⟩ : syracuseStep 2005219 = 3007829) B3007829
theorem B2141321 : Blo 2003435 2141321 := bbase (se 2 (by rfl) ⟨802995, by rfl⟩ : syracuseStep 2141321 = 1605991) (by norm_num)
theorem B5710189 : Blo 2003435 5710189 := bstep (se 3 (by rfl) ⟨1070660, by rfl⟩ : syracuseStep 5710189 = 2141321) B2141321
theorem B7613585 : Blo 2003435 7613585 := bstep (se 2 (by rfl) ⟨2855094, by rfl⟩ : syracuseStep 7613585 = 5710189) B5710189
theorem B5075723 : Blo 2003435 5075723 := bstep (se 1 (by rfl) ⟨3806792, by rfl⟩ : syracuseStep 5075723 = 7613585) B7613585
theorem B3383815 : Blo 2003435 3383815 := bstep (se 1 (by rfl) ⟨2537861, by rfl⟩ : syracuseStep 3383815 = 5075723) B5075723
theorem B4511753 : Blo 2003435 4511753 := bstep (se 2 (by rfl) ⟨1691907, by rfl⟩ : syracuseStep 4511753 = 3383815) B3383815
theorem B3007835 : Blo 2003435 3007835 := bstep (se 1 (by rfl) ⟨2255876, by rfl⟩ : syracuseStep 3007835 = 4511753) B4511753
theorem B2005223 : Blo 2003435 2005223 := bstep (se 1 (by rfl) ⟨1503917, by rfl⟩ : syracuseStep 2005223 = 3007835) B3007835
theorem B2255881 : Blo 2003435 2255881 := bbase (se 2 (by rfl) ⟨845955, by rfl⟩ : syracuseStep 2255881 = 1691911) (by norm_num)
theorem B3007841 : Blo 2003435 3007841 := bstep (se 2 (by rfl) ⟨1127940, by rfl⟩ : syracuseStep 3007841 = 2255881) B2255881
theorem B2005227 : Blo 2003435 2005227 := bstep (se 1 (by rfl) ⟨1503920, by rfl⟩ : syracuseStep 2005227 = 3007841) B3007841
theorem B7717493 : Blo 2003435 7717493 := bbase (se 5 (by rfl) ⟨361757, by rfl⟩ : syracuseStep 7717493 = 723515) (by norm_num)
theorem B5144995 : Blo 2003435 5144995 := bstep (se 1 (by rfl) ⟨3858746, by rfl⟩ : syracuseStep 5144995 = 7717493) B7717493
theorem B6859993 : Blo 2003435 6859993 := bstep (se 2 (by rfl) ⟨2572497, by rfl⟩ : syracuseStep 6859993 = 5144995) B5144995
theorem B9146657 : Blo 2003435 9146657 := bstep (se 2 (by rfl) ⟨3429996, by rfl⟩ : syracuseStep 9146657 = 6859993) B6859993
theorem B6097771 : Blo 2003435 6097771 := bstep (se 1 (by rfl) ⟨4573328, by rfl⟩ : syracuseStep 6097771 = 9146657) B9146657
theorem B8130361 : Blo 2003435 8130361 := bstep (se 2 (by rfl) ⟨3048885, by rfl⟩ : syracuseStep 8130361 = 6097771) B6097771
theorem B10840481 : Blo 2003435 10840481 := bstep (se 2 (by rfl) ⟨4065180, by rfl⟩ : syracuseStep 10840481 = 8130361) B8130361
theorem B7226987 : Blo 2003435 7226987 := bstep (se 1 (by rfl) ⟨5420240, by rfl⟩ : syracuseStep 7226987 = 10840481) B10840481
theorem B19271965 : Blo 2003435 19271965 := bstep (se 3 (by rfl) ⟨3613493, by rfl⟩ : syracuseStep 19271965 = 7226987) B7226987
theorem B25695953 : Blo 2003435 25695953 := bstep (se 2 (by rfl) ⟨9635982, by rfl⟩ : syracuseStep 25695953 = 19271965) B19271965
theorem B17130635 : Blo 2003435 17130635 := bstep (se 1 (by rfl) ⟨12847976, by rfl⟩ : syracuseStep 17130635 = 25695953) B25695953
theorem B11420423 : Blo 2003435 11420423 := bstep (se 1 (by rfl) ⟨8565317, by rfl⟩ : syracuseStep 11420423 = 17130635) B17130635
theorem B7613615 : Blo 2003435 7613615 := bstep (se 1 (by rfl) ⟨5710211, by rfl⟩ : syracuseStep 7613615 = 11420423) B11420423
theorem B5075743 : Blo 2003435 5075743 := bstep (se 1 (by rfl) ⟨3806807, by rfl⟩ : syracuseStep 5075743 = 7613615) B7613615
theorem B6767657 : Blo 2003435 6767657 := bstep (se 2 (by rfl) ⟨2537871, by rfl⟩ : syracuseStep 6767657 = 5075743) B5075743
theorem B4511771 : Blo 2003435 4511771 := bstep (se 1 (by rfl) ⟨3383828, by rfl⟩ : syracuseStep 4511771 = 6767657) B6767657
theorem B3007847 : Blo 2003435 3007847 := bstep (se 1 (by rfl) ⟨2255885, by rfl⟩ : syracuseStep 3007847 = 4511771) B4511771
theorem B2005231 : Blo 2003435 2005231 := bstep (se 1 (by rfl) ⟨1503923, by rfl⟩ : syracuseStep 2005231 = 3007847) B3007847
theorem B3007853 : Blo 2003435 3007853 := bbase (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) (by norm_num)
theorem B2005235 : Blo 2003435 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B4511789 : Blo 2003435 4511789 := bbase (se 3 (by rfl) ⟨845960, by rfl⟩ : syracuseStep 4511789 = 1691921) (by norm_num)
theorem B3007859 : Blo 2003435 3007859 := bstep (se 1 (by rfl) ⟨2255894, by rfl⟩ : syracuseStep 3007859 = 4511789) B4511789
theorem B2005239 : Blo 2003435 2005239 := bstep (se 1 (by rfl) ⟨1503929, by rfl⟩ : syracuseStep 2005239 = 3007859) B3007859
theorem B5145029 : Blo 2003435 5145029 := bbase (se 4 (by rfl) ⟨482346, by rfl⟩ : syracuseStep 5145029 = 964693) (by norm_num)
theorem B3430019 : Blo 2003435 3430019 := bstep (se 1 (by rfl) ⟨2572514, by rfl⟩ : syracuseStep 3430019 = 5145029) B5145029
theorem B2286679 : Blo 2003435 2286679 := bstep (se 1 (by rfl) ⟨1715009, by rfl⟩ : syracuseStep 2286679 = 3430019) B3430019
theorem B3048905 : Blo 2003435 3048905 := bstep (se 2 (by rfl) ⟨1143339, by rfl⟩ : syracuseStep 3048905 = 2286679) B2286679
theorem B2032603 : Blo 2003435 2032603 := bstep (se 1 (by rfl) ⟨1524452, by rfl⟩ : syracuseStep 2032603 = 3048905) B3048905
theorem B10840549 : Blo 2003435 10840549 := bstep (se 4 (by rfl) ⟨1016301, by rfl⟩ : syracuseStep 10840549 = 2032603) B2032603
theorem B14454065 : Blo 2003435 14454065 := bstep (se 2 (by rfl) ⟨5420274, by rfl⟩ : syracuseStep 14454065 = 10840549) B10840549
theorem B9636043 : Blo 2003435 9636043 := bstep (se 1 (by rfl) ⟨7227032, by rfl⟩ : syracuseStep 9636043 = 14454065) B14454065
theorem B12848057 : Blo 2003435 12848057 := bstep (se 2 (by rfl) ⟨4818021, by rfl⟩ : syracuseStep 12848057 = 9636043) B9636043
theorem B8565371 : Blo 2003435 8565371 := bstep (se 1 (by rfl) ⟨6424028, by rfl⟩ : syracuseStep 8565371 = 12848057) B12848057
theorem B5710247 : Blo 2003435 5710247 := bstep (se 1 (by rfl) ⟨4282685, by rfl⟩ : syracuseStep 5710247 = 8565371) B8565371
theorem B3806831 : Blo 2003435 3806831 := bstep (se 1 (by rfl) ⟨2855123, by rfl⟩ : syracuseStep 3806831 = 5710247) B5710247
theorem B2537887 : Blo 2003435 2537887 := bstep (se 1 (by rfl) ⟨1903415, by rfl⟩ : syracuseStep 2537887 = 3806831) B3806831
theorem B3383849 : Blo 2003435 3383849 := bstep (se 2 (by rfl) ⟨1268943, by rfl⟩ : syracuseStep 3383849 = 2537887) B2537887
theorem B2255899 : Blo 2003435 2255899 := bstep (se 1 (by rfl) ⟨1691924, by rfl⟩ : syracuseStep 2255899 = 3383849) B3383849
theorem B3007865 : Blo 2003435 3007865 := bstep (se 2 (by rfl) ⟨1127949, by rfl⟩ : syracuseStep 3007865 = 2255899) B2255899
theorem B2005243 : Blo 2003435 2005243 := bstep (se 1 (by rfl) ⟨1503932, by rfl⟩ : syracuseStep 2005243 = 3007865) B3007865
theorem B23152661 : Blo 2003435 23152661 := bbase (se 6 (by rfl) ⟨542640, by rfl⟩ : syracuseStep 23152661 = 1085281) (by norm_num)
theorem B15435107 : Blo 2003435 15435107 := bstep (se 1 (by rfl) ⟨11576330, by rfl⟩ : syracuseStep 15435107 = 23152661) B23152661
theorem B10290071 : Blo 2003435 10290071 := bstep (se 1 (by rfl) ⟨7717553, by rfl⟩ : syracuseStep 10290071 = 15435107) B15435107
theorem B6860047 : Blo 2003435 6860047 := bstep (se 1 (by rfl) ⟨5145035, by rfl⟩ : syracuseStep 6860047 = 10290071) B10290071
theorem B9146729 : Blo 2003435 9146729 := bstep (se 2 (by rfl) ⟨3430023, by rfl⟩ : syracuseStep 9146729 = 6860047) B6860047
theorem B24391277 : Blo 2003435 24391277 := bstep (se 3 (by rfl) ⟨4573364, by rfl⟩ : syracuseStep 24391277 = 9146729) B9146729
theorem B16260851 : Blo 2003435 16260851 := bstep (se 1 (by rfl) ⟨12195638, by rfl⟩ : syracuseStep 16260851 = 24391277) B24391277
theorem B10840567 : Blo 2003435 10840567 := bstep (se 1 (by rfl) ⟨8130425, by rfl⟩ : syracuseStep 10840567 = 16260851) B16260851
theorem B14454089 : Blo 2003435 14454089 := bstep (se 2 (by rfl) ⟨5420283, by rfl⟩ : syracuseStep 14454089 = 10840567) B10840567
theorem B9636059 : Blo 2003435 9636059 := bstep (se 1 (by rfl) ⟨7227044, by rfl⟩ : syracuseStep 9636059 = 14454089) B14454089
theorem B6424039 : Blo 2003435 6424039 := bstep (se 1 (by rfl) ⟨4818029, by rfl⟩ : syracuseStep 6424039 = 9636059) B9636059
theorem B34261541 : Blo 2003435 34261541 := bstep (se 4 (by rfl) ⟨3212019, by rfl⟩ : syracuseStep 34261541 = 6424039) B6424039
theorem B22841027 : Blo 2003435 22841027 := bstep (se 1 (by rfl) ⟨17130770, by rfl⟩ : syracuseStep 22841027 = 34261541) B34261541
theorem B15227351 : Blo 2003435 15227351 := bstep (se 1 (by rfl) ⟨11420513, by rfl⟩ : syracuseStep 15227351 = 22841027) B22841027
theorem B10151567 : Blo 2003435 10151567 := bstep (se 1 (by rfl) ⟨7613675, by rfl⟩ : syracuseStep 10151567 = 15227351) B15227351
theorem B6767711 : Blo 2003435 6767711 := bstep (se 1 (by rfl) ⟨5075783, by rfl⟩ : syracuseStep 6767711 = 10151567) B10151567
theorem B4511807 : Blo 2003435 4511807 := bstep (se 1 (by rfl) ⟨3383855, by rfl⟩ : syracuseStep 4511807 = 6767711) B6767711
theorem B3007871 : Blo 2003435 3007871 := bstep (se 1 (by rfl) ⟨2255903, by rfl⟩ : syracuseStep 3007871 = 4511807) B4511807
theorem B2005247 : Blo 2003435 2005247 := bstep (se 1 (by rfl) ⟨1503935, by rfl⟩ : syracuseStep 2005247 = 3007871) B3007871
theorem B3007877 : Blo 2003435 3007877 := bbase (se 4 (by rfl) ⟨281988, by rfl⟩ : syracuseStep 3007877 = 563977) (by norm_num)
theorem B2005251 : Blo 2003435 2005251 := bstep (se 1 (by rfl) ⟨1503938, by rfl⟩ : syracuseStep 2005251 = 3007877) B3007877
theorem B3383869 : Blo 2003435 3383869 := bbase (se 3 (by rfl) ⟨634475, by rfl⟩ : syracuseStep 3383869 = 1268951) (by norm_num)
theorem B4511825 : Blo 2003435 4511825 := bstep (se 2 (by rfl) ⟨1691934, by rfl⟩ : syracuseStep 4511825 = 3383869) B3383869
theorem B3007883 : Blo 2003435 3007883 := bstep (se 1 (by rfl) ⟨2255912, by rfl⟩ : syracuseStep 3007883 = 4511825) B4511825
theorem B2005255 : Blo 2003435 2005255 := bstep (se 1 (by rfl) ⟨1503941, by rfl⟩ : syracuseStep 2005255 = 3007883) B3007883
theorem B2255917 : Blo 2003435 2255917 := bbase (se 3 (by rfl) ⟨422984, by rfl⟩ : syracuseStep 2255917 = 845969) (by norm_num)
theorem B3007889 : Blo 2003435 3007889 := bstep (se 2 (by rfl) ⟨1127958, by rfl⟩ : syracuseStep 3007889 = 2255917) B2255917
theorem B2005259 : Blo 2003435 2005259 := bstep (se 1 (by rfl) ⟨1503944, by rfl⟩ : syracuseStep 2005259 = 3007889) B3007889
theorem B6767765 : Blo 2003435 6767765 := bbase (se 6 (by rfl) ⟨158619, by rfl⟩ : syracuseStep 6767765 = 317239) (by norm_num)
theorem B4511843 : Blo 2003435 4511843 := bstep (se 1 (by rfl) ⟨3383882, by rfl⟩ : syracuseStep 4511843 = 6767765) B6767765
theorem B3007895 : Blo 2003435 3007895 := bstep (se 1 (by rfl) ⟨2255921, by rfl⟩ : syracuseStep 3007895 = 4511843) B4511843
theorem B2005263 : Blo 2003435 2005263 := bstep (se 1 (by rfl) ⟨1503947, by rfl⟩ : syracuseStep 2005263 = 3007895) B3007895
theorem B3007901 : Blo 2003435 3007901 := bbase (se 3 (by rfl) ⟨563981, by rfl⟩ : syracuseStep 3007901 = 1127963) (by norm_num)
theorem B2005267 : Blo 2003435 2005267 := bstep (se 1 (by rfl) ⟨1503950, by rfl⟩ : syracuseStep 2005267 = 3007901) B3007901
theorem B4511861 : Blo 2003435 4511861 := bbase (se 5 (by rfl) ⟨211493, by rfl⟩ : syracuseStep 4511861 = 422987) (by norm_num)
theorem B3007907 : Blo 2003435 3007907 := bstep (se 1 (by rfl) ⟨2255930, by rfl⟩ : syracuseStep 3007907 = 4511861) B4511861
theorem B2005271 : Blo 2003435 2005271 := bstep (se 1 (by rfl) ⟨1503953, by rfl⟩ : syracuseStep 2005271 = 3007907) B3007907
theorem B2409049 : Blo 2003435 2409049 := bbase (se 2 (by rfl) ⟨903393, by rfl⟩ : syracuseStep 2409049 = 1806787) (by norm_num)
theorem B3212065 : Blo 2003435 3212065 := bstep (se 2 (by rfl) ⟨1204524, by rfl⟩ : syracuseStep 3212065 = 2409049) B2409049
theorem B17131013 : Blo 2003435 17131013 := bstep (se 4 (by rfl) ⟨1606032, by rfl⟩ : syracuseStep 17131013 = 3212065) B3212065
theorem B11420675 : Blo 2003435 11420675 := bstep (se 1 (by rfl) ⟨8565506, by rfl⟩ : syracuseStep 11420675 = 17131013) B17131013
theorem B7613783 : Blo 2003435 7613783 := bstep (se 1 (by rfl) ⟨5710337, by rfl⟩ : syracuseStep 7613783 = 11420675) B11420675
theorem B5075855 : Blo 2003435 5075855 := bstep (se 1 (by rfl) ⟨3806891, by rfl⟩ : syracuseStep 5075855 = 7613783) B7613783
theorem B3383903 : Blo 2003435 3383903 := bstep (se 1 (by rfl) ⟨2537927, by rfl⟩ : syracuseStep 3383903 = 5075855) B5075855
theorem B2255935 : Blo 2003435 2255935 := bstep (se 1 (by rfl) ⟨1691951, by rfl⟩ : syracuseStep 2255935 = 3383903) B3383903
theorem B3007913 : Blo 2003435 3007913 := bstep (se 2 (by rfl) ⟨1127967, by rfl⟩ : syracuseStep 3007913 = 2255935) B2255935
theorem B2005275 : Blo 2003435 2005275 := bstep (se 1 (by rfl) ⟨1503956, by rfl⟩ : syracuseStep 2005275 = 3007913) B3007913
theorem B7613797 : Blo 2003435 7613797 := bbase (se 4 (by rfl) ⟨713793, by rfl⟩ : syracuseStep 7613797 = 1427587) (by norm_num)
theorem B10151729 : Blo 2003435 10151729 := bstep (se 2 (by rfl) ⟨3806898, by rfl⟩ : syracuseStep 10151729 = 7613797) B7613797
theorem B6767819 : Blo 2003435 6767819 := bstep (se 1 (by rfl) ⟨5075864, by rfl⟩ : syracuseStep 6767819 = 10151729) B10151729
theorem B4511879 : Blo 2003435 4511879 := bstep (se 1 (by rfl) ⟨3383909, by rfl⟩ : syracuseStep 4511879 = 6767819) B6767819
theorem B3007919 : Blo 2003435 3007919 := bstep (se 1 (by rfl) ⟨2255939, by rfl⟩ : syracuseStep 3007919 = 4511879) B4511879
theorem B2005279 : Blo 2003435 2005279 := bstep (se 1 (by rfl) ⟨1503959, by rfl⟩ : syracuseStep 2005279 = 3007919) B3007919
theorem B3007925 : Blo 2003435 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B2005283 : Blo 2003435 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B5075885 : Blo 2003435 5075885 := bbase (se 3 (by rfl) ⟨951728, by rfl⟩ : syracuseStep 5075885 = 1903457) (by norm_num)
theorem B3383923 : Blo 2003435 3383923 := bstep (se 1 (by rfl) ⟨2537942, by rfl⟩ : syracuseStep 3383923 = 5075885) B5075885
theorem B4511897 : Blo 2003435 4511897 := bstep (se 2 (by rfl) ⟨1691961, by rfl⟩ : syracuseStep 4511897 = 3383923) B3383923
theorem B3007931 : Blo 2003435 3007931 := bstep (se 1 (by rfl) ⟨2255948, by rfl⟩ : syracuseStep 3007931 = 4511897) B4511897
theorem B2005287 : Blo 2003435 2005287 := bstep (se 1 (by rfl) ⟨1503965, by rfl⟩ : syracuseStep 2005287 = 3007931) B3007931
theorem B2255953 : Blo 2003435 2255953 := bbase (se 2 (by rfl) ⟨845982, by rfl⟩ : syracuseStep 2255953 = 1691965) (by norm_num)
theorem B3007937 : Blo 2003435 3007937 := bstep (se 2 (by rfl) ⟨1127976, by rfl⟩ : syracuseStep 3007937 = 2255953) B2255953
theorem B2005291 : Blo 2003435 2005291 := bstep (se 1 (by rfl) ⟨1503968, by rfl⟩ : syracuseStep 2005291 = 3007937) B3007937
theorem B2855197 : Blo 2003435 2855197 := bbase (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) (by norm_num)
theorem B3806929 : Blo 2003435 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B5075905 : Blo 2003435 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B6767873 : Blo 2003435 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B4511915 : Blo 2003435 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B3007943 : Blo 2003435 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B2005295 : Blo 2003435 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B3007949 : Blo 2003435 3007949 := bbase (se 3 (by rfl) ⟨563990, by rfl⟩ : syracuseStep 3007949 = 1127981) (by norm_num)
theorem B2005299 : Blo 2003435 2005299 := bstep (se 1 (by rfl) ⟨1503974, by rfl⟩ : syracuseStep 2005299 = 3007949) B3007949
theorem B4511933 : Blo 2003435 4511933 := bbase (se 3 (by rfl) ⟨845987, by rfl⟩ : syracuseStep 4511933 = 1691975) (by norm_num)
theorem B3007955 : Blo 2003435 3007955 := bstep (se 1 (by rfl) ⟨2255966, by rfl⟩ : syracuseStep 3007955 = 4511933) B4511933
theorem B2005303 : Blo 2003435 2005303 := bstep (se 1 (by rfl) ⟨1503977, by rfl⟩ : syracuseStep 2005303 = 3007955) B3007955
theorem B3383957 : Blo 2003435 3383957 := bbase (se 6 (by rfl) ⟨79311, by rfl⟩ : syracuseStep 3383957 = 158623) (by norm_num)
theorem B2255971 : Blo 2003435 2255971 := bstep (se 1 (by rfl) ⟨1691978, by rfl⟩ : syracuseStep 2255971 = 3383957) B3383957
theorem B3007961 : Blo 2003435 3007961 := bstep (se 2 (by rfl) ⟨1127985, by rfl⟩ : syracuseStep 3007961 = 2255971) B2255971
theorem B2005307 : Blo 2003435 2005307 := bstep (se 1 (by rfl) ⟨1503980, by rfl⟩ : syracuseStep 2005307 = 3007961) B3007961
theorem B28194965 : Blo 2003435 28194965 := bbase (se 6 (by rfl) ⟨660819, by rfl⟩ : syracuseStep 28194965 = 1321639) (by norm_num)
theorem B18796643 : Blo 2003435 18796643 := bstep (se 1 (by rfl) ⟨14097482, by rfl⟩ : syracuseStep 18796643 = 28194965) B28194965
theorem B12531095 : Blo 2003435 12531095 := bstep (se 1 (by rfl) ⟨9398321, by rfl⟩ : syracuseStep 12531095 = 18796643) B18796643
theorem B8354063 : Blo 2003435 8354063 := bstep (se 1 (by rfl) ⟨6265547, by rfl⟩ : syracuseStep 8354063 = 12531095) B12531095
theorem B22277501 : Blo 2003435 22277501 := bstep (se 3 (by rfl) ⟨4177031, by rfl⟩ : syracuseStep 22277501 = 8354063) B8354063
theorem B14851667 : Blo 2003435 14851667 := bstep (se 1 (by rfl) ⟨11138750, by rfl⟩ : syracuseStep 14851667 = 22277501) B22277501
theorem B9901111 : Blo 2003435 9901111 := bstep (se 1 (by rfl) ⟨7425833, by rfl⟩ : syracuseStep 9901111 = 14851667) B14851667
theorem B13201481 : Blo 2003435 13201481 := bstep (se 2 (by rfl) ⟨4950555, by rfl⟩ : syracuseStep 13201481 = 9901111) B9901111
theorem B8800987 : Blo 2003435 8800987 := bstep (se 1 (by rfl) ⟨6600740, by rfl⟩ : syracuseStep 8800987 = 13201481) B13201481
theorem B11734649 : Blo 2003435 11734649 := bstep (se 2 (by rfl) ⟨4400493, by rfl⟩ : syracuseStep 11734649 = 8800987) B8800987
theorem B7823099 : Blo 2003435 7823099 := bstep (se 1 (by rfl) ⟨5867324, by rfl⟩ : syracuseStep 7823099 = 11734649) B11734649
theorem B20861597 : Blo 2003435 20861597 := bstep (se 3 (by rfl) ⟨3911549, by rfl⟩ : syracuseStep 20861597 = 7823099) B7823099
theorem B55630925 : Blo 2003435 55630925 := bstep (se 3 (by rfl) ⟨10430798, by rfl⟩ : syracuseStep 55630925 = 20861597) B20861597
theorem B37087283 : Blo 2003435 37087283 := bstep (se 1 (by rfl) ⟨27815462, by rfl⟩ : syracuseStep 37087283 = 55630925) B55630925
theorem B24724855 : Blo 2003435 24724855 := bstep (se 1 (by rfl) ⟨18543641, by rfl⟩ : syracuseStep 24724855 = 37087283) B37087283
theorem B32966473 : Blo 2003435 32966473 := bstep (se 2 (by rfl) ⟨12362427, by rfl⟩ : syracuseStep 32966473 = 24724855) B24724855
theorem B43955297 : Blo 2003435 43955297 := bstep (se 2 (by rfl) ⟨16483236, by rfl⟩ : syracuseStep 43955297 = 32966473) B32966473
theorem B29303531 : Blo 2003435 29303531 := bstep (se 1 (by rfl) ⟨21977648, by rfl⟩ : syracuseStep 29303531 = 43955297) B43955297
theorem B19535687 : Blo 2003435 19535687 := bstep (se 1 (by rfl) ⟨14651765, by rfl⟩ : syracuseStep 19535687 = 29303531) B29303531
theorem B13023791 : Blo 2003435 13023791 := bstep (se 1 (by rfl) ⟨9767843, by rfl⟩ : syracuseStep 13023791 = 19535687) B19535687
theorem B8682527 : Blo 2003435 8682527 := bstep (se 1 (by rfl) ⟨6511895, by rfl⟩ : syracuseStep 8682527 = 13023791) B13023791
theorem B5788351 : Blo 2003435 5788351 := bstep (se 1 (by rfl) ⟨4341263, by rfl⟩ : syracuseStep 5788351 = 8682527) B8682527
theorem B7717801 : Blo 2003435 7717801 := bstep (se 2 (by rfl) ⟨2894175, by rfl⟩ : syracuseStep 7717801 = 5788351) B5788351
theorem B10290401 : Blo 2003435 10290401 := bstep (se 2 (by rfl) ⟨3858900, by rfl⟩ : syracuseStep 10290401 = 7717801) B7717801
theorem B6860267 : Blo 2003435 6860267 := bstep (se 1 (by rfl) ⟨5145200, by rfl⟩ : syracuseStep 6860267 = 10290401) B10290401
theorem B4573511 : Blo 2003435 4573511 := bstep (se 1 (by rfl) ⟨3430133, by rfl⟩ : syracuseStep 4573511 = 6860267) B6860267
theorem B3049007 : Blo 2003435 3049007 := bstep (se 1 (by rfl) ⟨2286755, by rfl⟩ : syracuseStep 3049007 = 4573511) B4573511
theorem B32522741 : Blo 2003435 32522741 := bstep (se 5 (by rfl) ⟨1524503, by rfl⟩ : syracuseStep 32522741 = 3049007) B3049007
theorem B21681827 : Blo 2003435 21681827 := bstep (se 1 (by rfl) ⟨16261370, by rfl⟩ : syracuseStep 21681827 = 32522741) B32522741
theorem B14454551 : Blo 2003435 14454551 := bstep (se 1 (by rfl) ⟨10840913, by rfl⟩ : syracuseStep 14454551 = 21681827) B21681827
theorem B9636367 : Blo 2003435 9636367 := bstep (se 1 (by rfl) ⟨7227275, by rfl⟩ : syracuseStep 9636367 = 14454551) B14454551
theorem B12848489 : Blo 2003435 12848489 := bstep (se 2 (by rfl) ⟨4818183, by rfl⟩ : syracuseStep 12848489 = 9636367) B9636367
theorem B8565659 : Blo 2003435 8565659 := bstep (se 1 (by rfl) ⟨6424244, by rfl⟩ : syracuseStep 8565659 = 12848489) B12848489
theorem B5710439 : Blo 2003435 5710439 := bstep (se 1 (by rfl) ⟨4282829, by rfl⟩ : syracuseStep 5710439 = 8565659) B8565659
theorem B15227837 : Blo 2003435 15227837 := bstep (se 3 (by rfl) ⟨2855219, by rfl⟩ : syracuseStep 15227837 = 5710439) B5710439
theorem B10151891 : Blo 2003435 10151891 := bstep (se 1 (by rfl) ⟨7613918, by rfl⟩ : syracuseStep 10151891 = 15227837) B15227837
theorem B6767927 : Blo 2003435 6767927 := bstep (se 1 (by rfl) ⟨5075945, by rfl⟩ : syracuseStep 6767927 = 10151891) B10151891
theorem B4511951 : Blo 2003435 4511951 := bstep (se 1 (by rfl) ⟨3383963, by rfl⟩ : syracuseStep 4511951 = 6767927) B6767927
theorem B3007967 : Blo 2003435 3007967 := bstep (se 1 (by rfl) ⟨2255975, by rfl⟩ : syracuseStep 3007967 = 4511951) B4511951
theorem B2005311 : Blo 2003435 2005311 := bstep (se 1 (by rfl) ⟨1503983, by rfl⟩ : syracuseStep 2005311 = 3007967) B3007967
theorem B3007973 : Blo 2003435 3007973 := bbase (se 4 (by rfl) ⟨281997, by rfl⟩ : syracuseStep 3007973 = 563995) (by norm_num)
theorem B2005315 : Blo 2003435 2005315 := bstep (se 1 (by rfl) ⟨1503986, by rfl⟩ : syracuseStep 2005315 = 3007973) B3007973
theorem B5215421 : Blo 2003435 5215421 := bbase (se 3 (by rfl) ⟨977891, by rfl⟩ : syracuseStep 5215421 = 1955783) (by norm_num)
theorem B3476947 : Blo 2003435 3476947 := bstep (se 1 (by rfl) ⟨2607710, by rfl⟩ : syracuseStep 3476947 = 5215421) B5215421
theorem B4635929 : Blo 2003435 4635929 := bstep (se 2 (by rfl) ⟨1738473, by rfl⟩ : syracuseStep 4635929 = 3476947) B3476947
theorem B3090619 : Blo 2003435 3090619 := bstep (se 1 (by rfl) ⟨2317964, by rfl⟩ : syracuseStep 3090619 = 4635929) B4635929
theorem B16483301 : Blo 2003435 16483301 := bstep (se 4 (by rfl) ⟨1545309, by rfl⟩ : syracuseStep 16483301 = 3090619) B3090619
theorem B10988867 : Blo 2003435 10988867 := bstep (se 1 (by rfl) ⟨8241650, by rfl⟩ : syracuseStep 10988867 = 16483301) B16483301
theorem B7325911 : Blo 2003435 7325911 := bstep (se 1 (by rfl) ⟨5494433, by rfl⟩ : syracuseStep 7325911 = 10988867) B10988867
theorem B9767881 : Blo 2003435 9767881 := bstep (se 2 (by rfl) ⟨3662955, by rfl⟩ : syracuseStep 9767881 = 7325911) B7325911
theorem B13023841 : Blo 2003435 13023841 := bstep (se 2 (by rfl) ⟨4883940, by rfl⟩ : syracuseStep 13023841 = 9767881) B9767881
theorem B17365121 : Blo 2003435 17365121 := bstep (se 2 (by rfl) ⟨6511920, by rfl⟩ : syracuseStep 17365121 = 13023841) B13023841
theorem B11576747 : Blo 2003435 11576747 := bstep (se 1 (by rfl) ⟨8682560, by rfl⟩ : syracuseStep 11576747 = 17365121) B17365121
theorem B30871325 : Blo 2003435 30871325 := bstep (se 3 (by rfl) ⟨5788373, by rfl⟩ : syracuseStep 30871325 = 11576747) B11576747
theorem B82323533 : Blo 2003435 82323533 := bstep (se 3 (by rfl) ⟨15435662, by rfl⟩ : syracuseStep 82323533 = 30871325) B30871325
theorem B54882355 : Blo 2003435 54882355 := bstep (se 1 (by rfl) ⟨41161766, by rfl⟩ : syracuseStep 54882355 = 82323533) B82323533
theorem B73176473 : Blo 2003435 73176473 := bstep (se 2 (by rfl) ⟨27441177, by rfl⟩ : syracuseStep 73176473 = 54882355) B54882355
theorem B48784315 : Blo 2003435 48784315 := bstep (se 1 (by rfl) ⟨36588236, by rfl⟩ : syracuseStep 48784315 = 73176473) B73176473
theorem B65045753 : Blo 2003435 65045753 := bstep (se 2 (by rfl) ⟨24392157, by rfl⟩ : syracuseStep 65045753 = 48784315) B48784315
theorem B43363835 : Blo 2003435 43363835 := bstep (se 1 (by rfl) ⟨32522876, by rfl⟩ : syracuseStep 43363835 = 65045753) B65045753
theorem B28909223 : Blo 2003435 28909223 := bstep (se 1 (by rfl) ⟨21681917, by rfl⟩ : syracuseStep 28909223 = 43363835) B43363835
theorem B19272815 : Blo 2003435 19272815 := bstep (se 1 (by rfl) ⟨14454611, by rfl⟩ : syracuseStep 19272815 = 28909223) B28909223
theorem B12848543 : Blo 2003435 12848543 := bstep (se 1 (by rfl) ⟨9636407, by rfl⟩ : syracuseStep 12848543 = 19272815) B19272815
theorem B8565695 : Blo 2003435 8565695 := bstep (se 1 (by rfl) ⟨6424271, by rfl⟩ : syracuseStep 8565695 = 12848543) B12848543
theorem B5710463 : Blo 2003435 5710463 := bstep (se 1 (by rfl) ⟨4282847, by rfl⟩ : syracuseStep 5710463 = 8565695) B8565695
theorem B3806975 : Blo 2003435 3806975 := bstep (se 1 (by rfl) ⟨2855231, by rfl⟩ : syracuseStep 3806975 = 5710463) B5710463
theorem B2537983 : Blo 2003435 2537983 := bstep (se 1 (by rfl) ⟨1903487, by rfl⟩ : syracuseStep 2537983 = 3806975) B3806975
theorem B3383977 : Blo 2003435 3383977 := bstep (se 2 (by rfl) ⟨1268991, by rfl⟩ : syracuseStep 3383977 = 2537983) B2537983
theorem B4511969 : Blo 2003435 4511969 := bstep (se 2 (by rfl) ⟨1691988, by rfl⟩ : syracuseStep 4511969 = 3383977) B3383977
theorem B3007979 : Blo 2003435 3007979 := bstep (se 1 (by rfl) ⟨2255984, by rfl⟩ : syracuseStep 3007979 = 4511969) B4511969
theorem B2005319 : Blo 2003435 2005319 := bstep (se 1 (by rfl) ⟨1503989, by rfl⟩ : syracuseStep 2005319 = 3007979) B3007979
theorem B2255989 : Blo 2003435 2255989 := bbase (se 5 (by rfl) ⟨105749, by rfl⟩ : syracuseStep 2255989 = 211499) (by norm_num)
theorem B3007985 : Blo 2003435 3007985 := bstep (se 2 (by rfl) ⟨1127994, by rfl⟩ : syracuseStep 3007985 = 2255989) B2255989
theorem B2005323 : Blo 2003435 2005323 := bstep (se 1 (by rfl) ⟨1503992, by rfl⟩ : syracuseStep 2005323 = 3007985) B3007985
theorem B2537993 : Blo 2003435 2537993 := bbase (se 2 (by rfl) ⟨951747, by rfl⟩ : syracuseStep 2537993 = 1903495) (by norm_num)
theorem B6767981 : Blo 2003435 6767981 := bstep (se 3 (by rfl) ⟨1268996, by rfl⟩ : syracuseStep 6767981 = 2537993) B2537993
theorem B4511987 : Blo 2003435 4511987 := bstep (se 1 (by rfl) ⟨3383990, by rfl⟩ : syracuseStep 4511987 = 6767981) B6767981
theorem B3007991 : Blo 2003435 3007991 := bstep (se 1 (by rfl) ⟨2255993, by rfl⟩ : syracuseStep 3007991 = 4511987) B4511987
theorem B2005327 : Blo 2003435 2005327 := bstep (se 1 (by rfl) ⟨1503995, by rfl⟩ : syracuseStep 2005327 = 3007991) B3007991
theorem B3007997 : Blo 2003435 3007997 := bbase (se 3 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 3007997 = 1127999) (by norm_num)
theorem B2005331 : Blo 2003435 2005331 := bstep (se 1 (by rfl) ⟨1503998, by rfl⟩ : syracuseStep 2005331 = 3007997) B3007997
theorem B4512005 : Blo 2003435 4512005 := bbase (se 4 (by rfl) ⟨423000, by rfl⟩ : syracuseStep 4512005 = 846001) (by norm_num)
theorem B3008003 : Blo 2003435 3008003 := bstep (se 1 (by rfl) ⟨2256002, by rfl⟩ : syracuseStep 3008003 = 4512005) B4512005
theorem B2005335 : Blo 2003435 2005335 := bstep (se 1 (by rfl) ⟨1504001, by rfl⟩ : syracuseStep 2005335 = 3008003) B3008003
theorem B3807013 : Blo 2003435 3807013 := bbase (se 4 (by rfl) ⟨356907, by rfl⟩ : syracuseStep 3807013 = 713815) (by norm_num)
theorem B5076017 : Blo 2003435 5076017 := bstep (se 2 (by rfl) ⟨1903506, by rfl⟩ : syracuseStep 5076017 = 3807013) B3807013
theorem B3384011 : Blo 2003435 3384011 := bstep (se 1 (by rfl) ⟨2538008, by rfl⟩ : syracuseStep 3384011 = 5076017) B5076017
theorem B2256007 : Blo 2003435 2256007 := bstep (se 1 (by rfl) ⟨1692005, by rfl⟩ : syracuseStep 2256007 = 3384011) B3384011
theorem B3008009 : Blo 2003435 3008009 := bstep (se 2 (by rfl) ⟨1128003, by rfl⟩ : syracuseStep 3008009 = 2256007) B2256007
theorem B2005339 : Blo 2003435 2005339 := bstep (se 1 (by rfl) ⟨1504004, by rfl⟩ : syracuseStep 2005339 = 3008009) B3008009
theorem B10152053 : Blo 2003435 10152053 := bbase (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) (by norm_num)
theorem B6768035 : Blo 2003435 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B4512023 : Blo 2003435 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B3008015 : Blo 2003435 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B2005343 : Blo 2003435 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B3008021 : Blo 2003435 3008021 := bbase (se 6 (by rfl) ⟨70500, by rfl⟩ : syracuseStep 3008021 = 141001) (by norm_num)
theorem B2005347 : Blo 2003435 2005347 := bstep (se 1 (by rfl) ⟨1504010, by rfl⟩ : syracuseStep 2005347 = 3008021) B3008021
theorem B6424373 : Blo 2003435 6424373 := bbase (se 5 (by rfl) ⟨301142, by rfl⟩ : syracuseStep 6424373 = 602285) (by norm_num)
theorem B17131661 : Blo 2003435 17131661 := bstep (se 3 (by rfl) ⟨3212186, by rfl⟩ : syracuseStep 17131661 = 6424373) B6424373
theorem B11421107 : Blo 2003435 11421107 := bstep (se 1 (by rfl) ⟨8565830, by rfl⟩ : syracuseStep 11421107 = 17131661) B17131661
theorem B7614071 : Blo 2003435 7614071 := bstep (se 1 (by rfl) ⟨5710553, by rfl⟩ : syracuseStep 7614071 = 11421107) B11421107
theorem B5076047 : Blo 2003435 5076047 := bstep (se 1 (by rfl) ⟨3807035, by rfl⟩ : syracuseStep 5076047 = 7614071) B7614071
theorem B3384031 : Blo 2003435 3384031 := bstep (se 1 (by rfl) ⟨2538023, by rfl⟩ : syracuseStep 3384031 = 5076047) B5076047
theorem B4512041 : Blo 2003435 4512041 := bstep (se 2 (by rfl) ⟨1692015, by rfl⟩ : syracuseStep 4512041 = 3384031) B3384031
theorem B3008027 : Blo 2003435 3008027 := bstep (se 1 (by rfl) ⟨2256020, by rfl⟩ : syracuseStep 3008027 = 4512041) B4512041
theorem B2005351 : Blo 2003435 2005351 := bstep (se 1 (by rfl) ⟨1504013, by rfl⟩ : syracuseStep 2005351 = 3008027) B3008027
theorem B2256025 : Blo 2003435 2256025 := bbase (se 2 (by rfl) ⟨846009, by rfl⟩ : syracuseStep 2256025 = 1692019) (by norm_num)
theorem B3008033 : Blo 2003435 3008033 := bstep (se 2 (by rfl) ⟨1128012, by rfl⟩ : syracuseStep 3008033 = 2256025) B2256025
theorem B2005355 : Blo 2003435 2005355 := bstep (se 1 (by rfl) ⟨1504016, by rfl⟩ : syracuseStep 2005355 = 3008033) B3008033
theorem B7614101 : Blo 2003435 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B5076067 : Blo 2003435 5076067 := bstep (se 1 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 5076067 = 7614101) B7614101
theorem B6768089 : Blo 2003435 6768089 := bstep (se 2 (by rfl) ⟨2538033, by rfl⟩ : syracuseStep 6768089 = 5076067) B5076067
theorem B4512059 : Blo 2003435 4512059 := bstep (se 1 (by rfl) ⟨3384044, by rfl⟩ : syracuseStep 4512059 = 6768089) B6768089
theorem B3008039 : Blo 2003435 3008039 := bstep (se 1 (by rfl) ⟨2256029, by rfl⟩ : syracuseStep 3008039 = 4512059) B4512059
theorem B2005359 : Blo 2003435 2005359 := bstep (se 1 (by rfl) ⟨1504019, by rfl⟩ : syracuseStep 2005359 = 3008039) B3008039
theorem B3008045 : Blo 2003435 3008045 := bbase (se 3 (by rfl) ⟨564008, by rfl⟩ : syracuseStep 3008045 = 1128017) (by norm_num)
theorem B2005363 : Blo 2003435 2005363 := bstep (se 1 (by rfl) ⟨1504022, by rfl⟩ : syracuseStep 2005363 = 3008045) B3008045
theorem B4512077 : Blo 2003435 4512077 := bbase (se 3 (by rfl) ⟨846014, by rfl⟩ : syracuseStep 4512077 = 1692029) (by norm_num)
theorem B3008051 : Blo 2003435 3008051 := bstep (se 1 (by rfl) ⟨2256038, by rfl⟩ : syracuseStep 3008051 = 4512077) B4512077
theorem B2005367 : Blo 2003435 2005367 := bstep (se 1 (by rfl) ⟨1504025, by rfl⟩ : syracuseStep 2005367 = 3008051) B3008051
theorem B2538049 : Blo 2003435 2538049 := bbase (se 2 (by rfl) ⟨951768, by rfl⟩ : syracuseStep 2538049 = 1903537) (by norm_num)
theorem B3384065 : Blo 2003435 3384065 := bstep (se 2 (by rfl) ⟨1269024, by rfl⟩ : syracuseStep 3384065 = 2538049) B2538049
theorem B2256043 : Blo 2003435 2256043 := bstep (se 1 (by rfl) ⟨1692032, by rfl⟩ : syracuseStep 2256043 = 3384065) B3384065
theorem B3008057 : Blo 2003435 3008057 := bstep (se 2 (by rfl) ⟨1128021, by rfl⟩ : syracuseStep 3008057 = 2256043) B2256043
theorem B2005371 : Blo 2003435 2005371 := bstep (se 1 (by rfl) ⟨1504028, by rfl⟩ : syracuseStep 2005371 = 3008057) B3008057
theorem B2409169 : Blo 2003435 2409169 := bbase (se 2 (by rfl) ⟨903438, by rfl⟩ : syracuseStep 2409169 = 1806877) (by norm_num)
theorem B3212225 : Blo 2003435 3212225 := bstep (se 2 (by rfl) ⟨1204584, by rfl⟩ : syracuseStep 3212225 = 2409169) B2409169
theorem B2141483 : Blo 2003435 2141483 := bstep (se 1 (by rfl) ⟨1606112, by rfl⟩ : syracuseStep 2141483 = 3212225) B3212225
theorem B22842485 : Blo 2003435 22842485 := bstep (se 5 (by rfl) ⟨1070741, by rfl⟩ : syracuseStep 22842485 = 2141483) B2141483
theorem B15228323 : Blo 2003435 15228323 := bstep (se 1 (by rfl) ⟨11421242, by rfl⟩ : syracuseStep 15228323 = 22842485) B22842485
theorem B10152215 : Blo 2003435 10152215 := bstep (se 1 (by rfl) ⟨7614161, by rfl⟩ : syracuseStep 10152215 = 15228323) B15228323
theorem B6768143 : Blo 2003435 6768143 := bstep (se 1 (by rfl) ⟨5076107, by rfl⟩ : syracuseStep 6768143 = 10152215) B10152215
theorem B4512095 : Blo 2003435 4512095 := bstep (se 1 (by rfl) ⟨3384071, by rfl⟩ : syracuseStep 4512095 = 6768143) B6768143
theorem B3008063 : Blo 2003435 3008063 := bstep (se 1 (by rfl) ⟨2256047, by rfl⟩ : syracuseStep 3008063 = 4512095) B4512095
theorem B2005375 : Blo 2003435 2005375 := bstep (se 1 (by rfl) ⟨1504031, by rfl⟩ : syracuseStep 2005375 = 3008063) B3008063
theorem B3008069 : Blo 2003435 3008069 := bbase (se 4 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 3008069 = 564013) (by norm_num)
theorem B2005379 : Blo 2003435 2005379 := bstep (se 1 (by rfl) ⟨1504034, by rfl⟩ : syracuseStep 2005379 = 3008069) B3008069
theorem B3384085 : Blo 2003435 3384085 := bbase (se 6 (by rfl) ⟨79314, by rfl⟩ : syracuseStep 3384085 = 158629) (by norm_num)
theorem B4512113 : Blo 2003435 4512113 := bstep (se 2 (by rfl) ⟨1692042, by rfl⟩ : syracuseStep 4512113 = 3384085) B3384085
theorem B3008075 : Blo 2003435 3008075 := bstep (se 1 (by rfl) ⟨2256056, by rfl⟩ : syracuseStep 3008075 = 4512113) B4512113
theorem B2005383 : Blo 2003435 2005383 := bstep (se 1 (by rfl) ⟨1504037, by rfl⟩ : syracuseStep 2005383 = 3008075) B3008075
theorem B2256061 : Blo 2003435 2256061 := bbase (se 3 (by rfl) ⟨423011, by rfl⟩ : syracuseStep 2256061 = 846023) (by norm_num)
theorem B3008081 : Blo 2003435 3008081 := bstep (se 2 (by rfl) ⟨1128030, by rfl⟩ : syracuseStep 3008081 = 2256061) B2256061
theorem B2005387 : Blo 2003435 2005387 := bstep (se 1 (by rfl) ⟨1504040, by rfl⟩ : syracuseStep 2005387 = 3008081) B3008081
theorem B6768197 : Blo 2003435 6768197 := bbase (se 4 (by rfl) ⟨634518, by rfl⟩ : syracuseStep 6768197 = 1269037) (by norm_num)
theorem B4512131 : Blo 2003435 4512131 := bstep (se 1 (by rfl) ⟨3384098, by rfl⟩ : syracuseStep 4512131 = 6768197) B6768197
theorem B3008087 : Blo 2003435 3008087 := bstep (se 1 (by rfl) ⟨2256065, by rfl⟩ : syracuseStep 3008087 = 4512131) B4512131
theorem B2005391 : Blo 2003435 2005391 := bstep (se 1 (by rfl) ⟨1504043, by rfl⟩ : syracuseStep 2005391 = 3008087) B3008087
theorem B3008093 : Blo 2003435 3008093 := bbase (se 3 (by rfl) ⟨564017, by rfl⟩ : syracuseStep 3008093 = 1128035) (by norm_num)
theorem B2005395 : Blo 2003435 2005395 := bstep (se 1 (by rfl) ⟨1504046, by rfl⟩ : syracuseStep 2005395 = 3008093) B3008093
theorem B4512149 : Blo 2003435 4512149 := bbase (se 6 (by rfl) ⟨105753, by rfl⟩ : syracuseStep 4512149 = 211507) (by norm_num)
theorem B3008099 : Blo 2003435 3008099 := bstep (se 1 (by rfl) ⟨2256074, by rfl⟩ : syracuseStep 3008099 = 4512149) B4512149
theorem B2005399 : Blo 2003435 2005399 := bstep (se 1 (by rfl) ⟨1504049, by rfl⟩ : syracuseStep 2005399 = 3008099) B3008099
theorem B3613805 : Blo 2003435 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B2409203 : Blo 2003435 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B6424541 : Blo 2003435 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B4283027 : Blo 2003435 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B2855351 : Blo 2003435 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B7614269 : Blo 2003435 7614269 := bstep (se 3 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 7614269 = 2855351) B2855351
theorem B5076179 : Blo 2003435 5076179 := bstep (se 1 (by rfl) ⟨3807134, by rfl⟩ : syracuseStep 5076179 = 7614269) B7614269
theorem B3384119 : Blo 2003435 3384119 := bstep (se 1 (by rfl) ⟨2538089, by rfl⟩ : syracuseStep 3384119 = 5076179) B5076179
theorem B2256079 : Blo 2003435 2256079 := bstep (se 1 (by rfl) ⟨1692059, by rfl⟩ : syracuseStep 2256079 = 3384119) B3384119
theorem B3008105 : Blo 2003435 3008105 := bstep (se 2 (by rfl) ⟨1128039, by rfl⟩ : syracuseStep 3008105 = 2256079) B2256079
theorem B2005403 : Blo 2003435 2005403 := bstep (se 1 (by rfl) ⟨1504052, by rfl⟩ : syracuseStep 2005403 = 3008105) B3008105
theorem B8566069 : Blo 2003435 8566069 := bbase (se 5 (by rfl) ⟨401534, by rfl⟩ : syracuseStep 8566069 = 803069) (by norm_num)
theorem B11421425 : Blo 2003435 11421425 := bstep (se 2 (by rfl) ⟨4283034, by rfl⟩ : syracuseStep 11421425 = 8566069) B8566069
theorem B7614283 : Blo 2003435 7614283 := bstep (se 1 (by rfl) ⟨5710712, by rfl⟩ : syracuseStep 7614283 = 11421425) B11421425
theorem B10152377 : Blo 2003435 10152377 := bstep (se 2 (by rfl) ⟨3807141, by rfl⟩ : syracuseStep 10152377 = 7614283) B7614283
theorem B6768251 : Blo 2003435 6768251 := bstep (se 1 (by rfl) ⟨5076188, by rfl⟩ : syracuseStep 6768251 = 10152377) B10152377
theorem B4512167 : Blo 2003435 4512167 := bstep (se 1 (by rfl) ⟨3384125, by rfl⟩ : syracuseStep 4512167 = 6768251) B6768251
theorem B3008111 : Blo 2003435 3008111 := bstep (se 1 (by rfl) ⟨2256083, by rfl⟩ : syracuseStep 3008111 = 4512167) B4512167
theorem B2005407 : Blo 2003435 2005407 := bstep (se 1 (by rfl) ⟨1504055, by rfl⟩ : syracuseStep 2005407 = 3008111) B3008111
theorem B3008117 : Blo 2003435 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B2005411 : Blo 2003435 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B3807157 : Blo 2003435 3807157 := bbase (se 5 (by rfl) ⟨178460, by rfl⟩ : syracuseStep 3807157 = 356921) (by norm_num)
theorem B5076209 : Blo 2003435 5076209 := bstep (se 2 (by rfl) ⟨1903578, by rfl⟩ : syracuseStep 5076209 = 3807157) B3807157
theorem B3384139 : Blo 2003435 3384139 := bstep (se 1 (by rfl) ⟨2538104, by rfl⟩ : syracuseStep 3384139 = 5076209) B5076209
theorem B4512185 : Blo 2003435 4512185 := bstep (se 2 (by rfl) ⟨1692069, by rfl⟩ : syracuseStep 4512185 = 3384139) B3384139
theorem B3008123 : Blo 2003435 3008123 := bstep (se 1 (by rfl) ⟨2256092, by rfl⟩ : syracuseStep 3008123 = 4512185) B4512185
theorem B2005415 : Blo 2003435 2005415 := bstep (se 1 (by rfl) ⟨1504061, by rfl⟩ : syracuseStep 2005415 = 3008123) B3008123
theorem B2256097 : Blo 2003435 2256097 := bbase (se 2 (by rfl) ⟨846036, by rfl⟩ : syracuseStep 2256097 = 1692073) (by norm_num)
theorem B3008129 : Blo 2003435 3008129 := bstep (se 2 (by rfl) ⟨1128048, by rfl⟩ : syracuseStep 3008129 = 2256097) B2256097
theorem B2005419 : Blo 2003435 2005419 := bstep (se 1 (by rfl) ⟨1504064, by rfl⟩ : syracuseStep 2005419 = 3008129) B3008129
theorem B5076229 : Blo 2003435 5076229 := bbase (se 4 (by rfl) ⟨475896, by rfl⟩ : syracuseStep 5076229 = 951793) (by norm_num)
theorem B6768305 : Blo 2003435 6768305 := bstep (se 2 (by rfl) ⟨2538114, by rfl⟩ : syracuseStep 6768305 = 5076229) B5076229
theorem B4512203 : Blo 2003435 4512203 := bstep (se 1 (by rfl) ⟨3384152, by rfl⟩ : syracuseStep 4512203 = 6768305) B6768305
theorem B3008135 : Blo 2003435 3008135 := bstep (se 1 (by rfl) ⟨2256101, by rfl⟩ : syracuseStep 3008135 = 4512203) B4512203
theorem B2005423 : Blo 2003435 2005423 := bstep (se 1 (by rfl) ⟨1504067, by rfl⟩ : syracuseStep 2005423 = 3008135) B3008135
theorem B3008141 : Blo 2003435 3008141 := bbase (se 3 (by rfl) ⟨564026, by rfl⟩ : syracuseStep 3008141 = 1128053) (by norm_num)
theorem B2005427 : Blo 2003435 2005427 := bstep (se 1 (by rfl) ⟨1504070, by rfl⟩ : syracuseStep 2005427 = 3008141) B3008141
theorem B4512221 : Blo 2003435 4512221 := bbase (se 3 (by rfl) ⟨846041, by rfl⟩ : syracuseStep 4512221 = 1692083) (by norm_num)
theorem B3008147 : Blo 2003435 3008147 := bstep (se 1 (by rfl) ⟨2256110, by rfl⟩ : syracuseStep 3008147 = 4512221) B4512221
theorem B2005431 : Blo 2003435 2005431 := bstep (se 1 (by rfl) ⟨1504073, by rfl⟩ : syracuseStep 2005431 = 3008147) B3008147
theorem B3384173 : Blo 2003435 3384173 := bbase (se 3 (by rfl) ⟨634532, by rfl⟩ : syracuseStep 3384173 = 1269065) (by norm_num)
theorem B2256115 : Blo 2003435 2256115 := bstep (se 1 (by rfl) ⟨1692086, by rfl⟩ : syracuseStep 2256115 = 3384173) B3384173
theorem B3008153 : Blo 2003435 3008153 := bstep (se 2 (by rfl) ⟨1128057, by rfl⟩ : syracuseStep 3008153 = 2256115) B2256115
theorem B2005435 : Blo 2003435 2005435 := bstep (se 1 (by rfl) ⟨1504076, by rfl⟩ : syracuseStep 2005435 = 3008153) B3008153
theorem C0 (j : ℕ) (h1 : 500858 ≤ j) (h2 : j ≤ 501358) : Blo 2003435 (4 * j + 3) := by
  interval_cases j
  · exact B2003435
  · exact B2003439
  · exact B2003443
  · exact B2003447
  · exact B2003451
  · exact B2003455
  · exact B2003459
  · exact B2003463
  · exact B2003467
  · exact B2003471
  · exact B2003475
  · exact B2003479
  · exact B2003483
  · exact B2003487
  · exact B2003491
  · exact B2003495
  · exact B2003499
  · exact B2003503
  · exact B2003507
  · exact B2003511
  · exact B2003515
  · exact B2003519
  · exact B2003523
  · exact B2003527
  · exact B2003531
  · exact B2003535
  · exact B2003539
  · exact B2003543
  · exact B2003547
  · exact B2003551
  · exact B2003555
  · exact B2003559
  · exact B2003563
  · exact B2003567
  · exact B2003571
  · exact B2003575
  · exact B2003579
  · exact B2003583
  · exact B2003587
  · exact B2003591
  · exact B2003595
  · exact B2003599
  · exact B2003603
  · exact B2003607
  · exact B2003611
  · exact B2003615
  · exact B2003619
  · exact B2003623
  · exact B2003627
  · exact B2003631
  · exact B2003635
  · exact B2003639
  · exact B2003643
  · exact B2003647
  · exact B2003651
  · exact B2003655
  · exact B2003659
  · exact B2003663
  · exact B2003667
  · exact B2003671
  · exact B2003675
  · exact B2003679
  · exact B2003683
  · exact B2003687
  · exact B2003691
  · exact B2003695
  · exact B2003699
  · exact B2003703
  · exact B2003707
  · exact B2003711
  · exact B2003715
  · exact B2003719
  · exact B2003723
  · exact B2003727
  · exact B2003731
  · exact B2003735
  · exact B2003739
  · exact B2003743
  · exact B2003747
  · exact B2003751
  · exact B2003755
  · exact B2003759
  · exact B2003763
  · exact B2003767
  · exact B2003771
  · exact B2003775
  · exact B2003779
  · exact B2003783
  · exact B2003787
  · exact B2003791
  · exact B2003795
  · exact B2003799
  · exact B2003803
  · exact B2003807
  · exact B2003811
  · exact B2003815
  · exact B2003819
  · exact B2003823
  · exact B2003827
  · exact B2003831
  · exact B2003835
  · exact B2003839
  · exact B2003843
  · exact B2003847
  · exact B2003851
  · exact B2003855
  · exact B2003859
  · exact B2003863
  · exact B2003867
  · exact B2003871
  · exact B2003875
  · exact B2003879
  · exact B2003883
  · exact B2003887
  · exact B2003891
  · exact B2003895
  · exact B2003899
  · exact B2003903
  · exact B2003907
  · exact B2003911
  · exact B2003915
  · exact B2003919
  · exact B2003923
  · exact B2003927
  · exact B2003931
  · exact B2003935
  · exact B2003939
  · exact B2003943
  · exact B2003947
  · exact B2003951
  · exact B2003955
  · exact B2003959
  · exact B2003963
  · exact B2003967
  · exact B2003971
  · exact B2003975
  · exact B2003979
  · exact B2003983
  · exact B2003987
  · exact B2003991
  · exact B2003995
  · exact B2003999
  · exact B2004003
  · exact B2004007
  · exact B2004011
  · exact B2004015
  · exact B2004019
  · exact B2004023
  · exact B2004027
  · exact B2004031
  · exact B2004035
  · exact B2004039
  · exact B2004043
  · exact B2004047
  · exact B2004051
  · exact B2004055
  · exact B2004059
  · exact B2004063
  · exact B2004067
  · exact B2004071
  · exact B2004075
  · exact B2004079
  · exact B2004083
  · exact B2004087
  · exact B2004091
  · exact B2004095
  · exact B2004099
  · exact B2004103
  · exact B2004107
  · exact B2004111
  · exact B2004115
  · exact B2004119
  · exact B2004123
  · exact B2004127
  · exact B2004131
  · exact B2004135
  · exact B2004139
  · exact B2004143
  · exact B2004147
  · exact B2004151
  · exact B2004155
  · exact B2004159
  · exact B2004163
  · exact B2004167
  · exact B2004171
  · exact B2004175
  · exact B2004179
  · exact B2004183
  · exact B2004187
  · exact B2004191
  · exact B2004195
  · exact B2004199
  · exact B2004203
  · exact B2004207
  · exact B2004211
  · exact B2004215
  · exact B2004219
  · exact B2004223
  · exact B2004227
  · exact B2004231
  · exact B2004235
  · exact B2004239
  · exact B2004243
  · exact B2004247
  · exact B2004251
  · exact B2004255
  · exact B2004259
  · exact B2004263
  · exact B2004267
  · exact B2004271
  · exact B2004275
  · exact B2004279
  · exact B2004283
  · exact B2004287
  · exact B2004291
  · exact B2004295
  · exact B2004299
  · exact B2004303
  · exact B2004307
  · exact B2004311
  · exact B2004315
  · exact B2004319
  · exact B2004323
  · exact B2004327
  · exact B2004331
  · exact B2004335
  · exact B2004339
  · exact B2004343
  · exact B2004347
  · exact B2004351
  · exact B2004355
  · exact B2004359
  · exact B2004363
  · exact B2004367
  · exact B2004371
  · exact B2004375
  · exact B2004379
  · exact B2004383
  · exact B2004387
  · exact B2004391
  · exact B2004395
  · exact B2004399
  · exact B2004403
  · exact B2004407
  · exact B2004411
  · exact B2004415
  · exact B2004419
  · exact B2004423
  · exact B2004427
  · exact B2004431
  · exact B2004435
  · exact B2004439
  · exact B2004443
  · exact B2004447
  · exact B2004451
  · exact B2004455
  · exact B2004459
  · exact B2004463
  · exact B2004467
  · exact B2004471
  · exact B2004475
  · exact B2004479
  · exact B2004483
  · exact B2004487
  · exact B2004491
  · exact B2004495
  · exact B2004499
  · exact B2004503
  · exact B2004507
  · exact B2004511
  · exact B2004515
  · exact B2004519
  · exact B2004523
  · exact B2004527
  · exact B2004531
  · exact B2004535
  · exact B2004539
  · exact B2004543
  · exact B2004547
  · exact B2004551
  · exact B2004555
  · exact B2004559
  · exact B2004563
  · exact B2004567
  · exact B2004571
  · exact B2004575
  · exact B2004579
  · exact B2004583
  · exact B2004587
  · exact B2004591
  · exact B2004595
  · exact B2004599
  · exact B2004603
  · exact B2004607
  · exact B2004611
  · exact B2004615
  · exact B2004619
  · exact B2004623
  · exact B2004627
  · exact B2004631
  · exact B2004635
  · exact B2004639
  · exact B2004643
  · exact B2004647
  · exact B2004651
  · exact B2004655
  · exact B2004659
  · exact B2004663
  · exact B2004667
  · exact B2004671
  · exact B2004675
  · exact B2004679
  · exact B2004683
  · exact B2004687
  · exact B2004691
  · exact B2004695
  · exact B2004699
  · exact B2004703
  · exact B2004707
  · exact B2004711
  · exact B2004715
  · exact B2004719
  · exact B2004723
  · exact B2004727
  · exact B2004731
  · exact B2004735
  · exact B2004739
  · exact B2004743
  · exact B2004747
  · exact B2004751
  · exact B2004755
  · exact B2004759
  · exact B2004763
  · exact B2004767
  · exact B2004771
  · exact B2004775
  · exact B2004779
  · exact B2004783
  · exact B2004787
  · exact B2004791
  · exact B2004795
  · exact B2004799
  · exact B2004803
  · exact B2004807
  · exact B2004811
  · exact B2004815
  · exact B2004819
  · exact B2004823
  · exact B2004827
  · exact B2004831
  · exact B2004835
  · exact B2004839
  · exact B2004843
  · exact B2004847
  · exact B2004851
  · exact B2004855
  · exact B2004859
  · exact B2004863
  · exact B2004867
  · exact B2004871
  · exact B2004875
  · exact B2004879
  · exact B2004883
  · exact B2004887
  · exact B2004891
  · exact B2004895
  · exact B2004899
  · exact B2004903
  · exact B2004907
  · exact B2004911
  · exact B2004915
  · exact B2004919
  · exact B2004923
  · exact B2004927
  · exact B2004931
  · exact B2004935
  · exact B2004939
  · exact B2004943
  · exact B2004947
  · exact B2004951
  · exact B2004955
  · exact B2004959
  · exact B2004963
  · exact B2004967
  · exact B2004971
  · exact B2004975
  · exact B2004979
  · exact B2004983
  · exact B2004987
  · exact B2004991
  · exact B2004995
  · exact B2004999
  · exact B2005003
  · exact B2005007
  · exact B2005011
  · exact B2005015
  · exact B2005019
  · exact B2005023
  · exact B2005027
  · exact B2005031
  · exact B2005035
  · exact B2005039
  · exact B2005043
  · exact B2005047
  · exact B2005051
  · exact B2005055
  · exact B2005059
  · exact B2005063
  · exact B2005067
  · exact B2005071
  · exact B2005075
  · exact B2005079
  · exact B2005083
  · exact B2005087
  · exact B2005091
  · exact B2005095
  · exact B2005099
  · exact B2005103
  · exact B2005107
  · exact B2005111
  · exact B2005115
  · exact B2005119
  · exact B2005123
  · exact B2005127
  · exact B2005131
  · exact B2005135
  · exact B2005139
  · exact B2005143
  · exact B2005147
  · exact B2005151
  · exact B2005155
  · exact B2005159
  · exact B2005163
  · exact B2005167
  · exact B2005171
  · exact B2005175
  · exact B2005179
  · exact B2005183
  · exact B2005187
  · exact B2005191
  · exact B2005195
  · exact B2005199
  · exact B2005203
  · exact B2005207
  · exact B2005211
  · exact B2005215
  · exact B2005219
  · exact B2005223
  · exact B2005227
  · exact B2005231
  · exact B2005235
  · exact B2005239
  · exact B2005243
  · exact B2005247
  · exact B2005251
  · exact B2005255
  · exact B2005259
  · exact B2005263
  · exact B2005267
  · exact B2005271
  · exact B2005275
  · exact B2005279
  · exact B2005283
  · exact B2005287
  · exact B2005291
  · exact B2005295
  · exact B2005299
  · exact B2005303
  · exact B2005307
  · exact B2005311
  · exact B2005315
  · exact B2005319
  · exact B2005323
  · exact B2005327
  · exact B2005331
  · exact B2005335
  · exact B2005339
  · exact B2005343
  · exact B2005347
  · exact B2005351
  · exact B2005355
  · exact B2005359
  · exact B2005363
  · exact B2005367
  · exact B2005371
  · exact B2005375
  · exact B2005379
  · exact B2005383
  · exact B2005387
  · exact B2005391
  · exact B2005395
  · exact B2005399
  · exact B2005403
  · exact B2005407
  · exact B2005411
  · exact B2005415
  · exact B2005419
  · exact B2005423
  · exact B2005427
  · exact B2005431
  · exact B2005435
theorem solution (m : ℕ) (hlo : 2003435 ≤ m) (hhi : m ≤ 2005435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 500858 ≤ j := by omega
    have hj2 : j ≤ 501358 := by omega
    have hb : Blo 2003435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
