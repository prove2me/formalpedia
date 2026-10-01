-- Prove2me | solution 1 for syracuse_descends_range_2139435_2141435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:15.586507+00:00
-- url     : https://prove2.me/submissions/0b52c4b8-28d2-46e4-8ef0-b1ca05ee1e89

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

theorem B2406865 : Blo 2139435 2406865 := bbase (se 2 (by rfl) ⟨902574, by rfl⟩ : syracuseStep 2406865 = 1805149) (by norm_num)
theorem B3209153 : Blo 2139435 3209153 := bstep (se 2 (by rfl) ⟨1203432, by rfl⟩ : syracuseStep 3209153 = 2406865) B2406865
theorem B2139435 : Blo 2139435 2139435 := bstep (se 1 (by rfl) ⟨1604576, by rfl⟩ : syracuseStep 2139435 = 3209153) B3209153
theorem B4569293 : Blo 2139435 4569293 := bbase (se 3 (by rfl) ⟨856742, by rfl⟩ : syracuseStep 4569293 = 1713485) (by norm_num)
theorem B3046195 : Blo 2139435 3046195 := bstep (se 1 (by rfl) ⟨2284646, by rfl⟩ : syracuseStep 3046195 = 4569293) B4569293
theorem B4061593 : Blo 2139435 4061593 := bstep (se 2 (by rfl) ⟨1523097, by rfl⟩ : syracuseStep 4061593 = 3046195) B3046195
theorem B5415457 : Blo 2139435 5415457 := bstep (se 2 (by rfl) ⟨2030796, by rfl⟩ : syracuseStep 5415457 = 4061593) B4061593
theorem B7220609 : Blo 2139435 7220609 := bstep (se 2 (by rfl) ⟨2707728, by rfl⟩ : syracuseStep 7220609 = 5415457) B5415457
theorem B4813739 : Blo 2139435 4813739 := bstep (se 1 (by rfl) ⟨3610304, by rfl⟩ : syracuseStep 4813739 = 7220609) B7220609
theorem B3209159 : Blo 2139435 3209159 := bstep (se 1 (by rfl) ⟨2406869, by rfl⟩ : syracuseStep 3209159 = 4813739) B4813739
theorem B2139439 : Blo 2139435 2139439 := bstep (se 1 (by rfl) ⟨1604579, by rfl⟩ : syracuseStep 2139439 = 3209159) B3209159
theorem B3209165 : Blo 2139435 3209165 := bbase (se 3 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 3209165 = 1203437) (by norm_num)
theorem B2139443 : Blo 2139435 2139443 := bstep (se 1 (by rfl) ⟨1604582, by rfl⟩ : syracuseStep 2139443 = 3209165) B3209165
theorem B4813757 : Blo 2139435 4813757 := bbase (se 3 (by rfl) ⟨902579, by rfl⟩ : syracuseStep 4813757 = 1805159) (by norm_num)
theorem B3209171 : Blo 2139435 3209171 := bstep (se 1 (by rfl) ⟨2406878, by rfl⟩ : syracuseStep 3209171 = 4813757) B4813757
theorem B2139447 : Blo 2139435 2139447 := bstep (se 1 (by rfl) ⟨1604585, by rfl⟩ : syracuseStep 2139447 = 3209171) B3209171
theorem B3610325 : Blo 2139435 3610325 := bbase (se 7 (by rfl) ⟨42308, by rfl⟩ : syracuseStep 3610325 = 84617) (by norm_num)
theorem B2406883 : Blo 2139435 2406883 := bstep (se 1 (by rfl) ⟨1805162, by rfl⟩ : syracuseStep 2406883 = 3610325) B3610325
theorem B3209177 : Blo 2139435 3209177 := bstep (se 2 (by rfl) ⟨1203441, by rfl⟩ : syracuseStep 3209177 = 2406883) B2406883
theorem B2139451 : Blo 2139435 2139451 := bstep (se 1 (by rfl) ⟨1604588, by rfl⟩ : syracuseStep 2139451 = 3209177) B3209177
theorem B5140493 : Blo 2139435 5140493 := bbase (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) (by norm_num)
theorem B3426995 : Blo 2139435 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B9138653 : Blo 2139435 9138653 := bstep (se 3 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 9138653 = 3426995) B3426995
theorem B6092435 : Blo 2139435 6092435 := bstep (se 1 (by rfl) ⟨4569326, by rfl⟩ : syracuseStep 6092435 = 9138653) B9138653
theorem B16246493 : Blo 2139435 16246493 := bstep (se 3 (by rfl) ⟨3046217, by rfl⟩ : syracuseStep 16246493 = 6092435) B6092435
theorem B10830995 : Blo 2139435 10830995 := bstep (se 1 (by rfl) ⟨8123246, by rfl⟩ : syracuseStep 10830995 = 16246493) B16246493
theorem B7220663 : Blo 2139435 7220663 := bstep (se 1 (by rfl) ⟨5415497, by rfl⟩ : syracuseStep 7220663 = 10830995) B10830995
theorem B4813775 : Blo 2139435 4813775 := bstep (se 1 (by rfl) ⟨3610331, by rfl⟩ : syracuseStep 4813775 = 7220663) B7220663
theorem B3209183 : Blo 2139435 3209183 := bstep (se 1 (by rfl) ⟨2406887, by rfl⟩ : syracuseStep 3209183 = 4813775) B4813775
theorem B2139455 : Blo 2139435 2139455 := bstep (se 1 (by rfl) ⟨1604591, by rfl⟩ : syracuseStep 2139455 = 3209183) B3209183
theorem B3209189 : Blo 2139435 3209189 := bbase (se 4 (by rfl) ⟨300861, by rfl⟩ : syracuseStep 3209189 = 601723) (by norm_num)
theorem B2139459 : Blo 2139435 2139459 := bstep (se 1 (by rfl) ⟨1604594, by rfl⟩ : syracuseStep 2139459 = 3209189) B3209189
theorem B4337309 : Blo 2139435 4337309 := bbase (se 3 (by rfl) ⟨813245, by rfl⟩ : syracuseStep 4337309 = 1626491) (by norm_num)
theorem B2891539 : Blo 2139435 2891539 := bstep (se 1 (by rfl) ⟨2168654, by rfl⟩ : syracuseStep 2891539 = 4337309) B4337309
theorem B3855385 : Blo 2139435 3855385 := bstep (se 2 (by rfl) ⟨1445769, by rfl⟩ : syracuseStep 3855385 = 2891539) B2891539
theorem B5140513 : Blo 2139435 5140513 := bstep (se 2 (by rfl) ⟨1927692, by rfl⟩ : syracuseStep 5140513 = 3855385) B3855385
theorem B6854017 : Blo 2139435 6854017 := bstep (se 2 (by rfl) ⟨2570256, by rfl⟩ : syracuseStep 6854017 = 5140513) B5140513
theorem B9138689 : Blo 2139435 9138689 := bstep (se 2 (by rfl) ⟨3427008, by rfl⟩ : syracuseStep 9138689 = 6854017) B6854017
theorem B6092459 : Blo 2139435 6092459 := bstep (se 1 (by rfl) ⟨4569344, by rfl⟩ : syracuseStep 6092459 = 9138689) B9138689
theorem B4061639 : Blo 2139435 4061639 := bstep (se 1 (by rfl) ⟨3046229, by rfl⟩ : syracuseStep 4061639 = 6092459) B6092459
theorem B2707759 : Blo 2139435 2707759 := bstep (se 1 (by rfl) ⟨2030819, by rfl⟩ : syracuseStep 2707759 = 4061639) B4061639
theorem B3610345 : Blo 2139435 3610345 := bstep (se 2 (by rfl) ⟨1353879, by rfl⟩ : syracuseStep 3610345 = 2707759) B2707759
theorem B4813793 : Blo 2139435 4813793 := bstep (se 2 (by rfl) ⟨1805172, by rfl⟩ : syracuseStep 4813793 = 3610345) B3610345
theorem B3209195 : Blo 2139435 3209195 := bstep (se 1 (by rfl) ⟨2406896, by rfl⟩ : syracuseStep 3209195 = 4813793) B4813793
theorem B2139463 : Blo 2139435 2139463 := bstep (se 1 (by rfl) ⟨1604597, by rfl⟩ : syracuseStep 2139463 = 3209195) B3209195
theorem B2406901 : Blo 2139435 2406901 := bbase (se 5 (by rfl) ⟨112823, by rfl⟩ : syracuseStep 2406901 = 225647) (by norm_num)
theorem B3209201 : Blo 2139435 3209201 := bstep (se 2 (by rfl) ⟨1203450, by rfl⟩ : syracuseStep 3209201 = 2406901) B2406901
theorem B2139467 : Blo 2139435 2139467 := bstep (se 1 (by rfl) ⟨1604600, by rfl⟩ : syracuseStep 2139467 = 3209201) B3209201
theorem B2707769 : Blo 2139435 2707769 := bbase (se 2 (by rfl) ⟨1015413, by rfl⟩ : syracuseStep 2707769 = 2030827) (by norm_num)
theorem B7220717 : Blo 2139435 7220717 := bstep (se 3 (by rfl) ⟨1353884, by rfl⟩ : syracuseStep 7220717 = 2707769) B2707769
theorem B4813811 : Blo 2139435 4813811 := bstep (se 1 (by rfl) ⟨3610358, by rfl⟩ : syracuseStep 4813811 = 7220717) B7220717
theorem B3209207 : Blo 2139435 3209207 := bstep (se 1 (by rfl) ⟨2406905, by rfl⟩ : syracuseStep 3209207 = 4813811) B4813811
theorem B2139471 : Blo 2139435 2139471 := bstep (se 1 (by rfl) ⟨1604603, by rfl⟩ : syracuseStep 2139471 = 3209207) B3209207
theorem B3209213 : Blo 2139435 3209213 := bbase (se 3 (by rfl) ⟨601727, by rfl⟩ : syracuseStep 3209213 = 1203455) (by norm_num)
theorem B2139475 : Blo 2139435 2139475 := bstep (se 1 (by rfl) ⟨1604606, by rfl⟩ : syracuseStep 2139475 = 3209213) B3209213
theorem B4813829 : Blo 2139435 4813829 := bbase (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) (by norm_num)
theorem B3209219 : Blo 2139435 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B2139479 : Blo 2139435 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B4061677 : Blo 2139435 4061677 := bbase (se 3 (by rfl) ⟨761564, by rfl⟩ : syracuseStep 4061677 = 1523129) (by norm_num)
theorem B5415569 : Blo 2139435 5415569 := bstep (se 2 (by rfl) ⟨2030838, by rfl⟩ : syracuseStep 5415569 = 4061677) B4061677
theorem B3610379 : Blo 2139435 3610379 := bstep (se 1 (by rfl) ⟨2707784, by rfl⟩ : syracuseStep 3610379 = 5415569) B5415569
theorem B2406919 : Blo 2139435 2406919 := bstep (se 1 (by rfl) ⟨1805189, by rfl⟩ : syracuseStep 2406919 = 3610379) B3610379
theorem B3209225 : Blo 2139435 3209225 := bstep (se 2 (by rfl) ⟨1203459, by rfl⟩ : syracuseStep 3209225 = 2406919) B2406919
theorem B2139483 : Blo 2139435 2139483 := bstep (se 1 (by rfl) ⟨1604612, by rfl⟩ : syracuseStep 2139483 = 3209225) B3209225
theorem B10831157 : Blo 2139435 10831157 := bbase (se 5 (by rfl) ⟨507710, by rfl⟩ : syracuseStep 10831157 = 1015421) (by norm_num)
theorem B7220771 : Blo 2139435 7220771 := bstep (se 1 (by rfl) ⟨5415578, by rfl⟩ : syracuseStep 7220771 = 10831157) B10831157
theorem B4813847 : Blo 2139435 4813847 := bstep (se 1 (by rfl) ⟨3610385, by rfl⟩ : syracuseStep 4813847 = 7220771) B7220771
theorem B3209231 : Blo 2139435 3209231 := bstep (se 1 (by rfl) ⟨2406923, by rfl⟩ : syracuseStep 3209231 = 4813847) B4813847
theorem B2139487 : Blo 2139435 2139487 := bstep (se 1 (by rfl) ⟨1604615, by rfl⟩ : syracuseStep 2139487 = 3209231) B3209231
theorem B3209237 : Blo 2139435 3209237 := bbase (se 6 (by rfl) ⟨75216, by rfl⟩ : syracuseStep 3209237 = 150433) (by norm_num)
theorem B2139491 : Blo 2139435 2139491 := bstep (se 1 (by rfl) ⟨1604618, by rfl⟩ : syracuseStep 2139491 = 3209237) B3209237
theorem B5140589 : Blo 2139435 5140589 := bbase (se 3 (by rfl) ⟨963860, by rfl⟩ : syracuseStep 5140589 = 1927721) (by norm_num)
theorem B13708237 : Blo 2139435 13708237 := bstep (se 3 (by rfl) ⟨2570294, by rfl⟩ : syracuseStep 13708237 = 5140589) B5140589
theorem B18277649 : Blo 2139435 18277649 := bstep (se 2 (by rfl) ⟨6854118, by rfl⟩ : syracuseStep 18277649 = 13708237) B13708237
theorem B12185099 : Blo 2139435 12185099 := bstep (se 1 (by rfl) ⟨9138824, by rfl⟩ : syracuseStep 12185099 = 18277649) B18277649
theorem B8123399 : Blo 2139435 8123399 := bstep (se 1 (by rfl) ⟨6092549, by rfl⟩ : syracuseStep 8123399 = 12185099) B12185099
theorem B5415599 : Blo 2139435 5415599 := bstep (se 1 (by rfl) ⟨4061699, by rfl⟩ : syracuseStep 5415599 = 8123399) B8123399
theorem B3610399 : Blo 2139435 3610399 := bstep (se 1 (by rfl) ⟨2707799, by rfl⟩ : syracuseStep 3610399 = 5415599) B5415599
theorem B4813865 : Blo 2139435 4813865 := bstep (se 2 (by rfl) ⟨1805199, by rfl⟩ : syracuseStep 4813865 = 3610399) B3610399
theorem B3209243 : Blo 2139435 3209243 := bstep (se 1 (by rfl) ⟨2406932, by rfl⟩ : syracuseStep 3209243 = 4813865) B4813865
theorem B2139495 : Blo 2139435 2139495 := bstep (se 1 (by rfl) ⟨1604621, by rfl⟩ : syracuseStep 2139495 = 3209243) B3209243
theorem B2406937 : Blo 2139435 2406937 := bbase (se 2 (by rfl) ⟨902601, by rfl⟩ : syracuseStep 2406937 = 1805203) (by norm_num)
theorem B3209249 : Blo 2139435 3209249 := bstep (se 2 (by rfl) ⟨1203468, by rfl⟩ : syracuseStep 3209249 = 2406937) B2406937
theorem B2139499 : Blo 2139435 2139499 := bstep (se 1 (by rfl) ⟨1604624, by rfl⟩ : syracuseStep 2139499 = 3209249) B3209249
theorem B8123429 : Blo 2139435 8123429 := bbase (se 4 (by rfl) ⟨761571, by rfl⟩ : syracuseStep 8123429 = 1523143) (by norm_num)
theorem B5415619 : Blo 2139435 5415619 := bstep (se 1 (by rfl) ⟨4061714, by rfl⟩ : syracuseStep 5415619 = 8123429) B8123429
theorem B7220825 : Blo 2139435 7220825 := bstep (se 2 (by rfl) ⟨2707809, by rfl⟩ : syracuseStep 7220825 = 5415619) B5415619
theorem B4813883 : Blo 2139435 4813883 := bstep (se 1 (by rfl) ⟨3610412, by rfl⟩ : syracuseStep 4813883 = 7220825) B7220825
theorem B3209255 : Blo 2139435 3209255 := bstep (se 1 (by rfl) ⟨2406941, by rfl⟩ : syracuseStep 3209255 = 4813883) B4813883
theorem B2139503 : Blo 2139435 2139503 := bstep (se 1 (by rfl) ⟨1604627, by rfl⟩ : syracuseStep 2139503 = 3209255) B3209255
theorem B3209261 : Blo 2139435 3209261 := bbase (se 3 (by rfl) ⟨601736, by rfl⟩ : syracuseStep 3209261 = 1203473) (by norm_num)
theorem B2139507 : Blo 2139435 2139507 := bstep (se 1 (by rfl) ⟨1604630, by rfl⟩ : syracuseStep 2139507 = 3209261) B3209261
theorem B4813901 : Blo 2139435 4813901 := bbase (se 3 (by rfl) ⟨902606, by rfl⟩ : syracuseStep 4813901 = 1805213) (by norm_num)
theorem B3209267 : Blo 2139435 3209267 := bstep (se 1 (by rfl) ⟨2406950, by rfl⟩ : syracuseStep 3209267 = 4813901) B4813901
theorem B2139511 : Blo 2139435 2139511 := bstep (se 1 (by rfl) ⟨1604633, by rfl⟩ : syracuseStep 2139511 = 3209267) B3209267
theorem B2707825 : Blo 2139435 2707825 := bbase (se 2 (by rfl) ⟨1015434, by rfl⟩ : syracuseStep 2707825 = 2030869) (by norm_num)
theorem B3610433 : Blo 2139435 3610433 := bstep (se 2 (by rfl) ⟨1353912, by rfl⟩ : syracuseStep 3610433 = 2707825) B2707825
theorem B2406955 : Blo 2139435 2406955 := bstep (se 1 (by rfl) ⟨1805216, by rfl⟩ : syracuseStep 2406955 = 3610433) B3610433
theorem B3209273 : Blo 2139435 3209273 := bstep (se 2 (by rfl) ⟨1203477, by rfl⟩ : syracuseStep 3209273 = 2406955) B2406955
theorem B2139515 : Blo 2139435 2139515 := bstep (se 1 (by rfl) ⟨1604636, by rfl⟩ : syracuseStep 2139515 = 3209273) B3209273
theorem B3855485 : Blo 2139435 3855485 := bbase (se 3 (by rfl) ⟨722903, by rfl⟩ : syracuseStep 3855485 = 1445807) (by norm_num)
theorem B10281293 : Blo 2139435 10281293 := bstep (se 3 (by rfl) ⟨1927742, by rfl⟩ : syracuseStep 10281293 = 3855485) B3855485
theorem B6854195 : Blo 2139435 6854195 := bstep (se 1 (by rfl) ⟨5140646, by rfl⟩ : syracuseStep 6854195 = 10281293) B10281293
theorem B4569463 : Blo 2139435 4569463 := bstep (se 1 (by rfl) ⟨3427097, by rfl⟩ : syracuseStep 4569463 = 6854195) B6854195
theorem B24370469 : Blo 2139435 24370469 := bstep (se 4 (by rfl) ⟨2284731, by rfl⟩ : syracuseStep 24370469 = 4569463) B4569463
theorem B16246979 : Blo 2139435 16246979 := bstep (se 1 (by rfl) ⟨12185234, by rfl⟩ : syracuseStep 16246979 = 24370469) B24370469
theorem B10831319 : Blo 2139435 10831319 := bstep (se 1 (by rfl) ⟨8123489, by rfl⟩ : syracuseStep 10831319 = 16246979) B16246979
theorem B7220879 : Blo 2139435 7220879 := bstep (se 1 (by rfl) ⟨5415659, by rfl⟩ : syracuseStep 7220879 = 10831319) B10831319
theorem B4813919 : Blo 2139435 4813919 := bstep (se 1 (by rfl) ⟨3610439, by rfl⟩ : syracuseStep 4813919 = 7220879) B7220879
theorem B3209279 : Blo 2139435 3209279 := bstep (se 1 (by rfl) ⟨2406959, by rfl⟩ : syracuseStep 3209279 = 4813919) B4813919
theorem B2139519 : Blo 2139435 2139519 := bstep (se 1 (by rfl) ⟨1604639, by rfl⟩ : syracuseStep 2139519 = 3209279) B3209279
theorem B3209285 : Blo 2139435 3209285 := bbase (se 4 (by rfl) ⟨300870, by rfl⟩ : syracuseStep 3209285 = 601741) (by norm_num)
theorem B2139523 : Blo 2139435 2139523 := bstep (se 1 (by rfl) ⟨1604642, by rfl⟩ : syracuseStep 2139523 = 3209285) B3209285
theorem B3610453 : Blo 2139435 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B4813937 : Blo 2139435 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B3209291 : Blo 2139435 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B2139527 : Blo 2139435 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B2406973 : Blo 2139435 2406973 := bbase (se 3 (by rfl) ⟨451307, by rfl⟩ : syracuseStep 2406973 = 902615) (by norm_num)
theorem B3209297 : Blo 2139435 3209297 := bstep (se 2 (by rfl) ⟨1203486, by rfl⟩ : syracuseStep 3209297 = 2406973) B2406973
theorem B2139531 : Blo 2139435 2139531 := bstep (se 1 (by rfl) ⟨1604648, by rfl⟩ : syracuseStep 2139531 = 3209297) B3209297
theorem B7220933 : Blo 2139435 7220933 := bbase (se 4 (by rfl) ⟨676962, by rfl⟩ : syracuseStep 7220933 = 1353925) (by norm_num)
theorem B4813955 : Blo 2139435 4813955 := bstep (se 1 (by rfl) ⟨3610466, by rfl⟩ : syracuseStep 4813955 = 7220933) B7220933
theorem B3209303 : Blo 2139435 3209303 := bstep (se 1 (by rfl) ⟨2406977, by rfl⟩ : syracuseStep 3209303 = 4813955) B4813955
theorem B2139535 : Blo 2139435 2139535 := bstep (se 1 (by rfl) ⟨1604651, by rfl⟩ : syracuseStep 2139535 = 3209303) B3209303
theorem B3209309 : Blo 2139435 3209309 := bbase (se 3 (by rfl) ⟨601745, by rfl⟩ : syracuseStep 3209309 = 1203491) (by norm_num)
theorem B2139539 : Blo 2139435 2139539 := bstep (se 1 (by rfl) ⟨1604654, by rfl⟩ : syracuseStep 2139539 = 3209309) B3209309
theorem B4813973 : Blo 2139435 4813973 := bbase (se 6 (by rfl) ⟨112827, by rfl⟩ : syracuseStep 4813973 = 225655) (by norm_num)
theorem B3209315 : Blo 2139435 3209315 := bstep (se 1 (by rfl) ⟨2406986, by rfl⟩ : syracuseStep 3209315 = 4813973) B4813973
theorem B2139543 : Blo 2139435 2139543 := bstep (se 1 (by rfl) ⟨1604657, by rfl⟩ : syracuseStep 2139543 = 3209315) B3209315
theorem B3046349 : Blo 2139435 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B8123597 : Blo 2139435 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B5415731 : Blo 2139435 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B3610487 : Blo 2139435 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B2406991 : Blo 2139435 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B3209321 : Blo 2139435 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B2139547 : Blo 2139435 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B5564533 : Blo 2139435 5564533 := bbase (se 5 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 5564533 = 521675) (by norm_num)
theorem B7419377 : Blo 2139435 7419377 := bstep (se 2 (by rfl) ⟨2782266, by rfl⟩ : syracuseStep 7419377 = 5564533) B5564533
theorem B19785005 : Blo 2139435 19785005 := bstep (se 3 (by rfl) ⟨3709688, by rfl⟩ : syracuseStep 19785005 = 7419377) B7419377
theorem B13190003 : Blo 2139435 13190003 := bstep (se 1 (by rfl) ⟨9892502, by rfl⟩ : syracuseStep 13190003 = 19785005) B19785005
theorem B8793335 : Blo 2139435 8793335 := bstep (se 1 (by rfl) ⟨6595001, by rfl⟩ : syracuseStep 8793335 = 13190003) B13190003
theorem B5862223 : Blo 2139435 5862223 := bstep (se 1 (by rfl) ⟨4396667, by rfl⟩ : syracuseStep 5862223 = 8793335) B8793335
theorem B7816297 : Blo 2139435 7816297 := bstep (se 2 (by rfl) ⟨2931111, by rfl⟩ : syracuseStep 7816297 = 5862223) B5862223
theorem B10421729 : Blo 2139435 10421729 := bstep (se 2 (by rfl) ⟨3908148, by rfl⟩ : syracuseStep 10421729 = 7816297) B7816297
theorem B6947819 : Blo 2139435 6947819 := bstep (se 1 (by rfl) ⟨5210864, by rfl⟩ : syracuseStep 6947819 = 10421729) B10421729
theorem B4631879 : Blo 2139435 4631879 := bstep (se 1 (by rfl) ⟨3473909, by rfl⟩ : syracuseStep 4631879 = 6947819) B6947819
theorem B3087919 : Blo 2139435 3087919 := bstep (se 1 (by rfl) ⟨2315939, by rfl⟩ : syracuseStep 3087919 = 4631879) B4631879
theorem B4117225 : Blo 2139435 4117225 := bstep (se 2 (by rfl) ⟨1543959, by rfl⟩ : syracuseStep 4117225 = 3087919) B3087919
theorem B5489633 : Blo 2139435 5489633 := bstep (se 2 (by rfl) ⟨2058612, by rfl⟩ : syracuseStep 5489633 = 4117225) B4117225
theorem B3659755 : Blo 2139435 3659755 := bstep (se 1 (by rfl) ⟨2744816, by rfl⟩ : syracuseStep 3659755 = 5489633) B5489633
theorem B4879673 : Blo 2139435 4879673 := bstep (se 2 (by rfl) ⟨1829877, by rfl⟩ : syracuseStep 4879673 = 3659755) B3659755
theorem B3253115 : Blo 2139435 3253115 := bstep (se 1 (by rfl) ⟨2439836, by rfl⟩ : syracuseStep 3253115 = 4879673) B4879673
theorem B2168743 : Blo 2139435 2168743 := bstep (se 1 (by rfl) ⟨1626557, by rfl⟩ : syracuseStep 2168743 = 3253115) B3253115
theorem B2891657 : Blo 2139435 2891657 := bstep (se 2 (by rfl) ⟨1084371, by rfl⟩ : syracuseStep 2891657 = 2168743) B2168743
theorem B7711085 : Blo 2139435 7711085 := bstep (se 3 (by rfl) ⟨1445828, by rfl⟩ : syracuseStep 7711085 = 2891657) B2891657
theorem B20562893 : Blo 2139435 20562893 := bstep (se 3 (by rfl) ⟨3855542, by rfl⟩ : syracuseStep 20562893 = 7711085) B7711085
theorem B13708595 : Blo 2139435 13708595 := bstep (se 1 (by rfl) ⟨10281446, by rfl⟩ : syracuseStep 13708595 = 20562893) B20562893
theorem B9139063 : Blo 2139435 9139063 := bstep (se 1 (by rfl) ⟨6854297, by rfl⟩ : syracuseStep 9139063 = 13708595) B13708595
theorem B12185417 : Blo 2139435 12185417 := bstep (se 2 (by rfl) ⟨4569531, by rfl⟩ : syracuseStep 12185417 = 9139063) B9139063
theorem B8123611 : Blo 2139435 8123611 := bstep (se 1 (by rfl) ⟨6092708, by rfl⟩ : syracuseStep 8123611 = 12185417) B12185417
theorem B10831481 : Blo 2139435 10831481 := bstep (se 2 (by rfl) ⟨4061805, by rfl⟩ : syracuseStep 10831481 = 8123611) B8123611
theorem B7220987 : Blo 2139435 7220987 := bstep (se 1 (by rfl) ⟨5415740, by rfl⟩ : syracuseStep 7220987 = 10831481) B10831481
theorem B4813991 : Blo 2139435 4813991 := bstep (se 1 (by rfl) ⟨3610493, by rfl⟩ : syracuseStep 4813991 = 7220987) B7220987
theorem B3209327 : Blo 2139435 3209327 := bstep (se 1 (by rfl) ⟨2406995, by rfl⟩ : syracuseStep 3209327 = 4813991) B4813991
theorem B2139551 : Blo 2139435 2139551 := bstep (se 1 (by rfl) ⟨1604663, by rfl⟩ : syracuseStep 2139551 = 3209327) B3209327
theorem B3209333 : Blo 2139435 3209333 := bbase (se 5 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 3209333 = 300875) (by norm_num)
theorem B2139555 : Blo 2139435 2139555 := bstep (se 1 (by rfl) ⟨1604666, by rfl⟩ : syracuseStep 2139555 = 3209333) B3209333
theorem B4061821 : Blo 2139435 4061821 := bbase (se 3 (by rfl) ⟨761591, by rfl⟩ : syracuseStep 4061821 = 1523183) (by norm_num)
theorem B5415761 : Blo 2139435 5415761 := bstep (se 2 (by rfl) ⟨2030910, by rfl⟩ : syracuseStep 5415761 = 4061821) B4061821
theorem B3610507 : Blo 2139435 3610507 := bstep (se 1 (by rfl) ⟨2707880, by rfl⟩ : syracuseStep 3610507 = 5415761) B5415761
theorem B4814009 : Blo 2139435 4814009 := bstep (se 2 (by rfl) ⟨1805253, by rfl⟩ : syracuseStep 4814009 = 3610507) B3610507
theorem B3209339 : Blo 2139435 3209339 := bstep (se 1 (by rfl) ⟨2407004, by rfl⟩ : syracuseStep 3209339 = 4814009) B4814009
theorem B2139559 : Blo 2139435 2139559 := bstep (se 1 (by rfl) ⟨1604669, by rfl⟩ : syracuseStep 2139559 = 3209339) B3209339
theorem B2407009 : Blo 2139435 2407009 := bbase (se 2 (by rfl) ⟨902628, by rfl⟩ : syracuseStep 2407009 = 1805257) (by norm_num)
theorem B3209345 : Blo 2139435 3209345 := bstep (se 2 (by rfl) ⟨1203504, by rfl⟩ : syracuseStep 3209345 = 2407009) B2407009
theorem B2139563 : Blo 2139435 2139563 := bstep (se 1 (by rfl) ⟨1604672, by rfl⟩ : syracuseStep 2139563 = 3209345) B3209345
theorem B5415781 : Blo 2139435 5415781 := bbase (se 4 (by rfl) ⟨507729, by rfl⟩ : syracuseStep 5415781 = 1015459) (by norm_num)
theorem B7221041 : Blo 2139435 7221041 := bstep (se 2 (by rfl) ⟨2707890, by rfl⟩ : syracuseStep 7221041 = 5415781) B5415781
theorem B4814027 : Blo 2139435 4814027 := bstep (se 1 (by rfl) ⟨3610520, by rfl⟩ : syracuseStep 4814027 = 7221041) B7221041
theorem B3209351 : Blo 2139435 3209351 := bstep (se 1 (by rfl) ⟨2407013, by rfl⟩ : syracuseStep 3209351 = 4814027) B4814027
theorem B2139567 : Blo 2139435 2139567 := bstep (se 1 (by rfl) ⟨1604675, by rfl⟩ : syracuseStep 2139567 = 3209351) B3209351
theorem B3209357 : Blo 2139435 3209357 := bbase (se 3 (by rfl) ⟨601754, by rfl⟩ : syracuseStep 3209357 = 1203509) (by norm_num)
theorem B2139571 : Blo 2139435 2139571 := bstep (se 1 (by rfl) ⟨1604678, by rfl⟩ : syracuseStep 2139571 = 3209357) B3209357
theorem B4814045 : Blo 2139435 4814045 := bbase (se 3 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 4814045 = 1805267) (by norm_num)
theorem B3209363 : Blo 2139435 3209363 := bstep (se 1 (by rfl) ⟨2407022, by rfl⟩ : syracuseStep 3209363 = 4814045) B4814045
theorem B2139575 : Blo 2139435 2139575 := bstep (se 1 (by rfl) ⟨1604681, by rfl⟩ : syracuseStep 2139575 = 3209363) B3209363
theorem B3610541 : Blo 2139435 3610541 := bbase (se 3 (by rfl) ⟨676976, by rfl⟩ : syracuseStep 3610541 = 1353953) (by norm_num)
theorem B2407027 : Blo 2139435 2407027 := bstep (se 1 (by rfl) ⟨1805270, by rfl⟩ : syracuseStep 2407027 = 3610541) B3610541
theorem B3209369 : Blo 2139435 3209369 := bstep (se 2 (by rfl) ⟨1203513, by rfl⟩ : syracuseStep 3209369 = 2407027) B2407027
theorem B2139579 : Blo 2139435 2139579 := bstep (se 1 (by rfl) ⟨1604684, by rfl⟩ : syracuseStep 2139579 = 3209369) B3209369
theorem B7042709 : Blo 2139435 7042709 := bbase (se 6 (by rfl) ⟨165063, by rfl⟩ : syracuseStep 7042709 = 330127) (by norm_num)
theorem B18780557 : Blo 2139435 18780557 := bstep (se 3 (by rfl) ⟨3521354, by rfl⟩ : syracuseStep 18780557 = 7042709) B7042709
theorem B50081485 : Blo 2139435 50081485 := bstep (se 3 (by rfl) ⟨9390278, by rfl⟩ : syracuseStep 50081485 = 18780557) B18780557
theorem B66775313 : Blo 2139435 66775313 := bstep (se 2 (by rfl) ⟨25040742, by rfl⟩ : syracuseStep 66775313 = 50081485) B50081485
theorem B44516875 : Blo 2139435 44516875 := bstep (se 1 (by rfl) ⟨33387656, by rfl⟩ : syracuseStep 44516875 = 66775313) B66775313
theorem B59355833 : Blo 2139435 59355833 := bstep (se 2 (by rfl) ⟨22258437, by rfl⟩ : syracuseStep 59355833 = 44516875) B44516875
theorem B633128885 : Blo 2139435 633128885 := bstep (se 5 (by rfl) ⟨29677916, by rfl⟩ : syracuseStep 633128885 = 59355833) B59355833
theorem B422085923 : Blo 2139435 422085923 := bstep (se 1 (by rfl) ⟨316564442, by rfl⟩ : syracuseStep 422085923 = 633128885) B633128885
theorem B281390615 : Blo 2139435 281390615 := bstep (se 1 (by rfl) ⟨211042961, by rfl⟩ : syracuseStep 281390615 = 422085923) B422085923
theorem B187593743 : Blo 2139435 187593743 := bstep (se 1 (by rfl) ⟨140695307, by rfl⟩ : syracuseStep 187593743 = 281390615) B281390615
theorem B500249981 : Blo 2139435 500249981 := bstep (se 3 (by rfl) ⟨93796871, by rfl⟩ : syracuseStep 500249981 = 187593743) B187593743
theorem B333499987 : Blo 2139435 333499987 := bstep (se 1 (by rfl) ⟨250124990, by rfl⟩ : syracuseStep 333499987 = 500249981) B500249981
theorem B1778666597 : Blo 2139435 1778666597 := bstep (se 4 (by rfl) ⟨166749993, by rfl⟩ : syracuseStep 1778666597 = 333499987) B333499987
theorem B1185777731 : Blo 2139435 1185777731 := bstep (se 1 (by rfl) ⟨889333298, by rfl⟩ : syracuseStep 1185777731 = 1778666597) B1778666597
theorem B790518487 : Blo 2139435 790518487 := bstep (se 1 (by rfl) ⟨592888865, by rfl⟩ : syracuseStep 790518487 = 1185777731) B1185777731
theorem B1054024649 : Blo 2139435 1054024649 := bstep (se 2 (by rfl) ⟨395259243, by rfl⟩ : syracuseStep 1054024649 = 790518487) B790518487
theorem B702683099 : Blo 2139435 702683099 := bstep (se 1 (by rfl) ⟨527012324, by rfl⟩ : syracuseStep 702683099 = 1054024649) B1054024649
theorem B468455399 : Blo 2139435 468455399 := bstep (se 1 (by rfl) ⟨351341549, by rfl⟩ : syracuseStep 468455399 = 702683099) B702683099
theorem B312303599 : Blo 2139435 312303599 := bstep (se 1 (by rfl) ⟨234227699, by rfl⟩ : syracuseStep 312303599 = 468455399) B468455399
theorem B208202399 : Blo 2139435 208202399 := bstep (se 1 (by rfl) ⟨156151799, by rfl⟩ : syracuseStep 208202399 = 312303599) B312303599
theorem B138801599 : Blo 2139435 138801599 := bstep (se 1 (by rfl) ⟨104101199, by rfl⟩ : syracuseStep 138801599 = 208202399) B208202399
theorem B92534399 : Blo 2139435 92534399 := bstep (se 1 (by rfl) ⟨69400799, by rfl⟩ : syracuseStep 92534399 = 138801599) B138801599
theorem B61689599 : Blo 2139435 61689599 := bstep (se 1 (by rfl) ⟨46267199, by rfl⟩ : syracuseStep 61689599 = 92534399) B92534399
theorem B41126399 : Blo 2139435 41126399 := bstep (se 1 (by rfl) ⟨30844799, by rfl⟩ : syracuseStep 41126399 = 61689599) B61689599
theorem B27417599 : Blo 2139435 27417599 := bstep (se 1 (by rfl) ⟨20563199, by rfl⟩ : syracuseStep 27417599 = 41126399) B41126399
theorem B18278399 : Blo 2139435 18278399 := bstep (se 1 (by rfl) ⟨13708799, by rfl⟩ : syracuseStep 18278399 = 27417599) B27417599
theorem B12185599 : Blo 2139435 12185599 := bstep (se 1 (by rfl) ⟨9139199, by rfl⟩ : syracuseStep 12185599 = 18278399) B18278399
theorem B16247465 : Blo 2139435 16247465 := bstep (se 2 (by rfl) ⟨6092799, by rfl⟩ : syracuseStep 16247465 = 12185599) B12185599
theorem B10831643 : Blo 2139435 10831643 := bstep (se 1 (by rfl) ⟨8123732, by rfl⟩ : syracuseStep 10831643 = 16247465) B16247465
theorem B7221095 : Blo 2139435 7221095 := bstep (se 1 (by rfl) ⟨5415821, by rfl⟩ : syracuseStep 7221095 = 10831643) B10831643
theorem B4814063 : Blo 2139435 4814063 := bstep (se 1 (by rfl) ⟨3610547, by rfl⟩ : syracuseStep 4814063 = 7221095) B7221095
theorem B3209375 : Blo 2139435 3209375 := bstep (se 1 (by rfl) ⟨2407031, by rfl⟩ : syracuseStep 3209375 = 4814063) B4814063
theorem B2139583 : Blo 2139435 2139583 := bstep (se 1 (by rfl) ⟨1604687, by rfl⟩ : syracuseStep 2139583 = 3209375) B3209375
theorem B3209381 : Blo 2139435 3209381 := bbase (se 4 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 3209381 = 601759) (by norm_num)
theorem B2139587 : Blo 2139435 2139587 := bstep (se 1 (by rfl) ⟨1604690, by rfl⟩ : syracuseStep 2139587 = 3209381) B3209381
theorem B2707921 : Blo 2139435 2707921 := bbase (se 2 (by rfl) ⟨1015470, by rfl⟩ : syracuseStep 2707921 = 2030941) (by norm_num)
theorem B3610561 : Blo 2139435 3610561 := bstep (se 2 (by rfl) ⟨1353960, by rfl⟩ : syracuseStep 3610561 = 2707921) B2707921
theorem B4814081 : Blo 2139435 4814081 := bstep (se 2 (by rfl) ⟨1805280, by rfl⟩ : syracuseStep 4814081 = 3610561) B3610561
theorem B3209387 : Blo 2139435 3209387 := bstep (se 1 (by rfl) ⟨2407040, by rfl⟩ : syracuseStep 3209387 = 4814081) B4814081
theorem B2139591 : Blo 2139435 2139591 := bstep (se 1 (by rfl) ⟨1604693, by rfl⟩ : syracuseStep 2139591 = 3209387) B3209387
theorem B2407045 : Blo 2139435 2407045 := bbase (se 4 (by rfl) ⟨225660, by rfl⟩ : syracuseStep 2407045 = 451321) (by norm_num)
theorem B3209393 : Blo 2139435 3209393 := bstep (se 2 (by rfl) ⟨1203522, by rfl⟩ : syracuseStep 3209393 = 2407045) B2407045
theorem B2139595 : Blo 2139435 2139595 := bstep (se 1 (by rfl) ⟨1604696, by rfl⟩ : syracuseStep 2139595 = 3209393) B3209393
theorem B6854453 : Blo 2139435 6854453 := bbase (se 5 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 6854453 = 642605) (by norm_num)
theorem B4569635 : Blo 2139435 4569635 := bstep (se 1 (by rfl) ⟨3427226, by rfl⟩ : syracuseStep 4569635 = 6854453) B6854453
theorem B3046423 : Blo 2139435 3046423 := bstep (se 1 (by rfl) ⟨2284817, by rfl⟩ : syracuseStep 3046423 = 4569635) B4569635
theorem B4061897 : Blo 2139435 4061897 := bstep (se 2 (by rfl) ⟨1523211, by rfl⟩ : syracuseStep 4061897 = 3046423) B3046423
theorem B2707931 : Blo 2139435 2707931 := bstep (se 1 (by rfl) ⟨2030948, by rfl⟩ : syracuseStep 2707931 = 4061897) B4061897
theorem B7221149 : Blo 2139435 7221149 := bstep (se 3 (by rfl) ⟨1353965, by rfl⟩ : syracuseStep 7221149 = 2707931) B2707931
theorem B4814099 : Blo 2139435 4814099 := bstep (se 1 (by rfl) ⟨3610574, by rfl⟩ : syracuseStep 4814099 = 7221149) B7221149
theorem B3209399 : Blo 2139435 3209399 := bstep (se 1 (by rfl) ⟨2407049, by rfl⟩ : syracuseStep 3209399 = 4814099) B4814099
theorem B2139599 : Blo 2139435 2139599 := bstep (se 1 (by rfl) ⟨1604699, by rfl⟩ : syracuseStep 2139599 = 3209399) B3209399
theorem B3209405 : Blo 2139435 3209405 := bbase (se 3 (by rfl) ⟨601763, by rfl⟩ : syracuseStep 3209405 = 1203527) (by norm_num)
theorem B2139603 : Blo 2139435 2139603 := bstep (se 1 (by rfl) ⟨1604702, by rfl⟩ : syracuseStep 2139603 = 3209405) B3209405
theorem B4814117 : Blo 2139435 4814117 := bbase (se 4 (by rfl) ⟨451323, by rfl⟩ : syracuseStep 4814117 = 902647) (by norm_num)
theorem B3209411 : Blo 2139435 3209411 := bstep (se 1 (by rfl) ⟨2407058, by rfl⟩ : syracuseStep 3209411 = 4814117) B4814117
theorem B2139607 : Blo 2139435 2139607 := bstep (se 1 (by rfl) ⟨1604705, by rfl⟩ : syracuseStep 2139607 = 3209411) B3209411
theorem B5415893 : Blo 2139435 5415893 := bbase (se 7 (by rfl) ⟨63467, by rfl⟩ : syracuseStep 5415893 = 126935) (by norm_num)
theorem B3610595 : Blo 2139435 3610595 := bstep (se 1 (by rfl) ⟨2707946, by rfl⟩ : syracuseStep 3610595 = 5415893) B5415893
theorem B2407063 : Blo 2139435 2407063 := bstep (se 1 (by rfl) ⟨1805297, by rfl⟩ : syracuseStep 2407063 = 3610595) B3610595
theorem B3209417 : Blo 2139435 3209417 := bstep (se 2 (by rfl) ⟨1203531, by rfl⟩ : syracuseStep 3209417 = 2407063) B2407063
theorem B2139611 : Blo 2139435 2139611 := bstep (se 1 (by rfl) ⟨1604708, by rfl⟩ : syracuseStep 2139611 = 3209417) B3209417
theorem B2931197 : Blo 2139435 2931197 := bbase (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) (by norm_num)
theorem B31266101 : Blo 2139435 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B20844067 : Blo 2139435 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B27792089 : Blo 2139435 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B18528059 : Blo 2139435 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B49408157 : Blo 2139435 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B131755085 : Blo 2139435 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B87836723 : Blo 2139435 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B58557815 : Blo 2139435 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B39038543 : Blo 2139435 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B26025695 : Blo 2139435 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B17350463 : Blo 2139435 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B11566975 : Blo 2139435 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B15422633 : Blo 2139435 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B10281755 : Blo 2139435 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B6854503 : Blo 2139435 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B9139337 : Blo 2139435 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B6092891 : Blo 2139435 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B4061927 : Blo 2139435 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B10831805 : Blo 2139435 10831805 := bstep (se 3 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 10831805 = 4061927) B4061927
theorem B7221203 : Blo 2139435 7221203 := bstep (se 1 (by rfl) ⟨5415902, by rfl⟩ : syracuseStep 7221203 = 10831805) B10831805
theorem B4814135 : Blo 2139435 4814135 := bstep (se 1 (by rfl) ⟨3610601, by rfl⟩ : syracuseStep 4814135 = 7221203) B7221203
theorem B3209423 : Blo 2139435 3209423 := bstep (se 1 (by rfl) ⟨2407067, by rfl⟩ : syracuseStep 3209423 = 4814135) B4814135
theorem B2139615 : Blo 2139435 2139615 := bstep (se 1 (by rfl) ⟨1604711, by rfl⟩ : syracuseStep 2139615 = 3209423) B3209423
theorem B3209429 : Blo 2139435 3209429 := bbase (se 7 (by rfl) ⟨37610, by rfl⟩ : syracuseStep 3209429 = 75221) (by norm_num)
theorem B2139619 : Blo 2139435 2139619 := bstep (se 1 (by rfl) ⟨1604714, by rfl⟩ : syracuseStep 2139619 = 3209429) B3209429
theorem B2570449 : Blo 2139435 2570449 := bbase (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) (by norm_num)
theorem B3427265 : Blo 2139435 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B2284843 : Blo 2139435 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B3046457 : Blo 2139435 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B8123885 : Blo 2139435 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B5415923 : Blo 2139435 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B3610615 : Blo 2139435 3610615 := bstep (se 1 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 3610615 = 5415923) B5415923
theorem B4814153 : Blo 2139435 4814153 := bstep (se 2 (by rfl) ⟨1805307, by rfl⟩ : syracuseStep 4814153 = 3610615) B3610615
theorem B3209435 : Blo 2139435 3209435 := bstep (se 1 (by rfl) ⟨2407076, by rfl⟩ : syracuseStep 3209435 = 4814153) B4814153
theorem B2139623 : Blo 2139435 2139623 := bstep (se 1 (by rfl) ⟨1604717, by rfl⟩ : syracuseStep 2139623 = 3209435) B3209435
theorem B2407081 : Blo 2139435 2407081 := bbase (se 2 (by rfl) ⟨902655, by rfl⟩ : syracuseStep 2407081 = 1805311) (by norm_num)
theorem B3209441 : Blo 2139435 3209441 := bstep (se 2 (by rfl) ⟨1203540, by rfl⟩ : syracuseStep 3209441 = 2407081) B2407081
theorem B2139627 : Blo 2139435 2139627 := bstep (se 1 (by rfl) ⟨1604720, by rfl⟩ : syracuseStep 2139627 = 3209441) B3209441
theorem B3427277 : Blo 2139435 3427277 := bbase (se 3 (by rfl) ⟨642614, by rfl⟩ : syracuseStep 3427277 = 1285229) (by norm_num)
theorem B9139405 : Blo 2139435 9139405 := bstep (se 3 (by rfl) ⟨1713638, by rfl⟩ : syracuseStep 9139405 = 3427277) B3427277
theorem B12185873 : Blo 2139435 12185873 := bstep (se 2 (by rfl) ⟨4569702, by rfl⟩ : syracuseStep 12185873 = 9139405) B9139405
theorem B8123915 : Blo 2139435 8123915 := bstep (se 1 (by rfl) ⟨6092936, by rfl⟩ : syracuseStep 8123915 = 12185873) B12185873
theorem B5415943 : Blo 2139435 5415943 := bstep (se 1 (by rfl) ⟨4061957, by rfl⟩ : syracuseStep 5415943 = 8123915) B8123915
theorem B7221257 : Blo 2139435 7221257 := bstep (se 2 (by rfl) ⟨2707971, by rfl⟩ : syracuseStep 7221257 = 5415943) B5415943
theorem B4814171 : Blo 2139435 4814171 := bstep (se 1 (by rfl) ⟨3610628, by rfl⟩ : syracuseStep 4814171 = 7221257) B7221257
theorem B3209447 : Blo 2139435 3209447 := bstep (se 1 (by rfl) ⟨2407085, by rfl⟩ : syracuseStep 3209447 = 4814171) B4814171
theorem B2139631 : Blo 2139435 2139631 := bstep (se 1 (by rfl) ⟨1604723, by rfl⟩ : syracuseStep 2139631 = 3209447) B3209447
theorem B3209453 : Blo 2139435 3209453 := bbase (se 3 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 3209453 = 1203545) (by norm_num)
theorem B2139635 : Blo 2139435 2139635 := bstep (se 1 (by rfl) ⟨1604726, by rfl⟩ : syracuseStep 2139635 = 3209453) B3209453
theorem B4814189 : Blo 2139435 4814189 := bbase (se 3 (by rfl) ⟨902660, by rfl⟩ : syracuseStep 4814189 = 1805321) (by norm_num)
theorem B3209459 : Blo 2139435 3209459 := bstep (se 1 (by rfl) ⟨2407094, by rfl⟩ : syracuseStep 3209459 = 4814189) B4814189
theorem B2139639 : Blo 2139435 2139639 := bstep (se 1 (by rfl) ⟨1604729, by rfl⟩ : syracuseStep 2139639 = 3209459) B3209459
theorem B4061981 : Blo 2139435 4061981 := bbase (se 3 (by rfl) ⟨761621, by rfl⟩ : syracuseStep 4061981 = 1523243) (by norm_num)
theorem B2707987 : Blo 2139435 2707987 := bstep (se 1 (by rfl) ⟨2030990, by rfl⟩ : syracuseStep 2707987 = 4061981) B4061981
theorem B3610649 : Blo 2139435 3610649 := bstep (se 2 (by rfl) ⟨1353993, by rfl⟩ : syracuseStep 3610649 = 2707987) B2707987
theorem B2407099 : Blo 2139435 2407099 := bstep (se 1 (by rfl) ⟨1805324, by rfl⟩ : syracuseStep 2407099 = 3610649) B3610649
theorem B3209465 : Blo 2139435 3209465 := bstep (se 2 (by rfl) ⟨1203549, by rfl⟩ : syracuseStep 3209465 = 2407099) B2407099
theorem B2139643 : Blo 2139435 2139643 := bstep (se 1 (by rfl) ⟨1604732, by rfl⟩ : syracuseStep 2139643 = 3209465) B3209465
theorem B5783573 : Blo 2139435 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B15422861 : Blo 2139435 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B10281907 : Blo 2139435 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B54836837 : Blo 2139435 54836837 := bstep (se 4 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 54836837 = 10281907) B10281907
theorem B36557891 : Blo 2139435 36557891 := bstep (se 1 (by rfl) ⟨27418418, by rfl⟩ : syracuseStep 36557891 = 54836837) B54836837
theorem B24371927 : Blo 2139435 24371927 := bstep (se 1 (by rfl) ⟨18278945, by rfl⟩ : syracuseStep 24371927 = 36557891) B36557891
theorem B16247951 : Blo 2139435 16247951 := bstep (se 1 (by rfl) ⟨12185963, by rfl⟩ : syracuseStep 16247951 = 24371927) B24371927
theorem B10831967 : Blo 2139435 10831967 := bstep (se 1 (by rfl) ⟨8123975, by rfl⟩ : syracuseStep 10831967 = 16247951) B16247951
theorem B7221311 : Blo 2139435 7221311 := bstep (se 1 (by rfl) ⟨5415983, by rfl⟩ : syracuseStep 7221311 = 10831967) B10831967
theorem B4814207 : Blo 2139435 4814207 := bstep (se 1 (by rfl) ⟨3610655, by rfl⟩ : syracuseStep 4814207 = 7221311) B7221311
theorem B3209471 : Blo 2139435 3209471 := bstep (se 1 (by rfl) ⟨2407103, by rfl⟩ : syracuseStep 3209471 = 4814207) B4814207
theorem B2139647 : Blo 2139435 2139647 := bstep (se 1 (by rfl) ⟨1604735, by rfl⟩ : syracuseStep 2139647 = 3209471) B3209471
theorem B3209477 : Blo 2139435 3209477 := bbase (se 4 (by rfl) ⟨300888, by rfl⟩ : syracuseStep 3209477 = 601777) (by norm_num)
theorem B2139651 : Blo 2139435 2139651 := bstep (se 1 (by rfl) ⟨1604738, by rfl⟩ : syracuseStep 2139651 = 3209477) B3209477
theorem B3610669 : Blo 2139435 3610669 := bbase (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) (by norm_num)
theorem B4814225 : Blo 2139435 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B3209483 : Blo 2139435 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B2139655 : Blo 2139435 2139655 := bstep (se 1 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 2139655 = 3209483) B3209483
theorem B2407117 : Blo 2139435 2407117 := bbase (se 3 (by rfl) ⟨451334, by rfl⟩ : syracuseStep 2407117 = 902669) (by norm_num)
theorem B3209489 : Blo 2139435 3209489 := bstep (se 2 (by rfl) ⟨1203558, by rfl⟩ : syracuseStep 3209489 = 2407117) B2407117
theorem B2139659 : Blo 2139435 2139659 := bstep (se 1 (by rfl) ⟨1604744, by rfl⟩ : syracuseStep 2139659 = 3209489) B3209489
theorem B7221365 : Blo 2139435 7221365 := bbase (se 5 (by rfl) ⟨338501, by rfl⟩ : syracuseStep 7221365 = 677003) (by norm_num)
theorem B4814243 : Blo 2139435 4814243 := bstep (se 1 (by rfl) ⟨3610682, by rfl⟩ : syracuseStep 4814243 = 7221365) B7221365
theorem B3209495 : Blo 2139435 3209495 := bstep (se 1 (by rfl) ⟨2407121, by rfl⟩ : syracuseStep 3209495 = 4814243) B4814243
theorem B2139663 : Blo 2139435 2139663 := bstep (se 1 (by rfl) ⟨1604747, by rfl⟩ : syracuseStep 2139663 = 3209495) B3209495
theorem B3209501 : Blo 2139435 3209501 := bbase (se 3 (by rfl) ⟨601781, by rfl⟩ : syracuseStep 3209501 = 1203563) (by norm_num)
theorem B2139667 : Blo 2139435 2139667 := bstep (se 1 (by rfl) ⟨1604750, by rfl⟩ : syracuseStep 2139667 = 3209501) B3209501
theorem B4814261 : Blo 2139435 4814261 := bbase (se 5 (by rfl) ⟨225668, by rfl⟩ : syracuseStep 4814261 = 451337) (by norm_num)
theorem B3209507 : Blo 2139435 3209507 := bstep (se 1 (by rfl) ⟨2407130, by rfl⟩ : syracuseStep 3209507 = 4814261) B4814261
theorem B2139671 : Blo 2139435 2139671 := bstep (se 1 (by rfl) ⟨1604753, by rfl⟩ : syracuseStep 2139671 = 3209507) B3209507
theorem B4569797 : Blo 2139435 4569797 := bbase (se 4 (by rfl) ⟨428418, by rfl⟩ : syracuseStep 4569797 = 856837) (by norm_num)
theorem B12186125 : Blo 2139435 12186125 := bstep (se 3 (by rfl) ⟨2284898, by rfl⟩ : syracuseStep 12186125 = 4569797) B4569797
theorem B8124083 : Blo 2139435 8124083 := bstep (se 1 (by rfl) ⟨6093062, by rfl⟩ : syracuseStep 8124083 = 12186125) B12186125
theorem B5416055 : Blo 2139435 5416055 := bstep (se 1 (by rfl) ⟨4062041, by rfl⟩ : syracuseStep 5416055 = 8124083) B8124083
theorem B3610703 : Blo 2139435 3610703 := bstep (se 1 (by rfl) ⟨2708027, by rfl⟩ : syracuseStep 3610703 = 5416055) B5416055
theorem B2407135 : Blo 2139435 2407135 := bstep (se 1 (by rfl) ⟨1805351, by rfl⟩ : syracuseStep 2407135 = 3610703) B3610703
theorem B3209513 : Blo 2139435 3209513 := bstep (se 2 (by rfl) ⟨1203567, by rfl⟩ : syracuseStep 3209513 = 2407135) B2407135
theorem B2139675 : Blo 2139435 2139675 := bstep (se 1 (by rfl) ⟨1604756, by rfl⟩ : syracuseStep 2139675 = 3209513) B3209513
theorem B4569805 : Blo 2139435 4569805 := bbase (se 3 (by rfl) ⟨856838, by rfl⟩ : syracuseStep 4569805 = 1713677) (by norm_num)
theorem B6093073 : Blo 2139435 6093073 := bstep (se 2 (by rfl) ⟨2284902, by rfl⟩ : syracuseStep 6093073 = 4569805) B4569805
theorem B8124097 : Blo 2139435 8124097 := bstep (se 2 (by rfl) ⟨3046536, by rfl⟩ : syracuseStep 8124097 = 6093073) B6093073
theorem B10832129 : Blo 2139435 10832129 := bstep (se 2 (by rfl) ⟨4062048, by rfl⟩ : syracuseStep 10832129 = 8124097) B8124097
theorem B7221419 : Blo 2139435 7221419 := bstep (se 1 (by rfl) ⟨5416064, by rfl⟩ : syracuseStep 7221419 = 10832129) B10832129
theorem B4814279 : Blo 2139435 4814279 := bstep (se 1 (by rfl) ⟨3610709, by rfl⟩ : syracuseStep 4814279 = 7221419) B7221419
theorem B3209519 : Blo 2139435 3209519 := bstep (se 1 (by rfl) ⟨2407139, by rfl⟩ : syracuseStep 3209519 = 4814279) B4814279
theorem B2139679 : Blo 2139435 2139679 := bstep (se 1 (by rfl) ⟨1604759, by rfl⟩ : syracuseStep 2139679 = 3209519) B3209519
theorem B3209525 : Blo 2139435 3209525 := bbase (se 5 (by rfl) ⟨150446, by rfl⟩ : syracuseStep 3209525 = 300893) (by norm_num)
theorem B2139683 : Blo 2139435 2139683 := bstep (se 1 (by rfl) ⟨1604762, by rfl⟩ : syracuseStep 2139683 = 3209525) B3209525
theorem B5416085 : Blo 2139435 5416085 := bbase (se 6 (by rfl) ⟨126939, by rfl⟩ : syracuseStep 5416085 = 253879) (by norm_num)
theorem B3610723 : Blo 2139435 3610723 := bstep (se 1 (by rfl) ⟨2708042, by rfl⟩ : syracuseStep 3610723 = 5416085) B5416085
theorem B4814297 : Blo 2139435 4814297 := bstep (se 2 (by rfl) ⟨1805361, by rfl⟩ : syracuseStep 4814297 = 3610723) B3610723
theorem B3209531 : Blo 2139435 3209531 := bstep (se 1 (by rfl) ⟨2407148, by rfl⟩ : syracuseStep 3209531 = 4814297) B4814297
theorem B2139687 : Blo 2139435 2139687 := bstep (se 1 (by rfl) ⟨1604765, by rfl⟩ : syracuseStep 2139687 = 3209531) B3209531
theorem B2407153 : Blo 2139435 2407153 := bbase (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) (by norm_num)
theorem B3209537 : Blo 2139435 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B2139691 : Blo 2139435 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B12352501 : Blo 2139435 12352501 := bbase (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) (by norm_num)
theorem B16470001 : Blo 2139435 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B21960001 : Blo 2139435 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B29280001 : Blo 2139435 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B39040001 : Blo 2139435 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B26026667 : Blo 2139435 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B17351111 : Blo 2139435 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B46269629 : Blo 2139435 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B30846419 : Blo 2139435 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B20564279 : Blo 2139435 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B13709519 : Blo 2139435 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B9139679 : Blo 2139435 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B6093119 : Blo 2139435 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B4062079 : Blo 2139435 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B5416105 : Blo 2139435 5416105 := bstep (se 2 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 5416105 = 4062079) B4062079
theorem B7221473 : Blo 2139435 7221473 := bstep (se 2 (by rfl) ⟨2708052, by rfl⟩ : syracuseStep 7221473 = 5416105) B5416105
theorem B4814315 : Blo 2139435 4814315 := bstep (se 1 (by rfl) ⟨3610736, by rfl⟩ : syracuseStep 4814315 = 7221473) B7221473
theorem B3209543 : Blo 2139435 3209543 := bstep (se 1 (by rfl) ⟨2407157, by rfl⟩ : syracuseStep 3209543 = 4814315) B4814315
theorem B2139695 : Blo 2139435 2139695 := bstep (se 1 (by rfl) ⟨1604771, by rfl⟩ : syracuseStep 2139695 = 3209543) B3209543
theorem B3209549 : Blo 2139435 3209549 := bbase (se 3 (by rfl) ⟨601790, by rfl⟩ : syracuseStep 3209549 = 1203581) (by norm_num)
theorem B2139699 : Blo 2139435 2139699 := bstep (se 1 (by rfl) ⟨1604774, by rfl⟩ : syracuseStep 2139699 = 3209549) B3209549
theorem B4814333 : Blo 2139435 4814333 := bbase (se 3 (by rfl) ⟨902687, by rfl⟩ : syracuseStep 4814333 = 1805375) (by norm_num)
theorem B3209555 : Blo 2139435 3209555 := bstep (se 1 (by rfl) ⟨2407166, by rfl⟩ : syracuseStep 3209555 = 4814333) B4814333
theorem B2139703 : Blo 2139435 2139703 := bstep (se 1 (by rfl) ⟨1604777, by rfl⟩ : syracuseStep 2139703 = 3209555) B3209555
theorem B3610757 : Blo 2139435 3610757 := bbase (se 4 (by rfl) ⟨338508, by rfl⟩ : syracuseStep 3610757 = 677017) (by norm_num)
theorem B2407171 : Blo 2139435 2407171 := bstep (se 1 (by rfl) ⟨1805378, by rfl⟩ : syracuseStep 2407171 = 3610757) B3610757
theorem B3209561 : Blo 2139435 3209561 := bstep (se 2 (by rfl) ⟨1203585, by rfl⟩ : syracuseStep 3209561 = 2407171) B2407171
theorem B2139707 : Blo 2139435 2139707 := bstep (se 1 (by rfl) ⟨1604780, by rfl⟩ : syracuseStep 2139707 = 3209561) B3209561
theorem B16248437 : Blo 2139435 16248437 := bbase (se 5 (by rfl) ⟨761645, by rfl⟩ : syracuseStep 16248437 = 1523291) (by norm_num)
theorem B10832291 : Blo 2139435 10832291 := bstep (se 1 (by rfl) ⟨8124218, by rfl⟩ : syracuseStep 10832291 = 16248437) B16248437
theorem B7221527 : Blo 2139435 7221527 := bstep (se 1 (by rfl) ⟨5416145, by rfl⟩ : syracuseStep 7221527 = 10832291) B10832291
theorem B4814351 : Blo 2139435 4814351 := bstep (se 1 (by rfl) ⟨3610763, by rfl⟩ : syracuseStep 4814351 = 7221527) B7221527
theorem B3209567 : Blo 2139435 3209567 := bstep (se 1 (by rfl) ⟨2407175, by rfl⟩ : syracuseStep 3209567 = 4814351) B4814351
theorem B2139711 : Blo 2139435 2139711 := bstep (se 1 (by rfl) ⟨1604783, by rfl⟩ : syracuseStep 2139711 = 3209567) B3209567
theorem B3209573 : Blo 2139435 3209573 := bbase (se 4 (by rfl) ⟨300897, by rfl⟩ : syracuseStep 3209573 = 601795) (by norm_num)
theorem B2139715 : Blo 2139435 2139715 := bstep (se 1 (by rfl) ⟨1604786, by rfl⟩ : syracuseStep 2139715 = 3209573) B3209573
theorem B4062125 : Blo 2139435 4062125 := bbase (se 3 (by rfl) ⟨761648, by rfl⟩ : syracuseStep 4062125 = 1523297) (by norm_num)
theorem B2708083 : Blo 2139435 2708083 := bstep (se 1 (by rfl) ⟨2031062, by rfl⟩ : syracuseStep 2708083 = 4062125) B4062125
theorem B3610777 : Blo 2139435 3610777 := bstep (se 2 (by rfl) ⟨1354041, by rfl⟩ : syracuseStep 3610777 = 2708083) B2708083
theorem B4814369 : Blo 2139435 4814369 := bstep (se 2 (by rfl) ⟨1805388, by rfl⟩ : syracuseStep 4814369 = 3610777) B3610777
theorem B3209579 : Blo 2139435 3209579 := bstep (se 1 (by rfl) ⟨2407184, by rfl⟩ : syracuseStep 3209579 = 4814369) B4814369
theorem B2139719 : Blo 2139435 2139719 := bstep (se 1 (by rfl) ⟨1604789, by rfl⟩ : syracuseStep 2139719 = 3209579) B3209579
theorem B2407189 : Blo 2139435 2407189 := bbase (se 6 (by rfl) ⟨56418, by rfl⟩ : syracuseStep 2407189 = 112837) (by norm_num)
theorem B3209585 : Blo 2139435 3209585 := bstep (se 2 (by rfl) ⟨1203594, by rfl⟩ : syracuseStep 3209585 = 2407189) B2407189
theorem B2139723 : Blo 2139435 2139723 := bstep (se 1 (by rfl) ⟨1604792, by rfl⟩ : syracuseStep 2139723 = 3209585) B3209585
theorem B2708093 : Blo 2139435 2708093 := bbase (se 3 (by rfl) ⟨507767, by rfl⟩ : syracuseStep 2708093 = 1015535) (by norm_num)
theorem B7221581 : Blo 2139435 7221581 := bstep (se 3 (by rfl) ⟨1354046, by rfl⟩ : syracuseStep 7221581 = 2708093) B2708093
theorem B4814387 : Blo 2139435 4814387 := bstep (se 1 (by rfl) ⟨3610790, by rfl⟩ : syracuseStep 4814387 = 7221581) B7221581
theorem B3209591 : Blo 2139435 3209591 := bstep (se 1 (by rfl) ⟨2407193, by rfl⟩ : syracuseStep 3209591 = 4814387) B4814387
theorem B2139727 : Blo 2139435 2139727 := bstep (se 1 (by rfl) ⟨1604795, by rfl⟩ : syracuseStep 2139727 = 3209591) B3209591
theorem B3209597 : Blo 2139435 3209597 := bbase (se 3 (by rfl) ⟨601799, by rfl⟩ : syracuseStep 3209597 = 1203599) (by norm_num)
theorem B2139731 : Blo 2139435 2139731 := bstep (se 1 (by rfl) ⟨1604798, by rfl⟩ : syracuseStep 2139731 = 3209597) B3209597
theorem B4814405 : Blo 2139435 4814405 := bbase (se 4 (by rfl) ⟨451350, by rfl⟩ : syracuseStep 4814405 = 902701) (by norm_num)
theorem B3209603 : Blo 2139435 3209603 := bstep (se 1 (by rfl) ⟨2407202, by rfl⟩ : syracuseStep 3209603 = 4814405) B4814405
theorem B2139735 : Blo 2139435 2139735 := bstep (se 1 (by rfl) ⟨1604801, by rfl⟩ : syracuseStep 2139735 = 3209603) B3209603
theorem B4337869 : Blo 2139435 4337869 := bbase (se 3 (by rfl) ⟨813350, by rfl⟩ : syracuseStep 4337869 = 1626701) (by norm_num)
theorem B5783825 : Blo 2139435 5783825 := bstep (se 2 (by rfl) ⟨2168934, by rfl⟩ : syracuseStep 5783825 = 4337869) B4337869
theorem B3855883 : Blo 2139435 3855883 := bstep (se 1 (by rfl) ⟨2891912, by rfl⟩ : syracuseStep 3855883 = 5783825) B5783825
theorem B5141177 : Blo 2139435 5141177 := bstep (se 2 (by rfl) ⟨1927941, by rfl⟩ : syracuseStep 5141177 = 3855883) B3855883
theorem B3427451 : Blo 2139435 3427451 := bstep (se 1 (by rfl) ⟨2570588, by rfl⟩ : syracuseStep 3427451 = 5141177) B5141177
theorem B2284967 : Blo 2139435 2284967 := bstep (se 1 (by rfl) ⟨1713725, by rfl⟩ : syracuseStep 2284967 = 3427451) B3427451
theorem B6093245 : Blo 2139435 6093245 := bstep (se 3 (by rfl) ⟨1142483, by rfl⟩ : syracuseStep 6093245 = 2284967) B2284967
theorem B4062163 : Blo 2139435 4062163 := bstep (se 1 (by rfl) ⟨3046622, by rfl⟩ : syracuseStep 4062163 = 6093245) B6093245
theorem B5416217 : Blo 2139435 5416217 := bstep (se 2 (by rfl) ⟨2031081, by rfl⟩ : syracuseStep 5416217 = 4062163) B4062163
theorem B3610811 : Blo 2139435 3610811 := bstep (se 1 (by rfl) ⟨2708108, by rfl⟩ : syracuseStep 3610811 = 5416217) B5416217
theorem B2407207 : Blo 2139435 2407207 := bstep (se 1 (by rfl) ⟨1805405, by rfl⟩ : syracuseStep 2407207 = 3610811) B3610811
theorem B3209609 : Blo 2139435 3209609 := bstep (se 2 (by rfl) ⟨1203603, by rfl⟩ : syracuseStep 3209609 = 2407207) B2407207
theorem B2139739 : Blo 2139435 2139739 := bstep (se 1 (by rfl) ⟨1604804, by rfl⟩ : syracuseStep 2139739 = 3209609) B3209609
theorem B10832453 : Blo 2139435 10832453 := bbase (se 4 (by rfl) ⟨1015542, by rfl⟩ : syracuseStep 10832453 = 2031085) (by norm_num)
theorem B7221635 : Blo 2139435 7221635 := bstep (se 1 (by rfl) ⟨5416226, by rfl⟩ : syracuseStep 7221635 = 10832453) B10832453
theorem B4814423 : Blo 2139435 4814423 := bstep (se 1 (by rfl) ⟨3610817, by rfl⟩ : syracuseStep 4814423 = 7221635) B7221635
theorem B3209615 : Blo 2139435 3209615 := bstep (se 1 (by rfl) ⟨2407211, by rfl⟩ : syracuseStep 3209615 = 4814423) B4814423
theorem B2139743 : Blo 2139435 2139743 := bstep (se 1 (by rfl) ⟨1604807, by rfl⟩ : syracuseStep 2139743 = 3209615) B3209615
theorem B3209621 : Blo 2139435 3209621 := bbase (se 6 (by rfl) ⟨75225, by rfl⟩ : syracuseStep 3209621 = 150451) (by norm_num)
theorem B2139747 : Blo 2139435 2139747 := bstep (se 1 (by rfl) ⟨1604810, by rfl⟩ : syracuseStep 2139747 = 3209621) B3209621
theorem B2473357 : Blo 2139435 2473357 := bbase (se 3 (by rfl) ⟨463754, by rfl⟩ : syracuseStep 2473357 = 927509) (by norm_num)
theorem B3297809 : Blo 2139435 3297809 := bstep (se 2 (by rfl) ⟨1236678, by rfl⟩ : syracuseStep 3297809 = 2473357) B2473357
theorem B2198539 : Blo 2139435 2198539 := bstep (se 1 (by rfl) ⟨1648904, by rfl⟩ : syracuseStep 2198539 = 3297809) B3297809
theorem B2931385 : Blo 2139435 2931385 := bstep (se 2 (by rfl) ⟨1099269, by rfl⟩ : syracuseStep 2931385 = 2198539) B2198539
theorem B3908513 : Blo 2139435 3908513 := bstep (se 2 (by rfl) ⟨1465692, by rfl⟩ : syracuseStep 3908513 = 2931385) B2931385
theorem B2605675 : Blo 2139435 2605675 := bstep (se 1 (by rfl) ⟨1954256, by rfl⟩ : syracuseStep 2605675 = 3908513) B3908513
theorem B3474233 : Blo 2139435 3474233 := bstep (se 2 (by rfl) ⟨1302837, by rfl⟩ : syracuseStep 3474233 = 2605675) B2605675
theorem B2316155 : Blo 2139435 2316155 := bstep (se 1 (by rfl) ⟨1737116, by rfl⟩ : syracuseStep 2316155 = 3474233) B3474233
theorem B6176413 : Blo 2139435 6176413 := bstep (se 3 (by rfl) ⟨1158077, by rfl⟩ : syracuseStep 6176413 = 2316155) B2316155
theorem B8235217 : Blo 2139435 8235217 := bstep (se 2 (by rfl) ⟨3088206, by rfl⟩ : syracuseStep 8235217 = 6176413) B6176413
theorem B10980289 : Blo 2139435 10980289 := bstep (se 2 (by rfl) ⟨4117608, by rfl⟩ : syracuseStep 10980289 = 8235217) B8235217
theorem B58561541 : Blo 2139435 58561541 := bstep (se 4 (by rfl) ⟨5490144, by rfl⟩ : syracuseStep 58561541 = 10980289) B10980289
theorem B39041027 : Blo 2139435 39041027 := bstep (se 1 (by rfl) ⟨29280770, by rfl⟩ : syracuseStep 39041027 = 58561541) B58561541
theorem B26027351 : Blo 2139435 26027351 := bstep (se 1 (by rfl) ⟨19520513, by rfl⟩ : syracuseStep 26027351 = 39041027) B39041027
theorem B17351567 : Blo 2139435 17351567 := bstep (se 1 (by rfl) ⟨13013675, by rfl⟩ : syracuseStep 17351567 = 26027351) B26027351
theorem B11567711 : Blo 2139435 11567711 := bstep (se 1 (by rfl) ⟨8675783, by rfl⟩ : syracuseStep 11567711 = 17351567) B17351567
theorem B7711807 : Blo 2139435 7711807 := bstep (se 1 (by rfl) ⟨5783855, by rfl⟩ : syracuseStep 7711807 = 11567711) B11567711
theorem B10282409 : Blo 2139435 10282409 := bstep (se 2 (by rfl) ⟨3855903, by rfl⟩ : syracuseStep 10282409 = 7711807) B7711807
theorem B6854939 : Blo 2139435 6854939 := bstep (se 1 (by rfl) ⟨5141204, by rfl⟩ : syracuseStep 6854939 = 10282409) B10282409
theorem B4569959 : Blo 2139435 4569959 := bstep (se 1 (by rfl) ⟨3427469, by rfl⟩ : syracuseStep 4569959 = 6854939) B6854939
theorem B12186557 : Blo 2139435 12186557 := bstep (se 3 (by rfl) ⟨2284979, by rfl⟩ : syracuseStep 12186557 = 4569959) B4569959
theorem B8124371 : Blo 2139435 8124371 := bstep (se 1 (by rfl) ⟨6093278, by rfl⟩ : syracuseStep 8124371 = 12186557) B12186557
theorem B5416247 : Blo 2139435 5416247 := bstep (se 1 (by rfl) ⟨4062185, by rfl⟩ : syracuseStep 5416247 = 8124371) B8124371
theorem B3610831 : Blo 2139435 3610831 := bstep (se 1 (by rfl) ⟨2708123, by rfl⟩ : syracuseStep 3610831 = 5416247) B5416247
theorem B4814441 : Blo 2139435 4814441 := bstep (se 2 (by rfl) ⟨1805415, by rfl⟩ : syracuseStep 4814441 = 3610831) B3610831
theorem B3209627 : Blo 2139435 3209627 := bstep (se 1 (by rfl) ⟨2407220, by rfl⟩ : syracuseStep 3209627 = 4814441) B4814441
theorem B2139751 : Blo 2139435 2139751 := bstep (se 1 (by rfl) ⟨1604813, by rfl⟩ : syracuseStep 2139751 = 3209627) B3209627
theorem B2407225 : Blo 2139435 2407225 := bbase (se 2 (by rfl) ⟨902709, by rfl⟩ : syracuseStep 2407225 = 1805419) (by norm_num)
theorem B3209633 : Blo 2139435 3209633 := bstep (se 2 (by rfl) ⟨1203612, by rfl⟩ : syracuseStep 3209633 = 2407225) B2407225
theorem B2139755 : Blo 2139435 2139755 := bstep (se 1 (by rfl) ⟨1604816, by rfl⟩ : syracuseStep 2139755 = 3209633) B3209633
theorem B6093301 : Blo 2139435 6093301 := bbase (se 5 (by rfl) ⟨285623, by rfl⟩ : syracuseStep 6093301 = 571247) (by norm_num)
theorem B8124401 : Blo 2139435 8124401 := bstep (se 2 (by rfl) ⟨3046650, by rfl⟩ : syracuseStep 8124401 = 6093301) B6093301
theorem B5416267 : Blo 2139435 5416267 := bstep (se 1 (by rfl) ⟨4062200, by rfl⟩ : syracuseStep 5416267 = 8124401) B8124401
theorem B7221689 : Blo 2139435 7221689 := bstep (se 2 (by rfl) ⟨2708133, by rfl⟩ : syracuseStep 7221689 = 5416267) B5416267
theorem B4814459 : Blo 2139435 4814459 := bstep (se 1 (by rfl) ⟨3610844, by rfl⟩ : syracuseStep 4814459 = 7221689) B7221689
theorem B3209639 : Blo 2139435 3209639 := bstep (se 1 (by rfl) ⟨2407229, by rfl⟩ : syracuseStep 3209639 = 4814459) B4814459
theorem B2139759 : Blo 2139435 2139759 := bstep (se 1 (by rfl) ⟨1604819, by rfl⟩ : syracuseStep 2139759 = 3209639) B3209639
theorem B3209645 : Blo 2139435 3209645 := bbase (se 3 (by rfl) ⟨601808, by rfl⟩ : syracuseStep 3209645 = 1203617) (by norm_num)
theorem B2139763 : Blo 2139435 2139763 := bstep (se 1 (by rfl) ⟨1604822, by rfl⟩ : syracuseStep 2139763 = 3209645) B3209645
theorem B4814477 : Blo 2139435 4814477 := bbase (se 3 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 4814477 = 1805429) (by norm_num)
theorem B3209651 : Blo 2139435 3209651 := bstep (se 1 (by rfl) ⟨2407238, by rfl⟩ : syracuseStep 3209651 = 4814477) B4814477
theorem B2139767 : Blo 2139435 2139767 := bstep (se 1 (by rfl) ⟨1604825, by rfl⟩ : syracuseStep 2139767 = 3209651) B3209651
theorem B2708149 : Blo 2139435 2708149 := bbase (se 5 (by rfl) ⟨126944, by rfl⟩ : syracuseStep 2708149 = 253889) (by norm_num)
theorem B3610865 : Blo 2139435 3610865 := bstep (se 2 (by rfl) ⟨1354074, by rfl⟩ : syracuseStep 3610865 = 2708149) B2708149
theorem B2407243 : Blo 2139435 2407243 := bstep (se 1 (by rfl) ⟨1805432, by rfl⟩ : syracuseStep 2407243 = 3610865) B3610865
theorem B3209657 : Blo 2139435 3209657 := bstep (se 2 (by rfl) ⟨1203621, by rfl⟩ : syracuseStep 3209657 = 2407243) B2407243
theorem B2139771 : Blo 2139435 2139771 := bstep (se 1 (by rfl) ⟨1604828, by rfl⟩ : syracuseStep 2139771 = 3209657) B3209657
theorem B4397125 : Blo 2139435 4397125 := bbase (se 4 (by rfl) ⟨412230, by rfl⟩ : syracuseStep 4397125 = 824461) (by norm_num)
theorem B5862833 : Blo 2139435 5862833 := bstep (se 2 (by rfl) ⟨2198562, by rfl⟩ : syracuseStep 5862833 = 4397125) B4397125
theorem B3908555 : Blo 2139435 3908555 := bstep (se 1 (by rfl) ⟨2931416, by rfl⟩ : syracuseStep 3908555 = 5862833) B5862833
theorem B2605703 : Blo 2139435 2605703 := bstep (se 1 (by rfl) ⟨1954277, by rfl⟩ : syracuseStep 2605703 = 3908555) B3908555
theorem B6948541 : Blo 2139435 6948541 := bstep (se 3 (by rfl) ⟨1302851, by rfl⟩ : syracuseStep 6948541 = 2605703) B2605703
theorem B9264721 : Blo 2139435 9264721 := bstep (se 2 (by rfl) ⟨3474270, by rfl⟩ : syracuseStep 9264721 = 6948541) B6948541
theorem B12352961 : Blo 2139435 12352961 := bstep (se 2 (by rfl) ⟨4632360, by rfl⟩ : syracuseStep 12352961 = 9264721) B9264721
theorem B8235307 : Blo 2139435 8235307 := bstep (se 1 (by rfl) ⟨6176480, by rfl⟩ : syracuseStep 8235307 = 12352961) B12352961
theorem B10980409 : Blo 2139435 10980409 := bstep (se 2 (by rfl) ⟨4117653, by rfl⟩ : syracuseStep 10980409 = 8235307) B8235307
theorem B14640545 : Blo 2139435 14640545 := bstep (se 2 (by rfl) ⟨5490204, by rfl⟩ : syracuseStep 14640545 = 10980409) B10980409
theorem B39041453 : Blo 2139435 39041453 := bstep (se 3 (by rfl) ⟨7320272, by rfl⟩ : syracuseStep 39041453 = 14640545) B14640545
theorem B104110541 : Blo 2139435 104110541 := bstep (se 3 (by rfl) ⟨19520726, by rfl⟩ : syracuseStep 104110541 = 39041453) B39041453
theorem B69407027 : Blo 2139435 69407027 := bstep (se 1 (by rfl) ⟨52055270, by rfl⟩ : syracuseStep 69407027 = 104110541) B104110541
theorem B46271351 : Blo 2139435 46271351 := bstep (se 1 (by rfl) ⟨34703513, by rfl⟩ : syracuseStep 46271351 = 69407027) B69407027
theorem B30847567 : Blo 2139435 30847567 := bstep (se 1 (by rfl) ⟨23135675, by rfl⟩ : syracuseStep 30847567 = 46271351) B46271351
theorem B41130089 : Blo 2139435 41130089 := bstep (se 2 (by rfl) ⟨15423783, by rfl⟩ : syracuseStep 41130089 = 30847567) B30847567
theorem B27420059 : Blo 2139435 27420059 := bstep (se 1 (by rfl) ⟨20565044, by rfl⟩ : syracuseStep 27420059 = 41130089) B41130089
theorem B18280039 : Blo 2139435 18280039 := bstep (se 1 (by rfl) ⟨13710029, by rfl⟩ : syracuseStep 18280039 = 27420059) B27420059
theorem B24373385 : Blo 2139435 24373385 := bstep (se 2 (by rfl) ⟨9140019, by rfl⟩ : syracuseStep 24373385 = 18280039) B18280039
theorem B16248923 : Blo 2139435 16248923 := bstep (se 1 (by rfl) ⟨12186692, by rfl⟩ : syracuseStep 16248923 = 24373385) B24373385
theorem B10832615 : Blo 2139435 10832615 := bstep (se 1 (by rfl) ⟨8124461, by rfl⟩ : syracuseStep 10832615 = 16248923) B16248923
theorem B7221743 : Blo 2139435 7221743 := bstep (se 1 (by rfl) ⟨5416307, by rfl⟩ : syracuseStep 7221743 = 10832615) B10832615
theorem B4814495 : Blo 2139435 4814495 := bstep (se 1 (by rfl) ⟨3610871, by rfl⟩ : syracuseStep 4814495 = 7221743) B7221743
theorem B3209663 : Blo 2139435 3209663 := bstep (se 1 (by rfl) ⟨2407247, by rfl⟩ : syracuseStep 3209663 = 4814495) B4814495
theorem B2139775 : Blo 2139435 2139775 := bstep (se 1 (by rfl) ⟨1604831, by rfl⟩ : syracuseStep 2139775 = 3209663) B3209663
theorem B3209669 : Blo 2139435 3209669 := bbase (se 4 (by rfl) ⟨300906, by rfl⟩ : syracuseStep 3209669 = 601813) (by norm_num)
theorem B2139779 : Blo 2139435 2139779 := bstep (se 1 (by rfl) ⟨1604834, by rfl⟩ : syracuseStep 2139779 = 3209669) B3209669
theorem B3610885 : Blo 2139435 3610885 := bbase (se 4 (by rfl) ⟨338520, by rfl⟩ : syracuseStep 3610885 = 677041) (by norm_num)
theorem B4814513 : Blo 2139435 4814513 := bstep (se 2 (by rfl) ⟨1805442, by rfl⟩ : syracuseStep 4814513 = 3610885) B3610885
theorem B3209675 : Blo 2139435 3209675 := bstep (se 1 (by rfl) ⟨2407256, by rfl⟩ : syracuseStep 3209675 = 4814513) B4814513
theorem B2139783 : Blo 2139435 2139783 := bstep (se 1 (by rfl) ⟨1604837, by rfl⟩ : syracuseStep 2139783 = 3209675) B3209675
theorem B2407261 : Blo 2139435 2407261 := bbase (se 3 (by rfl) ⟨451361, by rfl⟩ : syracuseStep 2407261 = 902723) (by norm_num)
theorem B3209681 : Blo 2139435 3209681 := bstep (se 2 (by rfl) ⟨1203630, by rfl⟩ : syracuseStep 3209681 = 2407261) B2407261
theorem B2139787 : Blo 2139435 2139787 := bstep (se 1 (by rfl) ⟨1604840, by rfl⟩ : syracuseStep 2139787 = 3209681) B3209681
theorem B7221797 : Blo 2139435 7221797 := bbase (se 4 (by rfl) ⟨677043, by rfl⟩ : syracuseStep 7221797 = 1354087) (by norm_num)
theorem B4814531 : Blo 2139435 4814531 := bstep (se 1 (by rfl) ⟨3610898, by rfl⟩ : syracuseStep 4814531 = 7221797) B7221797
theorem B3209687 : Blo 2139435 3209687 := bstep (se 1 (by rfl) ⟨2407265, by rfl⟩ : syracuseStep 3209687 = 4814531) B4814531
theorem B2139791 : Blo 2139435 2139791 := bstep (se 1 (by rfl) ⟨1604843, by rfl⟩ : syracuseStep 2139791 = 3209687) B3209687
theorem B3209693 : Blo 2139435 3209693 := bbase (se 3 (by rfl) ⟨601817, by rfl⟩ : syracuseStep 3209693 = 1203635) (by norm_num)
theorem B2139795 : Blo 2139435 2139795 := bstep (se 1 (by rfl) ⟨1604846, by rfl⟩ : syracuseStep 2139795 = 3209693) B3209693
theorem B4814549 : Blo 2139435 4814549 := bbase (se 7 (by rfl) ⟨56420, by rfl⟩ : syracuseStep 4814549 = 112841) (by norm_num)
theorem B3209699 : Blo 2139435 3209699 := bstep (se 1 (by rfl) ⟨2407274, by rfl⟩ : syracuseStep 3209699 = 4814549) B4814549
theorem B2139799 : Blo 2139435 2139799 := bstep (se 1 (by rfl) ⟨1604849, by rfl⟩ : syracuseStep 2139799 = 3209699) B3209699
theorem B2570665 : Blo 2139435 2570665 := bbase (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) (by norm_num)
theorem B3427553 : Blo 2139435 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B9140141 : Blo 2139435 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B6093427 : Blo 2139435 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B8124569 : Blo 2139435 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B5416379 : Blo 2139435 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B3610919 : Blo 2139435 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B2407279 : Blo 2139435 2407279 := bstep (se 1 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 2407279 = 3610919) B3610919
theorem B3209705 : Blo 2139435 3209705 := bstep (se 2 (by rfl) ⟨1203639, by rfl⟩ : syracuseStep 3209705 = 2407279) B2407279
theorem B2139803 : Blo 2139435 2139803 := bstep (se 1 (by rfl) ⟨1604852, by rfl⟩ : syracuseStep 2139803 = 3209705) B3209705
theorem B15634453 : Blo 2139435 15634453 := bbase (se 6 (by rfl) ⟨366432, by rfl⟩ : syracuseStep 15634453 = 732865) (by norm_num)
theorem B20845937 : Blo 2139435 20845937 := bstep (se 2 (by rfl) ⟨7817226, by rfl⟩ : syracuseStep 20845937 = 15634453) B15634453
theorem B55589165 : Blo 2139435 55589165 := bstep (se 3 (by rfl) ⟨10422968, by rfl⟩ : syracuseStep 55589165 = 20845937) B20845937
theorem B37059443 : Blo 2139435 37059443 := bstep (se 1 (by rfl) ⟨27794582, by rfl⟩ : syracuseStep 37059443 = 55589165) B55589165
theorem B24706295 : Blo 2139435 24706295 := bstep (se 1 (by rfl) ⟨18529721, by rfl⟩ : syracuseStep 24706295 = 37059443) B37059443
theorem B16470863 : Blo 2139435 16470863 := bstep (se 1 (by rfl) ⟨12353147, by rfl⟩ : syracuseStep 16470863 = 24706295) B24706295
theorem B10980575 : Blo 2139435 10980575 := bstep (se 1 (by rfl) ⟨8235431, by rfl⟩ : syracuseStep 10980575 = 16470863) B16470863
theorem B7320383 : Blo 2139435 7320383 := bstep (se 1 (by rfl) ⟨5490287, by rfl⟩ : syracuseStep 7320383 = 10980575) B10980575
theorem B4880255 : Blo 2139435 4880255 := bstep (se 1 (by rfl) ⟨3660191, by rfl⟩ : syracuseStep 4880255 = 7320383) B7320383
theorem B52056053 : Blo 2139435 52056053 := bstep (se 5 (by rfl) ⟨2440127, by rfl⟩ : syracuseStep 52056053 = 4880255) B4880255
theorem B34704035 : Blo 2139435 34704035 := bstep (se 1 (by rfl) ⟨26028026, by rfl⟩ : syracuseStep 34704035 = 52056053) B52056053
theorem B23136023 : Blo 2139435 23136023 := bstep (se 1 (by rfl) ⟨17352017, by rfl⟩ : syracuseStep 23136023 = 34704035) B34704035
theorem B15424015 : Blo 2139435 15424015 := bstep (se 1 (by rfl) ⟨11568011, by rfl⟩ : syracuseStep 15424015 = 23136023) B23136023
theorem B20565353 : Blo 2139435 20565353 := bstep (se 2 (by rfl) ⟨7712007, by rfl⟩ : syracuseStep 20565353 = 15424015) B15424015
theorem B13710235 : Blo 2139435 13710235 := bstep (se 1 (by rfl) ⟨10282676, by rfl⟩ : syracuseStep 13710235 = 20565353) B20565353
theorem B18280313 : Blo 2139435 18280313 := bstep (se 2 (by rfl) ⟨6855117, by rfl⟩ : syracuseStep 18280313 = 13710235) B13710235
theorem B12186875 : Blo 2139435 12186875 := bstep (se 1 (by rfl) ⟨9140156, by rfl⟩ : syracuseStep 12186875 = 18280313) B18280313
theorem B8124583 : Blo 2139435 8124583 := bstep (se 1 (by rfl) ⟨6093437, by rfl⟩ : syracuseStep 8124583 = 12186875) B12186875
theorem B10832777 : Blo 2139435 10832777 := bstep (se 2 (by rfl) ⟨4062291, by rfl⟩ : syracuseStep 10832777 = 8124583) B8124583
theorem B7221851 : Blo 2139435 7221851 := bstep (se 1 (by rfl) ⟨5416388, by rfl⟩ : syracuseStep 7221851 = 10832777) B10832777
theorem B4814567 : Blo 2139435 4814567 := bstep (se 1 (by rfl) ⟨3610925, by rfl⟩ : syracuseStep 4814567 = 7221851) B7221851
theorem B3209711 : Blo 2139435 3209711 := bstep (se 1 (by rfl) ⟨2407283, by rfl⟩ : syracuseStep 3209711 = 4814567) B4814567
theorem B2139807 : Blo 2139435 2139807 := bstep (se 1 (by rfl) ⟨1604855, by rfl⟩ : syracuseStep 2139807 = 3209711) B3209711
theorem B3209717 : Blo 2139435 3209717 := bbase (se 5 (by rfl) ⟨150455, by rfl⟩ : syracuseStep 3209717 = 300911) (by norm_num)
theorem B2139811 : Blo 2139435 2139811 := bstep (se 1 (by rfl) ⟨1604858, by rfl⟩ : syracuseStep 2139811 = 3209717) B3209717
theorem B6093461 : Blo 2139435 6093461 := bbase (se 6 (by rfl) ⟨142815, by rfl⟩ : syracuseStep 6093461 = 285631) (by norm_num)
theorem B4062307 : Blo 2139435 4062307 := bstep (se 1 (by rfl) ⟨3046730, by rfl⟩ : syracuseStep 4062307 = 6093461) B6093461
theorem B5416409 : Blo 2139435 5416409 := bstep (se 2 (by rfl) ⟨2031153, by rfl⟩ : syracuseStep 5416409 = 4062307) B4062307
theorem B3610939 : Blo 2139435 3610939 := bstep (se 1 (by rfl) ⟨2708204, by rfl⟩ : syracuseStep 3610939 = 5416409) B5416409
theorem B4814585 : Blo 2139435 4814585 := bstep (se 2 (by rfl) ⟨1805469, by rfl⟩ : syracuseStep 4814585 = 3610939) B3610939
theorem B3209723 : Blo 2139435 3209723 := bstep (se 1 (by rfl) ⟨2407292, by rfl⟩ : syracuseStep 3209723 = 4814585) B4814585
theorem B2139815 : Blo 2139435 2139815 := bstep (se 1 (by rfl) ⟨1604861, by rfl⟩ : syracuseStep 2139815 = 3209723) B3209723
theorem B2407297 : Blo 2139435 2407297 := bbase (se 2 (by rfl) ⟨902736, by rfl⟩ : syracuseStep 2407297 = 1805473) (by norm_num)
theorem B3209729 : Blo 2139435 3209729 := bstep (se 2 (by rfl) ⟨1203648, by rfl⟩ : syracuseStep 3209729 = 2407297) B2407297
theorem B2139819 : Blo 2139435 2139819 := bstep (se 1 (by rfl) ⟨1604864, by rfl⟩ : syracuseStep 2139819 = 3209729) B3209729
theorem B5416429 : Blo 2139435 5416429 := bbase (se 3 (by rfl) ⟨1015580, by rfl⟩ : syracuseStep 5416429 = 2031161) (by norm_num)
theorem B7221905 : Blo 2139435 7221905 := bstep (se 2 (by rfl) ⟨2708214, by rfl⟩ : syracuseStep 7221905 = 5416429) B5416429
theorem B4814603 : Blo 2139435 4814603 := bstep (se 1 (by rfl) ⟨3610952, by rfl⟩ : syracuseStep 4814603 = 7221905) B7221905
theorem B3209735 : Blo 2139435 3209735 := bstep (se 1 (by rfl) ⟨2407301, by rfl⟩ : syracuseStep 3209735 = 4814603) B4814603
theorem B2139823 : Blo 2139435 2139823 := bstep (se 1 (by rfl) ⟨1604867, by rfl⟩ : syracuseStep 2139823 = 3209735) B3209735
theorem B3209741 : Blo 2139435 3209741 := bbase (se 3 (by rfl) ⟨601826, by rfl⟩ : syracuseStep 3209741 = 1203653) (by norm_num)
theorem B2139827 : Blo 2139435 2139827 := bstep (se 1 (by rfl) ⟨1604870, by rfl⟩ : syracuseStep 2139827 = 3209741) B3209741
theorem B4814621 : Blo 2139435 4814621 := bbase (se 3 (by rfl) ⟨902741, by rfl⟩ : syracuseStep 4814621 = 1805483) (by norm_num)
theorem B3209747 : Blo 2139435 3209747 := bstep (se 1 (by rfl) ⟨2407310, by rfl⟩ : syracuseStep 3209747 = 4814621) B4814621
theorem B2139831 : Blo 2139435 2139831 := bstep (se 1 (by rfl) ⟨1604873, by rfl⟩ : syracuseStep 2139831 = 3209747) B3209747
theorem B3610973 : Blo 2139435 3610973 := bbase (se 3 (by rfl) ⟨677057, by rfl⟩ : syracuseStep 3610973 = 1354115) (by norm_num)
theorem B2407315 : Blo 2139435 2407315 := bstep (se 1 (by rfl) ⟨1805486, by rfl⟩ : syracuseStep 2407315 = 3610973) B3610973
theorem B3209753 : Blo 2139435 3209753 := bstep (se 2 (by rfl) ⟨1203657, by rfl⟩ : syracuseStep 3209753 = 2407315) B2407315
theorem B2139835 : Blo 2139435 2139835 := bstep (se 1 (by rfl) ⟨1604876, by rfl⟩ : syracuseStep 2139835 = 3209753) B3209753
theorem B9140293 : Blo 2139435 9140293 := bbase (se 4 (by rfl) ⟨856902, by rfl⟩ : syracuseStep 9140293 = 1713805) (by norm_num)
theorem B12187057 : Blo 2139435 12187057 := bstep (se 2 (by rfl) ⟨4570146, by rfl⟩ : syracuseStep 12187057 = 9140293) B9140293
theorem B16249409 : Blo 2139435 16249409 := bstep (se 2 (by rfl) ⟨6093528, by rfl⟩ : syracuseStep 16249409 = 12187057) B12187057
theorem B10832939 : Blo 2139435 10832939 := bstep (se 1 (by rfl) ⟨8124704, by rfl⟩ : syracuseStep 10832939 = 16249409) B16249409
theorem B7221959 : Blo 2139435 7221959 := bstep (se 1 (by rfl) ⟨5416469, by rfl⟩ : syracuseStep 7221959 = 10832939) B10832939
theorem B4814639 : Blo 2139435 4814639 := bstep (se 1 (by rfl) ⟨3610979, by rfl⟩ : syracuseStep 4814639 = 7221959) B7221959
theorem B3209759 : Blo 2139435 3209759 := bstep (se 1 (by rfl) ⟨2407319, by rfl⟩ : syracuseStep 3209759 = 4814639) B4814639
theorem B2139839 : Blo 2139435 2139839 := bstep (se 1 (by rfl) ⟨1604879, by rfl⟩ : syracuseStep 2139839 = 3209759) B3209759
theorem B3209765 : Blo 2139435 3209765 := bbase (se 4 (by rfl) ⟨300915, by rfl⟩ : syracuseStep 3209765 = 601831) (by norm_num)
theorem B2139843 : Blo 2139435 2139843 := bstep (se 1 (by rfl) ⟨1604882, by rfl⟩ : syracuseStep 2139843 = 3209765) B3209765
theorem B2708245 : Blo 2139435 2708245 := bbase (se 6 (by rfl) ⟨63474, by rfl⟩ : syracuseStep 2708245 = 126949) (by norm_num)
theorem B3610993 : Blo 2139435 3610993 := bstep (se 2 (by rfl) ⟨1354122, by rfl⟩ : syracuseStep 3610993 = 2708245) B2708245
theorem B4814657 : Blo 2139435 4814657 := bstep (se 2 (by rfl) ⟨1805496, by rfl⟩ : syracuseStep 4814657 = 3610993) B3610993
theorem B3209771 : Blo 2139435 3209771 := bstep (se 1 (by rfl) ⟨2407328, by rfl⟩ : syracuseStep 3209771 = 4814657) B4814657
theorem B2139847 : Blo 2139435 2139847 := bstep (se 1 (by rfl) ⟨1604885, by rfl⟩ : syracuseStep 2139847 = 3209771) B3209771
theorem B2407333 : Blo 2139435 2407333 := bbase (se 4 (by rfl) ⟨225687, by rfl⟩ : syracuseStep 2407333 = 451375) (by norm_num)
theorem B3209777 : Blo 2139435 3209777 := bstep (se 2 (by rfl) ⟨1203666, by rfl⟩ : syracuseStep 3209777 = 2407333) B2407333
theorem B2139851 : Blo 2139435 2139851 := bstep (se 1 (by rfl) ⟨1604888, by rfl⟩ : syracuseStep 2139851 = 3209777) B3209777
theorem B5490413 : Blo 2139435 5490413 := bbase (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) (by norm_num)
theorem B3660275 : Blo 2139435 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B9760733 : Blo 2139435 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B6507155 : Blo 2139435 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B4338103 : Blo 2139435 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B5784137 : Blo 2139435 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B3856091 : Blo 2139435 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B10282909 : Blo 2139435 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B13710545 : Blo 2139435 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B9140363 : Blo 2139435 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B6093575 : Blo 2139435 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B4062383 : Blo 2139435 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B2708255 : Blo 2139435 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B7222013 : Blo 2139435 7222013 := bstep (se 3 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 7222013 = 2708255) B2708255
theorem B4814675 : Blo 2139435 4814675 := bstep (se 1 (by rfl) ⟨3611006, by rfl⟩ : syracuseStep 4814675 = 7222013) B7222013
theorem B3209783 : Blo 2139435 3209783 := bstep (se 1 (by rfl) ⟨2407337, by rfl⟩ : syracuseStep 3209783 = 4814675) B4814675
theorem B2139855 : Blo 2139435 2139855 := bstep (se 1 (by rfl) ⟨1604891, by rfl⟩ : syracuseStep 2139855 = 3209783) B3209783
theorem B3209789 : Blo 2139435 3209789 := bbase (se 3 (by rfl) ⟨601835, by rfl⟩ : syracuseStep 3209789 = 1203671) (by norm_num)
theorem B2139859 : Blo 2139435 2139859 := bstep (se 1 (by rfl) ⟨1604894, by rfl⟩ : syracuseStep 2139859 = 3209789) B3209789
theorem B4814693 : Blo 2139435 4814693 := bbase (se 4 (by rfl) ⟨451377, by rfl⟩ : syracuseStep 4814693 = 902755) (by norm_num)
theorem B3209795 : Blo 2139435 3209795 := bstep (se 1 (by rfl) ⟨2407346, by rfl⟩ : syracuseStep 3209795 = 4814693) B4814693
theorem B2139863 : Blo 2139435 2139863 := bstep (se 1 (by rfl) ⟨1604897, by rfl⟩ : syracuseStep 2139863 = 3209795) B3209795
theorem B5416541 : Blo 2139435 5416541 := bbase (se 3 (by rfl) ⟨1015601, by rfl⟩ : syracuseStep 5416541 = 2031203) (by norm_num)
theorem B3611027 : Blo 2139435 3611027 := bstep (se 1 (by rfl) ⟨2708270, by rfl⟩ : syracuseStep 3611027 = 5416541) B5416541
theorem B2407351 : Blo 2139435 2407351 := bstep (se 1 (by rfl) ⟨1805513, by rfl⟩ : syracuseStep 2407351 = 3611027) B3611027
theorem B3209801 : Blo 2139435 3209801 := bstep (se 2 (by rfl) ⟨1203675, by rfl⟩ : syracuseStep 3209801 = 2407351) B2407351
theorem B2139867 : Blo 2139435 2139867 := bstep (se 1 (by rfl) ⟨1604900, by rfl⟩ : syracuseStep 2139867 = 3209801) B3209801
theorem B4062413 : Blo 2139435 4062413 := bbase (se 3 (by rfl) ⟨761702, by rfl⟩ : syracuseStep 4062413 = 1523405) (by norm_num)
theorem B10833101 : Blo 2139435 10833101 := bstep (se 3 (by rfl) ⟨2031206, by rfl⟩ : syracuseStep 10833101 = 4062413) B4062413
theorem B7222067 : Blo 2139435 7222067 := bstep (se 1 (by rfl) ⟨5416550, by rfl⟩ : syracuseStep 7222067 = 10833101) B10833101
theorem B4814711 : Blo 2139435 4814711 := bstep (se 1 (by rfl) ⟨3611033, by rfl⟩ : syracuseStep 4814711 = 7222067) B7222067
theorem B3209807 : Blo 2139435 3209807 := bstep (se 1 (by rfl) ⟨2407355, by rfl⟩ : syracuseStep 3209807 = 4814711) B4814711
theorem B2139871 : Blo 2139435 2139871 := bstep (se 1 (by rfl) ⟨1604903, by rfl⟩ : syracuseStep 2139871 = 3209807) B3209807
theorem B3209813 : Blo 2139435 3209813 := bbase (se 8 (by rfl) ⟨18807, by rfl⟩ : syracuseStep 3209813 = 37615) (by norm_num)
theorem B2139875 : Blo 2139435 2139875 := bstep (se 1 (by rfl) ⟨1604906, by rfl⟩ : syracuseStep 2139875 = 3209813) B3209813
theorem B6855349 : Blo 2139435 6855349 := bbase (se 5 (by rfl) ⟨321344, by rfl⟩ : syracuseStep 6855349 = 642689) (by norm_num)
theorem B9140465 : Blo 2139435 9140465 := bstep (se 2 (by rfl) ⟨3427674, by rfl⟩ : syracuseStep 9140465 = 6855349) B6855349
theorem B6093643 : Blo 2139435 6093643 := bstep (se 1 (by rfl) ⟨4570232, by rfl⟩ : syracuseStep 6093643 = 9140465) B9140465
theorem B8124857 : Blo 2139435 8124857 := bstep (se 2 (by rfl) ⟨3046821, by rfl⟩ : syracuseStep 8124857 = 6093643) B6093643
theorem B5416571 : Blo 2139435 5416571 := bstep (se 1 (by rfl) ⟨4062428, by rfl⟩ : syracuseStep 5416571 = 8124857) B8124857
theorem B3611047 : Blo 2139435 3611047 := bstep (se 1 (by rfl) ⟨2708285, by rfl⟩ : syracuseStep 3611047 = 5416571) B5416571
theorem B4814729 : Blo 2139435 4814729 := bstep (se 2 (by rfl) ⟨1805523, by rfl⟩ : syracuseStep 4814729 = 3611047) B3611047
theorem B3209819 : Blo 2139435 3209819 := bstep (se 1 (by rfl) ⟨2407364, by rfl⟩ : syracuseStep 3209819 = 4814729) B4814729
theorem B2139879 : Blo 2139435 2139879 := bstep (se 1 (by rfl) ⟨1604909, by rfl⟩ : syracuseStep 2139879 = 3209819) B3209819
theorem B2407369 : Blo 2139435 2407369 := bbase (se 2 (by rfl) ⟨902763, by rfl⟩ : syracuseStep 2407369 = 1805527) (by norm_num)
theorem B3209825 : Blo 2139435 3209825 := bstep (se 2 (by rfl) ⟨1203684, by rfl⟩ : syracuseStep 3209825 = 2407369) B2407369
theorem B2139883 : Blo 2139435 2139883 := bstep (se 1 (by rfl) ⟨1604912, by rfl⟩ : syracuseStep 2139883 = 3209825) B3209825
theorem B13897813 : Blo 2139435 13897813 := bbase (se 8 (by rfl) ⟨81432, by rfl⟩ : syracuseStep 13897813 = 162865) (by norm_num)
theorem B18530417 : Blo 2139435 18530417 := bstep (se 2 (by rfl) ⟨6948906, by rfl⟩ : syracuseStep 18530417 = 13897813) B13897813
theorem B49414445 : Blo 2139435 49414445 := bstep (se 3 (by rfl) ⟨9265208, by rfl⟩ : syracuseStep 49414445 = 18530417) B18530417
theorem B32942963 : Blo 2139435 32942963 := bstep (se 1 (by rfl) ⟨24707222, by rfl⟩ : syracuseStep 32942963 = 49414445) B49414445
theorem B21961975 : Blo 2139435 21961975 := bstep (se 1 (by rfl) ⟨16471481, by rfl⟩ : syracuseStep 21961975 = 32942963) B32942963
theorem B29282633 : Blo 2139435 29282633 := bstep (se 2 (by rfl) ⟨10980987, by rfl⟩ : syracuseStep 29282633 = 21961975) B21961975
theorem B19521755 : Blo 2139435 19521755 := bstep (se 1 (by rfl) ⟨14641316, by rfl⟩ : syracuseStep 19521755 = 29282633) B29282633
theorem B13014503 : Blo 2139435 13014503 := bstep (se 1 (by rfl) ⟨9760877, by rfl⟩ : syracuseStep 13014503 = 19521755) B19521755
theorem B8676335 : Blo 2139435 8676335 := bstep (se 1 (by rfl) ⟨6507251, by rfl⟩ : syracuseStep 8676335 = 13014503) B13014503
theorem B5784223 : Blo 2139435 5784223 := bstep (se 1 (by rfl) ⟨4338167, by rfl⟩ : syracuseStep 5784223 = 8676335) B8676335
theorem B7712297 : Blo 2139435 7712297 := bstep (se 2 (by rfl) ⟨2892111, by rfl⟩ : syracuseStep 7712297 = 5784223) B5784223
theorem B5141531 : Blo 2139435 5141531 := bstep (se 1 (by rfl) ⟨3856148, by rfl⟩ : syracuseStep 5141531 = 7712297) B7712297
theorem B3427687 : Blo 2139435 3427687 := bstep (se 1 (by rfl) ⟨2570765, by rfl⟩ : syracuseStep 3427687 = 5141531) B5141531
theorem B18280997 : Blo 2139435 18280997 := bstep (se 4 (by rfl) ⟨1713843, by rfl⟩ : syracuseStep 18280997 = 3427687) B3427687
theorem B12187331 : Blo 2139435 12187331 := bstep (se 1 (by rfl) ⟨9140498, by rfl⟩ : syracuseStep 12187331 = 18280997) B18280997
theorem B8124887 : Blo 2139435 8124887 := bstep (se 1 (by rfl) ⟨6093665, by rfl⟩ : syracuseStep 8124887 = 12187331) B12187331
theorem B5416591 : Blo 2139435 5416591 := bstep (se 1 (by rfl) ⟨4062443, by rfl⟩ : syracuseStep 5416591 = 8124887) B8124887
theorem B7222121 : Blo 2139435 7222121 := bstep (se 2 (by rfl) ⟨2708295, by rfl⟩ : syracuseStep 7222121 = 5416591) B5416591
theorem B4814747 : Blo 2139435 4814747 := bstep (se 1 (by rfl) ⟨3611060, by rfl⟩ : syracuseStep 4814747 = 7222121) B7222121
theorem B3209831 : Blo 2139435 3209831 := bstep (se 1 (by rfl) ⟨2407373, by rfl⟩ : syracuseStep 3209831 = 4814747) B4814747
theorem B2139887 : Blo 2139435 2139887 := bstep (se 1 (by rfl) ⟨1604915, by rfl⟩ : syracuseStep 2139887 = 3209831) B3209831
theorem B3209837 : Blo 2139435 3209837 := bbase (se 3 (by rfl) ⟨601844, by rfl⟩ : syracuseStep 3209837 = 1203689) (by norm_num)
theorem B2139891 : Blo 2139435 2139891 := bstep (se 1 (by rfl) ⟨1604918, by rfl⟩ : syracuseStep 2139891 = 3209837) B3209837
theorem B4814765 : Blo 2139435 4814765 := bbase (se 3 (by rfl) ⟨902768, by rfl⟩ : syracuseStep 4814765 = 1805537) (by norm_num)
theorem B3209843 : Blo 2139435 3209843 := bstep (se 1 (by rfl) ⟨2407382, by rfl⟩ : syracuseStep 3209843 = 4814765) B4814765
theorem B2139895 : Blo 2139435 2139895 := bstep (se 1 (by rfl) ⟨1604921, by rfl⟩ : syracuseStep 2139895 = 3209843) B3209843
theorem B6093701 : Blo 2139435 6093701 := bbase (se 4 (by rfl) ⟨571284, by rfl⟩ : syracuseStep 6093701 = 1142569) (by norm_num)
theorem B4062467 : Blo 2139435 4062467 := bstep (se 1 (by rfl) ⟨3046850, by rfl⟩ : syracuseStep 4062467 = 6093701) B6093701
theorem B2708311 : Blo 2139435 2708311 := bstep (se 1 (by rfl) ⟨2031233, by rfl⟩ : syracuseStep 2708311 = 4062467) B4062467
theorem B3611081 : Blo 2139435 3611081 := bstep (se 2 (by rfl) ⟨1354155, by rfl⟩ : syracuseStep 3611081 = 2708311) B2708311
theorem B2407387 : Blo 2139435 2407387 := bstep (se 1 (by rfl) ⟨1805540, by rfl⟩ : syracuseStep 2407387 = 3611081) B3611081
theorem B3209849 : Blo 2139435 3209849 := bstep (se 2 (by rfl) ⟨1203693, by rfl⟩ : syracuseStep 3209849 = 2407387) B2407387
theorem B2139899 : Blo 2139435 2139899 := bstep (se 1 (by rfl) ⟨1604924, by rfl⟩ : syracuseStep 2139899 = 3209849) B3209849
theorem B9760949 : Blo 2139435 9760949 := bbase (se 5 (by rfl) ⟨457544, by rfl⟩ : syracuseStep 9760949 = 915089) (by norm_num)
theorem B6507299 : Blo 2139435 6507299 := bstep (se 1 (by rfl) ⟨4880474, by rfl⟩ : syracuseStep 6507299 = 9760949) B9760949
theorem B4338199 : Blo 2139435 4338199 := bstep (se 1 (by rfl) ⟨3253649, by rfl⟩ : syracuseStep 4338199 = 6507299) B6507299
theorem B5784265 : Blo 2139435 5784265 := bstep (se 2 (by rfl) ⟨2169099, by rfl⟩ : syracuseStep 5784265 = 4338199) B4338199
theorem B7712353 : Blo 2139435 7712353 := bstep (se 2 (by rfl) ⟨2892132, by rfl⟩ : syracuseStep 7712353 = 5784265) B5784265
theorem B41132549 : Blo 2139435 41132549 := bstep (se 4 (by rfl) ⟨3856176, by rfl⟩ : syracuseStep 41132549 = 7712353) B7712353
theorem B27421699 : Blo 2139435 27421699 := bstep (se 1 (by rfl) ⟨20566274, by rfl⟩ : syracuseStep 27421699 = 41132549) B41132549
theorem B36562265 : Blo 2139435 36562265 := bstep (se 2 (by rfl) ⟨13710849, by rfl⟩ : syracuseStep 36562265 = 27421699) B27421699
theorem B24374843 : Blo 2139435 24374843 := bstep (se 1 (by rfl) ⟨18281132, by rfl⟩ : syracuseStep 24374843 = 36562265) B36562265
theorem B16249895 : Blo 2139435 16249895 := bstep (se 1 (by rfl) ⟨12187421, by rfl⟩ : syracuseStep 16249895 = 24374843) B24374843
theorem B10833263 : Blo 2139435 10833263 := bstep (se 1 (by rfl) ⟨8124947, by rfl⟩ : syracuseStep 10833263 = 16249895) B16249895
theorem B7222175 : Blo 2139435 7222175 := bstep (se 1 (by rfl) ⟨5416631, by rfl⟩ : syracuseStep 7222175 = 10833263) B10833263
theorem B4814783 : Blo 2139435 4814783 := bstep (se 1 (by rfl) ⟨3611087, by rfl⟩ : syracuseStep 4814783 = 7222175) B7222175
theorem B3209855 : Blo 2139435 3209855 := bstep (se 1 (by rfl) ⟨2407391, by rfl⟩ : syracuseStep 3209855 = 4814783) B4814783
theorem B2139903 : Blo 2139435 2139903 := bstep (se 1 (by rfl) ⟨1604927, by rfl⟩ : syracuseStep 2139903 = 3209855) B3209855
theorem B3209861 : Blo 2139435 3209861 := bbase (se 4 (by rfl) ⟨300924, by rfl⟩ : syracuseStep 3209861 = 601849) (by norm_num)
theorem B2139907 : Blo 2139435 2139907 := bstep (se 1 (by rfl) ⟨1604930, by rfl⟩ : syracuseStep 2139907 = 3209861) B3209861
theorem B3611101 : Blo 2139435 3611101 := bbase (se 3 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 3611101 = 1354163) (by norm_num)
theorem B4814801 : Blo 2139435 4814801 := bstep (se 2 (by rfl) ⟨1805550, by rfl⟩ : syracuseStep 4814801 = 3611101) B3611101
theorem B3209867 : Blo 2139435 3209867 := bstep (se 1 (by rfl) ⟨2407400, by rfl⟩ : syracuseStep 3209867 = 4814801) B4814801
theorem B2139911 : Blo 2139435 2139911 := bstep (se 1 (by rfl) ⟨1604933, by rfl⟩ : syracuseStep 2139911 = 3209867) B3209867
theorem B2407405 : Blo 2139435 2407405 := bbase (se 3 (by rfl) ⟨451388, by rfl⟩ : syracuseStep 2407405 = 902777) (by norm_num)
theorem B3209873 : Blo 2139435 3209873 := bstep (se 2 (by rfl) ⟨1203702, by rfl⟩ : syracuseStep 3209873 = 2407405) B2407405
theorem B2139915 : Blo 2139435 2139915 := bstep (se 1 (by rfl) ⟨1604936, by rfl⟩ : syracuseStep 2139915 = 3209873) B3209873
theorem B7222229 : Blo 2139435 7222229 := bbase (se 7 (by rfl) ⟨84635, by rfl⟩ : syracuseStep 7222229 = 169271) (by norm_num)
theorem B4814819 : Blo 2139435 4814819 := bstep (se 1 (by rfl) ⟨3611114, by rfl⟩ : syracuseStep 4814819 = 7222229) B7222229
theorem B3209879 : Blo 2139435 3209879 := bstep (se 1 (by rfl) ⟨2407409, by rfl⟩ : syracuseStep 3209879 = 4814819) B4814819
theorem B2139919 : Blo 2139435 2139919 := bstep (se 1 (by rfl) ⟨1604939, by rfl⟩ : syracuseStep 2139919 = 3209879) B3209879
theorem B3209885 : Blo 2139435 3209885 := bbase (se 3 (by rfl) ⟨601853, by rfl⟩ : syracuseStep 3209885 = 1203707) (by norm_num)
theorem B2139923 : Blo 2139435 2139923 := bstep (se 1 (by rfl) ⟨1604942, by rfl⟩ : syracuseStep 2139923 = 3209885) B3209885
theorem B4814837 : Blo 2139435 4814837 := bbase (se 5 (by rfl) ⟨225695, by rfl⟩ : syracuseStep 4814837 = 451391) (by norm_num)
theorem B3209891 : Blo 2139435 3209891 := bstep (se 1 (by rfl) ⟨2407418, by rfl⟩ : syracuseStep 3209891 = 4814837) B4814837
theorem B2139927 : Blo 2139435 2139927 := bstep (se 1 (by rfl) ⟨1604945, by rfl⟩ : syracuseStep 2139927 = 3209891) B3209891
theorem B6686165 : Blo 2139435 6686165 := bbase (se 7 (by rfl) ⟨78353, by rfl⟩ : syracuseStep 6686165 = 156707) (by norm_num)
theorem B4457443 : Blo 2139435 4457443 := bstep (se 1 (by rfl) ⟨3343082, by rfl⟩ : syracuseStep 4457443 = 6686165) B6686165
theorem B5943257 : Blo 2139435 5943257 := bstep (se 2 (by rfl) ⟨2228721, by rfl⟩ : syracuseStep 5943257 = 4457443) B4457443
theorem B3962171 : Blo 2139435 3962171 := bstep (se 1 (by rfl) ⟨2971628, by rfl⟩ : syracuseStep 3962171 = 5943257) B5943257
theorem B2641447 : Blo 2139435 2641447 := bstep (se 1 (by rfl) ⟨1981085, by rfl⟩ : syracuseStep 2641447 = 3962171) B3962171
theorem B3521929 : Blo 2139435 3521929 := bstep (se 2 (by rfl) ⟨1320723, by rfl⟩ : syracuseStep 3521929 = 2641447) B2641447
theorem B4695905 : Blo 2139435 4695905 := bstep (se 2 (by rfl) ⟨1760964, by rfl⟩ : syracuseStep 4695905 = 3521929) B3521929
theorem B3130603 : Blo 2139435 3130603 := bstep (se 1 (by rfl) ⟨2347952, by rfl⟩ : syracuseStep 3130603 = 4695905) B4695905
theorem B16696549 : Blo 2139435 16696549 := bstep (se 4 (by rfl) ⟨1565301, by rfl⟩ : syracuseStep 16696549 = 3130603) B3130603
theorem B89048261 : Blo 2139435 89048261 := bstep (se 4 (by rfl) ⟨8348274, by rfl⟩ : syracuseStep 89048261 = 16696549) B16696549
theorem B59365507 : Blo 2139435 59365507 := bstep (se 1 (by rfl) ⟨44524130, by rfl⟩ : syracuseStep 59365507 = 89048261) B89048261
theorem B79154009 : Blo 2139435 79154009 := bstep (se 2 (by rfl) ⟨29682753, by rfl⟩ : syracuseStep 79154009 = 59365507) B59365507
theorem B52769339 : Blo 2139435 52769339 := bstep (se 1 (by rfl) ⟨39577004, by rfl⟩ : syracuseStep 52769339 = 79154009) B79154009
theorem B35179559 : Blo 2139435 35179559 := bstep (se 1 (by rfl) ⟨26384669, by rfl⟩ : syracuseStep 35179559 = 52769339) B52769339
theorem B23453039 : Blo 2139435 23453039 := bstep (se 1 (by rfl) ⟨17589779, by rfl⟩ : syracuseStep 23453039 = 35179559) B35179559
theorem B15635359 : Blo 2139435 15635359 := bstep (se 1 (by rfl) ⟨11726519, by rfl⟩ : syracuseStep 15635359 = 23453039) B23453039
theorem B20847145 : Blo 2139435 20847145 := bstep (se 2 (by rfl) ⟨7817679, by rfl⟩ : syracuseStep 20847145 = 15635359) B15635359
theorem B27796193 : Blo 2139435 27796193 := bstep (se 2 (by rfl) ⟨10423572, by rfl⟩ : syracuseStep 27796193 = 20847145) B20847145
theorem B18530795 : Blo 2139435 18530795 := bstep (se 1 (by rfl) ⟨13898096, by rfl⟩ : syracuseStep 18530795 = 27796193) B27796193
theorem B49415453 : Blo 2139435 49415453 := bstep (se 3 (by rfl) ⟨9265397, by rfl⟩ : syracuseStep 49415453 = 18530795) B18530795
theorem B32943635 : Blo 2139435 32943635 := bstep (se 1 (by rfl) ⟨24707726, by rfl⟩ : syracuseStep 32943635 = 49415453) B49415453
theorem B21962423 : Blo 2139435 21962423 := bstep (se 1 (by rfl) ⟨16471817, by rfl⟩ : syracuseStep 21962423 = 32943635) B32943635
theorem B14641615 : Blo 2139435 14641615 := bstep (se 1 (by rfl) ⟨10981211, by rfl⟩ : syracuseStep 14641615 = 21962423) B21962423
theorem B19522153 : Blo 2139435 19522153 := bstep (se 2 (by rfl) ⟨7320807, by rfl⟩ : syracuseStep 19522153 = 14641615) B14641615
theorem B104118149 : Blo 2139435 104118149 := bstep (se 4 (by rfl) ⟨9761076, by rfl⟩ : syracuseStep 104118149 = 19522153) B19522153
theorem B69412099 : Blo 2139435 69412099 := bstep (se 1 (by rfl) ⟨52059074, by rfl⟩ : syracuseStep 69412099 = 104118149) B104118149
theorem B92549465 : Blo 2139435 92549465 := bstep (se 2 (by rfl) ⟨34706049, by rfl⟩ : syracuseStep 92549465 = 69412099) B69412099
theorem B61699643 : Blo 2139435 61699643 := bstep (se 1 (by rfl) ⟨46274732, by rfl⟩ : syracuseStep 61699643 = 92549465) B92549465
theorem B41133095 : Blo 2139435 41133095 := bstep (se 1 (by rfl) ⟨30849821, by rfl⟩ : syracuseStep 41133095 = 61699643) B61699643
theorem B27422063 : Blo 2139435 27422063 := bstep (se 1 (by rfl) ⟨20566547, by rfl⟩ : syracuseStep 27422063 = 41133095) B41133095
theorem B18281375 : Blo 2139435 18281375 := bstep (se 1 (by rfl) ⟨13711031, by rfl⟩ : syracuseStep 18281375 = 27422063) B27422063
theorem B12187583 : Blo 2139435 12187583 := bstep (se 1 (by rfl) ⟨9140687, by rfl⟩ : syracuseStep 12187583 = 18281375) B18281375
theorem B8125055 : Blo 2139435 8125055 := bstep (se 1 (by rfl) ⟨6093791, by rfl⟩ : syracuseStep 8125055 = 12187583) B12187583
theorem B5416703 : Blo 2139435 5416703 := bstep (se 1 (by rfl) ⟨4062527, by rfl⟩ : syracuseStep 5416703 = 8125055) B8125055
theorem B3611135 : Blo 2139435 3611135 := bstep (se 1 (by rfl) ⟨2708351, by rfl⟩ : syracuseStep 3611135 = 5416703) B5416703
theorem B2407423 : Blo 2139435 2407423 := bstep (se 1 (by rfl) ⟨1805567, by rfl⟩ : syracuseStep 2407423 = 3611135) B3611135
theorem B3209897 : Blo 2139435 3209897 := bstep (se 2 (by rfl) ⟨1203711, by rfl⟩ : syracuseStep 3209897 = 2407423) B2407423
theorem B2139931 : Blo 2139435 2139931 := bstep (se 1 (by rfl) ⟨1604948, by rfl⟩ : syracuseStep 2139931 = 3209897) B3209897
theorem B3046901 : Blo 2139435 3046901 := bbase (se 5 (by rfl) ⟨142823, by rfl⟩ : syracuseStep 3046901 = 285647) (by norm_num)
theorem B8125069 : Blo 2139435 8125069 := bstep (se 3 (by rfl) ⟨1523450, by rfl⟩ : syracuseStep 8125069 = 3046901) B3046901
theorem B10833425 : Blo 2139435 10833425 := bstep (se 2 (by rfl) ⟨4062534, by rfl⟩ : syracuseStep 10833425 = 8125069) B8125069
theorem B7222283 : Blo 2139435 7222283 := bstep (se 1 (by rfl) ⟨5416712, by rfl⟩ : syracuseStep 7222283 = 10833425) B10833425
theorem B4814855 : Blo 2139435 4814855 := bstep (se 1 (by rfl) ⟨3611141, by rfl⟩ : syracuseStep 4814855 = 7222283) B7222283
theorem B3209903 : Blo 2139435 3209903 := bstep (se 1 (by rfl) ⟨2407427, by rfl⟩ : syracuseStep 3209903 = 4814855) B4814855
theorem B2139935 : Blo 2139435 2139935 := bstep (se 1 (by rfl) ⟨1604951, by rfl⟩ : syracuseStep 2139935 = 3209903) B3209903
theorem B3209909 : Blo 2139435 3209909 := bbase (se 5 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 3209909 = 300929) (by norm_num)
theorem B2139939 : Blo 2139435 2139939 := bstep (se 1 (by rfl) ⟨1604954, by rfl⟩ : syracuseStep 2139939 = 3209909) B3209909
theorem B5416733 : Blo 2139435 5416733 := bbase (se 3 (by rfl) ⟨1015637, by rfl⟩ : syracuseStep 5416733 = 2031275) (by norm_num)
theorem B3611155 : Blo 2139435 3611155 := bstep (se 1 (by rfl) ⟨2708366, by rfl⟩ : syracuseStep 3611155 = 5416733) B5416733
theorem B4814873 : Blo 2139435 4814873 := bstep (se 2 (by rfl) ⟨1805577, by rfl⟩ : syracuseStep 4814873 = 3611155) B3611155
theorem B3209915 : Blo 2139435 3209915 := bstep (se 1 (by rfl) ⟨2407436, by rfl⟩ : syracuseStep 3209915 = 4814873) B4814873
theorem B2139943 : Blo 2139435 2139943 := bstep (se 1 (by rfl) ⟨1604957, by rfl⟩ : syracuseStep 2139943 = 3209915) B3209915
theorem B2407441 : Blo 2139435 2407441 := bbase (se 2 (by rfl) ⟨902790, by rfl⟩ : syracuseStep 2407441 = 1805581) (by norm_num)
theorem B3209921 : Blo 2139435 3209921 := bstep (se 2 (by rfl) ⟨1203720, by rfl⟩ : syracuseStep 3209921 = 2407441) B2407441
theorem B2139947 : Blo 2139435 2139947 := bstep (se 1 (by rfl) ⟨1604960, by rfl⟩ : syracuseStep 2139947 = 3209921) B3209921
theorem B4062565 : Blo 2139435 4062565 := bbase (se 4 (by rfl) ⟨380865, by rfl⟩ : syracuseStep 4062565 = 761731) (by norm_num)
theorem B5416753 : Blo 2139435 5416753 := bstep (se 2 (by rfl) ⟨2031282, by rfl⟩ : syracuseStep 5416753 = 4062565) B4062565
theorem B7222337 : Blo 2139435 7222337 := bstep (se 2 (by rfl) ⟨2708376, by rfl⟩ : syracuseStep 7222337 = 5416753) B5416753
theorem B4814891 : Blo 2139435 4814891 := bstep (se 1 (by rfl) ⟨3611168, by rfl⟩ : syracuseStep 4814891 = 7222337) B7222337
theorem B3209927 : Blo 2139435 3209927 := bstep (se 1 (by rfl) ⟨2407445, by rfl⟩ : syracuseStep 3209927 = 4814891) B4814891
theorem B2139951 : Blo 2139435 2139951 := bstep (se 1 (by rfl) ⟨1604963, by rfl⟩ : syracuseStep 2139951 = 3209927) B3209927
theorem B3209933 : Blo 2139435 3209933 := bbase (se 3 (by rfl) ⟨601862, by rfl⟩ : syracuseStep 3209933 = 1203725) (by norm_num)
theorem B2139955 : Blo 2139435 2139955 := bstep (se 1 (by rfl) ⟨1604966, by rfl⟩ : syracuseStep 2139955 = 3209933) B3209933
theorem B4814909 : Blo 2139435 4814909 := bbase (se 3 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 4814909 = 1805591) (by norm_num)
theorem B3209939 : Blo 2139435 3209939 := bstep (se 1 (by rfl) ⟨2407454, by rfl⟩ : syracuseStep 3209939 = 4814909) B4814909
theorem B2139959 : Blo 2139435 2139959 := bstep (se 1 (by rfl) ⟨1604969, by rfl⟩ : syracuseStep 2139959 = 3209939) B3209939
theorem B3611189 : Blo 2139435 3611189 := bbase (se 5 (by rfl) ⟨169274, by rfl⟩ : syracuseStep 3611189 = 338549) (by norm_num)
theorem B2407459 : Blo 2139435 2407459 := bstep (se 1 (by rfl) ⟨1805594, by rfl⟩ : syracuseStep 2407459 = 3611189) B3611189
theorem B3209945 : Blo 2139435 3209945 := bstep (se 2 (by rfl) ⟨1203729, by rfl⟩ : syracuseStep 3209945 = 2407459) B2407459
theorem B2139963 : Blo 2139435 2139963 := bstep (se 1 (by rfl) ⟨1604972, by rfl⟩ : syracuseStep 2139963 = 3209945) B3209945
theorem B6093893 : Blo 2139435 6093893 := bbase (se 4 (by rfl) ⟨571302, by rfl⟩ : syracuseStep 6093893 = 1142605) (by norm_num)
theorem B16250381 : Blo 2139435 16250381 := bstep (se 3 (by rfl) ⟨3046946, by rfl⟩ : syracuseStep 16250381 = 6093893) B6093893
theorem B10833587 : Blo 2139435 10833587 := bstep (se 1 (by rfl) ⟨8125190, by rfl⟩ : syracuseStep 10833587 = 16250381) B16250381
theorem B7222391 : Blo 2139435 7222391 := bstep (se 1 (by rfl) ⟨5416793, by rfl⟩ : syracuseStep 7222391 = 10833587) B10833587
theorem B4814927 : Blo 2139435 4814927 := bstep (se 1 (by rfl) ⟨3611195, by rfl⟩ : syracuseStep 4814927 = 7222391) B7222391
theorem B3209951 : Blo 2139435 3209951 := bstep (se 1 (by rfl) ⟨2407463, by rfl⟩ : syracuseStep 3209951 = 4814927) B4814927
theorem B2139967 : Blo 2139435 2139967 := bstep (se 1 (by rfl) ⟨1604975, by rfl⟩ : syracuseStep 2139967 = 3209951) B3209951
theorem B3209957 : Blo 2139435 3209957 := bbase (se 4 (by rfl) ⟨300933, by rfl⟩ : syracuseStep 3209957 = 601867) (by norm_num)
theorem B2139971 : Blo 2139435 2139971 := bstep (se 1 (by rfl) ⟨1604978, by rfl⟩ : syracuseStep 2139971 = 3209957) B3209957
theorem B3427829 : Blo 2139435 3427829 := bbase (se 5 (by rfl) ⟨160679, by rfl⟩ : syracuseStep 3427829 = 321359) (by norm_num)
theorem B2285219 : Blo 2139435 2285219 := bstep (se 1 (by rfl) ⟨1713914, by rfl⟩ : syracuseStep 2285219 = 3427829) B3427829
theorem B6093917 : Blo 2139435 6093917 := bstep (se 3 (by rfl) ⟨1142609, by rfl⟩ : syracuseStep 6093917 = 2285219) B2285219
theorem B4062611 : Blo 2139435 4062611 := bstep (se 1 (by rfl) ⟨3046958, by rfl⟩ : syracuseStep 4062611 = 6093917) B6093917
theorem B2708407 : Blo 2139435 2708407 := bstep (se 1 (by rfl) ⟨2031305, by rfl⟩ : syracuseStep 2708407 = 4062611) B4062611
theorem B3611209 : Blo 2139435 3611209 := bstep (se 2 (by rfl) ⟨1354203, by rfl⟩ : syracuseStep 3611209 = 2708407) B2708407
theorem B4814945 : Blo 2139435 4814945 := bstep (se 2 (by rfl) ⟨1805604, by rfl⟩ : syracuseStep 4814945 = 3611209) B3611209
theorem B3209963 : Blo 2139435 3209963 := bstep (se 1 (by rfl) ⟨2407472, by rfl⟩ : syracuseStep 3209963 = 4814945) B4814945
theorem B2139975 : Blo 2139435 2139975 := bstep (se 1 (by rfl) ⟨1604981, by rfl⟩ : syracuseStep 2139975 = 3209963) B3209963
theorem B2407477 : Blo 2139435 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B3209969 : Blo 2139435 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B2139979 : Blo 2139435 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B2708417 : Blo 2139435 2708417 := bbase (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) (by norm_num)
theorem B7222445 : Blo 2139435 7222445 := bstep (se 3 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 7222445 = 2708417) B2708417
theorem B4814963 : Blo 2139435 4814963 := bstep (se 1 (by rfl) ⟨3611222, by rfl⟩ : syracuseStep 4814963 = 7222445) B7222445
theorem B3209975 : Blo 2139435 3209975 := bstep (se 1 (by rfl) ⟨2407481, by rfl⟩ : syracuseStep 3209975 = 4814963) B4814963
theorem B2139983 : Blo 2139435 2139983 := bstep (se 1 (by rfl) ⟨1604987, by rfl⟩ : syracuseStep 2139983 = 3209975) B3209975
theorem B3209981 : Blo 2139435 3209981 := bbase (se 3 (by rfl) ⟨601871, by rfl⟩ : syracuseStep 3209981 = 1203743) (by norm_num)
theorem B2139987 : Blo 2139435 2139987 := bstep (se 1 (by rfl) ⟨1604990, by rfl⟩ : syracuseStep 2139987 = 3209981) B3209981
theorem B4814981 : Blo 2139435 4814981 := bbase (se 4 (by rfl) ⟨451404, by rfl⟩ : syracuseStep 4814981 = 902809) (by norm_num)
theorem B3209987 : Blo 2139435 3209987 := bstep (se 1 (by rfl) ⟨2407490, by rfl⟩ : syracuseStep 3209987 = 4814981) B4814981
theorem B2139991 : Blo 2139435 2139991 := bstep (se 1 (by rfl) ⟨1604993, by rfl⟩ : syracuseStep 2139991 = 3209987) B3209987
theorem B3427861 : Blo 2139435 3427861 := bbase (se 6 (by rfl) ⟨80340, by rfl⟩ : syracuseStep 3427861 = 160681) (by norm_num)
theorem B4570481 : Blo 2139435 4570481 := bstep (se 2 (by rfl) ⟨1713930, by rfl⟩ : syracuseStep 4570481 = 3427861) B3427861
theorem B3046987 : Blo 2139435 3046987 := bstep (se 1 (by rfl) ⟨2285240, by rfl⟩ : syracuseStep 3046987 = 4570481) B4570481
theorem B4062649 : Blo 2139435 4062649 := bstep (se 2 (by rfl) ⟨1523493, by rfl⟩ : syracuseStep 4062649 = 3046987) B3046987
theorem B5416865 : Blo 2139435 5416865 := bstep (se 2 (by rfl) ⟨2031324, by rfl⟩ : syracuseStep 5416865 = 4062649) B4062649
theorem B3611243 : Blo 2139435 3611243 := bstep (se 1 (by rfl) ⟨2708432, by rfl⟩ : syracuseStep 3611243 = 5416865) B5416865
theorem B2407495 : Blo 2139435 2407495 := bstep (se 1 (by rfl) ⟨1805621, by rfl⟩ : syracuseStep 2407495 = 3611243) B3611243
theorem B3209993 : Blo 2139435 3209993 := bstep (se 2 (by rfl) ⟨1203747, by rfl⟩ : syracuseStep 3209993 = 2407495) B2407495
theorem B2139995 : Blo 2139435 2139995 := bstep (se 1 (by rfl) ⟨1604996, by rfl⟩ : syracuseStep 2139995 = 3209993) B3209993
theorem B10833749 : Blo 2139435 10833749 := bbase (se 9 (by rfl) ⟨31739, by rfl⟩ : syracuseStep 10833749 = 63479) (by norm_num)
theorem B7222499 : Blo 2139435 7222499 := bstep (se 1 (by rfl) ⟨5416874, by rfl⟩ : syracuseStep 7222499 = 10833749) B10833749
theorem B4814999 : Blo 2139435 4814999 := bstep (se 1 (by rfl) ⟨3611249, by rfl⟩ : syracuseStep 4814999 = 7222499) B7222499
theorem B3209999 : Blo 2139435 3209999 := bstep (se 1 (by rfl) ⟨2407499, by rfl⟩ : syracuseStep 3209999 = 4814999) B4814999
theorem B2139999 : Blo 2139435 2139999 := bstep (se 1 (by rfl) ⟨1604999, by rfl⟩ : syracuseStep 2139999 = 3209999) B3209999
theorem B3210005 : Blo 2139435 3210005 := bbase (se 6 (by rfl) ⟨75234, by rfl⟩ : syracuseStep 3210005 = 150469) (by norm_num)
theorem B2140003 : Blo 2139435 2140003 := bstep (se 1 (by rfl) ⟨1605002, by rfl⟩ : syracuseStep 2140003 = 3210005) B3210005
theorem B2169205 : Blo 2139435 2169205 := bbase (se 5 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 2169205 = 203363) (by norm_num)
theorem B46276373 : Blo 2139435 46276373 := bstep (se 6 (by rfl) ⟨1084602, by rfl⟩ : syracuseStep 46276373 = 2169205) B2169205
theorem B30850915 : Blo 2139435 30850915 := bstep (se 1 (by rfl) ⟨23138186, by rfl⟩ : syracuseStep 30850915 = 46276373) B46276373
theorem B41134553 : Blo 2139435 41134553 := bstep (se 2 (by rfl) ⟨15425457, by rfl⟩ : syracuseStep 41134553 = 30850915) B30850915
theorem B27423035 : Blo 2139435 27423035 := bstep (se 1 (by rfl) ⟨20567276, by rfl⟩ : syracuseStep 27423035 = 41134553) B41134553
theorem B18282023 : Blo 2139435 18282023 := bstep (se 1 (by rfl) ⟨13711517, by rfl⟩ : syracuseStep 18282023 = 27423035) B27423035
theorem B12188015 : Blo 2139435 12188015 := bstep (se 1 (by rfl) ⟨9141011, by rfl⟩ : syracuseStep 12188015 = 18282023) B18282023
theorem B8125343 : Blo 2139435 8125343 := bstep (se 1 (by rfl) ⟨6094007, by rfl⟩ : syracuseStep 8125343 = 12188015) B12188015
theorem B5416895 : Blo 2139435 5416895 := bstep (se 1 (by rfl) ⟨4062671, by rfl⟩ : syracuseStep 5416895 = 8125343) B8125343
theorem B3611263 : Blo 2139435 3611263 := bstep (se 1 (by rfl) ⟨2708447, by rfl⟩ : syracuseStep 3611263 = 5416895) B5416895
theorem B4815017 : Blo 2139435 4815017 := bstep (se 2 (by rfl) ⟨1805631, by rfl⟩ : syracuseStep 4815017 = 3611263) B3611263
theorem B3210011 : Blo 2139435 3210011 := bstep (se 1 (by rfl) ⟨2407508, by rfl⟩ : syracuseStep 3210011 = 4815017) B4815017
theorem B2140007 : Blo 2139435 2140007 := bstep (se 1 (by rfl) ⟨1605005, by rfl⟩ : syracuseStep 2140007 = 3210011) B3210011
theorem B2407513 : Blo 2139435 2407513 := bbase (se 2 (by rfl) ⟨902817, by rfl⟩ : syracuseStep 2407513 = 1805635) (by norm_num)
theorem B3210017 : Blo 2139435 3210017 := bstep (se 2 (by rfl) ⟨1203756, by rfl⟩ : syracuseStep 3210017 = 2407513) B2407513
theorem B2140011 : Blo 2139435 2140011 := bstep (se 1 (by rfl) ⟨1605008, by rfl⟩ : syracuseStep 2140011 = 3210017) B3210017
theorem B9265765 : Blo 2139435 9265765 := bbase (se 4 (by rfl) ⟨868665, by rfl⟩ : syracuseStep 9265765 = 1737331) (by norm_num)
theorem B12354353 : Blo 2139435 12354353 := bstep (se 2 (by rfl) ⟨4632882, by rfl⟩ : syracuseStep 12354353 = 9265765) B9265765
theorem B8236235 : Blo 2139435 8236235 := bstep (se 1 (by rfl) ⟨6177176, by rfl⟩ : syracuseStep 8236235 = 12354353) B12354353
theorem B5490823 : Blo 2139435 5490823 := bstep (se 1 (by rfl) ⟨4118117, by rfl⟩ : syracuseStep 5490823 = 8236235) B8236235
theorem B7321097 : Blo 2139435 7321097 := bstep (se 2 (by rfl) ⟨2745411, by rfl⟩ : syracuseStep 7321097 = 5490823) B5490823
theorem B4880731 : Blo 2139435 4880731 := bstep (se 1 (by rfl) ⟨3660548, by rfl⟩ : syracuseStep 4880731 = 7321097) B7321097
theorem B6507641 : Blo 2139435 6507641 := bstep (se 2 (by rfl) ⟨2440365, by rfl⟩ : syracuseStep 6507641 = 4880731) B4880731
theorem B17353709 : Blo 2139435 17353709 := bstep (se 3 (by rfl) ⟨3253820, by rfl⟩ : syracuseStep 17353709 = 6507641) B6507641
theorem B11569139 : Blo 2139435 11569139 := bstep (se 1 (by rfl) ⟨8676854, by rfl⟩ : syracuseStep 11569139 = 17353709) B17353709
theorem B7712759 : Blo 2139435 7712759 := bstep (se 1 (by rfl) ⟨5784569, by rfl⟩ : syracuseStep 7712759 = 11569139) B11569139
theorem B5141839 : Blo 2139435 5141839 := bstep (se 1 (by rfl) ⟨3856379, by rfl⟩ : syracuseStep 5141839 = 7712759) B7712759
theorem B6855785 : Blo 2139435 6855785 := bstep (se 2 (by rfl) ⟨2570919, by rfl⟩ : syracuseStep 6855785 = 5141839) B5141839
theorem B4570523 : Blo 2139435 4570523 := bstep (se 1 (by rfl) ⟨3427892, by rfl⟩ : syracuseStep 4570523 = 6855785) B6855785
theorem B3047015 : Blo 2139435 3047015 := bstep (se 1 (by rfl) ⟨2285261, by rfl⟩ : syracuseStep 3047015 = 4570523) B4570523
theorem B8125373 : Blo 2139435 8125373 := bstep (se 3 (by rfl) ⟨1523507, by rfl⟩ : syracuseStep 8125373 = 3047015) B3047015
theorem B5416915 : Blo 2139435 5416915 := bstep (se 1 (by rfl) ⟨4062686, by rfl⟩ : syracuseStep 5416915 = 8125373) B8125373
theorem B7222553 : Blo 2139435 7222553 := bstep (se 2 (by rfl) ⟨2708457, by rfl⟩ : syracuseStep 7222553 = 5416915) B5416915
theorem B4815035 : Blo 2139435 4815035 := bstep (se 1 (by rfl) ⟨3611276, by rfl⟩ : syracuseStep 4815035 = 7222553) B7222553
theorem B3210023 : Blo 2139435 3210023 := bstep (se 1 (by rfl) ⟨2407517, by rfl⟩ : syracuseStep 3210023 = 4815035) B4815035
theorem B2140015 : Blo 2139435 2140015 := bstep (se 1 (by rfl) ⟨1605011, by rfl⟩ : syracuseStep 2140015 = 3210023) B3210023
theorem B3210029 : Blo 2139435 3210029 := bbase (se 3 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 3210029 = 1203761) (by norm_num)
theorem B2140019 : Blo 2139435 2140019 := bstep (se 1 (by rfl) ⟨1605014, by rfl⟩ : syracuseStep 2140019 = 3210029) B3210029
theorem B4815053 : Blo 2139435 4815053 := bbase (se 3 (by rfl) ⟨902822, by rfl⟩ : syracuseStep 4815053 = 1805645) (by norm_num)
theorem B3210035 : Blo 2139435 3210035 := bstep (se 1 (by rfl) ⟨2407526, by rfl⟩ : syracuseStep 3210035 = 4815053) B4815053
theorem B2140023 : Blo 2139435 2140023 := bstep (se 1 (by rfl) ⟨1605017, by rfl⟩ : syracuseStep 2140023 = 3210035) B3210035
theorem B2708473 : Blo 2139435 2708473 := bbase (se 2 (by rfl) ⟨1015677, by rfl⟩ : syracuseStep 2708473 = 2031355) (by norm_num)
theorem B3611297 : Blo 2139435 3611297 := bstep (se 2 (by rfl) ⟨1354236, by rfl⟩ : syracuseStep 3611297 = 2708473) B2708473
theorem B2407531 : Blo 2139435 2407531 := bstep (se 1 (by rfl) ⟨1805648, by rfl⟩ : syracuseStep 2407531 = 3611297) B3611297
theorem B3210041 : Blo 2139435 3210041 := bstep (se 2 (by rfl) ⟨1203765, by rfl⟩ : syracuseStep 3210041 = 2407531) B2407531
theorem B2140027 : Blo 2139435 2140027 := bstep (se 1 (by rfl) ⟨1605020, by rfl⟩ : syracuseStep 2140027 = 3210041) B3210041
theorem B2507429 : Blo 2139435 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B6686477 : Blo 2139435 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B4457651 : Blo 2139435 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B11887069 : Blo 2139435 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B15849425 : Blo 2139435 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B10566283 : Blo 2139435 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B14088377 : Blo 2139435 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B37569005 : Blo 2139435 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B25046003 : Blo 2139435 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B16697335 : Blo 2139435 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B22263113 : Blo 2139435 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B14842075 : Blo 2139435 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B19789433 : Blo 2139435 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B13192955 : Blo 2139435 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B8795303 : Blo 2139435 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B5863535 : Blo 2139435 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B3909023 : Blo 2139435 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B2606015 : Blo 2139435 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B6949373 : Blo 2139435 6949373 := bstep (se 3 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 6949373 = 2606015) B2606015
theorem B18531661 : Blo 2139435 18531661 := bstep (se 3 (by rfl) ⟨3474686, by rfl⟩ : syracuseStep 18531661 = 6949373) B6949373
theorem B24708881 : Blo 2139435 24708881 := bstep (se 2 (by rfl) ⟨9265830, by rfl⟩ : syracuseStep 24708881 = 18531661) B18531661
theorem B16472587 : Blo 2139435 16472587 := bstep (se 1 (by rfl) ⟨12354440, by rfl⟩ : syracuseStep 16472587 = 24708881) B24708881
theorem B21963449 : Blo 2139435 21963449 := bstep (se 2 (by rfl) ⟨8236293, by rfl⟩ : syracuseStep 21963449 = 16472587) B16472587
theorem B14642299 : Blo 2139435 14642299 := bstep (se 1 (by rfl) ⟨10981724, by rfl⟩ : syracuseStep 14642299 = 21963449) B21963449
theorem B19523065 : Blo 2139435 19523065 := bstep (se 2 (by rfl) ⟨7321149, by rfl⟩ : syracuseStep 19523065 = 14642299) B14642299
theorem B26030753 : Blo 2139435 26030753 := bstep (se 2 (by rfl) ⟨9761532, by rfl⟩ : syracuseStep 26030753 = 19523065) B19523065
theorem B17353835 : Blo 2139435 17353835 := bstep (se 1 (by rfl) ⟨13015376, by rfl⟩ : syracuseStep 17353835 = 26030753) B26030753
theorem B11569223 : Blo 2139435 11569223 := bstep (se 1 (by rfl) ⟨8676917, by rfl⟩ : syracuseStep 11569223 = 17353835) B17353835
theorem B7712815 : Blo 2139435 7712815 := bstep (se 1 (by rfl) ⟨5784611, by rfl⟩ : syracuseStep 7712815 = 11569223) B11569223
theorem B10283753 : Blo 2139435 10283753 := bstep (se 2 (by rfl) ⟨3856407, by rfl⟩ : syracuseStep 10283753 = 7712815) B7712815
theorem B6855835 : Blo 2139435 6855835 := bstep (se 1 (by rfl) ⟨5141876, by rfl⟩ : syracuseStep 6855835 = 10283753) B10283753
theorem B9141113 : Blo 2139435 9141113 := bstep (se 2 (by rfl) ⟨3427917, by rfl⟩ : syracuseStep 9141113 = 6855835) B6855835
theorem B24376301 : Blo 2139435 24376301 := bstep (se 3 (by rfl) ⟨4570556, by rfl⟩ : syracuseStep 24376301 = 9141113) B9141113
theorem B16250867 : Blo 2139435 16250867 := bstep (se 1 (by rfl) ⟨12188150, by rfl⟩ : syracuseStep 16250867 = 24376301) B24376301
theorem B10833911 : Blo 2139435 10833911 := bstep (se 1 (by rfl) ⟨8125433, by rfl⟩ : syracuseStep 10833911 = 16250867) B16250867
theorem B7222607 : Blo 2139435 7222607 := bstep (se 1 (by rfl) ⟨5416955, by rfl⟩ : syracuseStep 7222607 = 10833911) B10833911
theorem B4815071 : Blo 2139435 4815071 := bstep (se 1 (by rfl) ⟨3611303, by rfl⟩ : syracuseStep 4815071 = 7222607) B7222607
theorem B3210047 : Blo 2139435 3210047 := bstep (se 1 (by rfl) ⟨2407535, by rfl⟩ : syracuseStep 3210047 = 4815071) B4815071
theorem B2140031 : Blo 2139435 2140031 := bstep (se 1 (by rfl) ⟨1605023, by rfl⟩ : syracuseStep 2140031 = 3210047) B3210047
theorem B3210053 : Blo 2139435 3210053 := bbase (se 4 (by rfl) ⟨300942, by rfl⟩ : syracuseStep 3210053 = 601885) (by norm_num)
theorem B2140035 : Blo 2139435 2140035 := bstep (se 1 (by rfl) ⟨1605026, by rfl⟩ : syracuseStep 2140035 = 3210053) B3210053
theorem B3611317 : Blo 2139435 3611317 := bbase (se 5 (by rfl) ⟨169280, by rfl⟩ : syracuseStep 3611317 = 338561) (by norm_num)
theorem B4815089 : Blo 2139435 4815089 := bstep (se 2 (by rfl) ⟨1805658, by rfl⟩ : syracuseStep 4815089 = 3611317) B3611317
theorem B3210059 : Blo 2139435 3210059 := bstep (se 1 (by rfl) ⟨2407544, by rfl⟩ : syracuseStep 3210059 = 4815089) B4815089
theorem B2140039 : Blo 2139435 2140039 := bstep (se 1 (by rfl) ⟨1605029, by rfl⟩ : syracuseStep 2140039 = 3210059) B3210059
theorem B2407549 : Blo 2139435 2407549 := bbase (se 3 (by rfl) ⟨451415, by rfl⟩ : syracuseStep 2407549 = 902831) (by norm_num)
theorem B3210065 : Blo 2139435 3210065 := bstep (se 2 (by rfl) ⟨1203774, by rfl⟩ : syracuseStep 3210065 = 2407549) B2407549
theorem B2140043 : Blo 2139435 2140043 := bstep (se 1 (by rfl) ⟨1605032, by rfl⟩ : syracuseStep 2140043 = 3210065) B3210065
theorem B7222661 : Blo 2139435 7222661 := bbase (se 4 (by rfl) ⟨677124, by rfl⟩ : syracuseStep 7222661 = 1354249) (by norm_num)
theorem B4815107 : Blo 2139435 4815107 := bstep (se 1 (by rfl) ⟨3611330, by rfl⟩ : syracuseStep 4815107 = 7222661) B7222661
theorem B3210071 : Blo 2139435 3210071 := bstep (se 1 (by rfl) ⟨2407553, by rfl⟩ : syracuseStep 3210071 = 4815107) B4815107
theorem B2140047 : Blo 2139435 2140047 := bstep (se 1 (by rfl) ⟨1605035, by rfl⟩ : syracuseStep 2140047 = 3210071) B3210071
theorem B3210077 : Blo 2139435 3210077 := bbase (se 3 (by rfl) ⟨601889, by rfl⟩ : syracuseStep 3210077 = 1203779) (by norm_num)
theorem B2140051 : Blo 2139435 2140051 := bstep (se 1 (by rfl) ⟨1605038, by rfl⟩ : syracuseStep 2140051 = 3210077) B3210077
theorem B4815125 : Blo 2139435 4815125 := bbase (se 6 (by rfl) ⟨112854, by rfl⟩ : syracuseStep 4815125 = 225709) (by norm_num)
theorem B3210083 : Blo 2139435 3210083 := bstep (se 1 (by rfl) ⟨2407562, by rfl⟩ : syracuseStep 3210083 = 4815125) B4815125
theorem B2140055 : Blo 2139435 2140055 := bstep (se 1 (by rfl) ⟨1605041, by rfl⟩ : syracuseStep 2140055 = 3210083) B3210083
theorem B8125541 : Blo 2139435 8125541 := bbase (se 4 (by rfl) ⟨761769, by rfl⟩ : syracuseStep 8125541 = 1523539) (by norm_num)
theorem B5417027 : Blo 2139435 5417027 := bstep (se 1 (by rfl) ⟨4062770, by rfl⟩ : syracuseStep 5417027 = 8125541) B8125541
theorem B3611351 : Blo 2139435 3611351 := bstep (se 1 (by rfl) ⟨2708513, by rfl⟩ : syracuseStep 3611351 = 5417027) B5417027
theorem B2407567 : Blo 2139435 2407567 := bstep (se 1 (by rfl) ⟨1805675, by rfl⟩ : syracuseStep 2407567 = 3611351) B3611351
theorem B3210089 : Blo 2139435 3210089 := bstep (se 2 (by rfl) ⟨1203783, by rfl⟩ : syracuseStep 3210089 = 2407567) B2407567
theorem B2140059 : Blo 2139435 2140059 := bstep (se 1 (by rfl) ⟨1605044, by rfl⟩ : syracuseStep 2140059 = 3210089) B3210089
theorem B2570977 : Blo 2139435 2570977 := bbase (se 2 (by rfl) ⟨964116, by rfl⟩ : syracuseStep 2570977 = 1928233) (by norm_num)
theorem B3427969 : Blo 2139435 3427969 := bstep (se 2 (by rfl) ⟨1285488, by rfl⟩ : syracuseStep 3427969 = 2570977) B2570977
theorem B4570625 : Blo 2139435 4570625 := bstep (se 2 (by rfl) ⟨1713984, by rfl⟩ : syracuseStep 4570625 = 3427969) B3427969
theorem B12188333 : Blo 2139435 12188333 := bstep (se 3 (by rfl) ⟨2285312, by rfl⟩ : syracuseStep 12188333 = 4570625) B4570625
theorem B8125555 : Blo 2139435 8125555 := bstep (se 1 (by rfl) ⟨6094166, by rfl⟩ : syracuseStep 8125555 = 12188333) B12188333
theorem B10834073 : Blo 2139435 10834073 := bstep (se 2 (by rfl) ⟨4062777, by rfl⟩ : syracuseStep 10834073 = 8125555) B8125555
theorem B7222715 : Blo 2139435 7222715 := bstep (se 1 (by rfl) ⟨5417036, by rfl⟩ : syracuseStep 7222715 = 10834073) B10834073
theorem B4815143 : Blo 2139435 4815143 := bstep (se 1 (by rfl) ⟨3611357, by rfl⟩ : syracuseStep 4815143 = 7222715) B7222715
theorem B3210095 : Blo 2139435 3210095 := bstep (se 1 (by rfl) ⟨2407571, by rfl⟩ : syracuseStep 3210095 = 4815143) B4815143
theorem B2140063 : Blo 2139435 2140063 := bstep (se 1 (by rfl) ⟨1605047, by rfl⟩ : syracuseStep 2140063 = 3210095) B3210095
theorem B3210101 : Blo 2139435 3210101 := bbase (se 5 (by rfl) ⟨150473, by rfl⟩ : syracuseStep 3210101 = 300947) (by norm_num)
theorem B2140067 : Blo 2139435 2140067 := bstep (se 1 (by rfl) ⟨1605050, by rfl⟩ : syracuseStep 2140067 = 3210101) B3210101
theorem B4880861 : Blo 2139435 4880861 := bbase (se 3 (by rfl) ⟨915161, by rfl⟩ : syracuseStep 4880861 = 1830323) (by norm_num)
theorem B3253907 : Blo 2139435 3253907 := bstep (se 1 (by rfl) ⟨2440430, by rfl⟩ : syracuseStep 3253907 = 4880861) B4880861
theorem B2169271 : Blo 2139435 2169271 := bstep (se 1 (by rfl) ⟨1626953, by rfl⟩ : syracuseStep 2169271 = 3253907) B3253907
theorem B2892361 : Blo 2139435 2892361 := bstep (se 2 (by rfl) ⟨1084635, by rfl⟩ : syracuseStep 2892361 = 2169271) B2169271
theorem B3856481 : Blo 2139435 3856481 := bstep (se 2 (by rfl) ⟨1446180, by rfl⟩ : syracuseStep 3856481 = 2892361) B2892361
theorem B2570987 : Blo 2139435 2570987 := bstep (se 1 (by rfl) ⟨1928240, by rfl⟩ : syracuseStep 2570987 = 3856481) B3856481
theorem B6855965 : Blo 2139435 6855965 := bstep (se 3 (by rfl) ⟨1285493, by rfl⟩ : syracuseStep 6855965 = 2570987) B2570987
theorem B4570643 : Blo 2139435 4570643 := bstep (se 1 (by rfl) ⟨3427982, by rfl⟩ : syracuseStep 4570643 = 6855965) B6855965
theorem B3047095 : Blo 2139435 3047095 := bstep (se 1 (by rfl) ⟨2285321, by rfl⟩ : syracuseStep 3047095 = 4570643) B4570643
theorem B4062793 : Blo 2139435 4062793 := bstep (se 2 (by rfl) ⟨1523547, by rfl⟩ : syracuseStep 4062793 = 3047095) B3047095
theorem B5417057 : Blo 2139435 5417057 := bstep (se 2 (by rfl) ⟨2031396, by rfl⟩ : syracuseStep 5417057 = 4062793) B4062793
theorem B3611371 : Blo 2139435 3611371 := bstep (se 1 (by rfl) ⟨2708528, by rfl⟩ : syracuseStep 3611371 = 5417057) B5417057
theorem B4815161 : Blo 2139435 4815161 := bstep (se 2 (by rfl) ⟨1805685, by rfl⟩ : syracuseStep 4815161 = 3611371) B3611371
theorem B3210107 : Blo 2139435 3210107 := bstep (se 1 (by rfl) ⟨2407580, by rfl⟩ : syracuseStep 3210107 = 4815161) B4815161
theorem B2140071 : Blo 2139435 2140071 := bstep (se 1 (by rfl) ⟨1605053, by rfl⟩ : syracuseStep 2140071 = 3210107) B3210107
theorem B2407585 : Blo 2139435 2407585 := bbase (se 2 (by rfl) ⟨902844, by rfl⟩ : syracuseStep 2407585 = 1805689) (by norm_num)
theorem B3210113 : Blo 2139435 3210113 := bstep (se 2 (by rfl) ⟨1203792, by rfl⟩ : syracuseStep 3210113 = 2407585) B2407585
theorem B2140075 : Blo 2139435 2140075 := bstep (se 1 (by rfl) ⟨1605056, by rfl⟩ : syracuseStep 2140075 = 3210113) B3210113
theorem B5417077 : Blo 2139435 5417077 := bbase (se 5 (by rfl) ⟨253925, by rfl⟩ : syracuseStep 5417077 = 507851) (by norm_num)
theorem B7222769 : Blo 2139435 7222769 := bstep (se 2 (by rfl) ⟨2708538, by rfl⟩ : syracuseStep 7222769 = 5417077) B5417077
theorem B4815179 : Blo 2139435 4815179 := bstep (se 1 (by rfl) ⟨3611384, by rfl⟩ : syracuseStep 4815179 = 7222769) B7222769
theorem B3210119 : Blo 2139435 3210119 := bstep (se 1 (by rfl) ⟨2407589, by rfl⟩ : syracuseStep 3210119 = 4815179) B4815179
theorem B2140079 : Blo 2139435 2140079 := bstep (se 1 (by rfl) ⟨1605059, by rfl⟩ : syracuseStep 2140079 = 3210119) B3210119
theorem B3210125 : Blo 2139435 3210125 := bbase (se 3 (by rfl) ⟨601898, by rfl⟩ : syracuseStep 3210125 = 1203797) (by norm_num)
theorem B2140083 : Blo 2139435 2140083 := bstep (se 1 (by rfl) ⟨1605062, by rfl⟩ : syracuseStep 2140083 = 3210125) B3210125
theorem B4815197 : Blo 2139435 4815197 := bbase (se 3 (by rfl) ⟨902849, by rfl⟩ : syracuseStep 4815197 = 1805699) (by norm_num)
theorem B3210131 : Blo 2139435 3210131 := bstep (se 1 (by rfl) ⟨2407598, by rfl⟩ : syracuseStep 3210131 = 4815197) B4815197
theorem B2140087 : Blo 2139435 2140087 := bstep (se 1 (by rfl) ⟨1605065, by rfl⟩ : syracuseStep 2140087 = 3210131) B3210131
theorem B3611405 : Blo 2139435 3611405 := bbase (se 3 (by rfl) ⟨677138, by rfl⟩ : syracuseStep 3611405 = 1354277) (by norm_num)
theorem B2407603 : Blo 2139435 2407603 := bstep (se 1 (by rfl) ⟨1805702, by rfl⟩ : syracuseStep 2407603 = 3611405) B3611405
theorem B3210137 : Blo 2139435 3210137 := bstep (se 2 (by rfl) ⟨1203801, by rfl⟩ : syracuseStep 3210137 = 2407603) B2407603
theorem B2140091 : Blo 2139435 2140091 := bstep (se 1 (by rfl) ⟨1605068, by rfl⟩ : syracuseStep 2140091 = 3210137) B3210137
theorem B18282773 : Blo 2139435 18282773 := bbase (se 6 (by rfl) ⟨428502, by rfl⟩ : syracuseStep 18282773 = 857005) (by norm_num)
theorem B12188515 : Blo 2139435 12188515 := bstep (se 1 (by rfl) ⟨9141386, by rfl⟩ : syracuseStep 12188515 = 18282773) B18282773
theorem B16251353 : Blo 2139435 16251353 := bstep (se 2 (by rfl) ⟨6094257, by rfl⟩ : syracuseStep 16251353 = 12188515) B12188515
theorem B10834235 : Blo 2139435 10834235 := bstep (se 1 (by rfl) ⟨8125676, by rfl⟩ : syracuseStep 10834235 = 16251353) B16251353
theorem B7222823 : Blo 2139435 7222823 := bstep (se 1 (by rfl) ⟨5417117, by rfl⟩ : syracuseStep 7222823 = 10834235) B10834235
theorem B4815215 : Blo 2139435 4815215 := bstep (se 1 (by rfl) ⟨3611411, by rfl⟩ : syracuseStep 4815215 = 7222823) B7222823
theorem B3210143 : Blo 2139435 3210143 := bstep (se 1 (by rfl) ⟨2407607, by rfl⟩ : syracuseStep 3210143 = 4815215) B4815215
theorem B2140095 : Blo 2139435 2140095 := bstep (se 1 (by rfl) ⟨1605071, by rfl⟩ : syracuseStep 2140095 = 3210143) B3210143
theorem B3210149 : Blo 2139435 3210149 := bbase (se 4 (by rfl) ⟨300951, by rfl⟩ : syracuseStep 3210149 = 601903) (by norm_num)
theorem B2140099 : Blo 2139435 2140099 := bstep (se 1 (by rfl) ⟨1605074, by rfl⟩ : syracuseStep 2140099 = 3210149) B3210149
theorem B2708569 : Blo 2139435 2708569 := bbase (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) (by norm_num)
theorem B3611425 : Blo 2139435 3611425 := bstep (se 2 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 3611425 = 2708569) B2708569
theorem B4815233 : Blo 2139435 4815233 := bstep (se 2 (by rfl) ⟨1805712, by rfl⟩ : syracuseStep 4815233 = 3611425) B3611425
theorem B3210155 : Blo 2139435 3210155 := bstep (se 1 (by rfl) ⟨2407616, by rfl⟩ : syracuseStep 3210155 = 4815233) B4815233
theorem B2140103 : Blo 2139435 2140103 := bstep (se 1 (by rfl) ⟨1605077, by rfl⟩ : syracuseStep 2140103 = 3210155) B3210155
theorem B2407621 : Blo 2139435 2407621 := bbase (se 4 (by rfl) ⟨225714, by rfl⟩ : syracuseStep 2407621 = 451429) (by norm_num)
theorem B3210161 : Blo 2139435 3210161 := bstep (se 2 (by rfl) ⟨1203810, by rfl⟩ : syracuseStep 3210161 = 2407621) B2407621
theorem B2140107 : Blo 2139435 2140107 := bstep (se 1 (by rfl) ⟨1605080, by rfl⟩ : syracuseStep 2140107 = 3210161) B3210161
theorem B4062869 : Blo 2139435 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B2708579 : Blo 2139435 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B7222877 : Blo 2139435 7222877 := bstep (se 3 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 7222877 = 2708579) B2708579
theorem B4815251 : Blo 2139435 4815251 := bstep (se 1 (by rfl) ⟨3611438, by rfl⟩ : syracuseStep 4815251 = 7222877) B7222877
theorem B3210167 : Blo 2139435 3210167 := bstep (se 1 (by rfl) ⟨2407625, by rfl⟩ : syracuseStep 3210167 = 4815251) B4815251
theorem B2140111 : Blo 2139435 2140111 := bstep (se 1 (by rfl) ⟨1605083, by rfl⟩ : syracuseStep 2140111 = 3210167) B3210167
theorem B3210173 : Blo 2139435 3210173 := bbase (se 3 (by rfl) ⟨601907, by rfl⟩ : syracuseStep 3210173 = 1203815) (by norm_num)
theorem B2140115 : Blo 2139435 2140115 := bstep (se 1 (by rfl) ⟨1605086, by rfl⟩ : syracuseStep 2140115 = 3210173) B3210173
theorem B4815269 : Blo 2139435 4815269 := bbase (se 4 (by rfl) ⟨451431, by rfl⟩ : syracuseStep 4815269 = 902863) (by norm_num)
theorem B3210179 : Blo 2139435 3210179 := bstep (se 1 (by rfl) ⟨2407634, by rfl⟩ : syracuseStep 3210179 = 4815269) B4815269
theorem B2140119 : Blo 2139435 2140119 := bstep (se 1 (by rfl) ⟨1605089, by rfl⟩ : syracuseStep 2140119 = 3210179) B3210179
theorem B5417189 : Blo 2139435 5417189 := bbase (se 4 (by rfl) ⟨507861, by rfl⟩ : syracuseStep 5417189 = 1015723) (by norm_num)
theorem B3611459 : Blo 2139435 3611459 := bstep (se 1 (by rfl) ⟨2708594, by rfl⟩ : syracuseStep 3611459 = 5417189) B5417189
theorem B2407639 : Blo 2139435 2407639 := bstep (se 1 (by rfl) ⟨1805729, by rfl⟩ : syracuseStep 2407639 = 3611459) B3611459
theorem B3210185 : Blo 2139435 3210185 := bstep (se 2 (by rfl) ⟨1203819, by rfl⟩ : syracuseStep 3210185 = 2407639) B2407639
theorem B2140123 : Blo 2139435 2140123 := bstep (se 1 (by rfl) ⟨1605092, by rfl⟩ : syracuseStep 2140123 = 3210185) B3210185
theorem B2285381 : Blo 2139435 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B6094349 : Blo 2139435 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B4062899 : Blo 2139435 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B10834397 : Blo 2139435 10834397 := bstep (se 3 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 10834397 = 4062899) B4062899
theorem B7222931 : Blo 2139435 7222931 := bstep (se 1 (by rfl) ⟨5417198, by rfl⟩ : syracuseStep 7222931 = 10834397) B10834397
theorem B4815287 : Blo 2139435 4815287 := bstep (se 1 (by rfl) ⟨3611465, by rfl⟩ : syracuseStep 4815287 = 7222931) B7222931
theorem B3210191 : Blo 2139435 3210191 := bstep (se 1 (by rfl) ⟨2407643, by rfl⟩ : syracuseStep 3210191 = 4815287) B4815287
theorem B2140127 : Blo 2139435 2140127 := bstep (se 1 (by rfl) ⟨1605095, by rfl⟩ : syracuseStep 2140127 = 3210191) B3210191
theorem B3210197 : Blo 2139435 3210197 := bbase (se 7 (by rfl) ⟨37619, by rfl⟩ : syracuseStep 3210197 = 75239) (by norm_num)
theorem B2140131 : Blo 2139435 2140131 := bstep (se 1 (by rfl) ⟨1605098, by rfl⟩ : syracuseStep 2140131 = 3210197) B3210197
theorem B8125829 : Blo 2139435 8125829 := bbase (se 4 (by rfl) ⟨761796, by rfl⟩ : syracuseStep 8125829 = 1523593) (by norm_num)
theorem B5417219 : Blo 2139435 5417219 := bstep (se 1 (by rfl) ⟨4062914, by rfl⟩ : syracuseStep 5417219 = 8125829) B8125829
theorem B3611479 : Blo 2139435 3611479 := bstep (se 1 (by rfl) ⟨2708609, by rfl⟩ : syracuseStep 3611479 = 5417219) B5417219
theorem B4815305 : Blo 2139435 4815305 := bstep (se 2 (by rfl) ⟨1805739, by rfl⟩ : syracuseStep 4815305 = 3611479) B3611479
theorem B3210203 : Blo 2139435 3210203 := bstep (se 1 (by rfl) ⟨2407652, by rfl⟩ : syracuseStep 3210203 = 4815305) B4815305
theorem B2140135 : Blo 2139435 2140135 := bstep (se 1 (by rfl) ⟨1605101, by rfl⟩ : syracuseStep 2140135 = 3210203) B3210203
theorem B2407657 : Blo 2139435 2407657 := bbase (se 2 (by rfl) ⟨902871, by rfl⟩ : syracuseStep 2407657 = 1805743) (by norm_num)
theorem B3210209 : Blo 2139435 3210209 := bstep (se 2 (by rfl) ⟨1203828, by rfl⟩ : syracuseStep 3210209 = 2407657) B2407657
theorem B2140139 : Blo 2139435 2140139 := bstep (se 1 (by rfl) ⟨1605104, by rfl⟩ : syracuseStep 2140139 = 3210209) B3210209
theorem B12188789 : Blo 2139435 12188789 := bbase (se 5 (by rfl) ⟨571349, by rfl⟩ : syracuseStep 12188789 = 1142699) (by norm_num)
theorem B8125859 : Blo 2139435 8125859 := bstep (se 1 (by rfl) ⟨6094394, by rfl⟩ : syracuseStep 8125859 = 12188789) B12188789
theorem B5417239 : Blo 2139435 5417239 := bstep (se 1 (by rfl) ⟨4062929, by rfl⟩ : syracuseStep 5417239 = 8125859) B8125859
theorem B7222985 : Blo 2139435 7222985 := bstep (se 2 (by rfl) ⟨2708619, by rfl⟩ : syracuseStep 7222985 = 5417239) B5417239
theorem B4815323 : Blo 2139435 4815323 := bstep (se 1 (by rfl) ⟨3611492, by rfl⟩ : syracuseStep 4815323 = 7222985) B7222985
theorem B3210215 : Blo 2139435 3210215 := bstep (se 1 (by rfl) ⟨2407661, by rfl⟩ : syracuseStep 3210215 = 4815323) B4815323
theorem B2140143 : Blo 2139435 2140143 := bstep (se 1 (by rfl) ⟨1605107, by rfl⟩ : syracuseStep 2140143 = 3210215) B3210215
theorem B3210221 : Blo 2139435 3210221 := bbase (se 3 (by rfl) ⟨601916, by rfl⟩ : syracuseStep 3210221 = 1203833) (by norm_num)
theorem B2140147 : Blo 2139435 2140147 := bstep (se 1 (by rfl) ⟨1605110, by rfl⟩ : syracuseStep 2140147 = 3210221) B3210221
theorem B4815341 : Blo 2139435 4815341 := bbase (se 3 (by rfl) ⟨902876, by rfl⟩ : syracuseStep 4815341 = 1805753) (by norm_num)
theorem B3210227 : Blo 2139435 3210227 := bstep (se 1 (by rfl) ⟨2407670, by rfl⟩ : syracuseStep 3210227 = 4815341) B4815341
theorem B2140151 : Blo 2139435 2140151 := bstep (se 1 (by rfl) ⟨1605113, by rfl⟩ : syracuseStep 2140151 = 3210227) B3210227
theorem B5784949 : Blo 2139435 5784949 := bbase (se 5 (by rfl) ⟨271169, by rfl⟩ : syracuseStep 5784949 = 542339) (by norm_num)
theorem B7713265 : Blo 2139435 7713265 := bstep (se 2 (by rfl) ⟨2892474, by rfl⟩ : syracuseStep 7713265 = 5784949) B5784949
theorem B10284353 : Blo 2139435 10284353 := bstep (se 2 (by rfl) ⟨3856632, by rfl⟩ : syracuseStep 10284353 = 7713265) B7713265
theorem B6856235 : Blo 2139435 6856235 := bstep (se 1 (by rfl) ⟨5142176, by rfl⟩ : syracuseStep 6856235 = 10284353) B10284353
theorem B4570823 : Blo 2139435 4570823 := bstep (se 1 (by rfl) ⟨3428117, by rfl⟩ : syracuseStep 4570823 = 6856235) B6856235
theorem B3047215 : Blo 2139435 3047215 := bstep (se 1 (by rfl) ⟨2285411, by rfl⟩ : syracuseStep 3047215 = 4570823) B4570823
theorem B4062953 : Blo 2139435 4062953 := bstep (se 2 (by rfl) ⟨1523607, by rfl⟩ : syracuseStep 4062953 = 3047215) B3047215
theorem B2708635 : Blo 2139435 2708635 := bstep (se 1 (by rfl) ⟨2031476, by rfl⟩ : syracuseStep 2708635 = 4062953) B4062953
theorem B3611513 : Blo 2139435 3611513 := bstep (se 2 (by rfl) ⟨1354317, by rfl⟩ : syracuseStep 3611513 = 2708635) B2708635
theorem B2407675 : Blo 2139435 2407675 := bstep (se 1 (by rfl) ⟨1805756, by rfl⟩ : syracuseStep 2407675 = 3611513) B3611513
theorem B3210233 : Blo 2139435 3210233 := bstep (se 2 (by rfl) ⟨1203837, by rfl⟩ : syracuseStep 3210233 = 2407675) B2407675
theorem B2140155 : Blo 2139435 2140155 := bstep (se 1 (by rfl) ⟨1605116, by rfl⟩ : syracuseStep 2140155 = 3210233) B3210233
theorem B6261877 : Blo 2139435 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B8349169 : Blo 2139435 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B11132225 : Blo 2139435 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B7421483 : Blo 2139435 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B4947655 : Blo 2139435 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B6596873 : Blo 2139435 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B4397915 : Blo 2139435 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B11727773 : Blo 2139435 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B7818515 : Blo 2139435 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B5212343 : Blo 2139435 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B3474895 : Blo 2139435 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B4633193 : Blo 2139435 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B3088795 : Blo 2139435 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B4118393 : Blo 2139435 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2745595 : Blo 2139435 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B3660793 : Blo 2139435 3660793 := bstep (se 2 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 3660793 = 2745595) B2745595
theorem B19524229 : Blo 2139435 19524229 := bstep (se 4 (by rfl) ⟨1830396, by rfl⟩ : syracuseStep 19524229 = 3660793) B3660793
theorem B104129221 : Blo 2139435 104129221 := bstep (se 4 (by rfl) ⟨9762114, by rfl⟩ : syracuseStep 104129221 = 19524229) B19524229
theorem B138838961 : Blo 2139435 138838961 := bstep (se 2 (by rfl) ⟨52064610, by rfl⟩ : syracuseStep 138838961 = 104129221) B104129221
theorem B92559307 : Blo 2139435 92559307 := bstep (se 1 (by rfl) ⟨69419480, by rfl⟩ : syracuseStep 92559307 = 138838961) B138838961
theorem B123412409 : Blo 2139435 123412409 := bstep (se 2 (by rfl) ⟨46279653, by rfl⟩ : syracuseStep 123412409 = 92559307) B92559307
theorem B82274939 : Blo 2139435 82274939 := bstep (se 1 (by rfl) ⟨61706204, by rfl⟩ : syracuseStep 82274939 = 123412409) B123412409
theorem B54849959 : Blo 2139435 54849959 := bstep (se 1 (by rfl) ⟨41137469, by rfl⟩ : syracuseStep 54849959 = 82274939) B82274939
theorem B36566639 : Blo 2139435 36566639 := bstep (se 1 (by rfl) ⟨27424979, by rfl⟩ : syracuseStep 36566639 = 54849959) B54849959
theorem B24377759 : Blo 2139435 24377759 := bstep (se 1 (by rfl) ⟨18283319, by rfl⟩ : syracuseStep 24377759 = 36566639) B36566639
theorem B16251839 : Blo 2139435 16251839 := bstep (se 1 (by rfl) ⟨12188879, by rfl⟩ : syracuseStep 16251839 = 24377759) B24377759
theorem B10834559 : Blo 2139435 10834559 := bstep (se 1 (by rfl) ⟨8125919, by rfl⟩ : syracuseStep 10834559 = 16251839) B16251839
theorem B7223039 : Blo 2139435 7223039 := bstep (se 1 (by rfl) ⟨5417279, by rfl⟩ : syracuseStep 7223039 = 10834559) B10834559
theorem B4815359 : Blo 2139435 4815359 := bstep (se 1 (by rfl) ⟨3611519, by rfl⟩ : syracuseStep 4815359 = 7223039) B7223039
theorem B3210239 : Blo 2139435 3210239 := bstep (se 1 (by rfl) ⟨2407679, by rfl⟩ : syracuseStep 3210239 = 4815359) B4815359
theorem B2140159 : Blo 2139435 2140159 := bstep (se 1 (by rfl) ⟨1605119, by rfl⟩ : syracuseStep 2140159 = 3210239) B3210239
theorem B3210245 : Blo 2139435 3210245 := bbase (se 4 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 3210245 = 601921) (by norm_num)
theorem B2140163 : Blo 2139435 2140163 := bstep (se 1 (by rfl) ⟨1605122, by rfl⟩ : syracuseStep 2140163 = 3210245) B3210245
theorem B3611533 : Blo 2139435 3611533 := bbase (se 3 (by rfl) ⟨677162, by rfl⟩ : syracuseStep 3611533 = 1354325) (by norm_num)
theorem B4815377 : Blo 2139435 4815377 := bstep (se 2 (by rfl) ⟨1805766, by rfl⟩ : syracuseStep 4815377 = 3611533) B3611533
theorem B3210251 : Blo 2139435 3210251 := bstep (se 1 (by rfl) ⟨2407688, by rfl⟩ : syracuseStep 3210251 = 4815377) B4815377
theorem B2140167 : Blo 2139435 2140167 := bstep (se 1 (by rfl) ⟨1605125, by rfl⟩ : syracuseStep 2140167 = 3210251) B3210251
theorem B2407693 : Blo 2139435 2407693 := bbase (se 3 (by rfl) ⟨451442, by rfl⟩ : syracuseStep 2407693 = 902885) (by norm_num)
theorem B3210257 : Blo 2139435 3210257 := bstep (se 2 (by rfl) ⟨1203846, by rfl⟩ : syracuseStep 3210257 = 2407693) B2407693
theorem B2140171 : Blo 2139435 2140171 := bstep (se 1 (by rfl) ⟨1605128, by rfl⟩ : syracuseStep 2140171 = 3210257) B3210257
theorem B7223093 : Blo 2139435 7223093 := bbase (se 5 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 7223093 = 677165) (by norm_num)
theorem B4815395 : Blo 2139435 4815395 := bstep (se 1 (by rfl) ⟨3611546, by rfl⟩ : syracuseStep 4815395 = 7223093) B7223093
theorem B3210263 : Blo 2139435 3210263 := bstep (se 1 (by rfl) ⟨2407697, by rfl⟩ : syracuseStep 3210263 = 4815395) B4815395
theorem B2140175 : Blo 2139435 2140175 := bstep (se 1 (by rfl) ⟨1605131, by rfl⟩ : syracuseStep 2140175 = 3210263) B3210263
theorem B3210269 : Blo 2139435 3210269 := bbase (se 3 (by rfl) ⟨601925, by rfl⟩ : syracuseStep 3210269 = 1203851) (by norm_num)
theorem B2140179 : Blo 2139435 2140179 := bstep (se 1 (by rfl) ⟨1605134, by rfl⟩ : syracuseStep 2140179 = 3210269) B3210269
theorem B4815413 : Blo 2139435 4815413 := bbase (se 5 (by rfl) ⟨225722, by rfl⟩ : syracuseStep 4815413 = 451445) (by norm_num)
theorem B3210275 : Blo 2139435 3210275 := bstep (se 1 (by rfl) ⟨2407706, by rfl⟩ : syracuseStep 3210275 = 4815413) B4815413
theorem B2140183 : Blo 2139435 2140183 := bstep (se 1 (by rfl) ⟨1605137, by rfl⟩ : syracuseStep 2140183 = 3210275) B3210275
theorem B9141781 : Blo 2139435 9141781 := bbase (se 6 (by rfl) ⟨214260, by rfl⟩ : syracuseStep 9141781 = 428521) (by norm_num)
theorem B12189041 : Blo 2139435 12189041 := bstep (se 2 (by rfl) ⟨4570890, by rfl⟩ : syracuseStep 12189041 = 9141781) B9141781
theorem B8126027 : Blo 2139435 8126027 := bstep (se 1 (by rfl) ⟨6094520, by rfl⟩ : syracuseStep 8126027 = 12189041) B12189041
theorem B5417351 : Blo 2139435 5417351 := bstep (se 1 (by rfl) ⟨4063013, by rfl⟩ : syracuseStep 5417351 = 8126027) B8126027
theorem B3611567 : Blo 2139435 3611567 := bstep (se 1 (by rfl) ⟨2708675, by rfl⟩ : syracuseStep 3611567 = 5417351) B5417351
theorem B2407711 : Blo 2139435 2407711 := bstep (se 1 (by rfl) ⟨1805783, by rfl⟩ : syracuseStep 2407711 = 3611567) B3611567
theorem B3210281 : Blo 2139435 3210281 := bstep (se 2 (by rfl) ⟨1203855, by rfl⟩ : syracuseStep 3210281 = 2407711) B2407711
theorem B2140187 : Blo 2139435 2140187 := bstep (se 1 (by rfl) ⟨1605140, by rfl⟩ : syracuseStep 2140187 = 3210281) B3210281
theorem B9141797 : Blo 2139435 9141797 := bbase (se 4 (by rfl) ⟨857043, by rfl⟩ : syracuseStep 9141797 = 1714087) (by norm_num)
theorem B6094531 : Blo 2139435 6094531 := bstep (se 1 (by rfl) ⟨4570898, by rfl⟩ : syracuseStep 6094531 = 9141797) B9141797
theorem B8126041 : Blo 2139435 8126041 := bstep (se 2 (by rfl) ⟨3047265, by rfl⟩ : syracuseStep 8126041 = 6094531) B6094531
theorem B10834721 : Blo 2139435 10834721 := bstep (se 2 (by rfl) ⟨4063020, by rfl⟩ : syracuseStep 10834721 = 8126041) B8126041
theorem B7223147 : Blo 2139435 7223147 := bstep (se 1 (by rfl) ⟨5417360, by rfl⟩ : syracuseStep 7223147 = 10834721) B10834721
theorem B4815431 : Blo 2139435 4815431 := bstep (se 1 (by rfl) ⟨3611573, by rfl⟩ : syracuseStep 4815431 = 7223147) B7223147
theorem B3210287 : Blo 2139435 3210287 := bstep (se 1 (by rfl) ⟨2407715, by rfl⟩ : syracuseStep 3210287 = 4815431) B4815431
theorem B2140191 : Blo 2139435 2140191 := bstep (se 1 (by rfl) ⟨1605143, by rfl⟩ : syracuseStep 2140191 = 3210287) B3210287
theorem B3210293 : Blo 2139435 3210293 := bbase (se 5 (by rfl) ⟨150482, by rfl⟩ : syracuseStep 3210293 = 300965) (by norm_num)
theorem B2140195 : Blo 2139435 2140195 := bstep (se 1 (by rfl) ⟨1605146, by rfl⟩ : syracuseStep 2140195 = 3210293) B3210293
theorem B5417381 : Blo 2139435 5417381 := bbase (se 4 (by rfl) ⟨507879, by rfl⟩ : syracuseStep 5417381 = 1015759) (by norm_num)
theorem B3611587 : Blo 2139435 3611587 := bstep (se 1 (by rfl) ⟨2708690, by rfl⟩ : syracuseStep 3611587 = 5417381) B5417381
theorem B4815449 : Blo 2139435 4815449 := bstep (se 2 (by rfl) ⟨1805793, by rfl⟩ : syracuseStep 4815449 = 3611587) B3611587
theorem B3210299 : Blo 2139435 3210299 := bstep (se 1 (by rfl) ⟨2407724, by rfl⟩ : syracuseStep 3210299 = 4815449) B4815449
theorem B2140199 : Blo 2139435 2140199 := bstep (se 1 (by rfl) ⟨1605149, by rfl⟩ : syracuseStep 2140199 = 3210299) B3210299
theorem B2407729 : Blo 2139435 2407729 := bbase (se 2 (by rfl) ⟨902898, by rfl⟩ : syracuseStep 2407729 = 1805797) (by norm_num)
theorem B3210305 : Blo 2139435 3210305 := bstep (se 2 (by rfl) ⟨1203864, by rfl⟩ : syracuseStep 3210305 = 2407729) B2407729
theorem B2140203 : Blo 2139435 2140203 := bstep (se 1 (by rfl) ⟨1605152, by rfl⟩ : syracuseStep 2140203 = 3210305) B3210305
theorem B4570933 : Blo 2139435 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B6094577 : Blo 2139435 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B4063051 : Blo 2139435 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B5417401 : Blo 2139435 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B7223201 : Blo 2139435 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B4815467 : Blo 2139435 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B3210311 : Blo 2139435 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B2140207 : Blo 2139435 2140207 := bstep (se 1 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 2140207 = 3210311) B3210311
theorem B3210317 : Blo 2139435 3210317 := bbase (se 3 (by rfl) ⟨601934, by rfl⟩ : syracuseStep 3210317 = 1203869) (by norm_num)
theorem B2140211 : Blo 2139435 2140211 := bstep (se 1 (by rfl) ⟨1605158, by rfl⟩ : syracuseStep 2140211 = 3210317) B3210317
theorem B4815485 : Blo 2139435 4815485 := bbase (se 3 (by rfl) ⟨902903, by rfl⟩ : syracuseStep 4815485 = 1805807) (by norm_num)
theorem B3210323 : Blo 2139435 3210323 := bstep (se 1 (by rfl) ⟨2407742, by rfl⟩ : syracuseStep 3210323 = 4815485) B4815485
theorem B2140215 : Blo 2139435 2140215 := bstep (se 1 (by rfl) ⟨1605161, by rfl⟩ : syracuseStep 2140215 = 3210323) B3210323
theorem B3611621 : Blo 2139435 3611621 := bbase (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) (by norm_num)
theorem B2407747 : Blo 2139435 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B3210329 : Blo 2139435 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B2140219 : Blo 2139435 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B10284677 : Blo 2139435 10284677 := bbase (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) (by norm_num)
theorem B6856451 : Blo 2139435 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B4570967 : Blo 2139435 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B3047311 : Blo 2139435 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B16252325 : Blo 2139435 16252325 := bstep (se 4 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 16252325 = 3047311) B3047311
theorem B10834883 : Blo 2139435 10834883 := bstep (se 1 (by rfl) ⟨8126162, by rfl⟩ : syracuseStep 10834883 = 16252325) B16252325
theorem B7223255 : Blo 2139435 7223255 := bstep (se 1 (by rfl) ⟨5417441, by rfl⟩ : syracuseStep 7223255 = 10834883) B10834883
theorem B4815503 : Blo 2139435 4815503 := bstep (se 1 (by rfl) ⟨3611627, by rfl⟩ : syracuseStep 4815503 = 7223255) B7223255
theorem B3210335 : Blo 2139435 3210335 := bstep (se 1 (by rfl) ⟨2407751, by rfl⟩ : syracuseStep 3210335 = 4815503) B4815503
theorem B2140223 : Blo 2139435 2140223 := bstep (se 1 (by rfl) ⟨1605167, by rfl⟩ : syracuseStep 2140223 = 3210335) B3210335
theorem B3210341 : Blo 2139435 3210341 := bbase (se 4 (by rfl) ⟨300969, by rfl⟩ : syracuseStep 3210341 = 601939) (by norm_num)
theorem B2140227 : Blo 2139435 2140227 := bstep (se 1 (by rfl) ⟨1605170, by rfl⟩ : syracuseStep 2140227 = 3210341) B3210341
theorem B2169433 : Blo 2139435 2169433 := bbase (se 2 (by rfl) ⟨813537, by rfl⟩ : syracuseStep 2169433 = 1627075) (by norm_num)
theorem B11570309 : Blo 2139435 11570309 := bstep (se 4 (by rfl) ⟨1084716, by rfl⟩ : syracuseStep 11570309 = 2169433) B2169433
theorem B7713539 : Blo 2139435 7713539 := bstep (se 1 (by rfl) ⟨5785154, by rfl⟩ : syracuseStep 7713539 = 11570309) B11570309
theorem B5142359 : Blo 2139435 5142359 := bstep (se 1 (by rfl) ⟨3856769, by rfl⟩ : syracuseStep 5142359 = 7713539) B7713539
theorem B3428239 : Blo 2139435 3428239 := bstep (se 1 (by rfl) ⟨2571179, by rfl⟩ : syracuseStep 3428239 = 5142359) B5142359
theorem B4570985 : Blo 2139435 4570985 := bstep (se 2 (by rfl) ⟨1714119, by rfl⟩ : syracuseStep 4570985 = 3428239) B3428239
theorem B3047323 : Blo 2139435 3047323 := bstep (se 1 (by rfl) ⟨2285492, by rfl⟩ : syracuseStep 3047323 = 4570985) B4570985
theorem B4063097 : Blo 2139435 4063097 := bstep (se 2 (by rfl) ⟨1523661, by rfl⟩ : syracuseStep 4063097 = 3047323) B3047323
theorem B2708731 : Blo 2139435 2708731 := bstep (se 1 (by rfl) ⟨2031548, by rfl⟩ : syracuseStep 2708731 = 4063097) B4063097
theorem B3611641 : Blo 2139435 3611641 := bstep (se 2 (by rfl) ⟨1354365, by rfl⟩ : syracuseStep 3611641 = 2708731) B2708731
theorem B4815521 : Blo 2139435 4815521 := bstep (se 2 (by rfl) ⟨1805820, by rfl⟩ : syracuseStep 4815521 = 3611641) B3611641
theorem B3210347 : Blo 2139435 3210347 := bstep (se 1 (by rfl) ⟨2407760, by rfl⟩ : syracuseStep 3210347 = 4815521) B4815521
theorem B2140231 : Blo 2139435 2140231 := bstep (se 1 (by rfl) ⟨1605173, by rfl⟩ : syracuseStep 2140231 = 3210347) B3210347
theorem B2407765 : Blo 2139435 2407765 := bbase (se 11 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 2407765 = 3527) (by norm_num)
theorem B3210353 : Blo 2139435 3210353 := bstep (se 2 (by rfl) ⟨1203882, by rfl⟩ : syracuseStep 3210353 = 2407765) B2407765
theorem B2140235 : Blo 2139435 2140235 := bstep (se 1 (by rfl) ⟨1605176, by rfl⟩ : syracuseStep 2140235 = 3210353) B3210353
theorem B2708741 : Blo 2139435 2708741 := bbase (se 4 (by rfl) ⟨253944, by rfl⟩ : syracuseStep 2708741 = 507889) (by norm_num)
theorem B7223309 : Blo 2139435 7223309 := bstep (se 3 (by rfl) ⟨1354370, by rfl⟩ : syracuseStep 7223309 = 2708741) B2708741
theorem B4815539 : Blo 2139435 4815539 := bstep (se 1 (by rfl) ⟨3611654, by rfl⟩ : syracuseStep 4815539 = 7223309) B7223309
theorem B3210359 : Blo 2139435 3210359 := bstep (se 1 (by rfl) ⟨2407769, by rfl⟩ : syracuseStep 3210359 = 4815539) B4815539
theorem B2140239 : Blo 2139435 2140239 := bstep (se 1 (by rfl) ⟨1605179, by rfl⟩ : syracuseStep 2140239 = 3210359) B3210359
theorem B3210365 : Blo 2139435 3210365 := bbase (se 3 (by rfl) ⟨601943, by rfl⟩ : syracuseStep 3210365 = 1203887) (by norm_num)
theorem B2140243 : Blo 2139435 2140243 := bstep (se 1 (by rfl) ⟨1605182, by rfl⟩ : syracuseStep 2140243 = 3210365) B3210365
theorem B4815557 : Blo 2139435 4815557 := bbase (se 4 (by rfl) ⟨451458, by rfl⟩ : syracuseStep 4815557 = 902917) (by norm_num)
theorem B3210371 : Blo 2139435 3210371 := bstep (se 1 (by rfl) ⟨2407778, by rfl⟩ : syracuseStep 3210371 = 4815557) B4815557
theorem B2140247 : Blo 2139435 2140247 := bstep (se 1 (by rfl) ⟨1605185, by rfl⟩ : syracuseStep 2140247 = 3210371) B3210371
theorem B4881269 : Blo 2139435 4881269 := bbase (se 5 (by rfl) ⟨228809, by rfl⟩ : syracuseStep 4881269 = 457619) (by norm_num)
theorem B13016717 : Blo 2139435 13016717 := bstep (se 3 (by rfl) ⟨2440634, by rfl⟩ : syracuseStep 13016717 = 4881269) B4881269
theorem B8677811 : Blo 2139435 8677811 := bstep (se 1 (by rfl) ⟨6508358, by rfl⟩ : syracuseStep 8677811 = 13016717) B13016717
theorem B23140829 : Blo 2139435 23140829 := bstep (se 3 (by rfl) ⟨4338905, by rfl⟩ : syracuseStep 23140829 = 8677811) B8677811
theorem B15427219 : Blo 2139435 15427219 := bstep (se 1 (by rfl) ⟨11570414, by rfl⟩ : syracuseStep 15427219 = 23140829) B23140829
theorem B20569625 : Blo 2139435 20569625 := bstep (se 2 (by rfl) ⟨7713609, by rfl⟩ : syracuseStep 20569625 = 15427219) B15427219
theorem B13713083 : Blo 2139435 13713083 := bstep (se 1 (by rfl) ⟨10284812, by rfl⟩ : syracuseStep 13713083 = 20569625) B20569625
theorem B9142055 : Blo 2139435 9142055 := bstep (se 1 (by rfl) ⟨6856541, by rfl⟩ : syracuseStep 9142055 = 13713083) B13713083
theorem B6094703 : Blo 2139435 6094703 := bstep (se 1 (by rfl) ⟨4571027, by rfl⟩ : syracuseStep 6094703 = 9142055) B9142055
theorem B4063135 : Blo 2139435 4063135 := bstep (se 1 (by rfl) ⟨3047351, by rfl⟩ : syracuseStep 4063135 = 6094703) B6094703
theorem B5417513 : Blo 2139435 5417513 := bstep (se 2 (by rfl) ⟨2031567, by rfl⟩ : syracuseStep 5417513 = 4063135) B4063135
theorem B3611675 : Blo 2139435 3611675 := bstep (se 1 (by rfl) ⟨2708756, by rfl⟩ : syracuseStep 3611675 = 5417513) B5417513
theorem B2407783 : Blo 2139435 2407783 := bstep (se 1 (by rfl) ⟨1805837, by rfl⟩ : syracuseStep 2407783 = 3611675) B3611675
theorem B3210377 : Blo 2139435 3210377 := bstep (se 2 (by rfl) ⟨1203891, by rfl⟩ : syracuseStep 3210377 = 2407783) B2407783
theorem B2140251 : Blo 2139435 2140251 := bstep (se 1 (by rfl) ⟨1605188, by rfl⟩ : syracuseStep 2140251 = 3210377) B3210377
theorem B10835045 : Blo 2139435 10835045 := bbase (se 4 (by rfl) ⟨1015785, by rfl⟩ : syracuseStep 10835045 = 2031571) (by norm_num)
theorem B7223363 : Blo 2139435 7223363 := bstep (se 1 (by rfl) ⟨5417522, by rfl⟩ : syracuseStep 7223363 = 10835045) B10835045
theorem B4815575 : Blo 2139435 4815575 := bstep (se 1 (by rfl) ⟨3611681, by rfl⟩ : syracuseStep 4815575 = 7223363) B7223363
theorem B3210383 : Blo 2139435 3210383 := bstep (se 1 (by rfl) ⟨2407787, by rfl⟩ : syracuseStep 3210383 = 4815575) B4815575
theorem B2140255 : Blo 2139435 2140255 := bstep (se 1 (by rfl) ⟨1605191, by rfl⟩ : syracuseStep 2140255 = 3210383) B3210383
theorem B3210389 : Blo 2139435 3210389 := bbase (se 6 (by rfl) ⟨75243, by rfl⟩ : syracuseStep 3210389 = 150487) (by norm_num)
theorem B2140259 : Blo 2139435 2140259 := bstep (se 1 (by rfl) ⟨1605194, by rfl⟩ : syracuseStep 2140259 = 3210389) B3210389
theorem B10284869 : Blo 2139435 10284869 := bbase (se 4 (by rfl) ⟨964206, by rfl⟩ : syracuseStep 10284869 = 1928413) (by norm_num)
theorem B6856579 : Blo 2139435 6856579 := bstep (se 1 (by rfl) ⟨5142434, by rfl⟩ : syracuseStep 6856579 = 10284869) B10284869
theorem B9142105 : Blo 2139435 9142105 := bstep (se 2 (by rfl) ⟨3428289, by rfl⟩ : syracuseStep 9142105 = 6856579) B6856579
theorem B12189473 : Blo 2139435 12189473 := bstep (se 2 (by rfl) ⟨4571052, by rfl⟩ : syracuseStep 12189473 = 9142105) B9142105
theorem B8126315 : Blo 2139435 8126315 := bstep (se 1 (by rfl) ⟨6094736, by rfl⟩ : syracuseStep 8126315 = 12189473) B12189473
theorem B5417543 : Blo 2139435 5417543 := bstep (se 1 (by rfl) ⟨4063157, by rfl⟩ : syracuseStep 5417543 = 8126315) B8126315
theorem B3611695 : Blo 2139435 3611695 := bstep (se 1 (by rfl) ⟨2708771, by rfl⟩ : syracuseStep 3611695 = 5417543) B5417543
theorem B4815593 : Blo 2139435 4815593 := bstep (se 2 (by rfl) ⟨1805847, by rfl⟩ : syracuseStep 4815593 = 3611695) B3611695
theorem B3210395 : Blo 2139435 3210395 := bstep (se 1 (by rfl) ⟨2407796, by rfl⟩ : syracuseStep 3210395 = 4815593) B4815593
theorem B2140263 : Blo 2139435 2140263 := bstep (se 1 (by rfl) ⟨1605197, by rfl⟩ : syracuseStep 2140263 = 3210395) B3210395
theorem B2407801 : Blo 2139435 2407801 := bbase (se 2 (by rfl) ⟨902925, by rfl⟩ : syracuseStep 2407801 = 1805851) (by norm_num)
theorem B3210401 : Blo 2139435 3210401 := bstep (se 2 (by rfl) ⟨1203900, by rfl⟩ : syracuseStep 3210401 = 2407801) B2407801
theorem B2140267 : Blo 2139435 2140267 := bstep (se 1 (by rfl) ⟨1605200, by rfl⟩ : syracuseStep 2140267 = 3210401) B3210401
theorem B2440657 : Blo 2139435 2440657 := bbase (se 2 (by rfl) ⟨915246, by rfl⟩ : syracuseStep 2440657 = 1830493) (by norm_num)
theorem B13016837 : Blo 2139435 13016837 := bstep (se 4 (by rfl) ⟨1220328, by rfl⟩ : syracuseStep 13016837 = 2440657) B2440657
theorem B8677891 : Blo 2139435 8677891 := bstep (se 1 (by rfl) ⟨6508418, by rfl⟩ : syracuseStep 8677891 = 13016837) B13016837
theorem B11570521 : Blo 2139435 11570521 := bstep (se 2 (by rfl) ⟨4338945, by rfl⟩ : syracuseStep 11570521 = 8677891) B8677891
theorem B15427361 : Blo 2139435 15427361 := bstep (se 2 (by rfl) ⟨5785260, by rfl⟩ : syracuseStep 15427361 = 11570521) B11570521
theorem B10284907 : Blo 2139435 10284907 := bstep (se 1 (by rfl) ⟨7713680, by rfl⟩ : syracuseStep 10284907 = 15427361) B15427361
theorem B13713209 : Blo 2139435 13713209 := bstep (se 2 (by rfl) ⟨5142453, by rfl⟩ : syracuseStep 13713209 = 10284907) B10284907
theorem B9142139 : Blo 2139435 9142139 := bstep (se 1 (by rfl) ⟨6856604, by rfl⟩ : syracuseStep 9142139 = 13713209) B13713209
theorem B6094759 : Blo 2139435 6094759 := bstep (se 1 (by rfl) ⟨4571069, by rfl⟩ : syracuseStep 6094759 = 9142139) B9142139
theorem B8126345 : Blo 2139435 8126345 := bstep (se 2 (by rfl) ⟨3047379, by rfl⟩ : syracuseStep 8126345 = 6094759) B6094759
theorem B5417563 : Blo 2139435 5417563 := bstep (se 1 (by rfl) ⟨4063172, by rfl⟩ : syracuseStep 5417563 = 8126345) B8126345
theorem B7223417 : Blo 2139435 7223417 := bstep (se 2 (by rfl) ⟨2708781, by rfl⟩ : syracuseStep 7223417 = 5417563) B5417563
theorem B4815611 : Blo 2139435 4815611 := bstep (se 1 (by rfl) ⟨3611708, by rfl⟩ : syracuseStep 4815611 = 7223417) B7223417
theorem B3210407 : Blo 2139435 3210407 := bstep (se 1 (by rfl) ⟨2407805, by rfl⟩ : syracuseStep 3210407 = 4815611) B4815611
theorem B2140271 : Blo 2139435 2140271 := bstep (se 1 (by rfl) ⟨1605203, by rfl⟩ : syracuseStep 2140271 = 3210407) B3210407
theorem B3210413 : Blo 2139435 3210413 := bbase (se 3 (by rfl) ⟨601952, by rfl⟩ : syracuseStep 3210413 = 1203905) (by norm_num)
theorem B2140275 : Blo 2139435 2140275 := bstep (se 1 (by rfl) ⟨1605206, by rfl⟩ : syracuseStep 2140275 = 3210413) B3210413
theorem B4815629 : Blo 2139435 4815629 := bbase (se 3 (by rfl) ⟨902930, by rfl⟩ : syracuseStep 4815629 = 1805861) (by norm_num)
theorem B3210419 : Blo 2139435 3210419 := bstep (se 1 (by rfl) ⟨2407814, by rfl⟩ : syracuseStep 3210419 = 4815629) B4815629
theorem B2140279 : Blo 2139435 2140279 := bstep (se 1 (by rfl) ⟨1605209, by rfl⟩ : syracuseStep 2140279 = 3210419) B3210419
theorem B2708797 : Blo 2139435 2708797 := bbase (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) (by norm_num)
theorem B3611729 : Blo 2139435 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B2407819 : Blo 2139435 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B3210425 : Blo 2139435 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B2140283 : Blo 2139435 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B3661013 : Blo 2139435 3661013 := bbase (se 7 (by rfl) ⟨42902, by rfl⟩ : syracuseStep 3661013 = 85805) (by norm_num)
theorem B2440675 : Blo 2139435 2440675 := bstep (se 1 (by rfl) ⟨1830506, by rfl⟩ : syracuseStep 2440675 = 3661013) B3661013
theorem B13016933 : Blo 2139435 13016933 := bstep (se 4 (by rfl) ⟨1220337, by rfl⟩ : syracuseStep 13016933 = 2440675) B2440675
theorem B8677955 : Blo 2139435 8677955 := bstep (se 1 (by rfl) ⟨6508466, by rfl⟩ : syracuseStep 8677955 = 13016933) B13016933
theorem B23141213 : Blo 2139435 23141213 := bstep (se 3 (by rfl) ⟨4338977, by rfl⟩ : syracuseStep 23141213 = 8677955) B8677955
theorem B15427475 : Blo 2139435 15427475 := bstep (se 1 (by rfl) ⟨11570606, by rfl⟩ : syracuseStep 15427475 = 23141213) B23141213
theorem B10284983 : Blo 2139435 10284983 := bstep (se 1 (by rfl) ⟨7713737, by rfl⟩ : syracuseStep 10284983 = 15427475) B15427475
theorem B6856655 : Blo 2139435 6856655 := bstep (se 1 (by rfl) ⟨5142491, by rfl⟩ : syracuseStep 6856655 = 10284983) B10284983
theorem B18284413 : Blo 2139435 18284413 := bstep (se 3 (by rfl) ⟨3428327, by rfl⟩ : syracuseStep 18284413 = 6856655) B6856655
theorem B24379217 : Blo 2139435 24379217 := bstep (se 2 (by rfl) ⟨9142206, by rfl⟩ : syracuseStep 24379217 = 18284413) B18284413
theorem B16252811 : Blo 2139435 16252811 := bstep (se 1 (by rfl) ⟨12189608, by rfl⟩ : syracuseStep 16252811 = 24379217) B24379217
theorem B10835207 : Blo 2139435 10835207 := bstep (se 1 (by rfl) ⟨8126405, by rfl⟩ : syracuseStep 10835207 = 16252811) B16252811
theorem B7223471 : Blo 2139435 7223471 := bstep (se 1 (by rfl) ⟨5417603, by rfl⟩ : syracuseStep 7223471 = 10835207) B10835207
theorem B4815647 : Blo 2139435 4815647 := bstep (se 1 (by rfl) ⟨3611735, by rfl⟩ : syracuseStep 4815647 = 7223471) B7223471
theorem B3210431 : Blo 2139435 3210431 := bstep (se 1 (by rfl) ⟨2407823, by rfl⟩ : syracuseStep 3210431 = 4815647) B4815647
theorem B2140287 : Blo 2139435 2140287 := bstep (se 1 (by rfl) ⟨1605215, by rfl⟩ : syracuseStep 2140287 = 3210431) B3210431
theorem B3210437 : Blo 2139435 3210437 := bbase (se 4 (by rfl) ⟨300978, by rfl⟩ : syracuseStep 3210437 = 601957) (by norm_num)
theorem B2140291 : Blo 2139435 2140291 := bstep (se 1 (by rfl) ⟨1605218, by rfl⟩ : syracuseStep 2140291 = 3210437) B3210437
theorem B3611749 : Blo 2139435 3611749 := bbase (se 4 (by rfl) ⟨338601, by rfl⟩ : syracuseStep 3611749 = 677203) (by norm_num)
theorem B4815665 : Blo 2139435 4815665 := bstep (se 2 (by rfl) ⟨1805874, by rfl⟩ : syracuseStep 4815665 = 3611749) B3611749
theorem B3210443 : Blo 2139435 3210443 := bstep (se 1 (by rfl) ⟨2407832, by rfl⟩ : syracuseStep 3210443 = 4815665) B4815665
theorem B2140295 : Blo 2139435 2140295 := bstep (se 1 (by rfl) ⟨1605221, by rfl⟩ : syracuseStep 2140295 = 3210443) B3210443
theorem B2407837 : Blo 2139435 2407837 := bbase (se 3 (by rfl) ⟨451469, by rfl⟩ : syracuseStep 2407837 = 902939) (by norm_num)
theorem B3210449 : Blo 2139435 3210449 := bstep (se 2 (by rfl) ⟨1203918, by rfl⟩ : syracuseStep 3210449 = 2407837) B2407837
theorem B2140299 : Blo 2139435 2140299 := bstep (se 1 (by rfl) ⟨1605224, by rfl⟩ : syracuseStep 2140299 = 3210449) B3210449
theorem B7223525 : Blo 2139435 7223525 := bbase (se 4 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 7223525 = 1354411) (by norm_num)
theorem B4815683 : Blo 2139435 4815683 := bstep (se 1 (by rfl) ⟨3611762, by rfl⟩ : syracuseStep 4815683 = 7223525) B7223525
theorem B3210455 : Blo 2139435 3210455 := bstep (se 1 (by rfl) ⟨2407841, by rfl⟩ : syracuseStep 3210455 = 4815683) B4815683
theorem B2140303 : Blo 2139435 2140303 := bstep (se 1 (by rfl) ⟨1605227, by rfl⟩ : syracuseStep 2140303 = 3210455) B3210455
theorem B3210461 : Blo 2139435 3210461 := bbase (se 3 (by rfl) ⟨601961, by rfl⟩ : syracuseStep 3210461 = 1203923) (by norm_num)
theorem B2140307 : Blo 2139435 2140307 := bstep (se 1 (by rfl) ⟨1605230, by rfl⟩ : syracuseStep 2140307 = 3210461) B3210461
theorem B4815701 : Blo 2139435 4815701 := bbase (se 9 (by rfl) ⟨14108, by rfl⟩ : syracuseStep 4815701 = 28217) (by norm_num)
theorem B3210467 : Blo 2139435 3210467 := bstep (se 1 (by rfl) ⟨2407850, by rfl⟩ : syracuseStep 3210467 = 4815701) B4815701
theorem B2140311 : Blo 2139435 2140311 := bstep (se 1 (by rfl) ⟨1605233, by rfl⟩ : syracuseStep 2140311 = 3210467) B3210467
theorem B6094885 : Blo 2139435 6094885 := bbase (se 4 (by rfl) ⟨571395, by rfl⟩ : syracuseStep 6094885 = 1142791) (by norm_num)
theorem B8126513 : Blo 2139435 8126513 := bstep (se 2 (by rfl) ⟨3047442, by rfl⟩ : syracuseStep 8126513 = 6094885) B6094885
theorem B5417675 : Blo 2139435 5417675 := bstep (se 1 (by rfl) ⟨4063256, by rfl⟩ : syracuseStep 5417675 = 8126513) B8126513
theorem B3611783 : Blo 2139435 3611783 := bstep (se 1 (by rfl) ⟨2708837, by rfl⟩ : syracuseStep 3611783 = 5417675) B5417675
theorem B2407855 : Blo 2139435 2407855 := bstep (se 1 (by rfl) ⟨1805891, by rfl⟩ : syracuseStep 2407855 = 3611783) B3611783
theorem B3210473 : Blo 2139435 3210473 := bstep (se 2 (by rfl) ⟨1203927, by rfl⟩ : syracuseStep 3210473 = 2407855) B2407855
theorem B2140315 : Blo 2139435 2140315 := bstep (se 1 (by rfl) ⟨1605236, by rfl⟩ : syracuseStep 2140315 = 3210473) B3210473
theorem B9267077 : Blo 2139435 9267077 := bbase (se 4 (by rfl) ⟨868788, by rfl⟩ : syracuseStep 9267077 = 1737577) (by norm_num)
theorem B6178051 : Blo 2139435 6178051 := bstep (se 1 (by rfl) ⟨4633538, by rfl⟩ : syracuseStep 6178051 = 9267077) B9267077
theorem B32949605 : Blo 2139435 32949605 := bstep (se 4 (by rfl) ⟨3089025, by rfl⟩ : syracuseStep 32949605 = 6178051) B6178051
theorem B21966403 : Blo 2139435 21966403 := bstep (se 1 (by rfl) ⟨16474802, by rfl⟩ : syracuseStep 21966403 = 32949605) B32949605
theorem B29288537 : Blo 2139435 29288537 := bstep (se 2 (by rfl) ⟨10983201, by rfl⟩ : syracuseStep 29288537 = 21966403) B21966403
theorem B19525691 : Blo 2139435 19525691 := bstep (se 1 (by rfl) ⟨14644268, by rfl⟩ : syracuseStep 19525691 = 29288537) B29288537
theorem B13017127 : Blo 2139435 13017127 := bstep (se 1 (by rfl) ⟨9762845, by rfl⟩ : syracuseStep 13017127 = 19525691) B19525691
theorem B17356169 : Blo 2139435 17356169 := bstep (se 2 (by rfl) ⟨6508563, by rfl⟩ : syracuseStep 17356169 = 13017127) B13017127
theorem B11570779 : Blo 2139435 11570779 := bstep (se 1 (by rfl) ⟨8678084, by rfl⟩ : syracuseStep 11570779 = 17356169) B17356169
theorem B61710821 : Blo 2139435 61710821 := bstep (se 4 (by rfl) ⟨5785389, by rfl⟩ : syracuseStep 61710821 = 11570779) B11570779
theorem B41140547 : Blo 2139435 41140547 := bstep (se 1 (by rfl) ⟨30855410, by rfl⟩ : syracuseStep 41140547 = 61710821) B61710821
theorem B27427031 : Blo 2139435 27427031 := bstep (se 1 (by rfl) ⟨20570273, by rfl⟩ : syracuseStep 27427031 = 41140547) B41140547
theorem B18284687 : Blo 2139435 18284687 := bstep (se 1 (by rfl) ⟨13713515, by rfl⟩ : syracuseStep 18284687 = 27427031) B27427031
theorem B12189791 : Blo 2139435 12189791 := bstep (se 1 (by rfl) ⟨9142343, by rfl⟩ : syracuseStep 12189791 = 18284687) B18284687
theorem B8126527 : Blo 2139435 8126527 := bstep (se 1 (by rfl) ⟨6094895, by rfl⟩ : syracuseStep 8126527 = 12189791) B12189791
theorem B10835369 : Blo 2139435 10835369 := bstep (se 2 (by rfl) ⟨4063263, by rfl⟩ : syracuseStep 10835369 = 8126527) B8126527
theorem B7223579 : Blo 2139435 7223579 := bstep (se 1 (by rfl) ⟨5417684, by rfl⟩ : syracuseStep 7223579 = 10835369) B10835369
theorem B4815719 : Blo 2139435 4815719 := bstep (se 1 (by rfl) ⟨3611789, by rfl⟩ : syracuseStep 4815719 = 7223579) B7223579
theorem B3210479 : Blo 2139435 3210479 := bstep (se 1 (by rfl) ⟨2407859, by rfl⟩ : syracuseStep 3210479 = 4815719) B4815719
theorem B2140319 : Blo 2139435 2140319 := bstep (se 1 (by rfl) ⟨1605239, by rfl⟩ : syracuseStep 2140319 = 3210479) B3210479
theorem B3210485 : Blo 2139435 3210485 := bbase (se 5 (by rfl) ⟨150491, by rfl⟩ : syracuseStep 3210485 = 300983) (by norm_num)
theorem B2140323 : Blo 2139435 2140323 := bstep (se 1 (by rfl) ⟨1605242, by rfl⟩ : syracuseStep 2140323 = 3210485) B3210485
theorem B5944357 : Blo 2139435 5944357 := bbase (se 4 (by rfl) ⟨557283, by rfl⟩ : syracuseStep 5944357 = 1114567) (by norm_num)
theorem B7925809 : Blo 2139435 7925809 := bstep (se 2 (by rfl) ⟨2972178, by rfl⟩ : syracuseStep 7925809 = 5944357) B5944357
theorem B10567745 : Blo 2139435 10567745 := bstep (se 2 (by rfl) ⟨3962904, by rfl⟩ : syracuseStep 10567745 = 7925809) B7925809
theorem B7045163 : Blo 2139435 7045163 := bstep (se 1 (by rfl) ⟨5283872, by rfl⟩ : syracuseStep 7045163 = 10567745) B10567745
theorem B4696775 : Blo 2139435 4696775 := bstep (se 1 (by rfl) ⟨3522581, by rfl⟩ : syracuseStep 4696775 = 7045163) B7045163
theorem B3131183 : Blo 2139435 3131183 := bstep (se 1 (by rfl) ⟨2348387, by rfl⟩ : syracuseStep 3131183 = 4696775) B4696775
theorem B8349821 : Blo 2139435 8349821 := bstep (se 3 (by rfl) ⟨1565591, by rfl⟩ : syracuseStep 8349821 = 3131183) B3131183
theorem B5566547 : Blo 2139435 5566547 := bstep (se 1 (by rfl) ⟨4174910, by rfl⟩ : syracuseStep 5566547 = 8349821) B8349821
theorem B14844125 : Blo 2139435 14844125 := bstep (se 3 (by rfl) ⟨2783273, by rfl⟩ : syracuseStep 14844125 = 5566547) B5566547
theorem B39584333 : Blo 2139435 39584333 := bstep (se 3 (by rfl) ⟨7422062, by rfl⟩ : syracuseStep 39584333 = 14844125) B14844125
theorem B105558221 : Blo 2139435 105558221 := bstep (se 3 (by rfl) ⟨19792166, by rfl⟩ : syracuseStep 105558221 = 39584333) B39584333
theorem B70372147 : Blo 2139435 70372147 := bstep (se 1 (by rfl) ⟨52779110, by rfl⟩ : syracuseStep 70372147 = 105558221) B105558221
theorem B93829529 : Blo 2139435 93829529 := bstep (se 2 (by rfl) ⟨35186073, by rfl⟩ : syracuseStep 93829529 = 70372147) B70372147
theorem B62553019 : Blo 2139435 62553019 := bstep (se 1 (by rfl) ⟨46914764, by rfl⟩ : syracuseStep 62553019 = 93829529) B93829529
theorem B83404025 : Blo 2139435 83404025 := bstep (se 2 (by rfl) ⟨31276509, by rfl⟩ : syracuseStep 83404025 = 62553019) B62553019
theorem B55602683 : Blo 2139435 55602683 := bstep (se 1 (by rfl) ⟨41702012, by rfl⟩ : syracuseStep 55602683 = 83404025) B83404025
theorem B37068455 : Blo 2139435 37068455 := bstep (se 1 (by rfl) ⟨27801341, by rfl⟩ : syracuseStep 37068455 = 55602683) B55602683
theorem B24712303 : Blo 2139435 24712303 := bstep (se 1 (by rfl) ⟨18534227, by rfl⟩ : syracuseStep 24712303 = 37068455) B37068455
theorem B32949737 : Blo 2139435 32949737 := bstep (se 2 (by rfl) ⟨12356151, by rfl⟩ : syracuseStep 32949737 = 24712303) B24712303
theorem B21966491 : Blo 2139435 21966491 := bstep (se 1 (by rfl) ⟨16474868, by rfl⟩ : syracuseStep 21966491 = 32949737) B32949737
theorem B14644327 : Blo 2139435 14644327 := bstep (se 1 (by rfl) ⟨10983245, by rfl⟩ : syracuseStep 14644327 = 21966491) B21966491
theorem B19525769 : Blo 2139435 19525769 := bstep (se 2 (by rfl) ⟨7322163, by rfl⟩ : syracuseStep 19525769 = 14644327) B14644327
theorem B13017179 : Blo 2139435 13017179 := bstep (se 1 (by rfl) ⟨9762884, by rfl⟩ : syracuseStep 13017179 = 19525769) B19525769
theorem B8678119 : Blo 2139435 8678119 := bstep (se 1 (by rfl) ⟨6508589, by rfl⟩ : syracuseStep 8678119 = 13017179) B13017179
theorem B11570825 : Blo 2139435 11570825 := bstep (se 2 (by rfl) ⟨4339059, by rfl⟩ : syracuseStep 11570825 = 8678119) B8678119
theorem B7713883 : Blo 2139435 7713883 := bstep (se 1 (by rfl) ⟨5785412, by rfl⟩ : syracuseStep 7713883 = 11570825) B11570825
theorem B10285177 : Blo 2139435 10285177 := bstep (se 2 (by rfl) ⟨3856941, by rfl⟩ : syracuseStep 10285177 = 7713883) B7713883
theorem B13713569 : Blo 2139435 13713569 := bstep (se 2 (by rfl) ⟨5142588, by rfl⟩ : syracuseStep 13713569 = 10285177) B10285177
theorem B9142379 : Blo 2139435 9142379 := bstep (se 1 (by rfl) ⟨6856784, by rfl⟩ : syracuseStep 9142379 = 13713569) B13713569
theorem B6094919 : Blo 2139435 6094919 := bstep (se 1 (by rfl) ⟨4571189, by rfl⟩ : syracuseStep 6094919 = 9142379) B9142379
theorem B4063279 : Blo 2139435 4063279 := bstep (se 1 (by rfl) ⟨3047459, by rfl⟩ : syracuseStep 4063279 = 6094919) B6094919
theorem B5417705 : Blo 2139435 5417705 := bstep (se 2 (by rfl) ⟨2031639, by rfl⟩ : syracuseStep 5417705 = 4063279) B4063279
theorem B3611803 : Blo 2139435 3611803 := bstep (se 1 (by rfl) ⟨2708852, by rfl⟩ : syracuseStep 3611803 = 5417705) B5417705
theorem B4815737 : Blo 2139435 4815737 := bstep (se 2 (by rfl) ⟨1805901, by rfl⟩ : syracuseStep 4815737 = 3611803) B3611803
theorem B3210491 : Blo 2139435 3210491 := bstep (se 1 (by rfl) ⟨2407868, by rfl⟩ : syracuseStep 3210491 = 4815737) B4815737
theorem B2140327 : Blo 2139435 2140327 := bstep (se 1 (by rfl) ⟨1605245, by rfl⟩ : syracuseStep 2140327 = 3210491) B3210491
theorem B2407873 : Blo 2139435 2407873 := bbase (se 2 (by rfl) ⟨902952, by rfl⟩ : syracuseStep 2407873 = 1805905) (by norm_num)
theorem B3210497 : Blo 2139435 3210497 := bstep (se 2 (by rfl) ⟨1203936, by rfl⟩ : syracuseStep 3210497 = 2407873) B2407873
theorem B2140331 : Blo 2139435 2140331 := bstep (se 1 (by rfl) ⟨1605248, by rfl⟩ : syracuseStep 2140331 = 3210497) B3210497
theorem B5417725 : Blo 2139435 5417725 := bbase (se 3 (by rfl) ⟨1015823, by rfl⟩ : syracuseStep 5417725 = 2031647) (by norm_num)
theorem B7223633 : Blo 2139435 7223633 := bstep (se 2 (by rfl) ⟨2708862, by rfl⟩ : syracuseStep 7223633 = 5417725) B5417725
theorem B4815755 : Blo 2139435 4815755 := bstep (se 1 (by rfl) ⟨3611816, by rfl⟩ : syracuseStep 4815755 = 7223633) B7223633
theorem B3210503 : Blo 2139435 3210503 := bstep (se 1 (by rfl) ⟨2407877, by rfl⟩ : syracuseStep 3210503 = 4815755) B4815755
theorem B2140335 : Blo 2139435 2140335 := bstep (se 1 (by rfl) ⟨1605251, by rfl⟩ : syracuseStep 2140335 = 3210503) B3210503
theorem B3210509 : Blo 2139435 3210509 := bbase (se 3 (by rfl) ⟨601970, by rfl⟩ : syracuseStep 3210509 = 1203941) (by norm_num)
theorem B2140339 : Blo 2139435 2140339 := bstep (se 1 (by rfl) ⟨1605254, by rfl⟩ : syracuseStep 2140339 = 3210509) B3210509
theorem B4815773 : Blo 2139435 4815773 := bbase (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) (by norm_num)
theorem B3210515 : Blo 2139435 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B2140343 : Blo 2139435 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B3611837 : Blo 2139435 3611837 := bbase (se 3 (by rfl) ⟨677219, by rfl⟩ : syracuseStep 3611837 = 1354439) (by norm_num)
theorem B2407891 : Blo 2139435 2407891 := bstep (se 1 (by rfl) ⟨1805918, by rfl⟩ : syracuseStep 2407891 = 3611837) B3611837
theorem B3210521 : Blo 2139435 3210521 := bstep (se 2 (by rfl) ⟨1203945, by rfl⟩ : syracuseStep 3210521 = 2407891) B2407891
theorem B2140347 : Blo 2139435 2140347 := bstep (se 1 (by rfl) ⟨1605260, by rfl⟩ : syracuseStep 2140347 = 3210521) B3210521
theorem B12189973 : Blo 2139435 12189973 := bbase (se 6 (by rfl) ⟨285702, by rfl⟩ : syracuseStep 12189973 = 571405) (by norm_num)
theorem B16253297 : Blo 2139435 16253297 := bstep (se 2 (by rfl) ⟨6094986, by rfl⟩ : syracuseStep 16253297 = 12189973) B12189973
theorem B10835531 : Blo 2139435 10835531 := bstep (se 1 (by rfl) ⟨8126648, by rfl⟩ : syracuseStep 10835531 = 16253297) B16253297
theorem B7223687 : Blo 2139435 7223687 := bstep (se 1 (by rfl) ⟨5417765, by rfl⟩ : syracuseStep 7223687 = 10835531) B10835531
theorem B4815791 : Blo 2139435 4815791 := bstep (se 1 (by rfl) ⟨3611843, by rfl⟩ : syracuseStep 4815791 = 7223687) B7223687
theorem B3210527 : Blo 2139435 3210527 := bstep (se 1 (by rfl) ⟨2407895, by rfl⟩ : syracuseStep 3210527 = 4815791) B4815791
theorem B2140351 : Blo 2139435 2140351 := bstep (se 1 (by rfl) ⟨1605263, by rfl⟩ : syracuseStep 2140351 = 3210527) B3210527
theorem B3210533 : Blo 2139435 3210533 := bbase (se 4 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 3210533 = 601975) (by norm_num)
theorem B2140355 : Blo 2139435 2140355 := bstep (se 1 (by rfl) ⟨1605266, by rfl⟩ : syracuseStep 2140355 = 3210533) B3210533
theorem B2708893 : Blo 2139435 2708893 := bbase (se 3 (by rfl) ⟨507917, by rfl⟩ : syracuseStep 2708893 = 1015835) (by norm_num)
theorem B3611857 : Blo 2139435 3611857 := bstep (se 2 (by rfl) ⟨1354446, by rfl⟩ : syracuseStep 3611857 = 2708893) B2708893
theorem B4815809 : Blo 2139435 4815809 := bstep (se 2 (by rfl) ⟨1805928, by rfl⟩ : syracuseStep 4815809 = 3611857) B3611857
theorem B3210539 : Blo 2139435 3210539 := bstep (se 1 (by rfl) ⟨2407904, by rfl⟩ : syracuseStep 3210539 = 4815809) B4815809
theorem B2140359 : Blo 2139435 2140359 := bstep (se 1 (by rfl) ⟨1605269, by rfl⟩ : syracuseStep 2140359 = 3210539) B3210539
theorem B2407909 : Blo 2139435 2407909 := bbase (se 4 (by rfl) ⟨225741, by rfl⟩ : syracuseStep 2407909 = 451483) (by norm_num)
theorem B3210545 : Blo 2139435 3210545 := bstep (se 2 (by rfl) ⟨1203954, by rfl⟩ : syracuseStep 3210545 = 2407909) B2407909
theorem B2140363 : Blo 2139435 2140363 := bstep (se 1 (by rfl) ⟨1605272, by rfl⟩ : syracuseStep 2140363 = 3210545) B3210545
theorem B5142685 : Blo 2139435 5142685 := bbase (se 3 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 5142685 = 1928507) (by norm_num)
theorem B6856913 : Blo 2139435 6856913 := bstep (se 2 (by rfl) ⟨2571342, by rfl⟩ : syracuseStep 6856913 = 5142685) B5142685
theorem B4571275 : Blo 2139435 4571275 := bstep (se 1 (by rfl) ⟨3428456, by rfl⟩ : syracuseStep 4571275 = 6856913) B6856913
theorem B6095033 : Blo 2139435 6095033 := bstep (se 2 (by rfl) ⟨2285637, by rfl⟩ : syracuseStep 6095033 = 4571275) B4571275
theorem B4063355 : Blo 2139435 4063355 := bstep (se 1 (by rfl) ⟨3047516, by rfl⟩ : syracuseStep 4063355 = 6095033) B6095033
theorem B2708903 : Blo 2139435 2708903 := bstep (se 1 (by rfl) ⟨2031677, by rfl⟩ : syracuseStep 2708903 = 4063355) B4063355
theorem B7223741 : Blo 2139435 7223741 := bstep (se 3 (by rfl) ⟨1354451, by rfl⟩ : syracuseStep 7223741 = 2708903) B2708903
theorem B4815827 : Blo 2139435 4815827 := bstep (se 1 (by rfl) ⟨3611870, by rfl⟩ : syracuseStep 4815827 = 7223741) B7223741
theorem B3210551 : Blo 2139435 3210551 := bstep (se 1 (by rfl) ⟨2407913, by rfl⟩ : syracuseStep 3210551 = 4815827) B4815827
theorem B2140367 : Blo 2139435 2140367 := bstep (se 1 (by rfl) ⟨1605275, by rfl⟩ : syracuseStep 2140367 = 3210551) B3210551
theorem B3210557 : Blo 2139435 3210557 := bbase (se 3 (by rfl) ⟨601979, by rfl⟩ : syracuseStep 3210557 = 1203959) (by norm_num)
theorem B2140371 : Blo 2139435 2140371 := bstep (se 1 (by rfl) ⟨1605278, by rfl⟩ : syracuseStep 2140371 = 3210557) B3210557
theorem B4815845 : Blo 2139435 4815845 := bbase (se 4 (by rfl) ⟨451485, by rfl⟩ : syracuseStep 4815845 = 902971) (by norm_num)
theorem B3210563 : Blo 2139435 3210563 := bstep (se 1 (by rfl) ⟨2407922, by rfl⟩ : syracuseStep 3210563 = 4815845) B4815845
theorem B2140375 : Blo 2139435 2140375 := bstep (se 1 (by rfl) ⟨1605281, by rfl⟩ : syracuseStep 2140375 = 3210563) B3210563
theorem B5417837 : Blo 2139435 5417837 := bbase (se 3 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 5417837 = 2031689) (by norm_num)
theorem B3611891 : Blo 2139435 3611891 := bstep (se 1 (by rfl) ⟨2708918, by rfl⟩ : syracuseStep 3611891 = 5417837) B5417837
theorem B2407927 : Blo 2139435 2407927 := bstep (se 1 (by rfl) ⟨1805945, by rfl⟩ : syracuseStep 2407927 = 3611891) B3611891
theorem B3210569 : Blo 2139435 3210569 := bstep (se 2 (by rfl) ⟨1203963, by rfl⟩ : syracuseStep 3210569 = 2407927) B2407927
theorem B2140379 : Blo 2139435 2140379 := bstep (se 1 (by rfl) ⟨1605284, by rfl⟩ : syracuseStep 2140379 = 3210569) B3210569
theorem B4571309 : Blo 2139435 4571309 := bbase (se 3 (by rfl) ⟨857120, by rfl⟩ : syracuseStep 4571309 = 1714241) (by norm_num)
theorem B3047539 : Blo 2139435 3047539 := bstep (se 1 (by rfl) ⟨2285654, by rfl⟩ : syracuseStep 3047539 = 4571309) B4571309
theorem B4063385 : Blo 2139435 4063385 := bstep (se 2 (by rfl) ⟨1523769, by rfl⟩ : syracuseStep 4063385 = 3047539) B3047539
theorem B10835693 : Blo 2139435 10835693 := bstep (se 3 (by rfl) ⟨2031692, by rfl⟩ : syracuseStep 10835693 = 4063385) B4063385
theorem B7223795 : Blo 2139435 7223795 := bstep (se 1 (by rfl) ⟨5417846, by rfl⟩ : syracuseStep 7223795 = 10835693) B10835693
theorem B4815863 : Blo 2139435 4815863 := bstep (se 1 (by rfl) ⟨3611897, by rfl⟩ : syracuseStep 4815863 = 7223795) B7223795
theorem B3210575 : Blo 2139435 3210575 := bstep (se 1 (by rfl) ⟨2407931, by rfl⟩ : syracuseStep 3210575 = 4815863) B4815863
theorem B2140383 : Blo 2139435 2140383 := bstep (se 1 (by rfl) ⟨1605287, by rfl⟩ : syracuseStep 2140383 = 3210575) B3210575
theorem B3210581 : Blo 2139435 3210581 := bbase (se 11 (by rfl) ⟨2351, by rfl⟩ : syracuseStep 3210581 = 4703) (by norm_num)
theorem B2140387 : Blo 2139435 2140387 := bstep (se 1 (by rfl) ⟨1605290, by rfl⟩ : syracuseStep 2140387 = 3210581) B3210581
theorem B6950549 : Blo 2139435 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B4633699 : Blo 2139435 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B6178265 : Blo 2139435 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B4118843 : Blo 2139435 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B2745895 : Blo 2139435 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B3661193 : Blo 2139435 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B2440795 : Blo 2139435 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B3254393 : Blo 2139435 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B2169595 : Blo 2139435 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B11571173 : Blo 2139435 11571173 := bstep (se 4 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 11571173 = 2169595) B2169595
theorem B7714115 : Blo 2139435 7714115 := bstep (se 1 (by rfl) ⟨5785586, by rfl⟩ : syracuseStep 7714115 = 11571173) B11571173
theorem B5142743 : Blo 2139435 5142743 := bstep (se 1 (by rfl) ⟨3857057, by rfl⟩ : syracuseStep 5142743 = 7714115) B7714115
theorem B3428495 : Blo 2139435 3428495 := bstep (se 1 (by rfl) ⟨2571371, by rfl⟩ : syracuseStep 3428495 = 5142743) B5142743
theorem B2285663 : Blo 2139435 2285663 := bstep (se 1 (by rfl) ⟨1714247, by rfl⟩ : syracuseStep 2285663 = 3428495) B3428495
theorem B6095101 : Blo 2139435 6095101 := bstep (se 3 (by rfl) ⟨1142831, by rfl⟩ : syracuseStep 6095101 = 2285663) B2285663
theorem B8126801 : Blo 2139435 8126801 := bstep (se 2 (by rfl) ⟨3047550, by rfl⟩ : syracuseStep 8126801 = 6095101) B6095101
theorem B5417867 : Blo 2139435 5417867 := bstep (se 1 (by rfl) ⟨4063400, by rfl⟩ : syracuseStep 5417867 = 8126801) B8126801
theorem B3611911 : Blo 2139435 3611911 := bstep (se 1 (by rfl) ⟨2708933, by rfl⟩ : syracuseStep 3611911 = 5417867) B5417867
theorem B4815881 : Blo 2139435 4815881 := bstep (se 2 (by rfl) ⟨1805955, by rfl⟩ : syracuseStep 4815881 = 3611911) B3611911
theorem B3210587 : Blo 2139435 3210587 := bstep (se 1 (by rfl) ⟨2407940, by rfl⟩ : syracuseStep 3210587 = 4815881) B4815881
theorem B2140391 : Blo 2139435 2140391 := bstep (se 1 (by rfl) ⟨1605293, by rfl⟩ : syracuseStep 2140391 = 3210587) B3210587
theorem B2407945 : Blo 2139435 2407945 := bbase (se 2 (by rfl) ⟨902979, by rfl⟩ : syracuseStep 2407945 = 1805959) (by norm_num)
theorem B3210593 : Blo 2139435 3210593 := bstep (se 2 (by rfl) ⟨1203972, by rfl⟩ : syracuseStep 3210593 = 2407945) B2407945
theorem B2140395 : Blo 2139435 2140395 := bstep (se 1 (by rfl) ⟨1605296, by rfl⟩ : syracuseStep 2140395 = 3210593) B3210593
theorem B4339205 : Blo 2139435 4339205 := bbase (se 4 (by rfl) ⟨406800, by rfl⟩ : syracuseStep 4339205 = 813601) (by norm_num)
theorem B2892803 : Blo 2139435 2892803 := bstep (se 1 (by rfl) ⟨2169602, by rfl⟩ : syracuseStep 2892803 = 4339205) B4339205
theorem B30856565 : Blo 2139435 30856565 := bstep (se 5 (by rfl) ⟨1446401, by rfl⟩ : syracuseStep 30856565 = 2892803) B2892803
theorem B20571043 : Blo 2139435 20571043 := bstep (se 1 (by rfl) ⟨15428282, by rfl⟩ : syracuseStep 20571043 = 30856565) B30856565
theorem B27428057 : Blo 2139435 27428057 := bstep (se 2 (by rfl) ⟨10285521, by rfl⟩ : syracuseStep 27428057 = 20571043) B20571043
theorem B18285371 : Blo 2139435 18285371 := bstep (se 1 (by rfl) ⟨13714028, by rfl⟩ : syracuseStep 18285371 = 27428057) B27428057
theorem B12190247 : Blo 2139435 12190247 := bstep (se 1 (by rfl) ⟨9142685, by rfl⟩ : syracuseStep 12190247 = 18285371) B18285371
theorem B8126831 : Blo 2139435 8126831 := bstep (se 1 (by rfl) ⟨6095123, by rfl⟩ : syracuseStep 8126831 = 12190247) B12190247
theorem B5417887 : Blo 2139435 5417887 := bstep (se 1 (by rfl) ⟨4063415, by rfl⟩ : syracuseStep 5417887 = 8126831) B8126831
theorem B7223849 : Blo 2139435 7223849 := bstep (se 2 (by rfl) ⟨2708943, by rfl⟩ : syracuseStep 7223849 = 5417887) B5417887
theorem B4815899 : Blo 2139435 4815899 := bstep (se 1 (by rfl) ⟨3611924, by rfl⟩ : syracuseStep 4815899 = 7223849) B7223849
theorem B3210599 : Blo 2139435 3210599 := bstep (se 1 (by rfl) ⟨2407949, by rfl⟩ : syracuseStep 3210599 = 4815899) B4815899
theorem B2140399 : Blo 2139435 2140399 := bstep (se 1 (by rfl) ⟨1605299, by rfl⟩ : syracuseStep 2140399 = 3210599) B3210599
theorem B3210605 : Blo 2139435 3210605 := bbase (se 3 (by rfl) ⟨601988, by rfl⟩ : syracuseStep 3210605 = 1203977) (by norm_num)
theorem B2140403 : Blo 2139435 2140403 := bstep (se 1 (by rfl) ⟨1605302, by rfl⟩ : syracuseStep 2140403 = 3210605) B3210605
theorem B4815917 : Blo 2139435 4815917 := bbase (se 3 (by rfl) ⟨902984, by rfl⟩ : syracuseStep 4815917 = 1805969) (by norm_num)
theorem B3210611 : Blo 2139435 3210611 := bstep (se 1 (by rfl) ⟨2407958, by rfl⟩ : syracuseStep 3210611 = 4815917) B4815917
theorem B2140407 : Blo 2139435 2140407 := bstep (se 1 (by rfl) ⟨1605305, by rfl⟩ : syracuseStep 2140407 = 3210611) B3210611
theorem B7322453 : Blo 2139435 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B4881635 : Blo 2139435 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B3254423 : Blo 2139435 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B8678461 : Blo 2139435 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B11571281 : Blo 2139435 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B7714187 : Blo 2139435 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B5142791 : Blo 2139435 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B13714109 : Blo 2139435 13714109 := bstep (se 3 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 13714109 = 5142791) B5142791
theorem B9142739 : Blo 2139435 9142739 := bstep (se 1 (by rfl) ⟨6857054, by rfl⟩ : syracuseStep 9142739 = 13714109) B13714109
theorem B6095159 : Blo 2139435 6095159 := bstep (se 1 (by rfl) ⟨4571369, by rfl⟩ : syracuseStep 6095159 = 9142739) B9142739
theorem B4063439 : Blo 2139435 4063439 := bstep (se 1 (by rfl) ⟨3047579, by rfl⟩ : syracuseStep 4063439 = 6095159) B6095159
theorem B2708959 : Blo 2139435 2708959 := bstep (se 1 (by rfl) ⟨2031719, by rfl⟩ : syracuseStep 2708959 = 4063439) B4063439
theorem B3611945 : Blo 2139435 3611945 := bstep (se 2 (by rfl) ⟨1354479, by rfl⟩ : syracuseStep 3611945 = 2708959) B2708959
theorem B2407963 : Blo 2139435 2407963 := bstep (se 1 (by rfl) ⟨1805972, by rfl⟩ : syracuseStep 2407963 = 3611945) B3611945
theorem B3210617 : Blo 2139435 3210617 := bstep (se 2 (by rfl) ⟨1203981, by rfl⟩ : syracuseStep 3210617 = 2407963) B2407963
theorem B2140411 : Blo 2139435 2140411 := bstep (se 1 (by rfl) ⟨1605308, by rfl⟩ : syracuseStep 2140411 = 3210617) B3210617
theorem B17356949 : Blo 2139435 17356949 := bbase (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) (by norm_num)
theorem B11571299 : Blo 2139435 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B7714199 : Blo 2139435 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B5142799 : Blo 2139435 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B6857065 : Blo 2139435 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B36571013 : Blo 2139435 36571013 := bstep (se 4 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 36571013 = 6857065) B6857065
theorem B24380675 : Blo 2139435 24380675 := bstep (se 1 (by rfl) ⟨18285506, by rfl⟩ : syracuseStep 24380675 = 36571013) B36571013
theorem B16253783 : Blo 2139435 16253783 := bstep (se 1 (by rfl) ⟨12190337, by rfl⟩ : syracuseStep 16253783 = 24380675) B24380675
theorem B10835855 : Blo 2139435 10835855 := bstep (se 1 (by rfl) ⟨8126891, by rfl⟩ : syracuseStep 10835855 = 16253783) B16253783
theorem B7223903 : Blo 2139435 7223903 := bstep (se 1 (by rfl) ⟨5417927, by rfl⟩ : syracuseStep 7223903 = 10835855) B10835855
theorem B4815935 : Blo 2139435 4815935 := bstep (se 1 (by rfl) ⟨3611951, by rfl⟩ : syracuseStep 4815935 = 7223903) B7223903
theorem B3210623 : Blo 2139435 3210623 := bstep (se 1 (by rfl) ⟨2407967, by rfl⟩ : syracuseStep 3210623 = 4815935) B4815935
theorem B2140415 : Blo 2139435 2140415 := bstep (se 1 (by rfl) ⟨1605311, by rfl⟩ : syracuseStep 2140415 = 3210623) B3210623
theorem B3210629 : Blo 2139435 3210629 := bbase (se 4 (by rfl) ⟨300996, by rfl⟩ : syracuseStep 3210629 = 601993) (by norm_num)
theorem B2140419 : Blo 2139435 2140419 := bstep (se 1 (by rfl) ⟨1605314, by rfl⟩ : syracuseStep 2140419 = 3210629) B3210629
theorem B3611965 : Blo 2139435 3611965 := bbase (se 3 (by rfl) ⟨677243, by rfl⟩ : syracuseStep 3611965 = 1354487) (by norm_num)
theorem B4815953 : Blo 2139435 4815953 := bstep (se 2 (by rfl) ⟨1805982, by rfl⟩ : syracuseStep 4815953 = 3611965) B3611965
theorem B3210635 : Blo 2139435 3210635 := bstep (se 1 (by rfl) ⟨2407976, by rfl⟩ : syracuseStep 3210635 = 4815953) B4815953
theorem B2140423 : Blo 2139435 2140423 := bstep (se 1 (by rfl) ⟨1605317, by rfl⟩ : syracuseStep 2140423 = 3210635) B3210635
theorem B2407981 : Blo 2139435 2407981 := bbase (se 3 (by rfl) ⟨451496, by rfl⟩ : syracuseStep 2407981 = 902993) (by norm_num)
theorem B3210641 : Blo 2139435 3210641 := bstep (se 2 (by rfl) ⟨1203990, by rfl⟩ : syracuseStep 3210641 = 2407981) B2407981
theorem B2140427 : Blo 2139435 2140427 := bstep (se 1 (by rfl) ⟨1605320, by rfl⟩ : syracuseStep 2140427 = 3210641) B3210641
theorem B7223957 : Blo 2139435 7223957 := bbase (se 6 (by rfl) ⟨169311, by rfl⟩ : syracuseStep 7223957 = 338623) (by norm_num)
theorem B4815971 : Blo 2139435 4815971 := bstep (se 1 (by rfl) ⟨3611978, by rfl⟩ : syracuseStep 4815971 = 7223957) B7223957
theorem B3210647 : Blo 2139435 3210647 := bstep (se 1 (by rfl) ⟨2407985, by rfl⟩ : syracuseStep 3210647 = 4815971) B4815971
theorem B2140431 : Blo 2139435 2140431 := bstep (se 1 (by rfl) ⟨1605323, by rfl⟩ : syracuseStep 2140431 = 3210647) B3210647
theorem B3210653 : Blo 2139435 3210653 := bbase (se 3 (by rfl) ⟨601997, by rfl⟩ : syracuseStep 3210653 = 1203995) (by norm_num)
theorem B2140435 : Blo 2139435 2140435 := bstep (se 1 (by rfl) ⟨1605326, by rfl⟩ : syracuseStep 2140435 = 3210653) B3210653
theorem B4815989 : Blo 2139435 4815989 := bbase (se 5 (by rfl) ⟨225749, by rfl⟩ : syracuseStep 4815989 = 451499) (by norm_num)
theorem B3210659 : Blo 2139435 3210659 := bstep (se 1 (by rfl) ⟨2407994, by rfl⟩ : syracuseStep 3210659 = 4815989) B4815989
theorem B2140439 : Blo 2139435 2140439 := bstep (se 1 (by rfl) ⟨1605329, by rfl⟩ : syracuseStep 2140439 = 3210659) B3210659
theorem B18285749 : Blo 2139435 18285749 := bbase (se 5 (by rfl) ⟨857144, by rfl⟩ : syracuseStep 18285749 = 1714289) (by norm_num)
theorem B12190499 : Blo 2139435 12190499 := bstep (se 1 (by rfl) ⟨9142874, by rfl⟩ : syracuseStep 12190499 = 18285749) B18285749
theorem B8126999 : Blo 2139435 8126999 := bstep (se 1 (by rfl) ⟨6095249, by rfl⟩ : syracuseStep 8126999 = 12190499) B12190499
theorem B5417999 : Blo 2139435 5417999 := bstep (se 1 (by rfl) ⟨4063499, by rfl⟩ : syracuseStep 5417999 = 8126999) B8126999
theorem B3611999 : Blo 2139435 3611999 := bstep (se 1 (by rfl) ⟨2708999, by rfl⟩ : syracuseStep 3611999 = 5417999) B5417999
theorem B2407999 : Blo 2139435 2407999 := bstep (se 1 (by rfl) ⟨1805999, by rfl⟩ : syracuseStep 2407999 = 3611999) B3611999
theorem B3210665 : Blo 2139435 3210665 := bstep (se 2 (by rfl) ⟨1203999, by rfl⟩ : syracuseStep 3210665 = 2407999) B2407999
theorem B2140443 : Blo 2139435 2140443 := bstep (se 1 (by rfl) ⟨1605332, by rfl⟩ : syracuseStep 2140443 = 3210665) B3210665
theorem B8127013 : Blo 2139435 8127013 := bbase (se 4 (by rfl) ⟨761907, by rfl⟩ : syracuseStep 8127013 = 1523815) (by norm_num)
theorem B10836017 : Blo 2139435 10836017 := bstep (se 2 (by rfl) ⟨4063506, by rfl⟩ : syracuseStep 10836017 = 8127013) B8127013
theorem B7224011 : Blo 2139435 7224011 := bstep (se 1 (by rfl) ⟨5418008, by rfl⟩ : syracuseStep 7224011 = 10836017) B10836017
theorem B4816007 : Blo 2139435 4816007 := bstep (se 1 (by rfl) ⟨3612005, by rfl⟩ : syracuseStep 4816007 = 7224011) B7224011
theorem B3210671 : Blo 2139435 3210671 := bstep (se 1 (by rfl) ⟨2408003, by rfl⟩ : syracuseStep 3210671 = 4816007) B4816007
theorem B2140447 : Blo 2139435 2140447 := bstep (se 1 (by rfl) ⟨1605335, by rfl⟩ : syracuseStep 2140447 = 3210671) B3210671
theorem B3210677 : Blo 2139435 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B2140451 : Blo 2139435 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B5418029 : Blo 2139435 5418029 := bbase (se 3 (by rfl) ⟨1015880, by rfl⟩ : syracuseStep 5418029 = 2031761) (by norm_num)
theorem B3612019 : Blo 2139435 3612019 := bstep (se 1 (by rfl) ⟨2709014, by rfl⟩ : syracuseStep 3612019 = 5418029) B5418029
theorem B4816025 : Blo 2139435 4816025 := bstep (se 2 (by rfl) ⟨1806009, by rfl⟩ : syracuseStep 4816025 = 3612019) B3612019
theorem B3210683 : Blo 2139435 3210683 := bstep (se 1 (by rfl) ⟨2408012, by rfl⟩ : syracuseStep 3210683 = 4816025) B4816025
theorem B2140455 : Blo 2139435 2140455 := bstep (se 1 (by rfl) ⟨1605341, by rfl⟩ : syracuseStep 2140455 = 3210683) B3210683
theorem B2408017 : Blo 2139435 2408017 := bbase (se 2 (by rfl) ⟨903006, by rfl⟩ : syracuseStep 2408017 = 1806013) (by norm_num)
theorem B3210689 : Blo 2139435 3210689 := bstep (se 2 (by rfl) ⟨1204008, by rfl⟩ : syracuseStep 3210689 = 2408017) B2408017
theorem B2140459 : Blo 2139435 2140459 := bstep (se 1 (by rfl) ⟨1605344, by rfl⟩ : syracuseStep 2140459 = 3210689) B3210689
theorem B3047653 : Blo 2139435 3047653 := bbase (se 4 (by rfl) ⟨285717, by rfl⟩ : syracuseStep 3047653 = 571435) (by norm_num)
theorem B4063537 : Blo 2139435 4063537 := bstep (se 2 (by rfl) ⟨1523826, by rfl⟩ : syracuseStep 4063537 = 3047653) B3047653
theorem B5418049 : Blo 2139435 5418049 := bstep (se 2 (by rfl) ⟨2031768, by rfl⟩ : syracuseStep 5418049 = 4063537) B4063537
theorem B7224065 : Blo 2139435 7224065 := bstep (se 2 (by rfl) ⟨2709024, by rfl⟩ : syracuseStep 7224065 = 5418049) B5418049
theorem B4816043 : Blo 2139435 4816043 := bstep (se 1 (by rfl) ⟨3612032, by rfl⟩ : syracuseStep 4816043 = 7224065) B7224065
theorem B3210695 : Blo 2139435 3210695 := bstep (se 1 (by rfl) ⟨2408021, by rfl⟩ : syracuseStep 3210695 = 4816043) B4816043
theorem B2140463 : Blo 2139435 2140463 := bstep (se 1 (by rfl) ⟨1605347, by rfl⟩ : syracuseStep 2140463 = 3210695) B3210695
theorem B3210701 : Blo 2139435 3210701 := bbase (se 3 (by rfl) ⟨602006, by rfl⟩ : syracuseStep 3210701 = 1204013) (by norm_num)
theorem B2140467 : Blo 2139435 2140467 := bstep (se 1 (by rfl) ⟨1605350, by rfl⟩ : syracuseStep 2140467 = 3210701) B3210701
theorem B4816061 : Blo 2139435 4816061 := bbase (se 3 (by rfl) ⟨903011, by rfl⟩ : syracuseStep 4816061 = 1806023) (by norm_num)
theorem B3210707 : Blo 2139435 3210707 := bstep (se 1 (by rfl) ⟨2408030, by rfl⟩ : syracuseStep 3210707 = 4816061) B4816061
theorem B2140471 : Blo 2139435 2140471 := bstep (se 1 (by rfl) ⟨1605353, by rfl⟩ : syracuseStep 2140471 = 3210707) B3210707
theorem B3612053 : Blo 2139435 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B2408035 : Blo 2139435 2408035 := bstep (se 1 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 2408035 = 3612053) B3612053
theorem B3210713 : Blo 2139435 3210713 := bstep (se 2 (by rfl) ⟨1204017, by rfl⟩ : syracuseStep 3210713 = 2408035) B2408035
theorem B2140475 : Blo 2139435 2140475 := bstep (se 1 (by rfl) ⟨1605356, by rfl⟩ : syracuseStep 2140475 = 3210713) B3210713
theorem B7819685 : Blo 2139435 7819685 := bbase (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) (by norm_num)
theorem B5213123 : Blo 2139435 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B3475415 : Blo 2139435 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B2316943 : Blo 2139435 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B12357029 : Blo 2139435 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B8238019 : Blo 2139435 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B10984025 : Blo 2139435 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B29290733 : Blo 2139435 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B19527155 : Blo 2139435 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B13018103 : Blo 2139435 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B8678735 : Blo 2139435 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B5785823 : Blo 2139435 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B3857215 : Blo 2139435 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B5142953 : Blo 2139435 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B13714541 : Blo 2139435 13714541 := bstep (se 3 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 13714541 = 5142953) B5142953
theorem B9143027 : Blo 2139435 9143027 := bstep (se 1 (by rfl) ⟨6857270, by rfl⟩ : syracuseStep 9143027 = 13714541) B13714541
theorem B6095351 : Blo 2139435 6095351 := bstep (se 1 (by rfl) ⟨4571513, by rfl⟩ : syracuseStep 6095351 = 9143027) B9143027
theorem B16254269 : Blo 2139435 16254269 := bstep (se 3 (by rfl) ⟨3047675, by rfl⟩ : syracuseStep 16254269 = 6095351) B6095351
theorem B10836179 : Blo 2139435 10836179 := bstep (se 1 (by rfl) ⟨8127134, by rfl⟩ : syracuseStep 10836179 = 16254269) B16254269
theorem B7224119 : Blo 2139435 7224119 := bstep (se 1 (by rfl) ⟨5418089, by rfl⟩ : syracuseStep 7224119 = 10836179) B10836179
theorem B4816079 : Blo 2139435 4816079 := bstep (se 1 (by rfl) ⟨3612059, by rfl⟩ : syracuseStep 4816079 = 7224119) B7224119
theorem B3210719 : Blo 2139435 3210719 := bstep (se 1 (by rfl) ⟨2408039, by rfl⟩ : syracuseStep 3210719 = 4816079) B4816079
theorem B2140479 : Blo 2139435 2140479 := bstep (se 1 (by rfl) ⟨1605359, by rfl⟩ : syracuseStep 2140479 = 3210719) B3210719
theorem B3210725 : Blo 2139435 3210725 := bbase (se 4 (by rfl) ⟨301005, by rfl⟩ : syracuseStep 3210725 = 602011) (by norm_num)
theorem B2140483 : Blo 2139435 2140483 := bstep (se 1 (by rfl) ⟨1605362, by rfl⟩ : syracuseStep 2140483 = 3210725) B3210725
theorem B20571893 : Blo 2139435 20571893 := bbase (se 5 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 20571893 = 1928615) (by norm_num)
theorem B13714595 : Blo 2139435 13714595 := bstep (se 1 (by rfl) ⟨10285946, by rfl⟩ : syracuseStep 13714595 = 20571893) B20571893
theorem B9143063 : Blo 2139435 9143063 := bstep (se 1 (by rfl) ⟨6857297, by rfl⟩ : syracuseStep 9143063 = 13714595) B13714595
theorem B6095375 : Blo 2139435 6095375 := bstep (se 1 (by rfl) ⟨4571531, by rfl⟩ : syracuseStep 6095375 = 9143063) B9143063
theorem B4063583 : Blo 2139435 4063583 := bstep (se 1 (by rfl) ⟨3047687, by rfl⟩ : syracuseStep 4063583 = 6095375) B6095375
theorem B2709055 : Blo 2139435 2709055 := bstep (se 1 (by rfl) ⟨2031791, by rfl⟩ : syracuseStep 2709055 = 4063583) B4063583
theorem B3612073 : Blo 2139435 3612073 := bstep (se 2 (by rfl) ⟨1354527, by rfl⟩ : syracuseStep 3612073 = 2709055) B2709055
theorem B4816097 : Blo 2139435 4816097 := bstep (se 2 (by rfl) ⟨1806036, by rfl⟩ : syracuseStep 4816097 = 3612073) B3612073
theorem B3210731 : Blo 2139435 3210731 := bstep (se 1 (by rfl) ⟨2408048, by rfl⟩ : syracuseStep 3210731 = 4816097) B4816097
theorem B2140487 : Blo 2139435 2140487 := bstep (se 1 (by rfl) ⟨1605365, by rfl⟩ : syracuseStep 2140487 = 3210731) B3210731
theorem B2408053 : Blo 2139435 2408053 := bbase (se 5 (by rfl) ⟨112877, by rfl⟩ : syracuseStep 2408053 = 225755) (by norm_num)
theorem B3210737 : Blo 2139435 3210737 := bstep (se 2 (by rfl) ⟨1204026, by rfl⟩ : syracuseStep 3210737 = 2408053) B2408053
theorem B2140491 : Blo 2139435 2140491 := bstep (se 1 (by rfl) ⟨1605368, by rfl⟩ : syracuseStep 2140491 = 3210737) B3210737
theorem B2709065 : Blo 2139435 2709065 := bbase (se 2 (by rfl) ⟨1015899, by rfl⟩ : syracuseStep 2709065 = 2031799) (by norm_num)
theorem B7224173 : Blo 2139435 7224173 := bstep (se 3 (by rfl) ⟨1354532, by rfl⟩ : syracuseStep 7224173 = 2709065) B2709065
theorem B4816115 : Blo 2139435 4816115 := bstep (se 1 (by rfl) ⟨3612086, by rfl⟩ : syracuseStep 4816115 = 7224173) B7224173
theorem B3210743 : Blo 2139435 3210743 := bstep (se 1 (by rfl) ⟨2408057, by rfl⟩ : syracuseStep 3210743 = 4816115) B4816115
theorem B2140495 : Blo 2139435 2140495 := bstep (se 1 (by rfl) ⟨1605371, by rfl⟩ : syracuseStep 2140495 = 3210743) B3210743
theorem B3210749 : Blo 2139435 3210749 := bbase (se 3 (by rfl) ⟨602015, by rfl⟩ : syracuseStep 3210749 = 1204031) (by norm_num)
theorem B2140499 : Blo 2139435 2140499 := bstep (se 1 (by rfl) ⟨1605374, by rfl⟩ : syracuseStep 2140499 = 3210749) B3210749
theorem B4816133 : Blo 2139435 4816133 := bbase (se 4 (by rfl) ⟨451512, by rfl⟩ : syracuseStep 4816133 = 903025) (by norm_num)
theorem B3210755 : Blo 2139435 3210755 := bstep (se 1 (by rfl) ⟨2408066, by rfl⟩ : syracuseStep 3210755 = 4816133) B4816133
theorem B2140503 : Blo 2139435 2140503 := bstep (se 1 (by rfl) ⟨1605377, by rfl⟩ : syracuseStep 2140503 = 3210755) B3210755
theorem B4063621 : Blo 2139435 4063621 := bbase (se 4 (by rfl) ⟨380964, by rfl⟩ : syracuseStep 4063621 = 761929) (by norm_num)
theorem B5418161 : Blo 2139435 5418161 := bstep (se 2 (by rfl) ⟨2031810, by rfl⟩ : syracuseStep 5418161 = 4063621) B4063621
theorem B3612107 : Blo 2139435 3612107 := bstep (se 1 (by rfl) ⟨2709080, by rfl⟩ : syracuseStep 3612107 = 5418161) B5418161
theorem B2408071 : Blo 2139435 2408071 := bstep (se 1 (by rfl) ⟨1806053, by rfl⟩ : syracuseStep 2408071 = 3612107) B3612107
theorem B3210761 : Blo 2139435 3210761 := bstep (se 2 (by rfl) ⟨1204035, by rfl⟩ : syracuseStep 3210761 = 2408071) B2408071
theorem B2140507 : Blo 2139435 2140507 := bstep (se 1 (by rfl) ⟨1605380, by rfl⟩ : syracuseStep 2140507 = 3210761) B3210761
theorem B10836341 : Blo 2139435 10836341 := bbase (se 5 (by rfl) ⟨507953, by rfl⟩ : syracuseStep 10836341 = 1015907) (by norm_num)
theorem B7224227 : Blo 2139435 7224227 := bstep (se 1 (by rfl) ⟨5418170, by rfl⟩ : syracuseStep 7224227 = 10836341) B10836341
theorem B4816151 : Blo 2139435 4816151 := bstep (se 1 (by rfl) ⟨3612113, by rfl⟩ : syracuseStep 4816151 = 7224227) B7224227
theorem B3210767 : Blo 2139435 3210767 := bstep (se 1 (by rfl) ⟨2408075, by rfl⟩ : syracuseStep 3210767 = 4816151) B4816151
theorem B2140511 : Blo 2139435 2140511 := bstep (se 1 (by rfl) ⟨1605383, by rfl⟩ : syracuseStep 2140511 = 3210767) B3210767
theorem B3210773 : Blo 2139435 3210773 := bbase (se 6 (by rfl) ⟨75252, by rfl⟩ : syracuseStep 3210773 = 150505) (by norm_num)
theorem B2140515 : Blo 2139435 2140515 := bstep (se 1 (by rfl) ⟨1605386, by rfl⟩ : syracuseStep 2140515 = 3210773) B3210773
theorem B6509173 : Blo 2139435 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B8678897 : Blo 2139435 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B5785931 : Blo 2139435 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B15429149 : Blo 2139435 15429149 := bstep (se 3 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 15429149 = 5785931) B5785931
theorem B10286099 : Blo 2139435 10286099 := bstep (se 1 (by rfl) ⟨7714574, by rfl⟩ : syracuseStep 10286099 = 15429149) B15429149
theorem B6857399 : Blo 2139435 6857399 := bstep (se 1 (by rfl) ⟨5143049, by rfl⟩ : syracuseStep 6857399 = 10286099) B10286099
theorem B18286397 : Blo 2139435 18286397 := bstep (se 3 (by rfl) ⟨3428699, by rfl⟩ : syracuseStep 18286397 = 6857399) B6857399
theorem B12190931 : Blo 2139435 12190931 := bstep (se 1 (by rfl) ⟨9143198, by rfl⟩ : syracuseStep 12190931 = 18286397) B18286397
theorem B8127287 : Blo 2139435 8127287 := bstep (se 1 (by rfl) ⟨6095465, by rfl⟩ : syracuseStep 8127287 = 12190931) B12190931
theorem B5418191 : Blo 2139435 5418191 := bstep (se 1 (by rfl) ⟨4063643, by rfl⟩ : syracuseStep 5418191 = 8127287) B8127287
theorem B3612127 : Blo 2139435 3612127 := bstep (se 1 (by rfl) ⟨2709095, by rfl⟩ : syracuseStep 3612127 = 5418191) B5418191
theorem B4816169 : Blo 2139435 4816169 := bstep (se 2 (by rfl) ⟨1806063, by rfl⟩ : syracuseStep 4816169 = 3612127) B3612127
theorem B3210779 : Blo 2139435 3210779 := bstep (se 1 (by rfl) ⟨2408084, by rfl⟩ : syracuseStep 3210779 = 4816169) B4816169
theorem B2140519 : Blo 2139435 2140519 := bstep (se 1 (by rfl) ⟨1605389, by rfl⟩ : syracuseStep 2140519 = 3210779) B3210779
theorem B2408089 : Blo 2139435 2408089 := bbase (se 2 (by rfl) ⟨903033, by rfl⟩ : syracuseStep 2408089 = 1806067) (by norm_num)
theorem B3210785 : Blo 2139435 3210785 := bstep (se 2 (by rfl) ⟨1204044, by rfl⟩ : syracuseStep 3210785 = 2408089) B2408089
theorem B2140523 : Blo 2139435 2140523 := bstep (se 1 (by rfl) ⟨1605392, by rfl⟩ : syracuseStep 2140523 = 3210785) B3210785
theorem B8127317 : Blo 2139435 8127317 := bbase (se 9 (by rfl) ⟨23810, by rfl⟩ : syracuseStep 8127317 = 47621) (by norm_num)
theorem B5418211 : Blo 2139435 5418211 := bstep (se 1 (by rfl) ⟨4063658, by rfl⟩ : syracuseStep 5418211 = 8127317) B8127317
theorem B7224281 : Blo 2139435 7224281 := bstep (se 2 (by rfl) ⟨2709105, by rfl⟩ : syracuseStep 7224281 = 5418211) B5418211
theorem B4816187 : Blo 2139435 4816187 := bstep (se 1 (by rfl) ⟨3612140, by rfl⟩ : syracuseStep 4816187 = 7224281) B7224281
theorem B3210791 : Blo 2139435 3210791 := bstep (se 1 (by rfl) ⟨2408093, by rfl⟩ : syracuseStep 3210791 = 4816187) B4816187
theorem B2140527 : Blo 2139435 2140527 := bstep (se 1 (by rfl) ⟨1605395, by rfl⟩ : syracuseStep 2140527 = 3210791) B3210791
theorem B3210797 : Blo 2139435 3210797 := bbase (se 3 (by rfl) ⟨602024, by rfl⟩ : syracuseStep 3210797 = 1204049) (by norm_num)
theorem B2140531 : Blo 2139435 2140531 := bstep (se 1 (by rfl) ⟨1605398, by rfl⟩ : syracuseStep 2140531 = 3210797) B3210797
theorem B4816205 : Blo 2139435 4816205 := bbase (se 3 (by rfl) ⟨903038, by rfl⟩ : syracuseStep 4816205 = 1806077) (by norm_num)
theorem B3210803 : Blo 2139435 3210803 := bstep (se 1 (by rfl) ⟨2408102, by rfl⟩ : syracuseStep 3210803 = 4816205) B4816205
theorem B2140535 : Blo 2139435 2140535 := bstep (se 1 (by rfl) ⟨1605401, by rfl⟩ : syracuseStep 2140535 = 3210803) B3210803
theorem B2709121 : Blo 2139435 2709121 := bbase (se 2 (by rfl) ⟨1015920, by rfl⟩ : syracuseStep 2709121 = 2031841) (by norm_num)
theorem B3612161 : Blo 2139435 3612161 := bstep (se 2 (by rfl) ⟨1354560, by rfl⟩ : syracuseStep 3612161 = 2709121) B2709121
theorem B2408107 : Blo 2139435 2408107 := bstep (se 1 (by rfl) ⟨1806080, by rfl⟩ : syracuseStep 2408107 = 3612161) B3612161
theorem B3210809 : Blo 2139435 3210809 := bstep (se 2 (by rfl) ⟨1204053, by rfl⟩ : syracuseStep 3210809 = 2408107) B2408107
theorem B2140539 : Blo 2139435 2140539 := bstep (se 1 (by rfl) ⟨1605404, by rfl⟩ : syracuseStep 2140539 = 3210809) B3210809
theorem B2285825 : Blo 2139435 2285825 := bbase (se 2 (by rfl) ⟨857184, by rfl⟩ : syracuseStep 2285825 = 1714369) (by norm_num)
theorem B24382133 : Blo 2139435 24382133 := bstep (se 5 (by rfl) ⟨1142912, by rfl⟩ : syracuseStep 24382133 = 2285825) B2285825
theorem B16254755 : Blo 2139435 16254755 := bstep (se 1 (by rfl) ⟨12191066, by rfl⟩ : syracuseStep 16254755 = 24382133) B24382133
theorem B10836503 : Blo 2139435 10836503 := bstep (se 1 (by rfl) ⟨8127377, by rfl⟩ : syracuseStep 10836503 = 16254755) B16254755
theorem B7224335 : Blo 2139435 7224335 := bstep (se 1 (by rfl) ⟨5418251, by rfl⟩ : syracuseStep 7224335 = 10836503) B10836503
theorem B4816223 : Blo 2139435 4816223 := bstep (se 1 (by rfl) ⟨3612167, by rfl⟩ : syracuseStep 4816223 = 7224335) B7224335
theorem B3210815 : Blo 2139435 3210815 := bstep (se 1 (by rfl) ⟨2408111, by rfl⟩ : syracuseStep 3210815 = 4816223) B4816223
theorem B2140543 : Blo 2139435 2140543 := bstep (se 1 (by rfl) ⟨1605407, by rfl⟩ : syracuseStep 2140543 = 3210815) B3210815
theorem B3210821 : Blo 2139435 3210821 := bbase (se 4 (by rfl) ⟨301014, by rfl⟩ : syracuseStep 3210821 = 602029) (by norm_num)
theorem B2140547 : Blo 2139435 2140547 := bstep (se 1 (by rfl) ⟨1605410, by rfl⟩ : syracuseStep 2140547 = 3210821) B3210821
theorem B3612181 : Blo 2139435 3612181 := bbase (se 6 (by rfl) ⟨84660, by rfl⟩ : syracuseStep 3612181 = 169321) (by norm_num)
theorem B4816241 : Blo 2139435 4816241 := bstep (se 2 (by rfl) ⟨1806090, by rfl⟩ : syracuseStep 4816241 = 3612181) B3612181
theorem B3210827 : Blo 2139435 3210827 := bstep (se 1 (by rfl) ⟨2408120, by rfl⟩ : syracuseStep 3210827 = 4816241) B4816241
theorem B2140551 : Blo 2139435 2140551 := bstep (se 1 (by rfl) ⟨1605413, by rfl⟩ : syracuseStep 2140551 = 3210827) B3210827
theorem B2408125 : Blo 2139435 2408125 := bbase (se 3 (by rfl) ⟨451523, by rfl⟩ : syracuseStep 2408125 = 903047) (by norm_num)
theorem B3210833 : Blo 2139435 3210833 := bstep (se 2 (by rfl) ⟨1204062, by rfl⟩ : syracuseStep 3210833 = 2408125) B2408125
theorem B2140555 : Blo 2139435 2140555 := bstep (se 1 (by rfl) ⟨1605416, by rfl⟩ : syracuseStep 2140555 = 3210833) B3210833
theorem B7224389 : Blo 2139435 7224389 := bbase (se 4 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 7224389 = 1354573) (by norm_num)
theorem B4816259 : Blo 2139435 4816259 := bstep (se 1 (by rfl) ⟨3612194, by rfl⟩ : syracuseStep 4816259 = 7224389) B7224389
theorem B3210839 : Blo 2139435 3210839 := bstep (se 1 (by rfl) ⟨2408129, by rfl⟩ : syracuseStep 3210839 = 4816259) B4816259
theorem B2140559 : Blo 2139435 2140559 := bstep (se 1 (by rfl) ⟨1605419, by rfl⟩ : syracuseStep 2140559 = 3210839) B3210839
theorem B3210845 : Blo 2139435 3210845 := bbase (se 3 (by rfl) ⟨602033, by rfl⟩ : syracuseStep 3210845 = 1204067) (by norm_num)
theorem B2140563 : Blo 2139435 2140563 := bstep (se 1 (by rfl) ⟨1605422, by rfl⟩ : syracuseStep 2140563 = 3210845) B3210845
theorem B4816277 : Blo 2139435 4816277 := bbase (se 6 (by rfl) ⟨112881, by rfl⟩ : syracuseStep 4816277 = 225763) (by norm_num)
theorem B3210851 : Blo 2139435 3210851 := bstep (se 1 (by rfl) ⟨2408138, by rfl⟩ : syracuseStep 3210851 = 4816277) B4816277
theorem B2140567 : Blo 2139435 2140567 := bstep (se 1 (by rfl) ⟨1605425, by rfl⟩ : syracuseStep 2140567 = 3210851) B3210851
theorem B34716437 : Blo 2139435 34716437 := bbase (se 6 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 34716437 = 1627333) (by norm_num)
theorem B23144291 : Blo 2139435 23144291 := bstep (se 1 (by rfl) ⟨17358218, by rfl⟩ : syracuseStep 23144291 = 34716437) B34716437
theorem B15429527 : Blo 2139435 15429527 := bstep (se 1 (by rfl) ⟨11572145, by rfl⟩ : syracuseStep 15429527 = 23144291) B23144291
theorem B10286351 : Blo 2139435 10286351 := bstep (se 1 (by rfl) ⟨7714763, by rfl⟩ : syracuseStep 10286351 = 15429527) B15429527
theorem B6857567 : Blo 2139435 6857567 := bstep (se 1 (by rfl) ⟨5143175, by rfl⟩ : syracuseStep 6857567 = 10286351) B10286351
theorem B4571711 : Blo 2139435 4571711 := bstep (se 1 (by rfl) ⟨3428783, by rfl⟩ : syracuseStep 4571711 = 6857567) B6857567
theorem B3047807 : Blo 2139435 3047807 := bstep (se 1 (by rfl) ⟨2285855, by rfl⟩ : syracuseStep 3047807 = 4571711) B4571711
theorem B8127485 : Blo 2139435 8127485 := bstep (se 3 (by rfl) ⟨1523903, by rfl⟩ : syracuseStep 8127485 = 3047807) B3047807
theorem B5418323 : Blo 2139435 5418323 := bstep (se 1 (by rfl) ⟨4063742, by rfl⟩ : syracuseStep 5418323 = 8127485) B8127485
theorem B3612215 : Blo 2139435 3612215 := bstep (se 1 (by rfl) ⟨2709161, by rfl⟩ : syracuseStep 3612215 = 5418323) B5418323
theorem B2408143 : Blo 2139435 2408143 := bstep (se 1 (by rfl) ⟨1806107, by rfl⟩ : syracuseStep 2408143 = 3612215) B3612215
theorem B3210857 : Blo 2139435 3210857 := bstep (se 2 (by rfl) ⟨1204071, by rfl⟩ : syracuseStep 3210857 = 2408143) B2408143
theorem B2140571 : Blo 2139435 2140571 := bstep (se 1 (by rfl) ⟨1605428, by rfl⟩ : syracuseStep 2140571 = 3210857) B3210857
theorem B3428789 : Blo 2139435 3428789 := bbase (se 5 (by rfl) ⟨160724, by rfl⟩ : syracuseStep 3428789 = 321449) (by norm_num)
theorem B9143437 : Blo 2139435 9143437 := bstep (se 3 (by rfl) ⟨1714394, by rfl⟩ : syracuseStep 9143437 = 3428789) B3428789
theorem B12191249 : Blo 2139435 12191249 := bstep (se 2 (by rfl) ⟨4571718, by rfl⟩ : syracuseStep 12191249 = 9143437) B9143437
theorem B8127499 : Blo 2139435 8127499 := bstep (se 1 (by rfl) ⟨6095624, by rfl⟩ : syracuseStep 8127499 = 12191249) B12191249
theorem B10836665 : Blo 2139435 10836665 := bstep (se 2 (by rfl) ⟨4063749, by rfl⟩ : syracuseStep 10836665 = 8127499) B8127499
theorem B7224443 : Blo 2139435 7224443 := bstep (se 1 (by rfl) ⟨5418332, by rfl⟩ : syracuseStep 7224443 = 10836665) B10836665
theorem B4816295 : Blo 2139435 4816295 := bstep (se 1 (by rfl) ⟨3612221, by rfl⟩ : syracuseStep 4816295 = 7224443) B7224443
theorem B3210863 : Blo 2139435 3210863 := bstep (se 1 (by rfl) ⟨2408147, by rfl⟩ : syracuseStep 3210863 = 4816295) B4816295
theorem B2140575 : Blo 2139435 2140575 := bstep (se 1 (by rfl) ⟨1605431, by rfl⟩ : syracuseStep 2140575 = 3210863) B3210863
theorem B3210869 : Blo 2139435 3210869 := bbase (se 5 (by rfl) ⟨150509, by rfl⟩ : syracuseStep 3210869 = 301019) (by norm_num)
theorem B2140579 : Blo 2139435 2140579 := bstep (se 1 (by rfl) ⟨1605434, by rfl⟩ : syracuseStep 2140579 = 3210869) B3210869
theorem B4063765 : Blo 2139435 4063765 := bbase (se 6 (by rfl) ⟨95244, by rfl⟩ : syracuseStep 4063765 = 190489) (by norm_num)
theorem B5418353 : Blo 2139435 5418353 := bstep (se 2 (by rfl) ⟨2031882, by rfl⟩ : syracuseStep 5418353 = 4063765) B4063765
theorem B3612235 : Blo 2139435 3612235 := bstep (se 1 (by rfl) ⟨2709176, by rfl⟩ : syracuseStep 3612235 = 5418353) B5418353
theorem B4816313 : Blo 2139435 4816313 := bstep (se 2 (by rfl) ⟨1806117, by rfl⟩ : syracuseStep 4816313 = 3612235) B3612235
theorem B3210875 : Blo 2139435 3210875 := bstep (se 1 (by rfl) ⟨2408156, by rfl⟩ : syracuseStep 3210875 = 4816313) B4816313
theorem B2140583 : Blo 2139435 2140583 := bstep (se 1 (by rfl) ⟨1605437, by rfl⟩ : syracuseStep 2140583 = 3210875) B3210875
theorem B2408161 : Blo 2139435 2408161 := bbase (se 2 (by rfl) ⟨903060, by rfl⟩ : syracuseStep 2408161 = 1806121) (by norm_num)
theorem B3210881 : Blo 2139435 3210881 := bstep (se 2 (by rfl) ⟨1204080, by rfl⟩ : syracuseStep 3210881 = 2408161) B2408161
theorem B2140587 : Blo 2139435 2140587 := bstep (se 1 (by rfl) ⟨1605440, by rfl⟩ : syracuseStep 2140587 = 3210881) B3210881
theorem B5418373 : Blo 2139435 5418373 := bbase (se 4 (by rfl) ⟨507972, by rfl⟩ : syracuseStep 5418373 = 1015945) (by norm_num)
theorem B7224497 : Blo 2139435 7224497 := bstep (se 2 (by rfl) ⟨2709186, by rfl⟩ : syracuseStep 7224497 = 5418373) B5418373
theorem B4816331 : Blo 2139435 4816331 := bstep (se 1 (by rfl) ⟨3612248, by rfl⟩ : syracuseStep 4816331 = 7224497) B7224497
theorem B3210887 : Blo 2139435 3210887 := bstep (se 1 (by rfl) ⟨2408165, by rfl⟩ : syracuseStep 3210887 = 4816331) B4816331
theorem B2140591 : Blo 2139435 2140591 := bstep (se 1 (by rfl) ⟨1605443, by rfl⟩ : syracuseStep 2140591 = 3210887) B3210887
theorem B3210893 : Blo 2139435 3210893 := bbase (se 3 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 3210893 = 1204085) (by norm_num)
theorem B2140595 : Blo 2139435 2140595 := bstep (se 1 (by rfl) ⟨1605446, by rfl⟩ : syracuseStep 2140595 = 3210893) B3210893
theorem B4816349 : Blo 2139435 4816349 := bbase (se 3 (by rfl) ⟨903065, by rfl⟩ : syracuseStep 4816349 = 1806131) (by norm_num)
theorem B3210899 : Blo 2139435 3210899 := bstep (se 1 (by rfl) ⟨2408174, by rfl⟩ : syracuseStep 3210899 = 4816349) B4816349
theorem B2140599 : Blo 2139435 2140599 := bstep (se 1 (by rfl) ⟨1605449, by rfl⟩ : syracuseStep 2140599 = 3210899) B3210899
theorem B3612269 : Blo 2139435 3612269 := bbase (se 3 (by rfl) ⟨677300, by rfl⟩ : syracuseStep 3612269 = 1354601) (by norm_num)
theorem B2408179 : Blo 2139435 2408179 := bstep (se 1 (by rfl) ⟨1806134, by rfl⟩ : syracuseStep 2408179 = 3612269) B3612269
theorem B3210905 : Blo 2139435 3210905 := bstep (se 2 (by rfl) ⟨1204089, by rfl⟩ : syracuseStep 3210905 = 2408179) B2408179
theorem B2140603 : Blo 2139435 2140603 := bstep (se 1 (by rfl) ⟨1605452, by rfl⟩ : syracuseStep 2140603 = 3210905) B3210905
theorem B15429781 : Blo 2139435 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B20573041 : Blo 2139435 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B27430721 : Blo 2139435 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B18287147 : Blo 2139435 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B12191431 : Blo 2139435 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B16255241 : Blo 2139435 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B10836827 : Blo 2139435 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B7224551 : Blo 2139435 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B4816367 : Blo 2139435 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B3210911 : Blo 2139435 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B2140607 : Blo 2139435 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B3210917 : Blo 2139435 3210917 := bbase (se 4 (by rfl) ⟨301023, by rfl⟩ : syracuseStep 3210917 = 602047) (by norm_num)
theorem B2140611 : Blo 2139435 2140611 := bstep (se 1 (by rfl) ⟨1605458, by rfl⟩ : syracuseStep 2140611 = 3210917) B3210917
theorem B2709217 : Blo 2139435 2709217 := bbase (se 2 (by rfl) ⟨1015956, by rfl⟩ : syracuseStep 2709217 = 2031913) (by norm_num)
theorem B3612289 : Blo 2139435 3612289 := bstep (se 2 (by rfl) ⟨1354608, by rfl⟩ : syracuseStep 3612289 = 2709217) B2709217
theorem B4816385 : Blo 2139435 4816385 := bstep (se 2 (by rfl) ⟨1806144, by rfl⟩ : syracuseStep 4816385 = 3612289) B3612289
theorem B3210923 : Blo 2139435 3210923 := bstep (se 1 (by rfl) ⟨2408192, by rfl⟩ : syracuseStep 3210923 = 4816385) B4816385
theorem B2140615 : Blo 2139435 2140615 := bstep (se 1 (by rfl) ⟨1605461, by rfl⟩ : syracuseStep 2140615 = 3210923) B3210923
theorem B2408197 : Blo 2139435 2408197 := bbase (se 4 (by rfl) ⟨225768, by rfl⟩ : syracuseStep 2408197 = 451537) (by norm_num)
theorem B3210929 : Blo 2139435 3210929 := bstep (se 2 (by rfl) ⟨1204098, by rfl⟩ : syracuseStep 3210929 = 2408197) B2408197
theorem B2140619 : Blo 2139435 2140619 := bstep (se 1 (by rfl) ⟨1605464, by rfl⟩ : syracuseStep 2140619 = 3210929) B3210929
theorem B5143301 : Blo 2139435 5143301 := bbase (se 4 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 5143301 = 964369) (by norm_num)
theorem B3428867 : Blo 2139435 3428867 := bstep (se 1 (by rfl) ⟨2571650, by rfl⟩ : syracuseStep 3428867 = 5143301) B5143301
theorem B2285911 : Blo 2139435 2285911 := bstep (se 1 (by rfl) ⟨1714433, by rfl⟩ : syracuseStep 2285911 = 3428867) B3428867
theorem B3047881 : Blo 2139435 3047881 := bstep (se 2 (by rfl) ⟨1142955, by rfl⟩ : syracuseStep 3047881 = 2285911) B2285911
theorem B4063841 : Blo 2139435 4063841 := bstep (se 2 (by rfl) ⟨1523940, by rfl⟩ : syracuseStep 4063841 = 3047881) B3047881
theorem B2709227 : Blo 2139435 2709227 := bstep (se 1 (by rfl) ⟨2031920, by rfl⟩ : syracuseStep 2709227 = 4063841) B4063841
theorem B7224605 : Blo 2139435 7224605 := bstep (se 3 (by rfl) ⟨1354613, by rfl⟩ : syracuseStep 7224605 = 2709227) B2709227
theorem B4816403 : Blo 2139435 4816403 := bstep (se 1 (by rfl) ⟨3612302, by rfl⟩ : syracuseStep 4816403 = 7224605) B7224605
theorem B3210935 : Blo 2139435 3210935 := bstep (se 1 (by rfl) ⟨2408201, by rfl⟩ : syracuseStep 3210935 = 4816403) B4816403
theorem B2140623 : Blo 2139435 2140623 := bstep (se 1 (by rfl) ⟨1605467, by rfl⟩ : syracuseStep 2140623 = 3210935) B3210935
theorem B3210941 : Blo 2139435 3210941 := bbase (se 3 (by rfl) ⟨602051, by rfl⟩ : syracuseStep 3210941 = 1204103) (by norm_num)
theorem B2140627 : Blo 2139435 2140627 := bstep (se 1 (by rfl) ⟨1605470, by rfl⟩ : syracuseStep 2140627 = 3210941) B3210941
theorem B4816421 : Blo 2139435 4816421 := bbase (se 4 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 4816421 = 903079) (by norm_num)
theorem B3210947 : Blo 2139435 3210947 := bstep (se 1 (by rfl) ⟨2408210, by rfl⟩ : syracuseStep 3210947 = 4816421) B4816421
theorem B2140631 : Blo 2139435 2140631 := bstep (se 1 (by rfl) ⟨1605473, by rfl⟩ : syracuseStep 2140631 = 3210947) B3210947
theorem B5418485 : Blo 2139435 5418485 := bbase (se 5 (by rfl) ⟨253991, by rfl⟩ : syracuseStep 5418485 = 507983) (by norm_num)
theorem B3612323 : Blo 2139435 3612323 := bstep (se 1 (by rfl) ⟨2709242, by rfl⟩ : syracuseStep 3612323 = 5418485) B5418485
theorem B2408215 : Blo 2139435 2408215 := bstep (se 1 (by rfl) ⟨1806161, by rfl⟩ : syracuseStep 2408215 = 3612323) B3612323
theorem B3210953 : Blo 2139435 3210953 := bstep (se 2 (by rfl) ⟨1204107, by rfl⟩ : syracuseStep 3210953 = 2408215) B2408215
theorem B2140635 : Blo 2139435 2140635 := bstep (se 1 (by rfl) ⟨1605476, by rfl⟩ : syracuseStep 2140635 = 3210953) B3210953
theorem B5945221 : Blo 2139435 5945221 := bbase (se 4 (by rfl) ⟨557364, by rfl⟩ : syracuseStep 5945221 = 1114729) (by norm_num)
theorem B31707845 : Blo 2139435 31707845 := bstep (se 4 (by rfl) ⟨2972610, by rfl⟩ : syracuseStep 31707845 = 5945221) B5945221
theorem B21138563 : Blo 2139435 21138563 := bstep (se 1 (by rfl) ⟨15853922, by rfl⟩ : syracuseStep 21138563 = 31707845) B31707845
theorem B14092375 : Blo 2139435 14092375 := bstep (se 1 (by rfl) ⟨10569281, by rfl⟩ : syracuseStep 14092375 = 21138563) B21138563
theorem B18789833 : Blo 2139435 18789833 := bstep (se 2 (by rfl) ⟨7046187, by rfl⟩ : syracuseStep 18789833 = 14092375) B14092375
theorem B50106221 : Blo 2139435 50106221 := bstep (se 3 (by rfl) ⟨9394916, by rfl⟩ : syracuseStep 50106221 = 18789833) B18789833
theorem B33404147 : Blo 2139435 33404147 := bstep (se 1 (by rfl) ⟨25053110, by rfl⟩ : syracuseStep 33404147 = 50106221) B50106221
theorem B22269431 : Blo 2139435 22269431 := bstep (se 1 (by rfl) ⟨16702073, by rfl⟩ : syracuseStep 22269431 = 33404147) B33404147
theorem B14846287 : Blo 2139435 14846287 := bstep (se 1 (by rfl) ⟨11134715, by rfl⟩ : syracuseStep 14846287 = 22269431) B22269431
theorem B19795049 : Blo 2139435 19795049 := bstep (se 2 (by rfl) ⟨7423143, by rfl⟩ : syracuseStep 19795049 = 14846287) B14846287
theorem B13196699 : Blo 2139435 13196699 := bstep (se 1 (by rfl) ⟨9897524, by rfl⟩ : syracuseStep 13196699 = 19795049) B19795049
theorem B8797799 : Blo 2139435 8797799 := bstep (se 1 (by rfl) ⟨6598349, by rfl⟩ : syracuseStep 8797799 = 13196699) B13196699
theorem B5865199 : Blo 2139435 5865199 := bstep (se 1 (by rfl) ⟨4398899, by rfl⟩ : syracuseStep 5865199 = 8797799) B8797799
theorem B31281061 : Blo 2139435 31281061 := bstep (se 4 (by rfl) ⟨2932599, by rfl⟩ : syracuseStep 31281061 = 5865199) B5865199
theorem B41708081 : Blo 2139435 41708081 := bstep (se 2 (by rfl) ⟨15640530, by rfl⟩ : syracuseStep 41708081 = 31281061) B31281061
theorem B111221549 : Blo 2139435 111221549 := bstep (se 3 (by rfl) ⟨20854040, by rfl⟩ : syracuseStep 111221549 = 41708081) B41708081
theorem B74147699 : Blo 2139435 74147699 := bstep (se 1 (by rfl) ⟨55610774, by rfl⟩ : syracuseStep 74147699 = 111221549) B111221549
theorem B49431799 : Blo 2139435 49431799 := bstep (se 1 (by rfl) ⟨37073849, by rfl⟩ : syracuseStep 49431799 = 74147699) B74147699
theorem B65909065 : Blo 2139435 65909065 := bstep (se 2 (by rfl) ⟨24715899, by rfl⟩ : syracuseStep 65909065 = 49431799) B49431799
theorem B87878753 : Blo 2139435 87878753 := bstep (se 2 (by rfl) ⟨32954532, by rfl⟩ : syracuseStep 87878753 = 65909065) B65909065
theorem B58585835 : Blo 2139435 58585835 := bstep (se 1 (by rfl) ⟨43939376, by rfl⟩ : syracuseStep 58585835 = 87878753) B87878753
theorem B39057223 : Blo 2139435 39057223 := bstep (se 1 (by rfl) ⟨29292917, by rfl⟩ : syracuseStep 39057223 = 58585835) B58585835
theorem B52076297 : Blo 2139435 52076297 := bstep (se 2 (by rfl) ⟨19528611, by rfl⟩ : syracuseStep 52076297 = 39057223) B39057223
theorem B34717531 : Blo 2139435 34717531 := bstep (se 1 (by rfl) ⟨26038148, by rfl⟩ : syracuseStep 34717531 = 52076297) B52076297
theorem B46290041 : Blo 2139435 46290041 := bstep (se 2 (by rfl) ⟨17358765, by rfl⟩ : syracuseStep 46290041 = 34717531) B34717531
theorem B30860027 : Blo 2139435 30860027 := bstep (se 1 (by rfl) ⟨23145020, by rfl⟩ : syracuseStep 30860027 = 46290041) B46290041
theorem B20573351 : Blo 2139435 20573351 := bstep (se 1 (by rfl) ⟨15430013, by rfl⟩ : syracuseStep 20573351 = 30860027) B30860027
theorem B13715567 : Blo 2139435 13715567 := bstep (se 1 (by rfl) ⟨10286675, by rfl⟩ : syracuseStep 13715567 = 20573351) B20573351
theorem B9143711 : Blo 2139435 9143711 := bstep (se 1 (by rfl) ⟨6857783, by rfl⟩ : syracuseStep 9143711 = 13715567) B13715567
theorem B6095807 : Blo 2139435 6095807 := bstep (se 1 (by rfl) ⟨4571855, by rfl⟩ : syracuseStep 6095807 = 9143711) B9143711
theorem B4063871 : Blo 2139435 4063871 := bstep (se 1 (by rfl) ⟨3047903, by rfl⟩ : syracuseStep 4063871 = 6095807) B6095807
theorem B10836989 : Blo 2139435 10836989 := bstep (se 3 (by rfl) ⟨2031935, by rfl⟩ : syracuseStep 10836989 = 4063871) B4063871
theorem B7224659 : Blo 2139435 7224659 := bstep (se 1 (by rfl) ⟨5418494, by rfl⟩ : syracuseStep 7224659 = 10836989) B10836989
theorem B4816439 : Blo 2139435 4816439 := bstep (se 1 (by rfl) ⟨3612329, by rfl⟩ : syracuseStep 4816439 = 7224659) B7224659
theorem B3210959 : Blo 2139435 3210959 := bstep (se 1 (by rfl) ⟨2408219, by rfl⟩ : syracuseStep 3210959 = 4816439) B4816439
theorem B2140639 : Blo 2139435 2140639 := bstep (se 1 (by rfl) ⟨1605479, by rfl⟩ : syracuseStep 2140639 = 3210959) B3210959
theorem B3210965 : Blo 2139435 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B2140643 : Blo 2139435 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B5213533 : Blo 2139435 5213533 := bbase (se 3 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 5213533 = 1955075) (by norm_num)
theorem B6951377 : Blo 2139435 6951377 := bstep (se 2 (by rfl) ⟨2606766, by rfl⟩ : syracuseStep 6951377 = 5213533) B5213533
theorem B18537005 : Blo 2139435 18537005 := bstep (se 3 (by rfl) ⟨3475688, by rfl⟩ : syracuseStep 18537005 = 6951377) B6951377
theorem B12358003 : Blo 2139435 12358003 := bstep (se 1 (by rfl) ⟨9268502, by rfl⟩ : syracuseStep 12358003 = 18537005) B18537005
theorem B16477337 : Blo 2139435 16477337 := bstep (se 2 (by rfl) ⟨6179001, by rfl⟩ : syracuseStep 16477337 = 12358003) B12358003
theorem B10984891 : Blo 2139435 10984891 := bstep (se 1 (by rfl) ⟨8238668, by rfl⟩ : syracuseStep 10984891 = 16477337) B16477337
theorem B14646521 : Blo 2139435 14646521 := bstep (se 2 (by rfl) ⟨5492445, by rfl⟩ : syracuseStep 14646521 = 10984891) B10984891
theorem B9764347 : Blo 2139435 9764347 := bstep (se 1 (by rfl) ⟨7323260, by rfl⟩ : syracuseStep 9764347 = 14646521) B14646521
theorem B13019129 : Blo 2139435 13019129 := bstep (se 2 (by rfl) ⟨4882173, by rfl⟩ : syracuseStep 13019129 = 9764347) B9764347
theorem B8679419 : Blo 2139435 8679419 := bstep (se 1 (by rfl) ⟨6509564, by rfl⟩ : syracuseStep 8679419 = 13019129) B13019129
theorem B5786279 : Blo 2139435 5786279 := bstep (se 1 (by rfl) ⟨4339709, by rfl⟩ : syracuseStep 5786279 = 8679419) B8679419
theorem B3857519 : Blo 2139435 3857519 := bstep (se 1 (by rfl) ⟨2893139, by rfl⟩ : syracuseStep 3857519 = 5786279) B5786279
theorem B2571679 : Blo 2139435 2571679 := bstep (se 1 (by rfl) ⟨1928759, by rfl⟩ : syracuseStep 2571679 = 3857519) B3857519
theorem B3428905 : Blo 2139435 3428905 := bstep (se 2 (by rfl) ⟨1285839, by rfl⟩ : syracuseStep 3428905 = 2571679) B2571679
theorem B4571873 : Blo 2139435 4571873 := bstep (se 2 (by rfl) ⟨1714452, by rfl⟩ : syracuseStep 4571873 = 3428905) B3428905
theorem B3047915 : Blo 2139435 3047915 := bstep (se 1 (by rfl) ⟨2285936, by rfl⟩ : syracuseStep 3047915 = 4571873) B4571873
theorem B8127773 : Blo 2139435 8127773 := bstep (se 3 (by rfl) ⟨1523957, by rfl⟩ : syracuseStep 8127773 = 3047915) B3047915
theorem B5418515 : Blo 2139435 5418515 := bstep (se 1 (by rfl) ⟨4063886, by rfl⟩ : syracuseStep 5418515 = 8127773) B8127773
theorem B3612343 : Blo 2139435 3612343 := bstep (se 1 (by rfl) ⟨2709257, by rfl⟩ : syracuseStep 3612343 = 5418515) B5418515
theorem B4816457 : Blo 2139435 4816457 := bstep (se 2 (by rfl) ⟨1806171, by rfl⟩ : syracuseStep 4816457 = 3612343) B3612343
theorem B3210971 : Blo 2139435 3210971 := bstep (se 1 (by rfl) ⟨2408228, by rfl⟩ : syracuseStep 3210971 = 4816457) B4816457
theorem B2140647 : Blo 2139435 2140647 := bstep (se 1 (by rfl) ⟨1605485, by rfl⟩ : syracuseStep 2140647 = 3210971) B3210971
theorem B2408233 : Blo 2139435 2408233 := bbase (se 2 (by rfl) ⟨903087, by rfl⟩ : syracuseStep 2408233 = 1806175) (by norm_num)
theorem B3210977 : Blo 2139435 3210977 := bstep (se 2 (by rfl) ⟨1204116, by rfl⟩ : syracuseStep 3210977 = 2408233) B2408233
theorem B2140651 : Blo 2139435 2140651 := bstep (se 1 (by rfl) ⟨1605488, by rfl⟩ : syracuseStep 2140651 = 3210977) B3210977
theorem B13715669 : Blo 2139435 13715669 := bbase (se 7 (by rfl) ⟨160730, by rfl⟩ : syracuseStep 13715669 = 321461) (by norm_num)
theorem B9143779 : Blo 2139435 9143779 := bstep (se 1 (by rfl) ⟨6857834, by rfl⟩ : syracuseStep 9143779 = 13715669) B13715669
theorem B12191705 : Blo 2139435 12191705 := bstep (se 2 (by rfl) ⟨4571889, by rfl⟩ : syracuseStep 12191705 = 9143779) B9143779
theorem B8127803 : Blo 2139435 8127803 := bstep (se 1 (by rfl) ⟨6095852, by rfl⟩ : syracuseStep 8127803 = 12191705) B12191705
theorem B5418535 : Blo 2139435 5418535 := bstep (se 1 (by rfl) ⟨4063901, by rfl⟩ : syracuseStep 5418535 = 8127803) B8127803
theorem B7224713 : Blo 2139435 7224713 := bstep (se 2 (by rfl) ⟨2709267, by rfl⟩ : syracuseStep 7224713 = 5418535) B5418535
theorem B4816475 : Blo 2139435 4816475 := bstep (se 1 (by rfl) ⟨3612356, by rfl⟩ : syracuseStep 4816475 = 7224713) B7224713
theorem B3210983 : Blo 2139435 3210983 := bstep (se 1 (by rfl) ⟨2408237, by rfl⟩ : syracuseStep 3210983 = 4816475) B4816475
theorem B2140655 : Blo 2139435 2140655 := bstep (se 1 (by rfl) ⟨1605491, by rfl⟩ : syracuseStep 2140655 = 3210983) B3210983
theorem B3210989 : Blo 2139435 3210989 := bbase (se 3 (by rfl) ⟨602060, by rfl⟩ : syracuseStep 3210989 = 1204121) (by norm_num)
theorem B2140659 : Blo 2139435 2140659 := bstep (se 1 (by rfl) ⟨1605494, by rfl⟩ : syracuseStep 2140659 = 3210989) B3210989
theorem B4816493 : Blo 2139435 4816493 := bbase (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) (by norm_num)
theorem B3210995 : Blo 2139435 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B2140663 : Blo 2139435 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B4063925 : Blo 2139435 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B2709283 : Blo 2139435 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B3612377 : Blo 2139435 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B2408251 : Blo 2139435 2408251 := bstep (se 1 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 2408251 = 3612377) B3612377
theorem B3211001 : Blo 2139435 3211001 := bstep (se 2 (by rfl) ⟨1204125, by rfl⟩ : syracuseStep 3211001 = 2408251) B2408251
theorem B2140667 : Blo 2139435 2140667 := bstep (se 1 (by rfl) ⟨1605500, by rfl⟩ : syracuseStep 2140667 = 3211001) B3211001
theorem B3661669 : Blo 2139435 3661669 := bbase (se 4 (by rfl) ⟨343281, by rfl⟩ : syracuseStep 3661669 = 686563) (by norm_num)
theorem B4882225 : Blo 2139435 4882225 := bstep (se 2 (by rfl) ⟨1830834, by rfl⟩ : syracuseStep 4882225 = 3661669) B3661669
theorem B104154133 : Blo 2139435 104154133 := bstep (se 6 (by rfl) ⟨2441112, by rfl⟩ : syracuseStep 104154133 = 4882225) B4882225
theorem B138872177 : Blo 2139435 138872177 := bstep (se 2 (by rfl) ⟨52077066, by rfl⟩ : syracuseStep 138872177 = 104154133) B104154133
theorem B92581451 : Blo 2139435 92581451 := bstep (se 1 (by rfl) ⟨69436088, by rfl⟩ : syracuseStep 92581451 = 138872177) B138872177
theorem B61720967 : Blo 2139435 61720967 := bstep (se 1 (by rfl) ⟨46290725, by rfl⟩ : syracuseStep 61720967 = 92581451) B92581451
theorem B41147311 : Blo 2139435 41147311 := bstep (se 1 (by rfl) ⟨30860483, by rfl⟩ : syracuseStep 41147311 = 61720967) B61720967
theorem B54863081 : Blo 2139435 54863081 := bstep (se 2 (by rfl) ⟨20573655, by rfl⟩ : syracuseStep 54863081 = 41147311) B41147311
theorem B36575387 : Blo 2139435 36575387 := bstep (se 1 (by rfl) ⟨27431540, by rfl⟩ : syracuseStep 36575387 = 54863081) B54863081
theorem B24383591 : Blo 2139435 24383591 := bstep (se 1 (by rfl) ⟨18287693, by rfl⟩ : syracuseStep 24383591 = 36575387) B36575387
theorem B16255727 : Blo 2139435 16255727 := bstep (se 1 (by rfl) ⟨12191795, by rfl⟩ : syracuseStep 16255727 = 24383591) B24383591
theorem B10837151 : Blo 2139435 10837151 := bstep (se 1 (by rfl) ⟨8127863, by rfl⟩ : syracuseStep 10837151 = 16255727) B16255727
theorem B7224767 : Blo 2139435 7224767 := bstep (se 1 (by rfl) ⟨5418575, by rfl⟩ : syracuseStep 7224767 = 10837151) B10837151
theorem B4816511 : Blo 2139435 4816511 := bstep (se 1 (by rfl) ⟨3612383, by rfl⟩ : syracuseStep 4816511 = 7224767) B7224767
theorem B3211007 : Blo 2139435 3211007 := bstep (se 1 (by rfl) ⟨2408255, by rfl⟩ : syracuseStep 3211007 = 4816511) B4816511
theorem B2140671 : Blo 2139435 2140671 := bstep (se 1 (by rfl) ⟨1605503, by rfl⟩ : syracuseStep 2140671 = 3211007) B3211007
theorem B3211013 : Blo 2139435 3211013 := bbase (se 4 (by rfl) ⟨301032, by rfl⟩ : syracuseStep 3211013 = 602065) (by norm_num)
theorem B2140675 : Blo 2139435 2140675 := bstep (se 1 (by rfl) ⟨1605506, by rfl⟩ : syracuseStep 2140675 = 3211013) B3211013
theorem B3612397 : Blo 2139435 3612397 := bbase (se 3 (by rfl) ⟨677324, by rfl⟩ : syracuseStep 3612397 = 1354649) (by norm_num)
theorem B4816529 : Blo 2139435 4816529 := bstep (se 2 (by rfl) ⟨1806198, by rfl⟩ : syracuseStep 4816529 = 3612397) B3612397
theorem B3211019 : Blo 2139435 3211019 := bstep (se 1 (by rfl) ⟨2408264, by rfl⟩ : syracuseStep 3211019 = 4816529) B4816529
theorem B2140679 : Blo 2139435 2140679 := bstep (se 1 (by rfl) ⟨1605509, by rfl⟩ : syracuseStep 2140679 = 3211019) B3211019
theorem B2408269 : Blo 2139435 2408269 := bbase (se 3 (by rfl) ⟨451550, by rfl⟩ : syracuseStep 2408269 = 903101) (by norm_num)
theorem B3211025 : Blo 2139435 3211025 := bstep (se 2 (by rfl) ⟨1204134, by rfl⟩ : syracuseStep 3211025 = 2408269) B2408269
theorem B2140683 : Blo 2139435 2140683 := bstep (se 1 (by rfl) ⟨1605512, by rfl⟩ : syracuseStep 2140683 = 3211025) B3211025
theorem B7224821 : Blo 2139435 7224821 := bbase (se 5 (by rfl) ⟨338663, by rfl⟩ : syracuseStep 7224821 = 677327) (by norm_num)
theorem B4816547 : Blo 2139435 4816547 := bstep (se 1 (by rfl) ⟨3612410, by rfl⟩ : syracuseStep 4816547 = 7224821) B7224821
theorem B3211031 : Blo 2139435 3211031 := bstep (se 1 (by rfl) ⟨2408273, by rfl⟩ : syracuseStep 3211031 = 4816547) B4816547
theorem B2140687 : Blo 2139435 2140687 := bstep (se 1 (by rfl) ⟨1605515, by rfl⟩ : syracuseStep 2140687 = 3211031) B3211031
theorem B3211037 : Blo 2139435 3211037 := bbase (se 3 (by rfl) ⟨602069, by rfl⟩ : syracuseStep 3211037 = 1204139) (by norm_num)
theorem B2140691 : Blo 2139435 2140691 := bstep (se 1 (by rfl) ⟨1605518, by rfl⟩ : syracuseStep 2140691 = 3211037) B3211037
theorem B4816565 : Blo 2139435 4816565 := bbase (se 5 (by rfl) ⟨225776, by rfl⟩ : syracuseStep 4816565 = 451553) (by norm_num)
theorem B3211043 : Blo 2139435 3211043 := bstep (se 1 (by rfl) ⟨2408282, by rfl⟩ : syracuseStep 3211043 = 4816565) B4816565
theorem B2140695 : Blo 2139435 2140695 := bstep (se 1 (by rfl) ⟨1605521, by rfl⟩ : syracuseStep 2140695 = 3211043) B3211043
theorem B12191957 : Blo 2139435 12191957 := bbase (se 7 (by rfl) ⟨142874, by rfl⟩ : syracuseStep 12191957 = 285749) (by norm_num)
theorem B8127971 : Blo 2139435 8127971 := bstep (se 1 (by rfl) ⟨6095978, by rfl⟩ : syracuseStep 8127971 = 12191957) B12191957
theorem B5418647 : Blo 2139435 5418647 := bstep (se 1 (by rfl) ⟨4063985, by rfl⟩ : syracuseStep 5418647 = 8127971) B8127971
theorem B3612431 : Blo 2139435 3612431 := bstep (se 1 (by rfl) ⟨2709323, by rfl⟩ : syracuseStep 3612431 = 5418647) B5418647
theorem B2408287 : Blo 2139435 2408287 := bstep (se 1 (by rfl) ⟨1806215, by rfl⟩ : syracuseStep 2408287 = 3612431) B3612431
theorem B3211049 : Blo 2139435 3211049 := bstep (se 2 (by rfl) ⟨1204143, by rfl⟩ : syracuseStep 3211049 = 2408287) B2408287
theorem B2140699 : Blo 2139435 2140699 := bstep (se 1 (by rfl) ⟨1605524, by rfl⟩ : syracuseStep 2140699 = 3211049) B3211049
theorem B6095989 : Blo 2139435 6095989 := bbase (se 5 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 6095989 = 571499) (by norm_num)
theorem B8127985 : Blo 2139435 8127985 := bstep (se 2 (by rfl) ⟨3047994, by rfl⟩ : syracuseStep 8127985 = 6095989) B6095989
theorem B10837313 : Blo 2139435 10837313 := bstep (se 2 (by rfl) ⟨4063992, by rfl⟩ : syracuseStep 10837313 = 8127985) B8127985
theorem B7224875 : Blo 2139435 7224875 := bstep (se 1 (by rfl) ⟨5418656, by rfl⟩ : syracuseStep 7224875 = 10837313) B10837313
theorem B4816583 : Blo 2139435 4816583 := bstep (se 1 (by rfl) ⟨3612437, by rfl⟩ : syracuseStep 4816583 = 7224875) B7224875
theorem B3211055 : Blo 2139435 3211055 := bstep (se 1 (by rfl) ⟨2408291, by rfl⟩ : syracuseStep 3211055 = 4816583) B4816583
theorem B2140703 : Blo 2139435 2140703 := bstep (se 1 (by rfl) ⟨1605527, by rfl⟩ : syracuseStep 2140703 = 3211055) B3211055
theorem B3211061 : Blo 2139435 3211061 := bbase (se 5 (by rfl) ⟨150518, by rfl⟩ : syracuseStep 3211061 = 301037) (by norm_num)
theorem B2140707 : Blo 2139435 2140707 := bstep (se 1 (by rfl) ⟨1605530, by rfl⟩ : syracuseStep 2140707 = 3211061) B3211061
theorem B5418677 : Blo 2139435 5418677 := bbase (se 5 (by rfl) ⟨254000, by rfl⟩ : syracuseStep 5418677 = 508001) (by norm_num)
theorem B3612451 : Blo 2139435 3612451 := bstep (se 1 (by rfl) ⟨2709338, by rfl⟩ : syracuseStep 3612451 = 5418677) B5418677
theorem B4816601 : Blo 2139435 4816601 := bstep (se 2 (by rfl) ⟨1806225, by rfl⟩ : syracuseStep 4816601 = 3612451) B3612451
theorem B3211067 : Blo 2139435 3211067 := bstep (se 1 (by rfl) ⟨2408300, by rfl⟩ : syracuseStep 3211067 = 4816601) B4816601
theorem B2140711 : Blo 2139435 2140711 := bstep (se 1 (by rfl) ⟨1605533, by rfl⟩ : syracuseStep 2140711 = 3211067) B3211067
theorem B2408305 : Blo 2139435 2408305 := bbase (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) (by norm_num)
theorem B3211073 : Blo 2139435 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B2140715 : Blo 2139435 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B9144053 : Blo 2139435 9144053 := bbase (se 5 (by rfl) ⟨428627, by rfl⟩ : syracuseStep 9144053 = 857255) (by norm_num)
theorem B6096035 : Blo 2139435 6096035 := bstep (se 1 (by rfl) ⟨4572026, by rfl⟩ : syracuseStep 6096035 = 9144053) B9144053
theorem B4064023 : Blo 2139435 4064023 := bstep (se 1 (by rfl) ⟨3048017, by rfl⟩ : syracuseStep 4064023 = 6096035) B6096035
theorem B5418697 : Blo 2139435 5418697 := bstep (se 2 (by rfl) ⟨2032011, by rfl⟩ : syracuseStep 5418697 = 4064023) B4064023
theorem B7224929 : Blo 2139435 7224929 := bstep (se 2 (by rfl) ⟨2709348, by rfl⟩ : syracuseStep 7224929 = 5418697) B5418697
theorem B4816619 : Blo 2139435 4816619 := bstep (se 1 (by rfl) ⟨3612464, by rfl⟩ : syracuseStep 4816619 = 7224929) B7224929
theorem B3211079 : Blo 2139435 3211079 := bstep (se 1 (by rfl) ⟨2408309, by rfl⟩ : syracuseStep 3211079 = 4816619) B4816619
theorem B2140719 : Blo 2139435 2140719 := bstep (se 1 (by rfl) ⟨1605539, by rfl⟩ : syracuseStep 2140719 = 3211079) B3211079
theorem B3211085 : Blo 2139435 3211085 := bbase (se 3 (by rfl) ⟨602078, by rfl⟩ : syracuseStep 3211085 = 1204157) (by norm_num)
theorem B2140723 : Blo 2139435 2140723 := bstep (se 1 (by rfl) ⟨1605542, by rfl⟩ : syracuseStep 2140723 = 3211085) B3211085
theorem B4816637 : Blo 2139435 4816637 := bbase (se 3 (by rfl) ⟨903119, by rfl⟩ : syracuseStep 4816637 = 1806239) (by norm_num)
theorem B3211091 : Blo 2139435 3211091 := bstep (se 1 (by rfl) ⟨2408318, by rfl⟩ : syracuseStep 3211091 = 4816637) B4816637
theorem B2140727 : Blo 2139435 2140727 := bstep (se 1 (by rfl) ⟨1605545, by rfl⟩ : syracuseStep 2140727 = 3211091) B3211091
theorem B3612485 : Blo 2139435 3612485 := bbase (se 4 (by rfl) ⟨338670, by rfl⟩ : syracuseStep 3612485 = 677341) (by norm_num)
theorem B2408323 : Blo 2139435 2408323 := bstep (se 1 (by rfl) ⟨1806242, by rfl⟩ : syracuseStep 2408323 = 3612485) B3612485
theorem B3211097 : Blo 2139435 3211097 := bstep (se 2 (by rfl) ⟨1204161, by rfl⟩ : syracuseStep 3211097 = 2408323) B2408323
theorem B2140731 : Blo 2139435 2140731 := bstep (se 1 (by rfl) ⟨1605548, by rfl⟩ : syracuseStep 2140731 = 3211097) B3211097
theorem B16256213 : Blo 2139435 16256213 := bbase (se 7 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 16256213 = 381005) (by norm_num)
theorem B10837475 : Blo 2139435 10837475 := bstep (se 1 (by rfl) ⟨8128106, by rfl⟩ : syracuseStep 10837475 = 16256213) B16256213
theorem B7224983 : Blo 2139435 7224983 := bstep (se 1 (by rfl) ⟨5418737, by rfl⟩ : syracuseStep 7224983 = 10837475) B10837475
theorem B4816655 : Blo 2139435 4816655 := bstep (se 1 (by rfl) ⟨3612491, by rfl⟩ : syracuseStep 4816655 = 7224983) B7224983
theorem B3211103 : Blo 2139435 3211103 := bstep (se 1 (by rfl) ⟨2408327, by rfl⟩ : syracuseStep 3211103 = 4816655) B4816655
theorem B2140735 : Blo 2139435 2140735 := bstep (se 1 (by rfl) ⟨1605551, by rfl⟩ : syracuseStep 2140735 = 3211103) B3211103
theorem B3211109 : Blo 2139435 3211109 := bbase (se 4 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 3211109 = 602083) (by norm_num)
theorem B2140739 : Blo 2139435 2140739 := bstep (se 1 (by rfl) ⟨1605554, by rfl⟩ : syracuseStep 2140739 = 3211109) B3211109
theorem B4064069 : Blo 2139435 4064069 := bbase (se 4 (by rfl) ⟨381006, by rfl⟩ : syracuseStep 4064069 = 762013) (by norm_num)
theorem B2709379 : Blo 2139435 2709379 := bstep (se 1 (by rfl) ⟨2032034, by rfl⟩ : syracuseStep 2709379 = 4064069) B4064069
theorem B3612505 : Blo 2139435 3612505 := bstep (se 2 (by rfl) ⟨1354689, by rfl⟩ : syracuseStep 3612505 = 2709379) B2709379
theorem B4816673 : Blo 2139435 4816673 := bstep (se 2 (by rfl) ⟨1806252, by rfl⟩ : syracuseStep 4816673 = 3612505) B3612505
theorem B3211115 : Blo 2139435 3211115 := bstep (se 1 (by rfl) ⟨2408336, by rfl⟩ : syracuseStep 3211115 = 4816673) B4816673
theorem B2140743 : Blo 2139435 2140743 := bstep (se 1 (by rfl) ⟨1605557, by rfl⟩ : syracuseStep 2140743 = 3211115) B3211115
theorem B2408341 : Blo 2139435 2408341 := bbase (se 6 (by rfl) ⟨56445, by rfl⟩ : syracuseStep 2408341 = 112891) (by norm_num)
theorem B3211121 : Blo 2139435 3211121 := bstep (se 2 (by rfl) ⟨1204170, by rfl⟩ : syracuseStep 3211121 = 2408341) B2408341
theorem B2140747 : Blo 2139435 2140747 := bstep (se 1 (by rfl) ⟨1605560, by rfl⟩ : syracuseStep 2140747 = 3211121) B3211121
theorem B2709389 : Blo 2139435 2709389 := bbase (se 3 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 2709389 = 1016021) (by norm_num)
theorem B7225037 : Blo 2139435 7225037 := bstep (se 3 (by rfl) ⟨1354694, by rfl⟩ : syracuseStep 7225037 = 2709389) B2709389
theorem B4816691 : Blo 2139435 4816691 := bstep (se 1 (by rfl) ⟨3612518, by rfl⟩ : syracuseStep 4816691 = 7225037) B7225037
theorem B3211127 : Blo 2139435 3211127 := bstep (se 1 (by rfl) ⟨2408345, by rfl⟩ : syracuseStep 3211127 = 4816691) B4816691
theorem B2140751 : Blo 2139435 2140751 := bstep (se 1 (by rfl) ⟨1605563, by rfl⟩ : syracuseStep 2140751 = 3211127) B3211127
theorem B3211133 : Blo 2139435 3211133 := bbase (se 3 (by rfl) ⟨602087, by rfl⟩ : syracuseStep 3211133 = 1204175) (by norm_num)
theorem B2140755 : Blo 2139435 2140755 := bstep (se 1 (by rfl) ⟨1605566, by rfl⟩ : syracuseStep 2140755 = 3211133) B3211133
theorem B4816709 : Blo 2139435 4816709 := bbase (se 4 (by rfl) ⟨451566, by rfl⟩ : syracuseStep 4816709 = 903133) (by norm_num)
theorem B3211139 : Blo 2139435 3211139 := bstep (se 1 (by rfl) ⟨2408354, by rfl⟩ : syracuseStep 3211139 = 4816709) B4816709
theorem B2140759 : Blo 2139435 2140759 := bstep (se 1 (by rfl) ⟨1605569, by rfl⟩ : syracuseStep 2140759 = 3211139) B3211139
theorem B5143637 : Blo 2139435 5143637 := bbase (se 8 (by rfl) ⟨30138, by rfl⟩ : syracuseStep 5143637 = 60277) (by norm_num)
theorem B3429091 : Blo 2139435 3429091 := bstep (se 1 (by rfl) ⟨2571818, by rfl⟩ : syracuseStep 3429091 = 5143637) B5143637
theorem B4572121 : Blo 2139435 4572121 := bstep (se 2 (by rfl) ⟨1714545, by rfl⟩ : syracuseStep 4572121 = 3429091) B3429091
theorem B6096161 : Blo 2139435 6096161 := bstep (se 2 (by rfl) ⟨2286060, by rfl⟩ : syracuseStep 6096161 = 4572121) B4572121
theorem B4064107 : Blo 2139435 4064107 := bstep (se 1 (by rfl) ⟨3048080, by rfl⟩ : syracuseStep 4064107 = 6096161) B6096161
theorem B5418809 : Blo 2139435 5418809 := bstep (se 2 (by rfl) ⟨2032053, by rfl⟩ : syracuseStep 5418809 = 4064107) B4064107
theorem B3612539 : Blo 2139435 3612539 := bstep (se 1 (by rfl) ⟨2709404, by rfl⟩ : syracuseStep 3612539 = 5418809) B5418809
theorem B2408359 : Blo 2139435 2408359 := bstep (se 1 (by rfl) ⟨1806269, by rfl⟩ : syracuseStep 2408359 = 3612539) B3612539
theorem B3211145 : Blo 2139435 3211145 := bstep (se 2 (by rfl) ⟨1204179, by rfl⟩ : syracuseStep 3211145 = 2408359) B2408359
theorem B2140763 : Blo 2139435 2140763 := bstep (se 1 (by rfl) ⟨1605572, by rfl⟩ : syracuseStep 2140763 = 3211145) B3211145
theorem B10837637 : Blo 2139435 10837637 := bbase (se 4 (by rfl) ⟨1016028, by rfl⟩ : syracuseStep 10837637 = 2032057) (by norm_num)
theorem B7225091 : Blo 2139435 7225091 := bstep (se 1 (by rfl) ⟨5418818, by rfl⟩ : syracuseStep 7225091 = 10837637) B10837637
theorem B4816727 : Blo 2139435 4816727 := bstep (se 1 (by rfl) ⟨3612545, by rfl⟩ : syracuseStep 4816727 = 7225091) B7225091
theorem B3211151 : Blo 2139435 3211151 := bstep (se 1 (by rfl) ⟨2408363, by rfl⟩ : syracuseStep 3211151 = 4816727) B4816727
theorem B2140767 : Blo 2139435 2140767 := bstep (se 1 (by rfl) ⟨1605575, by rfl⟩ : syracuseStep 2140767 = 3211151) B3211151
theorem B3211157 : Blo 2139435 3211157 := bbase (se 6 (by rfl) ⟨75261, by rfl⟩ : syracuseStep 3211157 = 150523) (by norm_num)
theorem B2140771 : Blo 2139435 2140771 := bstep (se 1 (by rfl) ⟨1605578, by rfl⟩ : syracuseStep 2140771 = 3211157) B3211157
theorem B2286073 : Blo 2139435 2286073 := bbase (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) (by norm_num)
theorem B12192389 : Blo 2139435 12192389 := bstep (se 4 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 12192389 = 2286073) B2286073
theorem B8128259 : Blo 2139435 8128259 := bstep (se 1 (by rfl) ⟨6096194, by rfl⟩ : syracuseStep 8128259 = 12192389) B12192389
theorem B5418839 : Blo 2139435 5418839 := bstep (se 1 (by rfl) ⟨4064129, by rfl⟩ : syracuseStep 5418839 = 8128259) B8128259
theorem B3612559 : Blo 2139435 3612559 := bstep (se 1 (by rfl) ⟨2709419, by rfl⟩ : syracuseStep 3612559 = 5418839) B5418839
theorem B4816745 : Blo 2139435 4816745 := bstep (se 2 (by rfl) ⟨1806279, by rfl⟩ : syracuseStep 4816745 = 3612559) B3612559
theorem B3211163 : Blo 2139435 3211163 := bstep (se 1 (by rfl) ⟨2408372, by rfl⟩ : syracuseStep 3211163 = 4816745) B4816745
theorem B2140775 : Blo 2139435 2140775 := bstep (se 1 (by rfl) ⟨1605581, by rfl⟩ : syracuseStep 2140775 = 3211163) B3211163
theorem B2408377 : Blo 2139435 2408377 := bbase (se 2 (by rfl) ⟨903141, by rfl⟩ : syracuseStep 2408377 = 1806283) (by norm_num)
theorem B3211169 : Blo 2139435 3211169 := bstep (se 2 (by rfl) ⟨1204188, by rfl⟩ : syracuseStep 3211169 = 2408377) B2408377
theorem B2140779 : Blo 2139435 2140779 := bstep (se 1 (by rfl) ⟨1605584, by rfl⟩ : syracuseStep 2140779 = 3211169) B3211169
theorem B6858245 : Blo 2139435 6858245 := bbase (se 4 (by rfl) ⟨642960, by rfl⟩ : syracuseStep 6858245 = 1285921) (by norm_num)
theorem B4572163 : Blo 2139435 4572163 := bstep (se 1 (by rfl) ⟨3429122, by rfl⟩ : syracuseStep 4572163 = 6858245) B6858245
theorem B6096217 : Blo 2139435 6096217 := bstep (se 2 (by rfl) ⟨2286081, by rfl⟩ : syracuseStep 6096217 = 4572163) B4572163
theorem B8128289 : Blo 2139435 8128289 := bstep (se 2 (by rfl) ⟨3048108, by rfl⟩ : syracuseStep 8128289 = 6096217) B6096217
theorem B5418859 : Blo 2139435 5418859 := bstep (se 1 (by rfl) ⟨4064144, by rfl⟩ : syracuseStep 5418859 = 8128289) B8128289
theorem B7225145 : Blo 2139435 7225145 := bstep (se 2 (by rfl) ⟨2709429, by rfl⟩ : syracuseStep 7225145 = 5418859) B5418859
theorem B4816763 : Blo 2139435 4816763 := bstep (se 1 (by rfl) ⟨3612572, by rfl⟩ : syracuseStep 4816763 = 7225145) B7225145
theorem B3211175 : Blo 2139435 3211175 := bstep (se 1 (by rfl) ⟨2408381, by rfl⟩ : syracuseStep 3211175 = 4816763) B4816763
theorem B2140783 : Blo 2139435 2140783 := bstep (se 1 (by rfl) ⟨1605587, by rfl⟩ : syracuseStep 2140783 = 3211175) B3211175
theorem B3211181 : Blo 2139435 3211181 := bbase (se 3 (by rfl) ⟨602096, by rfl⟩ : syracuseStep 3211181 = 1204193) (by norm_num)
theorem B2140787 : Blo 2139435 2140787 := bstep (se 1 (by rfl) ⟨1605590, by rfl⟩ : syracuseStep 2140787 = 3211181) B3211181
theorem B4816781 : Blo 2139435 4816781 := bbase (se 3 (by rfl) ⟨903146, by rfl⟩ : syracuseStep 4816781 = 1806293) (by norm_num)
theorem B3211187 : Blo 2139435 3211187 := bstep (se 1 (by rfl) ⟨2408390, by rfl⟩ : syracuseStep 3211187 = 4816781) B4816781
theorem B2140791 : Blo 2139435 2140791 := bstep (se 1 (by rfl) ⟨1605593, by rfl⟩ : syracuseStep 2140791 = 3211187) B3211187
theorem B2709445 : Blo 2139435 2709445 := bbase (se 4 (by rfl) ⟨254010, by rfl⟩ : syracuseStep 2709445 = 508021) (by norm_num)
theorem B3612593 : Blo 2139435 3612593 := bstep (se 2 (by rfl) ⟨1354722, by rfl⟩ : syracuseStep 3612593 = 2709445) B2709445
theorem B2408395 : Blo 2139435 2408395 := bstep (se 1 (by rfl) ⟨1806296, by rfl⟩ : syracuseStep 2408395 = 3612593) B3612593
theorem B3211193 : Blo 2139435 3211193 := bstep (se 2 (by rfl) ⟨1204197, by rfl⟩ : syracuseStep 3211193 = 2408395) B2408395
theorem B2140795 : Blo 2139435 2140795 := bstep (se 1 (by rfl) ⟨1605596, by rfl⟩ : syracuseStep 2140795 = 3211193) B3211193
theorem B2317289 : Blo 2139435 2317289 := bbase (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) (by norm_num)
theorem B6179437 : Blo 2139435 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B8239249 : Blo 2139435 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B43942661 : Blo 2139435 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B29295107 : Blo 2139435 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B19530071 : Blo 2139435 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B13020047 : Blo 2139435 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B8680031 : Blo 2139435 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B5786687 : Blo 2139435 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B15431165 : Blo 2139435 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B10287443 : Blo 2139435 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B27433181 : Blo 2139435 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B18288787 : Blo 2139435 18288787 := bstep (se 1 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 18288787 = 27433181) B27433181
theorem B24385049 : Blo 2139435 24385049 := bstep (se 2 (by rfl) ⟨9144393, by rfl⟩ : syracuseStep 24385049 = 18288787) B18288787
theorem B16256699 : Blo 2139435 16256699 := bstep (se 1 (by rfl) ⟨12192524, by rfl⟩ : syracuseStep 16256699 = 24385049) B24385049
theorem B10837799 : Blo 2139435 10837799 := bstep (se 1 (by rfl) ⟨8128349, by rfl⟩ : syracuseStep 10837799 = 16256699) B16256699
theorem B7225199 : Blo 2139435 7225199 := bstep (se 1 (by rfl) ⟨5418899, by rfl⟩ : syracuseStep 7225199 = 10837799) B10837799
theorem B4816799 : Blo 2139435 4816799 := bstep (se 1 (by rfl) ⟨3612599, by rfl⟩ : syracuseStep 4816799 = 7225199) B7225199
theorem B3211199 : Blo 2139435 3211199 := bstep (se 1 (by rfl) ⟨2408399, by rfl⟩ : syracuseStep 3211199 = 4816799) B4816799
theorem B2140799 : Blo 2139435 2140799 := bstep (se 1 (by rfl) ⟨1605599, by rfl⟩ : syracuseStep 2140799 = 3211199) B3211199
theorem B3211205 : Blo 2139435 3211205 := bbase (se 4 (by rfl) ⟨301050, by rfl⟩ : syracuseStep 3211205 = 602101) (by norm_num)
theorem B2140803 : Blo 2139435 2140803 := bstep (se 1 (by rfl) ⟨1605602, by rfl⟩ : syracuseStep 2140803 = 3211205) B3211205
theorem B3612613 : Blo 2139435 3612613 := bbase (se 4 (by rfl) ⟨338682, by rfl⟩ : syracuseStep 3612613 = 677365) (by norm_num)
theorem B4816817 : Blo 2139435 4816817 := bstep (se 2 (by rfl) ⟨1806306, by rfl⟩ : syracuseStep 4816817 = 3612613) B3612613
theorem B3211211 : Blo 2139435 3211211 := bstep (se 1 (by rfl) ⟨2408408, by rfl⟩ : syracuseStep 3211211 = 4816817) B4816817
theorem B2140807 : Blo 2139435 2140807 := bstep (se 1 (by rfl) ⟨1605605, by rfl⟩ : syracuseStep 2140807 = 3211211) B3211211
theorem B2408413 : Blo 2139435 2408413 := bbase (se 3 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 2408413 = 903155) (by norm_num)
theorem B3211217 : Blo 2139435 3211217 := bstep (se 2 (by rfl) ⟨1204206, by rfl⟩ : syracuseStep 3211217 = 2408413) B2408413
theorem B2140811 : Blo 2139435 2140811 := bstep (se 1 (by rfl) ⟨1605608, by rfl⟩ : syracuseStep 2140811 = 3211217) B3211217
theorem B7225253 : Blo 2139435 7225253 := bbase (se 4 (by rfl) ⟨677367, by rfl⟩ : syracuseStep 7225253 = 1354735) (by norm_num)
theorem B4816835 : Blo 2139435 4816835 := bstep (se 1 (by rfl) ⟨3612626, by rfl⟩ : syracuseStep 4816835 = 7225253) B7225253
theorem B3211223 : Blo 2139435 3211223 := bstep (se 1 (by rfl) ⟨2408417, by rfl⟩ : syracuseStep 3211223 = 4816835) B4816835
theorem B2140815 : Blo 2139435 2140815 := bstep (se 1 (by rfl) ⟨1605611, by rfl⟩ : syracuseStep 2140815 = 3211223) B3211223
theorem B3211229 : Blo 2139435 3211229 := bbase (se 3 (by rfl) ⟨602105, by rfl⟩ : syracuseStep 3211229 = 1204211) (by norm_num)
theorem B2140819 : Blo 2139435 2140819 := bstep (se 1 (by rfl) ⟨1605614, by rfl⟩ : syracuseStep 2140819 = 3211229) B3211229
theorem B4816853 : Blo 2139435 4816853 := bbase (se 7 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 4816853 = 112895) (by norm_num)
theorem B3211235 : Blo 2139435 3211235 := bstep (se 1 (by rfl) ⟨2408426, by rfl⟩ : syracuseStep 3211235 = 4816853) B4816853
theorem B2140823 : Blo 2139435 2140823 := bstep (se 1 (by rfl) ⟨1605617, by rfl⟩ : syracuseStep 2140823 = 3211235) B3211235
theorem B2170037 : Blo 2139435 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B5786765 : Blo 2139435 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B3857843 : Blo 2139435 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B2571895 : Blo 2139435 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B13716773 : Blo 2139435 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B9144515 : Blo 2139435 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B6096343 : Blo 2139435 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B8128457 : Blo 2139435 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B5418971 : Blo 2139435 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B3612647 : Blo 2139435 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B2408431 : Blo 2139435 2408431 := bstep (se 1 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 2408431 = 3612647) B3612647
theorem B3211241 : Blo 2139435 3211241 := bstep (se 2 (by rfl) ⟨1204215, by rfl⟩ : syracuseStep 3211241 = 2408431) B2408431
theorem B2140827 : Blo 2139435 2140827 := bstep (se 1 (by rfl) ⟨1605620, by rfl⟩ : syracuseStep 2140827 = 3211241) B3211241
theorem B3255061 : Blo 2139435 3255061 := bbase (se 6 (by rfl) ⟨76290, by rfl⟩ : syracuseStep 3255061 = 152581) (by norm_num)
theorem B4340081 : Blo 2139435 4340081 := bstep (se 2 (by rfl) ⟨1627530, by rfl⟩ : syracuseStep 4340081 = 3255061) B3255061
theorem B11573549 : Blo 2139435 11573549 := bstep (se 3 (by rfl) ⟨2170040, by rfl⟩ : syracuseStep 11573549 = 4340081) B4340081
theorem B7715699 : Blo 2139435 7715699 := bstep (se 1 (by rfl) ⟨5786774, by rfl⟩ : syracuseStep 7715699 = 11573549) B11573549
theorem B5143799 : Blo 2139435 5143799 := bstep (se 1 (by rfl) ⟨3857849, by rfl⟩ : syracuseStep 5143799 = 7715699) B7715699
theorem B3429199 : Blo 2139435 3429199 := bstep (se 1 (by rfl) ⟨2571899, by rfl⟩ : syracuseStep 3429199 = 5143799) B5143799
theorem B18289061 : Blo 2139435 18289061 := bstep (se 4 (by rfl) ⟨1714599, by rfl⟩ : syracuseStep 18289061 = 3429199) B3429199
theorem B12192707 : Blo 2139435 12192707 := bstep (se 1 (by rfl) ⟨9144530, by rfl⟩ : syracuseStep 12192707 = 18289061) B18289061
theorem B8128471 : Blo 2139435 8128471 := bstep (se 1 (by rfl) ⟨6096353, by rfl⟩ : syracuseStep 8128471 = 12192707) B12192707
theorem B10837961 : Blo 2139435 10837961 := bstep (se 2 (by rfl) ⟨4064235, by rfl⟩ : syracuseStep 10837961 = 8128471) B8128471
theorem B7225307 : Blo 2139435 7225307 := bstep (se 1 (by rfl) ⟨5418980, by rfl⟩ : syracuseStep 7225307 = 10837961) B10837961
theorem B4816871 : Blo 2139435 4816871 := bstep (se 1 (by rfl) ⟨3612653, by rfl⟩ : syracuseStep 4816871 = 7225307) B7225307
theorem B3211247 : Blo 2139435 3211247 := bstep (se 1 (by rfl) ⟨2408435, by rfl⟩ : syracuseStep 3211247 = 4816871) B4816871
theorem B2140831 : Blo 2139435 2140831 := bstep (se 1 (by rfl) ⟨1605623, by rfl⟩ : syracuseStep 2140831 = 3211247) B3211247
theorem B3211253 : Blo 2139435 3211253 := bbase (se 5 (by rfl) ⟨150527, by rfl⟩ : syracuseStep 3211253 = 301055) (by norm_num)
theorem B2140835 : Blo 2139435 2140835 := bstep (se 1 (by rfl) ⟨1605626, by rfl⟩ : syracuseStep 2140835 = 3211253) B3211253
theorem B2170049 : Blo 2139435 2170049 := bbase (se 2 (by rfl) ⟨813768, by rfl⟩ : syracuseStep 2170049 = 1627537) (by norm_num)
theorem B5786797 : Blo 2139435 5786797 := bstep (se 3 (by rfl) ⟨1085024, by rfl⟩ : syracuseStep 5786797 = 2170049) B2170049
theorem B7715729 : Blo 2139435 7715729 := bstep (se 2 (by rfl) ⟨2893398, by rfl⟩ : syracuseStep 7715729 = 5786797) B5786797
theorem B5143819 : Blo 2139435 5143819 := bstep (se 1 (by rfl) ⟨3857864, by rfl⟩ : syracuseStep 5143819 = 7715729) B7715729
theorem B6858425 : Blo 2139435 6858425 := bstep (se 2 (by rfl) ⟨2571909, by rfl⟩ : syracuseStep 6858425 = 5143819) B5143819
theorem B4572283 : Blo 2139435 4572283 := bstep (se 1 (by rfl) ⟨3429212, by rfl⟩ : syracuseStep 4572283 = 6858425) B6858425
theorem B6096377 : Blo 2139435 6096377 := bstep (se 2 (by rfl) ⟨2286141, by rfl⟩ : syracuseStep 6096377 = 4572283) B4572283
theorem B4064251 : Blo 2139435 4064251 := bstep (se 1 (by rfl) ⟨3048188, by rfl⟩ : syracuseStep 4064251 = 6096377) B6096377
theorem B5419001 : Blo 2139435 5419001 := bstep (se 2 (by rfl) ⟨2032125, by rfl⟩ : syracuseStep 5419001 = 4064251) B4064251
theorem B3612667 : Blo 2139435 3612667 := bstep (se 1 (by rfl) ⟨2709500, by rfl⟩ : syracuseStep 3612667 = 5419001) B5419001
theorem B4816889 : Blo 2139435 4816889 := bstep (se 2 (by rfl) ⟨1806333, by rfl⟩ : syracuseStep 4816889 = 3612667) B3612667
theorem B3211259 : Blo 2139435 3211259 := bstep (se 1 (by rfl) ⟨2408444, by rfl⟩ : syracuseStep 3211259 = 4816889) B4816889
theorem B2140839 : Blo 2139435 2140839 := bstep (se 1 (by rfl) ⟨1605629, by rfl⟩ : syracuseStep 2140839 = 3211259) B3211259
theorem B2408449 : Blo 2139435 2408449 := bbase (se 2 (by rfl) ⟨903168, by rfl⟩ : syracuseStep 2408449 = 1806337) (by norm_num)
theorem B3211265 : Blo 2139435 3211265 := bstep (se 2 (by rfl) ⟨1204224, by rfl⟩ : syracuseStep 3211265 = 2408449) B2408449
theorem B2140843 : Blo 2139435 2140843 := bstep (se 1 (by rfl) ⟨1605632, by rfl⟩ : syracuseStep 2140843 = 3211265) B3211265
theorem B5419021 : Blo 2139435 5419021 := bbase (se 3 (by rfl) ⟨1016066, by rfl⟩ : syracuseStep 5419021 = 2032133) (by norm_num)
theorem B7225361 : Blo 2139435 7225361 := bstep (se 2 (by rfl) ⟨2709510, by rfl⟩ : syracuseStep 7225361 = 5419021) B5419021
theorem B4816907 : Blo 2139435 4816907 := bstep (se 1 (by rfl) ⟨3612680, by rfl⟩ : syracuseStep 4816907 = 7225361) B7225361
theorem B3211271 : Blo 2139435 3211271 := bstep (se 1 (by rfl) ⟨2408453, by rfl⟩ : syracuseStep 3211271 = 4816907) B4816907
theorem B2140847 : Blo 2139435 2140847 := bstep (se 1 (by rfl) ⟨1605635, by rfl⟩ : syracuseStep 2140847 = 3211271) B3211271
theorem B3211277 : Blo 2139435 3211277 := bbase (se 3 (by rfl) ⟨602114, by rfl⟩ : syracuseStep 3211277 = 1204229) (by norm_num)
theorem B2140851 : Blo 2139435 2140851 := bstep (se 1 (by rfl) ⟨1605638, by rfl⟩ : syracuseStep 2140851 = 3211277) B3211277
theorem B4816925 : Blo 2139435 4816925 := bbase (se 3 (by rfl) ⟨903173, by rfl⟩ : syracuseStep 4816925 = 1806347) (by norm_num)
theorem B3211283 : Blo 2139435 3211283 := bstep (se 1 (by rfl) ⟨2408462, by rfl⟩ : syracuseStep 3211283 = 4816925) B4816925
theorem B2140855 : Blo 2139435 2140855 := bstep (se 1 (by rfl) ⟨1605641, by rfl⟩ : syracuseStep 2140855 = 3211283) B3211283
theorem B3612701 : Blo 2139435 3612701 := bbase (se 3 (by rfl) ⟨677381, by rfl⟩ : syracuseStep 3612701 = 1354763) (by norm_num)
theorem B2408467 : Blo 2139435 2408467 := bstep (se 1 (by rfl) ⟨1806350, by rfl⟩ : syracuseStep 2408467 = 3612701) B3612701
theorem B3211289 : Blo 2139435 3211289 := bstep (se 2 (by rfl) ⟨1204233, by rfl⟩ : syracuseStep 3211289 = 2408467) B2408467
theorem B2140859 : Blo 2139435 2140859 := bstep (se 1 (by rfl) ⟨1605644, by rfl⟩ : syracuseStep 2140859 = 3211289) B3211289
theorem B3255109 : Blo 2139435 3255109 := bbase (se 4 (by rfl) ⟨305166, by rfl⟩ : syracuseStep 3255109 = 610333) (by norm_num)
theorem B17360581 : Blo 2139435 17360581 := bstep (se 4 (by rfl) ⟨1627554, by rfl⟩ : syracuseStep 17360581 = 3255109) B3255109
theorem B23147441 : Blo 2139435 23147441 := bstep (se 2 (by rfl) ⟨8680290, by rfl⟩ : syracuseStep 23147441 = 17360581) B17360581
theorem B15431627 : Blo 2139435 15431627 := bstep (se 1 (by rfl) ⟨11573720, by rfl⟩ : syracuseStep 15431627 = 23147441) B23147441
theorem B10287751 : Blo 2139435 10287751 := bstep (se 1 (by rfl) ⟨7715813, by rfl⟩ : syracuseStep 10287751 = 15431627) B15431627
theorem B13717001 : Blo 2139435 13717001 := bstep (se 2 (by rfl) ⟨5143875, by rfl⟩ : syracuseStep 13717001 = 10287751) B10287751
theorem B9144667 : Blo 2139435 9144667 := bstep (se 1 (by rfl) ⟨6858500, by rfl⟩ : syracuseStep 9144667 = 13717001) B13717001
theorem B12192889 : Blo 2139435 12192889 := bstep (se 2 (by rfl) ⟨4572333, by rfl⟩ : syracuseStep 12192889 = 9144667) B9144667
theorem B16257185 : Blo 2139435 16257185 := bstep (se 2 (by rfl) ⟨6096444, by rfl⟩ : syracuseStep 16257185 = 12192889) B12192889
theorem B10838123 : Blo 2139435 10838123 := bstep (se 1 (by rfl) ⟨8128592, by rfl⟩ : syracuseStep 10838123 = 16257185) B16257185
theorem B7225415 : Blo 2139435 7225415 := bstep (se 1 (by rfl) ⟨5419061, by rfl⟩ : syracuseStep 7225415 = 10838123) B10838123
theorem B4816943 : Blo 2139435 4816943 := bstep (se 1 (by rfl) ⟨3612707, by rfl⟩ : syracuseStep 4816943 = 7225415) B7225415
theorem B3211295 : Blo 2139435 3211295 := bstep (se 1 (by rfl) ⟨2408471, by rfl⟩ : syracuseStep 3211295 = 4816943) B4816943
theorem B2140863 : Blo 2139435 2140863 := bstep (se 1 (by rfl) ⟨1605647, by rfl⟩ : syracuseStep 2140863 = 3211295) B3211295
theorem B3211301 : Blo 2139435 3211301 := bbase (se 4 (by rfl) ⟨301059, by rfl⟩ : syracuseStep 3211301 = 602119) (by norm_num)
theorem B2140867 : Blo 2139435 2140867 := bstep (se 1 (by rfl) ⟨1605650, by rfl⟩ : syracuseStep 2140867 = 3211301) B3211301
theorem B2709541 : Blo 2139435 2709541 := bbase (se 4 (by rfl) ⟨254019, by rfl⟩ : syracuseStep 2709541 = 508039) (by norm_num)
theorem B3612721 : Blo 2139435 3612721 := bstep (se 2 (by rfl) ⟨1354770, by rfl⟩ : syracuseStep 3612721 = 2709541) B2709541
theorem B4816961 : Blo 2139435 4816961 := bstep (se 2 (by rfl) ⟨1806360, by rfl⟩ : syracuseStep 4816961 = 3612721) B3612721
theorem B3211307 : Blo 2139435 3211307 := bstep (se 1 (by rfl) ⟨2408480, by rfl⟩ : syracuseStep 3211307 = 4816961) B4816961
theorem B2140871 : Blo 2139435 2140871 := bstep (se 1 (by rfl) ⟨1605653, by rfl⟩ : syracuseStep 2140871 = 3211307) B3211307
theorem B2408485 : Blo 2139435 2408485 := bbase (se 4 (by rfl) ⟨225795, by rfl⟩ : syracuseStep 2408485 = 451591) (by norm_num)
theorem B3211313 : Blo 2139435 3211313 := bstep (se 2 (by rfl) ⟨1204242, by rfl⟩ : syracuseStep 3211313 = 2408485) B2408485
theorem B2140875 : Blo 2139435 2140875 := bstep (se 1 (by rfl) ⟨1605656, by rfl⟩ : syracuseStep 2140875 = 3211313) B3211313
theorem B4119781 : Blo 2139435 4119781 := bbase (se 4 (by rfl) ⟨386229, by rfl⟩ : syracuseStep 4119781 = 772459) (by norm_num)
theorem B5493041 : Blo 2139435 5493041 := bstep (se 2 (by rfl) ⟨2059890, by rfl⟩ : syracuseStep 5493041 = 4119781) B4119781
theorem B3662027 : Blo 2139435 3662027 := bstep (se 1 (by rfl) ⟨2746520, by rfl⟩ : syracuseStep 3662027 = 5493041) B5493041
theorem B2441351 : Blo 2139435 2441351 := bstep (se 1 (by rfl) ⟨1831013, by rfl⟩ : syracuseStep 2441351 = 3662027) B3662027
theorem B6510269 : Blo 2139435 6510269 := bstep (se 3 (by rfl) ⟨1220675, by rfl⟩ : syracuseStep 6510269 = 2441351) B2441351
theorem B4340179 : Blo 2139435 4340179 := bstep (se 1 (by rfl) ⟨3255134, by rfl⟩ : syracuseStep 4340179 = 6510269) B6510269
theorem B5786905 : Blo 2139435 5786905 := bstep (se 2 (by rfl) ⟨2170089, by rfl⟩ : syracuseStep 5786905 = 4340179) B4340179
theorem B7715873 : Blo 2139435 7715873 := bstep (se 2 (by rfl) ⟨2893452, by rfl⟩ : syracuseStep 7715873 = 5786905) B5786905
theorem B5143915 : Blo 2139435 5143915 := bstep (se 1 (by rfl) ⟨3857936, by rfl⟩ : syracuseStep 5143915 = 7715873) B7715873
theorem B6858553 : Blo 2139435 6858553 := bstep (se 2 (by rfl) ⟨2571957, by rfl⟩ : syracuseStep 6858553 = 5143915) B5143915
theorem B9144737 : Blo 2139435 9144737 := bstep (se 2 (by rfl) ⟨3429276, by rfl⟩ : syracuseStep 9144737 = 6858553) B6858553
theorem B6096491 : Blo 2139435 6096491 := bstep (se 1 (by rfl) ⟨4572368, by rfl⟩ : syracuseStep 6096491 = 9144737) B9144737
theorem B4064327 : Blo 2139435 4064327 := bstep (se 1 (by rfl) ⟨3048245, by rfl⟩ : syracuseStep 4064327 = 6096491) B6096491
theorem B2709551 : Blo 2139435 2709551 := bstep (se 1 (by rfl) ⟨2032163, by rfl⟩ : syracuseStep 2709551 = 4064327) B4064327
theorem B7225469 : Blo 2139435 7225469 := bstep (se 3 (by rfl) ⟨1354775, by rfl⟩ : syracuseStep 7225469 = 2709551) B2709551
theorem B4816979 : Blo 2139435 4816979 := bstep (se 1 (by rfl) ⟨3612734, by rfl⟩ : syracuseStep 4816979 = 7225469) B7225469
theorem B3211319 : Blo 2139435 3211319 := bstep (se 1 (by rfl) ⟨2408489, by rfl⟩ : syracuseStep 3211319 = 4816979) B4816979
theorem B2140879 : Blo 2139435 2140879 := bstep (se 1 (by rfl) ⟨1605659, by rfl⟩ : syracuseStep 2140879 = 3211319) B3211319
theorem B3211325 : Blo 2139435 3211325 := bbase (se 3 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 3211325 = 1204247) (by norm_num)
theorem B2140883 : Blo 2139435 2140883 := bstep (se 1 (by rfl) ⟨1605662, by rfl⟩ : syracuseStep 2140883 = 3211325) B3211325
theorem B4816997 : Blo 2139435 4816997 := bbase (se 4 (by rfl) ⟨451593, by rfl⟩ : syracuseStep 4816997 = 903187) (by norm_num)
theorem B3211331 : Blo 2139435 3211331 := bstep (se 1 (by rfl) ⟨2408498, by rfl⟩ : syracuseStep 3211331 = 4816997) B4816997
theorem B2140887 : Blo 2139435 2140887 := bstep (se 1 (by rfl) ⟨1605665, by rfl⟩ : syracuseStep 2140887 = 3211331) B3211331
theorem B5419133 : Blo 2139435 5419133 := bbase (se 3 (by rfl) ⟨1016087, by rfl⟩ : syracuseStep 5419133 = 2032175) (by norm_num)
theorem B3612755 : Blo 2139435 3612755 := bstep (se 1 (by rfl) ⟨2709566, by rfl⟩ : syracuseStep 3612755 = 5419133) B5419133
theorem B2408503 : Blo 2139435 2408503 := bstep (se 1 (by rfl) ⟨1806377, by rfl⟩ : syracuseStep 2408503 = 3612755) B3612755
theorem B3211337 : Blo 2139435 3211337 := bstep (se 2 (by rfl) ⟨1204251, by rfl⟩ : syracuseStep 3211337 = 2408503) B2408503
theorem B2140891 : Blo 2139435 2140891 := bstep (se 1 (by rfl) ⟨1605668, by rfl⟩ : syracuseStep 2140891 = 3211337) B3211337
theorem B4064357 : Blo 2139435 4064357 := bbase (se 4 (by rfl) ⟨381033, by rfl⟩ : syracuseStep 4064357 = 762067) (by norm_num)
theorem B10838285 : Blo 2139435 10838285 := bstep (se 3 (by rfl) ⟨2032178, by rfl⟩ : syracuseStep 10838285 = 4064357) B4064357
theorem B7225523 : Blo 2139435 7225523 := bstep (se 1 (by rfl) ⟨5419142, by rfl⟩ : syracuseStep 7225523 = 10838285) B10838285
theorem B4817015 : Blo 2139435 4817015 := bstep (se 1 (by rfl) ⟨3612761, by rfl⟩ : syracuseStep 4817015 = 7225523) B7225523
theorem B3211343 : Blo 2139435 3211343 := bstep (se 1 (by rfl) ⟨2408507, by rfl⟩ : syracuseStep 3211343 = 4817015) B4817015
theorem B2140895 : Blo 2139435 2140895 := bstep (se 1 (by rfl) ⟨1605671, by rfl⟩ : syracuseStep 2140895 = 3211343) B3211343
theorem B3211349 : Blo 2139435 3211349 := bbase (se 8 (by rfl) ⟨18816, by rfl⟩ : syracuseStep 3211349 = 37633) (by norm_num)
theorem B2140899 : Blo 2139435 2140899 := bstep (se 1 (by rfl) ⟨1605674, by rfl⟩ : syracuseStep 2140899 = 3211349) B3211349
theorem B6510341 : Blo 2139435 6510341 := bbase (se 4 (by rfl) ⟨610344, by rfl⟩ : syracuseStep 6510341 = 1220689) (by norm_num)
theorem B4340227 : Blo 2139435 4340227 := bstep (se 1 (by rfl) ⟨3255170, by rfl⟩ : syracuseStep 4340227 = 6510341) B6510341
theorem B5786969 : Blo 2139435 5786969 := bstep (se 2 (by rfl) ⟨2170113, by rfl⟩ : syracuseStep 5786969 = 4340227) B4340227
theorem B15431917 : Blo 2139435 15431917 := bstep (se 3 (by rfl) ⟨2893484, by rfl⟩ : syracuseStep 15431917 = 5786969) B5786969
theorem B20575889 : Blo 2139435 20575889 := bstep (se 2 (by rfl) ⟨7715958, by rfl⟩ : syracuseStep 20575889 = 15431917) B15431917
theorem B13717259 : Blo 2139435 13717259 := bstep (se 1 (by rfl) ⟨10287944, by rfl⟩ : syracuseStep 13717259 = 20575889) B20575889
theorem B9144839 : Blo 2139435 9144839 := bstep (se 1 (by rfl) ⟨6858629, by rfl⟩ : syracuseStep 9144839 = 13717259) B13717259
theorem B6096559 : Blo 2139435 6096559 := bstep (se 1 (by rfl) ⟨4572419, by rfl⟩ : syracuseStep 6096559 = 9144839) B9144839
theorem B8128745 : Blo 2139435 8128745 := bstep (se 2 (by rfl) ⟨3048279, by rfl⟩ : syracuseStep 8128745 = 6096559) B6096559
theorem B5419163 : Blo 2139435 5419163 := bstep (se 1 (by rfl) ⟨4064372, by rfl⟩ : syracuseStep 5419163 = 8128745) B8128745
theorem B3612775 : Blo 2139435 3612775 := bstep (se 1 (by rfl) ⟨2709581, by rfl⟩ : syracuseStep 3612775 = 5419163) B5419163
theorem B4817033 : Blo 2139435 4817033 := bstep (se 2 (by rfl) ⟨1806387, by rfl⟩ : syracuseStep 4817033 = 3612775) B3612775
theorem B3211355 : Blo 2139435 3211355 := bstep (se 1 (by rfl) ⟨2408516, by rfl⟩ : syracuseStep 3211355 = 4817033) B4817033
theorem B2140903 : Blo 2139435 2140903 := bstep (se 1 (by rfl) ⟨1605677, by rfl⟩ : syracuseStep 2140903 = 3211355) B3211355
theorem B2408521 : Blo 2139435 2408521 := bbase (se 2 (by rfl) ⟨903195, by rfl⟩ : syracuseStep 2408521 = 1806391) (by norm_num)
theorem B3211361 : Blo 2139435 3211361 := bstep (se 2 (by rfl) ⟨1204260, by rfl⟩ : syracuseStep 3211361 = 2408521) B2408521
theorem B2140907 : Blo 2139435 2140907 := bstep (se 1 (by rfl) ⟨1605680, by rfl⟩ : syracuseStep 2140907 = 3211361) B3211361
theorem B2746561 : Blo 2139435 2746561 := bbase (se 2 (by rfl) ⟨1029960, by rfl⟩ : syracuseStep 2746561 = 2059921) (by norm_num)
theorem B3662081 : Blo 2139435 3662081 := bstep (se 2 (by rfl) ⟨1373280, by rfl⟩ : syracuseStep 3662081 = 2746561) B2746561
theorem B2441387 : Blo 2139435 2441387 := bstep (se 1 (by rfl) ⟨1831040, by rfl⟩ : syracuseStep 2441387 = 3662081) B3662081
theorem B6510365 : Blo 2139435 6510365 := bstep (se 3 (by rfl) ⟨1220693, by rfl⟩ : syracuseStep 6510365 = 2441387) B2441387
theorem B4340243 : Blo 2139435 4340243 := bstep (se 1 (by rfl) ⟨3255182, by rfl⟩ : syracuseStep 4340243 = 6510365) B6510365
theorem B11573981 : Blo 2139435 11573981 := bstep (se 3 (by rfl) ⟨2170121, by rfl⟩ : syracuseStep 11573981 = 4340243) B4340243
theorem B7715987 : Blo 2139435 7715987 := bstep (se 1 (by rfl) ⟨5786990, by rfl⟩ : syracuseStep 7715987 = 11573981) B11573981
theorem B5143991 : Blo 2139435 5143991 := bstep (se 1 (by rfl) ⟨3857993, by rfl⟩ : syracuseStep 5143991 = 7715987) B7715987
theorem B13717309 : Blo 2139435 13717309 := bstep (se 3 (by rfl) ⟨2571995, by rfl⟩ : syracuseStep 13717309 = 5143991) B5143991
theorem B18289745 : Blo 2139435 18289745 := bstep (se 2 (by rfl) ⟨6858654, by rfl⟩ : syracuseStep 18289745 = 13717309) B13717309
theorem B12193163 : Blo 2139435 12193163 := bstep (se 1 (by rfl) ⟨9144872, by rfl⟩ : syracuseStep 12193163 = 18289745) B18289745
theorem B8128775 : Blo 2139435 8128775 := bstep (se 1 (by rfl) ⟨6096581, by rfl⟩ : syracuseStep 8128775 = 12193163) B12193163
theorem B5419183 : Blo 2139435 5419183 := bstep (se 1 (by rfl) ⟨4064387, by rfl⟩ : syracuseStep 5419183 = 8128775) B8128775
theorem B7225577 : Blo 2139435 7225577 := bstep (se 2 (by rfl) ⟨2709591, by rfl⟩ : syracuseStep 7225577 = 5419183) B5419183
theorem B4817051 : Blo 2139435 4817051 := bstep (se 1 (by rfl) ⟨3612788, by rfl⟩ : syracuseStep 4817051 = 7225577) B7225577
theorem B3211367 : Blo 2139435 3211367 := bstep (se 1 (by rfl) ⟨2408525, by rfl⟩ : syracuseStep 3211367 = 4817051) B4817051
theorem B2140911 : Blo 2139435 2140911 := bstep (se 1 (by rfl) ⟨1605683, by rfl⟩ : syracuseStep 2140911 = 3211367) B3211367
theorem B3211373 : Blo 2139435 3211373 := bbase (se 3 (by rfl) ⟨602132, by rfl⟩ : syracuseStep 3211373 = 1204265) (by norm_num)
theorem B2140915 : Blo 2139435 2140915 := bstep (se 1 (by rfl) ⟨1605686, by rfl⟩ : syracuseStep 2140915 = 3211373) B3211373
theorem B4817069 : Blo 2139435 4817069 := bbase (se 3 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 4817069 = 1806401) (by norm_num)
theorem B3211379 : Blo 2139435 3211379 := bstep (se 1 (by rfl) ⟨2408534, by rfl⟩ : syracuseStep 3211379 = 4817069) B4817069
theorem B2140919 : Blo 2139435 2140919 := bstep (se 1 (by rfl) ⟨1605689, by rfl⟩ : syracuseStep 2140919 = 3211379) B3211379
theorem B9765605 : Blo 2139435 9765605 := bbase (se 4 (by rfl) ⟨915525, by rfl⟩ : syracuseStep 9765605 = 1831051) (by norm_num)
theorem B6510403 : Blo 2139435 6510403 := bstep (se 1 (by rfl) ⟨4882802, by rfl⟩ : syracuseStep 6510403 = 9765605) B9765605
theorem B8680537 : Blo 2139435 8680537 := bstep (se 2 (by rfl) ⟨3255201, by rfl⟩ : syracuseStep 8680537 = 6510403) B6510403
theorem B11574049 : Blo 2139435 11574049 := bstep (se 2 (by rfl) ⟨4340268, by rfl⟩ : syracuseStep 11574049 = 8680537) B8680537
theorem B15432065 : Blo 2139435 15432065 := bstep (se 2 (by rfl) ⟨5787024, by rfl⟩ : syracuseStep 15432065 = 11574049) B11574049
theorem B10288043 : Blo 2139435 10288043 := bstep (se 1 (by rfl) ⟨7716032, by rfl⟩ : syracuseStep 10288043 = 15432065) B15432065
theorem B6858695 : Blo 2139435 6858695 := bstep (se 1 (by rfl) ⟨5144021, by rfl⟩ : syracuseStep 6858695 = 10288043) B10288043
theorem B4572463 : Blo 2139435 4572463 := bstep (se 1 (by rfl) ⟨3429347, by rfl⟩ : syracuseStep 4572463 = 6858695) B6858695
theorem B6096617 : Blo 2139435 6096617 := bstep (se 2 (by rfl) ⟨2286231, by rfl⟩ : syracuseStep 6096617 = 4572463) B4572463
theorem B4064411 : Blo 2139435 4064411 := bstep (se 1 (by rfl) ⟨3048308, by rfl⟩ : syracuseStep 4064411 = 6096617) B6096617
theorem B2709607 : Blo 2139435 2709607 := bstep (se 1 (by rfl) ⟨2032205, by rfl⟩ : syracuseStep 2709607 = 4064411) B4064411
theorem B3612809 : Blo 2139435 3612809 := bstep (se 2 (by rfl) ⟨1354803, by rfl⟩ : syracuseStep 3612809 = 2709607) B2709607
theorem B2408539 : Blo 2139435 2408539 := bstep (se 1 (by rfl) ⟨1806404, by rfl⟩ : syracuseStep 2408539 = 3612809) B3612809
theorem B3211385 : Blo 2139435 3211385 := bstep (se 2 (by rfl) ⟨1204269, by rfl⟩ : syracuseStep 3211385 = 2408539) B2408539
theorem B2140923 : Blo 2139435 2140923 := bstep (se 1 (by rfl) ⟨1605692, by rfl⟩ : syracuseStep 2140923 = 3211385) B3211385
theorem B5144029 : Blo 2139435 5144029 := bbase (se 3 (by rfl) ⟨964505, by rfl⟩ : syracuseStep 5144029 = 1929011) (by norm_num)
theorem B27434821 : Blo 2139435 27434821 := bstep (se 4 (by rfl) ⟨2572014, by rfl⟩ : syracuseStep 27434821 = 5144029) B5144029
theorem B36579761 : Blo 2139435 36579761 := bstep (se 2 (by rfl) ⟨13717410, by rfl⟩ : syracuseStep 36579761 = 27434821) B27434821
theorem B24386507 : Blo 2139435 24386507 := bstep (se 1 (by rfl) ⟨18289880, by rfl⟩ : syracuseStep 24386507 = 36579761) B36579761
theorem B16257671 : Blo 2139435 16257671 := bstep (se 1 (by rfl) ⟨12193253, by rfl⟩ : syracuseStep 16257671 = 24386507) B24386507
theorem B10838447 : Blo 2139435 10838447 := bstep (se 1 (by rfl) ⟨8128835, by rfl⟩ : syracuseStep 10838447 = 16257671) B16257671
theorem B7225631 : Blo 2139435 7225631 := bstep (se 1 (by rfl) ⟨5419223, by rfl⟩ : syracuseStep 7225631 = 10838447) B10838447
theorem B4817087 : Blo 2139435 4817087 := bstep (se 1 (by rfl) ⟨3612815, by rfl⟩ : syracuseStep 4817087 = 7225631) B7225631
theorem B3211391 : Blo 2139435 3211391 := bstep (se 1 (by rfl) ⟨2408543, by rfl⟩ : syracuseStep 3211391 = 4817087) B4817087
theorem B2140927 : Blo 2139435 2140927 := bstep (se 1 (by rfl) ⟨1605695, by rfl⟩ : syracuseStep 2140927 = 3211391) B3211391
theorem B3211397 : Blo 2139435 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B2140931 : Blo 2139435 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B3612829 : Blo 2139435 3612829 := bbase (se 3 (by rfl) ⟨677405, by rfl⟩ : syracuseStep 3612829 = 1354811) (by norm_num)
theorem B4817105 : Blo 2139435 4817105 := bstep (se 2 (by rfl) ⟨1806414, by rfl⟩ : syracuseStep 4817105 = 3612829) B3612829
theorem B3211403 : Blo 2139435 3211403 := bstep (se 1 (by rfl) ⟨2408552, by rfl⟩ : syracuseStep 3211403 = 4817105) B4817105
theorem B2140935 : Blo 2139435 2140935 := bstep (se 1 (by rfl) ⟨1605701, by rfl⟩ : syracuseStep 2140935 = 3211403) B3211403
theorem B2408557 : Blo 2139435 2408557 := bbase (se 3 (by rfl) ⟨451604, by rfl⟩ : syracuseStep 2408557 = 903209) (by norm_num)
theorem B3211409 : Blo 2139435 3211409 := bstep (se 2 (by rfl) ⟨1204278, by rfl⟩ : syracuseStep 3211409 = 2408557) B2408557
theorem B2140939 : Blo 2139435 2140939 := bstep (se 1 (by rfl) ⟨1605704, by rfl⟩ : syracuseStep 2140939 = 3211409) B3211409
theorem B7225685 : Blo 2139435 7225685 := bbase (se 10 (by rfl) ⟨10584, by rfl⟩ : syracuseStep 7225685 = 21169) (by norm_num)
theorem B4817123 : Blo 2139435 4817123 := bstep (se 1 (by rfl) ⟨3612842, by rfl⟩ : syracuseStep 4817123 = 7225685) B7225685
theorem B3211415 : Blo 2139435 3211415 := bstep (se 1 (by rfl) ⟨2408561, by rfl⟩ : syracuseStep 3211415 = 4817123) B4817123
theorem B2140943 : Blo 2139435 2140943 := bstep (se 1 (by rfl) ⟨1605707, by rfl⟩ : syracuseStep 2140943 = 3211415) B3211415
theorem B3211421 : Blo 2139435 3211421 := bbase (se 3 (by rfl) ⟨602141, by rfl⟩ : syracuseStep 3211421 = 1204283) (by norm_num)
theorem B2140947 : Blo 2139435 2140947 := bstep (se 1 (by rfl) ⟨1605710, by rfl⟩ : syracuseStep 2140947 = 3211421) B3211421
theorem B4817141 : Blo 2139435 4817141 := bbase (se 5 (by rfl) ⟨225803, by rfl⟩ : syracuseStep 4817141 = 451607) (by norm_num)
theorem B3211427 : Blo 2139435 3211427 := bstep (se 1 (by rfl) ⟨2408570, by rfl⟩ : syracuseStep 3211427 = 4817141) B4817141
theorem B2140951 : Blo 2139435 2140951 := bstep (se 1 (by rfl) ⟨1605713, by rfl⟩ : syracuseStep 2140951 = 3211427) B3211427
theorem B4340333 : Blo 2139435 4340333 := bbase (se 3 (by rfl) ⟨813812, by rfl⟩ : syracuseStep 4340333 = 1627625) (by norm_num)
theorem B2893555 : Blo 2139435 2893555 := bstep (se 1 (by rfl) ⟨2170166, by rfl⟩ : syracuseStep 2893555 = 4340333) B4340333
theorem B3858073 : Blo 2139435 3858073 := bstep (se 2 (by rfl) ⟨1446777, by rfl⟩ : syracuseStep 3858073 = 2893555) B2893555
theorem B20576389 : Blo 2139435 20576389 := bstep (se 4 (by rfl) ⟨1929036, by rfl⟩ : syracuseStep 20576389 = 3858073) B3858073
theorem B27435185 : Blo 2139435 27435185 := bstep (se 2 (by rfl) ⟨10288194, by rfl⟩ : syracuseStep 27435185 = 20576389) B20576389
theorem B18290123 : Blo 2139435 18290123 := bstep (se 1 (by rfl) ⟨13717592, by rfl⟩ : syracuseStep 18290123 = 27435185) B27435185
theorem B12193415 : Blo 2139435 12193415 := bstep (se 1 (by rfl) ⟨9145061, by rfl⟩ : syracuseStep 12193415 = 18290123) B18290123
theorem B8128943 : Blo 2139435 8128943 := bstep (se 1 (by rfl) ⟨6096707, by rfl⟩ : syracuseStep 8128943 = 12193415) B12193415
theorem B5419295 : Blo 2139435 5419295 := bstep (se 1 (by rfl) ⟨4064471, by rfl⟩ : syracuseStep 5419295 = 8128943) B8128943
theorem B3612863 : Blo 2139435 3612863 := bstep (se 1 (by rfl) ⟨2709647, by rfl⟩ : syracuseStep 3612863 = 5419295) B5419295
theorem B2408575 : Blo 2139435 2408575 := bstep (se 1 (by rfl) ⟨1806431, by rfl⟩ : syracuseStep 2408575 = 3612863) B3612863
theorem B3211433 : Blo 2139435 3211433 := bstep (se 2 (by rfl) ⟨1204287, by rfl⟩ : syracuseStep 3211433 = 2408575) B2408575
theorem B2140955 : Blo 2139435 2140955 := bstep (se 1 (by rfl) ⟨1605716, by rfl⟩ : syracuseStep 2140955 = 3211433) B3211433
theorem B4340341 : Blo 2139435 4340341 := bbase (se 5 (by rfl) ⟨203453, by rfl⟩ : syracuseStep 4340341 = 406907) (by norm_num)
theorem B5787121 : Blo 2139435 5787121 := bstep (se 2 (by rfl) ⟨2170170, by rfl⟩ : syracuseStep 5787121 = 4340341) B4340341
theorem B7716161 : Blo 2139435 7716161 := bstep (se 2 (by rfl) ⟨2893560, by rfl⟩ : syracuseStep 7716161 = 5787121) B5787121
theorem B5144107 : Blo 2139435 5144107 := bstep (se 1 (by rfl) ⟨3858080, by rfl⟩ : syracuseStep 5144107 = 7716161) B7716161
theorem B6858809 : Blo 2139435 6858809 := bstep (se 2 (by rfl) ⟨2572053, by rfl⟩ : syracuseStep 6858809 = 5144107) B5144107
theorem B4572539 : Blo 2139435 4572539 := bstep (se 1 (by rfl) ⟨3429404, by rfl⟩ : syracuseStep 4572539 = 6858809) B6858809
theorem B3048359 : Blo 2139435 3048359 := bstep (se 1 (by rfl) ⟨2286269, by rfl⟩ : syracuseStep 3048359 = 4572539) B4572539
theorem B8128957 : Blo 2139435 8128957 := bstep (se 3 (by rfl) ⟨1524179, by rfl⟩ : syracuseStep 8128957 = 3048359) B3048359
theorem B10838609 : Blo 2139435 10838609 := bstep (se 2 (by rfl) ⟨4064478, by rfl⟩ : syracuseStep 10838609 = 8128957) B8128957
theorem B7225739 : Blo 2139435 7225739 := bstep (se 1 (by rfl) ⟨5419304, by rfl⟩ : syracuseStep 7225739 = 10838609) B10838609
theorem B4817159 : Blo 2139435 4817159 := bstep (se 1 (by rfl) ⟨3612869, by rfl⟩ : syracuseStep 4817159 = 7225739) B7225739
theorem B3211439 : Blo 2139435 3211439 := bstep (se 1 (by rfl) ⟨2408579, by rfl⟩ : syracuseStep 3211439 = 4817159) B4817159
theorem B2140959 : Blo 2139435 2140959 := bstep (se 1 (by rfl) ⟨1605719, by rfl⟩ : syracuseStep 2140959 = 3211439) B3211439
theorem B3211445 : Blo 2139435 3211445 := bbase (se 5 (by rfl) ⟨150536, by rfl⟩ : syracuseStep 3211445 = 301073) (by norm_num)
theorem B2140963 : Blo 2139435 2140963 := bstep (se 1 (by rfl) ⟨1605722, by rfl⟩ : syracuseStep 2140963 = 3211445) B3211445
theorem B5419325 : Blo 2139435 5419325 := bbase (se 3 (by rfl) ⟨1016123, by rfl⟩ : syracuseStep 5419325 = 2032247) (by norm_num)
theorem B3612883 : Blo 2139435 3612883 := bstep (se 1 (by rfl) ⟨2709662, by rfl⟩ : syracuseStep 3612883 = 5419325) B5419325
theorem B4817177 : Blo 2139435 4817177 := bstep (se 2 (by rfl) ⟨1806441, by rfl⟩ : syracuseStep 4817177 = 3612883) B3612883
theorem B3211451 : Blo 2139435 3211451 := bstep (se 1 (by rfl) ⟨2408588, by rfl⟩ : syracuseStep 3211451 = 4817177) B4817177
theorem B2140967 : Blo 2139435 2140967 := bstep (se 1 (by rfl) ⟨1605725, by rfl⟩ : syracuseStep 2140967 = 3211451) B3211451
theorem B2408593 : Blo 2139435 2408593 := bbase (se 2 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 2408593 = 1806445) (by norm_num)
theorem B3211457 : Blo 2139435 3211457 := bstep (se 2 (by rfl) ⟨1204296, by rfl⟩ : syracuseStep 3211457 = 2408593) B2408593
theorem B2140971 : Blo 2139435 2140971 := bstep (se 1 (by rfl) ⟨1605728, by rfl⟩ : syracuseStep 2140971 = 3211457) B3211457
theorem B4064509 : Blo 2139435 4064509 := bbase (se 3 (by rfl) ⟨762095, by rfl⟩ : syracuseStep 4064509 = 1524191) (by norm_num)
theorem B5419345 : Blo 2139435 5419345 := bstep (se 2 (by rfl) ⟨2032254, by rfl⟩ : syracuseStep 5419345 = 4064509) B4064509
theorem B7225793 : Blo 2139435 7225793 := bstep (se 2 (by rfl) ⟨2709672, by rfl⟩ : syracuseStep 7225793 = 5419345) B5419345
theorem B4817195 : Blo 2139435 4817195 := bstep (se 1 (by rfl) ⟨3612896, by rfl⟩ : syracuseStep 4817195 = 7225793) B7225793
theorem B3211463 : Blo 2139435 3211463 := bstep (se 1 (by rfl) ⟨2408597, by rfl⟩ : syracuseStep 3211463 = 4817195) B4817195
theorem B2140975 : Blo 2139435 2140975 := bstep (se 1 (by rfl) ⟨1605731, by rfl⟩ : syracuseStep 2140975 = 3211463) B3211463
theorem B3211469 : Blo 2139435 3211469 := bbase (se 3 (by rfl) ⟨602150, by rfl⟩ : syracuseStep 3211469 = 1204301) (by norm_num)
theorem B2140979 : Blo 2139435 2140979 := bstep (se 1 (by rfl) ⟨1605734, by rfl⟩ : syracuseStep 2140979 = 3211469) B3211469
theorem B4817213 : Blo 2139435 4817213 := bbase (se 3 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 4817213 = 1806455) (by norm_num)
theorem B3211475 : Blo 2139435 3211475 := bstep (se 1 (by rfl) ⟨2408606, by rfl⟩ : syracuseStep 3211475 = 4817213) B4817213
theorem B2140983 : Blo 2139435 2140983 := bstep (se 1 (by rfl) ⟨1605737, by rfl⟩ : syracuseStep 2140983 = 3211475) B3211475
theorem B3612917 : Blo 2139435 3612917 := bbase (se 5 (by rfl) ⟨169355, by rfl⟩ : syracuseStep 3612917 = 338711) (by norm_num)
theorem B2408611 : Blo 2139435 2408611 := bstep (se 1 (by rfl) ⟨1806458, by rfl⟩ : syracuseStep 2408611 = 3612917) B3612917
theorem B3211481 : Blo 2139435 3211481 := bstep (se 2 (by rfl) ⟨1204305, by rfl⟩ : syracuseStep 3211481 = 2408611) B2408611
theorem B2140987 : Blo 2139435 2140987 := bstep (se 1 (by rfl) ⟨1605740, by rfl⟩ : syracuseStep 2140987 = 3211481) B3211481
theorem B21142037 : Blo 2139435 21142037 := bbase (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) (by norm_num)
theorem B14094691 : Blo 2139435 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B75171685 : Blo 2139435 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B100228913 : Blo 2139435 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B66819275 : Blo 2139435 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B44546183 : Blo 2139435 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B29697455 : Blo 2139435 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B79193213 : Blo 2139435 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B52795475 : Blo 2139435 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B35196983 : Blo 2139435 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B23464655 : Blo 2139435 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B15643103 : Blo 2139435 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B41714941 : Blo 2139435 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B55619921 : Blo 2139435 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B37079947 : Blo 2139435 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B197759717 : Blo 2139435 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B131839811 : Blo 2139435 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B87893207 : Blo 2139435 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B58595471 : Blo 2139435 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B39063647 : Blo 2139435 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B26042431 : Blo 2139435 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B34723241 : Blo 2139435 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B23148827 : Blo 2139435 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B15432551 : Blo 2139435 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B10288367 : Blo 2139435 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B6858911 : Blo 2139435 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B4572607 : Blo 2139435 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B6096809 : Blo 2139435 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B16258157 : Blo 2139435 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B10838771 : Blo 2139435 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B7225847 : Blo 2139435 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B4817231 : Blo 2139435 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B3211487 : Blo 2139435 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B2140991 : Blo 2139435 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B3211493 : Blo 2139435 3211493 := bbase (se 4 (by rfl) ⟨301077, by rfl⟩ : syracuseStep 3211493 = 602155) (by norm_num)
theorem B2140995 : Blo 2139435 2140995 := bstep (se 1 (by rfl) ⟨1605746, by rfl⟩ : syracuseStep 2140995 = 3211493) B3211493
theorem B3429469 : Blo 2139435 3429469 := bbase (se 3 (by rfl) ⟨643025, by rfl⟩ : syracuseStep 3429469 = 1286051) (by norm_num)
theorem B4572625 : Blo 2139435 4572625 := bstep (se 2 (by rfl) ⟨1714734, by rfl⟩ : syracuseStep 4572625 = 3429469) B3429469
theorem B6096833 : Blo 2139435 6096833 := bstep (se 2 (by rfl) ⟨2286312, by rfl⟩ : syracuseStep 6096833 = 4572625) B4572625
theorem B4064555 : Blo 2139435 4064555 := bstep (se 1 (by rfl) ⟨3048416, by rfl⟩ : syracuseStep 4064555 = 6096833) B6096833
theorem B2709703 : Blo 2139435 2709703 := bstep (se 1 (by rfl) ⟨2032277, by rfl⟩ : syracuseStep 2709703 = 4064555) B4064555
theorem B3612937 : Blo 2139435 3612937 := bstep (se 2 (by rfl) ⟨1354851, by rfl⟩ : syracuseStep 3612937 = 2709703) B2709703
theorem B4817249 : Blo 2139435 4817249 := bstep (se 2 (by rfl) ⟨1806468, by rfl⟩ : syracuseStep 4817249 = 3612937) B3612937
theorem B3211499 : Blo 2139435 3211499 := bstep (se 1 (by rfl) ⟨2408624, by rfl⟩ : syracuseStep 3211499 = 4817249) B4817249
theorem B2140999 : Blo 2139435 2140999 := bstep (se 1 (by rfl) ⟨1605749, by rfl⟩ : syracuseStep 2140999 = 3211499) B3211499
theorem B2408629 : Blo 2139435 2408629 := bbase (se 5 (by rfl) ⟨112904, by rfl⟩ : syracuseStep 2408629 = 225809) (by norm_num)
theorem B3211505 : Blo 2139435 3211505 := bstep (se 2 (by rfl) ⟨1204314, by rfl⟩ : syracuseStep 3211505 = 2408629) B2408629
theorem B2141003 : Blo 2139435 2141003 := bstep (se 1 (by rfl) ⟨1605752, by rfl⟩ : syracuseStep 2141003 = 3211505) B3211505
theorem B2709713 : Blo 2139435 2709713 := bbase (se 2 (by rfl) ⟨1016142, by rfl⟩ : syracuseStep 2709713 = 2032285) (by norm_num)
theorem B7225901 : Blo 2139435 7225901 := bstep (se 3 (by rfl) ⟨1354856, by rfl⟩ : syracuseStep 7225901 = 2709713) B2709713
theorem B4817267 : Blo 2139435 4817267 := bstep (se 1 (by rfl) ⟨3612950, by rfl⟩ : syracuseStep 4817267 = 7225901) B7225901
theorem B3211511 : Blo 2139435 3211511 := bstep (se 1 (by rfl) ⟨2408633, by rfl⟩ : syracuseStep 3211511 = 4817267) B4817267
theorem B2141007 : Blo 2139435 2141007 := bstep (se 1 (by rfl) ⟨1605755, by rfl⟩ : syracuseStep 2141007 = 3211511) B3211511
theorem B3211517 : Blo 2139435 3211517 := bbase (se 3 (by rfl) ⟨602159, by rfl⟩ : syracuseStep 3211517 = 1204319) (by norm_num)
theorem B2141011 : Blo 2139435 2141011 := bstep (se 1 (by rfl) ⟨1605758, by rfl⟩ : syracuseStep 2141011 = 3211517) B3211517
theorem B4817285 : Blo 2139435 4817285 := bbase (se 4 (by rfl) ⟨451620, by rfl⟩ : syracuseStep 4817285 = 903241) (by norm_num)
theorem B3211523 : Blo 2139435 3211523 := bstep (se 1 (by rfl) ⟨2408642, by rfl⟩ : syracuseStep 3211523 = 4817285) B4817285
theorem B2141015 : Blo 2139435 2141015 := bstep (se 1 (by rfl) ⟨1605761, by rfl⟩ : syracuseStep 2141015 = 3211523) B3211523
theorem B3048445 : Blo 2139435 3048445 := bbase (se 3 (by rfl) ⟨571583, by rfl⟩ : syracuseStep 3048445 = 1143167) (by norm_num)
theorem B4064593 : Blo 2139435 4064593 := bstep (se 2 (by rfl) ⟨1524222, by rfl⟩ : syracuseStep 4064593 = 3048445) B3048445
theorem B5419457 : Blo 2139435 5419457 := bstep (se 2 (by rfl) ⟨2032296, by rfl⟩ : syracuseStep 5419457 = 4064593) B4064593
theorem B3612971 : Blo 2139435 3612971 := bstep (se 1 (by rfl) ⟨2709728, by rfl⟩ : syracuseStep 3612971 = 5419457) B5419457
theorem B2408647 : Blo 2139435 2408647 := bstep (se 1 (by rfl) ⟨1806485, by rfl⟩ : syracuseStep 2408647 = 3612971) B3612971
theorem B3211529 : Blo 2139435 3211529 := bstep (se 2 (by rfl) ⟨1204323, by rfl⟩ : syracuseStep 3211529 = 2408647) B2408647
theorem B2141019 : Blo 2139435 2141019 := bstep (se 1 (by rfl) ⟨1605764, by rfl⟩ : syracuseStep 2141019 = 3211529) B3211529
theorem B10838933 : Blo 2139435 10838933 := bbase (se 6 (by rfl) ⟨254037, by rfl⟩ : syracuseStep 10838933 = 508075) (by norm_num)
theorem B7225955 : Blo 2139435 7225955 := bstep (se 1 (by rfl) ⟨5419466, by rfl⟩ : syracuseStep 7225955 = 10838933) B10838933
theorem B4817303 : Blo 2139435 4817303 := bstep (se 1 (by rfl) ⟨3612977, by rfl⟩ : syracuseStep 4817303 = 7225955) B7225955
theorem B3211535 : Blo 2139435 3211535 := bstep (se 1 (by rfl) ⟨2408651, by rfl⟩ : syracuseStep 3211535 = 4817303) B4817303
theorem B2141023 : Blo 2139435 2141023 := bstep (se 1 (by rfl) ⟨1605767, by rfl⟩ : syracuseStep 2141023 = 3211535) B3211535
theorem B3211541 : Blo 2139435 3211541 := bbase (se 6 (by rfl) ⟨75270, by rfl⟩ : syracuseStep 3211541 = 150541) (by norm_num)
theorem B2141027 : Blo 2139435 2141027 := bstep (se 1 (by rfl) ⟨1605770, by rfl⟩ : syracuseStep 2141027 = 3211541) B3211541
theorem B2607233 : Blo 2139435 2607233 := bbase (se 2 (by rfl) ⟨977712, by rfl⟩ : syracuseStep 2607233 = 1955425) (by norm_num)
theorem B27810485 : Blo 2139435 27810485 := bstep (se 5 (by rfl) ⟨1303616, by rfl⟩ : syracuseStep 27810485 = 2607233) B2607233
theorem B18540323 : Blo 2139435 18540323 := bstep (se 1 (by rfl) ⟨13905242, by rfl⟩ : syracuseStep 18540323 = 27810485) B27810485
theorem B12360215 : Blo 2139435 12360215 := bstep (se 1 (by rfl) ⟨9270161, by rfl⟩ : syracuseStep 12360215 = 18540323) B18540323
theorem B8240143 : Blo 2139435 8240143 := bstep (se 1 (by rfl) ⟨6180107, by rfl⟩ : syracuseStep 8240143 = 12360215) B12360215
theorem B10986857 : Blo 2139435 10986857 := bstep (se 2 (by rfl) ⟨4120071, by rfl⟩ : syracuseStep 10986857 = 8240143) B8240143
theorem B7324571 : Blo 2139435 7324571 := bstep (se 1 (by rfl) ⟨5493428, by rfl⟩ : syracuseStep 7324571 = 10986857) B10986857
theorem B4883047 : Blo 2139435 4883047 := bstep (se 1 (by rfl) ⟨3662285, by rfl⟩ : syracuseStep 4883047 = 7324571) B7324571
theorem B26042917 : Blo 2139435 26042917 := bstep (se 4 (by rfl) ⟨2441523, by rfl⟩ : syracuseStep 26042917 = 4883047) B4883047
theorem B34723889 : Blo 2139435 34723889 := bstep (se 2 (by rfl) ⟨13021458, by rfl⟩ : syracuseStep 34723889 = 26042917) B26042917
theorem B23149259 : Blo 2139435 23149259 := bstep (se 1 (by rfl) ⟨17361944, by rfl⟩ : syracuseStep 23149259 = 34723889) B34723889
theorem B15432839 : Blo 2139435 15432839 := bstep (se 1 (by rfl) ⟨11574629, by rfl⟩ : syracuseStep 15432839 = 23149259) B23149259
theorem B10288559 : Blo 2139435 10288559 := bstep (se 1 (by rfl) ⟨7716419, by rfl⟩ : syracuseStep 10288559 = 15432839) B15432839
theorem B27436157 : Blo 2139435 27436157 := bstep (se 3 (by rfl) ⟨5144279, by rfl⟩ : syracuseStep 27436157 = 10288559) B10288559
theorem B18290771 : Blo 2139435 18290771 := bstep (se 1 (by rfl) ⟨13718078, by rfl⟩ : syracuseStep 18290771 = 27436157) B27436157
theorem B12193847 : Blo 2139435 12193847 := bstep (se 1 (by rfl) ⟨9145385, by rfl⟩ : syracuseStep 12193847 = 18290771) B18290771
theorem B8129231 : Blo 2139435 8129231 := bstep (se 1 (by rfl) ⟨6096923, by rfl⟩ : syracuseStep 8129231 = 12193847) B12193847
theorem B5419487 : Blo 2139435 5419487 := bstep (se 1 (by rfl) ⟨4064615, by rfl⟩ : syracuseStep 5419487 = 8129231) B8129231
theorem B3612991 : Blo 2139435 3612991 := bstep (se 1 (by rfl) ⟨2709743, by rfl⟩ : syracuseStep 3612991 = 5419487) B5419487
theorem B4817321 : Blo 2139435 4817321 := bstep (se 2 (by rfl) ⟨1806495, by rfl⟩ : syracuseStep 4817321 = 3612991) B3612991
theorem B3211547 : Blo 2139435 3211547 := bstep (se 1 (by rfl) ⟨2408660, by rfl⟩ : syracuseStep 3211547 = 4817321) B4817321
theorem B2141031 : Blo 2139435 2141031 := bstep (se 1 (by rfl) ⟨1605773, by rfl⟩ : syracuseStep 2141031 = 3211547) B3211547
theorem B2408665 : Blo 2139435 2408665 := bbase (se 2 (by rfl) ⟨903249, by rfl⟩ : syracuseStep 2408665 = 1806499) (by norm_num)
theorem B3211553 : Blo 2139435 3211553 := bstep (se 2 (by rfl) ⟨1204332, by rfl⟩ : syracuseStep 3211553 = 2408665) B2408665
theorem B2141035 : Blo 2139435 2141035 := bstep (se 1 (by rfl) ⟨1605776, by rfl⟩ : syracuseStep 2141035 = 3211553) B3211553
theorem B3429533 : Blo 2139435 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B2286355 : Blo 2139435 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B3048473 : Blo 2139435 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B8129261 : Blo 2139435 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B5419507 : Blo 2139435 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B7226009 : Blo 2139435 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B4817339 : Blo 2139435 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B3211559 : Blo 2139435 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B2141039 : Blo 2139435 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B3211565 : Blo 2139435 3211565 := bbase (se 3 (by rfl) ⟨602168, by rfl⟩ : syracuseStep 3211565 = 1204337) (by norm_num)
theorem B2141043 : Blo 2139435 2141043 := bstep (se 1 (by rfl) ⟨1605782, by rfl⟩ : syracuseStep 2141043 = 3211565) B3211565
theorem B4817357 : Blo 2139435 4817357 := bbase (se 3 (by rfl) ⟨903254, by rfl⟩ : syracuseStep 4817357 = 1806509) (by norm_num)
theorem B3211571 : Blo 2139435 3211571 := bstep (se 1 (by rfl) ⟨2408678, by rfl⟩ : syracuseStep 3211571 = 4817357) B4817357
theorem B2141047 : Blo 2139435 2141047 := bstep (se 1 (by rfl) ⟨1605785, by rfl⟩ : syracuseStep 2141047 = 3211571) B3211571
theorem B2709769 : Blo 2139435 2709769 := bbase (se 2 (by rfl) ⟨1016163, by rfl⟩ : syracuseStep 2709769 = 2032327) (by norm_num)
theorem B3613025 : Blo 2139435 3613025 := bstep (se 2 (by rfl) ⟨1354884, by rfl⟩ : syracuseStep 3613025 = 2709769) B2709769
theorem B2408683 : Blo 2139435 2408683 := bstep (se 1 (by rfl) ⟨1806512, by rfl⟩ : syracuseStep 2408683 = 3613025) B3613025
theorem B3211577 : Blo 2139435 3211577 := bstep (se 2 (by rfl) ⟨1204341, by rfl⟩ : syracuseStep 3211577 = 2408683) B2408683
theorem B2141051 : Blo 2139435 2141051 := bstep (se 1 (by rfl) ⟨1605788, by rfl⟩ : syracuseStep 2141051 = 3211577) B3211577
theorem B5357789 : Blo 2139435 5357789 := bbase (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) (by norm_num)
theorem B3571859 : Blo 2139435 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B2381239 : Blo 2139435 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B3174985 : Blo 2139435 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B4233313 : Blo 2139435 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B5644417 : Blo 2139435 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B7525889 : Blo 2139435 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B5017259 : Blo 2139435 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B3344839 : Blo 2139435 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B71356565 : Blo 2139435 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B190284173 : Blo 2139435 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B126856115 : Blo 2139435 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B84570743 : Blo 2139435 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B56380495 : Blo 2139435 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B75173993 : Blo 2139435 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B50115995 : Blo 2139435 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B33410663 : Blo 2139435 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B22273775 : Blo 2139435 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B14849183 : Blo 2139435 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B39597821 : Blo 2139435 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B26398547 : Blo 2139435 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B17599031 : Blo 2139435 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B11732687 : Blo 2139435 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B7821791 : Blo 2139435 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B5214527 : Blo 2139435 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B3476351 : Blo 2139435 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B2317567 : Blo 2139435 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B3090089 : Blo 2139435 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B8240237 : Blo 2139435 8240237 := bstep (se 3 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 8240237 = 3090089) B3090089
theorem B5493491 : Blo 2139435 5493491 := bstep (se 1 (by rfl) ⟨4120118, by rfl⟩ : syracuseStep 5493491 = 8240237) B8240237
theorem B3662327 : Blo 2139435 3662327 := bstep (se 1 (by rfl) ⟨2746745, by rfl⟩ : syracuseStep 3662327 = 5493491) B5493491
theorem B2441551 : Blo 2139435 2441551 := bstep (se 1 (by rfl) ⟨1831163, by rfl⟩ : syracuseStep 2441551 = 3662327) B3662327
theorem B3255401 : Blo 2139435 3255401 := bstep (se 2 (by rfl) ⟨1220775, by rfl⟩ : syracuseStep 3255401 = 2441551) B2441551
theorem B8681069 : Blo 2139435 8681069 := bstep (se 3 (by rfl) ⟨1627700, by rfl⟩ : syracuseStep 8681069 = 3255401) B3255401
theorem B5787379 : Blo 2139435 5787379 := bstep (se 1 (by rfl) ⟨4340534, by rfl⟩ : syracuseStep 5787379 = 8681069) B8681069
theorem B30866021 : Blo 2139435 30866021 := bstep (se 4 (by rfl) ⟨2893689, by rfl⟩ : syracuseStep 30866021 = 5787379) B5787379
theorem B20577347 : Blo 2139435 20577347 := bstep (se 1 (by rfl) ⟨15433010, by rfl⟩ : syracuseStep 20577347 = 30866021) B30866021
theorem B13718231 : Blo 2139435 13718231 := bstep (se 1 (by rfl) ⟨10288673, by rfl⟩ : syracuseStep 13718231 = 20577347) B20577347
theorem B9145487 : Blo 2139435 9145487 := bstep (se 1 (by rfl) ⟨6859115, by rfl⟩ : syracuseStep 9145487 = 13718231) B13718231
theorem B24387965 : Blo 2139435 24387965 := bstep (se 3 (by rfl) ⟨4572743, by rfl⟩ : syracuseStep 24387965 = 9145487) B9145487
theorem B16258643 : Blo 2139435 16258643 := bstep (se 1 (by rfl) ⟨12193982, by rfl⟩ : syracuseStep 16258643 = 24387965) B24387965
theorem B10839095 : Blo 2139435 10839095 := bstep (se 1 (by rfl) ⟨8129321, by rfl⟩ : syracuseStep 10839095 = 16258643) B16258643
theorem B7226063 : Blo 2139435 7226063 := bstep (se 1 (by rfl) ⟨5419547, by rfl⟩ : syracuseStep 7226063 = 10839095) B10839095
theorem B4817375 : Blo 2139435 4817375 := bstep (se 1 (by rfl) ⟨3613031, by rfl⟩ : syracuseStep 4817375 = 7226063) B7226063
theorem B3211583 : Blo 2139435 3211583 := bstep (se 1 (by rfl) ⟨2408687, by rfl⟩ : syracuseStep 3211583 = 4817375) B4817375
theorem B2141055 : Blo 2139435 2141055 := bstep (se 1 (by rfl) ⟨1605791, by rfl⟩ : syracuseStep 2141055 = 3211583) B3211583
theorem B3211589 : Blo 2139435 3211589 := bbase (se 4 (by rfl) ⟨301086, by rfl⟩ : syracuseStep 3211589 = 602173) (by norm_num)
theorem B2141059 : Blo 2139435 2141059 := bstep (se 1 (by rfl) ⟨1605794, by rfl⟩ : syracuseStep 2141059 = 3211589) B3211589
theorem B3613045 : Blo 2139435 3613045 := bbase (se 5 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 3613045 = 338723) (by norm_num)
theorem B4817393 : Blo 2139435 4817393 := bstep (se 2 (by rfl) ⟨1806522, by rfl⟩ : syracuseStep 4817393 = 3613045) B3613045
theorem B3211595 : Blo 2139435 3211595 := bstep (se 1 (by rfl) ⟨2408696, by rfl⟩ : syracuseStep 3211595 = 4817393) B4817393
theorem B2141063 : Blo 2139435 2141063 := bstep (se 1 (by rfl) ⟨1605797, by rfl⟩ : syracuseStep 2141063 = 3211595) B3211595
theorem B2408701 : Blo 2139435 2408701 := bbase (se 3 (by rfl) ⟨451631, by rfl⟩ : syracuseStep 2408701 = 903263) (by norm_num)
theorem B3211601 : Blo 2139435 3211601 := bstep (se 2 (by rfl) ⟨1204350, by rfl⟩ : syracuseStep 3211601 = 2408701) B2408701
theorem B2141067 : Blo 2139435 2141067 := bstep (se 1 (by rfl) ⟨1605800, by rfl⟩ : syracuseStep 2141067 = 3211601) B3211601
theorem B7226117 : Blo 2139435 7226117 := bbase (se 4 (by rfl) ⟨677448, by rfl⟩ : syracuseStep 7226117 = 1354897) (by norm_num)
theorem B4817411 : Blo 2139435 4817411 := bstep (se 1 (by rfl) ⟨3613058, by rfl⟩ : syracuseStep 4817411 = 7226117) B7226117
theorem B3211607 : Blo 2139435 3211607 := bstep (se 1 (by rfl) ⟨2408705, by rfl⟩ : syracuseStep 3211607 = 4817411) B4817411
theorem B2141071 : Blo 2139435 2141071 := bstep (se 1 (by rfl) ⟨1605803, by rfl⟩ : syracuseStep 2141071 = 3211607) B3211607
theorem B3211613 : Blo 2139435 3211613 := bbase (se 3 (by rfl) ⟨602177, by rfl⟩ : syracuseStep 3211613 = 1204355) (by norm_num)
theorem B2141075 : Blo 2139435 2141075 := bstep (se 1 (by rfl) ⟨1605806, by rfl⟩ : syracuseStep 2141075 = 3211613) B3211613
theorem B4817429 : Blo 2139435 4817429 := bbase (se 6 (by rfl) ⟨112908, by rfl⟩ : syracuseStep 4817429 = 225817) (by norm_num)
theorem B3211619 : Blo 2139435 3211619 := bstep (se 1 (by rfl) ⟨2408714, by rfl⟩ : syracuseStep 3211619 = 4817429) B4817429
theorem B2141079 : Blo 2139435 2141079 := bstep (se 1 (by rfl) ⟨1605809, by rfl⟩ : syracuseStep 2141079 = 3211619) B3211619
theorem B8129429 : Blo 2139435 8129429 := bbase (se 6 (by rfl) ⟨190533, by rfl⟩ : syracuseStep 8129429 = 381067) (by norm_num)
theorem B5419619 : Blo 2139435 5419619 := bstep (se 1 (by rfl) ⟨4064714, by rfl⟩ : syracuseStep 5419619 = 8129429) B8129429
theorem B3613079 : Blo 2139435 3613079 := bstep (se 1 (by rfl) ⟨2709809, by rfl⟩ : syracuseStep 3613079 = 5419619) B5419619
theorem B2408719 : Blo 2139435 2408719 := bstep (se 1 (by rfl) ⟨1806539, by rfl⟩ : syracuseStep 2408719 = 3613079) B3613079
theorem B3211625 : Blo 2139435 3211625 := bstep (se 2 (by rfl) ⟨1204359, by rfl⟩ : syracuseStep 3211625 = 2408719) B2408719
theorem B2141083 : Blo 2139435 2141083 := bstep (se 1 (by rfl) ⟨1605812, by rfl⟩ : syracuseStep 2141083 = 3211625) B3211625
theorem B12194165 : Blo 2139435 12194165 := bbase (se 5 (by rfl) ⟨571601, by rfl⟩ : syracuseStep 12194165 = 1143203) (by norm_num)
theorem B8129443 : Blo 2139435 8129443 := bstep (se 1 (by rfl) ⟨6097082, by rfl⟩ : syracuseStep 8129443 = 12194165) B12194165
theorem B10839257 : Blo 2139435 10839257 := bstep (se 2 (by rfl) ⟨4064721, by rfl⟩ : syracuseStep 10839257 = 8129443) B8129443
theorem B7226171 : Blo 2139435 7226171 := bstep (se 1 (by rfl) ⟨5419628, by rfl⟩ : syracuseStep 7226171 = 10839257) B10839257
theorem B4817447 : Blo 2139435 4817447 := bstep (se 1 (by rfl) ⟨3613085, by rfl⟩ : syracuseStep 4817447 = 7226171) B7226171
theorem B3211631 : Blo 2139435 3211631 := bstep (se 1 (by rfl) ⟨2408723, by rfl⟩ : syracuseStep 3211631 = 4817447) B4817447
theorem B2141087 : Blo 2139435 2141087 := bstep (se 1 (by rfl) ⟨1605815, by rfl⟩ : syracuseStep 2141087 = 3211631) B3211631
theorem B3211637 : Blo 2139435 3211637 := bbase (se 5 (by rfl) ⟨150545, by rfl⟩ : syracuseStep 3211637 = 301091) (by norm_num)
theorem B2141091 : Blo 2139435 2141091 := bstep (se 1 (by rfl) ⟨1605818, by rfl⟩ : syracuseStep 2141091 = 3211637) B3211637
theorem B2170309 : Blo 2139435 2170309 := bbase (se 4 (by rfl) ⟨203466, by rfl⟩ : syracuseStep 2170309 = 406933) (by norm_num)
theorem B2893745 : Blo 2139435 2893745 := bstep (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) B2170309
theorem B7716653 : Blo 2139435 7716653 := bstep (se 3 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 7716653 = 2893745) B2893745
theorem B5144435 : Blo 2139435 5144435 := bstep (se 1 (by rfl) ⟨3858326, by rfl⟩ : syracuseStep 5144435 = 7716653) B7716653
theorem B3429623 : Blo 2139435 3429623 := bstep (se 1 (by rfl) ⟨2572217, by rfl⟩ : syracuseStep 3429623 = 5144435) B5144435
theorem B2286415 : Blo 2139435 2286415 := bstep (se 1 (by rfl) ⟨1714811, by rfl⟩ : syracuseStep 2286415 = 3429623) B3429623
theorem B3048553 : Blo 2139435 3048553 := bstep (se 2 (by rfl) ⟨1143207, by rfl⟩ : syracuseStep 3048553 = 2286415) B2286415
theorem B4064737 : Blo 2139435 4064737 := bstep (se 2 (by rfl) ⟨1524276, by rfl⟩ : syracuseStep 4064737 = 3048553) B3048553
theorem B5419649 : Blo 2139435 5419649 := bstep (se 2 (by rfl) ⟨2032368, by rfl⟩ : syracuseStep 5419649 = 4064737) B4064737
theorem B3613099 : Blo 2139435 3613099 := bstep (se 1 (by rfl) ⟨2709824, by rfl⟩ : syracuseStep 3613099 = 5419649) B5419649
theorem B4817465 : Blo 2139435 4817465 := bstep (se 2 (by rfl) ⟨1806549, by rfl⟩ : syracuseStep 4817465 = 3613099) B3613099
theorem B3211643 : Blo 2139435 3211643 := bstep (se 1 (by rfl) ⟨2408732, by rfl⟩ : syracuseStep 3211643 = 4817465) B4817465
theorem B2141095 : Blo 2139435 2141095 := bstep (se 1 (by rfl) ⟨1605821, by rfl⟩ : syracuseStep 2141095 = 3211643) B3211643
theorem B2408737 : Blo 2139435 2408737 := bbase (se 2 (by rfl) ⟨903276, by rfl⟩ : syracuseStep 2408737 = 1806553) (by norm_num)
theorem B3211649 : Blo 2139435 3211649 := bstep (se 2 (by rfl) ⟨1204368, by rfl⟩ : syracuseStep 3211649 = 2408737) B2408737
theorem B2141099 : Blo 2139435 2141099 := bstep (se 1 (by rfl) ⟨1605824, by rfl⟩ : syracuseStep 2141099 = 3211649) B3211649
theorem B5419669 : Blo 2139435 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B7226225 : Blo 2139435 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B4817483 : Blo 2139435 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B3211655 : Blo 2139435 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B2141103 : Blo 2139435 2141103 := bstep (se 1 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 2141103 = 3211655) B3211655
theorem B3211661 : Blo 2139435 3211661 := bbase (se 3 (by rfl) ⟨602186, by rfl⟩ : syracuseStep 3211661 = 1204373) (by norm_num)
theorem B2141107 : Blo 2139435 2141107 := bstep (se 1 (by rfl) ⟨1605830, by rfl⟩ : syracuseStep 2141107 = 3211661) B3211661
theorem B4817501 : Blo 2139435 4817501 := bbase (se 3 (by rfl) ⟨903281, by rfl⟩ : syracuseStep 4817501 = 1806563) (by norm_num)
theorem B3211667 : Blo 2139435 3211667 := bstep (se 1 (by rfl) ⟨2408750, by rfl⟩ : syracuseStep 3211667 = 4817501) B4817501
theorem B2141111 : Blo 2139435 2141111 := bstep (se 1 (by rfl) ⟨1605833, by rfl⟩ : syracuseStep 2141111 = 3211667) B3211667
theorem B3613133 : Blo 2139435 3613133 := bbase (se 3 (by rfl) ⟨677462, by rfl⟩ : syracuseStep 3613133 = 1354925) (by norm_num)
theorem B2408755 : Blo 2139435 2408755 := bstep (se 1 (by rfl) ⟨1806566, by rfl⟩ : syracuseStep 2408755 = 3613133) B3613133
theorem B3211673 : Blo 2139435 3211673 := bstep (se 2 (by rfl) ⟨1204377, by rfl⟩ : syracuseStep 3211673 = 2408755) B2408755
theorem B2141115 : Blo 2139435 2141115 := bstep (se 1 (by rfl) ⟨1605836, by rfl⟩ : syracuseStep 2141115 = 3211673) B3211673
theorem B10288981 : Blo 2139435 10288981 := bbase (se 9 (by rfl) ⟨30143, by rfl⟩ : syracuseStep 10288981 = 60287) (by norm_num)
theorem B13718641 : Blo 2139435 13718641 := bstep (se 2 (by rfl) ⟨5144490, by rfl⟩ : syracuseStep 13718641 = 10288981) B10288981
theorem B18291521 : Blo 2139435 18291521 := bstep (se 2 (by rfl) ⟨6859320, by rfl⟩ : syracuseStep 18291521 = 13718641) B13718641
theorem B12194347 : Blo 2139435 12194347 := bstep (se 1 (by rfl) ⟨9145760, by rfl⟩ : syracuseStep 12194347 = 18291521) B18291521
theorem B16259129 : Blo 2139435 16259129 := bstep (se 2 (by rfl) ⟨6097173, by rfl⟩ : syracuseStep 16259129 = 12194347) B12194347
theorem B10839419 : Blo 2139435 10839419 := bstep (se 1 (by rfl) ⟨8129564, by rfl⟩ : syracuseStep 10839419 = 16259129) B16259129
theorem B7226279 : Blo 2139435 7226279 := bstep (se 1 (by rfl) ⟨5419709, by rfl⟩ : syracuseStep 7226279 = 10839419) B10839419
theorem B4817519 : Blo 2139435 4817519 := bstep (se 1 (by rfl) ⟨3613139, by rfl⟩ : syracuseStep 4817519 = 7226279) B7226279
theorem B3211679 : Blo 2139435 3211679 := bstep (se 1 (by rfl) ⟨2408759, by rfl⟩ : syracuseStep 3211679 = 4817519) B4817519
theorem B2141119 : Blo 2139435 2141119 := bstep (se 1 (by rfl) ⟨1605839, by rfl⟩ : syracuseStep 2141119 = 3211679) B3211679
theorem B3211685 : Blo 2139435 3211685 := bbase (se 4 (by rfl) ⟨301095, by rfl⟩ : syracuseStep 3211685 = 602191) (by norm_num)
theorem B2141123 : Blo 2139435 2141123 := bstep (se 1 (by rfl) ⟨1605842, by rfl⟩ : syracuseStep 2141123 = 3211685) B3211685
theorem B2709865 : Blo 2139435 2709865 := bbase (se 2 (by rfl) ⟨1016199, by rfl⟩ : syracuseStep 2709865 = 2032399) (by norm_num)
theorem B3613153 : Blo 2139435 3613153 := bstep (se 2 (by rfl) ⟨1354932, by rfl⟩ : syracuseStep 3613153 = 2709865) B2709865
theorem B4817537 : Blo 2139435 4817537 := bstep (se 2 (by rfl) ⟨1806576, by rfl⟩ : syracuseStep 4817537 = 3613153) B3613153
theorem B3211691 : Blo 2139435 3211691 := bstep (se 1 (by rfl) ⟨2408768, by rfl⟩ : syracuseStep 3211691 = 4817537) B4817537
theorem B2141127 : Blo 2139435 2141127 := bstep (se 1 (by rfl) ⟨1605845, by rfl⟩ : syracuseStep 2141127 = 3211691) B3211691
theorem B2408773 : Blo 2139435 2408773 := bbase (se 4 (by rfl) ⟨225822, by rfl⟩ : syracuseStep 2408773 = 451645) (by norm_num)
theorem B3211697 : Blo 2139435 3211697 := bstep (se 2 (by rfl) ⟨1204386, by rfl⟩ : syracuseStep 3211697 = 2408773) B2408773
theorem B2141131 : Blo 2139435 2141131 := bstep (se 1 (by rfl) ⟨1605848, by rfl⟩ : syracuseStep 2141131 = 3211697) B3211697
theorem B4064813 : Blo 2139435 4064813 := bbase (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) (by norm_num)
theorem B2709875 : Blo 2139435 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B7226333 : Blo 2139435 7226333 := bstep (se 3 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 7226333 = 2709875) B2709875
theorem B4817555 : Blo 2139435 4817555 := bstep (se 1 (by rfl) ⟨3613166, by rfl⟩ : syracuseStep 4817555 = 7226333) B7226333
theorem B3211703 : Blo 2139435 3211703 := bstep (se 1 (by rfl) ⟨2408777, by rfl⟩ : syracuseStep 3211703 = 4817555) B4817555
theorem B2141135 : Blo 2139435 2141135 := bstep (se 1 (by rfl) ⟨1605851, by rfl⟩ : syracuseStep 2141135 = 3211703) B3211703
theorem B3211709 : Blo 2139435 3211709 := bbase (se 3 (by rfl) ⟨602195, by rfl⟩ : syracuseStep 3211709 = 1204391) (by norm_num)
theorem B2141139 : Blo 2139435 2141139 := bstep (se 1 (by rfl) ⟨1605854, by rfl⟩ : syracuseStep 2141139 = 3211709) B3211709
theorem B4817573 : Blo 2139435 4817573 := bbase (se 4 (by rfl) ⟨451647, by rfl⟩ : syracuseStep 4817573 = 903295) (by norm_num)
theorem B3211715 : Blo 2139435 3211715 := bstep (se 1 (by rfl) ⟨2408786, by rfl⟩ : syracuseStep 3211715 = 4817573) B4817573
theorem B2141143 : Blo 2139435 2141143 := bstep (se 1 (by rfl) ⟨1605857, by rfl⟩ : syracuseStep 2141143 = 3211715) B3211715
theorem B5419781 : Blo 2139435 5419781 := bbase (se 4 (by rfl) ⟨508104, by rfl⟩ : syracuseStep 5419781 = 1016209) (by norm_num)
theorem B3613187 : Blo 2139435 3613187 := bstep (se 1 (by rfl) ⟨2709890, by rfl⟩ : syracuseStep 3613187 = 5419781) B5419781
theorem B2408791 : Blo 2139435 2408791 := bstep (se 1 (by rfl) ⟨1806593, by rfl⟩ : syracuseStep 2408791 = 3613187) B3613187
theorem B3211721 : Blo 2139435 3211721 := bstep (se 2 (by rfl) ⟨1204395, by rfl⟩ : syracuseStep 3211721 = 2408791) B2408791
theorem B2141147 : Blo 2139435 2141147 := bstep (se 1 (by rfl) ⟨1605860, by rfl⟩ : syracuseStep 2141147 = 3211721) B3211721
theorem B4572949 : Blo 2139435 4572949 := bbase (se 6 (by rfl) ⟨107178, by rfl⟩ : syracuseStep 4572949 = 214357) (by norm_num)
theorem B6097265 : Blo 2139435 6097265 := bstep (se 2 (by rfl) ⟨2286474, by rfl⟩ : syracuseStep 6097265 = 4572949) B4572949
theorem B4064843 : Blo 2139435 4064843 := bstep (se 1 (by rfl) ⟨3048632, by rfl⟩ : syracuseStep 4064843 = 6097265) B6097265
theorem B10839581 : Blo 2139435 10839581 := bstep (se 3 (by rfl) ⟨2032421, by rfl⟩ : syracuseStep 10839581 = 4064843) B4064843
theorem B7226387 : Blo 2139435 7226387 := bstep (se 1 (by rfl) ⟨5419790, by rfl⟩ : syracuseStep 7226387 = 10839581) B10839581
theorem B4817591 : Blo 2139435 4817591 := bstep (se 1 (by rfl) ⟨3613193, by rfl⟩ : syracuseStep 4817591 = 7226387) B7226387
theorem B3211727 : Blo 2139435 3211727 := bstep (se 1 (by rfl) ⟨2408795, by rfl⟩ : syracuseStep 3211727 = 4817591) B4817591
theorem B2141151 : Blo 2139435 2141151 := bstep (se 1 (by rfl) ⟨1605863, by rfl⟩ : syracuseStep 2141151 = 3211727) B3211727
theorem B3211733 : Blo 2139435 3211733 := bbase (se 7 (by rfl) ⟨37637, by rfl⟩ : syracuseStep 3211733 = 75275) (by norm_num)
theorem B2141155 : Blo 2139435 2141155 := bstep (se 1 (by rfl) ⟨1605866, by rfl⟩ : syracuseStep 2141155 = 3211733) B3211733
theorem B8129717 : Blo 2139435 8129717 := bbase (se 5 (by rfl) ⟨381080, by rfl⟩ : syracuseStep 8129717 = 762161) (by norm_num)
theorem B5419811 : Blo 2139435 5419811 := bstep (se 1 (by rfl) ⟨4064858, by rfl⟩ : syracuseStep 5419811 = 8129717) B8129717
theorem B3613207 : Blo 2139435 3613207 := bstep (se 1 (by rfl) ⟨2709905, by rfl⟩ : syracuseStep 3613207 = 5419811) B5419811
theorem B4817609 : Blo 2139435 4817609 := bstep (se 2 (by rfl) ⟨1806603, by rfl⟩ : syracuseStep 4817609 = 3613207) B3613207
theorem B3211739 : Blo 2139435 3211739 := bstep (se 1 (by rfl) ⟨2408804, by rfl⟩ : syracuseStep 3211739 = 4817609) B4817609
theorem B2141159 : Blo 2139435 2141159 := bstep (se 1 (by rfl) ⟨1605869, by rfl⟩ : syracuseStep 2141159 = 3211739) B3211739
theorem B2408809 : Blo 2139435 2408809 := bbase (se 2 (by rfl) ⟨903303, by rfl⟩ : syracuseStep 2408809 = 1806607) (by norm_num)
theorem B3211745 : Blo 2139435 3211745 := bstep (se 2 (by rfl) ⟨1204404, by rfl⟩ : syracuseStep 3211745 = 2408809) B2408809
theorem B2141163 : Blo 2139435 2141163 := bstep (se 1 (by rfl) ⟨1605872, by rfl⟩ : syracuseStep 2141163 = 3211745) B3211745
theorem B8681525 : Blo 2139435 8681525 := bbase (se 5 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 8681525 = 813893) (by norm_num)
theorem B5787683 : Blo 2139435 5787683 := bstep (se 1 (by rfl) ⟨4340762, by rfl⟩ : syracuseStep 5787683 = 8681525) B8681525
theorem B3858455 : Blo 2139435 3858455 := bstep (se 1 (by rfl) ⟨2893841, by rfl⟩ : syracuseStep 3858455 = 5787683) B5787683
theorem B10289213 : Blo 2139435 10289213 := bstep (se 3 (by rfl) ⟨1929227, by rfl⟩ : syracuseStep 10289213 = 3858455) B3858455
theorem B6859475 : Blo 2139435 6859475 := bstep (se 1 (by rfl) ⟨5144606, by rfl⟩ : syracuseStep 6859475 = 10289213) B10289213
theorem B4572983 : Blo 2139435 4572983 := bstep (se 1 (by rfl) ⟨3429737, by rfl⟩ : syracuseStep 4572983 = 6859475) B6859475
theorem B12194621 : Blo 2139435 12194621 := bstep (se 3 (by rfl) ⟨2286491, by rfl⟩ : syracuseStep 12194621 = 4572983) B4572983
theorem B8129747 : Blo 2139435 8129747 := bstep (se 1 (by rfl) ⟨6097310, by rfl⟩ : syracuseStep 8129747 = 12194621) B12194621
theorem B5419831 : Blo 2139435 5419831 := bstep (se 1 (by rfl) ⟨4064873, by rfl⟩ : syracuseStep 5419831 = 8129747) B8129747
theorem B7226441 : Blo 2139435 7226441 := bstep (se 2 (by rfl) ⟨2709915, by rfl⟩ : syracuseStep 7226441 = 5419831) B5419831
theorem B4817627 : Blo 2139435 4817627 := bstep (se 1 (by rfl) ⟨3613220, by rfl⟩ : syracuseStep 4817627 = 7226441) B7226441
theorem B3211751 : Blo 2139435 3211751 := bstep (se 1 (by rfl) ⟨2408813, by rfl⟩ : syracuseStep 3211751 = 4817627) B4817627
theorem B2141167 : Blo 2139435 2141167 := bstep (se 1 (by rfl) ⟨1605875, by rfl⟩ : syracuseStep 2141167 = 3211751) B3211751
theorem B3211757 : Blo 2139435 3211757 := bbase (se 3 (by rfl) ⟨602204, by rfl⟩ : syracuseStep 3211757 = 1204409) (by norm_num)
theorem B2141171 : Blo 2139435 2141171 := bstep (se 1 (by rfl) ⟨1605878, by rfl⟩ : syracuseStep 2141171 = 3211757) B3211757
theorem B4817645 : Blo 2139435 4817645 := bbase (se 3 (by rfl) ⟨903308, by rfl⟩ : syracuseStep 4817645 = 1806617) (by norm_num)
theorem B3211763 : Blo 2139435 3211763 := bstep (se 1 (by rfl) ⟨2408822, by rfl⟩ : syracuseStep 3211763 = 4817645) B4817645
theorem B2141175 : Blo 2139435 2141175 := bstep (se 1 (by rfl) ⟨1605881, by rfl⟩ : syracuseStep 2141175 = 3211763) B3211763
theorem B2286505 : Blo 2139435 2286505 := bbase (se 2 (by rfl) ⟨857439, by rfl⟩ : syracuseStep 2286505 = 1714879) (by norm_num)
theorem B3048673 : Blo 2139435 3048673 := bstep (se 2 (by rfl) ⟨1143252, by rfl⟩ : syracuseStep 3048673 = 2286505) B2286505
theorem B4064897 : Blo 2139435 4064897 := bstep (se 2 (by rfl) ⟨1524336, by rfl⟩ : syracuseStep 4064897 = 3048673) B3048673
theorem B2709931 : Blo 2139435 2709931 := bstep (se 1 (by rfl) ⟨2032448, by rfl⟩ : syracuseStep 2709931 = 4064897) B4064897
theorem B3613241 : Blo 2139435 3613241 := bstep (se 2 (by rfl) ⟨1354965, by rfl⟩ : syracuseStep 3613241 = 2709931) B2709931
theorem B2408827 : Blo 2139435 2408827 := bstep (se 1 (by rfl) ⟨1806620, by rfl⟩ : syracuseStep 2408827 = 3613241) B3613241
theorem B3211769 : Blo 2139435 3211769 := bstep (se 2 (by rfl) ⟨1204413, by rfl⟩ : syracuseStep 3211769 = 2408827) B2408827
theorem B2141179 : Blo 2139435 2141179 := bstep (se 1 (by rfl) ⟨1605884, by rfl⟩ : syracuseStep 2141179 = 3211769) B3211769
theorem B2746909 : Blo 2139435 2746909 := bbase (se 3 (by rfl) ⟨515045, by rfl⟩ : syracuseStep 2746909 = 1030091) (by norm_num)
theorem B3662545 : Blo 2139435 3662545 := bstep (se 2 (by rfl) ⟨1373454, by rfl⟩ : syracuseStep 3662545 = 2746909) B2746909
theorem B4883393 : Blo 2139435 4883393 := bstep (se 2 (by rfl) ⟨1831272, by rfl⟩ : syracuseStep 4883393 = 3662545) B3662545
theorem B13022381 : Blo 2139435 13022381 := bstep (se 3 (by rfl) ⟨2441696, by rfl⟩ : syracuseStep 13022381 = 4883393) B4883393
theorem B8681587 : Blo 2139435 8681587 := bstep (se 1 (by rfl) ⟨6511190, by rfl⟩ : syracuseStep 8681587 = 13022381) B13022381
theorem B46301797 : Blo 2139435 46301797 := bstep (se 4 (by rfl) ⟨4340793, by rfl⟩ : syracuseStep 46301797 = 8681587) B8681587
theorem B61735729 : Blo 2139435 61735729 := bstep (se 2 (by rfl) ⟨23150898, by rfl⟩ : syracuseStep 61735729 = 46301797) B46301797
theorem B82314305 : Blo 2139435 82314305 := bstep (se 2 (by rfl) ⟨30867864, by rfl⟩ : syracuseStep 82314305 = 61735729) B61735729
theorem B54876203 : Blo 2139435 54876203 := bstep (se 1 (by rfl) ⟨41157152, by rfl⟩ : syracuseStep 54876203 = 82314305) B82314305
theorem B36584135 : Blo 2139435 36584135 := bstep (se 1 (by rfl) ⟨27438101, by rfl⟩ : syracuseStep 36584135 = 54876203) B54876203
theorem B24389423 : Blo 2139435 24389423 := bstep (se 1 (by rfl) ⟨18292067, by rfl⟩ : syracuseStep 24389423 = 36584135) B36584135
theorem B16259615 : Blo 2139435 16259615 := bstep (se 1 (by rfl) ⟨12194711, by rfl⟩ : syracuseStep 16259615 = 24389423) B24389423
theorem B10839743 : Blo 2139435 10839743 := bstep (se 1 (by rfl) ⟨8129807, by rfl⟩ : syracuseStep 10839743 = 16259615) B16259615
theorem B7226495 : Blo 2139435 7226495 := bstep (se 1 (by rfl) ⟨5419871, by rfl⟩ : syracuseStep 7226495 = 10839743) B10839743
theorem B4817663 : Blo 2139435 4817663 := bstep (se 1 (by rfl) ⟨3613247, by rfl⟩ : syracuseStep 4817663 = 7226495) B7226495
theorem B3211775 : Blo 2139435 3211775 := bstep (se 1 (by rfl) ⟨2408831, by rfl⟩ : syracuseStep 3211775 = 4817663) B4817663
theorem B2141183 : Blo 2139435 2141183 := bstep (se 1 (by rfl) ⟨1605887, by rfl⟩ : syracuseStep 2141183 = 3211775) B3211775
theorem B3211781 : Blo 2139435 3211781 := bbase (se 4 (by rfl) ⟨301104, by rfl⟩ : syracuseStep 3211781 = 602209) (by norm_num)
theorem B2141187 : Blo 2139435 2141187 := bstep (se 1 (by rfl) ⟨1605890, by rfl⟩ : syracuseStep 2141187 = 3211781) B3211781
theorem B3613261 : Blo 2139435 3613261 := bbase (se 3 (by rfl) ⟨677486, by rfl⟩ : syracuseStep 3613261 = 1354973) (by norm_num)
theorem B4817681 : Blo 2139435 4817681 := bstep (se 2 (by rfl) ⟨1806630, by rfl⟩ : syracuseStep 4817681 = 3613261) B3613261
theorem B3211787 : Blo 2139435 3211787 := bstep (se 1 (by rfl) ⟨2408840, by rfl⟩ : syracuseStep 3211787 = 4817681) B4817681
theorem B2141191 : Blo 2139435 2141191 := bstep (se 1 (by rfl) ⟨1605893, by rfl⟩ : syracuseStep 2141191 = 3211787) B3211787
theorem B2408845 : Blo 2139435 2408845 := bbase (se 3 (by rfl) ⟨451658, by rfl⟩ : syracuseStep 2408845 = 903317) (by norm_num)
theorem B3211793 : Blo 2139435 3211793 := bstep (se 2 (by rfl) ⟨1204422, by rfl⟩ : syracuseStep 3211793 = 2408845) B2408845
theorem B2141195 : Blo 2139435 2141195 := bstep (se 1 (by rfl) ⟨1605896, by rfl⟩ : syracuseStep 2141195 = 3211793) B3211793
theorem B7226549 : Blo 2139435 7226549 := bbase (se 5 (by rfl) ⟨338744, by rfl⟩ : syracuseStep 7226549 = 677489) (by norm_num)
theorem B4817699 : Blo 2139435 4817699 := bstep (se 1 (by rfl) ⟨3613274, by rfl⟩ : syracuseStep 4817699 = 7226549) B7226549
theorem B3211799 : Blo 2139435 3211799 := bstep (se 1 (by rfl) ⟨2408849, by rfl⟩ : syracuseStep 3211799 = 4817699) B4817699
theorem B2141199 : Blo 2139435 2141199 := bstep (se 1 (by rfl) ⟨1605899, by rfl⟩ : syracuseStep 2141199 = 3211799) B3211799
theorem B3211805 : Blo 2139435 3211805 := bbase (se 3 (by rfl) ⟨602213, by rfl⟩ : syracuseStep 3211805 = 1204427) (by norm_num)
theorem B2141203 : Blo 2139435 2141203 := bstep (se 1 (by rfl) ⟨1605902, by rfl⟩ : syracuseStep 2141203 = 3211805) B3211805
theorem B4817717 : Blo 2139435 4817717 := bbase (se 5 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 4817717 = 451661) (by norm_num)
theorem B3211811 : Blo 2139435 3211811 := bstep (se 1 (by rfl) ⟨2408858, by rfl⟩ : syracuseStep 3211811 = 4817717) B4817717
theorem B2141207 : Blo 2139435 2141207 := bstep (se 1 (by rfl) ⟨1605905, by rfl⟩ : syracuseStep 2141207 = 3211811) B3211811
theorem B2893901 : Blo 2139435 2893901 := bbase (se 3 (by rfl) ⟨542606, by rfl⟩ : syracuseStep 2893901 = 1085213) (by norm_num)
theorem B7717069 : Blo 2139435 7717069 := bstep (se 3 (by rfl) ⟨1446950, by rfl⟩ : syracuseStep 7717069 = 2893901) B2893901
theorem B10289425 : Blo 2139435 10289425 := bstep (se 2 (by rfl) ⟨3858534, by rfl⟩ : syracuseStep 10289425 = 7717069) B7717069
theorem B13719233 : Blo 2139435 13719233 := bstep (se 2 (by rfl) ⟨5144712, by rfl⟩ : syracuseStep 13719233 = 10289425) B10289425
theorem B9146155 : Blo 2139435 9146155 := bstep (se 1 (by rfl) ⟨6859616, by rfl⟩ : syracuseStep 9146155 = 13719233) B13719233
theorem B12194873 : Blo 2139435 12194873 := bstep (se 2 (by rfl) ⟨4573077, by rfl⟩ : syracuseStep 12194873 = 9146155) B9146155
theorem B8129915 : Blo 2139435 8129915 := bstep (se 1 (by rfl) ⟨6097436, by rfl⟩ : syracuseStep 8129915 = 12194873) B12194873
theorem B5419943 : Blo 2139435 5419943 := bstep (se 1 (by rfl) ⟨4064957, by rfl⟩ : syracuseStep 5419943 = 8129915) B8129915
theorem B3613295 : Blo 2139435 3613295 := bstep (se 1 (by rfl) ⟨2709971, by rfl⟩ : syracuseStep 3613295 = 5419943) B5419943
theorem B2408863 : Blo 2139435 2408863 := bstep (se 1 (by rfl) ⟨1806647, by rfl⟩ : syracuseStep 2408863 = 3613295) B3613295
theorem B3211817 : Blo 2139435 3211817 := bstep (se 2 (by rfl) ⟨1204431, by rfl⟩ : syracuseStep 3211817 = 2408863) B2408863
theorem B2141211 : Blo 2139435 2141211 := bstep (se 1 (by rfl) ⟨1605908, by rfl⟩ : syracuseStep 2141211 = 3211817) B3211817
theorem B15434165 : Blo 2139435 15434165 := bbase (se 5 (by rfl) ⟨723476, by rfl⟩ : syracuseStep 15434165 = 1446953) (by norm_num)
theorem B10289443 : Blo 2139435 10289443 := bstep (se 1 (by rfl) ⟨7717082, by rfl⟩ : syracuseStep 10289443 = 15434165) B15434165
theorem B13719257 : Blo 2139435 13719257 := bstep (se 2 (by rfl) ⟨5144721, by rfl⟩ : syracuseStep 13719257 = 10289443) B10289443
theorem B9146171 : Blo 2139435 9146171 := bstep (se 1 (by rfl) ⟨6859628, by rfl⟩ : syracuseStep 9146171 = 13719257) B13719257
theorem B6097447 : Blo 2139435 6097447 := bstep (se 1 (by rfl) ⟨4573085, by rfl⟩ : syracuseStep 6097447 = 9146171) B9146171
theorem B8129929 : Blo 2139435 8129929 := bstep (se 2 (by rfl) ⟨3048723, by rfl⟩ : syracuseStep 8129929 = 6097447) B6097447
theorem B10839905 : Blo 2139435 10839905 := bstep (se 2 (by rfl) ⟨4064964, by rfl⟩ : syracuseStep 10839905 = 8129929) B8129929
theorem B7226603 : Blo 2139435 7226603 := bstep (se 1 (by rfl) ⟨5419952, by rfl⟩ : syracuseStep 7226603 = 10839905) B10839905
theorem B4817735 : Blo 2139435 4817735 := bstep (se 1 (by rfl) ⟨3613301, by rfl⟩ : syracuseStep 4817735 = 7226603) B7226603
theorem B3211823 : Blo 2139435 3211823 := bstep (se 1 (by rfl) ⟨2408867, by rfl⟩ : syracuseStep 3211823 = 4817735) B4817735
theorem B2141215 : Blo 2139435 2141215 := bstep (se 1 (by rfl) ⟨1605911, by rfl⟩ : syracuseStep 2141215 = 3211823) B3211823
theorem B3211829 : Blo 2139435 3211829 := bbase (se 5 (by rfl) ⟨150554, by rfl⟩ : syracuseStep 3211829 = 301109) (by norm_num)
theorem B2141219 : Blo 2139435 2141219 := bstep (se 1 (by rfl) ⟨1605914, by rfl⟩ : syracuseStep 2141219 = 3211829) B3211829
theorem B5419973 : Blo 2139435 5419973 := bbase (se 4 (by rfl) ⟨508122, by rfl⟩ : syracuseStep 5419973 = 1016245) (by norm_num)
theorem B3613315 : Blo 2139435 3613315 := bstep (se 1 (by rfl) ⟨2709986, by rfl⟩ : syracuseStep 3613315 = 5419973) B5419973
theorem B4817753 : Blo 2139435 4817753 := bstep (se 2 (by rfl) ⟨1806657, by rfl⟩ : syracuseStep 4817753 = 3613315) B3613315
theorem B3211835 : Blo 2139435 3211835 := bstep (se 1 (by rfl) ⟨2408876, by rfl⟩ : syracuseStep 3211835 = 4817753) B4817753
theorem B2141223 : Blo 2139435 2141223 := bstep (se 1 (by rfl) ⟨1605917, by rfl⟩ : syracuseStep 2141223 = 3211835) B3211835
theorem B2408881 : Blo 2139435 2408881 := bbase (se 2 (by rfl) ⟨903330, by rfl⟩ : syracuseStep 2408881 = 1806661) (by norm_num)
theorem B3211841 : Blo 2139435 3211841 := bstep (se 2 (by rfl) ⟨1204440, by rfl⟩ : syracuseStep 3211841 = 2408881) B2408881
theorem B2141227 : Blo 2139435 2141227 := bstep (se 1 (by rfl) ⟨1605920, by rfl⟩ : syracuseStep 2141227 = 3211841) B3211841
theorem B6097493 : Blo 2139435 6097493 := bbase (se 8 (by rfl) ⟨35727, by rfl⟩ : syracuseStep 6097493 = 71455) (by norm_num)
theorem B4064995 : Blo 2139435 4064995 := bstep (se 1 (by rfl) ⟨3048746, by rfl⟩ : syracuseStep 4064995 = 6097493) B6097493
theorem B5419993 : Blo 2139435 5419993 := bstep (se 2 (by rfl) ⟨2032497, by rfl⟩ : syracuseStep 5419993 = 4064995) B4064995
theorem B7226657 : Blo 2139435 7226657 := bstep (se 2 (by rfl) ⟨2709996, by rfl⟩ : syracuseStep 7226657 = 5419993) B5419993
theorem B4817771 : Blo 2139435 4817771 := bstep (se 1 (by rfl) ⟨3613328, by rfl⟩ : syracuseStep 4817771 = 7226657) B7226657
theorem B3211847 : Blo 2139435 3211847 := bstep (se 1 (by rfl) ⟨2408885, by rfl⟩ : syracuseStep 3211847 = 4817771) B4817771
theorem B2141231 : Blo 2139435 2141231 := bstep (se 1 (by rfl) ⟨1605923, by rfl⟩ : syracuseStep 2141231 = 3211847) B3211847
theorem B3211853 : Blo 2139435 3211853 := bbase (se 3 (by rfl) ⟨602222, by rfl⟩ : syracuseStep 3211853 = 1204445) (by norm_num)
theorem B2141235 : Blo 2139435 2141235 := bstep (se 1 (by rfl) ⟨1605926, by rfl⟩ : syracuseStep 2141235 = 3211853) B3211853
theorem B4817789 : Blo 2139435 4817789 := bbase (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) (by norm_num)
theorem B3211859 : Blo 2139435 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B2141239 : Blo 2139435 2141239 := bstep (se 1 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 2141239 = 3211859) B3211859
theorem B3613349 : Blo 2139435 3613349 := bbase (se 4 (by rfl) ⟨338751, by rfl⟩ : syracuseStep 3613349 = 677503) (by norm_num)
theorem B2408899 : Blo 2139435 2408899 := bstep (se 1 (by rfl) ⟨1806674, by rfl⟩ : syracuseStep 2408899 = 3613349) B3613349
theorem B3211865 : Blo 2139435 3211865 := bstep (se 2 (by rfl) ⟨1204449, by rfl⟩ : syracuseStep 3211865 = 2408899) B2408899
theorem B2141243 : Blo 2139435 2141243 := bstep (se 1 (by rfl) ⟨1605932, by rfl⟩ : syracuseStep 2141243 = 3211865) B3211865
theorem B2286577 : Blo 2139435 2286577 := bbase (se 2 (by rfl) ⟨857466, by rfl⟩ : syracuseStep 2286577 = 1714933) (by norm_num)
theorem B3048769 : Blo 2139435 3048769 := bstep (se 2 (by rfl) ⟨1143288, by rfl⟩ : syracuseStep 3048769 = 2286577) B2286577
theorem B16260101 : Blo 2139435 16260101 := bstep (se 4 (by rfl) ⟨1524384, by rfl⟩ : syracuseStep 16260101 = 3048769) B3048769
theorem B10840067 : Blo 2139435 10840067 := bstep (se 1 (by rfl) ⟨8130050, by rfl⟩ : syracuseStep 10840067 = 16260101) B16260101
theorem B7226711 : Blo 2139435 7226711 := bstep (se 1 (by rfl) ⟨5420033, by rfl⟩ : syracuseStep 7226711 = 10840067) B10840067
theorem B4817807 : Blo 2139435 4817807 := bstep (se 1 (by rfl) ⟨3613355, by rfl⟩ : syracuseStep 4817807 = 7226711) B7226711
theorem B3211871 : Blo 2139435 3211871 := bstep (se 1 (by rfl) ⟨2408903, by rfl⟩ : syracuseStep 3211871 = 4817807) B4817807
theorem B2141247 : Blo 2139435 2141247 := bstep (se 1 (by rfl) ⟨1605935, by rfl⟩ : syracuseStep 2141247 = 3211871) B3211871
theorem B3211877 : Blo 2139435 3211877 := bbase (se 4 (by rfl) ⟨301113, by rfl⟩ : syracuseStep 3211877 = 602227) (by norm_num)
theorem B2141251 : Blo 2139435 2141251 := bstep (se 1 (by rfl) ⟨1605938, by rfl⟩ : syracuseStep 2141251 = 3211877) B3211877
theorem B3048781 : Blo 2139435 3048781 := bbase (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) (by norm_num)
theorem B4065041 : Blo 2139435 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B2710027 : Blo 2139435 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B3613369 : Blo 2139435 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B4817825 : Blo 2139435 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B3211883 : Blo 2139435 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B2141255 : Blo 2139435 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B2408917 : Blo 2139435 2408917 := bbase (se 7 (by rfl) ⟨28229, by rfl⟩ : syracuseStep 2408917 = 56459) (by norm_num)
theorem B3211889 : Blo 2139435 3211889 := bstep (se 2 (by rfl) ⟨1204458, by rfl⟩ : syracuseStep 3211889 = 2408917) B2408917
theorem B2141259 : Blo 2139435 2141259 := bstep (se 1 (by rfl) ⟨1605944, by rfl⟩ : syracuseStep 2141259 = 3211889) B3211889
theorem B2710037 : Blo 2139435 2710037 := bbase (se 6 (by rfl) ⟨63516, by rfl⟩ : syracuseStep 2710037 = 127033) (by norm_num)
theorem B7226765 : Blo 2139435 7226765 := bstep (se 3 (by rfl) ⟨1355018, by rfl⟩ : syracuseStep 7226765 = 2710037) B2710037
theorem B4817843 : Blo 2139435 4817843 := bstep (se 1 (by rfl) ⟨3613382, by rfl⟩ : syracuseStep 4817843 = 7226765) B7226765
theorem B3211895 : Blo 2139435 3211895 := bstep (se 1 (by rfl) ⟨2408921, by rfl⟩ : syracuseStep 3211895 = 4817843) B4817843
theorem B2141263 : Blo 2139435 2141263 := bstep (se 1 (by rfl) ⟨1605947, by rfl⟩ : syracuseStep 2141263 = 3211895) B3211895
theorem B3211901 : Blo 2139435 3211901 := bbase (se 3 (by rfl) ⟨602231, by rfl⟩ : syracuseStep 3211901 = 1204463) (by norm_num)
theorem B2141267 : Blo 2139435 2141267 := bstep (se 1 (by rfl) ⟨1605950, by rfl⟩ : syracuseStep 2141267 = 3211901) B3211901
theorem B4817861 : Blo 2139435 4817861 := bbase (se 4 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 4817861 = 903349) (by norm_num)
theorem B3211907 : Blo 2139435 3211907 := bstep (se 1 (by rfl) ⟨2408930, by rfl⟩ : syracuseStep 3211907 = 4817861) B4817861
theorem B2141271 : Blo 2139435 2141271 := bstep (se 1 (by rfl) ⟨1605953, by rfl⟩ : syracuseStep 2141271 = 3211907) B3211907
theorem B7717301 : Blo 2139435 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B5144867 : Blo 2139435 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B3429911 : Blo 2139435 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B9146429 : Blo 2139435 9146429 := bstep (se 3 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 9146429 = 3429911) B3429911
theorem B6097619 : Blo 2139435 6097619 := bstep (se 1 (by rfl) ⟨4573214, by rfl⟩ : syracuseStep 6097619 = 9146429) B9146429
theorem B4065079 : Blo 2139435 4065079 := bstep (se 1 (by rfl) ⟨3048809, by rfl⟩ : syracuseStep 4065079 = 6097619) B6097619
theorem B5420105 : Blo 2139435 5420105 := bstep (se 2 (by rfl) ⟨2032539, by rfl⟩ : syracuseStep 5420105 = 4065079) B4065079
theorem B3613403 : Blo 2139435 3613403 := bstep (se 1 (by rfl) ⟨2710052, by rfl⟩ : syracuseStep 3613403 = 5420105) B5420105
theorem B2408935 : Blo 2139435 2408935 := bstep (se 1 (by rfl) ⟨1806701, by rfl⟩ : syracuseStep 2408935 = 3613403) B3613403
theorem B3211913 : Blo 2139435 3211913 := bstep (se 2 (by rfl) ⟨1204467, by rfl⟩ : syracuseStep 3211913 = 2408935) B2408935
theorem B2141275 : Blo 2139435 2141275 := bstep (se 1 (by rfl) ⟨1605956, by rfl⟩ : syracuseStep 2141275 = 3211913) B3211913
theorem B10840229 : Blo 2139435 10840229 := bbase (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) (by norm_num)
theorem B7226819 : Blo 2139435 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B4817879 : Blo 2139435 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B3211919 : Blo 2139435 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B2141279 : Blo 2139435 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B3211925 : Blo 2139435 3211925 := bbase (se 6 (by rfl) ⟨75279, by rfl⟩ : syracuseStep 3211925 = 150559) (by norm_num)
theorem B2141283 : Blo 2139435 2141283 := bstep (se 1 (by rfl) ⟨1605962, by rfl⟩ : syracuseStep 2141283 = 3211925) B3211925
theorem B8467541 : Blo 2139435 8467541 := bbase (se 8 (by rfl) ⟨49614, by rfl⟩ : syracuseStep 8467541 = 99229) (by norm_num)
theorem B5645027 : Blo 2139435 5645027 := bstep (se 1 (by rfl) ⟨4233770, by rfl⟩ : syracuseStep 5645027 = 8467541) B8467541
theorem B3763351 : Blo 2139435 3763351 := bstep (se 1 (by rfl) ⟨2822513, by rfl⟩ : syracuseStep 3763351 = 5645027) B5645027
theorem B5017801 : Blo 2139435 5017801 := bstep (se 2 (by rfl) ⟨1881675, by rfl⟩ : syracuseStep 5017801 = 3763351) B3763351
theorem B6690401 : Blo 2139435 6690401 := bstep (se 2 (by rfl) ⟨2508900, by rfl⟩ : syracuseStep 6690401 = 5017801) B5017801
theorem B4460267 : Blo 2139435 4460267 := bstep (se 1 (by rfl) ⟨3345200, by rfl⟩ : syracuseStep 4460267 = 6690401) B6690401
theorem B2973511 : Blo 2139435 2973511 := bstep (se 1 (by rfl) ⟨2230133, by rfl⟩ : syracuseStep 2973511 = 4460267) B4460267
theorem B3964681 : Blo 2139435 3964681 := bstep (se 2 (by rfl) ⟨1486755, by rfl⟩ : syracuseStep 3964681 = 2973511) B2973511
theorem B5286241 : Blo 2139435 5286241 := bstep (se 2 (by rfl) ⟨1982340, by rfl⟩ : syracuseStep 5286241 = 3964681) B3964681
theorem B28193285 : Blo 2139435 28193285 := bstep (se 4 (by rfl) ⟨2643120, by rfl⟩ : syracuseStep 28193285 = 5286241) B5286241
theorem B18795523 : Blo 2139435 18795523 := bstep (se 1 (by rfl) ⟨14096642, by rfl⟩ : syracuseStep 18795523 = 28193285) B28193285
theorem B25060697 : Blo 2139435 25060697 := bstep (se 2 (by rfl) ⟨9397761, by rfl⟩ : syracuseStep 25060697 = 18795523) B18795523
theorem B16707131 : Blo 2139435 16707131 := bstep (se 1 (by rfl) ⟨12530348, by rfl⟩ : syracuseStep 16707131 = 25060697) B25060697
theorem B11138087 : Blo 2139435 11138087 := bstep (se 1 (by rfl) ⟨8353565, by rfl⟩ : syracuseStep 11138087 = 16707131) B16707131
theorem B29701565 : Blo 2139435 29701565 := bstep (se 3 (by rfl) ⟨5569043, by rfl⟩ : syracuseStep 29701565 = 11138087) B11138087
theorem B19801043 : Blo 2139435 19801043 := bstep (se 1 (by rfl) ⟨14850782, by rfl⟩ : syracuseStep 19801043 = 29701565) B29701565
theorem B13200695 : Blo 2139435 13200695 := bstep (se 1 (by rfl) ⟨9900521, by rfl⟩ : syracuseStep 13200695 = 19801043) B19801043
theorem B8800463 : Blo 2139435 8800463 := bstep (se 1 (by rfl) ⟨6600347, by rfl⟩ : syracuseStep 8800463 = 13200695) B13200695
theorem B5866975 : Blo 2139435 5866975 := bstep (se 1 (by rfl) ⟨4400231, by rfl⟩ : syracuseStep 5866975 = 8800463) B8800463
theorem B31290533 : Blo 2139435 31290533 := bstep (se 4 (by rfl) ⟨2933487, by rfl⟩ : syracuseStep 31290533 = 5866975) B5866975
theorem B20860355 : Blo 2139435 20860355 := bstep (se 1 (by rfl) ⟨15645266, by rfl⟩ : syracuseStep 20860355 = 31290533) B31290533
theorem B13906903 : Blo 2139435 13906903 := bstep (se 1 (by rfl) ⟨10430177, by rfl⟩ : syracuseStep 13906903 = 20860355) B20860355
theorem B18542537 : Blo 2139435 18542537 := bstep (se 2 (by rfl) ⟨6953451, by rfl⟩ : syracuseStep 18542537 = 13906903) B13906903
theorem B12361691 : Blo 2139435 12361691 := bstep (se 1 (by rfl) ⟨9271268, by rfl⟩ : syracuseStep 12361691 = 18542537) B18542537
theorem B32964509 : Blo 2139435 32964509 := bstep (se 3 (by rfl) ⟨6180845, by rfl⟩ : syracuseStep 32964509 = 12361691) B12361691
theorem B87905357 : Blo 2139435 87905357 := bstep (se 3 (by rfl) ⟨16482254, by rfl⟩ : syracuseStep 87905357 = 32964509) B32964509
theorem B58603571 : Blo 2139435 58603571 := bstep (se 1 (by rfl) ⟨43952678, by rfl⟩ : syracuseStep 58603571 = 87905357) B87905357
theorem B39069047 : Blo 2139435 39069047 := bstep (se 1 (by rfl) ⟨29301785, by rfl⟩ : syracuseStep 39069047 = 58603571) B58603571
theorem B26046031 : Blo 2139435 26046031 := bstep (se 1 (by rfl) ⟨19534523, by rfl⟩ : syracuseStep 26046031 = 39069047) B39069047
theorem B34728041 : Blo 2139435 34728041 := bstep (se 2 (by rfl) ⟨13023015, by rfl⟩ : syracuseStep 34728041 = 26046031) B26046031
theorem B23152027 : Blo 2139435 23152027 := bstep (se 1 (by rfl) ⟨17364020, by rfl⟩ : syracuseStep 23152027 = 34728041) B34728041
theorem B30869369 : Blo 2139435 30869369 := bstep (se 2 (by rfl) ⟨11576013, by rfl⟩ : syracuseStep 30869369 = 23152027) B23152027
theorem B20579579 : Blo 2139435 20579579 := bstep (se 1 (by rfl) ⟨15434684, by rfl⟩ : syracuseStep 20579579 = 30869369) B30869369
theorem B13719719 : Blo 2139435 13719719 := bstep (se 1 (by rfl) ⟨10289789, by rfl⟩ : syracuseStep 13719719 = 20579579) B20579579
theorem B9146479 : Blo 2139435 9146479 := bstep (se 1 (by rfl) ⟨6859859, by rfl⟩ : syracuseStep 9146479 = 13719719) B13719719
theorem B12195305 : Blo 2139435 12195305 := bstep (se 2 (by rfl) ⟨4573239, by rfl⟩ : syracuseStep 12195305 = 9146479) B9146479
theorem B8130203 : Blo 2139435 8130203 := bstep (se 1 (by rfl) ⟨6097652, by rfl⟩ : syracuseStep 8130203 = 12195305) B12195305
theorem B5420135 : Blo 2139435 5420135 := bstep (se 1 (by rfl) ⟨4065101, by rfl⟩ : syracuseStep 5420135 = 8130203) B8130203
theorem B3613423 : Blo 2139435 3613423 := bstep (se 1 (by rfl) ⟨2710067, by rfl⟩ : syracuseStep 3613423 = 5420135) B5420135
theorem B4817897 : Blo 2139435 4817897 := bstep (se 2 (by rfl) ⟨1806711, by rfl⟩ : syracuseStep 4817897 = 3613423) B3613423
theorem B3211931 : Blo 2139435 3211931 := bstep (se 1 (by rfl) ⟨2408948, by rfl⟩ : syracuseStep 3211931 = 4817897) B4817897
theorem B2141287 : Blo 2139435 2141287 := bstep (se 1 (by rfl) ⟨1605965, by rfl⟩ : syracuseStep 2141287 = 3211931) B3211931
theorem B2408953 : Blo 2139435 2408953 := bbase (se 2 (by rfl) ⟨903357, by rfl⟩ : syracuseStep 2408953 = 1806715) (by norm_num)
theorem B3211937 : Blo 2139435 3211937 := bstep (se 2 (by rfl) ⟨1204476, by rfl⟩ : syracuseStep 3211937 = 2408953) B2408953
theorem B2141291 : Blo 2139435 2141291 := bstep (se 1 (by rfl) ⟨1605968, by rfl⟩ : syracuseStep 2141291 = 3211937) B3211937
theorem B2572457 : Blo 2139435 2572457 := bbase (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) (by norm_num)
theorem B6859885 : Blo 2139435 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B9146513 : Blo 2139435 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B6097675 : Blo 2139435 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B8130233 : Blo 2139435 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B5420155 : Blo 2139435 5420155 := bstep (se 1 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 5420155 = 8130233) B8130233
theorem B7226873 : Blo 2139435 7226873 := bstep (se 2 (by rfl) ⟨2710077, by rfl⟩ : syracuseStep 7226873 = 5420155) B5420155
theorem B4817915 : Blo 2139435 4817915 := bstep (se 1 (by rfl) ⟨3613436, by rfl⟩ : syracuseStep 4817915 = 7226873) B7226873
theorem B3211943 : Blo 2139435 3211943 := bstep (se 1 (by rfl) ⟨2408957, by rfl⟩ : syracuseStep 3211943 = 4817915) B4817915
theorem B2141295 : Blo 2139435 2141295 := bstep (se 1 (by rfl) ⟨1605971, by rfl⟩ : syracuseStep 2141295 = 3211943) B3211943
theorem B3211949 : Blo 2139435 3211949 := bbase (se 3 (by rfl) ⟨602240, by rfl⟩ : syracuseStep 3211949 = 1204481) (by norm_num)
theorem B2141299 : Blo 2139435 2141299 := bstep (se 1 (by rfl) ⟨1605974, by rfl⟩ : syracuseStep 2141299 = 3211949) B3211949
theorem B4817933 : Blo 2139435 4817933 := bbase (se 3 (by rfl) ⟨903362, by rfl⟩ : syracuseStep 4817933 = 1806725) (by norm_num)
theorem B3211955 : Blo 2139435 3211955 := bstep (se 1 (by rfl) ⟨2408966, by rfl⟩ : syracuseStep 3211955 = 4817933) B4817933
theorem B2141303 : Blo 2139435 2141303 := bstep (se 1 (by rfl) ⟨1605977, by rfl⟩ : syracuseStep 2141303 = 3211955) B3211955
theorem B2710093 : Blo 2139435 2710093 := bbase (se 3 (by rfl) ⟨508142, by rfl⟩ : syracuseStep 2710093 = 1016285) (by norm_num)
theorem B3613457 : Blo 2139435 3613457 := bstep (se 2 (by rfl) ⟨1355046, by rfl⟩ : syracuseStep 3613457 = 2710093) B2710093
theorem B2408971 : Blo 2139435 2408971 := bstep (se 1 (by rfl) ⟨1806728, by rfl⟩ : syracuseStep 2408971 = 3613457) B3613457
theorem B3211961 : Blo 2139435 3211961 := bstep (se 2 (by rfl) ⟨1204485, by rfl⟩ : syracuseStep 3211961 = 2408971) B2408971
theorem B2141307 : Blo 2139435 2141307 := bstep (se 1 (by rfl) ⟨1605980, by rfl⟩ : syracuseStep 2141307 = 3211961) B3211961
theorem B12530485 : Blo 2139435 12530485 := bbase (se 5 (by rfl) ⟨587366, by rfl⟩ : syracuseStep 12530485 = 1174733) (by norm_num)
theorem B16707313 : Blo 2139435 16707313 := bstep (se 2 (by rfl) ⟨6265242, by rfl⟩ : syracuseStep 16707313 = 12530485) B12530485
theorem B89105669 : Blo 2139435 89105669 := bstep (se 4 (by rfl) ⟨8353656, by rfl⟩ : syracuseStep 89105669 = 16707313) B16707313
theorem B59403779 : Blo 2139435 59403779 := bstep (se 1 (by rfl) ⟨44552834, by rfl⟩ : syracuseStep 59403779 = 89105669) B89105669
theorem B39602519 : Blo 2139435 39602519 := bstep (se 1 (by rfl) ⟨29701889, by rfl⟩ : syracuseStep 39602519 = 59403779) B59403779
theorem B26401679 : Blo 2139435 26401679 := bstep (se 1 (by rfl) ⟨19801259, by rfl⟩ : syracuseStep 26401679 = 39602519) B39602519
theorem B17601119 : Blo 2139435 17601119 := bstep (se 1 (by rfl) ⟨13200839, by rfl⟩ : syracuseStep 17601119 = 26401679) B26401679
theorem B11734079 : Blo 2139435 11734079 := bstep (se 1 (by rfl) ⟨8800559, by rfl⟩ : syracuseStep 11734079 = 17601119) B17601119
theorem B31290877 : Blo 2139435 31290877 := bstep (se 3 (by rfl) ⟨5867039, by rfl⟩ : syracuseStep 31290877 = 11734079) B11734079
theorem B41721169 : Blo 2139435 41721169 := bstep (se 2 (by rfl) ⟨15645438, by rfl⟩ : syracuseStep 41721169 = 31290877) B31290877
theorem B55628225 : Blo 2139435 55628225 := bstep (se 2 (by rfl) ⟨20860584, by rfl⟩ : syracuseStep 55628225 = 41721169) B41721169
theorem B37085483 : Blo 2139435 37085483 := bstep (se 1 (by rfl) ⟨27814112, by rfl⟩ : syracuseStep 37085483 = 55628225) B55628225
theorem B98894621 : Blo 2139435 98894621 := bstep (se 3 (by rfl) ⟨18542741, by rfl⟩ : syracuseStep 98894621 = 37085483) B37085483
theorem B65929747 : Blo 2139435 65929747 := bstep (se 1 (by rfl) ⟨49447310, by rfl⟩ : syracuseStep 65929747 = 98894621) B98894621
theorem B87906329 : Blo 2139435 87906329 := bstep (se 2 (by rfl) ⟨32964873, by rfl⟩ : syracuseStep 87906329 = 65929747) B65929747
theorem B58604219 : Blo 2139435 58604219 := bstep (se 1 (by rfl) ⟨43953164, by rfl⟩ : syracuseStep 58604219 = 87906329) B87906329
theorem B39069479 : Blo 2139435 39069479 := bstep (se 1 (by rfl) ⟨29302109, by rfl⟩ : syracuseStep 39069479 = 58604219) B58604219
theorem B104185277 : Blo 2139435 104185277 := bstep (se 3 (by rfl) ⟨19534739, by rfl⟩ : syracuseStep 104185277 = 39069479) B39069479
theorem B69456851 : Blo 2139435 69456851 := bstep (se 1 (by rfl) ⟨52092638, by rfl⟩ : syracuseStep 69456851 = 104185277) B104185277
theorem B46304567 : Blo 2139435 46304567 := bstep (se 1 (by rfl) ⟨34728425, by rfl⟩ : syracuseStep 46304567 = 69456851) B69456851
theorem B30869711 : Blo 2139435 30869711 := bstep (se 1 (by rfl) ⟨23152283, by rfl⟩ : syracuseStep 30869711 = 46304567) B46304567
theorem B20579807 : Blo 2139435 20579807 := bstep (se 1 (by rfl) ⟨15434855, by rfl⟩ : syracuseStep 20579807 = 30869711) B30869711
theorem B13719871 : Blo 2139435 13719871 := bstep (se 1 (by rfl) ⟨10289903, by rfl⟩ : syracuseStep 13719871 = 20579807) B20579807
theorem B18293161 : Blo 2139435 18293161 := bstep (se 2 (by rfl) ⟨6859935, by rfl⟩ : syracuseStep 18293161 = 13719871) B13719871
theorem B24390881 : Blo 2139435 24390881 := bstep (se 2 (by rfl) ⟨9146580, by rfl⟩ : syracuseStep 24390881 = 18293161) B18293161
theorem B16260587 : Blo 2139435 16260587 := bstep (se 1 (by rfl) ⟨12195440, by rfl⟩ : syracuseStep 16260587 = 24390881) B24390881
theorem B10840391 : Blo 2139435 10840391 := bstep (se 1 (by rfl) ⟨8130293, by rfl⟩ : syracuseStep 10840391 = 16260587) B16260587
theorem B7226927 : Blo 2139435 7226927 := bstep (se 1 (by rfl) ⟨5420195, by rfl⟩ : syracuseStep 7226927 = 10840391) B10840391
theorem B4817951 : Blo 2139435 4817951 := bstep (se 1 (by rfl) ⟨3613463, by rfl⟩ : syracuseStep 4817951 = 7226927) B7226927
theorem B3211967 : Blo 2139435 3211967 := bstep (se 1 (by rfl) ⟨2408975, by rfl⟩ : syracuseStep 3211967 = 4817951) B4817951
theorem B2141311 : Blo 2139435 2141311 := bstep (se 1 (by rfl) ⟨1605983, by rfl⟩ : syracuseStep 2141311 = 3211967) B3211967
theorem B3211973 : Blo 2139435 3211973 := bbase (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) (by norm_num)
theorem B2141315 : Blo 2139435 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B3613477 : Blo 2139435 3613477 := bbase (se 4 (by rfl) ⟨338763, by rfl⟩ : syracuseStep 3613477 = 677527) (by norm_num)
theorem B4817969 : Blo 2139435 4817969 := bstep (se 2 (by rfl) ⟨1806738, by rfl⟩ : syracuseStep 4817969 = 3613477) B3613477
theorem B3211979 : Blo 2139435 3211979 := bstep (se 1 (by rfl) ⟨2408984, by rfl⟩ : syracuseStep 3211979 = 4817969) B4817969
theorem B2141319 : Blo 2139435 2141319 := bstep (se 1 (by rfl) ⟨1605989, by rfl⟩ : syracuseStep 2141319 = 3211979) B3211979
theorem B2408989 : Blo 2139435 2408989 := bbase (se 3 (by rfl) ⟨451685, by rfl⟩ : syracuseStep 2408989 = 903371) (by norm_num)
theorem B3211985 : Blo 2139435 3211985 := bstep (se 2 (by rfl) ⟨1204494, by rfl⟩ : syracuseStep 3211985 = 2408989) B2408989
theorem B2141323 : Blo 2139435 2141323 := bstep (se 1 (by rfl) ⟨1605992, by rfl⟩ : syracuseStep 2141323 = 3211985) B3211985
theorem B7226981 : Blo 2139435 7226981 := bbase (se 4 (by rfl) ⟨677529, by rfl⟩ : syracuseStep 7226981 = 1355059) (by norm_num)
theorem B4817987 : Blo 2139435 4817987 := bstep (se 1 (by rfl) ⟨3613490, by rfl⟩ : syracuseStep 4817987 = 7226981) B7226981
theorem B3211991 : Blo 2139435 3211991 := bstep (se 1 (by rfl) ⟨2408993, by rfl⟩ : syracuseStep 3211991 = 4817987) B4817987
theorem B2141327 : Blo 2139435 2141327 := bstep (se 1 (by rfl) ⟨1605995, by rfl⟩ : syracuseStep 2141327 = 3211991) B3211991
theorem B3211997 : Blo 2139435 3211997 := bbase (se 3 (by rfl) ⟨602249, by rfl⟩ : syracuseStep 3211997 = 1204499) (by norm_num)
theorem B2141331 : Blo 2139435 2141331 := bstep (se 1 (by rfl) ⟨1605998, by rfl⟩ : syracuseStep 2141331 = 3211997) B3211997
theorem B4818005 : Blo 2139435 4818005 := bbase (se 8 (by rfl) ⟨28230, by rfl⟩ : syracuseStep 4818005 = 56461) (by norm_num)
theorem B3212003 : Blo 2139435 3212003 := bstep (se 1 (by rfl) ⟨2409002, by rfl⟩ : syracuseStep 3212003 = 4818005) B4818005
theorem B2141335 : Blo 2139435 2141335 := bstep (se 1 (by rfl) ⟨1606001, by rfl⟩ : syracuseStep 2141335 = 3212003) B3212003
theorem B16707541 : Blo 2139435 16707541 := bbase (se 7 (by rfl) ⟨195791, by rfl⟩ : syracuseStep 16707541 = 391583) (by norm_num)
theorem B22276721 : Blo 2139435 22276721 := bstep (se 2 (by rfl) ⟨8353770, by rfl⟩ : syracuseStep 22276721 = 16707541) B16707541
theorem B14851147 : Blo 2139435 14851147 := bstep (se 1 (by rfl) ⟨11138360, by rfl⟩ : syracuseStep 14851147 = 22276721) B22276721
theorem B19801529 : Blo 2139435 19801529 := bstep (se 2 (by rfl) ⟨7425573, by rfl⟩ : syracuseStep 19801529 = 14851147) B14851147
theorem B13201019 : Blo 2139435 13201019 := bstep (se 1 (by rfl) ⟨9900764, by rfl⟩ : syracuseStep 13201019 = 19801529) B19801529
theorem B8800679 : Blo 2139435 8800679 := bstep (se 1 (by rfl) ⟨6600509, by rfl⟩ : syracuseStep 8800679 = 13201019) B13201019
theorem B5867119 : Blo 2139435 5867119 := bstep (se 1 (by rfl) ⟨4400339, by rfl⟩ : syracuseStep 5867119 = 8800679) B8800679
theorem B7822825 : Blo 2139435 7822825 := bstep (se 2 (by rfl) ⟨2933559, by rfl⟩ : syracuseStep 7822825 = 5867119) B5867119
theorem B41721733 : Blo 2139435 41721733 := bstep (se 4 (by rfl) ⟨3911412, by rfl⟩ : syracuseStep 41721733 = 7822825) B7822825
theorem B55628977 : Blo 2139435 55628977 := bstep (se 2 (by rfl) ⟨20860866, by rfl⟩ : syracuseStep 55628977 = 41721733) B41721733
theorem B74171969 : Blo 2139435 74171969 := bstep (se 2 (by rfl) ⟨27814488, by rfl⟩ : syracuseStep 74171969 = 55628977) B55628977
theorem B49447979 : Blo 2139435 49447979 := bstep (se 1 (by rfl) ⟨37085984, by rfl⟩ : syracuseStep 49447979 = 74171969) B74171969
theorem B32965319 : Blo 2139435 32965319 := bstep (se 1 (by rfl) ⟨24723989, by rfl⟩ : syracuseStep 32965319 = 49447979) B49447979
theorem B21976879 : Blo 2139435 21976879 := bstep (se 1 (by rfl) ⟨16482659, by rfl⟩ : syracuseStep 21976879 = 32965319) B32965319
theorem B29302505 : Blo 2139435 29302505 := bstep (se 2 (by rfl) ⟨10988439, by rfl⟩ : syracuseStep 29302505 = 21976879) B21976879
theorem B19535003 : Blo 2139435 19535003 := bstep (se 1 (by rfl) ⟨14651252, by rfl⟩ : syracuseStep 19535003 = 29302505) B29302505
theorem B13023335 : Blo 2139435 13023335 := bstep (se 1 (by rfl) ⟨9767501, by rfl⟩ : syracuseStep 13023335 = 19535003) B19535003
theorem B8682223 : Blo 2139435 8682223 := bstep (se 1 (by rfl) ⟨6511667, by rfl⟩ : syracuseStep 8682223 = 13023335) B13023335
theorem B11576297 : Blo 2139435 11576297 := bstep (se 2 (by rfl) ⟨4341111, by rfl⟩ : syracuseStep 11576297 = 8682223) B8682223
theorem B7717531 : Blo 2139435 7717531 := bstep (se 1 (by rfl) ⟨5788148, by rfl⟩ : syracuseStep 7717531 = 11576297) B11576297
theorem B10290041 : Blo 2139435 10290041 := bstep (se 2 (by rfl) ⟨3858765, by rfl⟩ : syracuseStep 10290041 = 7717531) B7717531
theorem B6860027 : Blo 2139435 6860027 := bstep (se 1 (by rfl) ⟨5145020, by rfl⟩ : syracuseStep 6860027 = 10290041) B10290041
theorem B4573351 : Blo 2139435 4573351 := bstep (se 1 (by rfl) ⟨3430013, by rfl⟩ : syracuseStep 4573351 = 6860027) B6860027
theorem B6097801 : Blo 2139435 6097801 := bstep (se 2 (by rfl) ⟨2286675, by rfl⟩ : syracuseStep 6097801 = 4573351) B4573351
theorem B8130401 : Blo 2139435 8130401 := bstep (se 2 (by rfl) ⟨3048900, by rfl⟩ : syracuseStep 8130401 = 6097801) B6097801
theorem B5420267 : Blo 2139435 5420267 := bstep (se 1 (by rfl) ⟨4065200, by rfl⟩ : syracuseStep 5420267 = 8130401) B8130401
theorem B3613511 : Blo 2139435 3613511 := bstep (se 1 (by rfl) ⟨2710133, by rfl⟩ : syracuseStep 3613511 = 5420267) B5420267
theorem B2409007 : Blo 2139435 2409007 := bstep (se 1 (by rfl) ⟨1806755, by rfl⟩ : syracuseStep 2409007 = 3613511) B3613511
theorem B3212009 : Blo 2139435 3212009 := bstep (se 2 (by rfl) ⟨1204503, by rfl⟩ : syracuseStep 3212009 = 2409007) B2409007
theorem B2141339 : Blo 2139435 2141339 := bstep (se 1 (by rfl) ⟨1606004, by rfl⟩ : syracuseStep 2141339 = 3212009) B3212009
theorem B4176893 : Blo 2139435 4176893 := bbase (se 3 (by rfl) ⟨783167, by rfl⟩ : syracuseStep 4176893 = 1566335) (by norm_num)
theorem B11138381 : Blo 2139435 11138381 := bstep (se 3 (by rfl) ⟨2088446, by rfl⟩ : syracuseStep 11138381 = 4176893) B4176893
theorem B7425587 : Blo 2139435 7425587 := bstep (se 1 (by rfl) ⟨5569190, by rfl⟩ : syracuseStep 7425587 = 11138381) B11138381
theorem B4950391 : Blo 2139435 4950391 := bstep (se 1 (by rfl) ⟨3712793, by rfl⟩ : syracuseStep 4950391 = 7425587) B7425587
theorem B6600521 : Blo 2139435 6600521 := bstep (se 2 (by rfl) ⟨2475195, by rfl⟩ : syracuseStep 6600521 = 4950391) B4950391
theorem B4400347 : Blo 2139435 4400347 := bstep (se 1 (by rfl) ⟨3300260, by rfl⟩ : syracuseStep 4400347 = 6600521) B6600521
theorem B5867129 : Blo 2139435 5867129 := bstep (se 2 (by rfl) ⟨2200173, by rfl⟩ : syracuseStep 5867129 = 4400347) B4400347
theorem B3911419 : Blo 2139435 3911419 := bstep (se 1 (by rfl) ⟨2933564, by rfl⟩ : syracuseStep 3911419 = 5867129) B5867129
theorem B20860901 : Blo 2139435 20860901 := bstep (se 4 (by rfl) ⟨1955709, by rfl⟩ : syracuseStep 20860901 = 3911419) B3911419
theorem B13907267 : Blo 2139435 13907267 := bstep (se 1 (by rfl) ⟨10430450, by rfl⟩ : syracuseStep 13907267 = 20860901) B20860901
theorem B9271511 : Blo 2139435 9271511 := bstep (se 1 (by rfl) ⟨6953633, by rfl⟩ : syracuseStep 9271511 = 13907267) B13907267
theorem B6181007 : Blo 2139435 6181007 := bstep (se 1 (by rfl) ⟨4635755, by rfl⟩ : syracuseStep 6181007 = 9271511) B9271511
theorem B16482685 : Blo 2139435 16482685 := bstep (se 3 (by rfl) ⟨3090503, by rfl⟩ : syracuseStep 16482685 = 6181007) B6181007
theorem B21976913 : Blo 2139435 21976913 := bstep (se 2 (by rfl) ⟨8241342, by rfl⟩ : syracuseStep 21976913 = 16482685) B16482685
theorem B14651275 : Blo 2139435 14651275 := bstep (se 1 (by rfl) ⟨10988456, by rfl⟩ : syracuseStep 14651275 = 21976913) B21976913
theorem B19535033 : Blo 2139435 19535033 := bstep (se 2 (by rfl) ⟨7325637, by rfl⟩ : syracuseStep 19535033 = 14651275) B14651275
theorem B13023355 : Blo 2139435 13023355 := bstep (se 1 (by rfl) ⟨9767516, by rfl⟩ : syracuseStep 13023355 = 19535033) B19535033
theorem B17364473 : Blo 2139435 17364473 := bstep (se 2 (by rfl) ⟨6511677, by rfl⟩ : syracuseStep 17364473 = 13023355) B13023355
theorem B11576315 : Blo 2139435 11576315 := bstep (se 1 (by rfl) ⟨8682236, by rfl⟩ : syracuseStep 11576315 = 17364473) B17364473
theorem B30870173 : Blo 2139435 30870173 := bstep (se 3 (by rfl) ⟨5788157, by rfl⟩ : syracuseStep 30870173 = 11576315) B11576315
theorem B20580115 : Blo 2139435 20580115 := bstep (se 1 (by rfl) ⟨15435086, by rfl⟩ : syracuseStep 20580115 = 30870173) B30870173
theorem B27440153 : Blo 2139435 27440153 := bstep (se 2 (by rfl) ⟨10290057, by rfl⟩ : syracuseStep 27440153 = 20580115) B20580115
theorem B18293435 : Blo 2139435 18293435 := bstep (se 1 (by rfl) ⟨13720076, by rfl⟩ : syracuseStep 18293435 = 27440153) B27440153
theorem B12195623 : Blo 2139435 12195623 := bstep (se 1 (by rfl) ⟨9146717, by rfl⟩ : syracuseStep 12195623 = 18293435) B18293435
theorem B8130415 : Blo 2139435 8130415 := bstep (se 1 (by rfl) ⟨6097811, by rfl⟩ : syracuseStep 8130415 = 12195623) B12195623
theorem B10840553 : Blo 2139435 10840553 := bstep (se 2 (by rfl) ⟨4065207, by rfl⟩ : syracuseStep 10840553 = 8130415) B8130415
theorem B7227035 : Blo 2139435 7227035 := bstep (se 1 (by rfl) ⟨5420276, by rfl⟩ : syracuseStep 7227035 = 10840553) B10840553
theorem B4818023 : Blo 2139435 4818023 := bstep (se 1 (by rfl) ⟨3613517, by rfl⟩ : syracuseStep 4818023 = 7227035) B7227035
theorem B3212015 : Blo 2139435 3212015 := bstep (se 1 (by rfl) ⟨2409011, by rfl⟩ : syracuseStep 3212015 = 4818023) B4818023
theorem B2141343 : Blo 2139435 2141343 := bstep (se 1 (by rfl) ⟨1606007, by rfl⟩ : syracuseStep 2141343 = 3212015) B3212015
theorem B3212021 : Blo 2139435 3212021 := bbase (se 5 (by rfl) ⟨150563, by rfl⟩ : syracuseStep 3212021 = 301127) (by norm_num)
theorem B2141347 : Blo 2139435 2141347 := bstep (se 1 (by rfl) ⟨1606010, by rfl⟩ : syracuseStep 2141347 = 3212021) B3212021
theorem B5788181 : Blo 2139435 5788181 := bbase (se 6 (by rfl) ⟨135660, by rfl⟩ : syracuseStep 5788181 = 271321) (by norm_num)
theorem B3858787 : Blo 2139435 3858787 := bstep (se 1 (by rfl) ⟨2894090, by rfl⟩ : syracuseStep 3858787 = 5788181) B5788181
theorem B5145049 : Blo 2139435 5145049 := bstep (se 2 (by rfl) ⟨1929393, by rfl⟩ : syracuseStep 5145049 = 3858787) B3858787
theorem B6860065 : Blo 2139435 6860065 := bstep (se 2 (by rfl) ⟨2572524, by rfl⟩ : syracuseStep 6860065 = 5145049) B5145049
theorem B9146753 : Blo 2139435 9146753 := bstep (se 2 (by rfl) ⟨3430032, by rfl⟩ : syracuseStep 9146753 = 6860065) B6860065
theorem B6097835 : Blo 2139435 6097835 := bstep (se 1 (by rfl) ⟨4573376, by rfl⟩ : syracuseStep 6097835 = 9146753) B9146753
theorem B4065223 : Blo 2139435 4065223 := bstep (se 1 (by rfl) ⟨3048917, by rfl⟩ : syracuseStep 4065223 = 6097835) B6097835
theorem B5420297 : Blo 2139435 5420297 := bstep (se 2 (by rfl) ⟨2032611, by rfl⟩ : syracuseStep 5420297 = 4065223) B4065223
theorem B3613531 : Blo 2139435 3613531 := bstep (se 1 (by rfl) ⟨2710148, by rfl⟩ : syracuseStep 3613531 = 5420297) B5420297
theorem B4818041 : Blo 2139435 4818041 := bstep (se 2 (by rfl) ⟨1806765, by rfl⟩ : syracuseStep 4818041 = 3613531) B3613531
theorem B3212027 : Blo 2139435 3212027 := bstep (se 1 (by rfl) ⟨2409020, by rfl⟩ : syracuseStep 3212027 = 4818041) B4818041
theorem B2141351 : Blo 2139435 2141351 := bstep (se 1 (by rfl) ⟨1606013, by rfl⟩ : syracuseStep 2141351 = 3212027) B3212027
theorem B2409025 : Blo 2139435 2409025 := bbase (se 2 (by rfl) ⟨903384, by rfl⟩ : syracuseStep 2409025 = 1806769) (by norm_num)
theorem B3212033 : Blo 2139435 3212033 := bstep (se 2 (by rfl) ⟨1204512, by rfl⟩ : syracuseStep 3212033 = 2409025) B2409025
theorem B2141355 : Blo 2139435 2141355 := bstep (se 1 (by rfl) ⟨1606016, by rfl⟩ : syracuseStep 2141355 = 3212033) B3212033
theorem B5420317 : Blo 2139435 5420317 := bbase (se 3 (by rfl) ⟨1016309, by rfl⟩ : syracuseStep 5420317 = 2032619) (by norm_num)
theorem B7227089 : Blo 2139435 7227089 := bstep (se 2 (by rfl) ⟨2710158, by rfl⟩ : syracuseStep 7227089 = 5420317) B5420317
theorem B4818059 : Blo 2139435 4818059 := bstep (se 1 (by rfl) ⟨3613544, by rfl⟩ : syracuseStep 4818059 = 7227089) B7227089
theorem B3212039 : Blo 2139435 3212039 := bstep (se 1 (by rfl) ⟨2409029, by rfl⟩ : syracuseStep 3212039 = 4818059) B4818059
theorem B2141359 : Blo 2139435 2141359 := bstep (se 1 (by rfl) ⟨1606019, by rfl⟩ : syracuseStep 2141359 = 3212039) B3212039
theorem B3212045 : Blo 2139435 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B2141363 : Blo 2139435 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B4818077 : Blo 2139435 4818077 := bbase (se 3 (by rfl) ⟨903389, by rfl⟩ : syracuseStep 4818077 = 1806779) (by norm_num)
theorem B3212051 : Blo 2139435 3212051 := bstep (se 1 (by rfl) ⟨2409038, by rfl⟩ : syracuseStep 3212051 = 4818077) B4818077
theorem B2141367 : Blo 2139435 2141367 := bstep (se 1 (by rfl) ⟨1606025, by rfl⟩ : syracuseStep 2141367 = 3212051) B3212051
theorem B3613565 : Blo 2139435 3613565 := bbase (se 3 (by rfl) ⟨677543, by rfl⟩ : syracuseStep 3613565 = 1355087) (by norm_num)
theorem B2409043 : Blo 2139435 2409043 := bstep (se 1 (by rfl) ⟨1806782, by rfl⟩ : syracuseStep 2409043 = 3613565) B3613565
theorem B3212057 : Blo 2139435 3212057 := bstep (se 2 (by rfl) ⟨1204521, by rfl⟩ : syracuseStep 3212057 = 2409043) B2409043
theorem B2141371 : Blo 2139435 2141371 := bstep (se 1 (by rfl) ⟨1606028, by rfl⟩ : syracuseStep 2141371 = 3212057) B3212057
theorem B2572553 : Blo 2139435 2572553 := bbase (se 2 (by rfl) ⟨964707, by rfl⟩ : syracuseStep 2572553 = 1929415) (by norm_num)
theorem B6860141 : Blo 2139435 6860141 := bstep (se 3 (by rfl) ⟨1286276, by rfl⟩ : syracuseStep 6860141 = 2572553) B2572553
theorem B4573427 : Blo 2139435 4573427 := bstep (se 1 (by rfl) ⟨3430070, by rfl⟩ : syracuseStep 4573427 = 6860141) B6860141
theorem B12195805 : Blo 2139435 12195805 := bstep (se 3 (by rfl) ⟨2286713, by rfl⟩ : syracuseStep 12195805 = 4573427) B4573427
theorem B16261073 : Blo 2139435 16261073 := bstep (se 2 (by rfl) ⟨6097902, by rfl⟩ : syracuseStep 16261073 = 12195805) B12195805
theorem B10840715 : Blo 2139435 10840715 := bstep (se 1 (by rfl) ⟨8130536, by rfl⟩ : syracuseStep 10840715 = 16261073) B16261073
theorem B7227143 : Blo 2139435 7227143 := bstep (se 1 (by rfl) ⟨5420357, by rfl⟩ : syracuseStep 7227143 = 10840715) B10840715
theorem B4818095 : Blo 2139435 4818095 := bstep (se 1 (by rfl) ⟨3613571, by rfl⟩ : syracuseStep 4818095 = 7227143) B7227143
theorem B3212063 : Blo 2139435 3212063 := bstep (se 1 (by rfl) ⟨2409047, by rfl⟩ : syracuseStep 3212063 = 4818095) B4818095
theorem B2141375 : Blo 2139435 2141375 := bstep (se 1 (by rfl) ⟨1606031, by rfl⟩ : syracuseStep 2141375 = 3212063) B3212063
theorem B3212069 : Blo 2139435 3212069 := bbase (se 4 (by rfl) ⟨301131, by rfl⟩ : syracuseStep 3212069 = 602263) (by norm_num)
theorem B2141379 : Blo 2139435 2141379 := bstep (se 1 (by rfl) ⟨1606034, by rfl⟩ : syracuseStep 2141379 = 3212069) B3212069
theorem B2710189 : Blo 2139435 2710189 := bbase (se 3 (by rfl) ⟨508160, by rfl⟩ : syracuseStep 2710189 = 1016321) (by norm_num)
theorem B3613585 : Blo 2139435 3613585 := bstep (se 2 (by rfl) ⟨1355094, by rfl⟩ : syracuseStep 3613585 = 2710189) B2710189
theorem B4818113 : Blo 2139435 4818113 := bstep (se 2 (by rfl) ⟨1806792, by rfl⟩ : syracuseStep 4818113 = 3613585) B3613585
theorem B3212075 : Blo 2139435 3212075 := bstep (se 1 (by rfl) ⟨2409056, by rfl⟩ : syracuseStep 3212075 = 4818113) B4818113
theorem B2141383 : Blo 2139435 2141383 := bstep (se 1 (by rfl) ⟨1606037, by rfl⟩ : syracuseStep 2141383 = 3212075) B3212075
theorem B2409061 : Blo 2139435 2409061 := bbase (se 4 (by rfl) ⟨225849, by rfl⟩ : syracuseStep 2409061 = 451699) (by norm_num)
theorem B3212081 : Blo 2139435 3212081 := bstep (se 2 (by rfl) ⟨1204530, by rfl⟩ : syracuseStep 3212081 = 2409061) B2409061
theorem B2141387 : Blo 2139435 2141387 := bstep (se 1 (by rfl) ⟨1606040, by rfl⟩ : syracuseStep 2141387 = 3212081) B3212081
theorem B2572573 : Blo 2139435 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B3430097 : Blo 2139435 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B2286731 : Blo 2139435 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B6097949 : Blo 2139435 6097949 := bstep (se 3 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 6097949 = 2286731) B2286731
theorem B4065299 : Blo 2139435 4065299 := bstep (se 1 (by rfl) ⟨3048974, by rfl⟩ : syracuseStep 4065299 = 6097949) B6097949
theorem B2710199 : Blo 2139435 2710199 := bstep (se 1 (by rfl) ⟨2032649, by rfl⟩ : syracuseStep 2710199 = 4065299) B4065299
theorem B7227197 : Blo 2139435 7227197 := bstep (se 3 (by rfl) ⟨1355099, by rfl⟩ : syracuseStep 7227197 = 2710199) B2710199
theorem B4818131 : Blo 2139435 4818131 := bstep (se 1 (by rfl) ⟨3613598, by rfl⟩ : syracuseStep 4818131 = 7227197) B7227197
theorem B3212087 : Blo 2139435 3212087 := bstep (se 1 (by rfl) ⟨2409065, by rfl⟩ : syracuseStep 3212087 = 4818131) B4818131
theorem B2141391 : Blo 2139435 2141391 := bstep (se 1 (by rfl) ⟨1606043, by rfl⟩ : syracuseStep 2141391 = 3212087) B3212087
theorem B3212093 : Blo 2139435 3212093 := bbase (se 3 (by rfl) ⟨602267, by rfl⟩ : syracuseStep 3212093 = 1204535) (by norm_num)
theorem B2141395 : Blo 2139435 2141395 := bstep (se 1 (by rfl) ⟨1606046, by rfl⟩ : syracuseStep 2141395 = 3212093) B3212093
theorem B4818149 : Blo 2139435 4818149 := bbase (se 4 (by rfl) ⟨451701, by rfl⟩ : syracuseStep 4818149 = 903403) (by norm_num)
theorem B3212099 : Blo 2139435 3212099 := bstep (se 1 (by rfl) ⟨2409074, by rfl⟩ : syracuseStep 3212099 = 4818149) B4818149
theorem B2141399 : Blo 2139435 2141399 := bstep (se 1 (by rfl) ⟨1606049, by rfl⟩ : syracuseStep 2141399 = 3212099) B3212099
theorem B5420429 : Blo 2139435 5420429 := bbase (se 3 (by rfl) ⟨1016330, by rfl⟩ : syracuseStep 5420429 = 2032661) (by norm_num)
theorem B3613619 : Blo 2139435 3613619 := bstep (se 1 (by rfl) ⟨2710214, by rfl⟩ : syracuseStep 3613619 = 5420429) B5420429
theorem B2409079 : Blo 2139435 2409079 := bstep (se 1 (by rfl) ⟨1806809, by rfl⟩ : syracuseStep 2409079 = 3613619) B3613619
theorem B3212105 : Blo 2139435 3212105 := bstep (se 2 (by rfl) ⟨1204539, by rfl⟩ : syracuseStep 3212105 = 2409079) B2409079
theorem B2141403 : Blo 2139435 2141403 := bstep (se 1 (by rfl) ⟨1606052, by rfl⟩ : syracuseStep 2141403 = 3212105) B3212105
theorem B3048997 : Blo 2139435 3048997 := bbase (se 4 (by rfl) ⟨285843, by rfl⟩ : syracuseStep 3048997 = 571687) (by norm_num)
theorem B4065329 : Blo 2139435 4065329 := bstep (se 2 (by rfl) ⟨1524498, by rfl⟩ : syracuseStep 4065329 = 3048997) B3048997
theorem B10840877 : Blo 2139435 10840877 := bstep (se 3 (by rfl) ⟨2032664, by rfl⟩ : syracuseStep 10840877 = 4065329) B4065329
theorem B7227251 : Blo 2139435 7227251 := bstep (se 1 (by rfl) ⟨5420438, by rfl⟩ : syracuseStep 7227251 = 10840877) B10840877
theorem B4818167 : Blo 2139435 4818167 := bstep (se 1 (by rfl) ⟨3613625, by rfl⟩ : syracuseStep 4818167 = 7227251) B7227251
theorem B3212111 : Blo 2139435 3212111 := bstep (se 1 (by rfl) ⟨2409083, by rfl⟩ : syracuseStep 3212111 = 4818167) B4818167
theorem B2141407 : Blo 2139435 2141407 := bstep (se 1 (by rfl) ⟨1606055, by rfl⟩ : syracuseStep 2141407 = 3212111) B3212111
theorem B3212117 : Blo 2139435 3212117 := bbase (se 9 (by rfl) ⟨9410, by rfl⟩ : syracuseStep 3212117 = 18821) (by norm_num)
theorem B2141411 : Blo 2139435 2141411 := bstep (se 1 (by rfl) ⟨1606058, by rfl⟩ : syracuseStep 2141411 = 3212117) B3212117
theorem B2170633 : Blo 2139435 2170633 := bbase (se 2 (by rfl) ⟨813987, by rfl⟩ : syracuseStep 2170633 = 1627975) (by norm_num)
theorem B2894177 : Blo 2139435 2894177 := bstep (se 2 (by rfl) ⟨1085316, by rfl⟩ : syracuseStep 2894177 = 2170633) B2170633
theorem B7717805 : Blo 2139435 7717805 := bstep (se 3 (by rfl) ⟨1447088, by rfl⟩ : syracuseStep 7717805 = 2894177) B2894177
theorem B5145203 : Blo 2139435 5145203 := bstep (se 1 (by rfl) ⟨3858902, by rfl⟩ : syracuseStep 5145203 = 7717805) B7717805
theorem B3430135 : Blo 2139435 3430135 := bstep (se 1 (by rfl) ⟨2572601, by rfl⟩ : syracuseStep 3430135 = 5145203) B5145203
theorem B4573513 : Blo 2139435 4573513 := bstep (se 2 (by rfl) ⟨1715067, by rfl⟩ : syracuseStep 4573513 = 3430135) B3430135
theorem B6098017 : Blo 2139435 6098017 := bstep (se 2 (by rfl) ⟨2286756, by rfl⟩ : syracuseStep 6098017 = 4573513) B4573513
theorem B8130689 : Blo 2139435 8130689 := bstep (se 2 (by rfl) ⟨3049008, by rfl⟩ : syracuseStep 8130689 = 6098017) B6098017
theorem B5420459 : Blo 2139435 5420459 := bstep (se 1 (by rfl) ⟨4065344, by rfl⟩ : syracuseStep 5420459 = 8130689) B8130689
theorem B3613639 : Blo 2139435 3613639 := bstep (se 1 (by rfl) ⟨2710229, by rfl⟩ : syracuseStep 3613639 = 5420459) B5420459
theorem B4818185 : Blo 2139435 4818185 := bstep (se 2 (by rfl) ⟨1806819, by rfl⟩ : syracuseStep 4818185 = 3613639) B3613639
theorem B3212123 : Blo 2139435 3212123 := bstep (se 1 (by rfl) ⟨2409092, by rfl⟩ : syracuseStep 3212123 = 4818185) B4818185
theorem B2141415 : Blo 2139435 2141415 := bstep (se 1 (by rfl) ⟨1606061, by rfl⟩ : syracuseStep 2141415 = 3212123) B3212123
theorem B2409097 : Blo 2139435 2409097 := bbase (se 2 (by rfl) ⟨903411, by rfl⟩ : syracuseStep 2409097 = 1806823) (by norm_num)
theorem B3212129 : Blo 2139435 3212129 := bstep (se 2 (by rfl) ⟨1204548, by rfl⟩ : syracuseStep 3212129 = 2409097) B2409097
theorem B2141419 : Blo 2139435 2141419 := bstep (se 1 (by rfl) ⟨1606064, by rfl⟩ : syracuseStep 2141419 = 3212129) B3212129
theorem B3964933 : Blo 2139435 3964933 := bbase (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) (by norm_num)
theorem B21146309 : Blo 2139435 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B14097539 : Blo 2139435 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B9398359 : Blo 2139435 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B12531145 : Blo 2139435 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B16708193 : Blo 2139435 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B11138795 : Blo 2139435 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B7425863 : Blo 2139435 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B4950575 : Blo 2139435 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B3300383 : Blo 2139435 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B2200255 : Blo 2139435 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B46938773 : Blo 2139435 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B31292515 : Blo 2139435 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B41723353 : Blo 2139435 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B55631137 : Blo 2139435 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B74174849 : Blo 2139435 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B49449899 : Blo 2139435 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B32966599 : Blo 2139435 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B43955465 : Blo 2139435 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B117214573 : Blo 2139435 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B156286097 : Blo 2139435 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B104190731 : Blo 2139435 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B69460487 : Blo 2139435 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B46306991 : Blo 2139435 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B30871327 : Blo 2139435 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B41161769 : Blo 2139435 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B27441179 : Blo 2139435 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B18294119 : Blo 2139435 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B12196079 : Blo 2139435 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B8130719 : Blo 2139435 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B5420479 : Blo 2139435 5420479 := bstep (se 1 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 5420479 = 8130719) B8130719
theorem B7227305 : Blo 2139435 7227305 := bstep (se 2 (by rfl) ⟨2710239, by rfl⟩ : syracuseStep 7227305 = 5420479) B5420479
theorem B4818203 : Blo 2139435 4818203 := bstep (se 1 (by rfl) ⟨3613652, by rfl⟩ : syracuseStep 4818203 = 7227305) B7227305
theorem B3212135 : Blo 2139435 3212135 := bstep (se 1 (by rfl) ⟨2409101, by rfl⟩ : syracuseStep 3212135 = 4818203) B4818203
theorem B2141423 : Blo 2139435 2141423 := bstep (se 1 (by rfl) ⟨1606067, by rfl⟩ : syracuseStep 2141423 = 3212135) B3212135
theorem B3212141 : Blo 2139435 3212141 := bbase (se 3 (by rfl) ⟨602276, by rfl⟩ : syracuseStep 3212141 = 1204553) (by norm_num)
theorem B2141427 : Blo 2139435 2141427 := bstep (se 1 (by rfl) ⟨1606070, by rfl⟩ : syracuseStep 2141427 = 3212141) B3212141
theorem B4818221 : Blo 2139435 4818221 := bbase (se 3 (by rfl) ⟨903416, by rfl⟩ : syracuseStep 4818221 = 1806833) (by norm_num)
theorem B3212147 : Blo 2139435 3212147 := bstep (se 1 (by rfl) ⟨2409110, by rfl⟩ : syracuseStep 3212147 = 4818221) B4818221
theorem B2141431 : Blo 2139435 2141431 := bstep (se 1 (by rfl) ⟨1606073, by rfl⟩ : syracuseStep 2141431 = 3212147) B3212147
theorem B12362549 : Blo 2139435 12362549 := bbase (se 5 (by rfl) ⟨579494, by rfl⟩ : syracuseStep 12362549 = 1158989) (by norm_num)
theorem B32966797 : Blo 2139435 32966797 := bstep (se 3 (by rfl) ⟨6181274, by rfl⟩ : syracuseStep 32966797 = 12362549) B12362549
theorem B43955729 : Blo 2139435 43955729 := bstep (se 2 (by rfl) ⟨16483398, by rfl⟩ : syracuseStep 43955729 = 32966797) B32966797
theorem B29303819 : Blo 2139435 29303819 := bstep (se 1 (by rfl) ⟨21977864, by rfl⟩ : syracuseStep 29303819 = 43955729) B43955729
theorem B19535879 : Blo 2139435 19535879 := bstep (se 1 (by rfl) ⟨14651909, by rfl⟩ : syracuseStep 19535879 = 29303819) B29303819
theorem B13023919 : Blo 2139435 13023919 := bstep (se 1 (by rfl) ⟨9767939, by rfl⟩ : syracuseStep 13023919 = 19535879) B19535879
theorem B17365225 : Blo 2139435 17365225 := bstep (se 2 (by rfl) ⟨6511959, by rfl⟩ : syracuseStep 17365225 = 13023919) B13023919
theorem B23153633 : Blo 2139435 23153633 := bstep (se 2 (by rfl) ⟨8682612, by rfl⟩ : syracuseStep 23153633 = 17365225) B17365225
theorem B15435755 : Blo 2139435 15435755 := bstep (se 1 (by rfl) ⟨11576816, by rfl⟩ : syracuseStep 15435755 = 23153633) B23153633
theorem B10290503 : Blo 2139435 10290503 := bstep (se 1 (by rfl) ⟨7717877, by rfl⟩ : syracuseStep 10290503 = 15435755) B15435755
theorem B6860335 : Blo 2139435 6860335 := bstep (se 1 (by rfl) ⟨5145251, by rfl⟩ : syracuseStep 6860335 = 10290503) B10290503
theorem B9147113 : Blo 2139435 9147113 := bstep (se 2 (by rfl) ⟨3430167, by rfl⟩ : syracuseStep 9147113 = 6860335) B6860335
theorem B6098075 : Blo 2139435 6098075 := bstep (se 1 (by rfl) ⟨4573556, by rfl⟩ : syracuseStep 6098075 = 9147113) B9147113
theorem B4065383 : Blo 2139435 4065383 := bstep (se 1 (by rfl) ⟨3049037, by rfl⟩ : syracuseStep 4065383 = 6098075) B6098075
theorem B2710255 : Blo 2139435 2710255 := bstep (se 1 (by rfl) ⟨2032691, by rfl⟩ : syracuseStep 2710255 = 4065383) B4065383
theorem B3613673 : Blo 2139435 3613673 := bstep (se 2 (by rfl) ⟨1355127, by rfl⟩ : syracuseStep 3613673 = 2710255) B2710255
theorem B2409115 : Blo 2139435 2409115 := bstep (se 1 (by rfl) ⟨1806836, by rfl⟩ : syracuseStep 2409115 = 3613673) B3613673
theorem B3212153 : Blo 2139435 3212153 := bstep (se 2 (by rfl) ⟨1204557, by rfl⟩ : syracuseStep 3212153 = 2409115) B2409115
theorem B2141435 : Blo 2139435 2141435 := bstep (se 1 (by rfl) ⟨1606076, by rfl⟩ : syracuseStep 2141435 = 3212153) B3212153
theorem C0 (j : ℕ) (h1 : 534858 ≤ j) (h2 : j ≤ 535358) : Blo 2139435 (4 * j + 3) := by
  interval_cases j
  · exact B2139435
  · exact B2139439
  · exact B2139443
  · exact B2139447
  · exact B2139451
  · exact B2139455
  · exact B2139459
  · exact B2139463
  · exact B2139467
  · exact B2139471
  · exact B2139475
  · exact B2139479
  · exact B2139483
  · exact B2139487
  · exact B2139491
  · exact B2139495
  · exact B2139499
  · exact B2139503
  · exact B2139507
  · exact B2139511
  · exact B2139515
  · exact B2139519
  · exact B2139523
  · exact B2139527
  · exact B2139531
  · exact B2139535
  · exact B2139539
  · exact B2139543
  · exact B2139547
  · exact B2139551
  · exact B2139555
  · exact B2139559
  · exact B2139563
  · exact B2139567
  · exact B2139571
  · exact B2139575
  · exact B2139579
  · exact B2139583
  · exact B2139587
  · exact B2139591
  · exact B2139595
  · exact B2139599
  · exact B2139603
  · exact B2139607
  · exact B2139611
  · exact B2139615
  · exact B2139619
  · exact B2139623
  · exact B2139627
  · exact B2139631
  · exact B2139635
  · exact B2139639
  · exact B2139643
  · exact B2139647
  · exact B2139651
  · exact B2139655
  · exact B2139659
  · exact B2139663
  · exact B2139667
  · exact B2139671
  · exact B2139675
  · exact B2139679
  · exact B2139683
  · exact B2139687
  · exact B2139691
  · exact B2139695
  · exact B2139699
  · exact B2139703
  · exact B2139707
  · exact B2139711
  · exact B2139715
  · exact B2139719
  · exact B2139723
  · exact B2139727
  · exact B2139731
  · exact B2139735
  · exact B2139739
  · exact B2139743
  · exact B2139747
  · exact B2139751
  · exact B2139755
  · exact B2139759
  · exact B2139763
  · exact B2139767
  · exact B2139771
  · exact B2139775
  · exact B2139779
  · exact B2139783
  · exact B2139787
  · exact B2139791
  · exact B2139795
  · exact B2139799
  · exact B2139803
  · exact B2139807
  · exact B2139811
  · exact B2139815
  · exact B2139819
  · exact B2139823
  · exact B2139827
  · exact B2139831
  · exact B2139835
  · exact B2139839
  · exact B2139843
  · exact B2139847
  · exact B2139851
  · exact B2139855
  · exact B2139859
  · exact B2139863
  · exact B2139867
  · exact B2139871
  · exact B2139875
  · exact B2139879
  · exact B2139883
  · exact B2139887
  · exact B2139891
  · exact B2139895
  · exact B2139899
  · exact B2139903
  · exact B2139907
  · exact B2139911
  · exact B2139915
  · exact B2139919
  · exact B2139923
  · exact B2139927
  · exact B2139931
  · exact B2139935
  · exact B2139939
  · exact B2139943
  · exact B2139947
  · exact B2139951
  · exact B2139955
  · exact B2139959
  · exact B2139963
  · exact B2139967
  · exact B2139971
  · exact B2139975
  · exact B2139979
  · exact B2139983
  · exact B2139987
  · exact B2139991
  · exact B2139995
  · exact B2139999
  · exact B2140003
  · exact B2140007
  · exact B2140011
  · exact B2140015
  · exact B2140019
  · exact B2140023
  · exact B2140027
  · exact B2140031
  · exact B2140035
  · exact B2140039
  · exact B2140043
  · exact B2140047
  · exact B2140051
  · exact B2140055
  · exact B2140059
  · exact B2140063
  · exact B2140067
  · exact B2140071
  · exact B2140075
  · exact B2140079
  · exact B2140083
  · exact B2140087
  · exact B2140091
  · exact B2140095
  · exact B2140099
  · exact B2140103
  · exact B2140107
  · exact B2140111
  · exact B2140115
  · exact B2140119
  · exact B2140123
  · exact B2140127
  · exact B2140131
  · exact B2140135
  · exact B2140139
  · exact B2140143
  · exact B2140147
  · exact B2140151
  · exact B2140155
  · exact B2140159
  · exact B2140163
  · exact B2140167
  · exact B2140171
  · exact B2140175
  · exact B2140179
  · exact B2140183
  · exact B2140187
  · exact B2140191
  · exact B2140195
  · exact B2140199
  · exact B2140203
  · exact B2140207
  · exact B2140211
  · exact B2140215
  · exact B2140219
  · exact B2140223
  · exact B2140227
  · exact B2140231
  · exact B2140235
  · exact B2140239
  · exact B2140243
  · exact B2140247
  · exact B2140251
  · exact B2140255
  · exact B2140259
  · exact B2140263
  · exact B2140267
  · exact B2140271
  · exact B2140275
  · exact B2140279
  · exact B2140283
  · exact B2140287
  · exact B2140291
  · exact B2140295
  · exact B2140299
  · exact B2140303
  · exact B2140307
  · exact B2140311
  · exact B2140315
  · exact B2140319
  · exact B2140323
  · exact B2140327
  · exact B2140331
  · exact B2140335
  · exact B2140339
  · exact B2140343
  · exact B2140347
  · exact B2140351
  · exact B2140355
  · exact B2140359
  · exact B2140363
  · exact B2140367
  · exact B2140371
  · exact B2140375
  · exact B2140379
  · exact B2140383
  · exact B2140387
  · exact B2140391
  · exact B2140395
  · exact B2140399
  · exact B2140403
  · exact B2140407
  · exact B2140411
  · exact B2140415
  · exact B2140419
  · exact B2140423
  · exact B2140427
  · exact B2140431
  · exact B2140435
  · exact B2140439
  · exact B2140443
  · exact B2140447
  · exact B2140451
  · exact B2140455
  · exact B2140459
  · exact B2140463
  · exact B2140467
  · exact B2140471
  · exact B2140475
  · exact B2140479
  · exact B2140483
  · exact B2140487
  · exact B2140491
  · exact B2140495
  · exact B2140499
  · exact B2140503
  · exact B2140507
  · exact B2140511
  · exact B2140515
  · exact B2140519
  · exact B2140523
  · exact B2140527
  · exact B2140531
  · exact B2140535
  · exact B2140539
  · exact B2140543
  · exact B2140547
  · exact B2140551
  · exact B2140555
  · exact B2140559
  · exact B2140563
  · exact B2140567
  · exact B2140571
  · exact B2140575
  · exact B2140579
  · exact B2140583
  · exact B2140587
  · exact B2140591
  · exact B2140595
  · exact B2140599
  · exact B2140603
  · exact B2140607
  · exact B2140611
  · exact B2140615
  · exact B2140619
  · exact B2140623
  · exact B2140627
  · exact B2140631
  · exact B2140635
  · exact B2140639
  · exact B2140643
  · exact B2140647
  · exact B2140651
  · exact B2140655
  · exact B2140659
  · exact B2140663
  · exact B2140667
  · exact B2140671
  · exact B2140675
  · exact B2140679
  · exact B2140683
  · exact B2140687
  · exact B2140691
  · exact B2140695
  · exact B2140699
  · exact B2140703
  · exact B2140707
  · exact B2140711
  · exact B2140715
  · exact B2140719
  · exact B2140723
  · exact B2140727
  · exact B2140731
  · exact B2140735
  · exact B2140739
  · exact B2140743
  · exact B2140747
  · exact B2140751
  · exact B2140755
  · exact B2140759
  · exact B2140763
  · exact B2140767
  · exact B2140771
  · exact B2140775
  · exact B2140779
  · exact B2140783
  · exact B2140787
  · exact B2140791
  · exact B2140795
  · exact B2140799
  · exact B2140803
  · exact B2140807
  · exact B2140811
  · exact B2140815
  · exact B2140819
  · exact B2140823
  · exact B2140827
  · exact B2140831
  · exact B2140835
  · exact B2140839
  · exact B2140843
  · exact B2140847
  · exact B2140851
  · exact B2140855
  · exact B2140859
  · exact B2140863
  · exact B2140867
  · exact B2140871
  · exact B2140875
  · exact B2140879
  · exact B2140883
  · exact B2140887
  · exact B2140891
  · exact B2140895
  · exact B2140899
  · exact B2140903
  · exact B2140907
  · exact B2140911
  · exact B2140915
  · exact B2140919
  · exact B2140923
  · exact B2140927
  · exact B2140931
  · exact B2140935
  · exact B2140939
  · exact B2140943
  · exact B2140947
  · exact B2140951
  · exact B2140955
  · exact B2140959
  · exact B2140963
  · exact B2140967
  · exact B2140971
  · exact B2140975
  · exact B2140979
  · exact B2140983
  · exact B2140987
  · exact B2140991
  · exact B2140995
  · exact B2140999
  · exact B2141003
  · exact B2141007
  · exact B2141011
  · exact B2141015
  · exact B2141019
  · exact B2141023
  · exact B2141027
  · exact B2141031
  · exact B2141035
  · exact B2141039
  · exact B2141043
  · exact B2141047
  · exact B2141051
  · exact B2141055
  · exact B2141059
  · exact B2141063
  · exact B2141067
  · exact B2141071
  · exact B2141075
  · exact B2141079
  · exact B2141083
  · exact B2141087
  · exact B2141091
  · exact B2141095
  · exact B2141099
  · exact B2141103
  · exact B2141107
  · exact B2141111
  · exact B2141115
  · exact B2141119
  · exact B2141123
  · exact B2141127
  · exact B2141131
  · exact B2141135
  · exact B2141139
  · exact B2141143
  · exact B2141147
  · exact B2141151
  · exact B2141155
  · exact B2141159
  · exact B2141163
  · exact B2141167
  · exact B2141171
  · exact B2141175
  · exact B2141179
  · exact B2141183
  · exact B2141187
  · exact B2141191
  · exact B2141195
  · exact B2141199
  · exact B2141203
  · exact B2141207
  · exact B2141211
  · exact B2141215
  · exact B2141219
  · exact B2141223
  · exact B2141227
  · exact B2141231
  · exact B2141235
  · exact B2141239
  · exact B2141243
  · exact B2141247
  · exact B2141251
  · exact B2141255
  · exact B2141259
  · exact B2141263
  · exact B2141267
  · exact B2141271
  · exact B2141275
  · exact B2141279
  · exact B2141283
  · exact B2141287
  · exact B2141291
  · exact B2141295
  · exact B2141299
  · exact B2141303
  · exact B2141307
  · exact B2141311
  · exact B2141315
  · exact B2141319
  · exact B2141323
  · exact B2141327
  · exact B2141331
  · exact B2141335
  · exact B2141339
  · exact B2141343
  · exact B2141347
  · exact B2141351
  · exact B2141355
  · exact B2141359
  · exact B2141363
  · exact B2141367
  · exact B2141371
  · exact B2141375
  · exact B2141379
  · exact B2141383
  · exact B2141387
  · exact B2141391
  · exact B2141395
  · exact B2141399
  · exact B2141403
  · exact B2141407
  · exact B2141411
  · exact B2141415
  · exact B2141419
  · exact B2141423
  · exact B2141427
  · exact B2141431
  · exact B2141435
theorem solution (m : ℕ) (hlo : 2139435 ≤ m) (hhi : m ≤ 2141435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 534858 ≤ j := by omega
    have hj2 : j ≤ 535358 := by omega
    have hb : Blo 2139435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
