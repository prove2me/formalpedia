-- Prove2me | solution 1 for syracuse_descends_range_1883435_1885435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:12:56.310892+00:00
-- url     : https://prove2.me/submissions/a3021eb8-f05b-4ee8-aea5-ecb02fb4e5cc

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

theorem B2118865 : Blo 1883435 2118865 := bbase (se 2 (by rfl) ⟨794574, by rfl⟩ : syracuseStep 2118865 = 1589149) (by norm_num)
theorem B2825153 : Blo 1883435 2825153 := bstep (se 2 (by rfl) ⟨1059432, by rfl⟩ : syracuseStep 2825153 = 2118865) B2118865
theorem B1883435 : Blo 1883435 1883435 := bstep (se 1 (by rfl) ⟨1412576, by rfl⟩ : syracuseStep 1883435 = 2825153) B2825153
theorem B13576085 : Blo 1883435 13576085 := bbase (se 6 (by rfl) ⟨318189, by rfl⟩ : syracuseStep 13576085 = 636379) (by norm_num)
theorem B9050723 : Blo 1883435 9050723 := bstep (se 1 (by rfl) ⟨6788042, by rfl⟩ : syracuseStep 9050723 = 13576085) B13576085
theorem B6033815 : Blo 1883435 6033815 := bstep (se 1 (by rfl) ⟨4525361, by rfl⟩ : syracuseStep 6033815 = 9050723) B9050723
theorem B4022543 : Blo 1883435 4022543 := bstep (se 1 (by rfl) ⟨3016907, by rfl⟩ : syracuseStep 4022543 = 6033815) B6033815
theorem B2681695 : Blo 1883435 2681695 := bstep (se 1 (by rfl) ⟨2011271, by rfl⟩ : syracuseStep 2681695 = 4022543) B4022543
theorem B3575593 : Blo 1883435 3575593 := bstep (se 2 (by rfl) ⟨1340847, by rfl⟩ : syracuseStep 3575593 = 2681695) B2681695
theorem B4767457 : Blo 1883435 4767457 := bstep (se 2 (by rfl) ⟨1787796, by rfl⟩ : syracuseStep 4767457 = 3575593) B3575593
theorem B6356609 : Blo 1883435 6356609 := bstep (se 2 (by rfl) ⟨2383728, by rfl⟩ : syracuseStep 6356609 = 4767457) B4767457
theorem B4237739 : Blo 1883435 4237739 := bstep (se 1 (by rfl) ⟨3178304, by rfl⟩ : syracuseStep 4237739 = 6356609) B6356609
theorem B2825159 : Blo 1883435 2825159 := bstep (se 1 (by rfl) ⟨2118869, by rfl⟩ : syracuseStep 2825159 = 4237739) B4237739
theorem B1883439 : Blo 1883435 1883439 := bstep (se 1 (by rfl) ⟨1412579, by rfl⟩ : syracuseStep 1883439 = 2825159) B2825159
theorem B2825165 : Blo 1883435 2825165 := bbase (se 3 (by rfl) ⟨529718, by rfl⟩ : syracuseStep 2825165 = 1059437) (by norm_num)
theorem B1883443 : Blo 1883435 1883443 := bstep (se 1 (by rfl) ⟨1412582, by rfl⟩ : syracuseStep 1883443 = 2825165) B2825165
theorem B4237757 : Blo 1883435 4237757 := bbase (se 3 (by rfl) ⟨794579, by rfl⟩ : syracuseStep 4237757 = 1589159) (by norm_num)
theorem B2825171 : Blo 1883435 2825171 := bstep (se 1 (by rfl) ⟨2118878, by rfl⟩ : syracuseStep 2825171 = 4237757) B4237757
theorem B1883447 : Blo 1883435 1883447 := bstep (se 1 (by rfl) ⟨1412585, by rfl⟩ : syracuseStep 1883447 = 2825171) B2825171
theorem B3178325 : Blo 1883435 3178325 := bbase (se 9 (by rfl) ⟨9311, by rfl⟩ : syracuseStep 3178325 = 18623) (by norm_num)
theorem B2118883 : Blo 1883435 2118883 := bstep (se 1 (by rfl) ⟨1589162, by rfl⟩ : syracuseStep 2118883 = 3178325) B3178325
theorem B2825177 : Blo 1883435 2825177 := bstep (se 2 (by rfl) ⟨1059441, by rfl⟩ : syracuseStep 2825177 = 2118883) B2118883
theorem B1883451 : Blo 1883435 1883451 := bstep (se 1 (by rfl) ⟨1412588, by rfl⟩ : syracuseStep 1883451 = 2825177) B2825177
theorem B1909153 : Blo 1883435 1909153 := bbase (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) (by norm_num)
theorem B10182149 : Blo 1883435 10182149 := bstep (se 4 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 10182149 = 1909153) B1909153
theorem B6788099 : Blo 1883435 6788099 := bstep (se 1 (by rfl) ⟨5091074, by rfl⟩ : syracuseStep 6788099 = 10182149) B10182149
theorem B4525399 : Blo 1883435 4525399 := bstep (se 1 (by rfl) ⟨3394049, by rfl⟩ : syracuseStep 4525399 = 6788099) B6788099
theorem B6033865 : Blo 1883435 6033865 := bstep (se 2 (by rfl) ⟨2262699, by rfl⟩ : syracuseStep 6033865 = 4525399) B4525399
theorem B8045153 : Blo 1883435 8045153 := bstep (se 2 (by rfl) ⟨3016932, by rfl⟩ : syracuseStep 8045153 = 6033865) B6033865
theorem B5363435 : Blo 1883435 5363435 := bstep (se 1 (by rfl) ⟨4022576, by rfl⟩ : syracuseStep 5363435 = 8045153) B8045153
theorem B14302493 : Blo 1883435 14302493 := bstep (se 3 (by rfl) ⟨2681717, by rfl⟩ : syracuseStep 14302493 = 5363435) B5363435
theorem B9534995 : Blo 1883435 9534995 := bstep (se 1 (by rfl) ⟨7151246, by rfl⟩ : syracuseStep 9534995 = 14302493) B14302493
theorem B6356663 : Blo 1883435 6356663 := bstep (se 1 (by rfl) ⟨4767497, by rfl⟩ : syracuseStep 6356663 = 9534995) B9534995
theorem B4237775 : Blo 1883435 4237775 := bstep (se 1 (by rfl) ⟨3178331, by rfl⟩ : syracuseStep 4237775 = 6356663) B6356663
theorem B2825183 : Blo 1883435 2825183 := bstep (se 1 (by rfl) ⟨2118887, by rfl⟩ : syracuseStep 2825183 = 4237775) B4237775
theorem B1883455 : Blo 1883435 1883455 := bstep (se 1 (by rfl) ⟨1412591, by rfl⟩ : syracuseStep 1883455 = 2825183) B2825183
theorem B2825189 : Blo 1883435 2825189 := bbase (se 4 (by rfl) ⟨264861, by rfl⟩ : syracuseStep 2825189 = 529723) (by norm_num)
theorem B1883459 : Blo 1883435 1883459 := bstep (se 1 (by rfl) ⟨1412594, by rfl⟩ : syracuseStep 1883459 = 2825189) B2825189
theorem B8045189 : Blo 1883435 8045189 := bbase (se 4 (by rfl) ⟨754236, by rfl⟩ : syracuseStep 8045189 = 1508473) (by norm_num)
theorem B5363459 : Blo 1883435 5363459 := bstep (se 1 (by rfl) ⟨4022594, by rfl⟩ : syracuseStep 5363459 = 8045189) B8045189
theorem B3575639 : Blo 1883435 3575639 := bstep (se 1 (by rfl) ⟨2681729, by rfl⟩ : syracuseStep 3575639 = 5363459) B5363459
theorem B2383759 : Blo 1883435 2383759 := bstep (se 1 (by rfl) ⟨1787819, by rfl⟩ : syracuseStep 2383759 = 3575639) B3575639
theorem B3178345 : Blo 1883435 3178345 := bstep (se 2 (by rfl) ⟨1191879, by rfl⟩ : syracuseStep 3178345 = 2383759) B2383759
theorem B4237793 : Blo 1883435 4237793 := bstep (se 2 (by rfl) ⟨1589172, by rfl⟩ : syracuseStep 4237793 = 3178345) B3178345
theorem B2825195 : Blo 1883435 2825195 := bstep (se 1 (by rfl) ⟨2118896, by rfl⟩ : syracuseStep 2825195 = 4237793) B4237793
theorem B1883463 : Blo 1883435 1883463 := bstep (se 1 (by rfl) ⟨1412597, by rfl⟩ : syracuseStep 1883463 = 2825195) B2825195
theorem B2118901 : Blo 1883435 2118901 := bbase (se 5 (by rfl) ⟨99323, by rfl⟩ : syracuseStep 2118901 = 198647) (by norm_num)
theorem B2825201 : Blo 1883435 2825201 := bstep (se 2 (by rfl) ⟨1059450, by rfl⟩ : syracuseStep 2825201 = 2118901) B2118901
theorem B1883467 : Blo 1883435 1883467 := bstep (se 1 (by rfl) ⟨1412600, by rfl⟩ : syracuseStep 1883467 = 2825201) B2825201
theorem B2383769 : Blo 1883435 2383769 := bbase (se 2 (by rfl) ⟨893913, by rfl⟩ : syracuseStep 2383769 = 1787827) (by norm_num)
theorem B6356717 : Blo 1883435 6356717 := bstep (se 3 (by rfl) ⟨1191884, by rfl⟩ : syracuseStep 6356717 = 2383769) B2383769
theorem B4237811 : Blo 1883435 4237811 := bstep (se 1 (by rfl) ⟨3178358, by rfl⟩ : syracuseStep 4237811 = 6356717) B6356717
theorem B2825207 : Blo 1883435 2825207 := bstep (se 1 (by rfl) ⟨2118905, by rfl⟩ : syracuseStep 2825207 = 4237811) B4237811
theorem B1883471 : Blo 1883435 1883471 := bstep (se 1 (by rfl) ⟨1412603, by rfl⟩ : syracuseStep 1883471 = 2825207) B2825207
theorem B2825213 : Blo 1883435 2825213 := bbase (se 3 (by rfl) ⟨529727, by rfl⟩ : syracuseStep 2825213 = 1059455) (by norm_num)
theorem B1883475 : Blo 1883435 1883475 := bstep (se 1 (by rfl) ⟨1412606, by rfl⟩ : syracuseStep 1883475 = 2825213) B2825213
theorem B4237829 : Blo 1883435 4237829 := bbase (se 4 (by rfl) ⟨397296, by rfl⟩ : syracuseStep 4237829 = 794593) (by norm_num)
theorem B2825219 : Blo 1883435 2825219 := bstep (se 1 (by rfl) ⟨2118914, by rfl⟩ : syracuseStep 2825219 = 4237829) B4237829
theorem B1883479 : Blo 1883435 1883479 := bstep (se 1 (by rfl) ⟨1412609, by rfl⟩ : syracuseStep 1883479 = 2825219) B2825219
theorem B3575677 : Blo 1883435 3575677 := bbase (se 3 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 3575677 = 1340879) (by norm_num)
theorem B4767569 : Blo 1883435 4767569 := bstep (se 2 (by rfl) ⟨1787838, by rfl⟩ : syracuseStep 4767569 = 3575677) B3575677
theorem B3178379 : Blo 1883435 3178379 := bstep (se 1 (by rfl) ⟨2383784, by rfl⟩ : syracuseStep 3178379 = 4767569) B4767569
theorem B2118919 : Blo 1883435 2118919 := bstep (se 1 (by rfl) ⟨1589189, by rfl⟩ : syracuseStep 2118919 = 3178379) B3178379
theorem B2825225 : Blo 1883435 2825225 := bstep (se 2 (by rfl) ⟨1059459, by rfl⟩ : syracuseStep 2825225 = 2118919) B2118919
theorem B1883483 : Blo 1883435 1883483 := bstep (se 1 (by rfl) ⟨1412612, by rfl⟩ : syracuseStep 1883483 = 2825225) B2825225
theorem B9535157 : Blo 1883435 9535157 := bbase (se 5 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 9535157 = 893921) (by norm_num)
theorem B6356771 : Blo 1883435 6356771 := bstep (se 1 (by rfl) ⟨4767578, by rfl⟩ : syracuseStep 6356771 = 9535157) B9535157
theorem B4237847 : Blo 1883435 4237847 := bstep (se 1 (by rfl) ⟨3178385, by rfl⟩ : syracuseStep 4237847 = 6356771) B6356771
theorem B2825231 : Blo 1883435 2825231 := bstep (se 1 (by rfl) ⟨2118923, by rfl⟩ : syracuseStep 2825231 = 4237847) B4237847
theorem B1883487 : Blo 1883435 1883487 := bstep (se 1 (by rfl) ⟨1412615, by rfl⟩ : syracuseStep 1883487 = 2825231) B2825231
theorem B2825237 : Blo 1883435 2825237 := bbase (se 6 (by rfl) ⟨66216, by rfl⟩ : syracuseStep 2825237 = 132433) (by norm_num)
theorem B1883491 : Blo 1883435 1883491 := bstep (se 1 (by rfl) ⟨1412618, by rfl⟩ : syracuseStep 1883491 = 2825237) B2825237
theorem B3221765 : Blo 1883435 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B2147843 : Blo 1883435 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B5727581 : Blo 1883435 5727581 := bstep (se 3 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 5727581 = 2147843) B2147843
theorem B3818387 : Blo 1883435 3818387 := bstep (se 1 (by rfl) ⟨2863790, by rfl⟩ : syracuseStep 3818387 = 5727581) B5727581
theorem B10182365 : Blo 1883435 10182365 := bstep (se 3 (by rfl) ⟨1909193, by rfl⟩ : syracuseStep 10182365 = 3818387) B3818387
theorem B6788243 : Blo 1883435 6788243 := bstep (se 1 (by rfl) ⟨5091182, by rfl⟩ : syracuseStep 6788243 = 10182365) B10182365
theorem B18101981 : Blo 1883435 18101981 := bstep (se 3 (by rfl) ⟨3394121, by rfl⟩ : syracuseStep 18101981 = 6788243) B6788243
theorem B12067987 : Blo 1883435 12067987 := bstep (se 1 (by rfl) ⟨9050990, by rfl⟩ : syracuseStep 12067987 = 18101981) B18101981
theorem B16090649 : Blo 1883435 16090649 := bstep (se 2 (by rfl) ⟨6033993, by rfl⟩ : syracuseStep 16090649 = 12067987) B12067987
theorem B10727099 : Blo 1883435 10727099 := bstep (se 1 (by rfl) ⟨8045324, by rfl⟩ : syracuseStep 10727099 = 16090649) B16090649
theorem B7151399 : Blo 1883435 7151399 := bstep (se 1 (by rfl) ⟨5363549, by rfl⟩ : syracuseStep 7151399 = 10727099) B10727099
theorem B4767599 : Blo 1883435 4767599 := bstep (se 1 (by rfl) ⟨3575699, by rfl⟩ : syracuseStep 4767599 = 7151399) B7151399
theorem B3178399 : Blo 1883435 3178399 := bstep (se 1 (by rfl) ⟨2383799, by rfl⟩ : syracuseStep 3178399 = 4767599) B4767599
theorem B4237865 : Blo 1883435 4237865 := bstep (se 2 (by rfl) ⟨1589199, by rfl⟩ : syracuseStep 4237865 = 3178399) B3178399
theorem B2825243 : Blo 1883435 2825243 := bstep (se 1 (by rfl) ⟨2118932, by rfl⟩ : syracuseStep 2825243 = 4237865) B4237865
theorem B1883495 : Blo 1883435 1883495 := bstep (se 1 (by rfl) ⟨1412621, by rfl⟩ : syracuseStep 1883495 = 2825243) B2825243
theorem B2118937 : Blo 1883435 2118937 := bbase (se 2 (by rfl) ⟨794601, by rfl⟩ : syracuseStep 2118937 = 1589203) (by norm_num)
theorem B2825249 : Blo 1883435 2825249 := bstep (se 2 (by rfl) ⟨1059468, by rfl⟩ : syracuseStep 2825249 = 2118937) B2118937
theorem B1883499 : Blo 1883435 1883499 := bstep (se 1 (by rfl) ⟨1412624, by rfl⟩ : syracuseStep 1883499 = 2825249) B2825249
theorem B7151429 : Blo 1883435 7151429 := bbase (se 4 (by rfl) ⟨670446, by rfl⟩ : syracuseStep 7151429 = 1340893) (by norm_num)
theorem B4767619 : Blo 1883435 4767619 := bstep (se 1 (by rfl) ⟨3575714, by rfl⟩ : syracuseStep 4767619 = 7151429) B7151429
theorem B6356825 : Blo 1883435 6356825 := bstep (se 2 (by rfl) ⟨2383809, by rfl⟩ : syracuseStep 6356825 = 4767619) B4767619
theorem B4237883 : Blo 1883435 4237883 := bstep (se 1 (by rfl) ⟨3178412, by rfl⟩ : syracuseStep 4237883 = 6356825) B6356825
theorem B2825255 : Blo 1883435 2825255 := bstep (se 1 (by rfl) ⟨2118941, by rfl⟩ : syracuseStep 2825255 = 4237883) B4237883
theorem B1883503 : Blo 1883435 1883503 := bstep (se 1 (by rfl) ⟨1412627, by rfl⟩ : syracuseStep 1883503 = 2825255) B2825255
theorem B2825261 : Blo 1883435 2825261 := bbase (se 3 (by rfl) ⟨529736, by rfl⟩ : syracuseStep 2825261 = 1059473) (by norm_num)
theorem B1883507 : Blo 1883435 1883507 := bstep (se 1 (by rfl) ⟨1412630, by rfl⟩ : syracuseStep 1883507 = 2825261) B2825261
theorem B4237901 : Blo 1883435 4237901 := bbase (se 3 (by rfl) ⟨794606, by rfl⟩ : syracuseStep 4237901 = 1589213) (by norm_num)
theorem B2825267 : Blo 1883435 2825267 := bstep (se 1 (by rfl) ⟨2118950, by rfl⟩ : syracuseStep 2825267 = 4237901) B4237901
theorem B1883511 : Blo 1883435 1883511 := bstep (se 1 (by rfl) ⟨1412633, by rfl⟩ : syracuseStep 1883511 = 2825267) B2825267
theorem B2383825 : Blo 1883435 2383825 := bbase (se 2 (by rfl) ⟨893934, by rfl⟩ : syracuseStep 2383825 = 1787869) (by norm_num)
theorem B3178433 : Blo 1883435 3178433 := bstep (se 2 (by rfl) ⟨1191912, by rfl⟩ : syracuseStep 3178433 = 2383825) B2383825
theorem B2118955 : Blo 1883435 2118955 := bstep (se 1 (by rfl) ⟨1589216, by rfl⟩ : syracuseStep 2118955 = 3178433) B3178433
theorem B2825273 : Blo 1883435 2825273 := bstep (se 2 (by rfl) ⟨1059477, by rfl⟩ : syracuseStep 2825273 = 2118955) B2118955
theorem B1883515 : Blo 1883435 1883515 := bstep (se 1 (by rfl) ⟨1412636, by rfl⟩ : syracuseStep 1883515 = 2825273) B2825273
theorem B3394165 : Blo 1883435 3394165 := bbase (se 5 (by rfl) ⟨159101, by rfl⟩ : syracuseStep 3394165 = 318203) (by norm_num)
theorem B4525553 : Blo 1883435 4525553 := bstep (se 2 (by rfl) ⟨1697082, by rfl⟩ : syracuseStep 4525553 = 3394165) B3394165
theorem B3017035 : Blo 1883435 3017035 := bstep (se 1 (by rfl) ⟨2262776, by rfl⟩ : syracuseStep 3017035 = 4525553) B4525553
theorem B4022713 : Blo 1883435 4022713 := bstep (se 2 (by rfl) ⟨1508517, by rfl⟩ : syracuseStep 4022713 = 3017035) B3017035
theorem B21454469 : Blo 1883435 21454469 := bstep (se 4 (by rfl) ⟨2011356, by rfl⟩ : syracuseStep 21454469 = 4022713) B4022713
theorem B14302979 : Blo 1883435 14302979 := bstep (se 1 (by rfl) ⟨10727234, by rfl⟩ : syracuseStep 14302979 = 21454469) B21454469
theorem B9535319 : Blo 1883435 9535319 := bstep (se 1 (by rfl) ⟨7151489, by rfl⟩ : syracuseStep 9535319 = 14302979) B14302979
theorem B6356879 : Blo 1883435 6356879 := bstep (se 1 (by rfl) ⟨4767659, by rfl⟩ : syracuseStep 6356879 = 9535319) B9535319
theorem B4237919 : Blo 1883435 4237919 := bstep (se 1 (by rfl) ⟨3178439, by rfl⟩ : syracuseStep 4237919 = 6356879) B6356879
theorem B2825279 : Blo 1883435 2825279 := bstep (se 1 (by rfl) ⟨2118959, by rfl⟩ : syracuseStep 2825279 = 4237919) B4237919
theorem B1883519 : Blo 1883435 1883519 := bstep (se 1 (by rfl) ⟨1412639, by rfl⟩ : syracuseStep 1883519 = 2825279) B2825279
theorem B2825285 : Blo 1883435 2825285 := bbase (se 4 (by rfl) ⟨264870, by rfl⟩ : syracuseStep 2825285 = 529741) (by norm_num)
theorem B1883523 : Blo 1883435 1883523 := bstep (se 1 (by rfl) ⟨1412642, by rfl⟩ : syracuseStep 1883523 = 2825285) B2825285
theorem B3178453 : Blo 1883435 3178453 := bbase (se 7 (by rfl) ⟨37247, by rfl⟩ : syracuseStep 3178453 = 74495) (by norm_num)
theorem B4237937 : Blo 1883435 4237937 := bstep (se 2 (by rfl) ⟨1589226, by rfl⟩ : syracuseStep 4237937 = 3178453) B3178453
theorem B2825291 : Blo 1883435 2825291 := bstep (se 1 (by rfl) ⟨2118968, by rfl⟩ : syracuseStep 2825291 = 4237937) B4237937
theorem B1883527 : Blo 1883435 1883527 := bstep (se 1 (by rfl) ⟨1412645, by rfl⟩ : syracuseStep 1883527 = 2825291) B2825291
theorem B2118973 : Blo 1883435 2118973 := bbase (se 3 (by rfl) ⟨397307, by rfl⟩ : syracuseStep 2118973 = 794615) (by norm_num)
theorem B2825297 : Blo 1883435 2825297 := bstep (se 2 (by rfl) ⟨1059486, by rfl⟩ : syracuseStep 2825297 = 2118973) B2118973
theorem B1883531 : Blo 1883435 1883531 := bstep (se 1 (by rfl) ⟨1412648, by rfl⟩ : syracuseStep 1883531 = 2825297) B2825297
theorem B6356933 : Blo 1883435 6356933 := bbase (se 4 (by rfl) ⟨595962, by rfl⟩ : syracuseStep 6356933 = 1191925) (by norm_num)
theorem B4237955 : Blo 1883435 4237955 := bstep (se 1 (by rfl) ⟨3178466, by rfl⟩ : syracuseStep 4237955 = 6356933) B6356933
theorem B2825303 : Blo 1883435 2825303 := bstep (se 1 (by rfl) ⟨2118977, by rfl⟩ : syracuseStep 2825303 = 4237955) B4237955
theorem B1883535 : Blo 1883435 1883535 := bstep (se 1 (by rfl) ⟨1412651, by rfl⟩ : syracuseStep 1883535 = 2825303) B2825303
theorem B2825309 : Blo 1883435 2825309 := bbase (se 3 (by rfl) ⟨529745, by rfl⟩ : syracuseStep 2825309 = 1059491) (by norm_num)
theorem B1883539 : Blo 1883435 1883539 := bstep (se 1 (by rfl) ⟨1412654, by rfl⟩ : syracuseStep 1883539 = 2825309) B2825309
theorem B4237973 : Blo 1883435 4237973 := bbase (se 6 (by rfl) ⟨99327, by rfl⟩ : syracuseStep 4237973 = 198655) (by norm_num)
theorem B2825315 : Blo 1883435 2825315 := bstep (se 1 (by rfl) ⟨2118986, by rfl⟩ : syracuseStep 2825315 = 4237973) B4237973
theorem B1883543 : Blo 1883435 1883543 := bstep (se 1 (by rfl) ⟨1412657, by rfl⟩ : syracuseStep 1883543 = 2825315) B2825315
theorem B3265813 : Blo 1883435 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B4354417 : Blo 1883435 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B23223557 : Blo 1883435 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B61929485 : Blo 1883435 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B41286323 : Blo 1883435 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B27524215 : Blo 1883435 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B146795813 : Blo 1883435 146795813 := bstep (se 4 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 146795813 = 27524215) B27524215
theorem B97863875 : Blo 1883435 97863875 := bstep (se 1 (by rfl) ⟨73397906, by rfl⟩ : syracuseStep 97863875 = 146795813) B146795813
theorem B65242583 : Blo 1883435 65242583 := bstep (se 1 (by rfl) ⟨48931937, by rfl⟩ : syracuseStep 65242583 = 97863875) B97863875
theorem B43495055 : Blo 1883435 43495055 := bstep (se 1 (by rfl) ⟨32621291, by rfl⟩ : syracuseStep 43495055 = 65242583) B65242583
theorem B28996703 : Blo 1883435 28996703 := bstep (se 1 (by rfl) ⟨21747527, by rfl⟩ : syracuseStep 28996703 = 43495055) B43495055
theorem B19331135 : Blo 1883435 19331135 := bstep (se 1 (by rfl) ⟨14498351, by rfl⟩ : syracuseStep 19331135 = 28996703) B28996703
theorem B12887423 : Blo 1883435 12887423 := bstep (se 1 (by rfl) ⟨9665567, by rfl⟩ : syracuseStep 12887423 = 19331135) B19331135
theorem B8591615 : Blo 1883435 8591615 := bstep (se 1 (by rfl) ⟨6443711, by rfl⟩ : syracuseStep 8591615 = 12887423) B12887423
theorem B5727743 : Blo 1883435 5727743 := bstep (se 1 (by rfl) ⟨4295807, by rfl⟩ : syracuseStep 5727743 = 8591615) B8591615
theorem B3818495 : Blo 1883435 3818495 := bstep (se 1 (by rfl) ⟨2863871, by rfl⟩ : syracuseStep 3818495 = 5727743) B5727743
theorem B2545663 : Blo 1883435 2545663 := bstep (se 1 (by rfl) ⟨1909247, by rfl⟩ : syracuseStep 2545663 = 3818495) B3818495
theorem B3394217 : Blo 1883435 3394217 := bstep (se 2 (by rfl) ⟨1272831, by rfl⟩ : syracuseStep 3394217 = 2545663) B2545663
theorem B2262811 : Blo 1883435 2262811 := bstep (se 1 (by rfl) ⟨1697108, by rfl⟩ : syracuseStep 2262811 = 3394217) B3394217
theorem B3017081 : Blo 1883435 3017081 := bstep (se 2 (by rfl) ⟨1131405, by rfl⟩ : syracuseStep 3017081 = 2262811) B2262811
theorem B2011387 : Blo 1883435 2011387 := bstep (se 1 (by rfl) ⟨1508540, by rfl⟩ : syracuseStep 2011387 = 3017081) B3017081
theorem B2681849 : Blo 1883435 2681849 := bstep (se 2 (by rfl) ⟨1005693, by rfl⟩ : syracuseStep 2681849 = 2011387) B2011387
theorem B7151597 : Blo 1883435 7151597 := bstep (se 3 (by rfl) ⟨1340924, by rfl⟩ : syracuseStep 7151597 = 2681849) B2681849
theorem B4767731 : Blo 1883435 4767731 := bstep (se 1 (by rfl) ⟨3575798, by rfl⟩ : syracuseStep 4767731 = 7151597) B7151597
theorem B3178487 : Blo 1883435 3178487 := bstep (se 1 (by rfl) ⟨2383865, by rfl⟩ : syracuseStep 3178487 = 4767731) B4767731
theorem B2118991 : Blo 1883435 2118991 := bstep (se 1 (by rfl) ⟨1589243, by rfl⟩ : syracuseStep 2118991 = 3178487) B3178487
theorem B2825321 : Blo 1883435 2825321 := bstep (se 2 (by rfl) ⟨1059495, by rfl⟩ : syracuseStep 2825321 = 2118991) B2118991
theorem B1883547 : Blo 1883435 1883547 := bstep (se 1 (by rfl) ⟨1412660, by rfl⟩ : syracuseStep 1883547 = 2825321) B2825321
theorem B4295813 : Blo 1883435 4295813 := bbase (se 4 (by rfl) ⟨402732, by rfl⟩ : syracuseStep 4295813 = 805465) (by norm_num)
theorem B11455501 : Blo 1883435 11455501 := bstep (se 3 (by rfl) ⟨2147906, by rfl⟩ : syracuseStep 11455501 = 4295813) B4295813
theorem B15274001 : Blo 1883435 15274001 := bstep (se 2 (by rfl) ⟨5727750, by rfl⟩ : syracuseStep 15274001 = 11455501) B11455501
theorem B10182667 : Blo 1883435 10182667 := bstep (se 1 (by rfl) ⟨7637000, by rfl⟩ : syracuseStep 10182667 = 15274001) B15274001
theorem B13576889 : Blo 1883435 13576889 := bstep (se 2 (by rfl) ⟨5091333, by rfl⟩ : syracuseStep 13576889 = 10182667) B10182667
theorem B9051259 : Blo 1883435 9051259 := bstep (se 1 (by rfl) ⟨6788444, by rfl⟩ : syracuseStep 9051259 = 13576889) B13576889
theorem B12068345 : Blo 1883435 12068345 := bstep (se 2 (by rfl) ⟨4525629, by rfl⟩ : syracuseStep 12068345 = 9051259) B9051259
theorem B8045563 : Blo 1883435 8045563 := bstep (se 1 (by rfl) ⟨6034172, by rfl⟩ : syracuseStep 8045563 = 12068345) B12068345
theorem B10727417 : Blo 1883435 10727417 := bstep (se 2 (by rfl) ⟨4022781, by rfl⟩ : syracuseStep 10727417 = 8045563) B8045563
theorem B7151611 : Blo 1883435 7151611 := bstep (se 1 (by rfl) ⟨5363708, by rfl⟩ : syracuseStep 7151611 = 10727417) B10727417
theorem B9535481 : Blo 1883435 9535481 := bstep (se 2 (by rfl) ⟨3575805, by rfl⟩ : syracuseStep 9535481 = 7151611) B7151611
theorem B6356987 : Blo 1883435 6356987 := bstep (se 1 (by rfl) ⟨4767740, by rfl⟩ : syracuseStep 6356987 = 9535481) B9535481
theorem B4237991 : Blo 1883435 4237991 := bstep (se 1 (by rfl) ⟨3178493, by rfl⟩ : syracuseStep 4237991 = 6356987) B6356987
theorem B2825327 : Blo 1883435 2825327 := bstep (se 1 (by rfl) ⟨2118995, by rfl⟩ : syracuseStep 2825327 = 4237991) B4237991
theorem B1883551 : Blo 1883435 1883551 := bstep (se 1 (by rfl) ⟨1412663, by rfl⟩ : syracuseStep 1883551 = 2825327) B2825327
theorem B2825333 : Blo 1883435 2825333 := bbase (se 5 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 2825333 = 264875) (by norm_num)
theorem B1883555 : Blo 1883435 1883555 := bstep (se 1 (by rfl) ⟨1412666, by rfl⟩ : syracuseStep 1883555 = 2825333) B2825333
theorem B3575821 : Blo 1883435 3575821 := bbase (se 3 (by rfl) ⟨670466, by rfl⟩ : syracuseStep 3575821 = 1340933) (by norm_num)
theorem B4767761 : Blo 1883435 4767761 := bstep (se 2 (by rfl) ⟨1787910, by rfl⟩ : syracuseStep 4767761 = 3575821) B3575821
theorem B3178507 : Blo 1883435 3178507 := bstep (se 1 (by rfl) ⟨2383880, by rfl⟩ : syracuseStep 3178507 = 4767761) B4767761
theorem B4238009 : Blo 1883435 4238009 := bstep (se 2 (by rfl) ⟨1589253, by rfl⟩ : syracuseStep 4238009 = 3178507) B3178507
theorem B2825339 : Blo 1883435 2825339 := bstep (se 1 (by rfl) ⟨2119004, by rfl⟩ : syracuseStep 2825339 = 4238009) B4238009
theorem B1883559 : Blo 1883435 1883559 := bstep (se 1 (by rfl) ⟨1412669, by rfl⟩ : syracuseStep 1883559 = 2825339) B2825339
theorem B2119009 : Blo 1883435 2119009 := bbase (se 2 (by rfl) ⟨794628, by rfl⟩ : syracuseStep 2119009 = 1589257) (by norm_num)
theorem B2825345 : Blo 1883435 2825345 := bstep (se 2 (by rfl) ⟨1059504, by rfl⟩ : syracuseStep 2825345 = 2119009) B2119009
theorem B1883563 : Blo 1883435 1883563 := bstep (se 1 (by rfl) ⟨1412672, by rfl⟩ : syracuseStep 1883563 = 2825345) B2825345
theorem B4767781 : Blo 1883435 4767781 := bbase (se 4 (by rfl) ⟨446979, by rfl⟩ : syracuseStep 4767781 = 893959) (by norm_num)
theorem B6357041 : Blo 1883435 6357041 := bstep (se 2 (by rfl) ⟨2383890, by rfl⟩ : syracuseStep 6357041 = 4767781) B4767781
theorem B4238027 : Blo 1883435 4238027 := bstep (se 1 (by rfl) ⟨3178520, by rfl⟩ : syracuseStep 4238027 = 6357041) B6357041
theorem B2825351 : Blo 1883435 2825351 := bstep (se 1 (by rfl) ⟨2119013, by rfl⟩ : syracuseStep 2825351 = 4238027) B4238027
theorem B1883567 : Blo 1883435 1883567 := bstep (se 1 (by rfl) ⟨1412675, by rfl⟩ : syracuseStep 1883567 = 2825351) B2825351
theorem B2825357 : Blo 1883435 2825357 := bbase (se 3 (by rfl) ⟨529754, by rfl⟩ : syracuseStep 2825357 = 1059509) (by norm_num)
theorem B1883571 : Blo 1883435 1883571 := bstep (se 1 (by rfl) ⟨1412678, by rfl⟩ : syracuseStep 1883571 = 2825357) B2825357
theorem B4238045 : Blo 1883435 4238045 := bbase (se 3 (by rfl) ⟨794633, by rfl⟩ : syracuseStep 4238045 = 1589267) (by norm_num)
theorem B2825363 : Blo 1883435 2825363 := bstep (se 1 (by rfl) ⟨2119022, by rfl⟩ : syracuseStep 2825363 = 4238045) B4238045
theorem B1883575 : Blo 1883435 1883575 := bstep (se 1 (by rfl) ⟨1412681, by rfl⟩ : syracuseStep 1883575 = 2825363) B2825363
theorem B3178541 : Blo 1883435 3178541 := bbase (se 3 (by rfl) ⟨595976, by rfl⟩ : syracuseStep 3178541 = 1191953) (by norm_num)
theorem B2119027 : Blo 1883435 2119027 := bstep (se 1 (by rfl) ⟨1589270, by rfl⟩ : syracuseStep 2119027 = 3178541) B3178541
theorem B2825369 : Blo 1883435 2825369 := bstep (se 2 (by rfl) ⟨1059513, by rfl⟩ : syracuseStep 2825369 = 2119027) B2119027
theorem B1883579 : Blo 1883435 1883579 := bstep (se 1 (by rfl) ⟨1412684, by rfl⟩ : syracuseStep 1883579 = 2825369) B2825369
theorem B7846949 : Blo 1883435 7846949 := bbase (se 4 (by rfl) ⟨735651, by rfl⟩ : syracuseStep 7846949 = 1471303) (by norm_num)
theorem B5231299 : Blo 1883435 5231299 := bstep (se 1 (by rfl) ⟨3923474, by rfl⟩ : syracuseStep 5231299 = 7846949) B7846949
theorem B6975065 : Blo 1883435 6975065 := bstep (se 2 (by rfl) ⟨2615649, by rfl⟩ : syracuseStep 6975065 = 5231299) B5231299
theorem B4650043 : Blo 1883435 4650043 := bstep (se 1 (by rfl) ⟨3487532, by rfl⟩ : syracuseStep 4650043 = 6975065) B6975065
theorem B6200057 : Blo 1883435 6200057 := bstep (se 2 (by rfl) ⟨2325021, by rfl⟩ : syracuseStep 6200057 = 4650043) B4650043
theorem B4133371 : Blo 1883435 4133371 := bstep (se 1 (by rfl) ⟨3100028, by rfl⟩ : syracuseStep 4133371 = 6200057) B6200057
theorem B5511161 : Blo 1883435 5511161 := bstep (se 2 (by rfl) ⟨2066685, by rfl⟩ : syracuseStep 5511161 = 4133371) B4133371
theorem B3674107 : Blo 1883435 3674107 := bstep (se 1 (by rfl) ⟨2755580, by rfl⟩ : syracuseStep 3674107 = 5511161) B5511161
theorem B4898809 : Blo 1883435 4898809 := bstep (se 2 (by rfl) ⟨1837053, by rfl⟩ : syracuseStep 4898809 = 3674107) B3674107
theorem B26126981 : Blo 1883435 26126981 := bstep (se 4 (by rfl) ⟨2449404, by rfl⟩ : syracuseStep 26126981 = 4898809) B4898809
theorem B17417987 : Blo 1883435 17417987 := bstep (se 1 (by rfl) ⟨13063490, by rfl⟩ : syracuseStep 17417987 = 26126981) B26126981
theorem B11611991 : Blo 1883435 11611991 := bstep (se 1 (by rfl) ⟨8708993, by rfl⟩ : syracuseStep 11611991 = 17417987) B17417987
theorem B7741327 : Blo 1883435 7741327 := bstep (se 1 (by rfl) ⟨5805995, by rfl⟩ : syracuseStep 7741327 = 11611991) B11611991
theorem B10321769 : Blo 1883435 10321769 := bstep (se 2 (by rfl) ⟨3870663, by rfl⟩ : syracuseStep 10321769 = 7741327) B7741327
theorem B27524717 : Blo 1883435 27524717 := bstep (se 3 (by rfl) ⟨5160884, by rfl⟩ : syracuseStep 27524717 = 10321769) B10321769
theorem B18349811 : Blo 1883435 18349811 := bstep (se 1 (by rfl) ⟨13762358, by rfl⟩ : syracuseStep 18349811 = 27524717) B27524717
theorem B12233207 : Blo 1883435 12233207 := bstep (se 1 (by rfl) ⟨9174905, by rfl⟩ : syracuseStep 12233207 = 18349811) B18349811
theorem B32621885 : Blo 1883435 32621885 := bstep (se 3 (by rfl) ⟨6116603, by rfl⟩ : syracuseStep 32621885 = 12233207) B12233207
theorem B21747923 : Blo 1883435 21747923 := bstep (se 1 (by rfl) ⟨16310942, by rfl⟩ : syracuseStep 21747923 = 32621885) B32621885
theorem B14498615 : Blo 1883435 14498615 := bstep (se 1 (by rfl) ⟨10873961, by rfl⟩ : syracuseStep 14498615 = 21747923) B21747923
theorem B9665743 : Blo 1883435 9665743 := bstep (se 1 (by rfl) ⟨7249307, by rfl⟩ : syracuseStep 9665743 = 14498615) B14498615
theorem B12887657 : Blo 1883435 12887657 := bstep (se 2 (by rfl) ⟨4832871, by rfl⟩ : syracuseStep 12887657 = 9665743) B9665743
theorem B8591771 : Blo 1883435 8591771 := bstep (se 1 (by rfl) ⟨6443828, by rfl⟩ : syracuseStep 8591771 = 12887657) B12887657
theorem B22911389 : Blo 1883435 22911389 := bstep (se 3 (by rfl) ⟨4295885, by rfl⟩ : syracuseStep 22911389 = 8591771) B8591771
theorem B15274259 : Blo 1883435 15274259 := bstep (se 1 (by rfl) ⟨11455694, by rfl⟩ : syracuseStep 15274259 = 22911389) B22911389
theorem B10182839 : Blo 1883435 10182839 := bstep (se 1 (by rfl) ⟨7637129, by rfl⟩ : syracuseStep 10182839 = 15274259) B15274259
theorem B27154237 : Blo 1883435 27154237 := bstep (se 3 (by rfl) ⟨5091419, by rfl⟩ : syracuseStep 27154237 = 10182839) B10182839
theorem B36205649 : Blo 1883435 36205649 := bstep (se 2 (by rfl) ⟨13577118, by rfl⟩ : syracuseStep 36205649 = 27154237) B27154237
theorem B24137099 : Blo 1883435 24137099 := bstep (se 1 (by rfl) ⟨18102824, by rfl⟩ : syracuseStep 24137099 = 36205649) B36205649
theorem B16091399 : Blo 1883435 16091399 := bstep (se 1 (by rfl) ⟨12068549, by rfl⟩ : syracuseStep 16091399 = 24137099) B24137099
theorem B10727599 : Blo 1883435 10727599 := bstep (se 1 (by rfl) ⟨8045699, by rfl⟩ : syracuseStep 10727599 = 16091399) B16091399
theorem B14303465 : Blo 1883435 14303465 := bstep (se 2 (by rfl) ⟨5363799, by rfl⟩ : syracuseStep 14303465 = 10727599) B10727599
theorem B9535643 : Blo 1883435 9535643 := bstep (se 1 (by rfl) ⟨7151732, by rfl⟩ : syracuseStep 9535643 = 14303465) B14303465
theorem B6357095 : Blo 1883435 6357095 := bstep (se 1 (by rfl) ⟨4767821, by rfl⟩ : syracuseStep 6357095 = 9535643) B9535643
theorem B4238063 : Blo 1883435 4238063 := bstep (se 1 (by rfl) ⟨3178547, by rfl⟩ : syracuseStep 4238063 = 6357095) B6357095
theorem B2825375 : Blo 1883435 2825375 := bstep (se 1 (by rfl) ⟨2119031, by rfl⟩ : syracuseStep 2825375 = 4238063) B4238063
theorem B1883583 : Blo 1883435 1883583 := bstep (se 1 (by rfl) ⟨1412687, by rfl⟩ : syracuseStep 1883583 = 2825375) B2825375
theorem B2825381 : Blo 1883435 2825381 := bbase (se 4 (by rfl) ⟨264879, by rfl⟩ : syracuseStep 2825381 = 529759) (by norm_num)
theorem B1883587 : Blo 1883435 1883587 := bstep (se 1 (by rfl) ⟨1412690, by rfl⟩ : syracuseStep 1883587 = 2825381) B2825381
theorem B2383921 : Blo 1883435 2383921 := bbase (se 2 (by rfl) ⟨893970, by rfl⟩ : syracuseStep 2383921 = 1787941) (by norm_num)
theorem B3178561 : Blo 1883435 3178561 := bstep (se 2 (by rfl) ⟨1191960, by rfl⟩ : syracuseStep 3178561 = 2383921) B2383921
theorem B4238081 : Blo 1883435 4238081 := bstep (se 2 (by rfl) ⟨1589280, by rfl⟩ : syracuseStep 4238081 = 3178561) B3178561
theorem B2825387 : Blo 1883435 2825387 := bstep (se 1 (by rfl) ⟨2119040, by rfl⟩ : syracuseStep 2825387 = 4238081) B4238081
theorem B1883591 : Blo 1883435 1883591 := bstep (se 1 (by rfl) ⟨1412693, by rfl⟩ : syracuseStep 1883591 = 2825387) B2825387
theorem B2119045 : Blo 1883435 2119045 := bbase (se 4 (by rfl) ⟨198660, by rfl⟩ : syracuseStep 2119045 = 397321) (by norm_num)
theorem B2825393 : Blo 1883435 2825393 := bstep (se 2 (by rfl) ⟨1059522, by rfl⟩ : syracuseStep 2825393 = 2119045) B2119045
theorem B1883595 : Blo 1883435 1883595 := bstep (se 1 (by rfl) ⟨1412696, by rfl⟩ : syracuseStep 1883595 = 2825393) B2825393
theorem B4022885 : Blo 1883435 4022885 := bbase (se 4 (by rfl) ⟨377145, by rfl⟩ : syracuseStep 4022885 = 754291) (by norm_num)
theorem B2681923 : Blo 1883435 2681923 := bstep (se 1 (by rfl) ⟨2011442, by rfl⟩ : syracuseStep 2681923 = 4022885) B4022885
theorem B3575897 : Blo 1883435 3575897 := bstep (se 2 (by rfl) ⟨1340961, by rfl⟩ : syracuseStep 3575897 = 2681923) B2681923
theorem B2383931 : Blo 1883435 2383931 := bstep (se 1 (by rfl) ⟨1787948, by rfl⟩ : syracuseStep 2383931 = 3575897) B3575897
theorem B6357149 : Blo 1883435 6357149 := bstep (se 3 (by rfl) ⟨1191965, by rfl⟩ : syracuseStep 6357149 = 2383931) B2383931
theorem B4238099 : Blo 1883435 4238099 := bstep (se 1 (by rfl) ⟨3178574, by rfl⟩ : syracuseStep 4238099 = 6357149) B6357149
theorem B2825399 : Blo 1883435 2825399 := bstep (se 1 (by rfl) ⟨2119049, by rfl⟩ : syracuseStep 2825399 = 4238099) B4238099
theorem B1883599 : Blo 1883435 1883599 := bstep (se 1 (by rfl) ⟨1412699, by rfl⟩ : syracuseStep 1883599 = 2825399) B2825399
theorem B2825405 : Blo 1883435 2825405 := bbase (se 3 (by rfl) ⟨529763, by rfl⟩ : syracuseStep 2825405 = 1059527) (by norm_num)
theorem B1883603 : Blo 1883435 1883603 := bstep (se 1 (by rfl) ⟨1412702, by rfl⟩ : syracuseStep 1883603 = 2825405) B2825405
theorem B4238117 : Blo 1883435 4238117 := bbase (se 4 (by rfl) ⟨397323, by rfl⟩ : syracuseStep 4238117 = 794647) (by norm_num)
theorem B2825411 : Blo 1883435 2825411 := bstep (se 1 (by rfl) ⟨2119058, by rfl⟩ : syracuseStep 2825411 = 4238117) B4238117
theorem B1883607 : Blo 1883435 1883607 := bstep (se 1 (by rfl) ⟨1412705, by rfl⟩ : syracuseStep 1883607 = 2825411) B2825411
theorem B4767893 : Blo 1883435 4767893 := bbase (se 6 (by rfl) ⟨111747, by rfl⟩ : syracuseStep 4767893 = 223495) (by norm_num)
theorem B3178595 : Blo 1883435 3178595 := bstep (se 1 (by rfl) ⟨2383946, by rfl⟩ : syracuseStep 3178595 = 4767893) B4767893
theorem B2119063 : Blo 1883435 2119063 := bstep (se 1 (by rfl) ⟨1589297, by rfl⟩ : syracuseStep 2119063 = 3178595) B3178595
theorem B2825417 : Blo 1883435 2825417 := bstep (se 2 (by rfl) ⟨1059531, by rfl⟩ : syracuseStep 2825417 = 2119063) B2119063
theorem B1883611 : Blo 1883435 1883611 := bstep (se 1 (by rfl) ⟨1412708, by rfl⟩ : syracuseStep 1883611 = 2825417) B2825417
theorem B3017189 : Blo 1883435 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B8045837 : Blo 1883435 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B5363891 : Blo 1883435 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B3575927 : Blo 1883435 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B9535805 : Blo 1883435 9535805 := bstep (se 3 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 9535805 = 3575927) B3575927
theorem B6357203 : Blo 1883435 6357203 := bstep (se 1 (by rfl) ⟨4767902, by rfl⟩ : syracuseStep 6357203 = 9535805) B9535805
theorem B4238135 : Blo 1883435 4238135 := bstep (se 1 (by rfl) ⟨3178601, by rfl⟩ : syracuseStep 4238135 = 6357203) B6357203
theorem B2825423 : Blo 1883435 2825423 := bstep (se 1 (by rfl) ⟨2119067, by rfl⟩ : syracuseStep 2825423 = 4238135) B4238135
theorem B1883615 : Blo 1883435 1883615 := bstep (se 1 (by rfl) ⟨1412711, by rfl⟩ : syracuseStep 1883615 = 2825423) B2825423
theorem B2825429 : Blo 1883435 2825429 := bbase (se 7 (by rfl) ⟨33110, by rfl⟩ : syracuseStep 2825429 = 66221) (by norm_num)
theorem B1883619 : Blo 1883435 1883619 := bstep (se 1 (by rfl) ⟨1412714, by rfl⟩ : syracuseStep 1883619 = 2825429) B2825429
theorem B2681957 : Blo 1883435 2681957 := bbase (se 4 (by rfl) ⟨251433, by rfl⟩ : syracuseStep 2681957 = 502867) (by norm_num)
theorem B7151885 : Blo 1883435 7151885 := bstep (se 3 (by rfl) ⟨1340978, by rfl⟩ : syracuseStep 7151885 = 2681957) B2681957
theorem B4767923 : Blo 1883435 4767923 := bstep (se 1 (by rfl) ⟨3575942, by rfl⟩ : syracuseStep 4767923 = 7151885) B7151885
theorem B3178615 : Blo 1883435 3178615 := bstep (se 1 (by rfl) ⟨2383961, by rfl⟩ : syracuseStep 3178615 = 4767923) B4767923
theorem B4238153 : Blo 1883435 4238153 := bstep (se 2 (by rfl) ⟨1589307, by rfl⟩ : syracuseStep 4238153 = 3178615) B3178615
theorem B2825435 : Blo 1883435 2825435 := bstep (se 1 (by rfl) ⟨2119076, by rfl⟩ : syracuseStep 2825435 = 4238153) B4238153
theorem B1883623 : Blo 1883435 1883623 := bstep (se 1 (by rfl) ⟨1412717, by rfl⟩ : syracuseStep 1883623 = 2825435) B2825435
theorem B2119081 : Blo 1883435 2119081 := bbase (se 2 (by rfl) ⟨794655, by rfl⟩ : syracuseStep 2119081 = 1589311) (by norm_num)
theorem B2825441 : Blo 1883435 2825441 := bstep (se 2 (by rfl) ⟨1059540, by rfl⟩ : syracuseStep 2825441 = 2119081) B2119081
theorem B1883627 : Blo 1883435 1883627 := bstep (se 1 (by rfl) ⟨1412720, by rfl⟩ : syracuseStep 1883627 = 2825441) B2825441
theorem B3058381 : Blo 1883435 3058381 := bbase (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) (by norm_num)
theorem B16311365 : Blo 1883435 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B10874243 : Blo 1883435 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B7249495 : Blo 1883435 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B9665993 : Blo 1883435 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B25775981 : Blo 1883435 25775981 := bstep (se 3 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 25775981 = 9665993) B9665993
theorem B17183987 : Blo 1883435 17183987 := bstep (se 1 (by rfl) ⟨12887990, by rfl⟩ : syracuseStep 17183987 = 25775981) B25775981
theorem B11455991 : Blo 1883435 11455991 := bstep (se 1 (by rfl) ⟨8591993, by rfl⟩ : syracuseStep 11455991 = 17183987) B17183987
theorem B7637327 : Blo 1883435 7637327 := bstep (se 1 (by rfl) ⟨5727995, by rfl⟩ : syracuseStep 7637327 = 11455991) B11455991
theorem B5091551 : Blo 1883435 5091551 := bstep (se 1 (by rfl) ⟨3818663, by rfl⟩ : syracuseStep 5091551 = 7637327) B7637327
theorem B3394367 : Blo 1883435 3394367 := bstep (se 1 (by rfl) ⟨2545775, by rfl⟩ : syracuseStep 3394367 = 5091551) B5091551
theorem B2262911 : Blo 1883435 2262911 := bstep (se 1 (by rfl) ⟨1697183, by rfl⟩ : syracuseStep 2262911 = 3394367) B3394367
theorem B6034429 : Blo 1883435 6034429 := bstep (se 3 (by rfl) ⟨1131455, by rfl⟩ : syracuseStep 6034429 = 2262911) B2262911
theorem B8045905 : Blo 1883435 8045905 := bstep (se 2 (by rfl) ⟨3017214, by rfl⟩ : syracuseStep 8045905 = 6034429) B6034429
theorem B10727873 : Blo 1883435 10727873 := bstep (se 2 (by rfl) ⟨4022952, by rfl⟩ : syracuseStep 10727873 = 8045905) B8045905
theorem B7151915 : Blo 1883435 7151915 := bstep (se 1 (by rfl) ⟨5363936, by rfl⟩ : syracuseStep 7151915 = 10727873) B10727873
theorem B4767943 : Blo 1883435 4767943 := bstep (se 1 (by rfl) ⟨3575957, by rfl⟩ : syracuseStep 4767943 = 7151915) B7151915
theorem B6357257 : Blo 1883435 6357257 := bstep (se 2 (by rfl) ⟨2383971, by rfl⟩ : syracuseStep 6357257 = 4767943) B4767943
theorem B4238171 : Blo 1883435 4238171 := bstep (se 1 (by rfl) ⟨3178628, by rfl⟩ : syracuseStep 4238171 = 6357257) B6357257
theorem B2825447 : Blo 1883435 2825447 := bstep (se 1 (by rfl) ⟨2119085, by rfl⟩ : syracuseStep 2825447 = 4238171) B4238171
theorem B1883631 : Blo 1883435 1883631 := bstep (se 1 (by rfl) ⟨1412723, by rfl⟩ : syracuseStep 1883631 = 2825447) B2825447
theorem B2825453 : Blo 1883435 2825453 := bbase (se 3 (by rfl) ⟨529772, by rfl⟩ : syracuseStep 2825453 = 1059545) (by norm_num)
theorem B1883635 : Blo 1883435 1883635 := bstep (se 1 (by rfl) ⟨1412726, by rfl⟩ : syracuseStep 1883635 = 2825453) B2825453
theorem B4238189 : Blo 1883435 4238189 := bbase (se 3 (by rfl) ⟨794660, by rfl⟩ : syracuseStep 4238189 = 1589321) (by norm_num)
theorem B2825459 : Blo 1883435 2825459 := bstep (se 1 (by rfl) ⟨2119094, by rfl⟩ : syracuseStep 2825459 = 4238189) B4238189
theorem B1883639 : Blo 1883435 1883639 := bstep (se 1 (by rfl) ⟨1412729, by rfl⟩ : syracuseStep 1883639 = 2825459) B2825459
theorem B3575981 : Blo 1883435 3575981 := bbase (se 3 (by rfl) ⟨670496, by rfl⟩ : syracuseStep 3575981 = 1340993) (by norm_num)
theorem B2383987 : Blo 1883435 2383987 := bstep (se 1 (by rfl) ⟨1787990, by rfl⟩ : syracuseStep 2383987 = 3575981) B3575981
theorem B3178649 : Blo 1883435 3178649 := bstep (se 2 (by rfl) ⟨1191993, by rfl⟩ : syracuseStep 3178649 = 2383987) B2383987
theorem B2119099 : Blo 1883435 2119099 := bstep (se 1 (by rfl) ⟨1589324, by rfl⟩ : syracuseStep 2119099 = 3178649) B3178649
theorem B2825465 : Blo 1883435 2825465 := bstep (se 2 (by rfl) ⟨1059549, by rfl⟩ : syracuseStep 2825465 = 2119099) B2119099
theorem B1883643 : Blo 1883435 1883643 := bstep (se 1 (by rfl) ⟨1412732, by rfl⟩ : syracuseStep 1883643 = 2825465) B2825465
theorem B2038937 : Blo 1883435 2038937 := bbase (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) (by norm_num)
theorem B21748661 : Blo 1883435 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B14499107 : Blo 1883435 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B9666071 : Blo 1883435 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B6444047 : Blo 1883435 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B17184125 : Blo 1883435 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B11456083 : Blo 1883435 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B61099109 : Blo 1883435 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B40732739 : Blo 1883435 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B27155159 : Blo 1883435 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B18103439 : Blo 1883435 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B48275837 : Blo 1883435 48275837 := bstep (se 3 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 48275837 = 18103439) B18103439
theorem B32183891 : Blo 1883435 32183891 := bstep (se 1 (by rfl) ⟨24137918, by rfl⟩ : syracuseStep 32183891 = 48275837) B48275837
theorem B21455927 : Blo 1883435 21455927 := bstep (se 1 (by rfl) ⟨16091945, by rfl⟩ : syracuseStep 21455927 = 32183891) B32183891
theorem B14303951 : Blo 1883435 14303951 := bstep (se 1 (by rfl) ⟨10727963, by rfl⟩ : syracuseStep 14303951 = 21455927) B21455927
theorem B9535967 : Blo 1883435 9535967 := bstep (se 1 (by rfl) ⟨7151975, by rfl⟩ : syracuseStep 9535967 = 14303951) B14303951
theorem B6357311 : Blo 1883435 6357311 := bstep (se 1 (by rfl) ⟨4767983, by rfl⟩ : syracuseStep 6357311 = 9535967) B9535967
theorem B4238207 : Blo 1883435 4238207 := bstep (se 1 (by rfl) ⟨3178655, by rfl⟩ : syracuseStep 4238207 = 6357311) B6357311
theorem B2825471 : Blo 1883435 2825471 := bstep (se 1 (by rfl) ⟨2119103, by rfl⟩ : syracuseStep 2825471 = 4238207) B4238207
theorem B1883647 : Blo 1883435 1883647 := bstep (se 1 (by rfl) ⟨1412735, by rfl⟩ : syracuseStep 1883647 = 2825471) B2825471
theorem B2825477 : Blo 1883435 2825477 := bbase (se 4 (by rfl) ⟨264888, by rfl⟩ : syracuseStep 2825477 = 529777) (by norm_num)
theorem B1883651 : Blo 1883435 1883651 := bstep (se 1 (by rfl) ⟨1412738, by rfl⟩ : syracuseStep 1883651 = 2825477) B2825477
theorem B3178669 : Blo 1883435 3178669 := bbase (se 3 (by rfl) ⟨596000, by rfl⟩ : syracuseStep 3178669 = 1192001) (by norm_num)
theorem B4238225 : Blo 1883435 4238225 := bstep (se 2 (by rfl) ⟨1589334, by rfl⟩ : syracuseStep 4238225 = 3178669) B3178669
theorem B2825483 : Blo 1883435 2825483 := bstep (se 1 (by rfl) ⟨2119112, by rfl⟩ : syracuseStep 2825483 = 4238225) B4238225
theorem B1883655 : Blo 1883435 1883655 := bstep (se 1 (by rfl) ⟨1412741, by rfl⟩ : syracuseStep 1883655 = 2825483) B2825483
theorem B2119117 : Blo 1883435 2119117 := bbase (se 3 (by rfl) ⟨397334, by rfl⟩ : syracuseStep 2119117 = 794669) (by norm_num)
theorem B2825489 : Blo 1883435 2825489 := bstep (se 2 (by rfl) ⟨1059558, by rfl⟩ : syracuseStep 2825489 = 2119117) B2119117
theorem B1883659 : Blo 1883435 1883659 := bstep (se 1 (by rfl) ⟨1412744, by rfl⟩ : syracuseStep 1883659 = 2825489) B2825489
theorem B6357365 : Blo 1883435 6357365 := bbase (se 5 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 6357365 = 596003) (by norm_num)
theorem B4238243 : Blo 1883435 4238243 := bstep (se 1 (by rfl) ⟨3178682, by rfl⟩ : syracuseStep 4238243 = 6357365) B6357365
theorem B2825495 : Blo 1883435 2825495 := bstep (se 1 (by rfl) ⟨2119121, by rfl⟩ : syracuseStep 2825495 = 4238243) B4238243
theorem B1883663 : Blo 1883435 1883663 := bstep (se 1 (by rfl) ⟨1412747, by rfl⟩ : syracuseStep 1883663 = 2825495) B2825495
theorem B2825501 : Blo 1883435 2825501 := bbase (se 3 (by rfl) ⟨529781, by rfl⟩ : syracuseStep 2825501 = 1059563) (by norm_num)
theorem B1883667 : Blo 1883435 1883667 := bstep (se 1 (by rfl) ⟨1412750, by rfl⟩ : syracuseStep 1883667 = 2825501) B2825501
theorem B4238261 : Blo 1883435 4238261 := bbase (se 5 (by rfl) ⟨198668, by rfl⟩ : syracuseStep 4238261 = 397337) (by norm_num)
theorem B2825507 : Blo 1883435 2825507 := bstep (se 1 (by rfl) ⟨2119130, by rfl⟩ : syracuseStep 2825507 = 4238261) B4238261
theorem B1883671 : Blo 1883435 1883671 := bstep (se 1 (by rfl) ⟨1412753, by rfl⟩ : syracuseStep 1883671 = 2825507) B2825507
theorem B2148049 : Blo 1883435 2148049 := bbase (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) (by norm_num)
theorem B2864065 : Blo 1883435 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B3818753 : Blo 1883435 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B2545835 : Blo 1883435 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B6788893 : Blo 1883435 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B9051857 : Blo 1883435 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B6034571 : Blo 1883435 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B4023047 : Blo 1883435 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B10728125 : Blo 1883435 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B7152083 : Blo 1883435 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B4768055 : Blo 1883435 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B3178703 : Blo 1883435 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B2119135 : Blo 1883435 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B2825513 : Blo 1883435 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B1883675 : Blo 1883435 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B13577813 : Blo 1883435 13577813 := bbase (se 8 (by rfl) ⟨79557, by rfl⟩ : syracuseStep 13577813 = 159115) (by norm_num)
theorem B9051875 : Blo 1883435 9051875 := bstep (se 1 (by rfl) ⟨6788906, by rfl⟩ : syracuseStep 9051875 = 13577813) B13577813
theorem B6034583 : Blo 1883435 6034583 := bstep (se 1 (by rfl) ⟨4525937, by rfl⟩ : syracuseStep 6034583 = 9051875) B9051875
theorem B4023055 : Blo 1883435 4023055 := bstep (se 1 (by rfl) ⟨3017291, by rfl⟩ : syracuseStep 4023055 = 6034583) B6034583
theorem B5364073 : Blo 1883435 5364073 := bstep (se 2 (by rfl) ⟨2011527, by rfl⟩ : syracuseStep 5364073 = 4023055) B4023055
theorem B7152097 : Blo 1883435 7152097 := bstep (se 2 (by rfl) ⟨2682036, by rfl⟩ : syracuseStep 7152097 = 5364073) B5364073
theorem B9536129 : Blo 1883435 9536129 := bstep (se 2 (by rfl) ⟨3576048, by rfl⟩ : syracuseStep 9536129 = 7152097) B7152097
theorem B6357419 : Blo 1883435 6357419 := bstep (se 1 (by rfl) ⟨4768064, by rfl⟩ : syracuseStep 6357419 = 9536129) B9536129
theorem B4238279 : Blo 1883435 4238279 := bstep (se 1 (by rfl) ⟨3178709, by rfl⟩ : syracuseStep 4238279 = 6357419) B6357419
theorem B2825519 : Blo 1883435 2825519 := bstep (se 1 (by rfl) ⟨2119139, by rfl⟩ : syracuseStep 2825519 = 4238279) B4238279
theorem B1883679 : Blo 1883435 1883679 := bstep (se 1 (by rfl) ⟨1412759, by rfl⟩ : syracuseStep 1883679 = 2825519) B2825519
theorem B2825525 : Blo 1883435 2825525 := bbase (se 5 (by rfl) ⟨132446, by rfl⟩ : syracuseStep 2825525 = 264893) (by norm_num)
theorem B1883683 : Blo 1883435 1883683 := bstep (se 1 (by rfl) ⟨1412762, by rfl⟩ : syracuseStep 1883683 = 2825525) B2825525
theorem B4768085 : Blo 1883435 4768085 := bbase (se 10 (by rfl) ⟨6984, by rfl⟩ : syracuseStep 4768085 = 13969) (by norm_num)
theorem B3178723 : Blo 1883435 3178723 := bstep (se 1 (by rfl) ⟨2384042, by rfl⟩ : syracuseStep 3178723 = 4768085) B4768085
theorem B4238297 : Blo 1883435 4238297 := bstep (se 2 (by rfl) ⟨1589361, by rfl⟩ : syracuseStep 4238297 = 3178723) B3178723
theorem B2825531 : Blo 1883435 2825531 := bstep (se 1 (by rfl) ⟨2119148, by rfl⟩ : syracuseStep 2825531 = 4238297) B4238297
theorem B1883687 : Blo 1883435 1883687 := bstep (se 1 (by rfl) ⟨1412765, by rfl⟩ : syracuseStep 1883687 = 2825531) B2825531
theorem B2119153 : Blo 1883435 2119153 := bbase (se 2 (by rfl) ⟨794682, by rfl⟩ : syracuseStep 2119153 = 1589365) (by norm_num)
theorem B2825537 : Blo 1883435 2825537 := bstep (se 2 (by rfl) ⟨1059576, by rfl⟩ : syracuseStep 2825537 = 2119153) B2119153
theorem B1883691 : Blo 1883435 1883691 := bstep (se 1 (by rfl) ⟨1412768, by rfl⟩ : syracuseStep 1883691 = 2825537) B2825537
theorem B12069269 : Blo 1883435 12069269 := bbase (se 6 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 12069269 = 565747) (by norm_num)
theorem B8046179 : Blo 1883435 8046179 := bstep (se 1 (by rfl) ⟨6034634, by rfl⟩ : syracuseStep 8046179 = 12069269) B12069269
theorem B5364119 : Blo 1883435 5364119 := bstep (se 1 (by rfl) ⟨4023089, by rfl⟩ : syracuseStep 5364119 = 8046179) B8046179
theorem B3576079 : Blo 1883435 3576079 := bstep (se 1 (by rfl) ⟨2682059, by rfl⟩ : syracuseStep 3576079 = 5364119) B5364119
theorem B4768105 : Blo 1883435 4768105 := bstep (se 2 (by rfl) ⟨1788039, by rfl⟩ : syracuseStep 4768105 = 3576079) B3576079
theorem B6357473 : Blo 1883435 6357473 := bstep (se 2 (by rfl) ⟨2384052, by rfl⟩ : syracuseStep 6357473 = 4768105) B4768105
theorem B4238315 : Blo 1883435 4238315 := bstep (se 1 (by rfl) ⟨3178736, by rfl⟩ : syracuseStep 4238315 = 6357473) B6357473
theorem B2825543 : Blo 1883435 2825543 := bstep (se 1 (by rfl) ⟨2119157, by rfl⟩ : syracuseStep 2825543 = 4238315) B4238315
theorem B1883695 : Blo 1883435 1883695 := bstep (se 1 (by rfl) ⟨1412771, by rfl⟩ : syracuseStep 1883695 = 2825543) B2825543
theorem B2825549 : Blo 1883435 2825549 := bbase (se 3 (by rfl) ⟨529790, by rfl⟩ : syracuseStep 2825549 = 1059581) (by norm_num)
theorem B1883699 : Blo 1883435 1883699 := bstep (se 1 (by rfl) ⟨1412774, by rfl⟩ : syracuseStep 1883699 = 2825549) B2825549
theorem B4238333 : Blo 1883435 4238333 := bbase (se 3 (by rfl) ⟨794687, by rfl⟩ : syracuseStep 4238333 = 1589375) (by norm_num)
theorem B2825555 : Blo 1883435 2825555 := bstep (se 1 (by rfl) ⟨2119166, by rfl⟩ : syracuseStep 2825555 = 4238333) B4238333
theorem B1883703 : Blo 1883435 1883703 := bstep (se 1 (by rfl) ⟨1412777, by rfl⟩ : syracuseStep 1883703 = 2825555) B2825555
theorem B3178757 : Blo 1883435 3178757 := bbase (se 4 (by rfl) ⟨298008, by rfl⟩ : syracuseStep 3178757 = 596017) (by norm_num)
theorem B2119171 : Blo 1883435 2119171 := bstep (se 1 (by rfl) ⟨1589378, by rfl⟩ : syracuseStep 2119171 = 3178757) B3178757
theorem B2825561 : Blo 1883435 2825561 := bstep (se 2 (by rfl) ⟨1059585, by rfl⟩ : syracuseStep 2825561 = 2119171) B2119171
theorem B1883707 : Blo 1883435 1883707 := bstep (se 1 (by rfl) ⟨1412780, by rfl⟩ : syracuseStep 1883707 = 2825561) B2825561
theorem B14304437 : Blo 1883435 14304437 := bbase (se 5 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 14304437 = 1341041) (by norm_num)
theorem B9536291 : Blo 1883435 9536291 := bstep (se 1 (by rfl) ⟨7152218, by rfl⟩ : syracuseStep 9536291 = 14304437) B14304437
theorem B6357527 : Blo 1883435 6357527 := bstep (se 1 (by rfl) ⟨4768145, by rfl⟩ : syracuseStep 6357527 = 9536291) B9536291
theorem B4238351 : Blo 1883435 4238351 := bstep (se 1 (by rfl) ⟨3178763, by rfl⟩ : syracuseStep 4238351 = 6357527) B6357527
theorem B2825567 : Blo 1883435 2825567 := bstep (se 1 (by rfl) ⟨2119175, by rfl⟩ : syracuseStep 2825567 = 4238351) B4238351
theorem B1883711 : Blo 1883435 1883711 := bstep (se 1 (by rfl) ⟨1412783, by rfl⟩ : syracuseStep 1883711 = 2825567) B2825567
theorem B2825573 : Blo 1883435 2825573 := bbase (se 4 (by rfl) ⟨264897, by rfl⟩ : syracuseStep 2825573 = 529795) (by norm_num)
theorem B1883715 : Blo 1883435 1883715 := bstep (se 1 (by rfl) ⟨1412786, by rfl⟩ : syracuseStep 1883715 = 2825573) B2825573
theorem B3576125 : Blo 1883435 3576125 := bbase (se 3 (by rfl) ⟨670523, by rfl⟩ : syracuseStep 3576125 = 1341047) (by norm_num)
theorem B2384083 : Blo 1883435 2384083 := bstep (se 1 (by rfl) ⟨1788062, by rfl⟩ : syracuseStep 2384083 = 3576125) B3576125
theorem B3178777 : Blo 1883435 3178777 := bstep (se 2 (by rfl) ⟨1192041, by rfl⟩ : syracuseStep 3178777 = 2384083) B2384083
theorem B4238369 : Blo 1883435 4238369 := bstep (se 2 (by rfl) ⟨1589388, by rfl⟩ : syracuseStep 4238369 = 3178777) B3178777
theorem B2825579 : Blo 1883435 2825579 := bstep (se 1 (by rfl) ⟨2119184, by rfl⟩ : syracuseStep 2825579 = 4238369) B4238369
theorem B1883719 : Blo 1883435 1883719 := bstep (se 1 (by rfl) ⟨1412789, by rfl⟩ : syracuseStep 1883719 = 2825579) B2825579
theorem B2119189 : Blo 1883435 2119189 := bbase (se 6 (by rfl) ⟨49668, by rfl⟩ : syracuseStep 2119189 = 99337) (by norm_num)
theorem B2825585 : Blo 1883435 2825585 := bstep (se 2 (by rfl) ⟨1059594, by rfl⟩ : syracuseStep 2825585 = 2119189) B2119189
theorem B1883723 : Blo 1883435 1883723 := bstep (se 1 (by rfl) ⟨1412792, by rfl⟩ : syracuseStep 1883723 = 2825585) B2825585
theorem B2384093 : Blo 1883435 2384093 := bbase (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) (by norm_num)
theorem B6357581 : Blo 1883435 6357581 := bstep (se 3 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 6357581 = 2384093) B2384093
theorem B4238387 : Blo 1883435 4238387 := bstep (se 1 (by rfl) ⟨3178790, by rfl⟩ : syracuseStep 4238387 = 6357581) B6357581
theorem B2825591 : Blo 1883435 2825591 := bstep (se 1 (by rfl) ⟨2119193, by rfl⟩ : syracuseStep 2825591 = 4238387) B4238387
theorem B1883727 : Blo 1883435 1883727 := bstep (se 1 (by rfl) ⟨1412795, by rfl⟩ : syracuseStep 1883727 = 2825591) B2825591
theorem B2825597 : Blo 1883435 2825597 := bbase (se 3 (by rfl) ⟨529799, by rfl⟩ : syracuseStep 2825597 = 1059599) (by norm_num)
theorem B1883731 : Blo 1883435 1883731 := bstep (se 1 (by rfl) ⟨1412798, by rfl⟩ : syracuseStep 1883731 = 2825597) B2825597
theorem B4238405 : Blo 1883435 4238405 := bbase (se 4 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 4238405 = 794701) (by norm_num)
theorem B2825603 : Blo 1883435 2825603 := bstep (se 1 (by rfl) ⟨2119202, by rfl⟩ : syracuseStep 2825603 = 4238405) B4238405
theorem B1883735 : Blo 1883435 1883735 := bstep (se 1 (by rfl) ⟨1412801, by rfl⟩ : syracuseStep 1883735 = 2825603) B2825603
theorem B5364245 : Blo 1883435 5364245 := bbase (se 6 (by rfl) ⟨125724, by rfl⟩ : syracuseStep 5364245 = 251449) (by norm_num)
theorem B3576163 : Blo 1883435 3576163 := bstep (se 1 (by rfl) ⟨2682122, by rfl⟩ : syracuseStep 3576163 = 5364245) B5364245
theorem B4768217 : Blo 1883435 4768217 := bstep (se 2 (by rfl) ⟨1788081, by rfl⟩ : syracuseStep 4768217 = 3576163) B3576163
theorem B3178811 : Blo 1883435 3178811 := bstep (se 1 (by rfl) ⟨2384108, by rfl⟩ : syracuseStep 3178811 = 4768217) B4768217
theorem B2119207 : Blo 1883435 2119207 := bstep (se 1 (by rfl) ⟨1589405, by rfl⟩ : syracuseStep 2119207 = 3178811) B3178811
theorem B2825609 : Blo 1883435 2825609 := bstep (se 2 (by rfl) ⟨1059603, by rfl⟩ : syracuseStep 2825609 = 2119207) B2119207
theorem B1883739 : Blo 1883435 1883739 := bstep (se 1 (by rfl) ⟨1412804, by rfl⟩ : syracuseStep 1883739 = 2825609) B2825609
theorem B9536453 : Blo 1883435 9536453 := bbase (se 4 (by rfl) ⟨894042, by rfl⟩ : syracuseStep 9536453 = 1788085) (by norm_num)
theorem B6357635 : Blo 1883435 6357635 := bstep (se 1 (by rfl) ⟨4768226, by rfl⟩ : syracuseStep 6357635 = 9536453) B9536453
theorem B4238423 : Blo 1883435 4238423 := bstep (se 1 (by rfl) ⟨3178817, by rfl⟩ : syracuseStep 4238423 = 6357635) B6357635
theorem B2825615 : Blo 1883435 2825615 := bstep (se 1 (by rfl) ⟨2119211, by rfl⟩ : syracuseStep 2825615 = 4238423) B4238423
theorem B1883743 : Blo 1883435 1883743 := bstep (se 1 (by rfl) ⟨1412807, by rfl⟩ : syracuseStep 1883743 = 2825615) B2825615
theorem B2825621 : Blo 1883435 2825621 := bbase (se 6 (by rfl) ⟨66225, by rfl⟩ : syracuseStep 2825621 = 132451) (by norm_num)
theorem B1883747 : Blo 1883435 1883747 := bstep (se 1 (by rfl) ⟨1412810, by rfl⟩ : syracuseStep 1883747 = 2825621) B2825621
theorem B3266165 : Blo 1883435 3266165 := bbase (se 5 (by rfl) ⟨153101, by rfl⟩ : syracuseStep 3266165 = 306203) (by norm_num)
theorem B8709773 : Blo 1883435 8709773 := bstep (se 3 (by rfl) ⟨1633082, by rfl⟩ : syracuseStep 8709773 = 3266165) B3266165
theorem B23226061 : Blo 1883435 23226061 := bstep (se 3 (by rfl) ⟨4354886, by rfl⟩ : syracuseStep 23226061 = 8709773) B8709773
theorem B30968081 : Blo 1883435 30968081 := bstep (se 2 (by rfl) ⟨11613030, by rfl⟩ : syracuseStep 30968081 = 23226061) B23226061
theorem B20645387 : Blo 1883435 20645387 := bstep (se 1 (by rfl) ⟨15484040, by rfl⟩ : syracuseStep 20645387 = 30968081) B30968081
theorem B13763591 : Blo 1883435 13763591 := bstep (se 1 (by rfl) ⟨10322693, by rfl⟩ : syracuseStep 13763591 = 20645387) B20645387
theorem B9175727 : Blo 1883435 9175727 := bstep (se 1 (by rfl) ⟨6881795, by rfl⟩ : syracuseStep 9175727 = 13763591) B13763591
theorem B24468605 : Blo 1883435 24468605 := bstep (se 3 (by rfl) ⟨4587863, by rfl⟩ : syracuseStep 24468605 = 9175727) B9175727
theorem B16312403 : Blo 1883435 16312403 := bstep (se 1 (by rfl) ⟨12234302, by rfl⟩ : syracuseStep 16312403 = 24468605) B24468605
theorem B10874935 : Blo 1883435 10874935 := bstep (se 1 (by rfl) ⟨8156201, by rfl⟩ : syracuseStep 10874935 = 16312403) B16312403
theorem B14499913 : Blo 1883435 14499913 := bstep (se 2 (by rfl) ⟨5437467, by rfl⟩ : syracuseStep 14499913 = 10874935) B10874935
theorem B19333217 : Blo 1883435 19333217 := bstep (se 2 (by rfl) ⟨7249956, by rfl⟩ : syracuseStep 19333217 = 14499913) B14499913
theorem B12888811 : Blo 1883435 12888811 := bstep (se 1 (by rfl) ⟨9666608, by rfl⟩ : syracuseStep 12888811 = 19333217) B19333217
theorem B17185081 : Blo 1883435 17185081 := bstep (se 2 (by rfl) ⟨6444405, by rfl⟩ : syracuseStep 17185081 = 12888811) B12888811
theorem B22913441 : Blo 1883435 22913441 := bstep (se 2 (by rfl) ⟨8592540, by rfl⟩ : syracuseStep 22913441 = 17185081) B17185081
theorem B15275627 : Blo 1883435 15275627 := bstep (se 1 (by rfl) ⟨11456720, by rfl⟩ : syracuseStep 15275627 = 22913441) B22913441
theorem B10183751 : Blo 1883435 10183751 := bstep (se 1 (by rfl) ⟨7637813, by rfl⟩ : syracuseStep 10183751 = 15275627) B15275627
theorem B6789167 : Blo 1883435 6789167 := bstep (se 1 (by rfl) ⟨5091875, by rfl⟩ : syracuseStep 6789167 = 10183751) B10183751
theorem B4526111 : Blo 1883435 4526111 := bstep (se 1 (by rfl) ⟨3394583, by rfl⟩ : syracuseStep 4526111 = 6789167) B6789167
theorem B3017407 : Blo 1883435 3017407 := bstep (se 1 (by rfl) ⟨2263055, by rfl⟩ : syracuseStep 3017407 = 4526111) B4526111
theorem B4023209 : Blo 1883435 4023209 := bstep (se 2 (by rfl) ⟨1508703, by rfl⟩ : syracuseStep 4023209 = 3017407) B3017407
theorem B10728557 : Blo 1883435 10728557 := bstep (se 3 (by rfl) ⟨2011604, by rfl⟩ : syracuseStep 10728557 = 4023209) B4023209
theorem B7152371 : Blo 1883435 7152371 := bstep (se 1 (by rfl) ⟨5364278, by rfl⟩ : syracuseStep 7152371 = 10728557) B10728557
theorem B4768247 : Blo 1883435 4768247 := bstep (se 1 (by rfl) ⟨3576185, by rfl⟩ : syracuseStep 4768247 = 7152371) B7152371
theorem B3178831 : Blo 1883435 3178831 := bstep (se 1 (by rfl) ⟨2384123, by rfl⟩ : syracuseStep 3178831 = 4768247) B4768247
theorem B4238441 : Blo 1883435 4238441 := bstep (se 2 (by rfl) ⟨1589415, by rfl⟩ : syracuseStep 4238441 = 3178831) B3178831
theorem B2825627 : Blo 1883435 2825627 := bstep (se 1 (by rfl) ⟨2119220, by rfl⟩ : syracuseStep 2825627 = 4238441) B4238441
theorem B1883751 : Blo 1883435 1883751 := bstep (se 1 (by rfl) ⟨1412813, by rfl⟩ : syracuseStep 1883751 = 2825627) B2825627
theorem B2119225 : Blo 1883435 2119225 := bbase (se 2 (by rfl) ⟨794709, by rfl⟩ : syracuseStep 2119225 = 1589419) (by norm_num)
theorem B2825633 : Blo 1883435 2825633 := bstep (se 2 (by rfl) ⟨1059612, by rfl⟩ : syracuseStep 2825633 = 2119225) B2119225
theorem B1883755 : Blo 1883435 1883755 := bstep (se 1 (by rfl) ⟨1412816, by rfl⟩ : syracuseStep 1883755 = 2825633) B2825633
theorem B2011613 : Blo 1883435 2011613 := bbase (se 3 (by rfl) ⟨377177, by rfl⟩ : syracuseStep 2011613 = 754355) (by norm_num)
theorem B5364301 : Blo 1883435 5364301 := bstep (se 3 (by rfl) ⟨1005806, by rfl⟩ : syracuseStep 5364301 = 2011613) B2011613
theorem B7152401 : Blo 1883435 7152401 := bstep (se 2 (by rfl) ⟨2682150, by rfl⟩ : syracuseStep 7152401 = 5364301) B5364301
theorem B4768267 : Blo 1883435 4768267 := bstep (se 1 (by rfl) ⟨3576200, by rfl⟩ : syracuseStep 4768267 = 7152401) B7152401
theorem B6357689 : Blo 1883435 6357689 := bstep (se 2 (by rfl) ⟨2384133, by rfl⟩ : syracuseStep 6357689 = 4768267) B4768267
theorem B4238459 : Blo 1883435 4238459 := bstep (se 1 (by rfl) ⟨3178844, by rfl⟩ : syracuseStep 4238459 = 6357689) B6357689
theorem B2825639 : Blo 1883435 2825639 := bstep (se 1 (by rfl) ⟨2119229, by rfl⟩ : syracuseStep 2825639 = 4238459) B4238459
theorem B1883759 : Blo 1883435 1883759 := bstep (se 1 (by rfl) ⟨1412819, by rfl⟩ : syracuseStep 1883759 = 2825639) B2825639
theorem B2825645 : Blo 1883435 2825645 := bbase (se 3 (by rfl) ⟨529808, by rfl⟩ : syracuseStep 2825645 = 1059617) (by norm_num)
theorem B1883763 : Blo 1883435 1883763 := bstep (se 1 (by rfl) ⟨1412822, by rfl⟩ : syracuseStep 1883763 = 2825645) B2825645
theorem B4238477 : Blo 1883435 4238477 := bbase (se 3 (by rfl) ⟨794714, by rfl⟩ : syracuseStep 4238477 = 1589429) (by norm_num)
theorem B2825651 : Blo 1883435 2825651 := bstep (se 1 (by rfl) ⟨2119238, by rfl⟩ : syracuseStep 2825651 = 4238477) B4238477
theorem B1883767 : Blo 1883435 1883767 := bstep (se 1 (by rfl) ⟨1412825, by rfl⟩ : syracuseStep 1883767 = 2825651) B2825651
theorem B2384149 : Blo 1883435 2384149 := bbase (se 6 (by rfl) ⟨55878, by rfl⟩ : syracuseStep 2384149 = 111757) (by norm_num)
theorem B3178865 : Blo 1883435 3178865 := bstep (se 2 (by rfl) ⟨1192074, by rfl⟩ : syracuseStep 3178865 = 2384149) B2384149
theorem B2119243 : Blo 1883435 2119243 := bstep (se 1 (by rfl) ⟨1589432, by rfl⟩ : syracuseStep 2119243 = 3178865) B3178865
theorem B2825657 : Blo 1883435 2825657 := bstep (se 2 (by rfl) ⟨1059621, by rfl⟩ : syracuseStep 2825657 = 2119243) B2119243
theorem B1883771 : Blo 1883435 1883771 := bstep (se 1 (by rfl) ⟨1412828, by rfl⟩ : syracuseStep 1883771 = 2825657) B2825657
theorem B4414357 : Blo 1883435 4414357 := bbase (se 6 (by rfl) ⟨103461, by rfl⟩ : syracuseStep 4414357 = 206923) (by norm_num)
theorem B23543237 : Blo 1883435 23543237 := bstep (se 4 (by rfl) ⟨2207178, by rfl⟩ : syracuseStep 23543237 = 4414357) B4414357
theorem B15695491 : Blo 1883435 15695491 := bstep (se 1 (by rfl) ⟨11771618, by rfl⟩ : syracuseStep 15695491 = 23543237) B23543237
theorem B20927321 : Blo 1883435 20927321 := bstep (se 2 (by rfl) ⟨7847745, by rfl⟩ : syracuseStep 20927321 = 15695491) B15695491
theorem B13951547 : Blo 1883435 13951547 := bstep (se 1 (by rfl) ⟨10463660, by rfl⟩ : syracuseStep 13951547 = 20927321) B20927321
theorem B9301031 : Blo 1883435 9301031 := bstep (se 1 (by rfl) ⟨6975773, by rfl⟩ : syracuseStep 9301031 = 13951547) B13951547
theorem B6200687 : Blo 1883435 6200687 := bstep (se 1 (by rfl) ⟨4650515, by rfl⟩ : syracuseStep 6200687 = 9301031) B9301031
theorem B4133791 : Blo 1883435 4133791 := bstep (se 1 (by rfl) ⟨3100343, by rfl⟩ : syracuseStep 4133791 = 6200687) B6200687
theorem B5511721 : Blo 1883435 5511721 := bstep (se 2 (by rfl) ⟨2066895, by rfl⟩ : syracuseStep 5511721 = 4133791) B4133791
theorem B7348961 : Blo 1883435 7348961 := bstep (se 2 (by rfl) ⟨2755860, by rfl⟩ : syracuseStep 7348961 = 5511721) B5511721
theorem B19597229 : Blo 1883435 19597229 := bstep (se 3 (by rfl) ⟨3674480, by rfl⟩ : syracuseStep 19597229 = 7348961) B7348961
theorem B13064819 : Blo 1883435 13064819 := bstep (se 1 (by rfl) ⟨9798614, by rfl⟩ : syracuseStep 13064819 = 19597229) B19597229
theorem B139358069 : Blo 1883435 139358069 := bstep (se 5 (by rfl) ⟨6532409, by rfl⟩ : syracuseStep 139358069 = 13064819) B13064819
theorem B92905379 : Blo 1883435 92905379 := bstep (se 1 (by rfl) ⟨69679034, by rfl⟩ : syracuseStep 92905379 = 139358069) B139358069
theorem B61936919 : Blo 1883435 61936919 := bstep (se 1 (by rfl) ⟨46452689, by rfl⟩ : syracuseStep 61936919 = 92905379) B92905379
theorem B41291279 : Blo 1883435 41291279 := bstep (se 1 (by rfl) ⟨30968459, by rfl⟩ : syracuseStep 41291279 = 61936919) B61936919
theorem B27527519 : Blo 1883435 27527519 := bstep (se 1 (by rfl) ⟨20645639, by rfl⟩ : syracuseStep 27527519 = 41291279) B41291279
theorem B18351679 : Blo 1883435 18351679 := bstep (se 1 (by rfl) ⟨13763759, by rfl⟩ : syracuseStep 18351679 = 27527519) B27527519
theorem B24468905 : Blo 1883435 24468905 := bstep (se 2 (by rfl) ⟨9175839, by rfl⟩ : syracuseStep 24468905 = 18351679) B18351679
theorem B16312603 : Blo 1883435 16312603 := bstep (se 1 (by rfl) ⟨12234452, by rfl⟩ : syracuseStep 16312603 = 24468905) B24468905
theorem B21750137 : Blo 1883435 21750137 := bstep (se 2 (by rfl) ⟨8156301, by rfl⟩ : syracuseStep 21750137 = 16312603) B16312603
theorem B14500091 : Blo 1883435 14500091 := bstep (se 1 (by rfl) ⟨10875068, by rfl⟩ : syracuseStep 14500091 = 21750137) B21750137
theorem B38666909 : Blo 1883435 38666909 := bstep (se 3 (by rfl) ⟨7250045, by rfl⟩ : syracuseStep 38666909 = 14500091) B14500091
theorem B25777939 : Blo 1883435 25777939 := bstep (se 1 (by rfl) ⟨19333454, by rfl⟩ : syracuseStep 25777939 = 38666909) B38666909
theorem B34370585 : Blo 1883435 34370585 := bstep (se 2 (by rfl) ⟨12888969, by rfl⟩ : syracuseStep 34370585 = 25777939) B25777939
theorem B22913723 : Blo 1883435 22913723 := bstep (se 1 (by rfl) ⟨17185292, by rfl⟩ : syracuseStep 22913723 = 34370585) B34370585
theorem B61103261 : Blo 1883435 61103261 := bstep (se 3 (by rfl) ⟨11456861, by rfl⟩ : syracuseStep 61103261 = 22913723) B22913723
theorem B40735507 : Blo 1883435 40735507 := bstep (se 1 (by rfl) ⟨30551630, by rfl⟩ : syracuseStep 40735507 = 61103261) B61103261
theorem B54314009 : Blo 1883435 54314009 := bstep (se 2 (by rfl) ⟨20367753, by rfl⟩ : syracuseStep 54314009 = 40735507) B40735507
theorem B36209339 : Blo 1883435 36209339 := bstep (se 1 (by rfl) ⟨27157004, by rfl⟩ : syracuseStep 36209339 = 54314009) B54314009
theorem B24139559 : Blo 1883435 24139559 := bstep (se 1 (by rfl) ⟨18104669, by rfl⟩ : syracuseStep 24139559 = 36209339) B36209339
theorem B16093039 : Blo 1883435 16093039 := bstep (se 1 (by rfl) ⟨12069779, by rfl⟩ : syracuseStep 16093039 = 24139559) B24139559
theorem B21457385 : Blo 1883435 21457385 := bstep (se 2 (by rfl) ⟨8046519, by rfl⟩ : syracuseStep 21457385 = 16093039) B16093039
theorem B14304923 : Blo 1883435 14304923 := bstep (se 1 (by rfl) ⟨10728692, by rfl⟩ : syracuseStep 14304923 = 21457385) B21457385
theorem B9536615 : Blo 1883435 9536615 := bstep (se 1 (by rfl) ⟨7152461, by rfl⟩ : syracuseStep 9536615 = 14304923) B14304923
theorem B6357743 : Blo 1883435 6357743 := bstep (se 1 (by rfl) ⟨4768307, by rfl⟩ : syracuseStep 6357743 = 9536615) B9536615
theorem B4238495 : Blo 1883435 4238495 := bstep (se 1 (by rfl) ⟨3178871, by rfl⟩ : syracuseStep 4238495 = 6357743) B6357743
theorem B2825663 : Blo 1883435 2825663 := bstep (se 1 (by rfl) ⟨2119247, by rfl⟩ : syracuseStep 2825663 = 4238495) B4238495
theorem B1883775 : Blo 1883435 1883775 := bstep (se 1 (by rfl) ⟨1412831, by rfl⟩ : syracuseStep 1883775 = 2825663) B2825663
theorem B2825669 : Blo 1883435 2825669 := bbase (se 4 (by rfl) ⟨264906, by rfl⟩ : syracuseStep 2825669 = 529813) (by norm_num)
theorem B1883779 : Blo 1883435 1883779 := bstep (se 1 (by rfl) ⟨1412834, by rfl⟩ : syracuseStep 1883779 = 2825669) B2825669
theorem B3178885 : Blo 1883435 3178885 := bbase (se 4 (by rfl) ⟨298020, by rfl⟩ : syracuseStep 3178885 = 596041) (by norm_num)
theorem B4238513 : Blo 1883435 4238513 := bstep (se 2 (by rfl) ⟨1589442, by rfl⟩ : syracuseStep 4238513 = 3178885) B3178885
theorem B2825675 : Blo 1883435 2825675 := bstep (se 1 (by rfl) ⟨2119256, by rfl⟩ : syracuseStep 2825675 = 4238513) B4238513
theorem B1883783 : Blo 1883435 1883783 := bstep (se 1 (by rfl) ⟨1412837, by rfl⟩ : syracuseStep 1883783 = 2825675) B2825675
theorem B2119261 : Blo 1883435 2119261 := bbase (se 3 (by rfl) ⟨397361, by rfl⟩ : syracuseStep 2119261 = 794723) (by norm_num)
theorem B2825681 : Blo 1883435 2825681 := bstep (se 2 (by rfl) ⟨1059630, by rfl⟩ : syracuseStep 2825681 = 2119261) B2119261
theorem B1883787 : Blo 1883435 1883787 := bstep (se 1 (by rfl) ⟨1412840, by rfl⟩ : syracuseStep 1883787 = 2825681) B2825681
theorem B6357797 : Blo 1883435 6357797 := bbase (se 4 (by rfl) ⟨596043, by rfl⟩ : syracuseStep 6357797 = 1192087) (by norm_num)
theorem B4238531 : Blo 1883435 4238531 := bstep (se 1 (by rfl) ⟨3178898, by rfl⟩ : syracuseStep 4238531 = 6357797) B6357797
theorem B2825687 : Blo 1883435 2825687 := bstep (se 1 (by rfl) ⟨2119265, by rfl⟩ : syracuseStep 2825687 = 4238531) B4238531
theorem B1883791 : Blo 1883435 1883791 := bstep (se 1 (by rfl) ⟨1412843, by rfl⟩ : syracuseStep 1883791 = 2825687) B2825687
theorem B2825693 : Blo 1883435 2825693 := bbase (se 3 (by rfl) ⟨529817, by rfl⟩ : syracuseStep 2825693 = 1059635) (by norm_num)
theorem B1883795 : Blo 1883435 1883795 := bstep (se 1 (by rfl) ⟨1412846, by rfl⟩ : syracuseStep 1883795 = 2825693) B2825693
theorem B4238549 : Blo 1883435 4238549 := bbase (se 7 (by rfl) ⟨49670, by rfl⟩ : syracuseStep 4238549 = 99341) (by norm_num)
theorem B2825699 : Blo 1883435 2825699 := bstep (se 1 (by rfl) ⟨2119274, by rfl⟩ : syracuseStep 2825699 = 4238549) B4238549
theorem B1883799 : Blo 1883435 1883799 := bstep (se 1 (by rfl) ⟨1412849, by rfl⟩ : syracuseStep 1883799 = 2825699) B2825699
theorem B6034981 : Blo 1883435 6034981 := bbase (se 4 (by rfl) ⟨565779, by rfl⟩ : syracuseStep 6034981 = 1131559) (by norm_num)
theorem B8046641 : Blo 1883435 8046641 := bstep (se 2 (by rfl) ⟨3017490, by rfl⟩ : syracuseStep 8046641 = 6034981) B6034981
theorem B5364427 : Blo 1883435 5364427 := bstep (se 1 (by rfl) ⟨4023320, by rfl⟩ : syracuseStep 5364427 = 8046641) B8046641
theorem B7152569 : Blo 1883435 7152569 := bstep (se 2 (by rfl) ⟨2682213, by rfl⟩ : syracuseStep 7152569 = 5364427) B5364427
theorem B4768379 : Blo 1883435 4768379 := bstep (se 1 (by rfl) ⟨3576284, by rfl⟩ : syracuseStep 4768379 = 7152569) B7152569
theorem B3178919 : Blo 1883435 3178919 := bstep (se 1 (by rfl) ⟨2384189, by rfl⟩ : syracuseStep 3178919 = 4768379) B4768379
theorem B2119279 : Blo 1883435 2119279 := bstep (se 1 (by rfl) ⟨1589459, by rfl⟩ : syracuseStep 2119279 = 3178919) B3178919
theorem B2825705 : Blo 1883435 2825705 := bstep (se 2 (by rfl) ⟨1059639, by rfl⟩ : syracuseStep 2825705 = 2119279) B2119279
theorem B1883803 : Blo 1883435 1883803 := bstep (se 1 (by rfl) ⟨1412852, by rfl⟩ : syracuseStep 1883803 = 2825705) B2825705
theorem B4296397 : Blo 1883435 4296397 := bbase (se 3 (by rfl) ⟨805574, by rfl⟩ : syracuseStep 4296397 = 1611149) (by norm_num)
theorem B5728529 : Blo 1883435 5728529 := bstep (se 2 (by rfl) ⟨2148198, by rfl⟩ : syracuseStep 5728529 = 4296397) B4296397
theorem B15276077 : Blo 1883435 15276077 := bstep (se 3 (by rfl) ⟨2864264, by rfl⟩ : syracuseStep 15276077 = 5728529) B5728529
theorem B10184051 : Blo 1883435 10184051 := bstep (se 1 (by rfl) ⟨7638038, by rfl⟩ : syracuseStep 10184051 = 15276077) B15276077
theorem B6789367 : Blo 1883435 6789367 := bstep (se 1 (by rfl) ⟨5092025, by rfl⟩ : syracuseStep 6789367 = 10184051) B10184051
theorem B9052489 : Blo 1883435 9052489 := bstep (se 2 (by rfl) ⟨3394683, by rfl⟩ : syracuseStep 9052489 = 6789367) B6789367
theorem B12069985 : Blo 1883435 12069985 := bstep (se 2 (by rfl) ⟨4526244, by rfl⟩ : syracuseStep 12069985 = 9052489) B9052489
theorem B16093313 : Blo 1883435 16093313 := bstep (se 2 (by rfl) ⟨6034992, by rfl⟩ : syracuseStep 16093313 = 12069985) B12069985
theorem B10728875 : Blo 1883435 10728875 := bstep (se 1 (by rfl) ⟨8046656, by rfl⟩ : syracuseStep 10728875 = 16093313) B16093313
theorem B7152583 : Blo 1883435 7152583 := bstep (se 1 (by rfl) ⟨5364437, by rfl⟩ : syracuseStep 7152583 = 10728875) B10728875
theorem B9536777 : Blo 1883435 9536777 := bstep (se 2 (by rfl) ⟨3576291, by rfl⟩ : syracuseStep 9536777 = 7152583) B7152583
theorem B6357851 : Blo 1883435 6357851 := bstep (se 1 (by rfl) ⟨4768388, by rfl⟩ : syracuseStep 6357851 = 9536777) B9536777
theorem B4238567 : Blo 1883435 4238567 := bstep (se 1 (by rfl) ⟨3178925, by rfl⟩ : syracuseStep 4238567 = 6357851) B6357851
theorem B2825711 : Blo 1883435 2825711 := bstep (se 1 (by rfl) ⟨2119283, by rfl⟩ : syracuseStep 2825711 = 4238567) B4238567
theorem B1883807 : Blo 1883435 1883807 := bstep (se 1 (by rfl) ⟨1412855, by rfl⟩ : syracuseStep 1883807 = 2825711) B2825711
theorem B2825717 : Blo 1883435 2825717 := bbase (se 5 (by rfl) ⟨132455, by rfl⟩ : syracuseStep 2825717 = 264911) (by norm_num)
theorem B1883811 : Blo 1883435 1883811 := bstep (se 1 (by rfl) ⟨1412858, by rfl⟩ : syracuseStep 1883811 = 2825717) B2825717
theorem B2011673 : Blo 1883435 2011673 := bbase (se 2 (by rfl) ⟨754377, by rfl⟩ : syracuseStep 2011673 = 1508755) (by norm_num)
theorem B5364461 : Blo 1883435 5364461 := bstep (se 3 (by rfl) ⟨1005836, by rfl⟩ : syracuseStep 5364461 = 2011673) B2011673
theorem B3576307 : Blo 1883435 3576307 := bstep (se 1 (by rfl) ⟨2682230, by rfl⟩ : syracuseStep 3576307 = 5364461) B5364461
theorem B4768409 : Blo 1883435 4768409 := bstep (se 2 (by rfl) ⟨1788153, by rfl⟩ : syracuseStep 4768409 = 3576307) B3576307
theorem B3178939 : Blo 1883435 3178939 := bstep (se 1 (by rfl) ⟨2384204, by rfl⟩ : syracuseStep 3178939 = 4768409) B4768409
theorem B4238585 : Blo 1883435 4238585 := bstep (se 2 (by rfl) ⟨1589469, by rfl⟩ : syracuseStep 4238585 = 3178939) B3178939
theorem B2825723 : Blo 1883435 2825723 := bstep (se 1 (by rfl) ⟨2119292, by rfl⟩ : syracuseStep 2825723 = 4238585) B4238585
theorem B1883815 : Blo 1883435 1883815 := bstep (se 1 (by rfl) ⟨1412861, by rfl⟩ : syracuseStep 1883815 = 2825723) B2825723
theorem B2119297 : Blo 1883435 2119297 := bbase (se 2 (by rfl) ⟨794736, by rfl⟩ : syracuseStep 2119297 = 1589473) (by norm_num)
theorem B2825729 : Blo 1883435 2825729 := bstep (se 2 (by rfl) ⟨1059648, by rfl⟩ : syracuseStep 2825729 = 2119297) B2119297
theorem B1883819 : Blo 1883435 1883819 := bstep (se 1 (by rfl) ⟨1412864, by rfl⟩ : syracuseStep 1883819 = 2825729) B2825729
theorem B4768429 : Blo 1883435 4768429 := bbase (se 3 (by rfl) ⟨894080, by rfl⟩ : syracuseStep 4768429 = 1788161) (by norm_num)
theorem B6357905 : Blo 1883435 6357905 := bstep (se 2 (by rfl) ⟨2384214, by rfl⟩ : syracuseStep 6357905 = 4768429) B4768429
theorem B4238603 : Blo 1883435 4238603 := bstep (se 1 (by rfl) ⟨3178952, by rfl⟩ : syracuseStep 4238603 = 6357905) B6357905
theorem B2825735 : Blo 1883435 2825735 := bstep (se 1 (by rfl) ⟨2119301, by rfl⟩ : syracuseStep 2825735 = 4238603) B4238603
theorem B1883823 : Blo 1883435 1883823 := bstep (se 1 (by rfl) ⟨1412867, by rfl⟩ : syracuseStep 1883823 = 2825735) B2825735
theorem B2825741 : Blo 1883435 2825741 := bbase (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) (by norm_num)
theorem B1883827 : Blo 1883435 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B4238621 : Blo 1883435 4238621 := bbase (se 3 (by rfl) ⟨794741, by rfl⟩ : syracuseStep 4238621 = 1589483) (by norm_num)
theorem B2825747 : Blo 1883435 2825747 := bstep (se 1 (by rfl) ⟨2119310, by rfl⟩ : syracuseStep 2825747 = 4238621) B4238621
theorem B1883831 : Blo 1883435 1883831 := bstep (se 1 (by rfl) ⟨1412873, by rfl⟩ : syracuseStep 1883831 = 2825747) B2825747
theorem B3178973 : Blo 1883435 3178973 := bbase (se 3 (by rfl) ⟨596057, by rfl⟩ : syracuseStep 3178973 = 1192115) (by norm_num)
theorem B2119315 : Blo 1883435 2119315 := bstep (se 1 (by rfl) ⟨1589486, by rfl⟩ : syracuseStep 2119315 = 3178973) B3178973
theorem B2825753 : Blo 1883435 2825753 := bstep (se 2 (by rfl) ⟨1059657, by rfl⟩ : syracuseStep 2825753 = 2119315) B2119315
theorem B1883835 : Blo 1883435 1883835 := bstep (se 1 (by rfl) ⟨1412876, by rfl⟩ : syracuseStep 1883835 = 2825753) B2825753
theorem B13578965 : Blo 1883435 13578965 := bbase (se 7 (by rfl) ⟨159128, by rfl⟩ : syracuseStep 13578965 = 318257) (by norm_num)
theorem B9052643 : Blo 1883435 9052643 := bstep (se 1 (by rfl) ⟨6789482, by rfl⟩ : syracuseStep 9052643 = 13578965) B13578965
theorem B6035095 : Blo 1883435 6035095 := bstep (se 1 (by rfl) ⟨4526321, by rfl⟩ : syracuseStep 6035095 = 9052643) B9052643
theorem B8046793 : Blo 1883435 8046793 := bstep (se 2 (by rfl) ⟨3017547, by rfl⟩ : syracuseStep 8046793 = 6035095) B6035095
theorem B10729057 : Blo 1883435 10729057 := bstep (se 2 (by rfl) ⟨4023396, by rfl⟩ : syracuseStep 10729057 = 8046793) B8046793
theorem B14305409 : Blo 1883435 14305409 := bstep (se 2 (by rfl) ⟨5364528, by rfl⟩ : syracuseStep 14305409 = 10729057) B10729057
theorem B9536939 : Blo 1883435 9536939 := bstep (se 1 (by rfl) ⟨7152704, by rfl⟩ : syracuseStep 9536939 = 14305409) B14305409
theorem B6357959 : Blo 1883435 6357959 := bstep (se 1 (by rfl) ⟨4768469, by rfl⟩ : syracuseStep 6357959 = 9536939) B9536939
theorem B4238639 : Blo 1883435 4238639 := bstep (se 1 (by rfl) ⟨3178979, by rfl⟩ : syracuseStep 4238639 = 6357959) B6357959
theorem B2825759 : Blo 1883435 2825759 := bstep (se 1 (by rfl) ⟨2119319, by rfl⟩ : syracuseStep 2825759 = 4238639) B4238639
theorem B1883839 : Blo 1883435 1883839 := bstep (se 1 (by rfl) ⟨1412879, by rfl⟩ : syracuseStep 1883839 = 2825759) B2825759
theorem B2825765 : Blo 1883435 2825765 := bbase (se 4 (by rfl) ⟨264915, by rfl⟩ : syracuseStep 2825765 = 529831) (by norm_num)
theorem B1883843 : Blo 1883435 1883843 := bstep (se 1 (by rfl) ⟨1412882, by rfl⟩ : syracuseStep 1883843 = 2825765) B2825765
theorem B2384245 : Blo 1883435 2384245 := bbase (se 5 (by rfl) ⟨111761, by rfl⟩ : syracuseStep 2384245 = 223523) (by norm_num)
theorem B3178993 : Blo 1883435 3178993 := bstep (se 2 (by rfl) ⟨1192122, by rfl⟩ : syracuseStep 3178993 = 2384245) B2384245
theorem B4238657 : Blo 1883435 4238657 := bstep (se 2 (by rfl) ⟨1589496, by rfl⟩ : syracuseStep 4238657 = 3178993) B3178993
theorem B2825771 : Blo 1883435 2825771 := bstep (se 1 (by rfl) ⟨2119328, by rfl⟩ : syracuseStep 2825771 = 4238657) B4238657
theorem B1883847 : Blo 1883435 1883847 := bstep (se 1 (by rfl) ⟨1412885, by rfl⟩ : syracuseStep 1883847 = 2825771) B2825771
theorem B2119333 : Blo 1883435 2119333 := bbase (se 4 (by rfl) ⟨198687, by rfl⟩ : syracuseStep 2119333 = 397375) (by norm_num)
theorem B2825777 : Blo 1883435 2825777 := bstep (se 2 (by rfl) ⟨1059666, by rfl⟩ : syracuseStep 2825777 = 2119333) B2119333
theorem B1883851 : Blo 1883435 1883851 := bstep (se 1 (by rfl) ⟨1412888, by rfl⟩ : syracuseStep 1883851 = 2825777) B2825777
theorem B27158165 : Blo 1883435 27158165 := bbase (se 6 (by rfl) ⟨636519, by rfl⟩ : syracuseStep 27158165 = 1273039) (by norm_num)
theorem B18105443 : Blo 1883435 18105443 := bstep (se 1 (by rfl) ⟨13579082, by rfl⟩ : syracuseStep 18105443 = 27158165) B27158165
theorem B12070295 : Blo 1883435 12070295 := bstep (se 1 (by rfl) ⟨9052721, by rfl⟩ : syracuseStep 12070295 = 18105443) B18105443
theorem B8046863 : Blo 1883435 8046863 := bstep (se 1 (by rfl) ⟨6035147, by rfl⟩ : syracuseStep 8046863 = 12070295) B12070295
theorem B5364575 : Blo 1883435 5364575 := bstep (se 1 (by rfl) ⟨4023431, by rfl⟩ : syracuseStep 5364575 = 8046863) B8046863
theorem B3576383 : Blo 1883435 3576383 := bstep (se 1 (by rfl) ⟨2682287, by rfl⟩ : syracuseStep 3576383 = 5364575) B5364575
theorem B2384255 : Blo 1883435 2384255 := bstep (se 1 (by rfl) ⟨1788191, by rfl⟩ : syracuseStep 2384255 = 3576383) B3576383
theorem B6358013 : Blo 1883435 6358013 := bstep (se 3 (by rfl) ⟨1192127, by rfl⟩ : syracuseStep 6358013 = 2384255) B2384255
theorem B4238675 : Blo 1883435 4238675 := bstep (se 1 (by rfl) ⟨3179006, by rfl⟩ : syracuseStep 4238675 = 6358013) B6358013
theorem B2825783 : Blo 1883435 2825783 := bstep (se 1 (by rfl) ⟨2119337, by rfl⟩ : syracuseStep 2825783 = 4238675) B4238675
theorem B1883855 : Blo 1883435 1883855 := bstep (se 1 (by rfl) ⟨1412891, by rfl⟩ : syracuseStep 1883855 = 2825783) B2825783
theorem B2825789 : Blo 1883435 2825789 := bbase (se 3 (by rfl) ⟨529835, by rfl⟩ : syracuseStep 2825789 = 1059671) (by norm_num)
theorem B1883859 : Blo 1883435 1883859 := bstep (se 1 (by rfl) ⟨1412894, by rfl⟩ : syracuseStep 1883859 = 2825789) B2825789
theorem B4238693 : Blo 1883435 4238693 := bbase (se 4 (by rfl) ⟨397377, by rfl⟩ : syracuseStep 4238693 = 794755) (by norm_num)
theorem B2825795 : Blo 1883435 2825795 := bstep (se 1 (by rfl) ⟨2119346, by rfl⟩ : syracuseStep 2825795 = 4238693) B4238693
theorem B1883863 : Blo 1883435 1883863 := bstep (se 1 (by rfl) ⟨1412897, by rfl⟩ : syracuseStep 1883863 = 2825795) B2825795
theorem B4768541 : Blo 1883435 4768541 := bbase (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) (by norm_num)
theorem B3179027 : Blo 1883435 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B2119351 : Blo 1883435 2119351 := bstep (se 1 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 2119351 = 3179027) B3179027
theorem B2825801 : Blo 1883435 2825801 := bstep (se 2 (by rfl) ⟨1059675, by rfl⟩ : syracuseStep 2825801 = 2119351) B2119351
theorem B1883867 : Blo 1883435 1883867 := bstep (se 1 (by rfl) ⟨1412900, by rfl⟩ : syracuseStep 1883867 = 2825801) B2825801
theorem B3576413 : Blo 1883435 3576413 := bbase (se 3 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 3576413 = 1341155) (by norm_num)
theorem B9537101 : Blo 1883435 9537101 := bstep (se 3 (by rfl) ⟨1788206, by rfl⟩ : syracuseStep 9537101 = 3576413) B3576413
theorem B6358067 : Blo 1883435 6358067 := bstep (se 1 (by rfl) ⟨4768550, by rfl⟩ : syracuseStep 6358067 = 9537101) B9537101
theorem B4238711 : Blo 1883435 4238711 := bstep (se 1 (by rfl) ⟨3179033, by rfl⟩ : syracuseStep 4238711 = 6358067) B6358067
theorem B2825807 : Blo 1883435 2825807 := bstep (se 1 (by rfl) ⟨2119355, by rfl⟩ : syracuseStep 2825807 = 4238711) B4238711
theorem B1883871 : Blo 1883435 1883871 := bstep (se 1 (by rfl) ⟨1412903, by rfl⟩ : syracuseStep 1883871 = 2825807) B2825807
theorem B2825813 : Blo 1883435 2825813 := bbase (se 8 (by rfl) ⟨16557, by rfl⟩ : syracuseStep 2825813 = 33115) (by norm_num)
theorem B1883875 : Blo 1883435 1883875 := bstep (se 1 (by rfl) ⟨1412906, by rfl⟩ : syracuseStep 1883875 = 2825813) B2825813
theorem B8046965 : Blo 1883435 8046965 := bbase (se 5 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 8046965 = 754403) (by norm_num)
theorem B5364643 : Blo 1883435 5364643 := bstep (se 1 (by rfl) ⟨4023482, by rfl⟩ : syracuseStep 5364643 = 8046965) B8046965
theorem B7152857 : Blo 1883435 7152857 := bstep (se 2 (by rfl) ⟨2682321, by rfl⟩ : syracuseStep 7152857 = 5364643) B5364643
theorem B4768571 : Blo 1883435 4768571 := bstep (se 1 (by rfl) ⟨3576428, by rfl⟩ : syracuseStep 4768571 = 7152857) B7152857
theorem B3179047 : Blo 1883435 3179047 := bstep (se 1 (by rfl) ⟨2384285, by rfl⟩ : syracuseStep 3179047 = 4768571) B4768571
theorem B4238729 : Blo 1883435 4238729 := bstep (se 2 (by rfl) ⟨1589523, by rfl⟩ : syracuseStep 4238729 = 3179047) B3179047
theorem B2825819 : Blo 1883435 2825819 := bstep (se 1 (by rfl) ⟨2119364, by rfl⟩ : syracuseStep 2825819 = 4238729) B4238729
theorem B1883879 : Blo 1883435 1883879 := bstep (se 1 (by rfl) ⟨1412909, by rfl⟩ : syracuseStep 1883879 = 2825819) B2825819
theorem B2119369 : Blo 1883435 2119369 := bbase (se 2 (by rfl) ⟨794763, by rfl⟩ : syracuseStep 2119369 = 1589527) (by norm_num)
theorem B2825825 : Blo 1883435 2825825 := bstep (se 2 (by rfl) ⟨1059684, by rfl⟩ : syracuseStep 2825825 = 2119369) B2119369
theorem B1883883 : Blo 1883435 1883883 := bstep (se 1 (by rfl) ⟨1412912, by rfl⟩ : syracuseStep 1883883 = 2825825) B2825825
theorem B4526437 : Blo 1883435 4526437 := bbase (se 4 (by rfl) ⟨424353, by rfl⟩ : syracuseStep 4526437 = 848707) (by norm_num)
theorem B6035249 : Blo 1883435 6035249 := bstep (se 2 (by rfl) ⟨2263218, by rfl⟩ : syracuseStep 6035249 = 4526437) B4526437
theorem B16093997 : Blo 1883435 16093997 := bstep (se 3 (by rfl) ⟨3017624, by rfl⟩ : syracuseStep 16093997 = 6035249) B6035249
theorem B10729331 : Blo 1883435 10729331 := bstep (se 1 (by rfl) ⟨8046998, by rfl⟩ : syracuseStep 10729331 = 16093997) B16093997
theorem B7152887 : Blo 1883435 7152887 := bstep (se 1 (by rfl) ⟨5364665, by rfl⟩ : syracuseStep 7152887 = 10729331) B10729331
theorem B4768591 : Blo 1883435 4768591 := bstep (se 1 (by rfl) ⟨3576443, by rfl⟩ : syracuseStep 4768591 = 7152887) B7152887
theorem B6358121 : Blo 1883435 6358121 := bstep (se 2 (by rfl) ⟨2384295, by rfl⟩ : syracuseStep 6358121 = 4768591) B4768591
theorem B4238747 : Blo 1883435 4238747 := bstep (se 1 (by rfl) ⟨3179060, by rfl⟩ : syracuseStep 4238747 = 6358121) B6358121
theorem B2825831 : Blo 1883435 2825831 := bstep (se 1 (by rfl) ⟨2119373, by rfl⟩ : syracuseStep 2825831 = 4238747) B4238747
theorem B1883887 : Blo 1883435 1883887 := bstep (se 1 (by rfl) ⟨1412915, by rfl⟩ : syracuseStep 1883887 = 2825831) B2825831
theorem B2825837 : Blo 1883435 2825837 := bbase (se 3 (by rfl) ⟨529844, by rfl⟩ : syracuseStep 2825837 = 1059689) (by norm_num)
theorem B1883891 : Blo 1883435 1883891 := bstep (se 1 (by rfl) ⟨1412918, by rfl⟩ : syracuseStep 1883891 = 2825837) B2825837
theorem B4238765 : Blo 1883435 4238765 := bbase (se 3 (by rfl) ⟨794768, by rfl⟩ : syracuseStep 4238765 = 1589537) (by norm_num)
theorem B2825843 : Blo 1883435 2825843 := bstep (se 1 (by rfl) ⟨2119382, by rfl⟩ : syracuseStep 2825843 = 4238765) B4238765
theorem B1883895 : Blo 1883435 1883895 := bstep (se 1 (by rfl) ⟨1412921, by rfl⟩ : syracuseStep 1883895 = 2825843) B2825843
theorem B3017645 : Blo 1883435 3017645 := bbase (se 3 (by rfl) ⟨565808, by rfl⟩ : syracuseStep 3017645 = 1131617) (by norm_num)
theorem B2011763 : Blo 1883435 2011763 := bstep (se 1 (by rfl) ⟨1508822, by rfl⟩ : syracuseStep 2011763 = 3017645) B3017645
theorem B5364701 : Blo 1883435 5364701 := bstep (se 3 (by rfl) ⟨1005881, by rfl⟩ : syracuseStep 5364701 = 2011763) B2011763
theorem B3576467 : Blo 1883435 3576467 := bstep (se 1 (by rfl) ⟨2682350, by rfl⟩ : syracuseStep 3576467 = 5364701) B5364701
theorem B2384311 : Blo 1883435 2384311 := bstep (se 1 (by rfl) ⟨1788233, by rfl⟩ : syracuseStep 2384311 = 3576467) B3576467
theorem B3179081 : Blo 1883435 3179081 := bstep (se 2 (by rfl) ⟨1192155, by rfl⟩ : syracuseStep 3179081 = 2384311) B2384311
theorem B2119387 : Blo 1883435 2119387 := bstep (se 1 (by rfl) ⟨1589540, by rfl⟩ : syracuseStep 2119387 = 3179081) B3179081
theorem B2825849 : Blo 1883435 2825849 := bstep (se 2 (by rfl) ⟨1059693, by rfl⟩ : syracuseStep 2825849 = 2119387) B2119387
theorem B1883899 : Blo 1883435 1883899 := bstep (se 1 (by rfl) ⟨1412924, by rfl⟩ : syracuseStep 1883899 = 2825849) B2825849
theorem B15276853 : Blo 1883435 15276853 := bbase (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) (by norm_num)
theorem B81476549 : Blo 1883435 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B54317699 : Blo 1883435 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B36211799 : Blo 1883435 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B24141199 : Blo 1883435 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B32188265 : Blo 1883435 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B21458843 : Blo 1883435 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B14305895 : Blo 1883435 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B9537263 : Blo 1883435 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B6358175 : Blo 1883435 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B4238783 : Blo 1883435 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B2825855 : Blo 1883435 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B1883903 : Blo 1883435 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B2825861 : Blo 1883435 2825861 := bbase (se 4 (by rfl) ⟨264924, by rfl⟩ : syracuseStep 2825861 = 529849) (by norm_num)
theorem B1883907 : Blo 1883435 1883907 := bstep (se 1 (by rfl) ⟨1412930, by rfl⟩ : syracuseStep 1883907 = 2825861) B2825861
theorem B3179101 : Blo 1883435 3179101 := bbase (se 3 (by rfl) ⟨596081, by rfl⟩ : syracuseStep 3179101 = 1192163) (by norm_num)
theorem B4238801 : Blo 1883435 4238801 := bstep (se 2 (by rfl) ⟨1589550, by rfl⟩ : syracuseStep 4238801 = 3179101) B3179101
theorem B2825867 : Blo 1883435 2825867 := bstep (se 1 (by rfl) ⟨2119400, by rfl⟩ : syracuseStep 2825867 = 4238801) B4238801
theorem B1883911 : Blo 1883435 1883911 := bstep (se 1 (by rfl) ⟨1412933, by rfl⟩ : syracuseStep 1883911 = 2825867) B2825867
theorem B2119405 : Blo 1883435 2119405 := bbase (se 3 (by rfl) ⟨397388, by rfl⟩ : syracuseStep 2119405 = 794777) (by norm_num)
theorem B2825873 : Blo 1883435 2825873 := bstep (se 2 (by rfl) ⟨1059702, by rfl⟩ : syracuseStep 2825873 = 2119405) B2119405
theorem B1883915 : Blo 1883435 1883915 := bstep (se 1 (by rfl) ⟨1412936, by rfl⟩ : syracuseStep 1883915 = 2825873) B2825873
theorem B6358229 : Blo 1883435 6358229 := bbase (se 7 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 6358229 = 149021) (by norm_num)
theorem B4238819 : Blo 1883435 4238819 := bstep (se 1 (by rfl) ⟨3179114, by rfl⟩ : syracuseStep 4238819 = 6358229) B6358229
theorem B2825879 : Blo 1883435 2825879 := bstep (se 1 (by rfl) ⟨2119409, by rfl⟩ : syracuseStep 2825879 = 4238819) B4238819
theorem B1883919 : Blo 1883435 1883919 := bstep (se 1 (by rfl) ⟨1412939, by rfl⟩ : syracuseStep 1883919 = 2825879) B2825879
theorem B2825885 : Blo 1883435 2825885 := bbase (se 3 (by rfl) ⟨529853, by rfl⟩ : syracuseStep 2825885 = 1059707) (by norm_num)
theorem B1883923 : Blo 1883435 1883923 := bstep (se 1 (by rfl) ⟨1412942, by rfl⟩ : syracuseStep 1883923 = 2825885) B2825885
theorem B4238837 : Blo 1883435 4238837 := bbase (se 5 (by rfl) ⟨198695, by rfl⟩ : syracuseStep 4238837 = 397391) (by norm_num)
theorem B2825891 : Blo 1883435 2825891 := bstep (se 1 (by rfl) ⟨2119418, by rfl⟩ : syracuseStep 2825891 = 4238837) B4238837
theorem B1883927 : Blo 1883435 1883927 := bstep (se 1 (by rfl) ⟨1412945, by rfl⟩ : syracuseStep 1883927 = 2825891) B2825891
theorem B3266477 : Blo 1883435 3266477 := bbase (se 3 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 3266477 = 1224929) (by norm_num)
theorem B2177651 : Blo 1883435 2177651 := bstep (se 1 (by rfl) ⟨1633238, by rfl⟩ : syracuseStep 2177651 = 3266477) B3266477
theorem B5807069 : Blo 1883435 5807069 := bstep (se 3 (by rfl) ⟨1088825, by rfl⟩ : syracuseStep 5807069 = 2177651) B2177651
theorem B3871379 : Blo 1883435 3871379 := bstep (se 1 (by rfl) ⟨2903534, by rfl⟩ : syracuseStep 3871379 = 5807069) B5807069
theorem B2580919 : Blo 1883435 2580919 := bstep (se 1 (by rfl) ⟨1935689, by rfl⟩ : syracuseStep 2580919 = 3871379) B3871379
theorem B55059605 : Blo 1883435 55059605 := bstep (se 6 (by rfl) ⟨1290459, by rfl⟩ : syracuseStep 55059605 = 2580919) B2580919
theorem B36706403 : Blo 1883435 36706403 := bstep (se 1 (by rfl) ⟨27529802, by rfl⟩ : syracuseStep 36706403 = 55059605) B55059605
theorem B97883741 : Blo 1883435 97883741 := bstep (se 3 (by rfl) ⟨18353201, by rfl⟩ : syracuseStep 97883741 = 36706403) B36706403
theorem B65255827 : Blo 1883435 65255827 := bstep (se 1 (by rfl) ⟨48941870, by rfl⟩ : syracuseStep 65255827 = 97883741) B97883741
theorem B87007769 : Blo 1883435 87007769 := bstep (se 2 (by rfl) ⟨32627913, by rfl⟩ : syracuseStep 87007769 = 65255827) B65255827
theorem B58005179 : Blo 1883435 58005179 := bstep (se 1 (by rfl) ⟨43503884, by rfl⟩ : syracuseStep 58005179 = 87007769) B87007769
theorem B38670119 : Blo 1883435 38670119 := bstep (se 1 (by rfl) ⟨29002589, by rfl⟩ : syracuseStep 38670119 = 58005179) B58005179
theorem B25780079 : Blo 1883435 25780079 := bstep (se 1 (by rfl) ⟨19335059, by rfl⟩ : syracuseStep 25780079 = 38670119) B38670119
theorem B68746877 : Blo 1883435 68746877 := bstep (se 3 (by rfl) ⟨12890039, by rfl⟩ : syracuseStep 68746877 = 25780079) B25780079
theorem B45831251 : Blo 1883435 45831251 := bstep (se 1 (by rfl) ⟨34373438, by rfl⟩ : syracuseStep 45831251 = 68746877) B68746877
theorem B30554167 : Blo 1883435 30554167 := bstep (se 1 (by rfl) ⟨22915625, by rfl⟩ : syracuseStep 30554167 = 45831251) B45831251
theorem B40738889 : Blo 1883435 40738889 := bstep (se 2 (by rfl) ⟨15277083, by rfl⟩ : syracuseStep 40738889 = 30554167) B30554167
theorem B27159259 : Blo 1883435 27159259 := bstep (se 1 (by rfl) ⟨20369444, by rfl⟩ : syracuseStep 27159259 = 40738889) B40738889
theorem B36212345 : Blo 1883435 36212345 := bstep (se 2 (by rfl) ⟨13579629, by rfl⟩ : syracuseStep 36212345 = 27159259) B27159259
theorem B24141563 : Blo 1883435 24141563 := bstep (se 1 (by rfl) ⟨18106172, by rfl⟩ : syracuseStep 24141563 = 36212345) B36212345
theorem B16094375 : Blo 1883435 16094375 := bstep (se 1 (by rfl) ⟨12070781, by rfl⟩ : syracuseStep 16094375 = 24141563) B24141563
theorem B10729583 : Blo 1883435 10729583 := bstep (se 1 (by rfl) ⟨8047187, by rfl⟩ : syracuseStep 10729583 = 16094375) B16094375
theorem B7153055 : Blo 1883435 7153055 := bstep (se 1 (by rfl) ⟨5364791, by rfl⟩ : syracuseStep 7153055 = 10729583) B10729583
theorem B4768703 : Blo 1883435 4768703 := bstep (se 1 (by rfl) ⟨3576527, by rfl⟩ : syracuseStep 4768703 = 7153055) B7153055
theorem B3179135 : Blo 1883435 3179135 := bstep (se 1 (by rfl) ⟨2384351, by rfl⟩ : syracuseStep 3179135 = 4768703) B4768703
theorem B2119423 : Blo 1883435 2119423 := bstep (se 1 (by rfl) ⟨1589567, by rfl⟩ : syracuseStep 2119423 = 3179135) B3179135
theorem B2825897 : Blo 1883435 2825897 := bstep (se 2 (by rfl) ⟨1059711, by rfl⟩ : syracuseStep 2825897 = 2119423) B2119423
theorem B1883931 : Blo 1883435 1883931 := bstep (se 1 (by rfl) ⟨1412948, by rfl⟩ : syracuseStep 1883931 = 2825897) B2825897
theorem B2011801 : Blo 1883435 2011801 := bbase (se 2 (by rfl) ⟨754425, by rfl⟩ : syracuseStep 2011801 = 1508851) (by norm_num)
theorem B2682401 : Blo 1883435 2682401 := bstep (se 2 (by rfl) ⟨1005900, by rfl⟩ : syracuseStep 2682401 = 2011801) B2011801
theorem B7153069 : Blo 1883435 7153069 := bstep (se 3 (by rfl) ⟨1341200, by rfl⟩ : syracuseStep 7153069 = 2682401) B2682401
theorem B9537425 : Blo 1883435 9537425 := bstep (se 2 (by rfl) ⟨3576534, by rfl⟩ : syracuseStep 9537425 = 7153069) B7153069
theorem B6358283 : Blo 1883435 6358283 := bstep (se 1 (by rfl) ⟨4768712, by rfl⟩ : syracuseStep 6358283 = 9537425) B9537425
theorem B4238855 : Blo 1883435 4238855 := bstep (se 1 (by rfl) ⟨3179141, by rfl⟩ : syracuseStep 4238855 = 6358283) B6358283
theorem B2825903 : Blo 1883435 2825903 := bstep (se 1 (by rfl) ⟨2119427, by rfl⟩ : syracuseStep 2825903 = 4238855) B4238855
theorem B1883935 : Blo 1883435 1883935 := bstep (se 1 (by rfl) ⟨1412951, by rfl⟩ : syracuseStep 1883935 = 2825903) B2825903
theorem B2825909 : Blo 1883435 2825909 := bbase (se 5 (by rfl) ⟨132464, by rfl⟩ : syracuseStep 2825909 = 264929) (by norm_num)
theorem B1883939 : Blo 1883435 1883939 := bstep (se 1 (by rfl) ⟨1412954, by rfl⟩ : syracuseStep 1883939 = 2825909) B2825909
theorem B4768733 : Blo 1883435 4768733 := bbase (se 3 (by rfl) ⟨894137, by rfl⟩ : syracuseStep 4768733 = 1788275) (by norm_num)
theorem B3179155 : Blo 1883435 3179155 := bstep (se 1 (by rfl) ⟨2384366, by rfl⟩ : syracuseStep 3179155 = 4768733) B4768733
theorem B4238873 : Blo 1883435 4238873 := bstep (se 2 (by rfl) ⟨1589577, by rfl⟩ : syracuseStep 4238873 = 3179155) B3179155
theorem B2825915 : Blo 1883435 2825915 := bstep (se 1 (by rfl) ⟨2119436, by rfl⟩ : syracuseStep 2825915 = 4238873) B4238873
theorem B1883943 : Blo 1883435 1883943 := bstep (se 1 (by rfl) ⟨1412957, by rfl⟩ : syracuseStep 1883943 = 2825915) B2825915
theorem B2119441 : Blo 1883435 2119441 := bbase (se 2 (by rfl) ⟨794790, by rfl⟩ : syracuseStep 2119441 = 1589581) (by norm_num)
theorem B2825921 : Blo 1883435 2825921 := bstep (se 2 (by rfl) ⟨1059720, by rfl⟩ : syracuseStep 2825921 = 2119441) B2119441
theorem B1883947 : Blo 1883435 1883947 := bstep (se 1 (by rfl) ⟨1412960, by rfl⟩ : syracuseStep 1883947 = 2825921) B2825921
theorem B3576565 : Blo 1883435 3576565 := bbase (se 5 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 3576565 = 335303) (by norm_num)
theorem B4768753 : Blo 1883435 4768753 := bstep (se 2 (by rfl) ⟨1788282, by rfl⟩ : syracuseStep 4768753 = 3576565) B3576565
theorem B6358337 : Blo 1883435 6358337 := bstep (se 2 (by rfl) ⟨2384376, by rfl⟩ : syracuseStep 6358337 = 4768753) B4768753
theorem B4238891 : Blo 1883435 4238891 := bstep (se 1 (by rfl) ⟨3179168, by rfl⟩ : syracuseStep 4238891 = 6358337) B6358337
theorem B2825927 : Blo 1883435 2825927 := bstep (se 1 (by rfl) ⟨2119445, by rfl⟩ : syracuseStep 2825927 = 4238891) B4238891
theorem B1883951 : Blo 1883435 1883951 := bstep (se 1 (by rfl) ⟨1412963, by rfl⟩ : syracuseStep 1883951 = 2825927) B2825927
theorem B2825933 : Blo 1883435 2825933 := bbase (se 3 (by rfl) ⟨529862, by rfl⟩ : syracuseStep 2825933 = 1059725) (by norm_num)
theorem B1883955 : Blo 1883435 1883955 := bstep (se 1 (by rfl) ⟨1412966, by rfl⟩ : syracuseStep 1883955 = 2825933) B2825933
theorem B4238909 : Blo 1883435 4238909 := bbase (se 3 (by rfl) ⟨794795, by rfl⟩ : syracuseStep 4238909 = 1589591) (by norm_num)
theorem B2825939 : Blo 1883435 2825939 := bstep (se 1 (by rfl) ⟨2119454, by rfl⟩ : syracuseStep 2825939 = 4238909) B4238909
theorem B1883959 : Blo 1883435 1883959 := bstep (se 1 (by rfl) ⟨1412969, by rfl⟩ : syracuseStep 1883959 = 2825939) B2825939
theorem B3179189 : Blo 1883435 3179189 := bbase (se 5 (by rfl) ⟨149024, by rfl⟩ : syracuseStep 3179189 = 298049) (by norm_num)
theorem B2119459 : Blo 1883435 2119459 := bstep (se 1 (by rfl) ⟨1589594, by rfl⟩ : syracuseStep 2119459 = 3179189) B3179189
theorem B2825945 : Blo 1883435 2825945 := bstep (se 2 (by rfl) ⟨1059729, by rfl⟩ : syracuseStep 2825945 = 2119459) B2119459
theorem B1883963 : Blo 1883435 1883963 := bstep (se 1 (by rfl) ⟨1412972, by rfl⟩ : syracuseStep 1883963 = 2825945) B2825945
theorem B3394973 : Blo 1883435 3394973 := bbase (se 3 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 3394973 = 1273115) (by norm_num)
theorem B2263315 : Blo 1883435 2263315 := bstep (se 1 (by rfl) ⟨1697486, by rfl⟩ : syracuseStep 2263315 = 3394973) B3394973
theorem B3017753 : Blo 1883435 3017753 := bstep (se 2 (by rfl) ⟨1131657, by rfl⟩ : syracuseStep 3017753 = 2263315) B2263315
theorem B2011835 : Blo 1883435 2011835 := bstep (se 1 (by rfl) ⟨1508876, by rfl⟩ : syracuseStep 2011835 = 3017753) B3017753
theorem B5364893 : Blo 1883435 5364893 := bstep (se 3 (by rfl) ⟨1005917, by rfl⟩ : syracuseStep 5364893 = 2011835) B2011835
theorem B14306381 : Blo 1883435 14306381 := bstep (se 3 (by rfl) ⟨2682446, by rfl⟩ : syracuseStep 14306381 = 5364893) B5364893
theorem B9537587 : Blo 1883435 9537587 := bstep (se 1 (by rfl) ⟨7153190, by rfl⟩ : syracuseStep 9537587 = 14306381) B14306381
theorem B6358391 : Blo 1883435 6358391 := bstep (se 1 (by rfl) ⟨4768793, by rfl⟩ : syracuseStep 6358391 = 9537587) B9537587
theorem B4238927 : Blo 1883435 4238927 := bstep (se 1 (by rfl) ⟨3179195, by rfl⟩ : syracuseStep 4238927 = 6358391) B6358391
theorem B2825951 : Blo 1883435 2825951 := bstep (se 1 (by rfl) ⟨2119463, by rfl⟩ : syracuseStep 2825951 = 4238927) B4238927
theorem B1883967 : Blo 1883435 1883967 := bstep (se 1 (by rfl) ⟨1412975, by rfl⟩ : syracuseStep 1883967 = 2825951) B2825951
theorem B2825957 : Blo 1883435 2825957 := bbase (se 4 (by rfl) ⟨264933, by rfl⟩ : syracuseStep 2825957 = 529867) (by norm_num)
theorem B1883971 : Blo 1883435 1883971 := bstep (se 1 (by rfl) ⟨1412978, by rfl⟩ : syracuseStep 1883971 = 2825957) B2825957
theorem B5364917 : Blo 1883435 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B3576611 : Blo 1883435 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B2384407 : Blo 1883435 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B3179209 : Blo 1883435 3179209 := bstep (se 2 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 3179209 = 2384407) B2384407
theorem B4238945 : Blo 1883435 4238945 := bstep (se 2 (by rfl) ⟨1589604, by rfl⟩ : syracuseStep 4238945 = 3179209) B3179209
theorem B2825963 : Blo 1883435 2825963 := bstep (se 1 (by rfl) ⟨2119472, by rfl⟩ : syracuseStep 2825963 = 4238945) B4238945
theorem B1883975 : Blo 1883435 1883975 := bstep (se 1 (by rfl) ⟨1412981, by rfl⟩ : syracuseStep 1883975 = 2825963) B2825963
theorem B2119477 : Blo 1883435 2119477 := bbase (se 5 (by rfl) ⟨99350, by rfl⟩ : syracuseStep 2119477 = 198701) (by norm_num)
theorem B2825969 : Blo 1883435 2825969 := bstep (se 2 (by rfl) ⟨1059738, by rfl⟩ : syracuseStep 2825969 = 2119477) B2119477
theorem B1883979 : Blo 1883435 1883979 := bstep (se 1 (by rfl) ⟨1412984, by rfl⟩ : syracuseStep 1883979 = 2825969) B2825969
theorem B2384417 : Blo 1883435 2384417 := bbase (se 2 (by rfl) ⟨894156, by rfl⟩ : syracuseStep 2384417 = 1788313) (by norm_num)
theorem B6358445 : Blo 1883435 6358445 := bstep (se 3 (by rfl) ⟨1192208, by rfl⟩ : syracuseStep 6358445 = 2384417) B2384417
theorem B4238963 : Blo 1883435 4238963 := bstep (se 1 (by rfl) ⟨3179222, by rfl⟩ : syracuseStep 4238963 = 6358445) B6358445
theorem B2825975 : Blo 1883435 2825975 := bstep (se 1 (by rfl) ⟨2119481, by rfl⟩ : syracuseStep 2825975 = 4238963) B4238963
theorem B1883983 : Blo 1883435 1883983 := bstep (se 1 (by rfl) ⟨1412987, by rfl⟩ : syracuseStep 1883983 = 2825975) B2825975
theorem B2825981 : Blo 1883435 2825981 := bbase (se 3 (by rfl) ⟨529871, by rfl⟩ : syracuseStep 2825981 = 1059743) (by norm_num)
theorem B1883987 : Blo 1883435 1883987 := bstep (se 1 (by rfl) ⟨1412990, by rfl⟩ : syracuseStep 1883987 = 2825981) B2825981
theorem B4238981 : Blo 1883435 4238981 := bbase (se 4 (by rfl) ⟨397404, by rfl⟩ : syracuseStep 4238981 = 794809) (by norm_num)
theorem B2825987 : Blo 1883435 2825987 := bstep (se 1 (by rfl) ⟨2119490, by rfl⟩ : syracuseStep 2825987 = 4238981) B4238981
theorem B1883991 : Blo 1883435 1883991 := bstep (se 1 (by rfl) ⟨1412993, by rfl⟩ : syracuseStep 1883991 = 2825987) B2825987
theorem B2263349 : Blo 1883435 2263349 := bbase (se 5 (by rfl) ⟨106094, by rfl⟩ : syracuseStep 2263349 = 212189) (by norm_num)
theorem B6035597 : Blo 1883435 6035597 := bstep (se 3 (by rfl) ⟨1131674, by rfl⟩ : syracuseStep 6035597 = 2263349) B2263349
theorem B4023731 : Blo 1883435 4023731 := bstep (se 1 (by rfl) ⟨3017798, by rfl⟩ : syracuseStep 4023731 = 6035597) B6035597
theorem B2682487 : Blo 1883435 2682487 := bstep (se 1 (by rfl) ⟨2011865, by rfl⟩ : syracuseStep 2682487 = 4023731) B4023731
theorem B3576649 : Blo 1883435 3576649 := bstep (se 2 (by rfl) ⟨1341243, by rfl⟩ : syracuseStep 3576649 = 2682487) B2682487
theorem B4768865 : Blo 1883435 4768865 := bstep (se 2 (by rfl) ⟨1788324, by rfl⟩ : syracuseStep 4768865 = 3576649) B3576649
theorem B3179243 : Blo 1883435 3179243 := bstep (se 1 (by rfl) ⟨2384432, by rfl⟩ : syracuseStep 3179243 = 4768865) B4768865
theorem B2119495 : Blo 1883435 2119495 := bstep (se 1 (by rfl) ⟨1589621, by rfl⟩ : syracuseStep 2119495 = 3179243) B3179243
theorem B2825993 : Blo 1883435 2825993 := bstep (se 2 (by rfl) ⟨1059747, by rfl⟩ : syracuseStep 2825993 = 2119495) B2119495
theorem B1883995 : Blo 1883435 1883995 := bstep (se 1 (by rfl) ⟨1412996, by rfl⟩ : syracuseStep 1883995 = 2825993) B2825993
theorem B9537749 : Blo 1883435 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B6358499 : Blo 1883435 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B4238999 : Blo 1883435 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B2825999 : Blo 1883435 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B1883999 : Blo 1883435 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B2826005 : Blo 1883435 2826005 := bbase (se 6 (by rfl) ⟨66234, by rfl⟩ : syracuseStep 2826005 = 132469) (by norm_num)
theorem B1884003 : Blo 1883435 1884003 := bstep (se 1 (by rfl) ⟨1413002, by rfl⟩ : syracuseStep 1884003 = 2826005) B2826005
theorem B4296853 : Blo 1883435 4296853 := bbase (se 6 (by rfl) ⟨100707, by rfl⟩ : syracuseStep 4296853 = 201415) (by norm_num)
theorem B5729137 : Blo 1883435 5729137 := bstep (se 2 (by rfl) ⟨2148426, by rfl⟩ : syracuseStep 5729137 = 4296853) B4296853
theorem B30555397 : Blo 1883435 30555397 := bstep (se 4 (by rfl) ⟨2864568, by rfl⟩ : syracuseStep 30555397 = 5729137) B5729137
theorem B40740529 : Blo 1883435 40740529 := bstep (se 2 (by rfl) ⟨15277698, by rfl⟩ : syracuseStep 40740529 = 30555397) B30555397
theorem B54320705 : Blo 1883435 54320705 := bstep (se 2 (by rfl) ⟨20370264, by rfl⟩ : syracuseStep 54320705 = 40740529) B40740529
theorem B36213803 : Blo 1883435 36213803 := bstep (se 1 (by rfl) ⟨27160352, by rfl⟩ : syracuseStep 36213803 = 54320705) B54320705
theorem B24142535 : Blo 1883435 24142535 := bstep (se 1 (by rfl) ⟨18106901, by rfl⟩ : syracuseStep 24142535 = 36213803) B36213803
theorem B16095023 : Blo 1883435 16095023 := bstep (se 1 (by rfl) ⟨12071267, by rfl⟩ : syracuseStep 16095023 = 24142535) B24142535
theorem B10730015 : Blo 1883435 10730015 := bstep (se 1 (by rfl) ⟨8047511, by rfl⟩ : syracuseStep 10730015 = 16095023) B16095023
theorem B7153343 : Blo 1883435 7153343 := bstep (se 1 (by rfl) ⟨5365007, by rfl⟩ : syracuseStep 7153343 = 10730015) B10730015
theorem B4768895 : Blo 1883435 4768895 := bstep (se 1 (by rfl) ⟨3576671, by rfl⟩ : syracuseStep 4768895 = 7153343) B7153343
theorem B3179263 : Blo 1883435 3179263 := bstep (se 1 (by rfl) ⟨2384447, by rfl⟩ : syracuseStep 3179263 = 4768895) B4768895
theorem B4239017 : Blo 1883435 4239017 := bstep (se 2 (by rfl) ⟨1589631, by rfl⟩ : syracuseStep 4239017 = 3179263) B3179263
theorem B2826011 : Blo 1883435 2826011 := bstep (se 1 (by rfl) ⟨2119508, by rfl⟩ : syracuseStep 2826011 = 4239017) B4239017
theorem B1884007 : Blo 1883435 1884007 := bstep (se 1 (by rfl) ⟨1413005, by rfl⟩ : syracuseStep 1884007 = 2826011) B2826011
theorem B2119513 : Blo 1883435 2119513 := bbase (se 2 (by rfl) ⟨794817, by rfl⟩ : syracuseStep 2119513 = 1589635) (by norm_num)
theorem B2826017 : Blo 1883435 2826017 := bstep (se 2 (by rfl) ⟨1059756, by rfl⟩ : syracuseStep 2826017 = 2119513) B2119513
theorem B1884011 : Blo 1883435 1884011 := bstep (se 1 (by rfl) ⟨1413008, by rfl⟩ : syracuseStep 1884011 = 2826017) B2826017
theorem B4023773 : Blo 1883435 4023773 := bbase (se 3 (by rfl) ⟨754457, by rfl⟩ : syracuseStep 4023773 = 1508915) (by norm_num)
theorem B2682515 : Blo 1883435 2682515 := bstep (se 1 (by rfl) ⟨2011886, by rfl⟩ : syracuseStep 2682515 = 4023773) B4023773
theorem B7153373 : Blo 1883435 7153373 := bstep (se 3 (by rfl) ⟨1341257, by rfl⟩ : syracuseStep 7153373 = 2682515) B2682515
theorem B4768915 : Blo 1883435 4768915 := bstep (se 1 (by rfl) ⟨3576686, by rfl⟩ : syracuseStep 4768915 = 7153373) B7153373
theorem B6358553 : Blo 1883435 6358553 := bstep (se 2 (by rfl) ⟨2384457, by rfl⟩ : syracuseStep 6358553 = 4768915) B4768915
theorem B4239035 : Blo 1883435 4239035 := bstep (se 1 (by rfl) ⟨3179276, by rfl⟩ : syracuseStep 4239035 = 6358553) B6358553
theorem B2826023 : Blo 1883435 2826023 := bstep (se 1 (by rfl) ⟨2119517, by rfl⟩ : syracuseStep 2826023 = 4239035) B4239035
theorem B1884015 : Blo 1883435 1884015 := bstep (se 1 (by rfl) ⟨1413011, by rfl⟩ : syracuseStep 1884015 = 2826023) B2826023
theorem B2826029 : Blo 1883435 2826029 := bbase (se 3 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 2826029 = 1059761) (by norm_num)
theorem B1884019 : Blo 1883435 1884019 := bstep (se 1 (by rfl) ⟨1413014, by rfl⟩ : syracuseStep 1884019 = 2826029) B2826029
theorem B4239053 : Blo 1883435 4239053 := bbase (se 3 (by rfl) ⟨794822, by rfl⟩ : syracuseStep 4239053 = 1589645) (by norm_num)
theorem B2826035 : Blo 1883435 2826035 := bstep (se 1 (by rfl) ⟨2119526, by rfl⟩ : syracuseStep 2826035 = 4239053) B4239053
theorem B1884023 : Blo 1883435 1884023 := bstep (se 1 (by rfl) ⟨1413017, by rfl⟩ : syracuseStep 1884023 = 2826035) B2826035
theorem B2384473 : Blo 1883435 2384473 := bbase (se 2 (by rfl) ⟨894177, by rfl⟩ : syracuseStep 2384473 = 1788355) (by norm_num)
theorem B3179297 : Blo 1883435 3179297 := bstep (se 2 (by rfl) ⟨1192236, by rfl⟩ : syracuseStep 3179297 = 2384473) B2384473
theorem B2119531 : Blo 1883435 2119531 := bstep (se 1 (by rfl) ⟨1589648, by rfl⟩ : syracuseStep 2119531 = 3179297) B3179297
theorem B2826041 : Blo 1883435 2826041 := bstep (se 2 (by rfl) ⟨1059765, by rfl⟩ : syracuseStep 2826041 = 2119531) B2119531
theorem B1884027 : Blo 1883435 1884027 := bstep (se 1 (by rfl) ⟨1413020, by rfl⟩ : syracuseStep 1884027 = 2826041) B2826041
theorem B2039353 : Blo 1883435 2039353 := bbase (se 2 (by rfl) ⟨764757, by rfl⟩ : syracuseStep 2039353 = 1529515) (by norm_num)
theorem B43506197 : Blo 1883435 43506197 := bstep (se 6 (by rfl) ⟨1019676, by rfl⟩ : syracuseStep 43506197 = 2039353) B2039353
theorem B29004131 : Blo 1883435 29004131 := bstep (se 1 (by rfl) ⟨21753098, by rfl⟩ : syracuseStep 29004131 = 43506197) B43506197
theorem B19336087 : Blo 1883435 19336087 := bstep (se 1 (by rfl) ⟨14502065, by rfl⟩ : syracuseStep 19336087 = 29004131) B29004131
theorem B25781449 : Blo 1883435 25781449 := bstep (se 2 (by rfl) ⟨9668043, by rfl⟩ : syracuseStep 25781449 = 19336087) B19336087
theorem B34375265 : Blo 1883435 34375265 := bstep (se 2 (by rfl) ⟨12890724, by rfl⟩ : syracuseStep 34375265 = 25781449) B25781449
theorem B22916843 : Blo 1883435 22916843 := bstep (se 1 (by rfl) ⟨17187632, by rfl⟩ : syracuseStep 22916843 = 34375265) B34375265
theorem B15277895 : Blo 1883435 15277895 := bstep (se 1 (by rfl) ⟨11458421, by rfl⟩ : syracuseStep 15277895 = 22916843) B22916843
theorem B10185263 : Blo 1883435 10185263 := bstep (se 1 (by rfl) ⟨7638947, by rfl⟩ : syracuseStep 10185263 = 15277895) B15277895
theorem B6790175 : Blo 1883435 6790175 := bstep (se 1 (by rfl) ⟨5092631, by rfl⟩ : syracuseStep 6790175 = 10185263) B10185263
theorem B4526783 : Blo 1883435 4526783 := bstep (se 1 (by rfl) ⟨3395087, by rfl⟩ : syracuseStep 4526783 = 6790175) B6790175
theorem B3017855 : Blo 1883435 3017855 := bstep (se 1 (by rfl) ⟨2263391, by rfl⟩ : syracuseStep 3017855 = 4526783) B4526783
theorem B8047613 : Blo 1883435 8047613 := bstep (se 3 (by rfl) ⟨1508927, by rfl⟩ : syracuseStep 8047613 = 3017855) B3017855
theorem B21460301 : Blo 1883435 21460301 := bstep (se 3 (by rfl) ⟨4023806, by rfl⟩ : syracuseStep 21460301 = 8047613) B8047613
theorem B14306867 : Blo 1883435 14306867 := bstep (se 1 (by rfl) ⟨10730150, by rfl⟩ : syracuseStep 14306867 = 21460301) B21460301
theorem B9537911 : Blo 1883435 9537911 := bstep (se 1 (by rfl) ⟨7153433, by rfl⟩ : syracuseStep 9537911 = 14306867) B14306867
theorem B6358607 : Blo 1883435 6358607 := bstep (se 1 (by rfl) ⟨4768955, by rfl⟩ : syracuseStep 6358607 = 9537911) B9537911
theorem B4239071 : Blo 1883435 4239071 := bstep (se 1 (by rfl) ⟨3179303, by rfl⟩ : syracuseStep 4239071 = 6358607) B6358607
theorem B2826047 : Blo 1883435 2826047 := bstep (se 1 (by rfl) ⟨2119535, by rfl⟩ : syracuseStep 2826047 = 4239071) B4239071
theorem B1884031 : Blo 1883435 1884031 := bstep (se 1 (by rfl) ⟨1413023, by rfl⟩ : syracuseStep 1884031 = 2826047) B2826047
theorem B2826053 : Blo 1883435 2826053 := bbase (se 4 (by rfl) ⟨264942, by rfl⟩ : syracuseStep 2826053 = 529885) (by norm_num)
theorem B1884035 : Blo 1883435 1884035 := bstep (se 1 (by rfl) ⟨1413026, by rfl⟩ : syracuseStep 1884035 = 2826053) B2826053
theorem B3179317 : Blo 1883435 3179317 := bbase (se 5 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 3179317 = 298061) (by norm_num)
theorem B4239089 : Blo 1883435 4239089 := bstep (se 2 (by rfl) ⟨1589658, by rfl⟩ : syracuseStep 4239089 = 3179317) B3179317
theorem B2826059 : Blo 1883435 2826059 := bstep (se 1 (by rfl) ⟨2119544, by rfl⟩ : syracuseStep 2826059 = 4239089) B4239089
theorem B1884039 : Blo 1883435 1884039 := bstep (se 1 (by rfl) ⟨1413029, by rfl⟩ : syracuseStep 1884039 = 2826059) B2826059
theorem B2119549 : Blo 1883435 2119549 := bbase (se 3 (by rfl) ⟨397415, by rfl⟩ : syracuseStep 2119549 = 794831) (by norm_num)
theorem B2826065 : Blo 1883435 2826065 := bstep (se 2 (by rfl) ⟨1059774, by rfl⟩ : syracuseStep 2826065 = 2119549) B2119549
theorem B1884043 : Blo 1883435 1884043 := bstep (se 1 (by rfl) ⟨1413032, by rfl⟩ : syracuseStep 1884043 = 2826065) B2826065
theorem B6358661 : Blo 1883435 6358661 := bbase (se 4 (by rfl) ⟨596124, by rfl⟩ : syracuseStep 6358661 = 1192249) (by norm_num)
theorem B4239107 : Blo 1883435 4239107 := bstep (se 1 (by rfl) ⟨3179330, by rfl⟩ : syracuseStep 4239107 = 6358661) B6358661
theorem B2826071 : Blo 1883435 2826071 := bstep (se 1 (by rfl) ⟨2119553, by rfl⟩ : syracuseStep 2826071 = 4239107) B4239107
theorem B1884047 : Blo 1883435 1884047 := bstep (se 1 (by rfl) ⟨1413035, by rfl⟩ : syracuseStep 1884047 = 2826071) B2826071
theorem B2826077 : Blo 1883435 2826077 := bbase (se 3 (by rfl) ⟨529889, by rfl⟩ : syracuseStep 2826077 = 1059779) (by norm_num)
theorem B1884051 : Blo 1883435 1884051 := bstep (se 1 (by rfl) ⟨1413038, by rfl⟩ : syracuseStep 1884051 = 2826077) B2826077
theorem B4239125 : Blo 1883435 4239125 := bbase (se 6 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 4239125 = 198709) (by norm_num)
theorem B2826083 : Blo 1883435 2826083 := bstep (se 1 (by rfl) ⟨2119562, by rfl⟩ : syracuseStep 2826083 = 4239125) B4239125
theorem B1884055 : Blo 1883435 1884055 := bstep (se 1 (by rfl) ⟨1413041, by rfl⟩ : syracuseStep 1884055 = 2826083) B2826083
theorem B7153541 : Blo 1883435 7153541 := bbase (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) (by norm_num)
theorem B4769027 : Blo 1883435 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B3179351 : Blo 1883435 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B2119567 : Blo 1883435 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B2826089 : Blo 1883435 2826089 := bstep (se 2 (by rfl) ⟨1059783, by rfl⟩ : syracuseStep 2826089 = 2119567) B2119567
theorem B1884059 : Blo 1883435 1884059 := bstep (se 1 (by rfl) ⟨1413044, by rfl⟩ : syracuseStep 1884059 = 2826089) B2826089
theorem B6035813 : Blo 1883435 6035813 := bbase (se 4 (by rfl) ⟨565857, by rfl⟩ : syracuseStep 6035813 = 1131715) (by norm_num)
theorem B4023875 : Blo 1883435 4023875 := bstep (se 1 (by rfl) ⟨3017906, by rfl⟩ : syracuseStep 4023875 = 6035813) B6035813
theorem B10730333 : Blo 1883435 10730333 := bstep (se 3 (by rfl) ⟨2011937, by rfl⟩ : syracuseStep 10730333 = 4023875) B4023875
theorem B7153555 : Blo 1883435 7153555 := bstep (se 1 (by rfl) ⟨5365166, by rfl⟩ : syracuseStep 7153555 = 10730333) B10730333
theorem B9538073 : Blo 1883435 9538073 := bstep (se 2 (by rfl) ⟨3576777, by rfl⟩ : syracuseStep 9538073 = 7153555) B7153555
theorem B6358715 : Blo 1883435 6358715 := bstep (se 1 (by rfl) ⟨4769036, by rfl⟩ : syracuseStep 6358715 = 9538073) B9538073
theorem B4239143 : Blo 1883435 4239143 := bstep (se 1 (by rfl) ⟨3179357, by rfl⟩ : syracuseStep 4239143 = 6358715) B6358715
theorem B2826095 : Blo 1883435 2826095 := bstep (se 1 (by rfl) ⟨2119571, by rfl⟩ : syracuseStep 2826095 = 4239143) B4239143
theorem B1884063 : Blo 1883435 1884063 := bstep (se 1 (by rfl) ⟨1413047, by rfl⟩ : syracuseStep 1884063 = 2826095) B2826095
theorem B2826101 : Blo 1883435 2826101 := bbase (se 5 (by rfl) ⟨132473, by rfl⟩ : syracuseStep 2826101 = 264947) (by norm_num)
theorem B1884067 : Blo 1883435 1884067 := bstep (se 1 (by rfl) ⟨1413050, by rfl⟩ : syracuseStep 1884067 = 2826101) B2826101
theorem B4023893 : Blo 1883435 4023893 := bbase (se 8 (by rfl) ⟨23577, by rfl⟩ : syracuseStep 4023893 = 47155) (by norm_num)
theorem B2682595 : Blo 1883435 2682595 := bstep (se 1 (by rfl) ⟨2011946, by rfl⟩ : syracuseStep 2682595 = 4023893) B4023893
theorem B3576793 : Blo 1883435 3576793 := bstep (se 2 (by rfl) ⟨1341297, by rfl⟩ : syracuseStep 3576793 = 2682595) B2682595
theorem B4769057 : Blo 1883435 4769057 := bstep (se 2 (by rfl) ⟨1788396, by rfl⟩ : syracuseStep 4769057 = 3576793) B3576793
theorem B3179371 : Blo 1883435 3179371 := bstep (se 1 (by rfl) ⟨2384528, by rfl⟩ : syracuseStep 3179371 = 4769057) B4769057
theorem B4239161 : Blo 1883435 4239161 := bstep (se 2 (by rfl) ⟨1589685, by rfl⟩ : syracuseStep 4239161 = 3179371) B3179371
theorem B2826107 : Blo 1883435 2826107 := bstep (se 1 (by rfl) ⟨2119580, by rfl⟩ : syracuseStep 2826107 = 4239161) B4239161
theorem B1884071 : Blo 1883435 1884071 := bstep (se 1 (by rfl) ⟨1413053, by rfl⟩ : syracuseStep 1884071 = 2826107) B2826107
theorem B2119585 : Blo 1883435 2119585 := bbase (se 2 (by rfl) ⟨794844, by rfl⟩ : syracuseStep 2119585 = 1589689) (by norm_num)
theorem B2826113 : Blo 1883435 2826113 := bstep (se 2 (by rfl) ⟨1059792, by rfl⟩ : syracuseStep 2826113 = 2119585) B2119585
theorem B1884075 : Blo 1883435 1884075 := bstep (se 1 (by rfl) ⟨1413056, by rfl⟩ : syracuseStep 1884075 = 2826113) B2826113
theorem B4769077 : Blo 1883435 4769077 := bbase (se 5 (by rfl) ⟨223550, by rfl⟩ : syracuseStep 4769077 = 447101) (by norm_num)
theorem B6358769 : Blo 1883435 6358769 := bstep (se 2 (by rfl) ⟨2384538, by rfl⟩ : syracuseStep 6358769 = 4769077) B4769077
theorem B4239179 : Blo 1883435 4239179 := bstep (se 1 (by rfl) ⟨3179384, by rfl⟩ : syracuseStep 4239179 = 6358769) B6358769
theorem B2826119 : Blo 1883435 2826119 := bstep (se 1 (by rfl) ⟨2119589, by rfl⟩ : syracuseStep 2826119 = 4239179) B4239179
theorem B1884079 : Blo 1883435 1884079 := bstep (se 1 (by rfl) ⟨1413059, by rfl⟩ : syracuseStep 1884079 = 2826119) B2826119
theorem B2826125 : Blo 1883435 2826125 := bbase (se 3 (by rfl) ⟨529898, by rfl⟩ : syracuseStep 2826125 = 1059797) (by norm_num)
theorem B1884083 : Blo 1883435 1884083 := bstep (se 1 (by rfl) ⟨1413062, by rfl⟩ : syracuseStep 1884083 = 2826125) B2826125
theorem B4239197 : Blo 1883435 4239197 := bbase (se 3 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 4239197 = 1589699) (by norm_num)
theorem B2826131 : Blo 1883435 2826131 := bstep (se 1 (by rfl) ⟨2119598, by rfl⟩ : syracuseStep 2826131 = 4239197) B4239197
theorem B1884087 : Blo 1883435 1884087 := bstep (se 1 (by rfl) ⟨1413065, by rfl⟩ : syracuseStep 1884087 = 2826131) B2826131
theorem B3179405 : Blo 1883435 3179405 := bbase (se 3 (by rfl) ⟨596138, by rfl⟩ : syracuseStep 3179405 = 1192277) (by norm_num)
theorem B2119603 : Blo 1883435 2119603 := bstep (se 1 (by rfl) ⟨1589702, by rfl⟩ : syracuseStep 2119603 = 3179405) B3179405
theorem B2826137 : Blo 1883435 2826137 := bstep (se 2 (by rfl) ⟨1059801, by rfl⟩ : syracuseStep 2826137 = 2119603) B2119603
theorem B1884091 : Blo 1883435 1884091 := bstep (se 1 (by rfl) ⟨1413068, by rfl⟩ : syracuseStep 1884091 = 2826137) B2826137
theorem B6790405 : Blo 1883435 6790405 := bbase (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) (by norm_num)
theorem B9053873 : Blo 1883435 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B6035915 : Blo 1883435 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B16095773 : Blo 1883435 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B10730515 : Blo 1883435 10730515 := bstep (se 1 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 10730515 = 16095773) B16095773
theorem B14307353 : Blo 1883435 14307353 := bstep (se 2 (by rfl) ⟨5365257, by rfl⟩ : syracuseStep 14307353 = 10730515) B10730515
theorem B9538235 : Blo 1883435 9538235 := bstep (se 1 (by rfl) ⟨7153676, by rfl⟩ : syracuseStep 9538235 = 14307353) B14307353
theorem B6358823 : Blo 1883435 6358823 := bstep (se 1 (by rfl) ⟨4769117, by rfl⟩ : syracuseStep 6358823 = 9538235) B9538235
theorem B4239215 : Blo 1883435 4239215 := bstep (se 1 (by rfl) ⟨3179411, by rfl⟩ : syracuseStep 4239215 = 6358823) B6358823
theorem B2826143 : Blo 1883435 2826143 := bstep (se 1 (by rfl) ⟨2119607, by rfl⟩ : syracuseStep 2826143 = 4239215) B4239215
theorem B1884095 : Blo 1883435 1884095 := bstep (se 1 (by rfl) ⟨1413071, by rfl⟩ : syracuseStep 1884095 = 2826143) B2826143
theorem B2826149 : Blo 1883435 2826149 := bbase (se 4 (by rfl) ⟨264951, by rfl⟩ : syracuseStep 2826149 = 529903) (by norm_num)
theorem B1884099 : Blo 1883435 1884099 := bstep (se 1 (by rfl) ⟨1413074, by rfl⟩ : syracuseStep 1884099 = 2826149) B2826149
theorem B2384569 : Blo 1883435 2384569 := bbase (se 2 (by rfl) ⟨894213, by rfl⟩ : syracuseStep 2384569 = 1788427) (by norm_num)
theorem B3179425 : Blo 1883435 3179425 := bstep (se 2 (by rfl) ⟨1192284, by rfl⟩ : syracuseStep 3179425 = 2384569) B2384569
theorem B4239233 : Blo 1883435 4239233 := bstep (se 2 (by rfl) ⟨1589712, by rfl⟩ : syracuseStep 4239233 = 3179425) B3179425
theorem B2826155 : Blo 1883435 2826155 := bstep (se 1 (by rfl) ⟨2119616, by rfl⟩ : syracuseStep 2826155 = 4239233) B4239233
theorem B1884103 : Blo 1883435 1884103 := bstep (se 1 (by rfl) ⟨1413077, by rfl⟩ : syracuseStep 1884103 = 2826155) B2826155
theorem B2119621 : Blo 1883435 2119621 := bbase (se 4 (by rfl) ⟨198714, by rfl⟩ : syracuseStep 2119621 = 397429) (by norm_num)
theorem B2826161 : Blo 1883435 2826161 := bstep (se 2 (by rfl) ⟨1059810, by rfl⟩ : syracuseStep 2826161 = 2119621) B2119621
theorem B1884107 : Blo 1883435 1884107 := bstep (se 1 (by rfl) ⟨1413080, by rfl⟩ : syracuseStep 1884107 = 2826161) B2826161
theorem B3576869 : Blo 1883435 3576869 := bbase (se 4 (by rfl) ⟨335331, by rfl⟩ : syracuseStep 3576869 = 670663) (by norm_num)
theorem B2384579 : Blo 1883435 2384579 := bstep (se 1 (by rfl) ⟨1788434, by rfl⟩ : syracuseStep 2384579 = 3576869) B3576869
theorem B6358877 : Blo 1883435 6358877 := bstep (se 3 (by rfl) ⟨1192289, by rfl⟩ : syracuseStep 6358877 = 2384579) B2384579
theorem B4239251 : Blo 1883435 4239251 := bstep (se 1 (by rfl) ⟨3179438, by rfl⟩ : syracuseStep 4239251 = 6358877) B6358877
theorem B2826167 : Blo 1883435 2826167 := bstep (se 1 (by rfl) ⟨2119625, by rfl⟩ : syracuseStep 2826167 = 4239251) B4239251
theorem B1884111 : Blo 1883435 1884111 := bstep (se 1 (by rfl) ⟨1413083, by rfl⟩ : syracuseStep 1884111 = 2826167) B2826167
theorem B2826173 : Blo 1883435 2826173 := bbase (se 3 (by rfl) ⟨529907, by rfl⟩ : syracuseStep 2826173 = 1059815) (by norm_num)
theorem B1884115 : Blo 1883435 1884115 := bstep (se 1 (by rfl) ⟨1413086, by rfl⟩ : syracuseStep 1884115 = 2826173) B2826173
theorem B4239269 : Blo 1883435 4239269 := bbase (se 4 (by rfl) ⟨397431, by rfl⟩ : syracuseStep 4239269 = 794863) (by norm_num)
theorem B2826179 : Blo 1883435 2826179 := bstep (se 1 (by rfl) ⟨2119634, by rfl⟩ : syracuseStep 2826179 = 4239269) B4239269
theorem B1884119 : Blo 1883435 1884119 := bstep (se 1 (by rfl) ⟨1413089, by rfl⟩ : syracuseStep 1884119 = 2826179) B2826179
theorem B4769189 : Blo 1883435 4769189 := bbase (se 4 (by rfl) ⟨447111, by rfl⟩ : syracuseStep 4769189 = 894223) (by norm_num)
theorem B3179459 : Blo 1883435 3179459 := bstep (se 1 (by rfl) ⟨2384594, by rfl⟩ : syracuseStep 3179459 = 4769189) B4769189
theorem B2119639 : Blo 1883435 2119639 := bstep (se 1 (by rfl) ⟨1589729, by rfl⟩ : syracuseStep 2119639 = 3179459) B3179459
theorem B2826185 : Blo 1883435 2826185 := bstep (se 2 (by rfl) ⟨1059819, by rfl⟩ : syracuseStep 2826185 = 2119639) B2119639
theorem B1884123 : Blo 1883435 1884123 := bstep (se 1 (by rfl) ⟨1413092, by rfl⟩ : syracuseStep 1884123 = 2826185) B2826185
theorem B5365349 : Blo 1883435 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B3576899 : Blo 1883435 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B9538397 : Blo 1883435 9538397 := bstep (se 3 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 9538397 = 3576899) B3576899
theorem B6358931 : Blo 1883435 6358931 := bstep (se 1 (by rfl) ⟨4769198, by rfl⟩ : syracuseStep 6358931 = 9538397) B9538397
theorem B4239287 : Blo 1883435 4239287 := bstep (se 1 (by rfl) ⟨3179465, by rfl⟩ : syracuseStep 4239287 = 6358931) B6358931
theorem B2826191 : Blo 1883435 2826191 := bstep (se 1 (by rfl) ⟨2119643, by rfl⟩ : syracuseStep 2826191 = 4239287) B4239287
theorem B1884127 : Blo 1883435 1884127 := bstep (se 1 (by rfl) ⟨1413095, by rfl⟩ : syracuseStep 1884127 = 2826191) B2826191
theorem B2826197 : Blo 1883435 2826197 := bbase (se 7 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 2826197 = 66239) (by norm_num)
theorem B1884131 : Blo 1883435 1884131 := bstep (se 1 (by rfl) ⟨1413098, by rfl⟩ : syracuseStep 1884131 = 2826197) B2826197
theorem B7153829 : Blo 1883435 7153829 := bbase (se 4 (by rfl) ⟨670671, by rfl⟩ : syracuseStep 7153829 = 1341343) (by norm_num)
theorem B4769219 : Blo 1883435 4769219 := bstep (se 1 (by rfl) ⟨3576914, by rfl⟩ : syracuseStep 4769219 = 7153829) B7153829
theorem B3179479 : Blo 1883435 3179479 := bstep (se 1 (by rfl) ⟨2384609, by rfl⟩ : syracuseStep 3179479 = 4769219) B4769219
theorem B4239305 : Blo 1883435 4239305 := bstep (se 2 (by rfl) ⟨1589739, by rfl⟩ : syracuseStep 4239305 = 3179479) B3179479
theorem B2826203 : Blo 1883435 2826203 := bstep (se 1 (by rfl) ⟨2119652, by rfl⟩ : syracuseStep 2826203 = 4239305) B4239305
theorem B1884135 : Blo 1883435 1884135 := bstep (se 1 (by rfl) ⟨1413101, by rfl⟩ : syracuseStep 1884135 = 2826203) B2826203
theorem B2119657 : Blo 1883435 2119657 := bbase (se 2 (by rfl) ⟨794871, by rfl⟩ : syracuseStep 2119657 = 1589743) (by norm_num)
theorem B2826209 : Blo 1883435 2826209 := bstep (se 2 (by rfl) ⟨1059828, by rfl⟩ : syracuseStep 2826209 = 2119657) B2119657
theorem B1884139 : Blo 1883435 1884139 := bstep (se 1 (by rfl) ⟨1413104, by rfl⟩ : syracuseStep 1884139 = 2826209) B2826209
theorem B4527053 : Blo 1883435 4527053 := bbase (se 3 (by rfl) ⟨848822, by rfl⟩ : syracuseStep 4527053 = 1697645) (by norm_num)
theorem B3018035 : Blo 1883435 3018035 := bstep (se 1 (by rfl) ⟨2263526, by rfl⟩ : syracuseStep 3018035 = 4527053) B4527053
theorem B2012023 : Blo 1883435 2012023 := bstep (se 1 (by rfl) ⟨1509017, by rfl⟩ : syracuseStep 2012023 = 3018035) B3018035
theorem B10730789 : Blo 1883435 10730789 := bstep (se 4 (by rfl) ⟨1006011, by rfl⟩ : syracuseStep 10730789 = 2012023) B2012023
theorem B7153859 : Blo 1883435 7153859 := bstep (se 1 (by rfl) ⟨5365394, by rfl⟩ : syracuseStep 7153859 = 10730789) B10730789
theorem B4769239 : Blo 1883435 4769239 := bstep (se 1 (by rfl) ⟨3576929, by rfl⟩ : syracuseStep 4769239 = 7153859) B7153859
theorem B6358985 : Blo 1883435 6358985 := bstep (se 2 (by rfl) ⟨2384619, by rfl⟩ : syracuseStep 6358985 = 4769239) B4769239
theorem B4239323 : Blo 1883435 4239323 := bstep (se 1 (by rfl) ⟨3179492, by rfl⟩ : syracuseStep 4239323 = 6358985) B6358985
theorem B2826215 : Blo 1883435 2826215 := bstep (se 1 (by rfl) ⟨2119661, by rfl⟩ : syracuseStep 2826215 = 4239323) B4239323
theorem B1884143 : Blo 1883435 1884143 := bstep (se 1 (by rfl) ⟨1413107, by rfl⟩ : syracuseStep 1884143 = 2826215) B2826215
theorem B2826221 : Blo 1883435 2826221 := bbase (se 3 (by rfl) ⟨529916, by rfl⟩ : syracuseStep 2826221 = 1059833) (by norm_num)
theorem B1884147 : Blo 1883435 1884147 := bstep (se 1 (by rfl) ⟨1413110, by rfl⟩ : syracuseStep 1884147 = 2826221) B2826221
theorem B4239341 : Blo 1883435 4239341 := bbase (se 3 (by rfl) ⟨794876, by rfl⟩ : syracuseStep 4239341 = 1589753) (by norm_num)
theorem B2826227 : Blo 1883435 2826227 := bstep (se 1 (by rfl) ⟨2119670, by rfl⟩ : syracuseStep 2826227 = 4239341) B4239341
theorem B1884151 : Blo 1883435 1884151 := bstep (se 1 (by rfl) ⟨1413113, by rfl⟩ : syracuseStep 1884151 = 2826227) B2826227
theorem B2294425 : Blo 1883435 2294425 := bbase (se 2 (by rfl) ⟨860409, by rfl⟩ : syracuseStep 2294425 = 1720819) (by norm_num)
theorem B12236933 : Blo 1883435 12236933 := bstep (se 4 (by rfl) ⟨1147212, by rfl⟩ : syracuseStep 12236933 = 2294425) B2294425
theorem B8157955 : Blo 1883435 8157955 := bstep (se 1 (by rfl) ⟨6118466, by rfl⟩ : syracuseStep 8157955 = 12236933) B12236933
theorem B10877273 : Blo 1883435 10877273 := bstep (se 2 (by rfl) ⟨4078977, by rfl⟩ : syracuseStep 10877273 = 8157955) B8157955
theorem B7251515 : Blo 1883435 7251515 := bstep (se 1 (by rfl) ⟨5438636, by rfl⟩ : syracuseStep 7251515 = 10877273) B10877273
theorem B4834343 : Blo 1883435 4834343 := bstep (se 1 (by rfl) ⟨3625757, by rfl⟩ : syracuseStep 4834343 = 7251515) B7251515
theorem B12891581 : Blo 1883435 12891581 := bstep (se 3 (by rfl) ⟨2417171, by rfl⟩ : syracuseStep 12891581 = 4834343) B4834343
theorem B8594387 : Blo 1883435 8594387 := bstep (se 1 (by rfl) ⟨6445790, by rfl⟩ : syracuseStep 8594387 = 12891581) B12891581
theorem B5729591 : Blo 1883435 5729591 := bstep (se 1 (by rfl) ⟨4297193, by rfl⟩ : syracuseStep 5729591 = 8594387) B8594387
theorem B3819727 : Blo 1883435 3819727 := bstep (se 1 (by rfl) ⟨2864795, by rfl⟩ : syracuseStep 3819727 = 5729591) B5729591
theorem B5092969 : Blo 1883435 5092969 := bstep (se 2 (by rfl) ⟨1909863, by rfl⟩ : syracuseStep 5092969 = 3819727) B3819727
theorem B6790625 : Blo 1883435 6790625 := bstep (se 2 (by rfl) ⟨2546484, by rfl⟩ : syracuseStep 6790625 = 5092969) B5092969
theorem B4527083 : Blo 1883435 4527083 := bstep (se 1 (by rfl) ⟨3395312, by rfl⟩ : syracuseStep 4527083 = 6790625) B6790625
theorem B3018055 : Blo 1883435 3018055 := bstep (se 1 (by rfl) ⟨2263541, by rfl⟩ : syracuseStep 3018055 = 4527083) B4527083
theorem B4024073 : Blo 1883435 4024073 := bstep (se 2 (by rfl) ⟨1509027, by rfl⟩ : syracuseStep 4024073 = 3018055) B3018055
theorem B2682715 : Blo 1883435 2682715 := bstep (se 1 (by rfl) ⟨2012036, by rfl⟩ : syracuseStep 2682715 = 4024073) B4024073
theorem B3576953 : Blo 1883435 3576953 := bstep (se 2 (by rfl) ⟨1341357, by rfl⟩ : syracuseStep 3576953 = 2682715) B2682715
theorem B2384635 : Blo 1883435 2384635 := bstep (se 1 (by rfl) ⟨1788476, by rfl⟩ : syracuseStep 2384635 = 3576953) B3576953
theorem B3179513 : Blo 1883435 3179513 := bstep (se 2 (by rfl) ⟨1192317, by rfl⟩ : syracuseStep 3179513 = 2384635) B2384635
theorem B2119675 : Blo 1883435 2119675 := bstep (se 1 (by rfl) ⟨1589756, by rfl⟩ : syracuseStep 2119675 = 3179513) B3179513
theorem B2826233 : Blo 1883435 2826233 := bstep (se 2 (by rfl) ⟨1059837, by rfl⟩ : syracuseStep 2826233 = 2119675) B2119675
theorem B1884155 : Blo 1883435 1884155 := bstep (se 1 (by rfl) ⟨1413116, by rfl⟩ : syracuseStep 1884155 = 2826233) B2826233
theorem B2207629 : Blo 1883435 2207629 := bbase (se 3 (by rfl) ⟨413930, by rfl⟩ : syracuseStep 2207629 = 827861) (by norm_num)
theorem B2943505 : Blo 1883435 2943505 := bstep (se 2 (by rfl) ⟨1103814, by rfl⟩ : syracuseStep 2943505 = 2207629) B2207629
theorem B15698693 : Blo 1883435 15698693 := bstep (se 4 (by rfl) ⟨1471752, by rfl⟩ : syracuseStep 15698693 = 2943505) B2943505
theorem B10465795 : Blo 1883435 10465795 := bstep (se 1 (by rfl) ⟨7849346, by rfl⟩ : syracuseStep 10465795 = 15698693) B15698693
theorem B13954393 : Blo 1883435 13954393 := bstep (se 2 (by rfl) ⟨5232897, by rfl⟩ : syracuseStep 13954393 = 10465795) B10465795
theorem B18605857 : Blo 1883435 18605857 := bstep (se 2 (by rfl) ⟨6977196, by rfl⟩ : syracuseStep 18605857 = 13954393) B13954393
theorem B24807809 : Blo 1883435 24807809 := bstep (se 2 (by rfl) ⟨9302928, by rfl⟩ : syracuseStep 24807809 = 18605857) B18605857
theorem B16538539 : Blo 1883435 16538539 := bstep (se 1 (by rfl) ⟨12403904, by rfl⟩ : syracuseStep 16538539 = 24807809) B24807809
theorem B22051385 : Blo 1883435 22051385 := bstep (se 2 (by rfl) ⟨8269269, by rfl⟩ : syracuseStep 22051385 = 16538539) B16538539
theorem B14700923 : Blo 1883435 14700923 := bstep (se 1 (by rfl) ⟨11025692, by rfl⟩ : syracuseStep 14700923 = 22051385) B22051385
theorem B9800615 : Blo 1883435 9800615 := bstep (se 1 (by rfl) ⟨7350461, by rfl⟩ : syracuseStep 9800615 = 14700923) B14700923
theorem B6533743 : Blo 1883435 6533743 := bstep (se 1 (by rfl) ⟨4900307, by rfl⟩ : syracuseStep 6533743 = 9800615) B9800615
theorem B8711657 : Blo 1883435 8711657 := bstep (se 2 (by rfl) ⟨3266871, by rfl⟩ : syracuseStep 8711657 = 6533743) B6533743
theorem B5807771 : Blo 1883435 5807771 := bstep (se 1 (by rfl) ⟨4355828, by rfl⟩ : syracuseStep 5807771 = 8711657) B8711657
theorem B3871847 : Blo 1883435 3871847 := bstep (se 1 (by rfl) ⟨2903885, by rfl⟩ : syracuseStep 3871847 = 5807771) B5807771
theorem B2581231 : Blo 1883435 2581231 := bstep (se 1 (by rfl) ⟨1935923, by rfl⟩ : syracuseStep 2581231 = 3871847) B3871847
theorem B3441641 : Blo 1883435 3441641 := bstep (se 2 (by rfl) ⟨1290615, by rfl⟩ : syracuseStep 3441641 = 2581231) B2581231
theorem B9177709 : Blo 1883435 9177709 := bstep (se 3 (by rfl) ⟨1720820, by rfl⟩ : syracuseStep 9177709 = 3441641) B3441641
theorem B12236945 : Blo 1883435 12236945 := bstep (se 2 (by rfl) ⟨4588854, by rfl⟩ : syracuseStep 12236945 = 9177709) B9177709
theorem B130527413 : Blo 1883435 130527413 := bstep (se 5 (by rfl) ⟨6118472, by rfl⟩ : syracuseStep 130527413 = 12236945) B12236945
theorem B87018275 : Blo 1883435 87018275 := bstep (se 1 (by rfl) ⟨65263706, by rfl⟩ : syracuseStep 87018275 = 130527413) B130527413
theorem B58012183 : Blo 1883435 58012183 := bstep (se 1 (by rfl) ⟨43509137, by rfl⟩ : syracuseStep 58012183 = 87018275) B87018275
theorem B77349577 : Blo 1883435 77349577 := bstep (se 2 (by rfl) ⟨29006091, by rfl⟩ : syracuseStep 77349577 = 58012183) B58012183
theorem B103132769 : Blo 1883435 103132769 := bstep (se 2 (by rfl) ⟨38674788, by rfl⟩ : syracuseStep 103132769 = 77349577) B77349577
theorem B275020717 : Blo 1883435 275020717 := bstep (se 3 (by rfl) ⟨51566384, by rfl⟩ : syracuseStep 275020717 = 103132769) B103132769
theorem B366694289 : Blo 1883435 366694289 := bstep (se 2 (by rfl) ⟨137510358, by rfl⟩ : syracuseStep 366694289 = 275020717) B275020717
theorem B244462859 : Blo 1883435 244462859 := bstep (se 1 (by rfl) ⟨183347144, by rfl⟩ : syracuseStep 244462859 = 366694289) B366694289
theorem B162975239 : Blo 1883435 162975239 := bstep (se 1 (by rfl) ⟨122231429, by rfl⟩ : syracuseStep 162975239 = 244462859) B244462859
theorem B108650159 : Blo 1883435 108650159 := bstep (se 1 (by rfl) ⟨81487619, by rfl⟩ : syracuseStep 108650159 = 162975239) B162975239
theorem B72433439 : Blo 1883435 72433439 := bstep (se 1 (by rfl) ⟨54325079, by rfl⟩ : syracuseStep 72433439 = 108650159) B108650159
theorem B48288959 : Blo 1883435 48288959 := bstep (se 1 (by rfl) ⟨36216719, by rfl⟩ : syracuseStep 48288959 = 72433439) B72433439
theorem B32192639 : Blo 1883435 32192639 := bstep (se 1 (by rfl) ⟨24144479, by rfl⟩ : syracuseStep 32192639 = 48288959) B48288959
theorem B21461759 : Blo 1883435 21461759 := bstep (se 1 (by rfl) ⟨16096319, by rfl⟩ : syracuseStep 21461759 = 32192639) B32192639
theorem B14307839 : Blo 1883435 14307839 := bstep (se 1 (by rfl) ⟨10730879, by rfl⟩ : syracuseStep 14307839 = 21461759) B21461759
theorem B9538559 : Blo 1883435 9538559 := bstep (se 1 (by rfl) ⟨7153919, by rfl⟩ : syracuseStep 9538559 = 14307839) B14307839
theorem B6359039 : Blo 1883435 6359039 := bstep (se 1 (by rfl) ⟨4769279, by rfl⟩ : syracuseStep 6359039 = 9538559) B9538559
theorem B4239359 : Blo 1883435 4239359 := bstep (se 1 (by rfl) ⟨3179519, by rfl⟩ : syracuseStep 4239359 = 6359039) B6359039
theorem B2826239 : Blo 1883435 2826239 := bstep (se 1 (by rfl) ⟨2119679, by rfl⟩ : syracuseStep 2826239 = 4239359) B4239359
theorem B1884159 : Blo 1883435 1884159 := bstep (se 1 (by rfl) ⟨1413119, by rfl⟩ : syracuseStep 1884159 = 2826239) B2826239
theorem B2826245 : Blo 1883435 2826245 := bbase (se 4 (by rfl) ⟨264960, by rfl⟩ : syracuseStep 2826245 = 529921) (by norm_num)
theorem B1884163 : Blo 1883435 1884163 := bstep (se 1 (by rfl) ⟨1413122, by rfl⟩ : syracuseStep 1884163 = 2826245) B2826245
theorem B3179533 : Blo 1883435 3179533 := bbase (se 3 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 3179533 = 1192325) (by norm_num)
theorem B4239377 : Blo 1883435 4239377 := bstep (se 2 (by rfl) ⟨1589766, by rfl⟩ : syracuseStep 4239377 = 3179533) B3179533
theorem B2826251 : Blo 1883435 2826251 := bstep (se 1 (by rfl) ⟨2119688, by rfl⟩ : syracuseStep 2826251 = 4239377) B4239377
theorem B1884167 : Blo 1883435 1884167 := bstep (se 1 (by rfl) ⟨1413125, by rfl⟩ : syracuseStep 1884167 = 2826251) B2826251
theorem B2119693 : Blo 1883435 2119693 := bbase (se 3 (by rfl) ⟨397442, by rfl⟩ : syracuseStep 2119693 = 794885) (by norm_num)
theorem B2826257 : Blo 1883435 2826257 := bstep (se 2 (by rfl) ⟨1059846, by rfl⟩ : syracuseStep 2826257 = 2119693) B2119693
theorem B1884171 : Blo 1883435 1884171 := bstep (se 1 (by rfl) ⟨1413128, by rfl⟩ : syracuseStep 1884171 = 2826257) B2826257
theorem B6359093 : Blo 1883435 6359093 := bbase (se 5 (by rfl) ⟨298082, by rfl⟩ : syracuseStep 6359093 = 596165) (by norm_num)
theorem B4239395 : Blo 1883435 4239395 := bstep (se 1 (by rfl) ⟨3179546, by rfl⟩ : syracuseStep 4239395 = 6359093) B6359093
theorem B2826263 : Blo 1883435 2826263 := bstep (se 1 (by rfl) ⟨2119697, by rfl⟩ : syracuseStep 2826263 = 4239395) B4239395
theorem B1884175 : Blo 1883435 1884175 := bstep (se 1 (by rfl) ⟨1413131, by rfl⟩ : syracuseStep 1884175 = 2826263) B2826263
theorem B2826269 : Blo 1883435 2826269 := bbase (se 3 (by rfl) ⟨529925, by rfl⟩ : syracuseStep 2826269 = 1059851) (by norm_num)
theorem B1884179 : Blo 1883435 1884179 := bstep (se 1 (by rfl) ⟨1413134, by rfl⟩ : syracuseStep 1884179 = 2826269) B2826269
theorem B4239413 : Blo 1883435 4239413 := bbase (se 5 (by rfl) ⟨198722, by rfl⟩ : syracuseStep 4239413 = 397445) (by norm_num)
theorem B2826275 : Blo 1883435 2826275 := bstep (se 1 (by rfl) ⟨2119706, by rfl⟩ : syracuseStep 2826275 = 4239413) B4239413
theorem B1884183 : Blo 1883435 1884183 := bstep (se 1 (by rfl) ⟨1413137, by rfl⟩ : syracuseStep 1884183 = 2826275) B2826275
theorem B12891797 : Blo 1883435 12891797 := bbase (se 6 (by rfl) ⟨302151, by rfl⟩ : syracuseStep 12891797 = 604303) (by norm_num)
theorem B8594531 : Blo 1883435 8594531 := bstep (se 1 (by rfl) ⟨6445898, by rfl⟩ : syracuseStep 8594531 = 12891797) B12891797
theorem B5729687 : Blo 1883435 5729687 := bstep (se 1 (by rfl) ⟨4297265, by rfl⟩ : syracuseStep 5729687 = 8594531) B8594531
theorem B3819791 : Blo 1883435 3819791 := bstep (se 1 (by rfl) ⟨2864843, by rfl⟩ : syracuseStep 3819791 = 5729687) B5729687
theorem B2546527 : Blo 1883435 2546527 := bstep (se 1 (by rfl) ⟨1909895, by rfl⟩ : syracuseStep 2546527 = 3819791) B3819791
theorem B3395369 : Blo 1883435 3395369 := bstep (se 2 (by rfl) ⟨1273263, by rfl⟩ : syracuseStep 3395369 = 2546527) B2546527
theorem B9054317 : Blo 1883435 9054317 := bstep (se 3 (by rfl) ⟨1697684, by rfl⟩ : syracuseStep 9054317 = 3395369) B3395369
theorem B6036211 : Blo 1883435 6036211 := bstep (se 1 (by rfl) ⟨4527158, by rfl⟩ : syracuseStep 6036211 = 9054317) B9054317
theorem B8048281 : Blo 1883435 8048281 := bstep (se 2 (by rfl) ⟨3018105, by rfl⟩ : syracuseStep 8048281 = 6036211) B6036211
theorem B10731041 : Blo 1883435 10731041 := bstep (se 2 (by rfl) ⟨4024140, by rfl⟩ : syracuseStep 10731041 = 8048281) B8048281
theorem B7154027 : Blo 1883435 7154027 := bstep (se 1 (by rfl) ⟨5365520, by rfl⟩ : syracuseStep 7154027 = 10731041) B10731041
theorem B4769351 : Blo 1883435 4769351 := bstep (se 1 (by rfl) ⟨3577013, by rfl⟩ : syracuseStep 4769351 = 7154027) B7154027
theorem B3179567 : Blo 1883435 3179567 := bstep (se 1 (by rfl) ⟨2384675, by rfl⟩ : syracuseStep 3179567 = 4769351) B4769351
theorem B2119711 : Blo 1883435 2119711 := bstep (se 1 (by rfl) ⟨1589783, by rfl⟩ : syracuseStep 2119711 = 3179567) B3179567
theorem B2826281 : Blo 1883435 2826281 := bstep (se 2 (by rfl) ⟨1059855, by rfl⟩ : syracuseStep 2826281 = 2119711) B2119711
theorem B1884187 : Blo 1883435 1884187 := bstep (se 1 (by rfl) ⟨1413140, by rfl⟩ : syracuseStep 1884187 = 2826281) B2826281
theorem B7849477 : Blo 1883435 7849477 := bbase (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) (by norm_num)
theorem B41863877 : Blo 1883435 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B27909251 : Blo 1883435 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B18606167 : Blo 1883435 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B12404111 : Blo 1883435 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B33077629 : Blo 1883435 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B176414021 : Blo 1883435 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B117609347 : Blo 1883435 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B313624925 : Blo 1883435 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B209083283 : Blo 1883435 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B139388855 : Blo 1883435 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B371703613 : Blo 1883435 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B495604817 : Blo 1883435 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B330403211 : Blo 1883435 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B220268807 : Blo 1883435 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B146845871 : Blo 1883435 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B97897247 : Blo 1883435 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B65264831 : Blo 1883435 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B43509887 : Blo 1883435 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B29006591 : Blo 1883435 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B77350909 : Blo 1883435 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B103134545 : Blo 1883435 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B68756363 : Blo 1883435 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B45837575 : Blo 1883435 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B30558383 : Blo 1883435 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B20372255 : Blo 1883435 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B13581503 : Blo 1883435 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B9054335 : Blo 1883435 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B6036223 : Blo 1883435 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B8048297 : Blo 1883435 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B5365531 : Blo 1883435 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B7154041 : Blo 1883435 7154041 := bstep (se 2 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 7154041 = 5365531) B5365531
theorem B9538721 : Blo 1883435 9538721 := bstep (se 2 (by rfl) ⟨3577020, by rfl⟩ : syracuseStep 9538721 = 7154041) B7154041
theorem B6359147 : Blo 1883435 6359147 := bstep (se 1 (by rfl) ⟨4769360, by rfl⟩ : syracuseStep 6359147 = 9538721) B9538721
theorem B4239431 : Blo 1883435 4239431 := bstep (se 1 (by rfl) ⟨3179573, by rfl⟩ : syracuseStep 4239431 = 6359147) B6359147
theorem B2826287 : Blo 1883435 2826287 := bstep (se 1 (by rfl) ⟨2119715, by rfl⟩ : syracuseStep 2826287 = 4239431) B4239431
theorem B1884191 : Blo 1883435 1884191 := bstep (se 1 (by rfl) ⟨1413143, by rfl⟩ : syracuseStep 1884191 = 2826287) B2826287
theorem B2826293 : Blo 1883435 2826293 := bbase (se 5 (by rfl) ⟨132482, by rfl⟩ : syracuseStep 2826293 = 264965) (by norm_num)
theorem B1884195 : Blo 1883435 1884195 := bstep (se 1 (by rfl) ⟨1413146, by rfl⟩ : syracuseStep 1884195 = 2826293) B2826293
theorem B4769381 : Blo 1883435 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B3179587 : Blo 1883435 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B4239449 : Blo 1883435 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B2826299 : Blo 1883435 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B1884199 : Blo 1883435 1884199 := bstep (se 1 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 1884199 = 2826299) B2826299
theorem B2119729 : Blo 1883435 2119729 := bbase (se 2 (by rfl) ⟨794898, by rfl⟩ : syracuseStep 2119729 = 1589797) (by norm_num)
theorem B2826305 : Blo 1883435 2826305 := bstep (se 2 (by rfl) ⟨1059864, by rfl⟩ : syracuseStep 2826305 = 2119729) B2119729
theorem B1884203 : Blo 1883435 1884203 := bstep (se 1 (by rfl) ⟨1413152, by rfl⟩ : syracuseStep 1884203 = 2826305) B2826305
theorem B3395405 : Blo 1883435 3395405 := bbase (se 3 (by rfl) ⟨636638, by rfl⟩ : syracuseStep 3395405 = 1273277) (by norm_num)
theorem B9054413 : Blo 1883435 9054413 := bstep (se 3 (by rfl) ⟨1697702, by rfl⟩ : syracuseStep 9054413 = 3395405) B3395405
theorem B6036275 : Blo 1883435 6036275 := bstep (se 1 (by rfl) ⟨4527206, by rfl⟩ : syracuseStep 6036275 = 9054413) B9054413
theorem B4024183 : Blo 1883435 4024183 := bstep (se 1 (by rfl) ⟨3018137, by rfl⟩ : syracuseStep 4024183 = 6036275) B6036275
theorem B5365577 : Blo 1883435 5365577 := bstep (se 2 (by rfl) ⟨2012091, by rfl⟩ : syracuseStep 5365577 = 4024183) B4024183
theorem B3577051 : Blo 1883435 3577051 := bstep (se 1 (by rfl) ⟨2682788, by rfl⟩ : syracuseStep 3577051 = 5365577) B5365577
theorem B4769401 : Blo 1883435 4769401 := bstep (se 2 (by rfl) ⟨1788525, by rfl⟩ : syracuseStep 4769401 = 3577051) B3577051
theorem B6359201 : Blo 1883435 6359201 := bstep (se 2 (by rfl) ⟨2384700, by rfl⟩ : syracuseStep 6359201 = 4769401) B4769401
theorem B4239467 : Blo 1883435 4239467 := bstep (se 1 (by rfl) ⟨3179600, by rfl⟩ : syracuseStep 4239467 = 6359201) B6359201
theorem B2826311 : Blo 1883435 2826311 := bstep (se 1 (by rfl) ⟨2119733, by rfl⟩ : syracuseStep 2826311 = 4239467) B4239467
theorem B1884207 : Blo 1883435 1884207 := bstep (se 1 (by rfl) ⟨1413155, by rfl⟩ : syracuseStep 1884207 = 2826311) B2826311
theorem B2826317 : Blo 1883435 2826317 := bbase (se 3 (by rfl) ⟨529934, by rfl⟩ : syracuseStep 2826317 = 1059869) (by norm_num)
theorem B1884211 : Blo 1883435 1884211 := bstep (se 1 (by rfl) ⟨1413158, by rfl⟩ : syracuseStep 1884211 = 2826317) B2826317
theorem B4239485 : Blo 1883435 4239485 := bbase (se 3 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 4239485 = 1589807) (by norm_num)
theorem B2826323 : Blo 1883435 2826323 := bstep (se 1 (by rfl) ⟨2119742, by rfl⟩ : syracuseStep 2826323 = 4239485) B4239485
theorem B1884215 : Blo 1883435 1884215 := bstep (se 1 (by rfl) ⟨1413161, by rfl⟩ : syracuseStep 1884215 = 2826323) B2826323
theorem B3179621 : Blo 1883435 3179621 := bbase (se 4 (by rfl) ⟨298089, by rfl⟩ : syracuseStep 3179621 = 596179) (by norm_num)
theorem B2119747 : Blo 1883435 2119747 := bstep (se 1 (by rfl) ⟨1589810, by rfl⟩ : syracuseStep 2119747 = 3179621) B3179621
theorem B2826329 : Blo 1883435 2826329 := bstep (se 2 (by rfl) ⟨1059873, by rfl⟩ : syracuseStep 2826329 = 2119747) B2119747
theorem B1884219 : Blo 1883435 1884219 := bstep (se 1 (by rfl) ⟨1413164, by rfl⟩ : syracuseStep 1884219 = 2826329) B2826329
theorem B4527245 : Blo 1883435 4527245 := bbase (se 3 (by rfl) ⟨848858, by rfl⟩ : syracuseStep 4527245 = 1697717) (by norm_num)
theorem B3018163 : Blo 1883435 3018163 := bstep (se 1 (by rfl) ⟨2263622, by rfl⟩ : syracuseStep 3018163 = 4527245) B4527245
theorem B4024217 : Blo 1883435 4024217 := bstep (se 2 (by rfl) ⟨1509081, by rfl⟩ : syracuseStep 4024217 = 3018163) B3018163
theorem B2682811 : Blo 1883435 2682811 := bstep (se 1 (by rfl) ⟨2012108, by rfl⟩ : syracuseStep 2682811 = 4024217) B4024217
theorem B14308325 : Blo 1883435 14308325 := bstep (se 4 (by rfl) ⟨1341405, by rfl⟩ : syracuseStep 14308325 = 2682811) B2682811
theorem B9538883 : Blo 1883435 9538883 := bstep (se 1 (by rfl) ⟨7154162, by rfl⟩ : syracuseStep 9538883 = 14308325) B14308325
theorem B6359255 : Blo 1883435 6359255 := bstep (se 1 (by rfl) ⟨4769441, by rfl⟩ : syracuseStep 6359255 = 9538883) B9538883
theorem B4239503 : Blo 1883435 4239503 := bstep (se 1 (by rfl) ⟨3179627, by rfl⟩ : syracuseStep 4239503 = 6359255) B6359255
theorem B2826335 : Blo 1883435 2826335 := bstep (se 1 (by rfl) ⟨2119751, by rfl⟩ : syracuseStep 2826335 = 4239503) B4239503
theorem B1884223 : Blo 1883435 1884223 := bstep (se 1 (by rfl) ⟨1413167, by rfl⟩ : syracuseStep 1884223 = 2826335) B2826335
theorem B2826341 : Blo 1883435 2826341 := bbase (se 4 (by rfl) ⟨264969, by rfl⟩ : syracuseStep 2826341 = 529939) (by norm_num)
theorem B1884227 : Blo 1883435 1884227 := bstep (se 1 (by rfl) ⟨1413170, by rfl⟩ : syracuseStep 1884227 = 2826341) B2826341
theorem B9669077 : Blo 1883435 9669077 := bbase (se 7 (by rfl) ⟨113309, by rfl⟩ : syracuseStep 9669077 = 226619) (by norm_num)
theorem B6446051 : Blo 1883435 6446051 := bstep (se 1 (by rfl) ⟨4834538, by rfl⟩ : syracuseStep 6446051 = 9669077) B9669077
theorem B4297367 : Blo 1883435 4297367 := bstep (se 1 (by rfl) ⟨3223025, by rfl⟩ : syracuseStep 4297367 = 6446051) B6446051
theorem B2864911 : Blo 1883435 2864911 := bstep (se 1 (by rfl) ⟨2148683, by rfl⟩ : syracuseStep 2864911 = 4297367) B4297367
theorem B3819881 : Blo 1883435 3819881 := bstep (se 2 (by rfl) ⟨1432455, by rfl⟩ : syracuseStep 3819881 = 2864911) B2864911
theorem B2546587 : Blo 1883435 2546587 := bstep (se 1 (by rfl) ⟨1909940, by rfl⟩ : syracuseStep 2546587 = 3819881) B3819881
theorem B3395449 : Blo 1883435 3395449 := bstep (se 2 (by rfl) ⟨1273293, by rfl⟩ : syracuseStep 3395449 = 2546587) B2546587
theorem B4527265 : Blo 1883435 4527265 := bstep (se 2 (by rfl) ⟨1697724, by rfl⟩ : syracuseStep 4527265 = 3395449) B3395449
theorem B6036353 : Blo 1883435 6036353 := bstep (se 2 (by rfl) ⟨2263632, by rfl⟩ : syracuseStep 6036353 = 4527265) B4527265
theorem B4024235 : Blo 1883435 4024235 := bstep (se 1 (by rfl) ⟨3018176, by rfl⟩ : syracuseStep 4024235 = 6036353) B6036353
theorem B2682823 : Blo 1883435 2682823 := bstep (se 1 (by rfl) ⟨2012117, by rfl⟩ : syracuseStep 2682823 = 4024235) B4024235
theorem B3577097 : Blo 1883435 3577097 := bstep (se 2 (by rfl) ⟨1341411, by rfl⟩ : syracuseStep 3577097 = 2682823) B2682823
theorem B2384731 : Blo 1883435 2384731 := bstep (se 1 (by rfl) ⟨1788548, by rfl⟩ : syracuseStep 2384731 = 3577097) B3577097
theorem B3179641 : Blo 1883435 3179641 := bstep (se 2 (by rfl) ⟨1192365, by rfl⟩ : syracuseStep 3179641 = 2384731) B2384731
theorem B4239521 : Blo 1883435 4239521 := bstep (se 2 (by rfl) ⟨1589820, by rfl⟩ : syracuseStep 4239521 = 3179641) B3179641
theorem B2826347 : Blo 1883435 2826347 := bstep (se 1 (by rfl) ⟨2119760, by rfl⟩ : syracuseStep 2826347 = 4239521) B4239521
theorem B1884231 : Blo 1883435 1884231 := bstep (se 1 (by rfl) ⟨1413173, by rfl⟩ : syracuseStep 1884231 = 2826347) B2826347
theorem B2119765 : Blo 1883435 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B2826353 : Blo 1883435 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B1884235 : Blo 1883435 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B2384741 : Blo 1883435 2384741 := bbase (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) (by norm_num)
theorem B6359309 : Blo 1883435 6359309 := bstep (se 3 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 6359309 = 2384741) B2384741
theorem B4239539 : Blo 1883435 4239539 := bstep (se 1 (by rfl) ⟨3179654, by rfl⟩ : syracuseStep 4239539 = 6359309) B6359309
theorem B2826359 : Blo 1883435 2826359 := bstep (se 1 (by rfl) ⟨2119769, by rfl⟩ : syracuseStep 2826359 = 4239539) B4239539
theorem B1884239 : Blo 1883435 1884239 := bstep (se 1 (by rfl) ⟨1413179, by rfl⟩ : syracuseStep 1884239 = 2826359) B2826359
theorem B2826365 : Blo 1883435 2826365 := bbase (se 3 (by rfl) ⟨529943, by rfl⟩ : syracuseStep 2826365 = 1059887) (by norm_num)
theorem B1884243 : Blo 1883435 1884243 := bstep (se 1 (by rfl) ⟨1413182, by rfl⟩ : syracuseStep 1884243 = 2826365) B2826365
theorem B4239557 : Blo 1883435 4239557 := bbase (se 4 (by rfl) ⟨397458, by rfl⟩ : syracuseStep 4239557 = 794917) (by norm_num)
theorem B2826371 : Blo 1883435 2826371 := bstep (se 1 (by rfl) ⟨2119778, by rfl⟩ : syracuseStep 2826371 = 4239557) B4239557
theorem B1884247 : Blo 1883435 1884247 := bstep (se 1 (by rfl) ⟨1413185, by rfl⟩ : syracuseStep 1884247 = 2826371) B2826371
theorem B6446117 : Blo 1883435 6446117 := bbase (se 4 (by rfl) ⟨604323, by rfl⟩ : syracuseStep 6446117 = 1208647) (by norm_num)
theorem B4297411 : Blo 1883435 4297411 := bstep (se 1 (by rfl) ⟨3223058, by rfl⟩ : syracuseStep 4297411 = 6446117) B6446117
theorem B5729881 : Blo 1883435 5729881 := bstep (se 2 (by rfl) ⟨2148705, by rfl⟩ : syracuseStep 5729881 = 4297411) B4297411
theorem B7639841 : Blo 1883435 7639841 := bstep (se 2 (by rfl) ⟨2864940, by rfl⟩ : syracuseStep 7639841 = 5729881) B5729881
theorem B5093227 : Blo 1883435 5093227 := bstep (se 1 (by rfl) ⟨3819920, by rfl⟩ : syracuseStep 5093227 = 7639841) B7639841
theorem B6790969 : Blo 1883435 6790969 := bstep (se 2 (by rfl) ⟨2546613, by rfl⟩ : syracuseStep 6790969 = 5093227) B5093227
theorem B9054625 : Blo 1883435 9054625 := bstep (se 2 (by rfl) ⟨3395484, by rfl⟩ : syracuseStep 9054625 = 6790969) B6790969
theorem B12072833 : Blo 1883435 12072833 := bstep (se 2 (by rfl) ⟨4527312, by rfl⟩ : syracuseStep 12072833 = 9054625) B9054625
theorem B8048555 : Blo 1883435 8048555 := bstep (se 1 (by rfl) ⟨6036416, by rfl⟩ : syracuseStep 8048555 = 12072833) B12072833
theorem B5365703 : Blo 1883435 5365703 := bstep (se 1 (by rfl) ⟨4024277, by rfl⟩ : syracuseStep 5365703 = 8048555) B8048555
theorem B3577135 : Blo 1883435 3577135 := bstep (se 1 (by rfl) ⟨2682851, by rfl⟩ : syracuseStep 3577135 = 5365703) B5365703
theorem B4769513 : Blo 1883435 4769513 := bstep (se 2 (by rfl) ⟨1788567, by rfl⟩ : syracuseStep 4769513 = 3577135) B3577135
theorem B3179675 : Blo 1883435 3179675 := bstep (se 1 (by rfl) ⟨2384756, by rfl⟩ : syracuseStep 3179675 = 4769513) B4769513
theorem B2119783 : Blo 1883435 2119783 := bstep (se 1 (by rfl) ⟨1589837, by rfl⟩ : syracuseStep 2119783 = 3179675) B3179675
theorem B2826377 : Blo 1883435 2826377 := bstep (se 2 (by rfl) ⟨1059891, by rfl⟩ : syracuseStep 2826377 = 2119783) B2119783
theorem B1884251 : Blo 1883435 1884251 := bstep (se 1 (by rfl) ⟨1413188, by rfl⟩ : syracuseStep 1884251 = 2826377) B2826377
theorem B9539045 : Blo 1883435 9539045 := bbase (se 4 (by rfl) ⟨894285, by rfl⟩ : syracuseStep 9539045 = 1788571) (by norm_num)
theorem B6359363 : Blo 1883435 6359363 := bstep (se 1 (by rfl) ⟨4769522, by rfl⟩ : syracuseStep 6359363 = 9539045) B9539045
theorem B4239575 : Blo 1883435 4239575 := bstep (se 1 (by rfl) ⟨3179681, by rfl⟩ : syracuseStep 4239575 = 6359363) B6359363
theorem B2826383 : Blo 1883435 2826383 := bstep (se 1 (by rfl) ⟨2119787, by rfl⟩ : syracuseStep 2826383 = 4239575) B4239575
theorem B1884255 : Blo 1883435 1884255 := bstep (se 1 (by rfl) ⟨1413191, by rfl⟩ : syracuseStep 1884255 = 2826383) B2826383
theorem B2826389 : Blo 1883435 2826389 := bbase (se 6 (by rfl) ⟨66243, by rfl⟩ : syracuseStep 2826389 = 132487) (by norm_num)
theorem B1884259 : Blo 1883435 1884259 := bstep (se 1 (by rfl) ⟨1413194, by rfl⟩ : syracuseStep 1884259 = 2826389) B2826389
theorem B4527341 : Blo 1883435 4527341 := bbase (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) (by norm_num)
theorem B3018227 : Blo 1883435 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B8048605 : Blo 1883435 8048605 := bstep (se 3 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 8048605 = 3018227) B3018227
theorem B10731473 : Blo 1883435 10731473 := bstep (se 2 (by rfl) ⟨4024302, by rfl⟩ : syracuseStep 10731473 = 8048605) B8048605
theorem B7154315 : Blo 1883435 7154315 := bstep (se 1 (by rfl) ⟨5365736, by rfl⟩ : syracuseStep 7154315 = 10731473) B10731473
theorem B4769543 : Blo 1883435 4769543 := bstep (se 1 (by rfl) ⟨3577157, by rfl⟩ : syracuseStep 4769543 = 7154315) B7154315
theorem B3179695 : Blo 1883435 3179695 := bstep (se 1 (by rfl) ⟨2384771, by rfl⟩ : syracuseStep 3179695 = 4769543) B4769543
theorem B4239593 : Blo 1883435 4239593 := bstep (se 2 (by rfl) ⟨1589847, by rfl⟩ : syracuseStep 4239593 = 3179695) B3179695
theorem B2826395 : Blo 1883435 2826395 := bstep (se 1 (by rfl) ⟨2119796, by rfl⟩ : syracuseStep 2826395 = 4239593) B4239593
theorem B1884263 : Blo 1883435 1884263 := bstep (se 1 (by rfl) ⟨1413197, by rfl⟩ : syracuseStep 1884263 = 2826395) B2826395
theorem B2119801 : Blo 1883435 2119801 := bbase (se 2 (by rfl) ⟨794925, by rfl⟩ : syracuseStep 2119801 = 1589851) (by norm_num)
theorem B2826401 : Blo 1883435 2826401 := bstep (se 2 (by rfl) ⟨1059900, by rfl⟩ : syracuseStep 2826401 = 2119801) B2119801
theorem B1884267 : Blo 1883435 1884267 := bstep (se 1 (by rfl) ⟨1413200, by rfl⟩ : syracuseStep 1884267 = 2826401) B2826401
theorem B12573877 : Blo 1883435 12573877 := bbase (se 5 (by rfl) ⟨589400, by rfl⟩ : syracuseStep 12573877 = 1178801) (by norm_num)
theorem B16765169 : Blo 1883435 16765169 := bstep (se 2 (by rfl) ⟨6286938, by rfl⟩ : syracuseStep 16765169 = 12573877) B12573877
theorem B178828469 : Blo 1883435 178828469 := bstep (se 5 (by rfl) ⟨8382584, by rfl⟩ : syracuseStep 178828469 = 16765169) B16765169
theorem B119218979 : Blo 1883435 119218979 := bstep (se 1 (by rfl) ⟨89414234, by rfl⟩ : syracuseStep 119218979 = 178828469) B178828469
theorem B79479319 : Blo 1883435 79479319 := bstep (se 1 (by rfl) ⟨59609489, by rfl⟩ : syracuseStep 79479319 = 119218979) B119218979
theorem B105972425 : Blo 1883435 105972425 := bstep (se 2 (by rfl) ⟨39739659, by rfl⟩ : syracuseStep 105972425 = 79479319) B79479319
theorem B70648283 : Blo 1883435 70648283 := bstep (se 1 (by rfl) ⟨52986212, by rfl⟩ : syracuseStep 70648283 = 105972425) B105972425
theorem B47098855 : Blo 1883435 47098855 := bstep (se 1 (by rfl) ⟨35324141, by rfl⟩ : syracuseStep 47098855 = 70648283) B70648283
theorem B62798473 : Blo 1883435 62798473 := bstep (se 2 (by rfl) ⟨23549427, by rfl⟩ : syracuseStep 62798473 = 47098855) B47098855
theorem B334925189 : Blo 1883435 334925189 := bstep (se 4 (by rfl) ⟨31399236, by rfl⟩ : syracuseStep 334925189 = 62798473) B62798473
theorem B223283459 : Blo 1883435 223283459 := bstep (se 1 (by rfl) ⟨167462594, by rfl⟩ : syracuseStep 223283459 = 334925189) B334925189
theorem B148855639 : Blo 1883435 148855639 := bstep (se 1 (by rfl) ⟨111641729, by rfl⟩ : syracuseStep 148855639 = 223283459) B223283459
theorem B198474185 : Blo 1883435 198474185 := bstep (se 2 (by rfl) ⟨74427819, by rfl⟩ : syracuseStep 198474185 = 148855639) B148855639
theorem B132316123 : Blo 1883435 132316123 := bstep (se 1 (by rfl) ⟨99237092, by rfl⟩ : syracuseStep 132316123 = 198474185) B198474185
theorem B176421497 : Blo 1883435 176421497 := bstep (se 2 (by rfl) ⟨66158061, by rfl⟩ : syracuseStep 176421497 = 132316123) B132316123
theorem B470457325 : Blo 1883435 470457325 := bstep (se 3 (by rfl) ⟨88210748, by rfl⟩ : syracuseStep 470457325 = 176421497) B176421497
theorem B2509105733 : Blo 1883435 2509105733 := bstep (se 4 (by rfl) ⟨235228662, by rfl⟩ : syracuseStep 2509105733 = 470457325) B470457325
theorem B1672737155 : Blo 1883435 1672737155 := bstep (se 1 (by rfl) ⟨1254552866, by rfl⟩ : syracuseStep 1672737155 = 2509105733) B2509105733
theorem B1115158103 : Blo 1883435 1115158103 := bstep (se 1 (by rfl) ⟨836368577, by rfl⟩ : syracuseStep 1115158103 = 1672737155) B1672737155
theorem B743438735 : Blo 1883435 743438735 := bstep (se 1 (by rfl) ⟨557579051, by rfl⟩ : syracuseStep 743438735 = 1115158103) B1115158103
theorem B495625823 : Blo 1883435 495625823 := bstep (se 1 (by rfl) ⟨371719367, by rfl⟩ : syracuseStep 495625823 = 743438735) B743438735
theorem B330417215 : Blo 1883435 330417215 := bstep (se 1 (by rfl) ⟨247812911, by rfl⟩ : syracuseStep 330417215 = 495625823) B495625823
theorem B220278143 : Blo 1883435 220278143 := bstep (se 1 (by rfl) ⟨165208607, by rfl⟩ : syracuseStep 220278143 = 330417215) B330417215
theorem B587408381 : Blo 1883435 587408381 := bstep (se 3 (by rfl) ⟨110139071, by rfl⟩ : syracuseStep 587408381 = 220278143) B220278143
theorem B391605587 : Blo 1883435 391605587 := bstep (se 1 (by rfl) ⟨293704190, by rfl⟩ : syracuseStep 391605587 = 587408381) B587408381
theorem B261070391 : Blo 1883435 261070391 := bstep (se 1 (by rfl) ⟨195802793, by rfl⟩ : syracuseStep 261070391 = 391605587) B391605587
theorem B696187709 : Blo 1883435 696187709 := bstep (se 3 (by rfl) ⟨130535195, by rfl⟩ : syracuseStep 696187709 = 261070391) B261070391
theorem B464125139 : Blo 1883435 464125139 := bstep (se 1 (by rfl) ⟨348093854, by rfl⟩ : syracuseStep 464125139 = 696187709) B696187709
theorem B309416759 : Blo 1883435 309416759 := bstep (se 1 (by rfl) ⟨232062569, by rfl⟩ : syracuseStep 309416759 = 464125139) B464125139
theorem B206277839 : Blo 1883435 206277839 := bstep (se 1 (by rfl) ⟨154708379, by rfl⟩ : syracuseStep 206277839 = 309416759) B309416759
theorem B137518559 : Blo 1883435 137518559 := bstep (se 1 (by rfl) ⟨103138919, by rfl⟩ : syracuseStep 137518559 = 206277839) B206277839
theorem B91679039 : Blo 1883435 91679039 := bstep (se 1 (by rfl) ⟨68759279, by rfl⟩ : syracuseStep 91679039 = 137518559) B137518559
theorem B61119359 : Blo 1883435 61119359 := bstep (se 1 (by rfl) ⟨45839519, by rfl⟩ : syracuseStep 61119359 = 91679039) B91679039
theorem B40746239 : Blo 1883435 40746239 := bstep (se 1 (by rfl) ⟨30559679, by rfl⟩ : syracuseStep 40746239 = 61119359) B61119359
theorem B27164159 : Blo 1883435 27164159 := bstep (se 1 (by rfl) ⟨20373119, by rfl⟩ : syracuseStep 27164159 = 40746239) B40746239
theorem B18109439 : Blo 1883435 18109439 := bstep (se 1 (by rfl) ⟨13582079, by rfl⟩ : syracuseStep 18109439 = 27164159) B27164159
theorem B12072959 : Blo 1883435 12072959 := bstep (se 1 (by rfl) ⟨9054719, by rfl⟩ : syracuseStep 12072959 = 18109439) B18109439
theorem B8048639 : Blo 1883435 8048639 := bstep (se 1 (by rfl) ⟨6036479, by rfl⟩ : syracuseStep 8048639 = 12072959) B12072959
theorem B5365759 : Blo 1883435 5365759 := bstep (se 1 (by rfl) ⟨4024319, by rfl⟩ : syracuseStep 5365759 = 8048639) B8048639
theorem B7154345 : Blo 1883435 7154345 := bstep (se 2 (by rfl) ⟨2682879, by rfl⟩ : syracuseStep 7154345 = 5365759) B5365759
theorem B4769563 : Blo 1883435 4769563 := bstep (se 1 (by rfl) ⟨3577172, by rfl⟩ : syracuseStep 4769563 = 7154345) B7154345
theorem B6359417 : Blo 1883435 6359417 := bstep (se 2 (by rfl) ⟨2384781, by rfl⟩ : syracuseStep 6359417 = 4769563) B4769563
theorem B4239611 : Blo 1883435 4239611 := bstep (se 1 (by rfl) ⟨3179708, by rfl⟩ : syracuseStep 4239611 = 6359417) B6359417
theorem B2826407 : Blo 1883435 2826407 := bstep (se 1 (by rfl) ⟨2119805, by rfl⟩ : syracuseStep 2826407 = 4239611) B4239611
theorem B1884271 : Blo 1883435 1884271 := bstep (se 1 (by rfl) ⟨1413203, by rfl⟩ : syracuseStep 1884271 = 2826407) B2826407
theorem B2826413 : Blo 1883435 2826413 := bbase (se 3 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 2826413 = 1059905) (by norm_num)
theorem B1884275 : Blo 1883435 1884275 := bstep (se 1 (by rfl) ⟨1413206, by rfl⟩ : syracuseStep 1884275 = 2826413) B2826413
theorem B4239629 : Blo 1883435 4239629 := bbase (se 3 (by rfl) ⟨794930, by rfl⟩ : syracuseStep 4239629 = 1589861) (by norm_num)
theorem B2826419 : Blo 1883435 2826419 := bstep (se 1 (by rfl) ⟨2119814, by rfl⟩ : syracuseStep 2826419 = 4239629) B4239629
theorem B1884279 : Blo 1883435 1884279 := bstep (se 1 (by rfl) ⟨1413209, by rfl⟩ : syracuseStep 1884279 = 2826419) B2826419
theorem B2384797 : Blo 1883435 2384797 := bbase (se 3 (by rfl) ⟨447149, by rfl⟩ : syracuseStep 2384797 = 894299) (by norm_num)
theorem B3179729 : Blo 1883435 3179729 := bstep (se 2 (by rfl) ⟨1192398, by rfl⟩ : syracuseStep 3179729 = 2384797) B2384797
theorem B2119819 : Blo 1883435 2119819 := bstep (se 1 (by rfl) ⟨1589864, by rfl⟩ : syracuseStep 2119819 = 3179729) B3179729
theorem B2826425 : Blo 1883435 2826425 := bstep (se 2 (by rfl) ⟨1059909, by rfl⟩ : syracuseStep 2826425 = 2119819) B2119819
theorem B1884283 : Blo 1883435 1884283 := bstep (se 1 (by rfl) ⟨1413212, by rfl⟩ : syracuseStep 1884283 = 2826425) B2826425
theorem B3395549 : Blo 1883435 3395549 := bbase (se 3 (by rfl) ⟨636665, by rfl⟩ : syracuseStep 3395549 = 1273331) (by norm_num)
theorem B2263699 : Blo 1883435 2263699 := bstep (se 1 (by rfl) ⟨1697774, by rfl⟩ : syracuseStep 2263699 = 3395549) B3395549
theorem B3018265 : Blo 1883435 3018265 := bstep (se 2 (by rfl) ⟨1131849, by rfl⟩ : syracuseStep 3018265 = 2263699) B2263699
theorem B16097413 : Blo 1883435 16097413 := bstep (se 4 (by rfl) ⟨1509132, by rfl⟩ : syracuseStep 16097413 = 3018265) B3018265
theorem B21463217 : Blo 1883435 21463217 := bstep (se 2 (by rfl) ⟨8048706, by rfl⟩ : syracuseStep 21463217 = 16097413) B16097413
theorem B14308811 : Blo 1883435 14308811 := bstep (se 1 (by rfl) ⟨10731608, by rfl⟩ : syracuseStep 14308811 = 21463217) B21463217
theorem B9539207 : Blo 1883435 9539207 := bstep (se 1 (by rfl) ⟨7154405, by rfl⟩ : syracuseStep 9539207 = 14308811) B14308811
theorem B6359471 : Blo 1883435 6359471 := bstep (se 1 (by rfl) ⟨4769603, by rfl⟩ : syracuseStep 6359471 = 9539207) B9539207
theorem B4239647 : Blo 1883435 4239647 := bstep (se 1 (by rfl) ⟨3179735, by rfl⟩ : syracuseStep 4239647 = 6359471) B6359471
theorem B2826431 : Blo 1883435 2826431 := bstep (se 1 (by rfl) ⟨2119823, by rfl⟩ : syracuseStep 2826431 = 4239647) B4239647
theorem B1884287 : Blo 1883435 1884287 := bstep (se 1 (by rfl) ⟨1413215, by rfl⟩ : syracuseStep 1884287 = 2826431) B2826431
theorem B2826437 : Blo 1883435 2826437 := bbase (se 4 (by rfl) ⟨264978, by rfl⟩ : syracuseStep 2826437 = 529957) (by norm_num)
theorem B1884291 : Blo 1883435 1884291 := bstep (se 1 (by rfl) ⟨1413218, by rfl⟩ : syracuseStep 1884291 = 2826437) B2826437
theorem B3179749 : Blo 1883435 3179749 := bbase (se 4 (by rfl) ⟨298101, by rfl⟩ : syracuseStep 3179749 = 596203) (by norm_num)
theorem B4239665 : Blo 1883435 4239665 := bstep (se 2 (by rfl) ⟨1589874, by rfl⟩ : syracuseStep 4239665 = 3179749) B3179749
theorem B2826443 : Blo 1883435 2826443 := bstep (se 1 (by rfl) ⟨2119832, by rfl⟩ : syracuseStep 2826443 = 4239665) B4239665
theorem B1884295 : Blo 1883435 1884295 := bstep (se 1 (by rfl) ⟨1413221, by rfl⟩ : syracuseStep 1884295 = 2826443) B2826443
theorem B2119837 : Blo 1883435 2119837 := bbase (se 3 (by rfl) ⟨397469, by rfl⟩ : syracuseStep 2119837 = 794939) (by norm_num)
theorem B2826449 : Blo 1883435 2826449 := bstep (se 2 (by rfl) ⟨1059918, by rfl⟩ : syracuseStep 2826449 = 2119837) B2119837
theorem B1884299 : Blo 1883435 1884299 := bstep (se 1 (by rfl) ⟨1413224, by rfl⟩ : syracuseStep 1884299 = 2826449) B2826449
theorem B6359525 : Blo 1883435 6359525 := bbase (se 4 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 6359525 = 1192411) (by norm_num)
theorem B4239683 : Blo 1883435 4239683 := bstep (se 1 (by rfl) ⟨3179762, by rfl⟩ : syracuseStep 4239683 = 6359525) B6359525
theorem B2826455 : Blo 1883435 2826455 := bstep (se 1 (by rfl) ⟨2119841, by rfl⟩ : syracuseStep 2826455 = 4239683) B4239683
theorem B1884303 : Blo 1883435 1884303 := bstep (se 1 (by rfl) ⟨1413227, by rfl⟩ : syracuseStep 1884303 = 2826455) B2826455
theorem B2826461 : Blo 1883435 2826461 := bbase (se 3 (by rfl) ⟨529961, by rfl⟩ : syracuseStep 2826461 = 1059923) (by norm_num)
theorem B1884307 : Blo 1883435 1884307 := bstep (se 1 (by rfl) ⟨1413230, by rfl⟩ : syracuseStep 1884307 = 2826461) B2826461
theorem B4239701 : Blo 1883435 4239701 := bbase (se 10 (by rfl) ⟨6210, by rfl⟩ : syracuseStep 4239701 = 12421) (by norm_num)
theorem B2826467 : Blo 1883435 2826467 := bstep (se 1 (by rfl) ⟨2119850, by rfl⟩ : syracuseStep 2826467 = 4239701) B4239701
theorem B1884311 : Blo 1883435 1884311 := bstep (se 1 (by rfl) ⟨1413233, by rfl⟩ : syracuseStep 1884311 = 2826467) B2826467
theorem B2417377 : Blo 1883435 2417377 := bbase (se 2 (by rfl) ⟨906516, by rfl⟩ : syracuseStep 2417377 = 1813033) (by norm_num)
theorem B3223169 : Blo 1883435 3223169 := bstep (se 2 (by rfl) ⟨1208688, by rfl⟩ : syracuseStep 3223169 = 2417377) B2417377
theorem B2148779 : Blo 1883435 2148779 := bstep (se 1 (by rfl) ⟨1611584, by rfl⟩ : syracuseStep 2148779 = 3223169) B3223169
theorem B5730077 : Blo 1883435 5730077 := bstep (se 3 (by rfl) ⟨1074389, by rfl⟩ : syracuseStep 5730077 = 2148779) B2148779
theorem B3820051 : Blo 1883435 3820051 := bstep (se 1 (by rfl) ⟨2865038, by rfl⟩ : syracuseStep 3820051 = 5730077) B5730077
theorem B5093401 : Blo 1883435 5093401 := bstep (se 2 (by rfl) ⟨1910025, by rfl⟩ : syracuseStep 5093401 = 3820051) B3820051
theorem B6791201 : Blo 1883435 6791201 := bstep (se 2 (by rfl) ⟨2546700, by rfl⟩ : syracuseStep 6791201 = 5093401) B5093401
theorem B4527467 : Blo 1883435 4527467 := bstep (se 1 (by rfl) ⟨3395600, by rfl⟩ : syracuseStep 4527467 = 6791201) B6791201
theorem B3018311 : Blo 1883435 3018311 := bstep (se 1 (by rfl) ⟨2263733, by rfl⟩ : syracuseStep 3018311 = 4527467) B4527467
theorem B2012207 : Blo 1883435 2012207 := bstep (se 1 (by rfl) ⟨1509155, by rfl⟩ : syracuseStep 2012207 = 3018311) B3018311
theorem B5365885 : Blo 1883435 5365885 := bstep (se 3 (by rfl) ⟨1006103, by rfl⟩ : syracuseStep 5365885 = 2012207) B2012207
theorem B7154513 : Blo 1883435 7154513 := bstep (se 2 (by rfl) ⟨2682942, by rfl⟩ : syracuseStep 7154513 = 5365885) B5365885
theorem B4769675 : Blo 1883435 4769675 := bstep (se 1 (by rfl) ⟨3577256, by rfl⟩ : syracuseStep 4769675 = 7154513) B7154513
theorem B3179783 : Blo 1883435 3179783 := bstep (se 1 (by rfl) ⟨2384837, by rfl⟩ : syracuseStep 3179783 = 4769675) B4769675
theorem B2119855 : Blo 1883435 2119855 := bstep (se 1 (by rfl) ⟨1589891, by rfl⟩ : syracuseStep 2119855 = 3179783) B3179783
theorem B2826473 : Blo 1883435 2826473 := bstep (se 2 (by rfl) ⟨1059927, by rfl⟩ : syracuseStep 2826473 = 2119855) B2119855
theorem B1884315 : Blo 1883435 1884315 := bstep (se 1 (by rfl) ⟨1413236, by rfl⟩ : syracuseStep 1884315 = 2826473) B2826473
theorem B36219797 : Blo 1883435 36219797 := bbase (se 6 (by rfl) ⟨848901, by rfl⟩ : syracuseStep 36219797 = 1697803) (by norm_num)
theorem B24146531 : Blo 1883435 24146531 := bstep (se 1 (by rfl) ⟨18109898, by rfl⟩ : syracuseStep 24146531 = 36219797) B36219797
theorem B16097687 : Blo 1883435 16097687 := bstep (se 1 (by rfl) ⟨12073265, by rfl⟩ : syracuseStep 16097687 = 24146531) B24146531
theorem B10731791 : Blo 1883435 10731791 := bstep (se 1 (by rfl) ⟨8048843, by rfl⟩ : syracuseStep 10731791 = 16097687) B16097687
theorem B7154527 : Blo 1883435 7154527 := bstep (se 1 (by rfl) ⟨5365895, by rfl⟩ : syracuseStep 7154527 = 10731791) B10731791
theorem B9539369 : Blo 1883435 9539369 := bstep (se 2 (by rfl) ⟨3577263, by rfl⟩ : syracuseStep 9539369 = 7154527) B7154527
theorem B6359579 : Blo 1883435 6359579 := bstep (se 1 (by rfl) ⟨4769684, by rfl⟩ : syracuseStep 6359579 = 9539369) B9539369
theorem B4239719 : Blo 1883435 4239719 := bstep (se 1 (by rfl) ⟨3179789, by rfl⟩ : syracuseStep 4239719 = 6359579) B6359579
theorem B2826479 : Blo 1883435 2826479 := bstep (se 1 (by rfl) ⟨2119859, by rfl⟩ : syracuseStep 2826479 = 4239719) B4239719
theorem B1884319 : Blo 1883435 1884319 := bstep (se 1 (by rfl) ⟨1413239, by rfl⟩ : syracuseStep 1884319 = 2826479) B2826479
theorem B2826485 : Blo 1883435 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B1884323 : Blo 1883435 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B3311741 : Blo 1883435 3311741 := bbase (se 3 (by rfl) ⟨620951, by rfl⟩ : syracuseStep 3311741 = 1241903) (by norm_num)
theorem B2207827 : Blo 1883435 2207827 := bstep (se 1 (by rfl) ⟨1655870, by rfl⟩ : syracuseStep 2207827 = 3311741) B3311741
theorem B2943769 : Blo 1883435 2943769 := bstep (se 2 (by rfl) ⟨1103913, by rfl⟩ : syracuseStep 2943769 = 2207827) B2207827
theorem B3925025 : Blo 1883435 3925025 := bstep (se 2 (by rfl) ⟨1471884, by rfl⟩ : syracuseStep 3925025 = 2943769) B2943769
theorem B2616683 : Blo 1883435 2616683 := bstep (se 1 (by rfl) ⟨1962512, by rfl⟩ : syracuseStep 2616683 = 3925025) B3925025
theorem B6977821 : Blo 1883435 6977821 := bstep (se 3 (by rfl) ⟨1308341, by rfl⟩ : syracuseStep 6977821 = 2616683) B2616683
theorem B9303761 : Blo 1883435 9303761 := bstep (se 2 (by rfl) ⟨3488910, by rfl⟩ : syracuseStep 9303761 = 6977821) B6977821
theorem B6202507 : Blo 1883435 6202507 := bstep (se 1 (by rfl) ⟨4651880, by rfl⟩ : syracuseStep 6202507 = 9303761) B9303761
theorem B8270009 : Blo 1883435 8270009 := bstep (se 2 (by rfl) ⟨3101253, by rfl⟩ : syracuseStep 8270009 = 6202507) B6202507
theorem B5513339 : Blo 1883435 5513339 := bstep (se 1 (by rfl) ⟨4135004, by rfl⟩ : syracuseStep 5513339 = 8270009) B8270009
theorem B3675559 : Blo 1883435 3675559 := bstep (se 1 (by rfl) ⟨2756669, by rfl⟩ : syracuseStep 3675559 = 5513339) B5513339
theorem B4900745 : Blo 1883435 4900745 := bstep (se 2 (by rfl) ⟨1837779, by rfl⟩ : syracuseStep 4900745 = 3675559) B3675559
theorem B3267163 : Blo 1883435 3267163 := bstep (se 1 (by rfl) ⟨2450372, by rfl⟩ : syracuseStep 3267163 = 4900745) B4900745
theorem B4356217 : Blo 1883435 4356217 := bstep (se 2 (by rfl) ⟨1633581, by rfl⟩ : syracuseStep 4356217 = 3267163) B3267163
theorem B5808289 : Blo 1883435 5808289 := bstep (se 2 (by rfl) ⟨2178108, by rfl⟩ : syracuseStep 5808289 = 4356217) B4356217
theorem B7744385 : Blo 1883435 7744385 := bstep (se 2 (by rfl) ⟨2904144, by rfl⟩ : syracuseStep 7744385 = 5808289) B5808289
theorem B20651693 : Blo 1883435 20651693 := bstep (se 3 (by rfl) ⟨3872192, by rfl⟩ : syracuseStep 20651693 = 7744385) B7744385
theorem B55071181 : Blo 1883435 55071181 := bstep (se 3 (by rfl) ⟨10325846, by rfl⟩ : syracuseStep 55071181 = 20651693) B20651693
theorem B73428241 : Blo 1883435 73428241 := bstep (se 2 (by rfl) ⟨27535590, by rfl⟩ : syracuseStep 73428241 = 55071181) B55071181
theorem B97904321 : Blo 1883435 97904321 := bstep (se 2 (by rfl) ⟨36714120, by rfl⟩ : syracuseStep 97904321 = 73428241) B73428241
theorem B65269547 : Blo 1883435 65269547 := bstep (se 1 (by rfl) ⟨48952160, by rfl⟩ : syracuseStep 65269547 = 97904321) B97904321
theorem B43513031 : Blo 1883435 43513031 := bstep (se 1 (by rfl) ⟨32634773, by rfl⟩ : syracuseStep 43513031 = 65269547) B65269547
theorem B29008687 : Blo 1883435 29008687 := bstep (se 1 (by rfl) ⟨21756515, by rfl⟩ : syracuseStep 29008687 = 43513031) B43513031
theorem B38678249 : Blo 1883435 38678249 := bstep (se 2 (by rfl) ⟨14504343, by rfl⟩ : syracuseStep 38678249 = 29008687) B29008687
theorem B103141997 : Blo 1883435 103141997 := bstep (se 3 (by rfl) ⟨19339124, by rfl⟩ : syracuseStep 103141997 = 38678249) B38678249
theorem B68761331 : Blo 1883435 68761331 := bstep (se 1 (by rfl) ⟨51570998, by rfl⟩ : syracuseStep 68761331 = 103141997) B103141997
theorem B45840887 : Blo 1883435 45840887 := bstep (se 1 (by rfl) ⟨34380665, by rfl⟩ : syracuseStep 45840887 = 68761331) B68761331
theorem B30560591 : Blo 1883435 30560591 := bstep (se 1 (by rfl) ⟨22920443, by rfl⟩ : syracuseStep 30560591 = 45840887) B45840887
theorem B20373727 : Blo 1883435 20373727 := bstep (se 1 (by rfl) ⟨15280295, by rfl⟩ : syracuseStep 20373727 = 30560591) B30560591
theorem B27164969 : Blo 1883435 27164969 := bstep (se 2 (by rfl) ⟨10186863, by rfl⟩ : syracuseStep 27164969 = 20373727) B20373727
theorem B18109979 : Blo 1883435 18109979 := bstep (se 1 (by rfl) ⟨13582484, by rfl⟩ : syracuseStep 18109979 = 27164969) B27164969
theorem B12073319 : Blo 1883435 12073319 := bstep (se 1 (by rfl) ⟨9054989, by rfl⟩ : syracuseStep 12073319 = 18109979) B18109979
theorem B8048879 : Blo 1883435 8048879 := bstep (se 1 (by rfl) ⟨6036659, by rfl⟩ : syracuseStep 8048879 = 12073319) B12073319
theorem B5365919 : Blo 1883435 5365919 := bstep (se 1 (by rfl) ⟨4024439, by rfl⟩ : syracuseStep 5365919 = 8048879) B8048879
theorem B3577279 : Blo 1883435 3577279 := bstep (se 1 (by rfl) ⟨2682959, by rfl⟩ : syracuseStep 3577279 = 5365919) B5365919
theorem B4769705 : Blo 1883435 4769705 := bstep (se 2 (by rfl) ⟨1788639, by rfl⟩ : syracuseStep 4769705 = 3577279) B3577279
theorem B3179803 : Blo 1883435 3179803 := bstep (se 1 (by rfl) ⟨2384852, by rfl⟩ : syracuseStep 3179803 = 4769705) B4769705
theorem B4239737 : Blo 1883435 4239737 := bstep (se 2 (by rfl) ⟨1589901, by rfl⟩ : syracuseStep 4239737 = 3179803) B3179803
theorem B2826491 : Blo 1883435 2826491 := bstep (se 1 (by rfl) ⟨2119868, by rfl⟩ : syracuseStep 2826491 = 4239737) B4239737
theorem B1884327 : Blo 1883435 1884327 := bstep (se 1 (by rfl) ⟨1413245, by rfl⟩ : syracuseStep 1884327 = 2826491) B2826491
theorem B2119873 : Blo 1883435 2119873 := bbase (se 2 (by rfl) ⟨794952, by rfl⟩ : syracuseStep 2119873 = 1589905) (by norm_num)
theorem B2826497 : Blo 1883435 2826497 := bstep (se 2 (by rfl) ⟨1059936, by rfl⟩ : syracuseStep 2826497 = 2119873) B2119873
theorem B1884331 : Blo 1883435 1884331 := bstep (se 1 (by rfl) ⟨1413248, by rfl⟩ : syracuseStep 1884331 = 2826497) B2826497
theorem B4769725 : Blo 1883435 4769725 := bbase (se 3 (by rfl) ⟨894323, by rfl⟩ : syracuseStep 4769725 = 1788647) (by norm_num)
theorem B6359633 : Blo 1883435 6359633 := bstep (se 2 (by rfl) ⟨2384862, by rfl⟩ : syracuseStep 6359633 = 4769725) B4769725
theorem B4239755 : Blo 1883435 4239755 := bstep (se 1 (by rfl) ⟨3179816, by rfl⟩ : syracuseStep 4239755 = 6359633) B6359633
theorem B2826503 : Blo 1883435 2826503 := bstep (se 1 (by rfl) ⟨2119877, by rfl⟩ : syracuseStep 2826503 = 4239755) B4239755
theorem B1884335 : Blo 1883435 1884335 := bstep (se 1 (by rfl) ⟨1413251, by rfl⟩ : syracuseStep 1884335 = 2826503) B2826503
theorem B2826509 : Blo 1883435 2826509 := bbase (se 3 (by rfl) ⟨529970, by rfl⟩ : syracuseStep 2826509 = 1059941) (by norm_num)
theorem B1884339 : Blo 1883435 1884339 := bstep (se 1 (by rfl) ⟨1413254, by rfl⟩ : syracuseStep 1884339 = 2826509) B2826509
theorem B4239773 : Blo 1883435 4239773 := bbase (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) (by norm_num)
theorem B2826515 : Blo 1883435 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B1884343 : Blo 1883435 1884343 := bstep (se 1 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 1884343 = 2826515) B2826515
theorem B3179837 : Blo 1883435 3179837 := bbase (se 3 (by rfl) ⟨596219, by rfl⟩ : syracuseStep 3179837 = 1192439) (by norm_num)
theorem B2119891 : Blo 1883435 2119891 := bstep (se 1 (by rfl) ⟨1589918, by rfl⟩ : syracuseStep 2119891 = 3179837) B3179837
theorem B2826521 : Blo 1883435 2826521 := bstep (se 2 (by rfl) ⟨1059945, by rfl⟩ : syracuseStep 2826521 = 2119891) B2119891
theorem B1884347 : Blo 1883435 1884347 := bstep (se 1 (by rfl) ⟨1413260, by rfl⟩ : syracuseStep 1884347 = 2826521) B2826521
theorem B2012245 : Blo 1883435 2012245 := bbase (se 8 (by rfl) ⟨11790, by rfl⟩ : syracuseStep 2012245 = 23581) (by norm_num)
theorem B10731973 : Blo 1883435 10731973 := bstep (se 4 (by rfl) ⟨1006122, by rfl⟩ : syracuseStep 10731973 = 2012245) B2012245
theorem B14309297 : Blo 1883435 14309297 := bstep (se 2 (by rfl) ⟨5365986, by rfl⟩ : syracuseStep 14309297 = 10731973) B10731973
theorem B9539531 : Blo 1883435 9539531 := bstep (se 1 (by rfl) ⟨7154648, by rfl⟩ : syracuseStep 9539531 = 14309297) B14309297
theorem B6359687 : Blo 1883435 6359687 := bstep (se 1 (by rfl) ⟨4769765, by rfl⟩ : syracuseStep 6359687 = 9539531) B9539531
theorem B4239791 : Blo 1883435 4239791 := bstep (se 1 (by rfl) ⟨3179843, by rfl⟩ : syracuseStep 4239791 = 6359687) B6359687
theorem B2826527 : Blo 1883435 2826527 := bstep (se 1 (by rfl) ⟨2119895, by rfl⟩ : syracuseStep 2826527 = 4239791) B4239791
theorem B1884351 : Blo 1883435 1884351 := bstep (se 1 (by rfl) ⟨1413263, by rfl⟩ : syracuseStep 1884351 = 2826527) B2826527
theorem B2826533 : Blo 1883435 2826533 := bbase (se 4 (by rfl) ⟨264987, by rfl⟩ : syracuseStep 2826533 = 529975) (by norm_num)
theorem B1884355 : Blo 1883435 1884355 := bstep (se 1 (by rfl) ⟨1413266, by rfl⟩ : syracuseStep 1884355 = 2826533) B2826533
theorem B2384893 : Blo 1883435 2384893 := bbase (se 3 (by rfl) ⟨447167, by rfl⟩ : syracuseStep 2384893 = 894335) (by norm_num)
theorem B3179857 : Blo 1883435 3179857 := bstep (se 2 (by rfl) ⟨1192446, by rfl⟩ : syracuseStep 3179857 = 2384893) B2384893
theorem B4239809 : Blo 1883435 4239809 := bstep (se 2 (by rfl) ⟨1589928, by rfl⟩ : syracuseStep 4239809 = 3179857) B3179857
theorem B2826539 : Blo 1883435 2826539 := bstep (se 1 (by rfl) ⟨2119904, by rfl⟩ : syracuseStep 2826539 = 4239809) B4239809
theorem B1884359 : Blo 1883435 1884359 := bstep (se 1 (by rfl) ⟨1413269, by rfl⟩ : syracuseStep 1884359 = 2826539) B2826539
theorem B2119909 : Blo 1883435 2119909 := bbase (se 4 (by rfl) ⟨198741, by rfl⟩ : syracuseStep 2119909 = 397483) (by norm_num)
theorem B2826545 : Blo 1883435 2826545 := bstep (se 2 (by rfl) ⟨1059954, by rfl⟩ : syracuseStep 2826545 = 2119909) B2119909
theorem B1884363 : Blo 1883435 1884363 := bstep (se 1 (by rfl) ⟨1413272, by rfl⟩ : syracuseStep 1884363 = 2826545) B2826545
theorem B4024525 : Blo 1883435 4024525 := bbase (se 3 (by rfl) ⟨754598, by rfl⟩ : syracuseStep 4024525 = 1509197) (by norm_num)
theorem B5366033 : Blo 1883435 5366033 := bstep (se 2 (by rfl) ⟨2012262, by rfl⟩ : syracuseStep 5366033 = 4024525) B4024525
theorem B3577355 : Blo 1883435 3577355 := bstep (se 1 (by rfl) ⟨2683016, by rfl⟩ : syracuseStep 3577355 = 5366033) B5366033
theorem B2384903 : Blo 1883435 2384903 := bstep (se 1 (by rfl) ⟨1788677, by rfl⟩ : syracuseStep 2384903 = 3577355) B3577355
theorem B6359741 : Blo 1883435 6359741 := bstep (se 3 (by rfl) ⟨1192451, by rfl⟩ : syracuseStep 6359741 = 2384903) B2384903
theorem B4239827 : Blo 1883435 4239827 := bstep (se 1 (by rfl) ⟨3179870, by rfl⟩ : syracuseStep 4239827 = 6359741) B6359741
theorem B2826551 : Blo 1883435 2826551 := bstep (se 1 (by rfl) ⟨2119913, by rfl⟩ : syracuseStep 2826551 = 4239827) B4239827
theorem B1884367 : Blo 1883435 1884367 := bstep (se 1 (by rfl) ⟨1413275, by rfl⟩ : syracuseStep 1884367 = 2826551) B2826551
theorem B2826557 : Blo 1883435 2826557 := bbase (se 3 (by rfl) ⟨529979, by rfl⟩ : syracuseStep 2826557 = 1059959) (by norm_num)
theorem B1884371 : Blo 1883435 1884371 := bstep (se 1 (by rfl) ⟨1413278, by rfl⟩ : syracuseStep 1884371 = 2826557) B2826557
theorem B4239845 : Blo 1883435 4239845 := bbase (se 4 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 4239845 = 794971) (by norm_num)
theorem B2826563 : Blo 1883435 2826563 := bstep (se 1 (by rfl) ⟨2119922, by rfl⟩ : syracuseStep 2826563 = 4239845) B4239845
theorem B1884375 : Blo 1883435 1884375 := bstep (se 1 (by rfl) ⟨1413281, by rfl⟩ : syracuseStep 1884375 = 2826563) B2826563
theorem B4769837 : Blo 1883435 4769837 := bbase (se 3 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 4769837 = 1788689) (by norm_num)
theorem B3179891 : Blo 1883435 3179891 := bstep (se 1 (by rfl) ⟨2384918, by rfl⟩ : syracuseStep 3179891 = 4769837) B4769837
theorem B2119927 : Blo 1883435 2119927 := bstep (se 1 (by rfl) ⟨1589945, by rfl⟩ : syracuseStep 2119927 = 3179891) B3179891
theorem B2826569 : Blo 1883435 2826569 := bstep (se 2 (by rfl) ⟨1059963, by rfl⟩ : syracuseStep 2826569 = 2119927) B2119927
theorem B1884379 : Blo 1883435 1884379 := bstep (se 1 (by rfl) ⟨1413284, by rfl⟩ : syracuseStep 1884379 = 2826569) B2826569
theorem B2294701 : Blo 1883435 2294701 := bbase (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) (by norm_num)
theorem B48953621 : Blo 1883435 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B32635747 : Blo 1883435 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B43514329 : Blo 1883435 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B58019105 : Blo 1883435 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B38679403 : Blo 1883435 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B51572537 : Blo 1883435 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B34381691 : Blo 1883435 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B22921127 : Blo 1883435 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B15280751 : Blo 1883435 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B10187167 : Blo 1883435 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B13582889 : Blo 1883435 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B9055259 : Blo 1883435 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B6036839 : Blo 1883435 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B4024559 : Blo 1883435 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B2683039 : Blo 1883435 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B3577385 : Blo 1883435 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B9539693 : Blo 1883435 9539693 := bstep (se 3 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 9539693 = 3577385) B3577385
theorem B6359795 : Blo 1883435 6359795 := bstep (se 1 (by rfl) ⟨4769846, by rfl⟩ : syracuseStep 6359795 = 9539693) B9539693
theorem B4239863 : Blo 1883435 4239863 := bstep (se 1 (by rfl) ⟨3179897, by rfl⟩ : syracuseStep 4239863 = 6359795) B6359795
theorem B2826575 : Blo 1883435 2826575 := bstep (se 1 (by rfl) ⟨2119931, by rfl⟩ : syracuseStep 2826575 = 4239863) B4239863
theorem B1884383 : Blo 1883435 1884383 := bstep (se 1 (by rfl) ⟨1413287, by rfl⟩ : syracuseStep 1884383 = 2826575) B2826575
theorem B2826581 : Blo 1883435 2826581 := bbase (se 10 (by rfl) ⟨4140, by rfl⟩ : syracuseStep 2826581 = 8281) (by norm_num)
theorem B1884387 : Blo 1883435 1884387 := bstep (se 1 (by rfl) ⟨1413290, by rfl⟩ : syracuseStep 1884387 = 2826581) B2826581
theorem B5366101 : Blo 1883435 5366101 := bbase (se 10 (by rfl) ⟨7860, by rfl⟩ : syracuseStep 5366101 = 15721) (by norm_num)
theorem B7154801 : Blo 1883435 7154801 := bstep (se 2 (by rfl) ⟨2683050, by rfl⟩ : syracuseStep 7154801 = 5366101) B5366101
theorem B4769867 : Blo 1883435 4769867 := bstep (se 1 (by rfl) ⟨3577400, by rfl⟩ : syracuseStep 4769867 = 7154801) B7154801
theorem B3179911 : Blo 1883435 3179911 := bstep (se 1 (by rfl) ⟨2384933, by rfl⟩ : syracuseStep 3179911 = 4769867) B4769867
theorem B4239881 : Blo 1883435 4239881 := bstep (se 2 (by rfl) ⟨1589955, by rfl⟩ : syracuseStep 4239881 = 3179911) B3179911
theorem B2826587 : Blo 1883435 2826587 := bstep (se 1 (by rfl) ⟨2119940, by rfl⟩ : syracuseStep 2826587 = 4239881) B4239881
theorem B1884391 : Blo 1883435 1884391 := bstep (se 1 (by rfl) ⟨1413293, by rfl⟩ : syracuseStep 1884391 = 2826587) B2826587
theorem B2119945 : Blo 1883435 2119945 := bbase (se 2 (by rfl) ⟨794979, by rfl⟩ : syracuseStep 2119945 = 1589959) (by norm_num)
theorem B2826593 : Blo 1883435 2826593 := bstep (se 2 (by rfl) ⟨1059972, by rfl⟩ : syracuseStep 2826593 = 2119945) B2119945
theorem B1884395 : Blo 1883435 1884395 := bstep (se 1 (by rfl) ⟨1413296, by rfl⟩ : syracuseStep 1884395 = 2826593) B2826593
theorem B2546813 : Blo 1883435 2546813 := bbase (se 3 (by rfl) ⟨477527, by rfl⟩ : syracuseStep 2546813 = 955055) (by norm_num)
theorem B6791501 : Blo 1883435 6791501 := bstep (se 3 (by rfl) ⟨1273406, by rfl⟩ : syracuseStep 6791501 = 2546813) B2546813
theorem B4527667 : Blo 1883435 4527667 := bstep (se 1 (by rfl) ⟨3395750, by rfl⟩ : syracuseStep 4527667 = 6791501) B6791501
theorem B24147557 : Blo 1883435 24147557 := bstep (se 4 (by rfl) ⟨2263833, by rfl⟩ : syracuseStep 24147557 = 4527667) B4527667
theorem B16098371 : Blo 1883435 16098371 := bstep (se 1 (by rfl) ⟨12073778, by rfl⟩ : syracuseStep 16098371 = 24147557) B24147557
theorem B10732247 : Blo 1883435 10732247 := bstep (se 1 (by rfl) ⟨8049185, by rfl⟩ : syracuseStep 10732247 = 16098371) B16098371
theorem B7154831 : Blo 1883435 7154831 := bstep (se 1 (by rfl) ⟨5366123, by rfl⟩ : syracuseStep 7154831 = 10732247) B10732247
theorem B4769887 : Blo 1883435 4769887 := bstep (se 1 (by rfl) ⟨3577415, by rfl⟩ : syracuseStep 4769887 = 7154831) B7154831
theorem B6359849 : Blo 1883435 6359849 := bstep (se 2 (by rfl) ⟨2384943, by rfl⟩ : syracuseStep 6359849 = 4769887) B4769887
theorem B4239899 : Blo 1883435 4239899 := bstep (se 1 (by rfl) ⟨3179924, by rfl⟩ : syracuseStep 4239899 = 6359849) B6359849
theorem B2826599 : Blo 1883435 2826599 := bstep (se 1 (by rfl) ⟨2119949, by rfl⟩ : syracuseStep 2826599 = 4239899) B4239899
theorem B1884399 : Blo 1883435 1884399 := bstep (se 1 (by rfl) ⟨1413299, by rfl⟩ : syracuseStep 1884399 = 2826599) B2826599
theorem B2826605 : Blo 1883435 2826605 := bbase (se 3 (by rfl) ⟨529988, by rfl⟩ : syracuseStep 2826605 = 1059977) (by norm_num)
theorem B1884403 : Blo 1883435 1884403 := bstep (se 1 (by rfl) ⟨1413302, by rfl⟩ : syracuseStep 1884403 = 2826605) B2826605
theorem B4239917 : Blo 1883435 4239917 := bbase (se 3 (by rfl) ⟨794984, by rfl⟩ : syracuseStep 4239917 = 1589969) (by norm_num)
theorem B2826611 : Blo 1883435 2826611 := bstep (se 1 (by rfl) ⟨2119958, by rfl⟩ : syracuseStep 2826611 = 4239917) B4239917
theorem B1884407 : Blo 1883435 1884407 := bstep (se 1 (by rfl) ⟨1413305, by rfl⟩ : syracuseStep 1884407 = 2826611) B2826611
theorem B3395773 : Blo 1883435 3395773 := bbase (se 3 (by rfl) ⟨636707, by rfl⟩ : syracuseStep 3395773 = 1273415) (by norm_num)
theorem B18110789 : Blo 1883435 18110789 := bstep (se 4 (by rfl) ⟨1697886, by rfl⟩ : syracuseStep 18110789 = 3395773) B3395773
theorem B12073859 : Blo 1883435 12073859 := bstep (se 1 (by rfl) ⟨9055394, by rfl⟩ : syracuseStep 12073859 = 18110789) B18110789
theorem B8049239 : Blo 1883435 8049239 := bstep (se 1 (by rfl) ⟨6036929, by rfl⟩ : syracuseStep 8049239 = 12073859) B12073859
theorem B5366159 : Blo 1883435 5366159 := bstep (se 1 (by rfl) ⟨4024619, by rfl⟩ : syracuseStep 5366159 = 8049239) B8049239
theorem B3577439 : Blo 1883435 3577439 := bstep (se 1 (by rfl) ⟨2683079, by rfl⟩ : syracuseStep 3577439 = 5366159) B5366159
theorem B2384959 : Blo 1883435 2384959 := bstep (se 1 (by rfl) ⟨1788719, by rfl⟩ : syracuseStep 2384959 = 3577439) B3577439
theorem B3179945 : Blo 1883435 3179945 := bstep (se 2 (by rfl) ⟨1192479, by rfl⟩ : syracuseStep 3179945 = 2384959) B2384959
theorem B2119963 : Blo 1883435 2119963 := bstep (se 1 (by rfl) ⟨1589972, by rfl⟩ : syracuseStep 2119963 = 3179945) B3179945
theorem B2826617 : Blo 1883435 2826617 := bstep (se 2 (by rfl) ⟨1059981, by rfl⟩ : syracuseStep 2826617 = 2119963) B2119963
theorem B1884411 : Blo 1883435 1884411 := bstep (se 1 (by rfl) ⟨1413308, by rfl⟩ : syracuseStep 1884411 = 2826617) B2826617
theorem B32197013 : Blo 1883435 32197013 := bbase (se 6 (by rfl) ⟨754617, by rfl⟩ : syracuseStep 32197013 = 1509235) (by norm_num)
theorem B21464675 : Blo 1883435 21464675 := bstep (se 1 (by rfl) ⟨16098506, by rfl⟩ : syracuseStep 21464675 = 32197013) B32197013
theorem B14309783 : Blo 1883435 14309783 := bstep (se 1 (by rfl) ⟨10732337, by rfl⟩ : syracuseStep 14309783 = 21464675) B21464675
theorem B9539855 : Blo 1883435 9539855 := bstep (se 1 (by rfl) ⟨7154891, by rfl⟩ : syracuseStep 9539855 = 14309783) B14309783
theorem B6359903 : Blo 1883435 6359903 := bstep (se 1 (by rfl) ⟨4769927, by rfl⟩ : syracuseStep 6359903 = 9539855) B9539855
theorem B4239935 : Blo 1883435 4239935 := bstep (se 1 (by rfl) ⟨3179951, by rfl⟩ : syracuseStep 4239935 = 6359903) B6359903
theorem B2826623 : Blo 1883435 2826623 := bstep (se 1 (by rfl) ⟨2119967, by rfl⟩ : syracuseStep 2826623 = 4239935) B4239935
theorem B1884415 : Blo 1883435 1884415 := bstep (se 1 (by rfl) ⟨1413311, by rfl⟩ : syracuseStep 1884415 = 2826623) B2826623
theorem B2826629 : Blo 1883435 2826629 := bbase (se 4 (by rfl) ⟨264996, by rfl⟩ : syracuseStep 2826629 = 529993) (by norm_num)
theorem B1884419 : Blo 1883435 1884419 := bstep (se 1 (by rfl) ⟨1413314, by rfl⟩ : syracuseStep 1884419 = 2826629) B2826629
theorem B3179965 : Blo 1883435 3179965 := bbase (se 3 (by rfl) ⟨596243, by rfl⟩ : syracuseStep 3179965 = 1192487) (by norm_num)
theorem B4239953 : Blo 1883435 4239953 := bstep (se 2 (by rfl) ⟨1589982, by rfl⟩ : syracuseStep 4239953 = 3179965) B3179965
theorem B2826635 : Blo 1883435 2826635 := bstep (se 1 (by rfl) ⟨2119976, by rfl⟩ : syracuseStep 2826635 = 4239953) B4239953
theorem B1884423 : Blo 1883435 1884423 := bstep (se 1 (by rfl) ⟨1413317, by rfl⟩ : syracuseStep 1884423 = 2826635) B2826635
theorem B2119981 : Blo 1883435 2119981 := bbase (se 3 (by rfl) ⟨397496, by rfl⟩ : syracuseStep 2119981 = 794993) (by norm_num)
theorem B2826641 : Blo 1883435 2826641 := bstep (se 2 (by rfl) ⟨1059990, by rfl⟩ : syracuseStep 2826641 = 2119981) B2119981
theorem B1884427 : Blo 1883435 1884427 := bstep (se 1 (by rfl) ⟨1413320, by rfl⟩ : syracuseStep 1884427 = 2826641) B2826641
theorem B6359957 : Blo 1883435 6359957 := bbase (se 6 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 6359957 = 298123) (by norm_num)
theorem B4239971 : Blo 1883435 4239971 := bstep (se 1 (by rfl) ⟨3179978, by rfl⟩ : syracuseStep 4239971 = 6359957) B6359957
theorem B2826647 : Blo 1883435 2826647 := bstep (se 1 (by rfl) ⟨2119985, by rfl⟩ : syracuseStep 2826647 = 4239971) B4239971
theorem B1884431 : Blo 1883435 1884431 := bstep (se 1 (by rfl) ⟨1413323, by rfl⟩ : syracuseStep 1884431 = 2826647) B2826647
theorem B2826653 : Blo 1883435 2826653 := bbase (se 3 (by rfl) ⟨529997, by rfl⟩ : syracuseStep 2826653 = 1059995) (by norm_num)
theorem B1884435 : Blo 1883435 1884435 := bstep (se 1 (by rfl) ⟨1413326, by rfl⟩ : syracuseStep 1884435 = 2826653) B2826653
theorem B4239989 : Blo 1883435 4239989 := bbase (se 5 (by rfl) ⟨198749, by rfl⟩ : syracuseStep 4239989 = 397499) (by norm_num)
theorem B2826659 : Blo 1883435 2826659 := bstep (se 1 (by rfl) ⟨2119994, by rfl⟩ : syracuseStep 2826659 = 4239989) B4239989
theorem B1884439 : Blo 1883435 1884439 := bstep (se 1 (by rfl) ⟨1413329, by rfl⟩ : syracuseStep 1884439 = 2826659) B2826659
theorem B15281237 : Blo 1883435 15281237 := bbase (se 8 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 15281237 = 179077) (by norm_num)
theorem B10187491 : Blo 1883435 10187491 := bstep (se 1 (by rfl) ⟨7640618, by rfl⟩ : syracuseStep 10187491 = 15281237) B15281237
theorem B13583321 : Blo 1883435 13583321 := bstep (se 2 (by rfl) ⟨5093745, by rfl⟩ : syracuseStep 13583321 = 10187491) B10187491
theorem B9055547 : Blo 1883435 9055547 := bstep (se 1 (by rfl) ⟨6791660, by rfl⟩ : syracuseStep 9055547 = 13583321) B13583321
theorem B6037031 : Blo 1883435 6037031 := bstep (se 1 (by rfl) ⟨4527773, by rfl⟩ : syracuseStep 6037031 = 9055547) B9055547
theorem B16098749 : Blo 1883435 16098749 := bstep (se 3 (by rfl) ⟨3018515, by rfl⟩ : syracuseStep 16098749 = 6037031) B6037031
theorem B10732499 : Blo 1883435 10732499 := bstep (se 1 (by rfl) ⟨8049374, by rfl⟩ : syracuseStep 10732499 = 16098749) B16098749
theorem B7154999 : Blo 1883435 7154999 := bstep (se 1 (by rfl) ⟨5366249, by rfl⟩ : syracuseStep 7154999 = 10732499) B10732499
theorem B4769999 : Blo 1883435 4769999 := bstep (se 1 (by rfl) ⟨3577499, by rfl⟩ : syracuseStep 4769999 = 7154999) B7154999
theorem B3179999 : Blo 1883435 3179999 := bstep (se 1 (by rfl) ⟨2384999, by rfl⟩ : syracuseStep 3179999 = 4769999) B4769999
theorem B2119999 : Blo 1883435 2119999 := bstep (se 1 (by rfl) ⟨1589999, by rfl⟩ : syracuseStep 2119999 = 3179999) B3179999
theorem B2826665 : Blo 1883435 2826665 := bstep (se 2 (by rfl) ⟨1059999, by rfl⟩ : syracuseStep 2826665 = 2119999) B2119999
theorem B1884443 : Blo 1883435 1884443 := bstep (se 1 (by rfl) ⟨1413332, by rfl⟩ : syracuseStep 1884443 = 2826665) B2826665
theorem B7155013 : Blo 1883435 7155013 := bbase (se 4 (by rfl) ⟨670782, by rfl⟩ : syracuseStep 7155013 = 1341565) (by norm_num)
theorem B9540017 : Blo 1883435 9540017 := bstep (se 2 (by rfl) ⟨3577506, by rfl⟩ : syracuseStep 9540017 = 7155013) B7155013
theorem B6360011 : Blo 1883435 6360011 := bstep (se 1 (by rfl) ⟨4770008, by rfl⟩ : syracuseStep 6360011 = 9540017) B9540017
theorem B4240007 : Blo 1883435 4240007 := bstep (se 1 (by rfl) ⟨3180005, by rfl⟩ : syracuseStep 4240007 = 6360011) B6360011
theorem B2826671 : Blo 1883435 2826671 := bstep (se 1 (by rfl) ⟨2120003, by rfl⟩ : syracuseStep 2826671 = 4240007) B4240007
theorem B1884447 : Blo 1883435 1884447 := bstep (se 1 (by rfl) ⟨1413335, by rfl⟩ : syracuseStep 1884447 = 2826671) B2826671
theorem B2826677 : Blo 1883435 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B1884451 : Blo 1883435 1884451 := bstep (se 1 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 1884451 = 2826677) B2826677
theorem B4770029 : Blo 1883435 4770029 := bbase (se 3 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 4770029 = 1788761) (by norm_num)
theorem B3180019 : Blo 1883435 3180019 := bstep (se 1 (by rfl) ⟨2385014, by rfl⟩ : syracuseStep 3180019 = 4770029) B4770029
theorem B4240025 : Blo 1883435 4240025 := bstep (se 2 (by rfl) ⟨1590009, by rfl⟩ : syracuseStep 4240025 = 3180019) B3180019
theorem B2826683 : Blo 1883435 2826683 := bstep (se 1 (by rfl) ⟨2120012, by rfl⟩ : syracuseStep 2826683 = 4240025) B4240025
theorem B1884455 : Blo 1883435 1884455 := bstep (se 1 (by rfl) ⟨1413341, by rfl⟩ : syracuseStep 1884455 = 2826683) B2826683
theorem B2120017 : Blo 1883435 2120017 := bbase (se 2 (by rfl) ⟨795006, by rfl⟩ : syracuseStep 2120017 = 1590013) (by norm_num)
theorem B2826689 : Blo 1883435 2826689 := bstep (se 2 (by rfl) ⟨1060008, by rfl⟩ : syracuseStep 2826689 = 2120017) B2120017
theorem B1884459 : Blo 1883435 1884459 := bstep (se 1 (by rfl) ⟨1413344, by rfl⟩ : syracuseStep 1884459 = 2826689) B2826689
theorem B2012365 : Blo 1883435 2012365 := bbase (se 3 (by rfl) ⟨377318, by rfl⟩ : syracuseStep 2012365 = 754637) (by norm_num)
theorem B2683153 : Blo 1883435 2683153 := bstep (se 2 (by rfl) ⟨1006182, by rfl⟩ : syracuseStep 2683153 = 2012365) B2012365
theorem B3577537 : Blo 1883435 3577537 := bstep (se 2 (by rfl) ⟨1341576, by rfl⟩ : syracuseStep 3577537 = 2683153) B2683153
theorem B4770049 : Blo 1883435 4770049 := bstep (se 2 (by rfl) ⟨1788768, by rfl⟩ : syracuseStep 4770049 = 3577537) B3577537
theorem B6360065 : Blo 1883435 6360065 := bstep (se 2 (by rfl) ⟨2385024, by rfl⟩ : syracuseStep 6360065 = 4770049) B4770049
theorem B4240043 : Blo 1883435 4240043 := bstep (se 1 (by rfl) ⟨3180032, by rfl⟩ : syracuseStep 4240043 = 6360065) B6360065
theorem B2826695 : Blo 1883435 2826695 := bstep (se 1 (by rfl) ⟨2120021, by rfl⟩ : syracuseStep 2826695 = 4240043) B4240043
theorem B1884463 : Blo 1883435 1884463 := bstep (se 1 (by rfl) ⟨1413347, by rfl⟩ : syracuseStep 1884463 = 2826695) B2826695
theorem B2826701 : Blo 1883435 2826701 := bbase (se 3 (by rfl) ⟨530006, by rfl⟩ : syracuseStep 2826701 = 1060013) (by norm_num)
theorem B1884467 : Blo 1883435 1884467 := bstep (se 1 (by rfl) ⟨1413350, by rfl⟩ : syracuseStep 1884467 = 2826701) B2826701
theorem B4240061 : Blo 1883435 4240061 := bbase (se 3 (by rfl) ⟨795011, by rfl⟩ : syracuseStep 4240061 = 1590023) (by norm_num)
theorem B2826707 : Blo 1883435 2826707 := bstep (se 1 (by rfl) ⟨2120030, by rfl⟩ : syracuseStep 2826707 = 4240061) B4240061
theorem B1884471 : Blo 1883435 1884471 := bstep (se 1 (by rfl) ⟨1413353, by rfl⟩ : syracuseStep 1884471 = 2826707) B2826707
theorem B3180053 : Blo 1883435 3180053 := bbase (se 6 (by rfl) ⟨74532, by rfl⟩ : syracuseStep 3180053 = 149065) (by norm_num)
theorem B2120035 : Blo 1883435 2120035 := bstep (se 1 (by rfl) ⟨1590026, by rfl⟩ : syracuseStep 2120035 = 3180053) B3180053
theorem B2826713 : Blo 1883435 2826713 := bstep (se 2 (by rfl) ⟨1060017, by rfl⟩ : syracuseStep 2826713 = 2120035) B2120035
theorem B1884475 : Blo 1883435 1884475 := bstep (se 1 (by rfl) ⟨1413356, by rfl⟩ : syracuseStep 1884475 = 2826713) B2826713
theorem B4835173 : Blo 1883435 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B6446897 : Blo 1883435 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B4297931 : Blo 1883435 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B2865287 : Blo 1883435 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B1910191 : Blo 1883435 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B2546921 : Blo 1883435 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B6791789 : Blo 1883435 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B18111437 : Blo 1883435 18111437 := bstep (se 3 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 18111437 = 6791789) B6791789
theorem B12074291 : Blo 1883435 12074291 := bstep (se 1 (by rfl) ⟨9055718, by rfl⟩ : syracuseStep 12074291 = 18111437) B18111437
theorem B8049527 : Blo 1883435 8049527 := bstep (se 1 (by rfl) ⟨6037145, by rfl⟩ : syracuseStep 8049527 = 12074291) B12074291
theorem B5366351 : Blo 1883435 5366351 := bstep (se 1 (by rfl) ⟨4024763, by rfl⟩ : syracuseStep 5366351 = 8049527) B8049527
theorem B14310269 : Blo 1883435 14310269 := bstep (se 3 (by rfl) ⟨2683175, by rfl⟩ : syracuseStep 14310269 = 5366351) B5366351
theorem B9540179 : Blo 1883435 9540179 := bstep (se 1 (by rfl) ⟨7155134, by rfl⟩ : syracuseStep 9540179 = 14310269) B14310269
theorem B6360119 : Blo 1883435 6360119 := bstep (se 1 (by rfl) ⟨4770089, by rfl⟩ : syracuseStep 6360119 = 9540179) B9540179
theorem B4240079 : Blo 1883435 4240079 := bstep (se 1 (by rfl) ⟨3180059, by rfl⟩ : syracuseStep 4240079 = 6360119) B6360119
theorem B2826719 : Blo 1883435 2826719 := bstep (se 1 (by rfl) ⟨2120039, by rfl⟩ : syracuseStep 2826719 = 4240079) B4240079
theorem B1884479 : Blo 1883435 1884479 := bstep (se 1 (by rfl) ⟨1413359, by rfl⟩ : syracuseStep 1884479 = 2826719) B2826719
theorem B2826725 : Blo 1883435 2826725 := bbase (se 4 (by rfl) ⟨265005, by rfl⟩ : syracuseStep 2826725 = 530011) (by norm_num)
theorem B1884483 : Blo 1883435 1884483 := bstep (se 1 (by rfl) ⟨1413362, by rfl⟩ : syracuseStep 1884483 = 2826725) B2826725
theorem B4297949 : Blo 1883435 4297949 := bbase (se 3 (by rfl) ⟨805865, by rfl⟩ : syracuseStep 4297949 = 1611731) (by norm_num)
theorem B2865299 : Blo 1883435 2865299 := bstep (se 1 (by rfl) ⟨2148974, by rfl⟩ : syracuseStep 2865299 = 4297949) B4297949
theorem B30563189 : Blo 1883435 30563189 := bstep (se 5 (by rfl) ⟨1432649, by rfl⟩ : syracuseStep 30563189 = 2865299) B2865299
theorem B20375459 : Blo 1883435 20375459 := bstep (se 1 (by rfl) ⟨15281594, by rfl⟩ : syracuseStep 20375459 = 30563189) B30563189
theorem B13583639 : Blo 1883435 13583639 := bstep (se 1 (by rfl) ⟨10187729, by rfl⟩ : syracuseStep 13583639 = 20375459) B20375459
theorem B9055759 : Blo 1883435 9055759 := bstep (se 1 (by rfl) ⟨6791819, by rfl⟩ : syracuseStep 9055759 = 13583639) B13583639
theorem B12074345 : Blo 1883435 12074345 := bstep (se 2 (by rfl) ⟨4527879, by rfl⟩ : syracuseStep 12074345 = 9055759) B9055759
theorem B8049563 : Blo 1883435 8049563 := bstep (se 1 (by rfl) ⟨6037172, by rfl⟩ : syracuseStep 8049563 = 12074345) B12074345
theorem B5366375 : Blo 1883435 5366375 := bstep (se 1 (by rfl) ⟨4024781, by rfl⟩ : syracuseStep 5366375 = 8049563) B8049563
theorem B3577583 : Blo 1883435 3577583 := bstep (se 1 (by rfl) ⟨2683187, by rfl⟩ : syracuseStep 3577583 = 5366375) B5366375
theorem B2385055 : Blo 1883435 2385055 := bstep (se 1 (by rfl) ⟨1788791, by rfl⟩ : syracuseStep 2385055 = 3577583) B3577583
theorem B3180073 : Blo 1883435 3180073 := bstep (se 2 (by rfl) ⟨1192527, by rfl⟩ : syracuseStep 3180073 = 2385055) B2385055
theorem B4240097 : Blo 1883435 4240097 := bstep (se 2 (by rfl) ⟨1590036, by rfl⟩ : syracuseStep 4240097 = 3180073) B3180073
theorem B2826731 : Blo 1883435 2826731 := bstep (se 1 (by rfl) ⟨2120048, by rfl⟩ : syracuseStep 2826731 = 4240097) B4240097
theorem B1884487 : Blo 1883435 1884487 := bstep (se 1 (by rfl) ⟨1413365, by rfl⟩ : syracuseStep 1884487 = 2826731) B2826731
theorem B2120053 : Blo 1883435 2120053 := bbase (se 5 (by rfl) ⟨99377, by rfl⟩ : syracuseStep 2120053 = 198755) (by norm_num)
theorem B2826737 : Blo 1883435 2826737 := bstep (se 2 (by rfl) ⟨1060026, by rfl⟩ : syracuseStep 2826737 = 2120053) B2120053
theorem B1884491 : Blo 1883435 1884491 := bstep (se 1 (by rfl) ⟨1413368, by rfl⟩ : syracuseStep 1884491 = 2826737) B2826737
theorem B2385065 : Blo 1883435 2385065 := bbase (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) (by norm_num)
theorem B6360173 : Blo 1883435 6360173 := bstep (se 3 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 6360173 = 2385065) B2385065
theorem B4240115 : Blo 1883435 4240115 := bstep (se 1 (by rfl) ⟨3180086, by rfl⟩ : syracuseStep 4240115 = 6360173) B6360173
theorem B2826743 : Blo 1883435 2826743 := bstep (se 1 (by rfl) ⟨2120057, by rfl⟩ : syracuseStep 2826743 = 4240115) B4240115
theorem B1884495 : Blo 1883435 1884495 := bstep (se 1 (by rfl) ⟨1413371, by rfl⟩ : syracuseStep 1884495 = 2826743) B2826743
theorem B2826749 : Blo 1883435 2826749 := bbase (se 3 (by rfl) ⟨530015, by rfl⟩ : syracuseStep 2826749 = 1060031) (by norm_num)
theorem B1884499 : Blo 1883435 1884499 := bstep (se 1 (by rfl) ⟨1413374, by rfl⟩ : syracuseStep 1884499 = 2826749) B2826749
theorem B4240133 : Blo 1883435 4240133 := bbase (se 4 (by rfl) ⟨397512, by rfl⟩ : syracuseStep 4240133 = 795025) (by norm_num)
theorem B2826755 : Blo 1883435 2826755 := bstep (se 1 (by rfl) ⟨2120066, by rfl⟩ : syracuseStep 2826755 = 4240133) B4240133
theorem B1884503 : Blo 1883435 1884503 := bstep (se 1 (by rfl) ⟨1413377, by rfl⟩ : syracuseStep 1884503 = 2826755) B2826755
theorem B3577621 : Blo 1883435 3577621 := bbase (se 6 (by rfl) ⟨83850, by rfl⟩ : syracuseStep 3577621 = 167701) (by norm_num)
theorem B4770161 : Blo 1883435 4770161 := bstep (se 2 (by rfl) ⟨1788810, by rfl⟩ : syracuseStep 4770161 = 3577621) B3577621
theorem B3180107 : Blo 1883435 3180107 := bstep (se 1 (by rfl) ⟨2385080, by rfl⟩ : syracuseStep 3180107 = 4770161) B4770161
theorem B2120071 : Blo 1883435 2120071 := bstep (se 1 (by rfl) ⟨1590053, by rfl⟩ : syracuseStep 2120071 = 3180107) B3180107
theorem B2826761 : Blo 1883435 2826761 := bstep (se 2 (by rfl) ⟨1060035, by rfl⟩ : syracuseStep 2826761 = 2120071) B2120071
theorem B1884507 : Blo 1883435 1884507 := bstep (se 1 (by rfl) ⟨1413380, by rfl⟩ : syracuseStep 1884507 = 2826761) B2826761
theorem B9540341 : Blo 1883435 9540341 := bbase (se 5 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 9540341 = 894407) (by norm_num)
theorem B6360227 : Blo 1883435 6360227 := bstep (se 1 (by rfl) ⟨4770170, by rfl⟩ : syracuseStep 6360227 = 9540341) B9540341
theorem B4240151 : Blo 1883435 4240151 := bstep (se 1 (by rfl) ⟨3180113, by rfl⟩ : syracuseStep 4240151 = 6360227) B6360227
theorem B2826767 : Blo 1883435 2826767 := bstep (se 1 (by rfl) ⟨2120075, by rfl⟩ : syracuseStep 2826767 = 4240151) B4240151
theorem B1884511 : Blo 1883435 1884511 := bstep (se 1 (by rfl) ⟨1413383, by rfl⟩ : syracuseStep 1884511 = 2826767) B2826767
theorem B2826773 : Blo 1883435 2826773 := bbase (se 6 (by rfl) ⟨66252, by rfl⟩ : syracuseStep 2826773 = 132505) (by norm_num)
theorem B1884515 : Blo 1883435 1884515 := bstep (se 1 (by rfl) ⟨1413386, by rfl⟩ : syracuseStep 1884515 = 2826773) B2826773
theorem B3018637 : Blo 1883435 3018637 := bbase (se 3 (by rfl) ⟨565994, by rfl⟩ : syracuseStep 3018637 = 1131989) (by norm_num)
theorem B16099397 : Blo 1883435 16099397 := bstep (se 4 (by rfl) ⟨1509318, by rfl⟩ : syracuseStep 16099397 = 3018637) B3018637
theorem B10732931 : Blo 1883435 10732931 := bstep (se 1 (by rfl) ⟨8049698, by rfl⟩ : syracuseStep 10732931 = 16099397) B16099397
theorem B7155287 : Blo 1883435 7155287 := bstep (se 1 (by rfl) ⟨5366465, by rfl⟩ : syracuseStep 7155287 = 10732931) B10732931
theorem B4770191 : Blo 1883435 4770191 := bstep (se 1 (by rfl) ⟨3577643, by rfl⟩ : syracuseStep 4770191 = 7155287) B7155287
theorem B3180127 : Blo 1883435 3180127 := bstep (se 1 (by rfl) ⟨2385095, by rfl⟩ : syracuseStep 3180127 = 4770191) B4770191
theorem B4240169 : Blo 1883435 4240169 := bstep (se 2 (by rfl) ⟨1590063, by rfl⟩ : syracuseStep 4240169 = 3180127) B3180127
theorem B2826779 : Blo 1883435 2826779 := bstep (se 1 (by rfl) ⟨2120084, by rfl⟩ : syracuseStep 2826779 = 4240169) B4240169
theorem B1884519 : Blo 1883435 1884519 := bstep (se 1 (by rfl) ⟨1413389, by rfl⟩ : syracuseStep 1884519 = 2826779) B2826779
theorem B2120089 : Blo 1883435 2120089 := bbase (se 2 (by rfl) ⟨795033, by rfl⟩ : syracuseStep 2120089 = 1590067) (by norm_num)
theorem B2826785 : Blo 1883435 2826785 := bstep (se 2 (by rfl) ⟨1060044, by rfl⟩ : syracuseStep 2826785 = 2120089) B2120089
theorem B1884523 : Blo 1883435 1884523 := bstep (se 1 (by rfl) ⟨1413392, by rfl⟩ : syracuseStep 1884523 = 2826785) B2826785
theorem B7155317 : Blo 1883435 7155317 := bbase (se 5 (by rfl) ⟨335405, by rfl⟩ : syracuseStep 7155317 = 670811) (by norm_num)
theorem B4770211 : Blo 1883435 4770211 := bstep (se 1 (by rfl) ⟨3577658, by rfl⟩ : syracuseStep 4770211 = 7155317) B7155317
theorem B6360281 : Blo 1883435 6360281 := bstep (se 2 (by rfl) ⟨2385105, by rfl⟩ : syracuseStep 6360281 = 4770211) B4770211
theorem B4240187 : Blo 1883435 4240187 := bstep (se 1 (by rfl) ⟨3180140, by rfl⟩ : syracuseStep 4240187 = 6360281) B6360281
theorem B2826791 : Blo 1883435 2826791 := bstep (se 1 (by rfl) ⟨2120093, by rfl⟩ : syracuseStep 2826791 = 4240187) B4240187
theorem B1884527 : Blo 1883435 1884527 := bstep (se 1 (by rfl) ⟨1413395, by rfl⟩ : syracuseStep 1884527 = 2826791) B2826791
theorem B2826797 : Blo 1883435 2826797 := bbase (se 3 (by rfl) ⟨530024, by rfl⟩ : syracuseStep 2826797 = 1060049) (by norm_num)
theorem B1884531 : Blo 1883435 1884531 := bstep (se 1 (by rfl) ⟨1413398, by rfl⟩ : syracuseStep 1884531 = 2826797) B2826797
theorem B4240205 : Blo 1883435 4240205 := bbase (se 3 (by rfl) ⟨795038, by rfl⟩ : syracuseStep 4240205 = 1590077) (by norm_num)
theorem B2826803 : Blo 1883435 2826803 := bstep (se 1 (by rfl) ⟨2120102, by rfl⟩ : syracuseStep 2826803 = 4240205) B4240205
theorem B1884535 : Blo 1883435 1884535 := bstep (se 1 (by rfl) ⟨1413401, by rfl⟩ : syracuseStep 1884535 = 2826803) B2826803
theorem B2385121 : Blo 1883435 2385121 := bbase (se 2 (by rfl) ⟨894420, by rfl⟩ : syracuseStep 2385121 = 1788841) (by norm_num)
theorem B3180161 : Blo 1883435 3180161 := bstep (se 2 (by rfl) ⟨1192560, by rfl⟩ : syracuseStep 3180161 = 2385121) B2385121
theorem B2120107 : Blo 1883435 2120107 := bstep (se 1 (by rfl) ⟨1590080, by rfl⟩ : syracuseStep 2120107 = 3180161) B3180161
theorem B2826809 : Blo 1883435 2826809 := bstep (se 2 (by rfl) ⟨1060053, by rfl⟩ : syracuseStep 2826809 = 2120107) B2120107
theorem B1884539 : Blo 1883435 1884539 := bstep (se 1 (by rfl) ⟨1413404, by rfl⟩ : syracuseStep 1884539 = 2826809) B2826809
theorem B21466133 : Blo 1883435 21466133 := bbase (se 6 (by rfl) ⟨503112, by rfl⟩ : syracuseStep 21466133 = 1006225) (by norm_num)
theorem B14310755 : Blo 1883435 14310755 := bstep (se 1 (by rfl) ⟨10733066, by rfl⟩ : syracuseStep 14310755 = 21466133) B21466133
theorem B9540503 : Blo 1883435 9540503 := bstep (se 1 (by rfl) ⟨7155377, by rfl⟩ : syracuseStep 9540503 = 14310755) B14310755
theorem B6360335 : Blo 1883435 6360335 := bstep (se 1 (by rfl) ⟨4770251, by rfl⟩ : syracuseStep 6360335 = 9540503) B9540503
theorem B4240223 : Blo 1883435 4240223 := bstep (se 1 (by rfl) ⟨3180167, by rfl⟩ : syracuseStep 4240223 = 6360335) B6360335
theorem B2826815 : Blo 1883435 2826815 := bstep (se 1 (by rfl) ⟨2120111, by rfl⟩ : syracuseStep 2826815 = 4240223) B4240223
theorem B1884543 : Blo 1883435 1884543 := bstep (se 1 (by rfl) ⟨1413407, by rfl⟩ : syracuseStep 1884543 = 2826815) B2826815
theorem B2826821 : Blo 1883435 2826821 := bbase (se 4 (by rfl) ⟨265014, by rfl⟩ : syracuseStep 2826821 = 530029) (by norm_num)
theorem B1884547 : Blo 1883435 1884547 := bstep (se 1 (by rfl) ⟨1413410, by rfl⟩ : syracuseStep 1884547 = 2826821) B2826821
theorem B3180181 : Blo 1883435 3180181 := bbase (se 6 (by rfl) ⟨74535, by rfl⟩ : syracuseStep 3180181 = 149071) (by norm_num)
theorem B4240241 : Blo 1883435 4240241 := bstep (se 2 (by rfl) ⟨1590090, by rfl⟩ : syracuseStep 4240241 = 3180181) B3180181
theorem B2826827 : Blo 1883435 2826827 := bstep (se 1 (by rfl) ⟨2120120, by rfl⟩ : syracuseStep 2826827 = 4240241) B4240241
theorem B1884551 : Blo 1883435 1884551 := bstep (se 1 (by rfl) ⟨1413413, by rfl⟩ : syracuseStep 1884551 = 2826827) B2826827
theorem B2120125 : Blo 1883435 2120125 := bbase (se 3 (by rfl) ⟨397523, by rfl⟩ : syracuseStep 2120125 = 795047) (by norm_num)
theorem B2826833 : Blo 1883435 2826833 := bstep (se 2 (by rfl) ⟨1060062, by rfl⟩ : syracuseStep 2826833 = 2120125) B2120125
theorem B1884555 : Blo 1883435 1884555 := bstep (se 1 (by rfl) ⟨1413416, by rfl⟩ : syracuseStep 1884555 = 2826833) B2826833
theorem B6360389 : Blo 1883435 6360389 := bbase (se 4 (by rfl) ⟨596286, by rfl⟩ : syracuseStep 6360389 = 1192573) (by norm_num)
theorem B4240259 : Blo 1883435 4240259 := bstep (se 1 (by rfl) ⟨3180194, by rfl⟩ : syracuseStep 4240259 = 6360389) B6360389
theorem B2826839 : Blo 1883435 2826839 := bstep (se 1 (by rfl) ⟨2120129, by rfl⟩ : syracuseStep 2826839 = 4240259) B4240259
theorem B1884559 : Blo 1883435 1884559 := bstep (se 1 (by rfl) ⟨1413419, by rfl⟩ : syracuseStep 1884559 = 2826839) B2826839
theorem B2826845 : Blo 1883435 2826845 := bbase (se 3 (by rfl) ⟨530033, by rfl⟩ : syracuseStep 2826845 = 1060067) (by norm_num)
theorem B1884563 : Blo 1883435 1884563 := bstep (se 1 (by rfl) ⟨1413422, by rfl⟩ : syracuseStep 1884563 = 2826845) B2826845
theorem B4240277 : Blo 1883435 4240277 := bbase (se 6 (by rfl) ⟨99381, by rfl⟩ : syracuseStep 4240277 = 198763) (by norm_num)
theorem B2826851 : Blo 1883435 2826851 := bstep (se 1 (by rfl) ⟨2120138, by rfl⟩ : syracuseStep 2826851 = 4240277) B4240277
theorem B1884567 : Blo 1883435 1884567 := bstep (se 1 (by rfl) ⟨1413425, by rfl⟩ : syracuseStep 1884567 = 2826851) B2826851
theorem B2264041 : Blo 1883435 2264041 := bbase (se 2 (by rfl) ⟨849015, by rfl⟩ : syracuseStep 2264041 = 1698031) (by norm_num)
theorem B3018721 : Blo 1883435 3018721 := bstep (se 2 (by rfl) ⟨1132020, by rfl⟩ : syracuseStep 3018721 = 2264041) B2264041
theorem B4024961 : Blo 1883435 4024961 := bstep (se 2 (by rfl) ⟨1509360, by rfl⟩ : syracuseStep 4024961 = 3018721) B3018721
theorem B2683307 : Blo 1883435 2683307 := bstep (se 1 (by rfl) ⟨2012480, by rfl⟩ : syracuseStep 2683307 = 4024961) B4024961
theorem B7155485 : Blo 1883435 7155485 := bstep (se 3 (by rfl) ⟨1341653, by rfl⟩ : syracuseStep 7155485 = 2683307) B2683307
theorem B4770323 : Blo 1883435 4770323 := bstep (se 1 (by rfl) ⟨3577742, by rfl⟩ : syracuseStep 4770323 = 7155485) B7155485
theorem B3180215 : Blo 1883435 3180215 := bstep (se 1 (by rfl) ⟨2385161, by rfl⟩ : syracuseStep 3180215 = 4770323) B4770323
theorem B2120143 : Blo 1883435 2120143 := bstep (se 1 (by rfl) ⟨1590107, by rfl⟩ : syracuseStep 2120143 = 3180215) B3180215
theorem B2826857 : Blo 1883435 2826857 := bstep (se 2 (by rfl) ⟨1060071, by rfl⟩ : syracuseStep 2826857 = 2120143) B2120143
theorem B1884571 : Blo 1883435 1884571 := bstep (se 1 (by rfl) ⟨1413428, by rfl⟩ : syracuseStep 1884571 = 2826857) B2826857
theorem B2264045 : Blo 1883435 2264045 := bbase (se 3 (by rfl) ⟨424508, by rfl⟩ : syracuseStep 2264045 = 849017) (by norm_num)
theorem B6037453 : Blo 1883435 6037453 := bstep (se 3 (by rfl) ⟨1132022, by rfl⟩ : syracuseStep 6037453 = 2264045) B2264045
theorem B8049937 : Blo 1883435 8049937 := bstep (se 2 (by rfl) ⟨3018726, by rfl⟩ : syracuseStep 8049937 = 6037453) B6037453
theorem B10733249 : Blo 1883435 10733249 := bstep (se 2 (by rfl) ⟨4024968, by rfl⟩ : syracuseStep 10733249 = 8049937) B8049937
theorem B7155499 : Blo 1883435 7155499 := bstep (se 1 (by rfl) ⟨5366624, by rfl⟩ : syracuseStep 7155499 = 10733249) B10733249
theorem B9540665 : Blo 1883435 9540665 := bstep (se 2 (by rfl) ⟨3577749, by rfl⟩ : syracuseStep 9540665 = 7155499) B7155499
theorem B6360443 : Blo 1883435 6360443 := bstep (se 1 (by rfl) ⟨4770332, by rfl⟩ : syracuseStep 6360443 = 9540665) B9540665
theorem B4240295 : Blo 1883435 4240295 := bstep (se 1 (by rfl) ⟨3180221, by rfl⟩ : syracuseStep 4240295 = 6360443) B6360443
theorem B2826863 : Blo 1883435 2826863 := bstep (se 1 (by rfl) ⟨2120147, by rfl⟩ : syracuseStep 2826863 = 4240295) B4240295
theorem B1884575 : Blo 1883435 1884575 := bstep (se 1 (by rfl) ⟨1413431, by rfl⟩ : syracuseStep 1884575 = 2826863) B2826863
theorem B2826869 : Blo 1883435 2826869 := bbase (se 5 (by rfl) ⟨132509, by rfl⟩ : syracuseStep 2826869 = 265019) (by norm_num)
theorem B1884579 : Blo 1883435 1884579 := bstep (se 1 (by rfl) ⟨1413434, by rfl⟩ : syracuseStep 1884579 = 2826869) B2826869
theorem B3577765 : Blo 1883435 3577765 := bbase (se 4 (by rfl) ⟨335415, by rfl⟩ : syracuseStep 3577765 = 670831) (by norm_num)
theorem B4770353 : Blo 1883435 4770353 := bstep (se 2 (by rfl) ⟨1788882, by rfl⟩ : syracuseStep 4770353 = 3577765) B3577765
theorem B3180235 : Blo 1883435 3180235 := bstep (se 1 (by rfl) ⟨2385176, by rfl⟩ : syracuseStep 3180235 = 4770353) B4770353
theorem B4240313 : Blo 1883435 4240313 := bstep (se 2 (by rfl) ⟨1590117, by rfl⟩ : syracuseStep 4240313 = 3180235) B3180235
theorem B2826875 : Blo 1883435 2826875 := bstep (se 1 (by rfl) ⟨2120156, by rfl⟩ : syracuseStep 2826875 = 4240313) B4240313
theorem B1884583 : Blo 1883435 1884583 := bstep (se 1 (by rfl) ⟨1413437, by rfl⟩ : syracuseStep 1884583 = 2826875) B2826875
theorem B2120161 : Blo 1883435 2120161 := bbase (se 2 (by rfl) ⟨795060, by rfl⟩ : syracuseStep 2120161 = 1590121) (by norm_num)
theorem B2826881 : Blo 1883435 2826881 := bstep (se 2 (by rfl) ⟨1060080, by rfl⟩ : syracuseStep 2826881 = 2120161) B2120161
theorem B1884587 : Blo 1883435 1884587 := bstep (se 1 (by rfl) ⟨1413440, by rfl⟩ : syracuseStep 1884587 = 2826881) B2826881
theorem B4770373 : Blo 1883435 4770373 := bbase (se 4 (by rfl) ⟨447222, by rfl⟩ : syracuseStep 4770373 = 894445) (by norm_num)
theorem B6360497 : Blo 1883435 6360497 := bstep (se 2 (by rfl) ⟨2385186, by rfl⟩ : syracuseStep 6360497 = 4770373) B4770373
theorem B4240331 : Blo 1883435 4240331 := bstep (se 1 (by rfl) ⟨3180248, by rfl⟩ : syracuseStep 4240331 = 6360497) B6360497
theorem B2826887 : Blo 1883435 2826887 := bstep (se 1 (by rfl) ⟨2120165, by rfl⟩ : syracuseStep 2826887 = 4240331) B4240331
theorem B1884591 : Blo 1883435 1884591 := bstep (se 1 (by rfl) ⟨1413443, by rfl⟩ : syracuseStep 1884591 = 2826887) B2826887
theorem B2826893 : Blo 1883435 2826893 := bbase (se 3 (by rfl) ⟨530042, by rfl⟩ : syracuseStep 2826893 = 1060085) (by norm_num)
theorem B1884595 : Blo 1883435 1884595 := bstep (se 1 (by rfl) ⟨1413446, by rfl⟩ : syracuseStep 1884595 = 2826893) B2826893
theorem B4240349 : Blo 1883435 4240349 := bbase (se 3 (by rfl) ⟨795065, by rfl⟩ : syracuseStep 4240349 = 1590131) (by norm_num)
theorem B2826899 : Blo 1883435 2826899 := bstep (se 1 (by rfl) ⟨2120174, by rfl⟩ : syracuseStep 2826899 = 4240349) B4240349
theorem B1884599 : Blo 1883435 1884599 := bstep (se 1 (by rfl) ⟨1413449, by rfl⟩ : syracuseStep 1884599 = 2826899) B2826899
theorem B3180269 : Blo 1883435 3180269 := bbase (se 3 (by rfl) ⟨596300, by rfl⟩ : syracuseStep 3180269 = 1192601) (by norm_num)
theorem B2120179 : Blo 1883435 2120179 := bstep (se 1 (by rfl) ⟨1590134, by rfl⟩ : syracuseStep 2120179 = 3180269) B3180269
theorem B2826905 : Blo 1883435 2826905 := bstep (se 2 (by rfl) ⟨1060089, by rfl⟩ : syracuseStep 2826905 = 2120179) B2120179
theorem B1884603 : Blo 1883435 1884603 := bstep (se 1 (by rfl) ⟨1413452, by rfl⟩ : syracuseStep 1884603 = 2826905) B2826905
theorem B3396125 : Blo 1883435 3396125 := bbase (se 3 (by rfl) ⟨636773, by rfl⟩ : syracuseStep 3396125 = 1273547) (by norm_num)
theorem B9056333 : Blo 1883435 9056333 := bstep (se 3 (by rfl) ⟨1698062, by rfl⟩ : syracuseStep 9056333 = 3396125) B3396125
theorem B24150221 : Blo 1883435 24150221 := bstep (se 3 (by rfl) ⟨4528166, by rfl⟩ : syracuseStep 24150221 = 9056333) B9056333
theorem B16100147 : Blo 1883435 16100147 := bstep (se 1 (by rfl) ⟨12075110, by rfl⟩ : syracuseStep 16100147 = 24150221) B24150221
theorem B10733431 : Blo 1883435 10733431 := bstep (se 1 (by rfl) ⟨8050073, by rfl⟩ : syracuseStep 10733431 = 16100147) B16100147
theorem B14311241 : Blo 1883435 14311241 := bstep (se 2 (by rfl) ⟨5366715, by rfl⟩ : syracuseStep 14311241 = 10733431) B10733431
theorem B9540827 : Blo 1883435 9540827 := bstep (se 1 (by rfl) ⟨7155620, by rfl⟩ : syracuseStep 9540827 = 14311241) B14311241
theorem B6360551 : Blo 1883435 6360551 := bstep (se 1 (by rfl) ⟨4770413, by rfl⟩ : syracuseStep 6360551 = 9540827) B9540827
theorem B4240367 : Blo 1883435 4240367 := bstep (se 1 (by rfl) ⟨3180275, by rfl⟩ : syracuseStep 4240367 = 6360551) B6360551
theorem B2826911 : Blo 1883435 2826911 := bstep (se 1 (by rfl) ⟨2120183, by rfl⟩ : syracuseStep 2826911 = 4240367) B4240367
theorem B1884607 : Blo 1883435 1884607 := bstep (se 1 (by rfl) ⟨1413455, by rfl⟩ : syracuseStep 1884607 = 2826911) B2826911
theorem B2826917 : Blo 1883435 2826917 := bbase (se 4 (by rfl) ⟨265023, by rfl⟩ : syracuseStep 2826917 = 530047) (by norm_num)
theorem B1884611 : Blo 1883435 1884611 := bstep (se 1 (by rfl) ⟨1413458, by rfl⟩ : syracuseStep 1884611 = 2826917) B2826917
theorem B2385217 : Blo 1883435 2385217 := bbase (se 2 (by rfl) ⟨894456, by rfl⟩ : syracuseStep 2385217 = 1788913) (by norm_num)
theorem B3180289 : Blo 1883435 3180289 := bstep (se 2 (by rfl) ⟨1192608, by rfl⟩ : syracuseStep 3180289 = 2385217) B2385217
theorem B4240385 : Blo 1883435 4240385 := bstep (se 2 (by rfl) ⟨1590144, by rfl⟩ : syracuseStep 4240385 = 3180289) B3180289
theorem B2826923 : Blo 1883435 2826923 := bstep (se 1 (by rfl) ⟨2120192, by rfl⟩ : syracuseStep 2826923 = 4240385) B4240385
theorem B1884615 : Blo 1883435 1884615 := bstep (se 1 (by rfl) ⟨1413461, by rfl⟩ : syracuseStep 1884615 = 2826923) B2826923
theorem B2120197 : Blo 1883435 2120197 := bbase (se 4 (by rfl) ⟨198768, by rfl⟩ : syracuseStep 2120197 = 397537) (by norm_num)
theorem B2826929 : Blo 1883435 2826929 := bstep (se 2 (by rfl) ⟨1060098, by rfl⟩ : syracuseStep 2826929 = 2120197) B2120197
theorem B1884619 : Blo 1883435 1884619 := bstep (se 1 (by rfl) ⟨1413464, by rfl⟩ : syracuseStep 1884619 = 2826929) B2826929
theorem B2683381 : Blo 1883435 2683381 := bbase (se 5 (by rfl) ⟨125783, by rfl⟩ : syracuseStep 2683381 = 251567) (by norm_num)
theorem B3577841 : Blo 1883435 3577841 := bstep (se 2 (by rfl) ⟨1341690, by rfl⟩ : syracuseStep 3577841 = 2683381) B2683381
theorem B2385227 : Blo 1883435 2385227 := bstep (se 1 (by rfl) ⟨1788920, by rfl⟩ : syracuseStep 2385227 = 3577841) B3577841
theorem B6360605 : Blo 1883435 6360605 := bstep (se 3 (by rfl) ⟨1192613, by rfl⟩ : syracuseStep 6360605 = 2385227) B2385227
theorem B4240403 : Blo 1883435 4240403 := bstep (se 1 (by rfl) ⟨3180302, by rfl⟩ : syracuseStep 4240403 = 6360605) B6360605
theorem B2826935 : Blo 1883435 2826935 := bstep (se 1 (by rfl) ⟨2120201, by rfl⟩ : syracuseStep 2826935 = 4240403) B4240403
theorem B1884623 : Blo 1883435 1884623 := bstep (se 1 (by rfl) ⟨1413467, by rfl⟩ : syracuseStep 1884623 = 2826935) B2826935
theorem B2826941 : Blo 1883435 2826941 := bbase (se 3 (by rfl) ⟨530051, by rfl⟩ : syracuseStep 2826941 = 1060103) (by norm_num)
theorem B1884627 : Blo 1883435 1884627 := bstep (se 1 (by rfl) ⟨1413470, by rfl⟩ : syracuseStep 1884627 = 2826941) B2826941
theorem B4240421 : Blo 1883435 4240421 := bbase (se 4 (by rfl) ⟨397539, by rfl⟩ : syracuseStep 4240421 = 795079) (by norm_num)
theorem B2826947 : Blo 1883435 2826947 := bstep (se 1 (by rfl) ⟨2120210, by rfl⟩ : syracuseStep 2826947 = 4240421) B4240421
theorem B1884631 : Blo 1883435 1884631 := bstep (se 1 (by rfl) ⟨1413473, by rfl⟩ : syracuseStep 1884631 = 2826947) B2826947
theorem B4770485 : Blo 1883435 4770485 := bbase (se 5 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 4770485 = 447233) (by norm_num)
theorem B3180323 : Blo 1883435 3180323 := bstep (se 1 (by rfl) ⟨2385242, by rfl⟩ : syracuseStep 3180323 = 4770485) B4770485
theorem B2120215 : Blo 1883435 2120215 := bstep (se 1 (by rfl) ⟨1590161, by rfl⟩ : syracuseStep 2120215 = 3180323) B3180323
theorem B2826953 : Blo 1883435 2826953 := bstep (se 2 (by rfl) ⟨1060107, by rfl⟩ : syracuseStep 2826953 = 2120215) B2120215
theorem B1884635 : Blo 1883435 1884635 := bstep (se 1 (by rfl) ⟨1413476, by rfl⟩ : syracuseStep 1884635 = 2826953) B2826953
theorem B12075317 : Blo 1883435 12075317 := bbase (se 5 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 12075317 = 1132061) (by norm_num)
theorem B8050211 : Blo 1883435 8050211 := bstep (se 1 (by rfl) ⟨6037658, by rfl⟩ : syracuseStep 8050211 = 12075317) B12075317
theorem B5366807 : Blo 1883435 5366807 := bstep (se 1 (by rfl) ⟨4025105, by rfl⟩ : syracuseStep 5366807 = 8050211) B8050211
theorem B3577871 : Blo 1883435 3577871 := bstep (se 1 (by rfl) ⟨2683403, by rfl⟩ : syracuseStep 3577871 = 5366807) B5366807
theorem B9540989 : Blo 1883435 9540989 := bstep (se 3 (by rfl) ⟨1788935, by rfl⟩ : syracuseStep 9540989 = 3577871) B3577871
theorem B6360659 : Blo 1883435 6360659 := bstep (se 1 (by rfl) ⟨4770494, by rfl⟩ : syracuseStep 6360659 = 9540989) B9540989
theorem B4240439 : Blo 1883435 4240439 := bstep (se 1 (by rfl) ⟨3180329, by rfl⟩ : syracuseStep 4240439 = 6360659) B6360659
theorem B2826959 : Blo 1883435 2826959 := bstep (se 1 (by rfl) ⟨2120219, by rfl⟩ : syracuseStep 2826959 = 4240439) B4240439
theorem B1884639 : Blo 1883435 1884639 := bstep (se 1 (by rfl) ⟨1413479, by rfl⟩ : syracuseStep 1884639 = 2826959) B2826959
theorem B2826965 : Blo 1883435 2826965 := bbase (se 7 (by rfl) ⟨33128, by rfl⟩ : syracuseStep 2826965 = 66257) (by norm_num)
theorem B1884643 : Blo 1883435 1884643 := bstep (se 1 (by rfl) ⟨1413482, by rfl⟩ : syracuseStep 1884643 = 2826965) B2826965
theorem B6037685 : Blo 1883435 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B4025123 : Blo 1883435 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B2683415 : Blo 1883435 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B7155773 : Blo 1883435 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B4770515 : Blo 1883435 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B3180343 : Blo 1883435 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B4240457 : Blo 1883435 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B2826971 : Blo 1883435 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1884647 : Blo 1883435 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B2120233 : Blo 1883435 2120233 := bbase (se 2 (by rfl) ⟨795087, by rfl⟩ : syracuseStep 2120233 = 1590175) (by norm_num)
theorem B2826977 : Blo 1883435 2826977 := bstep (se 2 (by rfl) ⟨1060116, by rfl⟩ : syracuseStep 2826977 = 2120233) B2120233
theorem B1884651 : Blo 1883435 1884651 := bstep (se 1 (by rfl) ⟨1413488, by rfl⟩ : syracuseStep 1884651 = 2826977) B2826977
theorem B6120085 : Blo 1883435 6120085 := bbase (se 6 (by rfl) ⟨143439, by rfl⟩ : syracuseStep 6120085 = 286879) (by norm_num)
theorem B8160113 : Blo 1883435 8160113 := bstep (se 2 (by rfl) ⟨3060042, by rfl⟩ : syracuseStep 8160113 = 6120085) B6120085
theorem B21760301 : Blo 1883435 21760301 := bstep (se 3 (by rfl) ⟨4080056, by rfl⟩ : syracuseStep 21760301 = 8160113) B8160113
theorem B14506867 : Blo 1883435 14506867 := bstep (se 1 (by rfl) ⟨10880150, by rfl⟩ : syracuseStep 14506867 = 21760301) B21760301
theorem B19342489 : Blo 1883435 19342489 := bstep (se 2 (by rfl) ⟨7253433, by rfl⟩ : syracuseStep 19342489 = 14506867) B14506867
theorem B25789985 : Blo 1883435 25789985 := bstep (se 2 (by rfl) ⟨9671244, by rfl⟩ : syracuseStep 25789985 = 19342489) B19342489
theorem B17193323 : Blo 1883435 17193323 := bstep (se 1 (by rfl) ⟨12894992, by rfl⟩ : syracuseStep 17193323 = 25789985) B25789985
theorem B45848861 : Blo 1883435 45848861 := bstep (se 3 (by rfl) ⟨8596661, by rfl⟩ : syracuseStep 45848861 = 17193323) B17193323
theorem B30565907 : Blo 1883435 30565907 := bstep (se 1 (by rfl) ⟨22924430, by rfl⟩ : syracuseStep 30565907 = 45848861) B45848861
theorem B20377271 : Blo 1883435 20377271 := bstep (se 1 (by rfl) ⟨15282953, by rfl⟩ : syracuseStep 20377271 = 30565907) B30565907
theorem B13584847 : Blo 1883435 13584847 := bstep (se 1 (by rfl) ⟨10188635, by rfl⟩ : syracuseStep 13584847 = 20377271) B20377271
theorem B18113129 : Blo 1883435 18113129 := bstep (se 2 (by rfl) ⟨6792423, by rfl⟩ : syracuseStep 18113129 = 13584847) B13584847
theorem B12075419 : Blo 1883435 12075419 := bstep (se 1 (by rfl) ⟨9056564, by rfl⟩ : syracuseStep 12075419 = 18113129) B18113129
theorem B8050279 : Blo 1883435 8050279 := bstep (se 1 (by rfl) ⟨6037709, by rfl⟩ : syracuseStep 8050279 = 12075419) B12075419
theorem B10733705 : Blo 1883435 10733705 := bstep (se 2 (by rfl) ⟨4025139, by rfl⟩ : syracuseStep 10733705 = 8050279) B8050279
theorem B7155803 : Blo 1883435 7155803 := bstep (se 1 (by rfl) ⟨5366852, by rfl⟩ : syracuseStep 7155803 = 10733705) B10733705
theorem B4770535 : Blo 1883435 4770535 := bstep (se 1 (by rfl) ⟨3577901, by rfl⟩ : syracuseStep 4770535 = 7155803) B7155803
theorem B6360713 : Blo 1883435 6360713 := bstep (se 2 (by rfl) ⟨2385267, by rfl⟩ : syracuseStep 6360713 = 4770535) B4770535
theorem B4240475 : Blo 1883435 4240475 := bstep (se 1 (by rfl) ⟨3180356, by rfl⟩ : syracuseStep 4240475 = 6360713) B6360713
theorem B2826983 : Blo 1883435 2826983 := bstep (se 1 (by rfl) ⟨2120237, by rfl⟩ : syracuseStep 2826983 = 4240475) B4240475
theorem B1884655 : Blo 1883435 1884655 := bstep (se 1 (by rfl) ⟨1413491, by rfl⟩ : syracuseStep 1884655 = 2826983) B2826983
theorem B2826989 : Blo 1883435 2826989 := bbase (se 3 (by rfl) ⟨530060, by rfl⟩ : syracuseStep 2826989 = 1060121) (by norm_num)
theorem B1884659 : Blo 1883435 1884659 := bstep (se 1 (by rfl) ⟨1413494, by rfl⟩ : syracuseStep 1884659 = 2826989) B2826989
theorem B4240493 : Blo 1883435 4240493 := bbase (se 3 (by rfl) ⟨795092, by rfl⟩ : syracuseStep 4240493 = 1590185) (by norm_num)
theorem B2826995 : Blo 1883435 2826995 := bstep (se 1 (by rfl) ⟨2120246, by rfl⟩ : syracuseStep 2826995 = 4240493) B4240493
theorem B1884663 : Blo 1883435 1884663 := bstep (se 1 (by rfl) ⟨1413497, by rfl⟩ : syracuseStep 1884663 = 2826995) B2826995
theorem B3577925 : Blo 1883435 3577925 := bbase (se 4 (by rfl) ⟨335430, by rfl⟩ : syracuseStep 3577925 = 670861) (by norm_num)
theorem B2385283 : Blo 1883435 2385283 := bstep (se 1 (by rfl) ⟨1788962, by rfl⟩ : syracuseStep 2385283 = 3577925) B3577925
theorem B3180377 : Blo 1883435 3180377 := bstep (se 2 (by rfl) ⟨1192641, by rfl⟩ : syracuseStep 3180377 = 2385283) B2385283
theorem B2120251 : Blo 1883435 2120251 := bstep (se 1 (by rfl) ⟨1590188, by rfl⟩ : syracuseStep 2120251 = 3180377) B3180377
theorem B2827001 : Blo 1883435 2827001 := bstep (se 2 (by rfl) ⟨1060125, by rfl⟩ : syracuseStep 2827001 = 2120251) B2120251
theorem B1884667 : Blo 1883435 1884667 := bstep (se 1 (by rfl) ⟨1413500, by rfl⟩ : syracuseStep 1884667 = 2827001) B2827001
theorem B32640725 : Blo 1883435 32640725 := bbase (se 7 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 32640725 = 765017) (by norm_num)
theorem B21760483 : Blo 1883435 21760483 := bstep (se 1 (by rfl) ⟨16320362, by rfl⟩ : syracuseStep 21760483 = 32640725) B32640725
theorem B29013977 : Blo 1883435 29013977 := bstep (se 2 (by rfl) ⟨10880241, by rfl⟩ : syracuseStep 29013977 = 21760483) B21760483
theorem B19342651 : Blo 1883435 19342651 := bstep (se 1 (by rfl) ⟨14506988, by rfl⟩ : syracuseStep 19342651 = 29013977) B29013977
theorem B25790201 : Blo 1883435 25790201 := bstep (se 2 (by rfl) ⟨9671325, by rfl⟩ : syracuseStep 25790201 = 19342651) B19342651
theorem B17193467 : Blo 1883435 17193467 := bstep (se 1 (by rfl) ⟨12895100, by rfl⟩ : syracuseStep 17193467 = 25790201) B25790201
theorem B11462311 : Blo 1883435 11462311 := bstep (se 1 (by rfl) ⟨8596733, by rfl⟩ : syracuseStep 11462311 = 17193467) B17193467
theorem B15283081 : Blo 1883435 15283081 := bstep (se 2 (by rfl) ⟨5731155, by rfl⟩ : syracuseStep 15283081 = 11462311) B11462311
theorem B20377441 : Blo 1883435 20377441 := bstep (se 2 (by rfl) ⟨7641540, by rfl⟩ : syracuseStep 20377441 = 15283081) B15283081
theorem B27169921 : Blo 1883435 27169921 := bstep (se 2 (by rfl) ⟨10188720, by rfl⟩ : syracuseStep 27169921 = 20377441) B20377441
theorem B36226561 : Blo 1883435 36226561 := bstep (se 2 (by rfl) ⟨13584960, by rfl⟩ : syracuseStep 36226561 = 27169921) B27169921
theorem B48302081 : Blo 1883435 48302081 := bstep (se 2 (by rfl) ⟨18113280, by rfl⟩ : syracuseStep 48302081 = 36226561) B36226561
theorem B32201387 : Blo 1883435 32201387 := bstep (se 1 (by rfl) ⟨24151040, by rfl⟩ : syracuseStep 32201387 = 48302081) B48302081
theorem B21467591 : Blo 1883435 21467591 := bstep (se 1 (by rfl) ⟨16100693, by rfl⟩ : syracuseStep 21467591 = 32201387) B32201387
theorem B14311727 : Blo 1883435 14311727 := bstep (se 1 (by rfl) ⟨10733795, by rfl⟩ : syracuseStep 14311727 = 21467591) B21467591
theorem B9541151 : Blo 1883435 9541151 := bstep (se 1 (by rfl) ⟨7155863, by rfl⟩ : syracuseStep 9541151 = 14311727) B14311727
theorem B6360767 : Blo 1883435 6360767 := bstep (se 1 (by rfl) ⟨4770575, by rfl⟩ : syracuseStep 6360767 = 9541151) B9541151
theorem B4240511 : Blo 1883435 4240511 := bstep (se 1 (by rfl) ⟨3180383, by rfl⟩ : syracuseStep 4240511 = 6360767) B6360767
theorem B2827007 : Blo 1883435 2827007 := bstep (se 1 (by rfl) ⟨2120255, by rfl⟩ : syracuseStep 2827007 = 4240511) B4240511
theorem B1884671 : Blo 1883435 1884671 := bstep (se 1 (by rfl) ⟨1413503, by rfl⟩ : syracuseStep 1884671 = 2827007) B2827007
theorem B2827013 : Blo 1883435 2827013 := bbase (se 4 (by rfl) ⟨265032, by rfl⟩ : syracuseStep 2827013 = 530065) (by norm_num)
theorem B1884675 : Blo 1883435 1884675 := bstep (se 1 (by rfl) ⟨1413506, by rfl⟩ : syracuseStep 1884675 = 2827013) B2827013
theorem B3180397 : Blo 1883435 3180397 := bbase (se 3 (by rfl) ⟨596324, by rfl⟩ : syracuseStep 3180397 = 1192649) (by norm_num)
theorem B4240529 : Blo 1883435 4240529 := bstep (se 2 (by rfl) ⟨1590198, by rfl⟩ : syracuseStep 4240529 = 3180397) B3180397
theorem B2827019 : Blo 1883435 2827019 := bstep (se 1 (by rfl) ⟨2120264, by rfl⟩ : syracuseStep 2827019 = 4240529) B4240529
theorem B1884679 : Blo 1883435 1884679 := bstep (se 1 (by rfl) ⟨1413509, by rfl⟩ : syracuseStep 1884679 = 2827019) B2827019
theorem B2120269 : Blo 1883435 2120269 := bbase (se 3 (by rfl) ⟨397550, by rfl⟩ : syracuseStep 2120269 = 795101) (by norm_num)
theorem B2827025 : Blo 1883435 2827025 := bstep (se 2 (by rfl) ⟨1060134, by rfl⟩ : syracuseStep 2827025 = 2120269) B2120269
theorem B1884683 : Blo 1883435 1884683 := bstep (se 1 (by rfl) ⟨1413512, by rfl⟩ : syracuseStep 1884683 = 2827025) B2827025
theorem B6360821 : Blo 1883435 6360821 := bbase (se 5 (by rfl) ⟨298163, by rfl⟩ : syracuseStep 6360821 = 596327) (by norm_num)
theorem B4240547 : Blo 1883435 4240547 := bstep (se 1 (by rfl) ⟨3180410, by rfl⟩ : syracuseStep 4240547 = 6360821) B6360821
theorem B2827031 : Blo 1883435 2827031 := bstep (se 1 (by rfl) ⟨2120273, by rfl⟩ : syracuseStep 2827031 = 4240547) B4240547
theorem B1884687 : Blo 1883435 1884687 := bstep (se 1 (by rfl) ⟨1413515, by rfl⟩ : syracuseStep 1884687 = 2827031) B2827031
theorem B2827037 : Blo 1883435 2827037 := bbase (se 3 (by rfl) ⟨530069, by rfl⟩ : syracuseStep 2827037 = 1060139) (by norm_num)
theorem B1884691 : Blo 1883435 1884691 := bstep (se 1 (by rfl) ⟨1413518, by rfl⟩ : syracuseStep 1884691 = 2827037) B2827037
theorem B4240565 : Blo 1883435 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B2827043 : Blo 1883435 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B1884695 : Blo 1883435 1884695 := bstep (se 1 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 1884695 = 2827043) B2827043
theorem B2012617 : Blo 1883435 2012617 := bbase (se 2 (by rfl) ⟨754731, by rfl⟩ : syracuseStep 2012617 = 1509463) (by norm_num)
theorem B10733957 : Blo 1883435 10733957 := bstep (se 4 (by rfl) ⟨1006308, by rfl⟩ : syracuseStep 10733957 = 2012617) B2012617
theorem B7155971 : Blo 1883435 7155971 := bstep (se 1 (by rfl) ⟨5366978, by rfl⟩ : syracuseStep 7155971 = 10733957) B10733957
theorem B4770647 : Blo 1883435 4770647 := bstep (se 1 (by rfl) ⟨3577985, by rfl⟩ : syracuseStep 4770647 = 7155971) B7155971
theorem B3180431 : Blo 1883435 3180431 := bstep (se 1 (by rfl) ⟨2385323, by rfl⟩ : syracuseStep 3180431 = 4770647) B4770647
theorem B2120287 : Blo 1883435 2120287 := bstep (se 1 (by rfl) ⟨1590215, by rfl⟩ : syracuseStep 2120287 = 3180431) B3180431
theorem B2827049 : Blo 1883435 2827049 := bstep (se 2 (by rfl) ⟨1060143, by rfl⟩ : syracuseStep 2827049 = 2120287) B2120287
theorem B1884699 : Blo 1883435 1884699 := bstep (se 1 (by rfl) ⟨1413524, by rfl⟩ : syracuseStep 1884699 = 2827049) B2827049
theorem B2012621 : Blo 1883435 2012621 := bbase (se 3 (by rfl) ⟨377366, by rfl⟩ : syracuseStep 2012621 = 754733) (by norm_num)
theorem B5366989 : Blo 1883435 5366989 := bstep (se 3 (by rfl) ⟨1006310, by rfl⟩ : syracuseStep 5366989 = 2012621) B2012621
theorem B7155985 : Blo 1883435 7155985 := bstep (se 2 (by rfl) ⟨2683494, by rfl⟩ : syracuseStep 7155985 = 5366989) B5366989
theorem B9541313 : Blo 1883435 9541313 := bstep (se 2 (by rfl) ⟨3577992, by rfl⟩ : syracuseStep 9541313 = 7155985) B7155985
theorem B6360875 : Blo 1883435 6360875 := bstep (se 1 (by rfl) ⟨4770656, by rfl⟩ : syracuseStep 6360875 = 9541313) B9541313
theorem B4240583 : Blo 1883435 4240583 := bstep (se 1 (by rfl) ⟨3180437, by rfl⟩ : syracuseStep 4240583 = 6360875) B6360875
theorem B2827055 : Blo 1883435 2827055 := bstep (se 1 (by rfl) ⟨2120291, by rfl⟩ : syracuseStep 2827055 = 4240583) B4240583
theorem B1884703 : Blo 1883435 1884703 := bstep (se 1 (by rfl) ⟨1413527, by rfl⟩ : syracuseStep 1884703 = 2827055) B2827055
theorem B2827061 : Blo 1883435 2827061 := bbase (se 5 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 2827061 = 265037) (by norm_num)
theorem B1884707 : Blo 1883435 1884707 := bstep (se 1 (by rfl) ⟨1413530, by rfl⟩ : syracuseStep 1884707 = 2827061) B2827061
theorem B4770677 : Blo 1883435 4770677 := bbase (se 5 (by rfl) ⟨223625, by rfl⟩ : syracuseStep 4770677 = 447251) (by norm_num)
theorem B3180451 : Blo 1883435 3180451 := bstep (se 1 (by rfl) ⟨2385338, by rfl⟩ : syracuseStep 3180451 = 4770677) B4770677
theorem B4240601 : Blo 1883435 4240601 := bstep (se 2 (by rfl) ⟨1590225, by rfl⟩ : syracuseStep 4240601 = 3180451) B3180451
theorem B2827067 : Blo 1883435 2827067 := bstep (se 1 (by rfl) ⟨2120300, by rfl⟩ : syracuseStep 2827067 = 4240601) B4240601
theorem B1884711 : Blo 1883435 1884711 := bstep (se 1 (by rfl) ⟨1413533, by rfl⟩ : syracuseStep 1884711 = 2827067) B2827067
theorem B2120305 : Blo 1883435 2120305 := bbase (se 2 (by rfl) ⟨795114, by rfl⟩ : syracuseStep 2120305 = 1590229) (by norm_num)
theorem B2827073 : Blo 1883435 2827073 := bstep (se 2 (by rfl) ⟨1060152, by rfl⟩ : syracuseStep 2827073 = 2120305) B2120305
theorem B1884715 : Blo 1883435 1884715 := bstep (se 1 (by rfl) ⟨1413536, by rfl⟩ : syracuseStep 1884715 = 2827073) B2827073
theorem B21761045 : Blo 1883435 21761045 := bbase (se 6 (by rfl) ⟨510024, by rfl⟩ : syracuseStep 21761045 = 1020049) (by norm_num)
theorem B14507363 : Blo 1883435 14507363 := bstep (se 1 (by rfl) ⟨10880522, by rfl⟩ : syracuseStep 14507363 = 21761045) B21761045
theorem B9671575 : Blo 1883435 9671575 := bstep (se 1 (by rfl) ⟨7253681, by rfl⟩ : syracuseStep 9671575 = 14507363) B14507363
theorem B12895433 : Blo 1883435 12895433 := bstep (se 2 (by rfl) ⟨4835787, by rfl⟩ : syracuseStep 12895433 = 9671575) B9671575
theorem B8596955 : Blo 1883435 8596955 := bstep (se 1 (by rfl) ⟨6447716, by rfl⟩ : syracuseStep 8596955 = 12895433) B12895433
theorem B22925213 : Blo 1883435 22925213 := bstep (se 3 (by rfl) ⟨4298477, by rfl⟩ : syracuseStep 22925213 = 8596955) B8596955
theorem B15283475 : Blo 1883435 15283475 := bstep (se 1 (by rfl) ⟨11462606, by rfl⟩ : syracuseStep 15283475 = 22925213) B22925213
theorem B10188983 : Blo 1883435 10188983 := bstep (se 1 (by rfl) ⟨7641737, by rfl⟩ : syracuseStep 10188983 = 15283475) B15283475
theorem B6792655 : Blo 1883435 6792655 := bstep (se 1 (by rfl) ⟨5094491, by rfl⟩ : syracuseStep 6792655 = 10188983) B10188983
theorem B9056873 : Blo 1883435 9056873 := bstep (se 2 (by rfl) ⟨3396327, by rfl⟩ : syracuseStep 9056873 = 6792655) B6792655
theorem B6037915 : Blo 1883435 6037915 := bstep (se 1 (by rfl) ⟨4528436, by rfl⟩ : syracuseStep 6037915 = 9056873) B9056873
theorem B8050553 : Blo 1883435 8050553 := bstep (se 2 (by rfl) ⟨3018957, by rfl⟩ : syracuseStep 8050553 = 6037915) B6037915
theorem B5367035 : Blo 1883435 5367035 := bstep (se 1 (by rfl) ⟨4025276, by rfl⟩ : syracuseStep 5367035 = 8050553) B8050553
theorem B3578023 : Blo 1883435 3578023 := bstep (se 1 (by rfl) ⟨2683517, by rfl⟩ : syracuseStep 3578023 = 5367035) B5367035
theorem B4770697 : Blo 1883435 4770697 := bstep (se 2 (by rfl) ⟨1789011, by rfl⟩ : syracuseStep 4770697 = 3578023) B3578023
theorem B6360929 : Blo 1883435 6360929 := bstep (se 2 (by rfl) ⟨2385348, by rfl⟩ : syracuseStep 6360929 = 4770697) B4770697
theorem B4240619 : Blo 1883435 4240619 := bstep (se 1 (by rfl) ⟨3180464, by rfl⟩ : syracuseStep 4240619 = 6360929) B6360929
theorem B2827079 : Blo 1883435 2827079 := bstep (se 1 (by rfl) ⟨2120309, by rfl⟩ : syracuseStep 2827079 = 4240619) B4240619
theorem B1884719 : Blo 1883435 1884719 := bstep (se 1 (by rfl) ⟨1413539, by rfl⟩ : syracuseStep 1884719 = 2827079) B2827079
theorem B2827085 : Blo 1883435 2827085 := bbase (se 3 (by rfl) ⟨530078, by rfl⟩ : syracuseStep 2827085 = 1060157) (by norm_num)
theorem B1884723 : Blo 1883435 1884723 := bstep (se 1 (by rfl) ⟨1413542, by rfl⟩ : syracuseStep 1884723 = 2827085) B2827085
theorem B4240637 : Blo 1883435 4240637 := bbase (se 3 (by rfl) ⟨795119, by rfl⟩ : syracuseStep 4240637 = 1590239) (by norm_num)
theorem B2827091 : Blo 1883435 2827091 := bstep (se 1 (by rfl) ⟨2120318, by rfl⟩ : syracuseStep 2827091 = 4240637) B4240637
theorem B1884727 : Blo 1883435 1884727 := bstep (se 1 (by rfl) ⟨1413545, by rfl⟩ : syracuseStep 1884727 = 2827091) B2827091
theorem B3180485 : Blo 1883435 3180485 := bbase (se 4 (by rfl) ⟨298170, by rfl⟩ : syracuseStep 3180485 = 596341) (by norm_num)
theorem B2120323 : Blo 1883435 2120323 := bstep (se 1 (by rfl) ⟨1590242, by rfl⟩ : syracuseStep 2120323 = 3180485) B3180485
theorem B2827097 : Blo 1883435 2827097 := bstep (se 2 (by rfl) ⟨1060161, by rfl⟩ : syracuseStep 2827097 = 2120323) B2120323
theorem B1884731 : Blo 1883435 1884731 := bstep (se 1 (by rfl) ⟨1413548, by rfl⟩ : syracuseStep 1884731 = 2827097) B2827097
theorem B14312213 : Blo 1883435 14312213 := bbase (se 6 (by rfl) ⟨335442, by rfl⟩ : syracuseStep 14312213 = 670885) (by norm_num)
theorem B9541475 : Blo 1883435 9541475 := bstep (se 1 (by rfl) ⟨7156106, by rfl⟩ : syracuseStep 9541475 = 14312213) B14312213
theorem B6360983 : Blo 1883435 6360983 := bstep (se 1 (by rfl) ⟨4770737, by rfl⟩ : syracuseStep 6360983 = 9541475) B9541475
theorem B4240655 : Blo 1883435 4240655 := bstep (se 1 (by rfl) ⟨3180491, by rfl⟩ : syracuseStep 4240655 = 6360983) B6360983
theorem B2827103 : Blo 1883435 2827103 := bstep (se 1 (by rfl) ⟨2120327, by rfl⟩ : syracuseStep 2827103 = 4240655) B4240655
theorem B1884735 : Blo 1883435 1884735 := bstep (se 1 (by rfl) ⟨1413551, by rfl⟩ : syracuseStep 1884735 = 2827103) B2827103
theorem B2827109 : Blo 1883435 2827109 := bbase (se 4 (by rfl) ⟨265041, by rfl⟩ : syracuseStep 2827109 = 530083) (by norm_num)
theorem B1884739 : Blo 1883435 1884739 := bstep (se 1 (by rfl) ⟨1413554, by rfl⟩ : syracuseStep 1884739 = 2827109) B2827109
theorem B3578069 : Blo 1883435 3578069 := bbase (se 7 (by rfl) ⟨41930, by rfl⟩ : syracuseStep 3578069 = 83861) (by norm_num)
theorem B2385379 : Blo 1883435 2385379 := bstep (se 1 (by rfl) ⟨1789034, by rfl⟩ : syracuseStep 2385379 = 3578069) B3578069
theorem B3180505 : Blo 1883435 3180505 := bstep (se 2 (by rfl) ⟨1192689, by rfl⟩ : syracuseStep 3180505 = 2385379) B2385379
theorem B4240673 : Blo 1883435 4240673 := bstep (se 2 (by rfl) ⟨1590252, by rfl⟩ : syracuseStep 4240673 = 3180505) B3180505
theorem B2827115 : Blo 1883435 2827115 := bstep (se 1 (by rfl) ⟨2120336, by rfl⟩ : syracuseStep 2827115 = 4240673) B4240673
theorem B1884743 : Blo 1883435 1884743 := bstep (se 1 (by rfl) ⟨1413557, by rfl⟩ : syracuseStep 1884743 = 2827115) B2827115
theorem B2120341 : Blo 1883435 2120341 := bbase (se 6 (by rfl) ⟨49695, by rfl⟩ : syracuseStep 2120341 = 99391) (by norm_num)
theorem B2827121 : Blo 1883435 2827121 := bstep (se 2 (by rfl) ⟨1060170, by rfl⟩ : syracuseStep 2827121 = 2120341) B2120341
theorem B1884747 : Blo 1883435 1884747 := bstep (se 1 (by rfl) ⟨1413560, by rfl⟩ : syracuseStep 1884747 = 2827121) B2827121
theorem B2385389 : Blo 1883435 2385389 := bbase (se 3 (by rfl) ⟨447260, by rfl⟩ : syracuseStep 2385389 = 894521) (by norm_num)
theorem B6361037 : Blo 1883435 6361037 := bstep (se 3 (by rfl) ⟨1192694, by rfl⟩ : syracuseStep 6361037 = 2385389) B2385389
theorem B4240691 : Blo 1883435 4240691 := bstep (se 1 (by rfl) ⟨3180518, by rfl⟩ : syracuseStep 4240691 = 6361037) B6361037
theorem B2827127 : Blo 1883435 2827127 := bstep (se 1 (by rfl) ⟨2120345, by rfl⟩ : syracuseStep 2827127 = 4240691) B4240691
theorem B1884751 : Blo 1883435 1884751 := bstep (se 1 (by rfl) ⟨1413563, by rfl⟩ : syracuseStep 1884751 = 2827127) B2827127
theorem B2827133 : Blo 1883435 2827133 := bbase (se 3 (by rfl) ⟨530087, by rfl⟩ : syracuseStep 2827133 = 1060175) (by norm_num)
theorem B1884755 : Blo 1883435 1884755 := bstep (se 1 (by rfl) ⟨1413566, by rfl⟩ : syracuseStep 1884755 = 2827133) B2827133
theorem B4240709 : Blo 1883435 4240709 := bbase (se 4 (by rfl) ⟨397566, by rfl⟩ : syracuseStep 4240709 = 795133) (by norm_num)
theorem B2827139 : Blo 1883435 2827139 := bstep (se 1 (by rfl) ⟨2120354, by rfl⟩ : syracuseStep 2827139 = 4240709) B4240709
theorem B1884759 : Blo 1883435 1884759 := bstep (se 1 (by rfl) ⟨1413569, by rfl⟩ : syracuseStep 1884759 = 2827139) B2827139
theorem B19343605 : Blo 1883435 19343605 := bbase (se 5 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 19343605 = 1813463) (by norm_num)
theorem B25791473 : Blo 1883435 25791473 := bstep (se 2 (by rfl) ⟨9671802, by rfl⟩ : syracuseStep 25791473 = 19343605) B19343605
theorem B17194315 : Blo 1883435 17194315 := bstep (se 1 (by rfl) ⟨12895736, by rfl⟩ : syracuseStep 17194315 = 25791473) B25791473
theorem B22925753 : Blo 1883435 22925753 := bstep (se 2 (by rfl) ⟨8597157, by rfl⟩ : syracuseStep 22925753 = 17194315) B17194315
theorem B15283835 : Blo 1883435 15283835 := bstep (se 1 (by rfl) ⟨11462876, by rfl⟩ : syracuseStep 15283835 = 22925753) B22925753
theorem B10189223 : Blo 1883435 10189223 := bstep (se 1 (by rfl) ⟨7641917, by rfl⟩ : syracuseStep 10189223 = 15283835) B15283835
theorem B6792815 : Blo 1883435 6792815 := bstep (se 1 (by rfl) ⟨5094611, by rfl⟩ : syracuseStep 6792815 = 10189223) B10189223
theorem B4528543 : Blo 1883435 4528543 := bstep (se 1 (by rfl) ⟨3396407, by rfl⟩ : syracuseStep 4528543 = 6792815) B6792815
theorem B6038057 : Blo 1883435 6038057 := bstep (se 2 (by rfl) ⟨2264271, by rfl⟩ : syracuseStep 6038057 = 4528543) B4528543
theorem B4025371 : Blo 1883435 4025371 := bstep (se 1 (by rfl) ⟨3019028, by rfl⟩ : syracuseStep 4025371 = 6038057) B6038057
theorem B5367161 : Blo 1883435 5367161 := bstep (se 2 (by rfl) ⟨2012685, by rfl⟩ : syracuseStep 5367161 = 4025371) B4025371
theorem B3578107 : Blo 1883435 3578107 := bstep (se 1 (by rfl) ⟨2683580, by rfl⟩ : syracuseStep 3578107 = 5367161) B5367161
theorem B4770809 : Blo 1883435 4770809 := bstep (se 2 (by rfl) ⟨1789053, by rfl⟩ : syracuseStep 4770809 = 3578107) B3578107
theorem B3180539 : Blo 1883435 3180539 := bstep (se 1 (by rfl) ⟨2385404, by rfl⟩ : syracuseStep 3180539 = 4770809) B4770809
theorem B2120359 : Blo 1883435 2120359 := bstep (se 1 (by rfl) ⟨1590269, by rfl⟩ : syracuseStep 2120359 = 3180539) B3180539
theorem B2827145 : Blo 1883435 2827145 := bstep (se 2 (by rfl) ⟨1060179, by rfl⟩ : syracuseStep 2827145 = 2120359) B2120359
theorem B1884763 : Blo 1883435 1884763 := bstep (se 1 (by rfl) ⟨1413572, by rfl⟩ : syracuseStep 1884763 = 2827145) B2827145
theorem B9541637 : Blo 1883435 9541637 := bbase (se 4 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 9541637 = 1789057) (by norm_num)
theorem B6361091 : Blo 1883435 6361091 := bstep (se 1 (by rfl) ⟨4770818, by rfl⟩ : syracuseStep 6361091 = 9541637) B9541637
theorem B4240727 : Blo 1883435 4240727 := bstep (se 1 (by rfl) ⟨3180545, by rfl⟩ : syracuseStep 4240727 = 6361091) B6361091
theorem B2827151 : Blo 1883435 2827151 := bstep (se 1 (by rfl) ⟨2120363, by rfl⟩ : syracuseStep 2827151 = 4240727) B4240727
theorem B1884767 : Blo 1883435 1884767 := bstep (se 1 (by rfl) ⟨1413575, by rfl⟩ : syracuseStep 1884767 = 2827151) B2827151
theorem B2827157 : Blo 1883435 2827157 := bbase (se 6 (by rfl) ⟨66261, by rfl⟩ : syracuseStep 2827157 = 132523) (by norm_num)
theorem B1884771 : Blo 1883435 1884771 := bstep (se 1 (by rfl) ⟨1413578, by rfl⟩ : syracuseStep 1884771 = 2827157) B2827157
theorem B10734389 : Blo 1883435 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B7156259 : Blo 1883435 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B4770839 : Blo 1883435 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B3180559 : Blo 1883435 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B4240745 : Blo 1883435 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B2827163 : Blo 1883435 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B1884775 : Blo 1883435 1884775 := bstep (se 1 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 1884775 = 2827163) B2827163
theorem B2120377 : Blo 1883435 2120377 := bbase (se 2 (by rfl) ⟨795141, by rfl⟩ : syracuseStep 2120377 = 1590283) (by norm_num)
theorem B2827169 : Blo 1883435 2827169 := bstep (se 2 (by rfl) ⟨1060188, by rfl⟩ : syracuseStep 2827169 = 2120377) B2120377
theorem B1884779 : Blo 1883435 1884779 := bstep (se 1 (by rfl) ⟨1413584, by rfl⟩ : syracuseStep 1884779 = 2827169) B2827169
theorem B4025413 : Blo 1883435 4025413 := bbase (se 4 (by rfl) ⟨377382, by rfl⟩ : syracuseStep 4025413 = 754765) (by norm_num)
theorem B5367217 : Blo 1883435 5367217 := bstep (se 2 (by rfl) ⟨2012706, by rfl⟩ : syracuseStep 5367217 = 4025413) B4025413
theorem B7156289 : Blo 1883435 7156289 := bstep (se 2 (by rfl) ⟨2683608, by rfl⟩ : syracuseStep 7156289 = 5367217) B5367217
theorem B4770859 : Blo 1883435 4770859 := bstep (se 1 (by rfl) ⟨3578144, by rfl⟩ : syracuseStep 4770859 = 7156289) B7156289
theorem B6361145 : Blo 1883435 6361145 := bstep (se 2 (by rfl) ⟨2385429, by rfl⟩ : syracuseStep 6361145 = 4770859) B4770859
theorem B4240763 : Blo 1883435 4240763 := bstep (se 1 (by rfl) ⟨3180572, by rfl⟩ : syracuseStep 4240763 = 6361145) B6361145
theorem B2827175 : Blo 1883435 2827175 := bstep (se 1 (by rfl) ⟨2120381, by rfl⟩ : syracuseStep 2827175 = 4240763) B4240763
theorem B1884783 : Blo 1883435 1884783 := bstep (se 1 (by rfl) ⟨1413587, by rfl⟩ : syracuseStep 1884783 = 2827175) B2827175
theorem B2827181 : Blo 1883435 2827181 := bbase (se 3 (by rfl) ⟨530096, by rfl⟩ : syracuseStep 2827181 = 1060193) (by norm_num)
theorem B1884787 : Blo 1883435 1884787 := bstep (se 1 (by rfl) ⟨1413590, by rfl⟩ : syracuseStep 1884787 = 2827181) B2827181
theorem B4240781 : Blo 1883435 4240781 := bbase (se 3 (by rfl) ⟨795146, by rfl⟩ : syracuseStep 4240781 = 1590293) (by norm_num)
theorem B2827187 : Blo 1883435 2827187 := bstep (se 1 (by rfl) ⟨2120390, by rfl⟩ : syracuseStep 2827187 = 4240781) B4240781
theorem B1884791 : Blo 1883435 1884791 := bstep (se 1 (by rfl) ⟨1413593, by rfl⟩ : syracuseStep 1884791 = 2827187) B2827187
theorem B2385445 : Blo 1883435 2385445 := bbase (se 4 (by rfl) ⟨223635, by rfl⟩ : syracuseStep 2385445 = 447271) (by norm_num)
theorem B3180593 : Blo 1883435 3180593 := bstep (se 2 (by rfl) ⟨1192722, by rfl⟩ : syracuseStep 3180593 = 2385445) B2385445
theorem B2120395 : Blo 1883435 2120395 := bstep (se 1 (by rfl) ⟨1590296, by rfl⟩ : syracuseStep 2120395 = 3180593) B3180593
theorem B2827193 : Blo 1883435 2827193 := bstep (se 2 (by rfl) ⟨1060197, by rfl⟩ : syracuseStep 2827193 = 2120395) B2120395
theorem B1884795 : Blo 1883435 1884795 := bstep (se 1 (by rfl) ⟨1413596, by rfl⟩ : syracuseStep 1884795 = 2827193) B2827193
theorem B34389269 : Blo 1883435 34389269 := bbase (se 6 (by rfl) ⟨805998, by rfl⟩ : syracuseStep 34389269 = 1611997) (by norm_num)
theorem B22926179 : Blo 1883435 22926179 := bstep (se 1 (by rfl) ⟨17194634, by rfl⟩ : syracuseStep 22926179 = 34389269) B34389269
theorem B61136477 : Blo 1883435 61136477 := bstep (se 3 (by rfl) ⟨11463089, by rfl⟩ : syracuseStep 61136477 = 22926179) B22926179
theorem B40757651 : Blo 1883435 40757651 := bstep (se 1 (by rfl) ⟨30568238, by rfl⟩ : syracuseStep 40757651 = 61136477) B61136477
theorem B27171767 : Blo 1883435 27171767 := bstep (se 1 (by rfl) ⟨20378825, by rfl⟩ : syracuseStep 27171767 = 40757651) B40757651
theorem B18114511 : Blo 1883435 18114511 := bstep (se 1 (by rfl) ⟨13585883, by rfl⟩ : syracuseStep 18114511 = 27171767) B27171767
theorem B24152681 : Blo 1883435 24152681 := bstep (se 2 (by rfl) ⟨9057255, by rfl⟩ : syracuseStep 24152681 = 18114511) B18114511
theorem B16101787 : Blo 1883435 16101787 := bstep (se 1 (by rfl) ⟨12076340, by rfl⟩ : syracuseStep 16101787 = 24152681) B24152681
theorem B21469049 : Blo 1883435 21469049 := bstep (se 2 (by rfl) ⟨8050893, by rfl⟩ : syracuseStep 21469049 = 16101787) B16101787
theorem B14312699 : Blo 1883435 14312699 := bstep (se 1 (by rfl) ⟨10734524, by rfl⟩ : syracuseStep 14312699 = 21469049) B21469049
theorem B9541799 : Blo 1883435 9541799 := bstep (se 1 (by rfl) ⟨7156349, by rfl⟩ : syracuseStep 9541799 = 14312699) B14312699
theorem B6361199 : Blo 1883435 6361199 := bstep (se 1 (by rfl) ⟨4770899, by rfl⟩ : syracuseStep 6361199 = 9541799) B9541799
theorem B4240799 : Blo 1883435 4240799 := bstep (se 1 (by rfl) ⟨3180599, by rfl⟩ : syracuseStep 4240799 = 6361199) B6361199
theorem B2827199 : Blo 1883435 2827199 := bstep (se 1 (by rfl) ⟨2120399, by rfl⟩ : syracuseStep 2827199 = 4240799) B4240799
theorem B1884799 : Blo 1883435 1884799 := bstep (se 1 (by rfl) ⟨1413599, by rfl⟩ : syracuseStep 1884799 = 2827199) B2827199
theorem B2827205 : Blo 1883435 2827205 := bbase (se 4 (by rfl) ⟨265050, by rfl⟩ : syracuseStep 2827205 = 530101) (by norm_num)
theorem B1884803 : Blo 1883435 1884803 := bstep (se 1 (by rfl) ⟨1413602, by rfl⟩ : syracuseStep 1884803 = 2827205) B2827205
theorem B3180613 : Blo 1883435 3180613 := bbase (se 4 (by rfl) ⟨298182, by rfl⟩ : syracuseStep 3180613 = 596365) (by norm_num)
theorem B4240817 : Blo 1883435 4240817 := bstep (se 2 (by rfl) ⟨1590306, by rfl⟩ : syracuseStep 4240817 = 3180613) B3180613
theorem B2827211 : Blo 1883435 2827211 := bstep (se 1 (by rfl) ⟨2120408, by rfl⟩ : syracuseStep 2827211 = 4240817) B4240817
theorem B1884807 : Blo 1883435 1884807 := bstep (se 1 (by rfl) ⟨1413605, by rfl⟩ : syracuseStep 1884807 = 2827211) B2827211
theorem B2120413 : Blo 1883435 2120413 := bbase (se 3 (by rfl) ⟨397577, by rfl⟩ : syracuseStep 2120413 = 795155) (by norm_num)
theorem B2827217 : Blo 1883435 2827217 := bstep (se 2 (by rfl) ⟨1060206, by rfl⟩ : syracuseStep 2827217 = 2120413) B2120413
theorem B1884811 : Blo 1883435 1884811 := bstep (se 1 (by rfl) ⟨1413608, by rfl⟩ : syracuseStep 1884811 = 2827217) B2827217
theorem B6361253 : Blo 1883435 6361253 := bbase (se 4 (by rfl) ⟨596367, by rfl⟩ : syracuseStep 6361253 = 1192735) (by norm_num)
theorem B4240835 : Blo 1883435 4240835 := bstep (se 1 (by rfl) ⟨3180626, by rfl⟩ : syracuseStep 4240835 = 6361253) B6361253
theorem B2827223 : Blo 1883435 2827223 := bstep (se 1 (by rfl) ⟨2120417, by rfl⟩ : syracuseStep 2827223 = 4240835) B4240835
theorem B1884815 : Blo 1883435 1884815 := bstep (se 1 (by rfl) ⟨1413611, by rfl⟩ : syracuseStep 1884815 = 2827223) B2827223
theorem B2827229 : Blo 1883435 2827229 := bbase (se 3 (by rfl) ⟨530105, by rfl⟩ : syracuseStep 2827229 = 1060211) (by norm_num)
theorem B1884819 : Blo 1883435 1884819 := bstep (se 1 (by rfl) ⟨1413614, by rfl⟩ : syracuseStep 1884819 = 2827229) B2827229
theorem B4240853 : Blo 1883435 4240853 := bbase (se 7 (by rfl) ⟨49697, by rfl⟩ : syracuseStep 4240853 = 99395) (by norm_num)
theorem B2827235 : Blo 1883435 2827235 := bstep (se 1 (by rfl) ⟨2120426, by rfl⟩ : syracuseStep 2827235 = 4240853) B4240853
theorem B1884823 : Blo 1883435 1884823 := bstep (se 1 (by rfl) ⟨1413617, by rfl⟩ : syracuseStep 1884823 = 2827235) B2827235
theorem B4357373 : Blo 1883435 4357373 := bbase (se 3 (by rfl) ⟨817007, by rfl⟩ : syracuseStep 4357373 = 1634015) (by norm_num)
theorem B11619661 : Blo 1883435 11619661 := bstep (se 3 (by rfl) ⟨2178686, by rfl⟩ : syracuseStep 11619661 = 4357373) B4357373
theorem B15492881 : Blo 1883435 15492881 := bstep (se 2 (by rfl) ⟨5809830, by rfl⟩ : syracuseStep 15492881 = 11619661) B11619661
theorem B41314349 : Blo 1883435 41314349 := bstep (se 3 (by rfl) ⟨7746440, by rfl⟩ : syracuseStep 41314349 = 15492881) B15492881
theorem B27542899 : Blo 1883435 27542899 := bstep (se 1 (by rfl) ⟨20657174, by rfl⟩ : syracuseStep 27542899 = 41314349) B41314349
theorem B36723865 : Blo 1883435 36723865 := bstep (se 2 (by rfl) ⟨13771449, by rfl⟩ : syracuseStep 36723865 = 27542899) B27542899
theorem B48965153 : Blo 1883435 48965153 := bstep (se 2 (by rfl) ⟨18361932, by rfl⟩ : syracuseStep 48965153 = 36723865) B36723865
theorem B130573741 : Blo 1883435 130573741 := bstep (se 3 (by rfl) ⟨24482576, by rfl⟩ : syracuseStep 130573741 = 48965153) B48965153
theorem B174098321 : Blo 1883435 174098321 := bstep (se 2 (by rfl) ⟨65286870, by rfl⟩ : syracuseStep 174098321 = 130573741) B130573741
theorem B116065547 : Blo 1883435 116065547 := bstep (se 1 (by rfl) ⟨87049160, by rfl⟩ : syracuseStep 116065547 = 174098321) B174098321
theorem B77377031 : Blo 1883435 77377031 := bstep (se 1 (by rfl) ⟨58032773, by rfl⟩ : syracuseStep 77377031 = 116065547) B116065547
theorem B51584687 : Blo 1883435 51584687 := bstep (se 1 (by rfl) ⟨38688515, by rfl⟩ : syracuseStep 51584687 = 77377031) B77377031
theorem B34389791 : Blo 1883435 34389791 := bstep (se 1 (by rfl) ⟨25792343, by rfl⟩ : syracuseStep 34389791 = 51584687) B51584687
theorem B22926527 : Blo 1883435 22926527 := bstep (se 1 (by rfl) ⟨17194895, by rfl⟩ : syracuseStep 22926527 = 34389791) B34389791
theorem B15284351 : Blo 1883435 15284351 := bstep (se 1 (by rfl) ⟨11463263, by rfl⟩ : syracuseStep 15284351 = 22926527) B22926527
theorem B10189567 : Blo 1883435 10189567 := bstep (se 1 (by rfl) ⟨7642175, by rfl⟩ : syracuseStep 10189567 = 15284351) B15284351
theorem B13586089 : Blo 1883435 13586089 := bstep (se 2 (by rfl) ⟨5094783, by rfl⟩ : syracuseStep 13586089 = 10189567) B10189567
theorem B18114785 : Blo 1883435 18114785 := bstep (se 2 (by rfl) ⟨6793044, by rfl⟩ : syracuseStep 18114785 = 13586089) B13586089
theorem B12076523 : Blo 1883435 12076523 := bstep (se 1 (by rfl) ⟨9057392, by rfl⟩ : syracuseStep 12076523 = 18114785) B18114785
theorem B8051015 : Blo 1883435 8051015 := bstep (se 1 (by rfl) ⟨6038261, by rfl⟩ : syracuseStep 8051015 = 12076523) B12076523
theorem B5367343 : Blo 1883435 5367343 := bstep (se 1 (by rfl) ⟨4025507, by rfl⟩ : syracuseStep 5367343 = 8051015) B8051015
theorem B7156457 : Blo 1883435 7156457 := bstep (se 2 (by rfl) ⟨2683671, by rfl⟩ : syracuseStep 7156457 = 5367343) B5367343
theorem B4770971 : Blo 1883435 4770971 := bstep (se 1 (by rfl) ⟨3578228, by rfl⟩ : syracuseStep 4770971 = 7156457) B7156457
theorem B3180647 : Blo 1883435 3180647 := bstep (se 1 (by rfl) ⟨2385485, by rfl⟩ : syracuseStep 3180647 = 4770971) B4770971
theorem B2120431 : Blo 1883435 2120431 := bstep (se 1 (by rfl) ⟨1590323, by rfl⟩ : syracuseStep 2120431 = 3180647) B3180647
theorem B2827241 : Blo 1883435 2827241 := bstep (se 2 (by rfl) ⟨1060215, by rfl⟩ : syracuseStep 2827241 = 2120431) B2120431
theorem B1884827 : Blo 1883435 1884827 := bstep (se 1 (by rfl) ⟨1413620, by rfl⟩ : syracuseStep 1884827 = 2827241) B2827241
theorem B2547397 : Blo 1883435 2547397 := bbase (se 4 (by rfl) ⟨238818, by rfl⟩ : syracuseStep 2547397 = 477637) (by norm_num)
theorem B3396529 : Blo 1883435 3396529 := bstep (se 2 (by rfl) ⟨1273698, by rfl⟩ : syracuseStep 3396529 = 2547397) B2547397
theorem B4528705 : Blo 1883435 4528705 := bstep (se 2 (by rfl) ⟨1698264, by rfl⟩ : syracuseStep 4528705 = 3396529) B3396529
theorem B6038273 : Blo 1883435 6038273 := bstep (se 2 (by rfl) ⟨2264352, by rfl⟩ : syracuseStep 6038273 = 4528705) B4528705
theorem B16102061 : Blo 1883435 16102061 := bstep (se 3 (by rfl) ⟨3019136, by rfl⟩ : syracuseStep 16102061 = 6038273) B6038273
theorem B10734707 : Blo 1883435 10734707 := bstep (se 1 (by rfl) ⟨8051030, by rfl⟩ : syracuseStep 10734707 = 16102061) B16102061
theorem B7156471 : Blo 1883435 7156471 := bstep (se 1 (by rfl) ⟨5367353, by rfl⟩ : syracuseStep 7156471 = 10734707) B10734707
theorem B9541961 : Blo 1883435 9541961 := bstep (se 2 (by rfl) ⟨3578235, by rfl⟩ : syracuseStep 9541961 = 7156471) B7156471
theorem B6361307 : Blo 1883435 6361307 := bstep (se 1 (by rfl) ⟨4770980, by rfl⟩ : syracuseStep 6361307 = 9541961) B9541961
theorem B4240871 : Blo 1883435 4240871 := bstep (se 1 (by rfl) ⟨3180653, by rfl⟩ : syracuseStep 4240871 = 6361307) B6361307
theorem B2827247 : Blo 1883435 2827247 := bstep (se 1 (by rfl) ⟨2120435, by rfl⟩ : syracuseStep 2827247 = 4240871) B4240871
theorem B1884831 : Blo 1883435 1884831 := bstep (se 1 (by rfl) ⟨1413623, by rfl⟩ : syracuseStep 1884831 = 2827247) B2827247
theorem B2827253 : Blo 1883435 2827253 := bbase (se 5 (by rfl) ⟨132527, by rfl⟩ : syracuseStep 2827253 = 265055) (by norm_num)
theorem B1884835 : Blo 1883435 1884835 := bstep (se 1 (by rfl) ⟨1413626, by rfl⟩ : syracuseStep 1884835 = 2827253) B2827253
theorem B4025533 : Blo 1883435 4025533 := bbase (se 3 (by rfl) ⟨754787, by rfl⟩ : syracuseStep 4025533 = 1509575) (by norm_num)
theorem B5367377 : Blo 1883435 5367377 := bstep (se 2 (by rfl) ⟨2012766, by rfl⟩ : syracuseStep 5367377 = 4025533) B4025533
theorem B3578251 : Blo 1883435 3578251 := bstep (se 1 (by rfl) ⟨2683688, by rfl⟩ : syracuseStep 3578251 = 5367377) B5367377
theorem B4771001 : Blo 1883435 4771001 := bstep (se 2 (by rfl) ⟨1789125, by rfl⟩ : syracuseStep 4771001 = 3578251) B3578251
theorem B3180667 : Blo 1883435 3180667 := bstep (se 1 (by rfl) ⟨2385500, by rfl⟩ : syracuseStep 3180667 = 4771001) B4771001
theorem B4240889 : Blo 1883435 4240889 := bstep (se 2 (by rfl) ⟨1590333, by rfl⟩ : syracuseStep 4240889 = 3180667) B3180667
theorem B2827259 : Blo 1883435 2827259 := bstep (se 1 (by rfl) ⟨2120444, by rfl⟩ : syracuseStep 2827259 = 4240889) B4240889
theorem B1884839 : Blo 1883435 1884839 := bstep (se 1 (by rfl) ⟨1413629, by rfl⟩ : syracuseStep 1884839 = 2827259) B2827259
theorem B2120449 : Blo 1883435 2120449 := bbase (se 2 (by rfl) ⟨795168, by rfl⟩ : syracuseStep 2120449 = 1590337) (by norm_num)
theorem B2827265 : Blo 1883435 2827265 := bstep (se 2 (by rfl) ⟨1060224, by rfl⟩ : syracuseStep 2827265 = 2120449) B2120449
theorem B1884843 : Blo 1883435 1884843 := bstep (se 1 (by rfl) ⟨1413632, by rfl⟩ : syracuseStep 1884843 = 2827265) B2827265
theorem B4771021 : Blo 1883435 4771021 := bbase (se 3 (by rfl) ⟨894566, by rfl⟩ : syracuseStep 4771021 = 1789133) (by norm_num)
theorem B6361361 : Blo 1883435 6361361 := bstep (se 2 (by rfl) ⟨2385510, by rfl⟩ : syracuseStep 6361361 = 4771021) B4771021
theorem B4240907 : Blo 1883435 4240907 := bstep (se 1 (by rfl) ⟨3180680, by rfl⟩ : syracuseStep 4240907 = 6361361) B6361361
theorem B2827271 : Blo 1883435 2827271 := bstep (se 1 (by rfl) ⟨2120453, by rfl⟩ : syracuseStep 2827271 = 4240907) B4240907
theorem B1884847 : Blo 1883435 1884847 := bstep (se 1 (by rfl) ⟨1413635, by rfl⟩ : syracuseStep 1884847 = 2827271) B2827271
theorem B2827277 : Blo 1883435 2827277 := bbase (se 3 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 2827277 = 1060229) (by norm_num)
theorem B1884851 : Blo 1883435 1884851 := bstep (se 1 (by rfl) ⟨1413638, by rfl⟩ : syracuseStep 1884851 = 2827277) B2827277
theorem B4240925 : Blo 1883435 4240925 := bbase (se 3 (by rfl) ⟨795173, by rfl⟩ : syracuseStep 4240925 = 1590347) (by norm_num)
theorem B2827283 : Blo 1883435 2827283 := bstep (se 1 (by rfl) ⟨2120462, by rfl⟩ : syracuseStep 2827283 = 4240925) B4240925
theorem B1884855 : Blo 1883435 1884855 := bstep (se 1 (by rfl) ⟨1413641, by rfl⟩ : syracuseStep 1884855 = 2827283) B2827283
theorem B3180701 : Blo 1883435 3180701 := bbase (se 3 (by rfl) ⟨596381, by rfl⟩ : syracuseStep 3180701 = 1192763) (by norm_num)
theorem B2120467 : Blo 1883435 2120467 := bstep (se 1 (by rfl) ⟨1590350, by rfl⟩ : syracuseStep 2120467 = 3180701) B3180701
theorem B2827289 : Blo 1883435 2827289 := bstep (se 2 (by rfl) ⟨1060233, by rfl⟩ : syracuseStep 2827289 = 2120467) B2120467
theorem B1884859 : Blo 1883435 1884859 := bstep (se 1 (by rfl) ⟨1413644, by rfl⟩ : syracuseStep 1884859 = 2827289) B2827289
theorem B7852277 : Blo 1883435 7852277 := bbase (se 5 (by rfl) ⟨368075, by rfl⟩ : syracuseStep 7852277 = 736151) (by norm_num)
theorem B5234851 : Blo 1883435 5234851 := bstep (se 1 (by rfl) ⟨3926138, by rfl⟩ : syracuseStep 5234851 = 7852277) B7852277
theorem B27919205 : Blo 1883435 27919205 := bstep (se 4 (by rfl) ⟨2617425, by rfl⟩ : syracuseStep 27919205 = 5234851) B5234851
theorem B18612803 : Blo 1883435 18612803 := bstep (se 1 (by rfl) ⟨13959602, by rfl⟩ : syracuseStep 18612803 = 27919205) B27919205
theorem B12408535 : Blo 1883435 12408535 := bstep (se 1 (by rfl) ⟨9306401, by rfl⟩ : syracuseStep 12408535 = 18612803) B18612803
theorem B66178853 : Blo 1883435 66178853 := bstep (se 4 (by rfl) ⟨6204267, by rfl⟩ : syracuseStep 66178853 = 12408535) B12408535
theorem B44119235 : Blo 1883435 44119235 := bstep (se 1 (by rfl) ⟨33089426, by rfl⟩ : syracuseStep 44119235 = 66178853) B66178853
theorem B29412823 : Blo 1883435 29412823 := bstep (se 1 (by rfl) ⟨22059617, by rfl⟩ : syracuseStep 29412823 = 44119235) B44119235
theorem B39217097 : Blo 1883435 39217097 := bstep (se 2 (by rfl) ⟨14706411, by rfl⟩ : syracuseStep 39217097 = 29412823) B29412823
theorem B26144731 : Blo 1883435 26144731 := bstep (se 1 (by rfl) ⟨19608548, by rfl⟩ : syracuseStep 26144731 = 39217097) B39217097
theorem B34859641 : Blo 1883435 34859641 := bstep (se 2 (by rfl) ⟨13072365, by rfl⟩ : syracuseStep 34859641 = 26144731) B26144731
theorem B46479521 : Blo 1883435 46479521 := bstep (se 2 (by rfl) ⟨17429820, by rfl⟩ : syracuseStep 46479521 = 34859641) B34859641
theorem B30986347 : Blo 1883435 30986347 := bstep (se 1 (by rfl) ⟨23239760, by rfl⟩ : syracuseStep 30986347 = 46479521) B46479521
theorem B41315129 : Blo 1883435 41315129 := bstep (se 2 (by rfl) ⟨15493173, by rfl⟩ : syracuseStep 41315129 = 30986347) B30986347
theorem B27543419 : Blo 1883435 27543419 := bstep (se 1 (by rfl) ⟨20657564, by rfl⟩ : syracuseStep 27543419 = 41315129) B41315129
theorem B18362279 : Blo 1883435 18362279 := bstep (se 1 (by rfl) ⟨13771709, by rfl⟩ : syracuseStep 18362279 = 27543419) B27543419
theorem B12241519 : Blo 1883435 12241519 := bstep (se 1 (by rfl) ⟨9181139, by rfl⟩ : syracuseStep 12241519 = 18362279) B18362279
theorem B65288101 : Blo 1883435 65288101 := bstep (se 4 (by rfl) ⟨6120759, by rfl⟩ : syracuseStep 65288101 = 12241519) B12241519
theorem B87050801 : Blo 1883435 87050801 := bstep (se 2 (by rfl) ⟨32644050, by rfl⟩ : syracuseStep 87050801 = 65288101) B65288101
theorem B58033867 : Blo 1883435 58033867 := bstep (se 1 (by rfl) ⟨43525400, by rfl⟩ : syracuseStep 58033867 = 87050801) B87050801
theorem B77378489 : Blo 1883435 77378489 := bstep (se 2 (by rfl) ⟨29016933, by rfl⟩ : syracuseStep 77378489 = 58033867) B58033867
theorem B51585659 : Blo 1883435 51585659 := bstep (se 1 (by rfl) ⟨38689244, by rfl⟩ : syracuseStep 51585659 = 77378489) B77378489
theorem B34390439 : Blo 1883435 34390439 := bstep (se 1 (by rfl) ⟨25792829, by rfl⟩ : syracuseStep 34390439 = 51585659) B51585659
theorem B22926959 : Blo 1883435 22926959 := bstep (se 1 (by rfl) ⟨17195219, by rfl⟩ : syracuseStep 22926959 = 34390439) B34390439
theorem B15284639 : Blo 1883435 15284639 := bstep (se 1 (by rfl) ⟨11463479, by rfl⟩ : syracuseStep 15284639 = 22926959) B22926959
theorem B40759037 : Blo 1883435 40759037 := bstep (se 3 (by rfl) ⟨7642319, by rfl⟩ : syracuseStep 40759037 = 15284639) B15284639
theorem B27172691 : Blo 1883435 27172691 := bstep (se 1 (by rfl) ⟨20379518, by rfl⟩ : syracuseStep 27172691 = 40759037) B40759037
theorem B18115127 : Blo 1883435 18115127 := bstep (se 1 (by rfl) ⟨13586345, by rfl⟩ : syracuseStep 18115127 = 27172691) B27172691
theorem B12076751 : Blo 1883435 12076751 := bstep (se 1 (by rfl) ⟨9057563, by rfl⟩ : syracuseStep 12076751 = 18115127) B18115127
theorem B8051167 : Blo 1883435 8051167 := bstep (se 1 (by rfl) ⟨6038375, by rfl⟩ : syracuseStep 8051167 = 12076751) B12076751
theorem B10734889 : Blo 1883435 10734889 := bstep (se 2 (by rfl) ⟨4025583, by rfl⟩ : syracuseStep 10734889 = 8051167) B8051167
theorem B14313185 : Blo 1883435 14313185 := bstep (se 2 (by rfl) ⟨5367444, by rfl⟩ : syracuseStep 14313185 = 10734889) B10734889
theorem B9542123 : Blo 1883435 9542123 := bstep (se 1 (by rfl) ⟨7156592, by rfl⟩ : syracuseStep 9542123 = 14313185) B14313185
theorem B6361415 : Blo 1883435 6361415 := bstep (se 1 (by rfl) ⟨4771061, by rfl⟩ : syracuseStep 6361415 = 9542123) B9542123
theorem B4240943 : Blo 1883435 4240943 := bstep (se 1 (by rfl) ⟨3180707, by rfl⟩ : syracuseStep 4240943 = 6361415) B6361415
theorem B2827295 : Blo 1883435 2827295 := bstep (se 1 (by rfl) ⟨2120471, by rfl⟩ : syracuseStep 2827295 = 4240943) B4240943
theorem B1884863 : Blo 1883435 1884863 := bstep (se 1 (by rfl) ⟨1413647, by rfl⟩ : syracuseStep 1884863 = 2827295) B2827295
theorem B2827301 : Blo 1883435 2827301 := bbase (se 4 (by rfl) ⟨265059, by rfl⟩ : syracuseStep 2827301 = 530119) (by norm_num)
theorem B1884867 : Blo 1883435 1884867 := bstep (se 1 (by rfl) ⟨1413650, by rfl⟩ : syracuseStep 1884867 = 2827301) B2827301
theorem B2385541 : Blo 1883435 2385541 := bbase (se 4 (by rfl) ⟨223644, by rfl⟩ : syracuseStep 2385541 = 447289) (by norm_num)
theorem B3180721 : Blo 1883435 3180721 := bstep (se 2 (by rfl) ⟨1192770, by rfl⟩ : syracuseStep 3180721 = 2385541) B2385541
theorem B4240961 : Blo 1883435 4240961 := bstep (se 2 (by rfl) ⟨1590360, by rfl⟩ : syracuseStep 4240961 = 3180721) B3180721
theorem B2827307 : Blo 1883435 2827307 := bstep (se 1 (by rfl) ⟨2120480, by rfl⟩ : syracuseStep 2827307 = 4240961) B4240961
theorem B1884871 : Blo 1883435 1884871 := bstep (se 1 (by rfl) ⟨1413653, by rfl⟩ : syracuseStep 1884871 = 2827307) B2827307
theorem B2120485 : Blo 1883435 2120485 := bbase (se 4 (by rfl) ⟨198795, by rfl⟩ : syracuseStep 2120485 = 397591) (by norm_num)
theorem B2827313 : Blo 1883435 2827313 := bstep (se 2 (by rfl) ⟨1060242, by rfl⟩ : syracuseStep 2827313 = 2120485) B2120485
theorem B1884875 : Blo 1883435 1884875 := bstep (se 1 (by rfl) ⟨1413656, by rfl⟩ : syracuseStep 1884875 = 2827313) B2827313
theorem B8051237 : Blo 1883435 8051237 := bbase (se 4 (by rfl) ⟨754803, by rfl⟩ : syracuseStep 8051237 = 1509607) (by norm_num)
theorem B5367491 : Blo 1883435 5367491 := bstep (se 1 (by rfl) ⟨4025618, by rfl⟩ : syracuseStep 5367491 = 8051237) B8051237
theorem B3578327 : Blo 1883435 3578327 := bstep (se 1 (by rfl) ⟨2683745, by rfl⟩ : syracuseStep 3578327 = 5367491) B5367491
theorem B2385551 : Blo 1883435 2385551 := bstep (se 1 (by rfl) ⟨1789163, by rfl⟩ : syracuseStep 2385551 = 3578327) B3578327
theorem B6361469 : Blo 1883435 6361469 := bstep (se 3 (by rfl) ⟨1192775, by rfl⟩ : syracuseStep 6361469 = 2385551) B2385551
theorem B4240979 : Blo 1883435 4240979 := bstep (se 1 (by rfl) ⟨3180734, by rfl⟩ : syracuseStep 4240979 = 6361469) B6361469
theorem B2827319 : Blo 1883435 2827319 := bstep (se 1 (by rfl) ⟨2120489, by rfl⟩ : syracuseStep 2827319 = 4240979) B4240979
theorem B1884879 : Blo 1883435 1884879 := bstep (se 1 (by rfl) ⟨1413659, by rfl⟩ : syracuseStep 1884879 = 2827319) B2827319
theorem B2827325 : Blo 1883435 2827325 := bbase (se 3 (by rfl) ⟨530123, by rfl⟩ : syracuseStep 2827325 = 1060247) (by norm_num)
theorem B1884883 : Blo 1883435 1884883 := bstep (se 1 (by rfl) ⟨1413662, by rfl⟩ : syracuseStep 1884883 = 2827325) B2827325
theorem B4240997 : Blo 1883435 4240997 := bbase (se 4 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 4240997 = 795187) (by norm_num)
theorem B2827331 : Blo 1883435 2827331 := bstep (se 1 (by rfl) ⟨2120498, by rfl⟩ : syracuseStep 2827331 = 4240997) B4240997
theorem B1884887 : Blo 1883435 1884887 := bstep (se 1 (by rfl) ⟨1413665, by rfl⟩ : syracuseStep 1884887 = 2827331) B2827331
theorem B4771133 : Blo 1883435 4771133 := bbase (se 3 (by rfl) ⟨894587, by rfl⟩ : syracuseStep 4771133 = 1789175) (by norm_num)
theorem B3180755 : Blo 1883435 3180755 := bstep (se 1 (by rfl) ⟨2385566, by rfl⟩ : syracuseStep 3180755 = 4771133) B4771133
theorem B2120503 : Blo 1883435 2120503 := bstep (se 1 (by rfl) ⟨1590377, by rfl⟩ : syracuseStep 2120503 = 3180755) B3180755
theorem B2827337 : Blo 1883435 2827337 := bstep (se 2 (by rfl) ⟨1060251, by rfl⟩ : syracuseStep 2827337 = 2120503) B2120503
theorem B1884891 : Blo 1883435 1884891 := bstep (se 1 (by rfl) ⟨1413668, by rfl⟩ : syracuseStep 1884891 = 2827337) B2827337
theorem B3578357 : Blo 1883435 3578357 := bbase (se 5 (by rfl) ⟨167735, by rfl⟩ : syracuseStep 3578357 = 335471) (by norm_num)
theorem B9542285 : Blo 1883435 9542285 := bstep (se 3 (by rfl) ⟨1789178, by rfl⟩ : syracuseStep 9542285 = 3578357) B3578357
theorem B6361523 : Blo 1883435 6361523 := bstep (se 1 (by rfl) ⟨4771142, by rfl⟩ : syracuseStep 6361523 = 9542285) B9542285
theorem B4241015 : Blo 1883435 4241015 := bstep (se 1 (by rfl) ⟨3180761, by rfl⟩ : syracuseStep 4241015 = 6361523) B6361523
theorem B2827343 : Blo 1883435 2827343 := bstep (se 1 (by rfl) ⟨2120507, by rfl⟩ : syracuseStep 2827343 = 4241015) B4241015
theorem B1884895 : Blo 1883435 1884895 := bstep (se 1 (by rfl) ⟨1413671, by rfl⟩ : syracuseStep 1884895 = 2827343) B2827343
theorem B2827349 : Blo 1883435 2827349 := bbase (se 8 (by rfl) ⟨16566, by rfl⟩ : syracuseStep 2827349 = 33133) (by norm_num)
theorem B1884899 : Blo 1883435 1884899 := bstep (se 1 (by rfl) ⟨1413674, by rfl⟩ : syracuseStep 1884899 = 2827349) B2827349
theorem B1910621 : Blo 1883435 1910621 := bbase (se 3 (by rfl) ⟨358241, by rfl⟩ : syracuseStep 1910621 = 716483) (by norm_num)
theorem B5094989 : Blo 1883435 5094989 := bstep (se 3 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 5094989 = 1910621) B1910621
theorem B3396659 : Blo 1883435 3396659 := bstep (se 1 (by rfl) ⟨2547494, by rfl⟩ : syracuseStep 3396659 = 5094989) B5094989
theorem B9057757 : Blo 1883435 9057757 := bstep (se 3 (by rfl) ⟨1698329, by rfl⟩ : syracuseStep 9057757 = 3396659) B3396659
theorem B12077009 : Blo 1883435 12077009 := bstep (se 2 (by rfl) ⟨4528878, by rfl⟩ : syracuseStep 12077009 = 9057757) B9057757
theorem B8051339 : Blo 1883435 8051339 := bstep (se 1 (by rfl) ⟨6038504, by rfl⟩ : syracuseStep 8051339 = 12077009) B12077009
theorem B5367559 : Blo 1883435 5367559 := bstep (se 1 (by rfl) ⟨4025669, by rfl⟩ : syracuseStep 5367559 = 8051339) B8051339
theorem B7156745 : Blo 1883435 7156745 := bstep (se 2 (by rfl) ⟨2683779, by rfl⟩ : syracuseStep 7156745 = 5367559) B5367559
theorem B4771163 : Blo 1883435 4771163 := bstep (se 1 (by rfl) ⟨3578372, by rfl⟩ : syracuseStep 4771163 = 7156745) B7156745
theorem B3180775 : Blo 1883435 3180775 := bstep (se 1 (by rfl) ⟨2385581, by rfl⟩ : syracuseStep 3180775 = 4771163) B4771163
theorem B4241033 : Blo 1883435 4241033 := bstep (se 2 (by rfl) ⟨1590387, by rfl⟩ : syracuseStep 4241033 = 3180775) B3180775
theorem B2827355 : Blo 1883435 2827355 := bstep (se 1 (by rfl) ⟨2120516, by rfl⟩ : syracuseStep 2827355 = 4241033) B4241033
theorem B1884903 : Blo 1883435 1884903 := bstep (se 1 (by rfl) ⟨1413677, by rfl⟩ : syracuseStep 1884903 = 2827355) B2827355
theorem B2120521 : Blo 1883435 2120521 := bbase (se 2 (by rfl) ⟨795195, by rfl⟩ : syracuseStep 2120521 = 1590391) (by norm_num)
theorem B2827361 : Blo 1883435 2827361 := bstep (se 2 (by rfl) ⟨1060260, by rfl⟩ : syracuseStep 2827361 = 2120521) B2120521
theorem B1884907 : Blo 1883435 1884907 := bstep (se 1 (by rfl) ⟨1413680, by rfl⟩ : syracuseStep 1884907 = 2827361) B2827361
theorem B1910629 : Blo 1883435 1910629 := bbase (se 4 (by rfl) ⟨179121, by rfl⟩ : syracuseStep 1910629 = 358243) (by norm_num)
theorem B2547505 : Blo 1883435 2547505 := bstep (se 2 (by rfl) ⟨955314, by rfl⟩ : syracuseStep 2547505 = 1910629) B1910629
theorem B3396673 : Blo 1883435 3396673 := bstep (se 2 (by rfl) ⟨1273752, by rfl⟩ : syracuseStep 3396673 = 2547505) B2547505
theorem B18115589 : Blo 1883435 18115589 := bstep (se 4 (by rfl) ⟨1698336, by rfl⟩ : syracuseStep 18115589 = 3396673) B3396673
theorem B12077059 : Blo 1883435 12077059 := bstep (se 1 (by rfl) ⟨9057794, by rfl⟩ : syracuseStep 12077059 = 18115589) B18115589
theorem B16102745 : Blo 1883435 16102745 := bstep (se 2 (by rfl) ⟨6038529, by rfl⟩ : syracuseStep 16102745 = 12077059) B12077059
theorem B10735163 : Blo 1883435 10735163 := bstep (se 1 (by rfl) ⟨8051372, by rfl⟩ : syracuseStep 10735163 = 16102745) B16102745
theorem B7156775 : Blo 1883435 7156775 := bstep (se 1 (by rfl) ⟨5367581, by rfl⟩ : syracuseStep 7156775 = 10735163) B10735163
theorem B4771183 : Blo 1883435 4771183 := bstep (se 1 (by rfl) ⟨3578387, by rfl⟩ : syracuseStep 4771183 = 7156775) B7156775
theorem B6361577 : Blo 1883435 6361577 := bstep (se 2 (by rfl) ⟨2385591, by rfl⟩ : syracuseStep 6361577 = 4771183) B4771183
theorem B4241051 : Blo 1883435 4241051 := bstep (se 1 (by rfl) ⟨3180788, by rfl⟩ : syracuseStep 4241051 = 6361577) B6361577
theorem B2827367 : Blo 1883435 2827367 := bstep (se 1 (by rfl) ⟨2120525, by rfl⟩ : syracuseStep 2827367 = 4241051) B4241051
theorem B1884911 : Blo 1883435 1884911 := bstep (se 1 (by rfl) ⟨1413683, by rfl⟩ : syracuseStep 1884911 = 2827367) B2827367
theorem B2827373 : Blo 1883435 2827373 := bbase (se 3 (by rfl) ⟨530132, by rfl⟩ : syracuseStep 2827373 = 1060265) (by norm_num)
theorem B1884915 : Blo 1883435 1884915 := bstep (se 1 (by rfl) ⟨1413686, by rfl⟩ : syracuseStep 1884915 = 2827373) B2827373
theorem B4241069 : Blo 1883435 4241069 := bbase (se 3 (by rfl) ⟨795200, by rfl⟩ : syracuseStep 4241069 = 1590401) (by norm_num)
theorem B2827379 : Blo 1883435 2827379 := bstep (se 1 (by rfl) ⟨2120534, by rfl⟩ : syracuseStep 2827379 = 4241069) B4241069
theorem B1884919 : Blo 1883435 1884919 := bstep (se 1 (by rfl) ⟨1413689, by rfl⟩ : syracuseStep 1884919 = 2827379) B2827379
theorem B3019285 : Blo 1883435 3019285 := bbase (se 6 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 3019285 = 141529) (by norm_num)
theorem B4025713 : Blo 1883435 4025713 := bstep (se 2 (by rfl) ⟨1509642, by rfl⟩ : syracuseStep 4025713 = 3019285) B3019285
theorem B5367617 : Blo 1883435 5367617 := bstep (se 2 (by rfl) ⟨2012856, by rfl⟩ : syracuseStep 5367617 = 4025713) B4025713
theorem B3578411 : Blo 1883435 3578411 := bstep (se 1 (by rfl) ⟨2683808, by rfl⟩ : syracuseStep 3578411 = 5367617) B5367617
theorem B2385607 : Blo 1883435 2385607 := bstep (se 1 (by rfl) ⟨1789205, by rfl⟩ : syracuseStep 2385607 = 3578411) B3578411
theorem B3180809 : Blo 1883435 3180809 := bstep (se 2 (by rfl) ⟨1192803, by rfl⟩ : syracuseStep 3180809 = 2385607) B2385607
theorem B2120539 : Blo 1883435 2120539 := bstep (se 1 (by rfl) ⟨1590404, by rfl⟩ : syracuseStep 2120539 = 3180809) B3180809
theorem B2827385 : Blo 1883435 2827385 := bstep (se 2 (by rfl) ⟨1060269, by rfl⟩ : syracuseStep 2827385 = 2120539) B2120539
theorem B1884923 : Blo 1883435 1884923 := bstep (se 1 (by rfl) ⟨1413692, by rfl⟩ : syracuseStep 1884923 = 2827385) B2827385
theorem B3060485 : Blo 1883435 3060485 := bbase (se 4 (by rfl) ⟨286920, by rfl⟩ : syracuseStep 3060485 = 573841) (by norm_num)
theorem B2040323 : Blo 1883435 2040323 := bstep (se 1 (by rfl) ⟨1530242, by rfl⟩ : syracuseStep 2040323 = 3060485) B3060485
theorem B5440861 : Blo 1883435 5440861 := bstep (se 3 (by rfl) ⟨1020161, by rfl⟩ : syracuseStep 5440861 = 2040323) B2040323
theorem B7254481 : Blo 1883435 7254481 := bstep (se 2 (by rfl) ⟨2720430, by rfl⟩ : syracuseStep 7254481 = 5440861) B5440861
theorem B9672641 : Blo 1883435 9672641 := bstep (se 2 (by rfl) ⟨3627240, by rfl⟩ : syracuseStep 9672641 = 7254481) B7254481
theorem B6448427 : Blo 1883435 6448427 := bstep (se 1 (by rfl) ⟨4836320, by rfl⟩ : syracuseStep 6448427 = 9672641) B9672641
theorem B4298951 : Blo 1883435 4298951 := bstep (se 1 (by rfl) ⟨3224213, by rfl⟩ : syracuseStep 4298951 = 6448427) B6448427
theorem B11463869 : Blo 1883435 11463869 := bstep (se 3 (by rfl) ⟨2149475, by rfl⟩ : syracuseStep 11463869 = 4298951) B4298951
theorem B7642579 : Blo 1883435 7642579 := bstep (se 1 (by rfl) ⟨5731934, by rfl⟩ : syracuseStep 7642579 = 11463869) B11463869
theorem B10190105 : Blo 1883435 10190105 := bstep (se 2 (by rfl) ⟨3821289, by rfl⟩ : syracuseStep 10190105 = 7642579) B7642579
theorem B6793403 : Blo 1883435 6793403 := bstep (se 1 (by rfl) ⟨5095052, by rfl⟩ : syracuseStep 6793403 = 10190105) B10190105
theorem B18115741 : Blo 1883435 18115741 := bstep (se 3 (by rfl) ⟨3396701, by rfl⟩ : syracuseStep 18115741 = 6793403) B6793403
theorem B24154321 : Blo 1883435 24154321 := bstep (se 2 (by rfl) ⟨9057870, by rfl⟩ : syracuseStep 24154321 = 18115741) B18115741
theorem B32205761 : Blo 1883435 32205761 := bstep (se 2 (by rfl) ⟨12077160, by rfl⟩ : syracuseStep 32205761 = 24154321) B24154321
theorem B21470507 : Blo 1883435 21470507 := bstep (se 1 (by rfl) ⟨16102880, by rfl⟩ : syracuseStep 21470507 = 32205761) B32205761
theorem B14313671 : Blo 1883435 14313671 := bstep (se 1 (by rfl) ⟨10735253, by rfl⟩ : syracuseStep 14313671 = 21470507) B21470507
theorem B9542447 : Blo 1883435 9542447 := bstep (se 1 (by rfl) ⟨7156835, by rfl⟩ : syracuseStep 9542447 = 14313671) B14313671
theorem B6361631 : Blo 1883435 6361631 := bstep (se 1 (by rfl) ⟨4771223, by rfl⟩ : syracuseStep 6361631 = 9542447) B9542447
theorem B4241087 : Blo 1883435 4241087 := bstep (se 1 (by rfl) ⟨3180815, by rfl⟩ : syracuseStep 4241087 = 6361631) B6361631
theorem B2827391 : Blo 1883435 2827391 := bstep (se 1 (by rfl) ⟨2120543, by rfl⟩ : syracuseStep 2827391 = 4241087) B4241087
theorem B1884927 : Blo 1883435 1884927 := bstep (se 1 (by rfl) ⟨1413695, by rfl⟩ : syracuseStep 1884927 = 2827391) B2827391
theorem B2827397 : Blo 1883435 2827397 := bbase (se 4 (by rfl) ⟨265068, by rfl⟩ : syracuseStep 2827397 = 530137) (by norm_num)
theorem B1884931 : Blo 1883435 1884931 := bstep (se 1 (by rfl) ⟨1413698, by rfl⟩ : syracuseStep 1884931 = 2827397) B2827397
theorem B3180829 : Blo 1883435 3180829 := bbase (se 3 (by rfl) ⟨596405, by rfl⟩ : syracuseStep 3180829 = 1192811) (by norm_num)
theorem B4241105 : Blo 1883435 4241105 := bstep (se 2 (by rfl) ⟨1590414, by rfl⟩ : syracuseStep 4241105 = 3180829) B3180829
theorem B2827403 : Blo 1883435 2827403 := bstep (se 1 (by rfl) ⟨2120552, by rfl⟩ : syracuseStep 2827403 = 4241105) B4241105
theorem B1884935 : Blo 1883435 1884935 := bstep (se 1 (by rfl) ⟨1413701, by rfl⟩ : syracuseStep 1884935 = 2827403) B2827403
theorem B2120557 : Blo 1883435 2120557 := bbase (se 3 (by rfl) ⟨397604, by rfl⟩ : syracuseStep 2120557 = 795209) (by norm_num)
theorem B2827409 : Blo 1883435 2827409 := bstep (se 2 (by rfl) ⟨1060278, by rfl⟩ : syracuseStep 2827409 = 2120557) B2120557
theorem B1884939 : Blo 1883435 1884939 := bstep (se 1 (by rfl) ⟨1413704, by rfl⟩ : syracuseStep 1884939 = 2827409) B2827409
theorem B6361685 : Blo 1883435 6361685 := bbase (se 8 (by rfl) ⟨37275, by rfl⟩ : syracuseStep 6361685 = 74551) (by norm_num)
theorem B4241123 : Blo 1883435 4241123 := bstep (se 1 (by rfl) ⟨3180842, by rfl⟩ : syracuseStep 4241123 = 6361685) B6361685
theorem B2827415 : Blo 1883435 2827415 := bstep (se 1 (by rfl) ⟨2120561, by rfl⟩ : syracuseStep 2827415 = 4241123) B4241123
theorem B1884943 : Blo 1883435 1884943 := bstep (se 1 (by rfl) ⟨1413707, by rfl⟩ : syracuseStep 1884943 = 2827415) B2827415
theorem B2827421 : Blo 1883435 2827421 := bbase (se 3 (by rfl) ⟨530141, by rfl⟩ : syracuseStep 2827421 = 1060283) (by norm_num)
theorem B1884947 : Blo 1883435 1884947 := bstep (se 1 (by rfl) ⟨1413710, by rfl⟩ : syracuseStep 1884947 = 2827421) B2827421
theorem B4241141 : Blo 1883435 4241141 := bbase (se 5 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 4241141 = 397607) (by norm_num)
theorem B2827427 : Blo 1883435 2827427 := bstep (se 1 (by rfl) ⟨2120570, by rfl⟩ : syracuseStep 2827427 = 4241141) B4241141
theorem B1884951 : Blo 1883435 1884951 := bstep (se 1 (by rfl) ⟨1413713, by rfl⟩ : syracuseStep 1884951 = 2827427) B2827427
theorem B5732021 : Blo 1883435 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B3821347 : Blo 1883435 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B20380517 : Blo 1883435 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B13587011 : Blo 1883435 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B9058007 : Blo 1883435 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B24154685 : Blo 1883435 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B16103123 : Blo 1883435 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B10735415 : Blo 1883435 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B7156943 : Blo 1883435 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B4771295 : Blo 1883435 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B3180863 : Blo 1883435 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B2120575 : Blo 1883435 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B2827433 : Blo 1883435 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B1884955 : Blo 1883435 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B4025789 : Blo 1883435 4025789 := bbase (se 3 (by rfl) ⟨754835, by rfl⟩ : syracuseStep 4025789 = 1509671) (by norm_num)
theorem B2683859 : Blo 1883435 2683859 := bstep (se 1 (by rfl) ⟨2012894, by rfl⟩ : syracuseStep 2683859 = 4025789) B4025789
theorem B7156957 : Blo 1883435 7156957 := bstep (se 3 (by rfl) ⟨1341929, by rfl⟩ : syracuseStep 7156957 = 2683859) B2683859
theorem B9542609 : Blo 1883435 9542609 := bstep (se 2 (by rfl) ⟨3578478, by rfl⟩ : syracuseStep 9542609 = 7156957) B7156957
theorem B6361739 : Blo 1883435 6361739 := bstep (se 1 (by rfl) ⟨4771304, by rfl⟩ : syracuseStep 6361739 = 9542609) B9542609
theorem B4241159 : Blo 1883435 4241159 := bstep (se 1 (by rfl) ⟨3180869, by rfl⟩ : syracuseStep 4241159 = 6361739) B6361739
theorem B2827439 : Blo 1883435 2827439 := bstep (se 1 (by rfl) ⟨2120579, by rfl⟩ : syracuseStep 2827439 = 4241159) B4241159
theorem B1884959 : Blo 1883435 1884959 := bstep (se 1 (by rfl) ⟨1413719, by rfl⟩ : syracuseStep 1884959 = 2827439) B2827439
theorem B2827445 : Blo 1883435 2827445 := bbase (se 5 (by rfl) ⟨132536, by rfl⟩ : syracuseStep 2827445 = 265073) (by norm_num)
theorem B1884963 : Blo 1883435 1884963 := bstep (se 1 (by rfl) ⟨1413722, by rfl⟩ : syracuseStep 1884963 = 2827445) B2827445
theorem B4771325 : Blo 1883435 4771325 := bbase (se 3 (by rfl) ⟨894623, by rfl⟩ : syracuseStep 4771325 = 1789247) (by norm_num)
theorem B3180883 : Blo 1883435 3180883 := bstep (se 1 (by rfl) ⟨2385662, by rfl⟩ : syracuseStep 3180883 = 4771325) B4771325
theorem B4241177 : Blo 1883435 4241177 := bstep (se 2 (by rfl) ⟨1590441, by rfl⟩ : syracuseStep 4241177 = 3180883) B3180883
theorem B2827451 : Blo 1883435 2827451 := bstep (se 1 (by rfl) ⟨2120588, by rfl⟩ : syracuseStep 2827451 = 4241177) B4241177
theorem B1884967 : Blo 1883435 1884967 := bstep (se 1 (by rfl) ⟨1413725, by rfl⟩ : syracuseStep 1884967 = 2827451) B2827451
theorem B2120593 : Blo 1883435 2120593 := bbase (se 2 (by rfl) ⟨795222, by rfl⟩ : syracuseStep 2120593 = 1590445) (by norm_num)
theorem B2827457 : Blo 1883435 2827457 := bstep (se 2 (by rfl) ⟨1060296, by rfl⟩ : syracuseStep 2827457 = 2120593) B2120593
theorem B1884971 : Blo 1883435 1884971 := bstep (se 1 (by rfl) ⟨1413728, by rfl⟩ : syracuseStep 1884971 = 2827457) B2827457
theorem B3578509 : Blo 1883435 3578509 := bbase (se 3 (by rfl) ⟨670970, by rfl⟩ : syracuseStep 3578509 = 1341941) (by norm_num)
theorem B4771345 : Blo 1883435 4771345 := bstep (se 2 (by rfl) ⟨1789254, by rfl⟩ : syracuseStep 4771345 = 3578509) B3578509
theorem B6361793 : Blo 1883435 6361793 := bstep (se 2 (by rfl) ⟨2385672, by rfl⟩ : syracuseStep 6361793 = 4771345) B4771345
theorem B4241195 : Blo 1883435 4241195 := bstep (se 1 (by rfl) ⟨3180896, by rfl⟩ : syracuseStep 4241195 = 6361793) B6361793
theorem B2827463 : Blo 1883435 2827463 := bstep (se 1 (by rfl) ⟨2120597, by rfl⟩ : syracuseStep 2827463 = 4241195) B4241195
theorem B1884975 : Blo 1883435 1884975 := bstep (se 1 (by rfl) ⟨1413731, by rfl⟩ : syracuseStep 1884975 = 2827463) B2827463
theorem B2827469 : Blo 1883435 2827469 := bbase (se 3 (by rfl) ⟨530150, by rfl⟩ : syracuseStep 2827469 = 1060301) (by norm_num)
theorem B1884979 : Blo 1883435 1884979 := bstep (se 1 (by rfl) ⟨1413734, by rfl⟩ : syracuseStep 1884979 = 2827469) B2827469
theorem B4241213 : Blo 1883435 4241213 := bbase (se 3 (by rfl) ⟨795227, by rfl⟩ : syracuseStep 4241213 = 1590455) (by norm_num)
theorem B2827475 : Blo 1883435 2827475 := bstep (se 1 (by rfl) ⟨2120606, by rfl⟩ : syracuseStep 2827475 = 4241213) B4241213
theorem B1884983 : Blo 1883435 1884983 := bstep (se 1 (by rfl) ⟨1413737, by rfl⟩ : syracuseStep 1884983 = 2827475) B2827475
theorem B3180917 : Blo 1883435 3180917 := bbase (se 5 (by rfl) ⟨149105, by rfl⟩ : syracuseStep 3180917 = 298211) (by norm_num)
theorem B2120611 : Blo 1883435 2120611 := bstep (se 1 (by rfl) ⟨1590458, by rfl⟩ : syracuseStep 2120611 = 3180917) B3180917
theorem B2827481 : Blo 1883435 2827481 := bstep (se 2 (by rfl) ⟨1060305, by rfl⟩ : syracuseStep 2827481 = 2120611) B2120611
theorem B1884987 : Blo 1883435 1884987 := bstep (se 1 (by rfl) ⟨1413740, by rfl⟩ : syracuseStep 1884987 = 2827481) B2827481
theorem B2264545 : Blo 1883435 2264545 := bbase (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) (by norm_num)
theorem B3019393 : Blo 1883435 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B4025857 : Blo 1883435 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B5367809 : Blo 1883435 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B14314157 : Blo 1883435 14314157 := bstep (se 3 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 14314157 = 5367809) B5367809
theorem B9542771 : Blo 1883435 9542771 := bstep (se 1 (by rfl) ⟨7157078, by rfl⟩ : syracuseStep 9542771 = 14314157) B14314157
theorem B6361847 : Blo 1883435 6361847 := bstep (se 1 (by rfl) ⟨4771385, by rfl⟩ : syracuseStep 6361847 = 9542771) B9542771
theorem B4241231 : Blo 1883435 4241231 := bstep (se 1 (by rfl) ⟨3180923, by rfl⟩ : syracuseStep 4241231 = 6361847) B6361847
theorem B2827487 : Blo 1883435 2827487 := bstep (se 1 (by rfl) ⟨2120615, by rfl⟩ : syracuseStep 2827487 = 4241231) B4241231
theorem B1884991 : Blo 1883435 1884991 := bstep (se 1 (by rfl) ⟨1413743, by rfl⟩ : syracuseStep 1884991 = 2827487) B2827487
theorem B2827493 : Blo 1883435 2827493 := bbase (se 4 (by rfl) ⟨265077, by rfl⟩ : syracuseStep 2827493 = 530155) (by norm_num)
theorem B1884995 : Blo 1883435 1884995 := bstep (se 1 (by rfl) ⟨1413746, by rfl⟩ : syracuseStep 1884995 = 2827493) B2827493
theorem B16323221 : Blo 1883435 16323221 := bbase (se 6 (by rfl) ⟨382575, by rfl⟩ : syracuseStep 16323221 = 765151) (by norm_num)
theorem B10882147 : Blo 1883435 10882147 := bstep (se 1 (by rfl) ⟨8161610, by rfl⟩ : syracuseStep 10882147 = 16323221) B16323221
theorem B14509529 : Blo 1883435 14509529 := bstep (se 2 (by rfl) ⟨5441073, by rfl⟩ : syracuseStep 14509529 = 10882147) B10882147
theorem B9673019 : Blo 1883435 9673019 := bstep (se 1 (by rfl) ⟨7254764, by rfl⟩ : syracuseStep 9673019 = 14509529) B14509529
theorem B6448679 : Blo 1883435 6448679 := bstep (se 1 (by rfl) ⟨4836509, by rfl⟩ : syracuseStep 6448679 = 9673019) B9673019
theorem B4299119 : Blo 1883435 4299119 := bstep (se 1 (by rfl) ⟨3224339, by rfl⟩ : syracuseStep 4299119 = 6448679) B6448679
theorem B2866079 : Blo 1883435 2866079 := bstep (se 1 (by rfl) ⟨2149559, by rfl⟩ : syracuseStep 2866079 = 4299119) B4299119
theorem B1910719 : Blo 1883435 1910719 := bstep (se 1 (by rfl) ⟨1433039, by rfl⟩ : syracuseStep 1910719 = 2866079) B2866079
theorem B2547625 : Blo 1883435 2547625 := bstep (se 2 (by rfl) ⟨955359, by rfl⟩ : syracuseStep 2547625 = 1910719) B1910719
theorem B3396833 : Blo 1883435 3396833 := bstep (se 2 (by rfl) ⟨1273812, by rfl⟩ : syracuseStep 3396833 = 2547625) B2547625
theorem B2264555 : Blo 1883435 2264555 := bstep (se 1 (by rfl) ⟨1698416, by rfl⟩ : syracuseStep 2264555 = 3396833) B3396833
theorem B6038813 : Blo 1883435 6038813 := bstep (se 3 (by rfl) ⟨1132277, by rfl⟩ : syracuseStep 6038813 = 2264555) B2264555
theorem B4025875 : Blo 1883435 4025875 := bstep (se 1 (by rfl) ⟨3019406, by rfl⟩ : syracuseStep 4025875 = 6038813) B6038813
theorem B5367833 : Blo 1883435 5367833 := bstep (se 2 (by rfl) ⟨2012937, by rfl⟩ : syracuseStep 5367833 = 4025875) B4025875
theorem B3578555 : Blo 1883435 3578555 := bstep (se 1 (by rfl) ⟨2683916, by rfl⟩ : syracuseStep 3578555 = 5367833) B5367833
theorem B2385703 : Blo 1883435 2385703 := bstep (se 1 (by rfl) ⟨1789277, by rfl⟩ : syracuseStep 2385703 = 3578555) B3578555
theorem B3180937 : Blo 1883435 3180937 := bstep (se 2 (by rfl) ⟨1192851, by rfl⟩ : syracuseStep 3180937 = 2385703) B2385703
theorem B4241249 : Blo 1883435 4241249 := bstep (se 2 (by rfl) ⟨1590468, by rfl⟩ : syracuseStep 4241249 = 3180937) B3180937
theorem B2827499 : Blo 1883435 2827499 := bstep (se 1 (by rfl) ⟨2120624, by rfl⟩ : syracuseStep 2827499 = 4241249) B4241249
theorem B1884999 : Blo 1883435 1884999 := bstep (se 1 (by rfl) ⟨1413749, by rfl⟩ : syracuseStep 1884999 = 2827499) B2827499
theorem B2120629 : Blo 1883435 2120629 := bbase (se 5 (by rfl) ⟨99404, by rfl⟩ : syracuseStep 2120629 = 198809) (by norm_num)
theorem B2827505 : Blo 1883435 2827505 := bstep (se 2 (by rfl) ⟨1060314, by rfl⟩ : syracuseStep 2827505 = 2120629) B2120629
theorem B1885003 : Blo 1883435 1885003 := bstep (se 1 (by rfl) ⟨1413752, by rfl⟩ : syracuseStep 1885003 = 2827505) B2827505
theorem B2385713 : Blo 1883435 2385713 := bbase (se 2 (by rfl) ⟨894642, by rfl⟩ : syracuseStep 2385713 = 1789285) (by norm_num)
theorem B6361901 : Blo 1883435 6361901 := bstep (se 3 (by rfl) ⟨1192856, by rfl⟩ : syracuseStep 6361901 = 2385713) B2385713
theorem B4241267 : Blo 1883435 4241267 := bstep (se 1 (by rfl) ⟨3180950, by rfl⟩ : syracuseStep 4241267 = 6361901) B6361901
theorem B2827511 : Blo 1883435 2827511 := bstep (se 1 (by rfl) ⟨2120633, by rfl⟩ : syracuseStep 2827511 = 4241267) B4241267
theorem B1885007 : Blo 1883435 1885007 := bstep (se 1 (by rfl) ⟨1413755, by rfl⟩ : syracuseStep 1885007 = 2827511) B2827511
theorem B2827517 : Blo 1883435 2827517 := bbase (se 3 (by rfl) ⟨530159, by rfl⟩ : syracuseStep 2827517 = 1060319) (by norm_num)
theorem B1885011 : Blo 1883435 1885011 := bstep (se 1 (by rfl) ⟨1413758, by rfl⟩ : syracuseStep 1885011 = 2827517) B2827517
theorem B4241285 : Blo 1883435 4241285 := bbase (se 4 (by rfl) ⟨397620, by rfl⟩ : syracuseStep 4241285 = 795241) (by norm_num)
theorem B2827523 : Blo 1883435 2827523 := bstep (se 1 (by rfl) ⟨2120642, by rfl⟩ : syracuseStep 2827523 = 4241285) B4241285
theorem B1885015 : Blo 1883435 1885015 := bstep (se 1 (by rfl) ⟨1413761, by rfl⟩ : syracuseStep 1885015 = 2827523) B2827523
theorem B2866109 : Blo 1883435 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B7642957 : Blo 1883435 7642957 := bstep (se 3 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 7642957 = 2866109) B2866109
theorem B10190609 : Blo 1883435 10190609 := bstep (se 2 (by rfl) ⟨3821478, by rfl⟩ : syracuseStep 10190609 = 7642957) B7642957
theorem B6793739 : Blo 1883435 6793739 := bstep (se 1 (by rfl) ⟨5095304, by rfl⟩ : syracuseStep 6793739 = 10190609) B10190609
theorem B4529159 : Blo 1883435 4529159 := bstep (se 1 (by rfl) ⟨3396869, by rfl⟩ : syracuseStep 4529159 = 6793739) B6793739
theorem B3019439 : Blo 1883435 3019439 := bstep (se 1 (by rfl) ⟨2264579, by rfl⟩ : syracuseStep 3019439 = 4529159) B4529159
theorem B2012959 : Blo 1883435 2012959 := bstep (se 1 (by rfl) ⟨1509719, by rfl⟩ : syracuseStep 2012959 = 3019439) B3019439
theorem B2683945 : Blo 1883435 2683945 := bstep (se 2 (by rfl) ⟨1006479, by rfl⟩ : syracuseStep 2683945 = 2012959) B2012959
theorem B3578593 : Blo 1883435 3578593 := bstep (se 2 (by rfl) ⟨1341972, by rfl⟩ : syracuseStep 3578593 = 2683945) B2683945
theorem B4771457 : Blo 1883435 4771457 := bstep (se 2 (by rfl) ⟨1789296, by rfl⟩ : syracuseStep 4771457 = 3578593) B3578593
theorem B3180971 : Blo 1883435 3180971 := bstep (se 1 (by rfl) ⟨2385728, by rfl⟩ : syracuseStep 3180971 = 4771457) B4771457
theorem B2120647 : Blo 1883435 2120647 := bstep (se 1 (by rfl) ⟨1590485, by rfl⟩ : syracuseStep 2120647 = 3180971) B3180971
theorem B2827529 : Blo 1883435 2827529 := bstep (se 2 (by rfl) ⟨1060323, by rfl⟩ : syracuseStep 2827529 = 2120647) B2120647
theorem B1885019 : Blo 1883435 1885019 := bstep (se 1 (by rfl) ⟨1413764, by rfl⟩ : syracuseStep 1885019 = 2827529) B2827529
theorem B9542933 : Blo 1883435 9542933 := bbase (se 6 (by rfl) ⟨223662, by rfl⟩ : syracuseStep 9542933 = 447325) (by norm_num)
theorem B6361955 : Blo 1883435 6361955 := bstep (se 1 (by rfl) ⟨4771466, by rfl⟩ : syracuseStep 6361955 = 9542933) B9542933
theorem B4241303 : Blo 1883435 4241303 := bstep (se 1 (by rfl) ⟨3180977, by rfl⟩ : syracuseStep 4241303 = 6361955) B6361955
theorem B2827535 : Blo 1883435 2827535 := bstep (se 1 (by rfl) ⟨2120651, by rfl⟩ : syracuseStep 2827535 = 4241303) B4241303
theorem B1885023 : Blo 1883435 1885023 := bstep (se 1 (by rfl) ⟨1413767, by rfl⟩ : syracuseStep 1885023 = 2827535) B2827535
theorem B2827541 : Blo 1883435 2827541 := bbase (se 6 (by rfl) ⟨66270, by rfl⟩ : syracuseStep 2827541 = 132541) (by norm_num)
theorem B1885027 : Blo 1883435 1885027 := bstep (se 1 (by rfl) ⟨1413770, by rfl⟩ : syracuseStep 1885027 = 2827541) B2827541
theorem B9307237 : Blo 1883435 9307237 := bbase (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) (by norm_num)
theorem B12409649 : Blo 1883435 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B8273099 : Blo 1883435 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B5515399 : Blo 1883435 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B7353865 : Blo 1883435 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B9805153 : Blo 1883435 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B13073537 : Blo 1883435 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B8715691 : Blo 1883435 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B11620921 : Blo 1883435 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B15494561 : Blo 1883435 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B10329707 : Blo 1883435 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B6886471 : Blo 1883435 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B9181961 : Blo 1883435 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B6121307 : Blo 1883435 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B4080871 : Blo 1883435 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B21764645 : Blo 1883435 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B14509763 : Blo 1883435 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B9673175 : Blo 1883435 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B6448783 : Blo 1883435 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B8598377 : Blo 1883435 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B5732251 : Blo 1883435 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B30572005 : Blo 1883435 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B40762673 : Blo 1883435 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B27175115 : Blo 1883435 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B18116743 : Blo 1883435 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B24155657 : Blo 1883435 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B16103771 : Blo 1883435 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B10735847 : Blo 1883435 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B7157231 : Blo 1883435 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B4771487 : Blo 1883435 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B3180991 : Blo 1883435 3180991 := bstep (se 1 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 3180991 = 4771487) B4771487
theorem B4241321 : Blo 1883435 4241321 := bstep (se 2 (by rfl) ⟨1590495, by rfl⟩ : syracuseStep 4241321 = 3180991) B3180991
theorem B2827547 : Blo 1883435 2827547 := bstep (se 1 (by rfl) ⟨2120660, by rfl⟩ : syracuseStep 2827547 = 4241321) B4241321
theorem B1885031 : Blo 1883435 1885031 := bstep (se 1 (by rfl) ⟨1413773, by rfl⟩ : syracuseStep 1885031 = 2827547) B2827547
theorem B2120665 : Blo 1883435 2120665 := bbase (se 2 (by rfl) ⟨795249, by rfl⟩ : syracuseStep 2120665 = 1590499) (by norm_num)
theorem B2827553 : Blo 1883435 2827553 := bstep (se 2 (by rfl) ⟨1060332, by rfl⟩ : syracuseStep 2827553 = 2120665) B2120665
theorem B1885035 : Blo 1883435 1885035 := bstep (se 1 (by rfl) ⟨1413776, by rfl⟩ : syracuseStep 1885035 = 2827553) B2827553
theorem B2683973 : Blo 1883435 2683973 := bbase (se 4 (by rfl) ⟨251622, by rfl⟩ : syracuseStep 2683973 = 503245) (by norm_num)
theorem B7157261 : Blo 1883435 7157261 := bstep (se 3 (by rfl) ⟨1341986, by rfl⟩ : syracuseStep 7157261 = 2683973) B2683973
theorem B4771507 : Blo 1883435 4771507 := bstep (se 1 (by rfl) ⟨3578630, by rfl⟩ : syracuseStep 4771507 = 7157261) B7157261
theorem B6362009 : Blo 1883435 6362009 := bstep (se 2 (by rfl) ⟨2385753, by rfl⟩ : syracuseStep 6362009 = 4771507) B4771507
theorem B4241339 : Blo 1883435 4241339 := bstep (se 1 (by rfl) ⟨3181004, by rfl⟩ : syracuseStep 4241339 = 6362009) B6362009
theorem B2827559 : Blo 1883435 2827559 := bstep (se 1 (by rfl) ⟨2120669, by rfl⟩ : syracuseStep 2827559 = 4241339) B4241339
theorem B1885039 : Blo 1883435 1885039 := bstep (se 1 (by rfl) ⟨1413779, by rfl⟩ : syracuseStep 1885039 = 2827559) B2827559
theorem B2827565 : Blo 1883435 2827565 := bbase (se 3 (by rfl) ⟨530168, by rfl⟩ : syracuseStep 2827565 = 1060337) (by norm_num)
theorem B1885043 : Blo 1883435 1885043 := bstep (se 1 (by rfl) ⟨1413782, by rfl⟩ : syracuseStep 1885043 = 2827565) B2827565
theorem B4241357 : Blo 1883435 4241357 := bbase (se 3 (by rfl) ⟨795254, by rfl⟩ : syracuseStep 4241357 = 1590509) (by norm_num)
theorem B2827571 : Blo 1883435 2827571 := bstep (se 1 (by rfl) ⟨2120678, by rfl⟩ : syracuseStep 2827571 = 4241357) B4241357
theorem B1885047 : Blo 1883435 1885047 := bstep (se 1 (by rfl) ⟨1413785, by rfl⟩ : syracuseStep 1885047 = 2827571) B2827571
theorem B2385769 : Blo 1883435 2385769 := bbase (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) (by norm_num)
theorem B3181025 : Blo 1883435 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B2120683 : Blo 1883435 2120683 := bstep (se 1 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 2120683 = 3181025) B3181025
theorem B2827577 : Blo 1883435 2827577 := bstep (se 2 (by rfl) ⟨1060341, by rfl⟩ : syracuseStep 2827577 = 2120683) B2120683
theorem B1885051 : Blo 1883435 1885051 := bstep (se 1 (by rfl) ⟨1413788, by rfl⟩ : syracuseStep 1885051 = 2827577) B2827577
theorem B4653677 : Blo 1883435 4653677 := bbase (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) (by norm_num)
theorem B12409805 : Blo 1883435 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B33092813 : Blo 1883435 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B88247501 : Blo 1883435 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B58831667 : Blo 1883435 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B39221111 : Blo 1883435 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B26147407 : Blo 1883435 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B34863209 : Blo 1883435 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B23242139 : Blo 1883435 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B15494759 : Blo 1883435 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B10329839 : Blo 1883435 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B6886559 : Blo 1883435 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B18364157 : Blo 1883435 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B12242771 : Blo 1883435 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B8161847 : Blo 1883435 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B5441231 : Blo 1883435 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B3627487 : Blo 1883435 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B19346597 : Blo 1883435 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B12897731 : Blo 1883435 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B8598487 : Blo 1883435 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B11464649 : Blo 1883435 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B7643099 : Blo 1883435 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B5095399 : Blo 1883435 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B6793865 : Blo 1883435 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B4529243 : Blo 1883435 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B12077981 : Blo 1883435 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B8051987 : Blo 1883435 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B21471965 : Blo 1883435 21471965 := bstep (se 3 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 21471965 = 8051987) B8051987
theorem B14314643 : Blo 1883435 14314643 := bstep (se 1 (by rfl) ⟨10735982, by rfl⟩ : syracuseStep 14314643 = 21471965) B21471965
theorem B9543095 : Blo 1883435 9543095 := bstep (se 1 (by rfl) ⟨7157321, by rfl⟩ : syracuseStep 9543095 = 14314643) B14314643
theorem B6362063 : Blo 1883435 6362063 := bstep (se 1 (by rfl) ⟨4771547, by rfl⟩ : syracuseStep 6362063 = 9543095) B9543095
theorem B4241375 : Blo 1883435 4241375 := bstep (se 1 (by rfl) ⟨3181031, by rfl⟩ : syracuseStep 4241375 = 6362063) B6362063
theorem B2827583 : Blo 1883435 2827583 := bstep (se 1 (by rfl) ⟨2120687, by rfl⟩ : syracuseStep 2827583 = 4241375) B4241375
theorem B1885055 : Blo 1883435 1885055 := bstep (se 1 (by rfl) ⟨1413791, by rfl⟩ : syracuseStep 1885055 = 2827583) B2827583
theorem B2827589 : Blo 1883435 2827589 := bbase (se 4 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 2827589 = 530173) (by norm_num)
theorem B1885059 : Blo 1883435 1885059 := bstep (se 1 (by rfl) ⟨1413794, by rfl⟩ : syracuseStep 1885059 = 2827589) B2827589
theorem B3181045 : Blo 1883435 3181045 := bbase (se 5 (by rfl) ⟨149111, by rfl⟩ : syracuseStep 3181045 = 298223) (by norm_num)
theorem B4241393 : Blo 1883435 4241393 := bstep (se 2 (by rfl) ⟨1590522, by rfl⟩ : syracuseStep 4241393 = 3181045) B3181045
theorem B2827595 : Blo 1883435 2827595 := bstep (se 1 (by rfl) ⟨2120696, by rfl⟩ : syracuseStep 2827595 = 4241393) B4241393
theorem B1885063 : Blo 1883435 1885063 := bstep (se 1 (by rfl) ⟨1413797, by rfl⟩ : syracuseStep 1885063 = 2827595) B2827595
theorem B2120701 : Blo 1883435 2120701 := bbase (se 3 (by rfl) ⟨397631, by rfl⟩ : syracuseStep 2120701 = 795263) (by norm_num)
theorem B2827601 : Blo 1883435 2827601 := bstep (se 2 (by rfl) ⟨1060350, by rfl⟩ : syracuseStep 2827601 = 2120701) B2120701
theorem B1885067 : Blo 1883435 1885067 := bstep (se 1 (by rfl) ⟨1413800, by rfl⟩ : syracuseStep 1885067 = 2827601) B2827601
theorem B6362117 : Blo 1883435 6362117 := bbase (se 4 (by rfl) ⟨596448, by rfl⟩ : syracuseStep 6362117 = 1192897) (by norm_num)
theorem B4241411 : Blo 1883435 4241411 := bstep (se 1 (by rfl) ⟨3181058, by rfl⟩ : syracuseStep 4241411 = 6362117) B6362117
theorem B2827607 : Blo 1883435 2827607 := bstep (se 1 (by rfl) ⟨2120705, by rfl⟩ : syracuseStep 2827607 = 4241411) B4241411
theorem B1885071 : Blo 1883435 1885071 := bstep (se 1 (by rfl) ⟨1413803, by rfl⟩ : syracuseStep 1885071 = 2827607) B2827607
theorem B2827613 : Blo 1883435 2827613 := bbase (se 3 (by rfl) ⟨530177, by rfl⟩ : syracuseStep 2827613 = 1060355) (by norm_num)
theorem B1885075 : Blo 1883435 1885075 := bstep (se 1 (by rfl) ⟨1413806, by rfl⟩ : syracuseStep 1885075 = 2827613) B2827613
theorem B4241429 : Blo 1883435 4241429 := bbase (se 6 (by rfl) ⟨99408, by rfl⟩ : syracuseStep 4241429 = 198817) (by norm_num)
theorem B2827619 : Blo 1883435 2827619 := bstep (se 1 (by rfl) ⟨2120714, by rfl⟩ : syracuseStep 2827619 = 4241429) B4241429
theorem B1885079 : Blo 1883435 1885079 := bstep (se 1 (by rfl) ⟨1413809, by rfl⟩ : syracuseStep 1885079 = 2827619) B2827619
theorem B7157429 : Blo 1883435 7157429 := bbase (se 5 (by rfl) ⟨335504, by rfl⟩ : syracuseStep 7157429 = 671009) (by norm_num)
theorem B4771619 : Blo 1883435 4771619 := bstep (se 1 (by rfl) ⟨3578714, by rfl⟩ : syracuseStep 4771619 = 7157429) B7157429
theorem B3181079 : Blo 1883435 3181079 := bstep (se 1 (by rfl) ⟨2385809, by rfl⟩ : syracuseStep 3181079 = 4771619) B4771619
theorem B2120719 : Blo 1883435 2120719 := bstep (se 1 (by rfl) ⟨1590539, by rfl⟩ : syracuseStep 2120719 = 3181079) B3181079
theorem B2827625 : Blo 1883435 2827625 := bstep (se 2 (by rfl) ⟨1060359, by rfl⟩ : syracuseStep 2827625 = 2120719) B2120719
theorem B1885083 : Blo 1883435 1885083 := bstep (se 1 (by rfl) ⟨1413812, by rfl⟩ : syracuseStep 1885083 = 2827625) B2827625
theorem B3873757 : Blo 1883435 3873757 := bbase (se 3 (by rfl) ⟨726329, by rfl⟩ : syracuseStep 3873757 = 1452659) (by norm_num)
theorem B5165009 : Blo 1883435 5165009 := bstep (se 2 (by rfl) ⟨1936878, by rfl⟩ : syracuseStep 5165009 = 3873757) B3873757
theorem B3443339 : Blo 1883435 3443339 := bstep (se 1 (by rfl) ⟨2582504, by rfl⟩ : syracuseStep 3443339 = 5165009) B5165009
theorem B2295559 : Blo 1883435 2295559 := bstep (se 1 (by rfl) ⟨1721669, by rfl⟩ : syracuseStep 2295559 = 3443339) B3443339
theorem B12242981 : Blo 1883435 12242981 := bstep (se 4 (by rfl) ⟨1147779, by rfl⟩ : syracuseStep 12242981 = 2295559) B2295559
theorem B8161987 : Blo 1883435 8161987 := bstep (se 1 (by rfl) ⟨6121490, by rfl⟩ : syracuseStep 8161987 = 12242981) B12242981
theorem B10882649 : Blo 1883435 10882649 := bstep (se 2 (by rfl) ⟨4080993, by rfl⟩ : syracuseStep 10882649 = 8161987) B8161987
theorem B7255099 : Blo 1883435 7255099 := bstep (se 1 (by rfl) ⟨5441324, by rfl⟩ : syracuseStep 7255099 = 10882649) B10882649
theorem B38693861 : Blo 1883435 38693861 := bstep (se 4 (by rfl) ⟨3627549, by rfl⟩ : syracuseStep 38693861 = 7255099) B7255099
theorem B25795907 : Blo 1883435 25795907 := bstep (se 1 (by rfl) ⟨19346930, by rfl⟩ : syracuseStep 25795907 = 38693861) B38693861
theorem B17197271 : Blo 1883435 17197271 := bstep (se 1 (by rfl) ⟨12897953, by rfl⟩ : syracuseStep 17197271 = 25795907) B25795907
theorem B11464847 : Blo 1883435 11464847 := bstep (se 1 (by rfl) ⟨8598635, by rfl⟩ : syracuseStep 11464847 = 17197271) B17197271
theorem B7643231 : Blo 1883435 7643231 := bstep (se 1 (by rfl) ⟨5732423, by rfl⟩ : syracuseStep 7643231 = 11464847) B11464847
theorem B5095487 : Blo 1883435 5095487 := bstep (se 1 (by rfl) ⟨3821615, by rfl⟩ : syracuseStep 5095487 = 7643231) B7643231
theorem B3396991 : Blo 1883435 3396991 := bstep (se 1 (by rfl) ⟨2547743, by rfl⟩ : syracuseStep 3396991 = 5095487) B5095487
theorem B4529321 : Blo 1883435 4529321 := bstep (se 2 (by rfl) ⟨1698495, by rfl⟩ : syracuseStep 4529321 = 3396991) B3396991
theorem B3019547 : Blo 1883435 3019547 := bstep (se 1 (by rfl) ⟨2264660, by rfl⟩ : syracuseStep 3019547 = 4529321) B4529321
theorem B2013031 : Blo 1883435 2013031 := bstep (se 1 (by rfl) ⟨1509773, by rfl⟩ : syracuseStep 2013031 = 3019547) B3019547
theorem B10736165 : Blo 1883435 10736165 := bstep (se 4 (by rfl) ⟨1006515, by rfl⟩ : syracuseStep 10736165 = 2013031) B2013031
theorem B7157443 : Blo 1883435 7157443 := bstep (se 1 (by rfl) ⟨5368082, by rfl⟩ : syracuseStep 7157443 = 10736165) B10736165
theorem B9543257 : Blo 1883435 9543257 := bstep (se 2 (by rfl) ⟨3578721, by rfl⟩ : syracuseStep 9543257 = 7157443) B7157443
theorem B6362171 : Blo 1883435 6362171 := bstep (se 1 (by rfl) ⟨4771628, by rfl⟩ : syracuseStep 6362171 = 9543257) B9543257
theorem B4241447 : Blo 1883435 4241447 := bstep (se 1 (by rfl) ⟨3181085, by rfl⟩ : syracuseStep 4241447 = 6362171) B6362171
theorem B2827631 : Blo 1883435 2827631 := bstep (se 1 (by rfl) ⟨2120723, by rfl⟩ : syracuseStep 2827631 = 4241447) B4241447
theorem B1885087 : Blo 1883435 1885087 := bstep (se 1 (by rfl) ⟨1413815, by rfl⟩ : syracuseStep 1885087 = 2827631) B2827631
theorem B2827637 : Blo 1883435 2827637 := bbase (se 5 (by rfl) ⟨132545, by rfl⟩ : syracuseStep 2827637 = 265091) (by norm_num)
theorem B1885091 : Blo 1883435 1885091 := bstep (se 1 (by rfl) ⟨1413818, by rfl⟩ : syracuseStep 1885091 = 2827637) B2827637
theorem B2684053 : Blo 1883435 2684053 := bbase (se 6 (by rfl) ⟨62907, by rfl⟩ : syracuseStep 2684053 = 125815) (by norm_num)
theorem B3578737 : Blo 1883435 3578737 := bstep (se 2 (by rfl) ⟨1342026, by rfl⟩ : syracuseStep 3578737 = 2684053) B2684053
theorem B4771649 : Blo 1883435 4771649 := bstep (se 2 (by rfl) ⟨1789368, by rfl⟩ : syracuseStep 4771649 = 3578737) B3578737
theorem B3181099 : Blo 1883435 3181099 := bstep (se 1 (by rfl) ⟨2385824, by rfl⟩ : syracuseStep 3181099 = 4771649) B4771649
theorem B4241465 : Blo 1883435 4241465 := bstep (se 2 (by rfl) ⟨1590549, by rfl⟩ : syracuseStep 4241465 = 3181099) B3181099
theorem B2827643 : Blo 1883435 2827643 := bstep (se 1 (by rfl) ⟨2120732, by rfl⟩ : syracuseStep 2827643 = 4241465) B4241465
theorem B1885095 : Blo 1883435 1885095 := bstep (se 1 (by rfl) ⟨1413821, by rfl⟩ : syracuseStep 1885095 = 2827643) B2827643
theorem B2120737 : Blo 1883435 2120737 := bbase (se 2 (by rfl) ⟨795276, by rfl⟩ : syracuseStep 2120737 = 1590553) (by norm_num)
theorem B2827649 : Blo 1883435 2827649 := bstep (se 2 (by rfl) ⟨1060368, by rfl⟩ : syracuseStep 2827649 = 2120737) B2120737
theorem B1885099 : Blo 1883435 1885099 := bstep (se 1 (by rfl) ⟨1413824, by rfl⟩ : syracuseStep 1885099 = 2827649) B2827649
theorem B4771669 : Blo 1883435 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B6362225 : Blo 1883435 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B4241483 : Blo 1883435 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B2827655 : Blo 1883435 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B1885103 : Blo 1883435 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B2827661 : Blo 1883435 2827661 := bbase (se 3 (by rfl) ⟨530186, by rfl⟩ : syracuseStep 2827661 = 1060373) (by norm_num)
theorem B1885107 : Blo 1883435 1885107 := bstep (se 1 (by rfl) ⟨1413830, by rfl⟩ : syracuseStep 1885107 = 2827661) B2827661
theorem B4241501 : Blo 1883435 4241501 := bbase (se 3 (by rfl) ⟨795281, by rfl⟩ : syracuseStep 4241501 = 1590563) (by norm_num)
theorem B2827667 : Blo 1883435 2827667 := bstep (se 1 (by rfl) ⟨2120750, by rfl⟩ : syracuseStep 2827667 = 4241501) B4241501
theorem B1885111 : Blo 1883435 1885111 := bstep (se 1 (by rfl) ⟨1413833, by rfl⟩ : syracuseStep 1885111 = 2827667) B2827667
theorem B3181133 : Blo 1883435 3181133 := bbase (se 3 (by rfl) ⟨596462, by rfl⟩ : syracuseStep 3181133 = 1192925) (by norm_num)
theorem B2120755 : Blo 1883435 2120755 := bstep (se 1 (by rfl) ⟨1590566, by rfl⟩ : syracuseStep 2120755 = 3181133) B3181133
theorem B2827673 : Blo 1883435 2827673 := bstep (se 2 (by rfl) ⟨1060377, by rfl⟩ : syracuseStep 2827673 = 2120755) B2120755
theorem B1885115 : Blo 1883435 1885115 := bstep (se 1 (by rfl) ⟨1413836, by rfl⟩ : syracuseStep 1885115 = 2827673) B2827673
theorem B4081061 : Blo 1883435 4081061 := bbase (se 4 (by rfl) ⟨382599, by rfl⟩ : syracuseStep 4081061 = 765199) (by norm_num)
theorem B10882829 : Blo 1883435 10882829 := bstep (se 3 (by rfl) ⟨2040530, by rfl⟩ : syracuseStep 10882829 = 4081061) B4081061
theorem B7255219 : Blo 1883435 7255219 := bstep (se 1 (by rfl) ⟨5441414, by rfl⟩ : syracuseStep 7255219 = 10882829) B10882829
theorem B9673625 : Blo 1883435 9673625 := bstep (se 2 (by rfl) ⟨3627609, by rfl⟩ : syracuseStep 9673625 = 7255219) B7255219
theorem B25796333 : Blo 1883435 25796333 := bstep (se 3 (by rfl) ⟨4836812, by rfl⟩ : syracuseStep 25796333 = 9673625) B9673625
theorem B17197555 : Blo 1883435 17197555 := bstep (se 1 (by rfl) ⟨12898166, by rfl⟩ : syracuseStep 17197555 = 25796333) B25796333
theorem B22930073 : Blo 1883435 22930073 := bstep (se 2 (by rfl) ⟨8598777, by rfl⟩ : syracuseStep 22930073 = 17197555) B17197555
theorem B15286715 : Blo 1883435 15286715 := bstep (se 1 (by rfl) ⟨11465036, by rfl⟩ : syracuseStep 15286715 = 22930073) B22930073
theorem B10191143 : Blo 1883435 10191143 := bstep (se 1 (by rfl) ⟨7643357, by rfl⟩ : syracuseStep 10191143 = 15286715) B15286715
theorem B27176381 : Blo 1883435 27176381 := bstep (se 3 (by rfl) ⟨5095571, by rfl⟩ : syracuseStep 27176381 = 10191143) B10191143
theorem B18117587 : Blo 1883435 18117587 := bstep (se 1 (by rfl) ⟨13588190, by rfl⟩ : syracuseStep 18117587 = 27176381) B27176381
theorem B12078391 : Blo 1883435 12078391 := bstep (se 1 (by rfl) ⟨9058793, by rfl⟩ : syracuseStep 12078391 = 18117587) B18117587
theorem B16104521 : Blo 1883435 16104521 := bstep (se 2 (by rfl) ⟨6039195, by rfl⟩ : syracuseStep 16104521 = 12078391) B12078391
theorem B10736347 : Blo 1883435 10736347 := bstep (se 1 (by rfl) ⟨8052260, by rfl⟩ : syracuseStep 10736347 = 16104521) B16104521
theorem B14315129 : Blo 1883435 14315129 := bstep (se 2 (by rfl) ⟨5368173, by rfl⟩ : syracuseStep 14315129 = 10736347) B10736347
theorem B9543419 : Blo 1883435 9543419 := bstep (se 1 (by rfl) ⟨7157564, by rfl⟩ : syracuseStep 9543419 = 14315129) B14315129
theorem B6362279 : Blo 1883435 6362279 := bstep (se 1 (by rfl) ⟨4771709, by rfl⟩ : syracuseStep 6362279 = 9543419) B9543419
theorem B4241519 : Blo 1883435 4241519 := bstep (se 1 (by rfl) ⟨3181139, by rfl⟩ : syracuseStep 4241519 = 6362279) B6362279
theorem B2827679 : Blo 1883435 2827679 := bstep (se 1 (by rfl) ⟨2120759, by rfl⟩ : syracuseStep 2827679 = 4241519) B4241519
theorem B1885119 : Blo 1883435 1885119 := bstep (se 1 (by rfl) ⟨1413839, by rfl⟩ : syracuseStep 1885119 = 2827679) B2827679
theorem B2827685 : Blo 1883435 2827685 := bbase (se 4 (by rfl) ⟨265095, by rfl⟩ : syracuseStep 2827685 = 530191) (by norm_num)
theorem B1885123 : Blo 1883435 1885123 := bstep (se 1 (by rfl) ⟨1413842, by rfl⟩ : syracuseStep 1885123 = 2827685) B2827685
theorem B2385865 : Blo 1883435 2385865 := bbase (se 2 (by rfl) ⟨894699, by rfl⟩ : syracuseStep 2385865 = 1789399) (by norm_num)
theorem B3181153 : Blo 1883435 3181153 := bstep (se 2 (by rfl) ⟨1192932, by rfl⟩ : syracuseStep 3181153 = 2385865) B2385865
theorem B4241537 : Blo 1883435 4241537 := bstep (se 2 (by rfl) ⟨1590576, by rfl⟩ : syracuseStep 4241537 = 3181153) B3181153
theorem B2827691 : Blo 1883435 2827691 := bstep (se 1 (by rfl) ⟨2120768, by rfl⟩ : syracuseStep 2827691 = 4241537) B4241537
theorem B1885127 : Blo 1883435 1885127 := bstep (se 1 (by rfl) ⟨1413845, by rfl⟩ : syracuseStep 1885127 = 2827691) B2827691
theorem B2120773 : Blo 1883435 2120773 := bbase (se 4 (by rfl) ⟨198822, by rfl⟩ : syracuseStep 2120773 = 397645) (by norm_num)
theorem B2827697 : Blo 1883435 2827697 := bstep (se 2 (by rfl) ⟨1060386, by rfl⟩ : syracuseStep 2827697 = 2120773) B2120773
theorem B1885131 : Blo 1883435 1885131 := bstep (se 1 (by rfl) ⟨1413848, by rfl⟩ : syracuseStep 1885131 = 2827697) B2827697
theorem B3578813 : Blo 1883435 3578813 := bbase (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) (by norm_num)
theorem B2385875 : Blo 1883435 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B6362333 : Blo 1883435 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B4241555 : Blo 1883435 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B2827703 : Blo 1883435 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B1885135 : Blo 1883435 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B2827709 : Blo 1883435 2827709 := bbase (se 3 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 2827709 = 1060391) (by norm_num)
theorem B1885139 : Blo 1883435 1885139 := bstep (se 1 (by rfl) ⟨1413854, by rfl⟩ : syracuseStep 1885139 = 2827709) B2827709
theorem B4241573 : Blo 1883435 4241573 := bbase (se 4 (by rfl) ⟨397647, by rfl⟩ : syracuseStep 4241573 = 795295) (by norm_num)
theorem B2827715 : Blo 1883435 2827715 := bstep (se 1 (by rfl) ⟨2120786, by rfl⟩ : syracuseStep 2827715 = 4241573) B4241573
theorem B1885143 : Blo 1883435 1885143 := bstep (se 1 (by rfl) ⟨1413857, by rfl⟩ : syracuseStep 1885143 = 2827715) B2827715
theorem B4771781 : Blo 1883435 4771781 := bbase (se 4 (by rfl) ⟨447354, by rfl⟩ : syracuseStep 4771781 = 894709) (by norm_num)
theorem B3181187 : Blo 1883435 3181187 := bstep (se 1 (by rfl) ⟨2385890, by rfl⟩ : syracuseStep 3181187 = 4771781) B4771781
theorem B2120791 : Blo 1883435 2120791 := bstep (se 1 (by rfl) ⟨1590593, by rfl⟩ : syracuseStep 2120791 = 3181187) B3181187
theorem B2827721 : Blo 1883435 2827721 := bstep (se 2 (by rfl) ⟨1060395, by rfl⟩ : syracuseStep 2827721 = 2120791) B2120791
theorem B1885147 : Blo 1883435 1885147 := bstep (se 1 (by rfl) ⟨1413860, by rfl⟩ : syracuseStep 1885147 = 2827721) B2827721
theorem B9058949 : Blo 1883435 9058949 := bbase (se 4 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 9058949 = 1698553) (by norm_num)
theorem B6039299 : Blo 1883435 6039299 := bstep (se 1 (by rfl) ⟨4529474, by rfl⟩ : syracuseStep 6039299 = 9058949) B9058949
theorem B4026199 : Blo 1883435 4026199 := bstep (se 1 (by rfl) ⟨3019649, by rfl⟩ : syracuseStep 4026199 = 6039299) B6039299
theorem B5368265 : Blo 1883435 5368265 := bstep (se 2 (by rfl) ⟨2013099, by rfl⟩ : syracuseStep 5368265 = 4026199) B4026199
theorem B3578843 : Blo 1883435 3578843 := bstep (se 1 (by rfl) ⟨2684132, by rfl⟩ : syracuseStep 3578843 = 5368265) B5368265
theorem B9543581 : Blo 1883435 9543581 := bstep (se 3 (by rfl) ⟨1789421, by rfl⟩ : syracuseStep 9543581 = 3578843) B3578843
theorem B6362387 : Blo 1883435 6362387 := bstep (se 1 (by rfl) ⟨4771790, by rfl⟩ : syracuseStep 6362387 = 9543581) B9543581
theorem B4241591 : Blo 1883435 4241591 := bstep (se 1 (by rfl) ⟨3181193, by rfl⟩ : syracuseStep 4241591 = 6362387) B6362387
theorem B2827727 : Blo 1883435 2827727 := bstep (se 1 (by rfl) ⟨2120795, by rfl⟩ : syracuseStep 2827727 = 4241591) B4241591
theorem B1885151 : Blo 1883435 1885151 := bstep (se 1 (by rfl) ⟨1413863, by rfl⟩ : syracuseStep 1885151 = 2827727) B2827727
theorem B2827733 : Blo 1883435 2827733 := bbase (se 7 (by rfl) ⟨33137, by rfl⟩ : syracuseStep 2827733 = 66275) (by norm_num)
theorem B1885155 : Blo 1883435 1885155 := bstep (se 1 (by rfl) ⟨1413866, by rfl⟩ : syracuseStep 1885155 = 2827733) B2827733
theorem B7157717 : Blo 1883435 7157717 := bbase (se 7 (by rfl) ⟨83879, by rfl⟩ : syracuseStep 7157717 = 167759) (by norm_num)
theorem B4771811 : Blo 1883435 4771811 := bstep (se 1 (by rfl) ⟨3578858, by rfl⟩ : syracuseStep 4771811 = 7157717) B7157717
theorem B3181207 : Blo 1883435 3181207 := bstep (se 1 (by rfl) ⟨2385905, by rfl⟩ : syracuseStep 3181207 = 4771811) B4771811
theorem B4241609 : Blo 1883435 4241609 := bstep (se 2 (by rfl) ⟨1590603, by rfl⟩ : syracuseStep 4241609 = 3181207) B3181207
theorem B2827739 : Blo 1883435 2827739 := bstep (se 1 (by rfl) ⟨2120804, by rfl⟩ : syracuseStep 2827739 = 4241609) B4241609
theorem B1885159 : Blo 1883435 1885159 := bstep (se 1 (by rfl) ⟨1413869, by rfl⟩ : syracuseStep 1885159 = 2827739) B2827739
theorem B2120809 : Blo 1883435 2120809 := bbase (se 2 (by rfl) ⟨795303, by rfl⟩ : syracuseStep 2120809 = 1590607) (by norm_num)
theorem B2827745 : Blo 1883435 2827745 := bstep (se 2 (by rfl) ⟨1060404, by rfl⟩ : syracuseStep 2827745 = 2120809) B2120809
theorem B1885163 : Blo 1883435 1885163 := bstep (se 1 (by rfl) ⟨1413872, by rfl⟩ : syracuseStep 1885163 = 2827745) B2827745
theorem B11465333 : Blo 1883435 11465333 := bbase (se 5 (by rfl) ⟨537437, by rfl⟩ : syracuseStep 11465333 = 1074875) (by norm_num)
theorem B7643555 : Blo 1883435 7643555 := bstep (se 1 (by rfl) ⟨5732666, by rfl⟩ : syracuseStep 7643555 = 11465333) B11465333
theorem B5095703 : Blo 1883435 5095703 := bstep (se 1 (by rfl) ⟨3821777, by rfl⟩ : syracuseStep 5095703 = 7643555) B7643555
theorem B3397135 : Blo 1883435 3397135 := bstep (se 1 (by rfl) ⟨2547851, by rfl⟩ : syracuseStep 3397135 = 5095703) B5095703
theorem B4529513 : Blo 1883435 4529513 := bstep (se 2 (by rfl) ⟨1698567, by rfl⟩ : syracuseStep 4529513 = 3397135) B3397135
theorem B3019675 : Blo 1883435 3019675 := bstep (se 1 (by rfl) ⟨2264756, by rfl⟩ : syracuseStep 3019675 = 4529513) B4529513
theorem B4026233 : Blo 1883435 4026233 := bstep (se 2 (by rfl) ⟨1509837, by rfl⟩ : syracuseStep 4026233 = 3019675) B3019675
theorem B10736621 : Blo 1883435 10736621 := bstep (se 3 (by rfl) ⟨2013116, by rfl⟩ : syracuseStep 10736621 = 4026233) B4026233
theorem B7157747 : Blo 1883435 7157747 := bstep (se 1 (by rfl) ⟨5368310, by rfl⟩ : syracuseStep 7157747 = 10736621) B10736621
theorem B4771831 : Blo 1883435 4771831 := bstep (se 1 (by rfl) ⟨3578873, by rfl⟩ : syracuseStep 4771831 = 7157747) B7157747
theorem B6362441 : Blo 1883435 6362441 := bstep (se 2 (by rfl) ⟨2385915, by rfl⟩ : syracuseStep 6362441 = 4771831) B4771831
theorem B4241627 : Blo 1883435 4241627 := bstep (se 1 (by rfl) ⟨3181220, by rfl⟩ : syracuseStep 4241627 = 6362441) B6362441
theorem B2827751 : Blo 1883435 2827751 := bstep (se 1 (by rfl) ⟨2120813, by rfl⟩ : syracuseStep 2827751 = 4241627) B4241627
theorem B1885167 : Blo 1883435 1885167 := bstep (se 1 (by rfl) ⟨1413875, by rfl⟩ : syracuseStep 1885167 = 2827751) B2827751
theorem B2827757 : Blo 1883435 2827757 := bbase (se 3 (by rfl) ⟨530204, by rfl⟩ : syracuseStep 2827757 = 1060409) (by norm_num)
theorem B1885171 : Blo 1883435 1885171 := bstep (se 1 (by rfl) ⟨1413878, by rfl⟩ : syracuseStep 1885171 = 2827757) B2827757
theorem B4241645 : Blo 1883435 4241645 := bbase (se 3 (by rfl) ⟨795308, by rfl⟩ : syracuseStep 4241645 = 1590617) (by norm_num)
theorem B2827763 : Blo 1883435 2827763 := bstep (se 1 (by rfl) ⟨2120822, by rfl⟩ : syracuseStep 2827763 = 4241645) B4241645
theorem B1885175 : Blo 1883435 1885175 := bstep (se 1 (by rfl) ⟨1413881, by rfl⟩ : syracuseStep 1885175 = 2827763) B2827763
theorem B2684173 : Blo 1883435 2684173 := bbase (se 3 (by rfl) ⟨503282, by rfl⟩ : syracuseStep 2684173 = 1006565) (by norm_num)
theorem B3578897 : Blo 1883435 3578897 := bstep (se 2 (by rfl) ⟨1342086, by rfl⟩ : syracuseStep 3578897 = 2684173) B2684173
theorem B2385931 : Blo 1883435 2385931 := bstep (se 1 (by rfl) ⟨1789448, by rfl⟩ : syracuseStep 2385931 = 3578897) B3578897
theorem B3181241 : Blo 1883435 3181241 := bstep (se 2 (by rfl) ⟨1192965, by rfl⟩ : syracuseStep 3181241 = 2385931) B2385931
theorem B2120827 : Blo 1883435 2120827 := bstep (se 1 (by rfl) ⟨1590620, by rfl⟩ : syracuseStep 2120827 = 3181241) B3181241
theorem B2827769 : Blo 1883435 2827769 := bstep (se 2 (by rfl) ⟨1060413, by rfl⟩ : syracuseStep 2827769 = 2120827) B2120827
theorem B1885179 : Blo 1883435 1885179 := bstep (se 1 (by rfl) ⟨1413884, by rfl⟩ : syracuseStep 1885179 = 2827769) B2827769
theorem B3627733 : Blo 1883435 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B4836977 : Blo 1883435 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B3224651 : Blo 1883435 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B8599069 : Blo 1883435 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B11465425 : Blo 1883435 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B15287233 : Blo 1883435 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B20382977 : Blo 1883435 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B13588651 : Blo 1883435 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B72472805 : Blo 1883435 72472805 := bstep (se 4 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 72472805 = 13588651) B13588651
theorem B48315203 : Blo 1883435 48315203 := bstep (se 1 (by rfl) ⟨36236402, by rfl⟩ : syracuseStep 48315203 = 72472805) B72472805
theorem B32210135 : Blo 1883435 32210135 := bstep (se 1 (by rfl) ⟨24157601, by rfl⟩ : syracuseStep 32210135 = 48315203) B48315203
theorem B21473423 : Blo 1883435 21473423 := bstep (se 1 (by rfl) ⟨16105067, by rfl⟩ : syracuseStep 21473423 = 32210135) B32210135
theorem B14315615 : Blo 1883435 14315615 := bstep (se 1 (by rfl) ⟨10736711, by rfl⟩ : syracuseStep 14315615 = 21473423) B21473423
theorem B9543743 : Blo 1883435 9543743 := bstep (se 1 (by rfl) ⟨7157807, by rfl⟩ : syracuseStep 9543743 = 14315615) B14315615
theorem B6362495 : Blo 1883435 6362495 := bstep (se 1 (by rfl) ⟨4771871, by rfl⟩ : syracuseStep 6362495 = 9543743) B9543743
theorem B4241663 : Blo 1883435 4241663 := bstep (se 1 (by rfl) ⟨3181247, by rfl⟩ : syracuseStep 4241663 = 6362495) B6362495
theorem B2827775 : Blo 1883435 2827775 := bstep (se 1 (by rfl) ⟨2120831, by rfl⟩ : syracuseStep 2827775 = 4241663) B4241663
theorem B1885183 : Blo 1883435 1885183 := bstep (se 1 (by rfl) ⟨1413887, by rfl⟩ : syracuseStep 1885183 = 2827775) B2827775
theorem B2827781 : Blo 1883435 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B1885187 : Blo 1883435 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B3181261 : Blo 1883435 3181261 := bbase (se 3 (by rfl) ⟨596486, by rfl⟩ : syracuseStep 3181261 = 1192973) (by norm_num)
theorem B4241681 : Blo 1883435 4241681 := bstep (se 2 (by rfl) ⟨1590630, by rfl⟩ : syracuseStep 4241681 = 3181261) B3181261
theorem B2827787 : Blo 1883435 2827787 := bstep (se 1 (by rfl) ⟨2120840, by rfl⟩ : syracuseStep 2827787 = 4241681) B4241681
theorem B1885191 : Blo 1883435 1885191 := bstep (se 1 (by rfl) ⟨1413893, by rfl⟩ : syracuseStep 1885191 = 2827787) B2827787
theorem B2120845 : Blo 1883435 2120845 := bbase (se 3 (by rfl) ⟨397658, by rfl⟩ : syracuseStep 2120845 = 795317) (by norm_num)
theorem B2827793 : Blo 1883435 2827793 := bstep (se 2 (by rfl) ⟨1060422, by rfl⟩ : syracuseStep 2827793 = 2120845) B2120845
theorem B1885195 : Blo 1883435 1885195 := bstep (se 1 (by rfl) ⟨1413896, by rfl⟩ : syracuseStep 1885195 = 2827793) B2827793
theorem B6362549 : Blo 1883435 6362549 := bbase (se 5 (by rfl) ⟨298244, by rfl⟩ : syracuseStep 6362549 = 596489) (by norm_num)
theorem B4241699 : Blo 1883435 4241699 := bstep (se 1 (by rfl) ⟨3181274, by rfl⟩ : syracuseStep 4241699 = 6362549) B6362549
theorem B2827799 : Blo 1883435 2827799 := bstep (se 1 (by rfl) ⟨2120849, by rfl⟩ : syracuseStep 2827799 = 4241699) B4241699
theorem B1885199 : Blo 1883435 1885199 := bstep (se 1 (by rfl) ⟨1413899, by rfl⟩ : syracuseStep 1885199 = 2827799) B2827799
theorem B2827805 : Blo 1883435 2827805 := bbase (se 3 (by rfl) ⟨530213, by rfl⟩ : syracuseStep 2827805 = 1060427) (by norm_num)
theorem B1885203 : Blo 1883435 1885203 := bstep (se 1 (by rfl) ⟨1413902, by rfl⟩ : syracuseStep 1885203 = 2827805) B2827805
theorem B4241717 : Blo 1883435 4241717 := bbase (se 5 (by rfl) ⟨198830, by rfl⟩ : syracuseStep 4241717 = 397661) (by norm_num)
theorem B2827811 : Blo 1883435 2827811 := bstep (se 1 (by rfl) ⟨2120858, by rfl⟩ : syracuseStep 2827811 = 4241717) B4241717
theorem B1885207 : Blo 1883435 1885207 := bstep (se 1 (by rfl) ⟨1413905, by rfl⟩ : syracuseStep 1885207 = 2827811) B2827811
theorem B1910933 : Blo 1883435 1910933 := bbase (se 6 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 1910933 = 89575) (by norm_num)
theorem B20383285 : Blo 1883435 20383285 := bstep (se 5 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 20383285 = 1910933) B1910933
theorem B27177713 : Blo 1883435 27177713 := bstep (se 2 (by rfl) ⟨10191642, by rfl⟩ : syracuseStep 27177713 = 20383285) B20383285
theorem B18118475 : Blo 1883435 18118475 := bstep (se 1 (by rfl) ⟨13588856, by rfl⟩ : syracuseStep 18118475 = 27177713) B27177713
theorem B12078983 : Blo 1883435 12078983 := bstep (se 1 (by rfl) ⟨9059237, by rfl⟩ : syracuseStep 12078983 = 18118475) B18118475
theorem B8052655 : Blo 1883435 8052655 := bstep (se 1 (by rfl) ⟨6039491, by rfl⟩ : syracuseStep 8052655 = 12078983) B12078983
theorem B10736873 : Blo 1883435 10736873 := bstep (se 2 (by rfl) ⟨4026327, by rfl⟩ : syracuseStep 10736873 = 8052655) B8052655
theorem B7157915 : Blo 1883435 7157915 := bstep (se 1 (by rfl) ⟨5368436, by rfl⟩ : syracuseStep 7157915 = 10736873) B10736873
theorem B4771943 : Blo 1883435 4771943 := bstep (se 1 (by rfl) ⟨3578957, by rfl⟩ : syracuseStep 4771943 = 7157915) B7157915
theorem B3181295 : Blo 1883435 3181295 := bstep (se 1 (by rfl) ⟨2385971, by rfl⟩ : syracuseStep 3181295 = 4771943) B4771943
theorem B2120863 : Blo 1883435 2120863 := bstep (se 1 (by rfl) ⟨1590647, by rfl⟩ : syracuseStep 2120863 = 3181295) B3181295
theorem B2827817 : Blo 1883435 2827817 := bstep (se 2 (by rfl) ⟨1060431, by rfl⟩ : syracuseStep 2827817 = 2120863) B2120863
theorem B1885211 : Blo 1883435 1885211 := bstep (se 1 (by rfl) ⟨1413908, by rfl⟩ : syracuseStep 1885211 = 2827817) B2827817
theorem B3538181 : Blo 1883435 3538181 := bbase (se 4 (by rfl) ⟨331704, by rfl⟩ : syracuseStep 3538181 = 663409) (by norm_num)
theorem B2358787 : Blo 1883435 2358787 := bstep (se 1 (by rfl) ⟨1769090, by rfl⟩ : syracuseStep 2358787 = 3538181) B3538181
theorem B3145049 : Blo 1883435 3145049 := bstep (se 2 (by rfl) ⟨1179393, by rfl⟩ : syracuseStep 3145049 = 2358787) B2358787
theorem B2096699 : Blo 1883435 2096699 := bstep (se 1 (by rfl) ⟨1572524, by rfl⟩ : syracuseStep 2096699 = 3145049) B3145049
theorem B5591197 : Blo 1883435 5591197 := bstep (se 3 (by rfl) ⟨1048349, by rfl⟩ : syracuseStep 5591197 = 2096699) B2096699
theorem B7454929 : Blo 1883435 7454929 := bstep (se 2 (by rfl) ⟨2795598, by rfl⟩ : syracuseStep 7454929 = 5591197) B5591197
theorem B9939905 : Blo 1883435 9939905 := bstep (se 2 (by rfl) ⟨3727464, by rfl⟩ : syracuseStep 9939905 = 7454929) B7454929
theorem B6626603 : Blo 1883435 6626603 := bstep (se 1 (by rfl) ⟨4969952, by rfl⟩ : syracuseStep 6626603 = 9939905) B9939905
theorem B4417735 : Blo 1883435 4417735 := bstep (se 1 (by rfl) ⟨3313301, by rfl⟩ : syracuseStep 4417735 = 6626603) B6626603
theorem B5890313 : Blo 1883435 5890313 := bstep (se 2 (by rfl) ⟨2208867, by rfl⟩ : syracuseStep 5890313 = 4417735) B4417735
theorem B3926875 : Blo 1883435 3926875 := bstep (se 1 (by rfl) ⟨2945156, by rfl⟩ : syracuseStep 3926875 = 5890313) B5890313
theorem B5235833 : Blo 1883435 5235833 := bstep (se 2 (by rfl) ⟨1963437, by rfl⟩ : syracuseStep 5235833 = 3926875) B3926875
theorem B3490555 : Blo 1883435 3490555 := bstep (se 1 (by rfl) ⟨2617916, by rfl⟩ : syracuseStep 3490555 = 5235833) B5235833
theorem B4654073 : Blo 1883435 4654073 := bstep (se 2 (by rfl) ⟨1745277, by rfl⟩ : syracuseStep 4654073 = 3490555) B3490555
theorem B3102715 : Blo 1883435 3102715 := bstep (se 1 (by rfl) ⟨2327036, by rfl⟩ : syracuseStep 3102715 = 4654073) B4654073
theorem B16547813 : Blo 1883435 16547813 := bstep (se 4 (by rfl) ⟨1551357, by rfl⟩ : syracuseStep 16547813 = 3102715) B3102715
theorem B11031875 : Blo 1883435 11031875 := bstep (se 1 (by rfl) ⟨8273906, by rfl⟩ : syracuseStep 11031875 = 16547813) B16547813
theorem B7354583 : Blo 1883435 7354583 := bstep (se 1 (by rfl) ⟨5515937, by rfl⟩ : syracuseStep 7354583 = 11031875) B11031875
theorem B4903055 : Blo 1883435 4903055 := bstep (se 1 (by rfl) ⟨3677291, by rfl⟩ : syracuseStep 4903055 = 7354583) B7354583
theorem B3268703 : Blo 1883435 3268703 := bstep (se 1 (by rfl) ⟨2451527, by rfl⟩ : syracuseStep 3268703 = 4903055) B4903055
theorem B2179135 : Blo 1883435 2179135 := bstep (se 1 (by rfl) ⟨1634351, by rfl⟩ : syracuseStep 2179135 = 3268703) B3268703
theorem B2905513 : Blo 1883435 2905513 := bstep (se 2 (by rfl) ⟨1089567, by rfl⟩ : syracuseStep 2905513 = 2179135) B2179135
theorem B15496069 : Blo 1883435 15496069 := bstep (se 4 (by rfl) ⟨1452756, by rfl⟩ : syracuseStep 15496069 = 2905513) B2905513
theorem B20661425 : Blo 1883435 20661425 := bstep (se 2 (by rfl) ⟨7748034, by rfl⟩ : syracuseStep 20661425 = 15496069) B15496069
theorem B13774283 : Blo 1883435 13774283 := bstep (se 1 (by rfl) ⟨10330712, by rfl⟩ : syracuseStep 13774283 = 20661425) B20661425
theorem B9182855 : Blo 1883435 9182855 := bstep (se 1 (by rfl) ⟨6887141, by rfl⟩ : syracuseStep 9182855 = 13774283) B13774283
theorem B6121903 : Blo 1883435 6121903 := bstep (se 1 (by rfl) ⟨4591427, by rfl⟩ : syracuseStep 6121903 = 9182855) B9182855
theorem B8162537 : Blo 1883435 8162537 := bstep (se 2 (by rfl) ⟨3060951, by rfl⟩ : syracuseStep 8162537 = 6121903) B6121903
theorem B87067061 : Blo 1883435 87067061 := bstep (se 5 (by rfl) ⟨4081268, by rfl⟩ : syracuseStep 87067061 = 8162537) B8162537
theorem B58044707 : Blo 1883435 58044707 := bstep (se 1 (by rfl) ⟨43533530, by rfl⟩ : syracuseStep 58044707 = 87067061) B87067061
theorem B38696471 : Blo 1883435 38696471 := bstep (se 1 (by rfl) ⟨29022353, by rfl⟩ : syracuseStep 38696471 = 58044707) B58044707
theorem B25797647 : Blo 1883435 25797647 := bstep (se 1 (by rfl) ⟨19348235, by rfl⟩ : syracuseStep 25797647 = 38696471) B38696471
theorem B68793725 : Blo 1883435 68793725 := bstep (se 3 (by rfl) ⟨12898823, by rfl⟩ : syracuseStep 68793725 = 25797647) B25797647
theorem B45862483 : Blo 1883435 45862483 := bstep (se 1 (by rfl) ⟨34396862, by rfl⟩ : syracuseStep 45862483 = 68793725) B68793725
theorem B61149977 : Blo 1883435 61149977 := bstep (se 2 (by rfl) ⟨22931241, by rfl⟩ : syracuseStep 61149977 = 45862483) B45862483
theorem B40766651 : Blo 1883435 40766651 := bstep (se 1 (by rfl) ⟨30574988, by rfl⟩ : syracuseStep 40766651 = 61149977) B61149977
theorem B27177767 : Blo 1883435 27177767 := bstep (se 1 (by rfl) ⟨20383325, by rfl⟩ : syracuseStep 27177767 = 40766651) B40766651
theorem B18118511 : Blo 1883435 18118511 := bstep (se 1 (by rfl) ⟨13588883, by rfl⟩ : syracuseStep 18118511 = 27177767) B27177767
theorem B12079007 : Blo 1883435 12079007 := bstep (se 1 (by rfl) ⟨9059255, by rfl⟩ : syracuseStep 12079007 = 18118511) B18118511
theorem B8052671 : Blo 1883435 8052671 := bstep (se 1 (by rfl) ⟨6039503, by rfl⟩ : syracuseStep 8052671 = 12079007) B12079007
theorem B5368447 : Blo 1883435 5368447 := bstep (se 1 (by rfl) ⟨4026335, by rfl⟩ : syracuseStep 5368447 = 8052671) B8052671
theorem B7157929 : Blo 1883435 7157929 := bstep (se 2 (by rfl) ⟨2684223, by rfl⟩ : syracuseStep 7157929 = 5368447) B5368447
theorem B9543905 : Blo 1883435 9543905 := bstep (se 2 (by rfl) ⟨3578964, by rfl⟩ : syracuseStep 9543905 = 7157929) B7157929
theorem B6362603 : Blo 1883435 6362603 := bstep (se 1 (by rfl) ⟨4771952, by rfl⟩ : syracuseStep 6362603 = 9543905) B9543905
theorem B4241735 : Blo 1883435 4241735 := bstep (se 1 (by rfl) ⟨3181301, by rfl⟩ : syracuseStep 4241735 = 6362603) B6362603
theorem B2827823 : Blo 1883435 2827823 := bstep (se 1 (by rfl) ⟨2120867, by rfl⟩ : syracuseStep 2827823 = 4241735) B4241735
theorem B1885215 : Blo 1883435 1885215 := bstep (se 1 (by rfl) ⟨1413911, by rfl⟩ : syracuseStep 1885215 = 2827823) B2827823
theorem B2827829 : Blo 1883435 2827829 := bbase (se 5 (by rfl) ⟨132554, by rfl⟩ : syracuseStep 2827829 = 265109) (by norm_num)
theorem B1885219 : Blo 1883435 1885219 := bstep (se 1 (by rfl) ⟨1413914, by rfl⟩ : syracuseStep 1885219 = 2827829) B2827829
theorem B4771973 : Blo 1883435 4771973 := bbase (se 4 (by rfl) ⟨447372, by rfl⟩ : syracuseStep 4771973 = 894745) (by norm_num)
theorem B3181315 : Blo 1883435 3181315 := bstep (se 1 (by rfl) ⟨2385986, by rfl⟩ : syracuseStep 3181315 = 4771973) B4771973
theorem B4241753 : Blo 1883435 4241753 := bstep (se 2 (by rfl) ⟨1590657, by rfl⟩ : syracuseStep 4241753 = 3181315) B3181315
theorem B2827835 : Blo 1883435 2827835 := bstep (se 1 (by rfl) ⟨2120876, by rfl⟩ : syracuseStep 2827835 = 4241753) B4241753
theorem B1885223 : Blo 1883435 1885223 := bstep (se 1 (by rfl) ⟨1413917, by rfl⟩ : syracuseStep 1885223 = 2827835) B2827835
theorem B2120881 : Blo 1883435 2120881 := bbase (se 2 (by rfl) ⟨795330, by rfl⟩ : syracuseStep 2120881 = 1590661) (by norm_num)
theorem B2827841 : Blo 1883435 2827841 := bstep (se 2 (by rfl) ⟨1060440, by rfl⟩ : syracuseStep 2827841 = 2120881) B2120881
theorem B1885227 : Blo 1883435 1885227 := bstep (se 1 (by rfl) ⟨1413920, by rfl⟩ : syracuseStep 1885227 = 2827841) B2827841
theorem B2013185 : Blo 1883435 2013185 := bbase (se 2 (by rfl) ⟨754944, by rfl⟩ : syracuseStep 2013185 = 1509889) (by norm_num)
theorem B5368493 : Blo 1883435 5368493 := bstep (se 3 (by rfl) ⟨1006592, by rfl⟩ : syracuseStep 5368493 = 2013185) B2013185
theorem B3578995 : Blo 1883435 3578995 := bstep (se 1 (by rfl) ⟨2684246, by rfl⟩ : syracuseStep 3578995 = 5368493) B5368493
theorem B4771993 : Blo 1883435 4771993 := bstep (se 2 (by rfl) ⟨1789497, by rfl⟩ : syracuseStep 4771993 = 3578995) B3578995
theorem B6362657 : Blo 1883435 6362657 := bstep (se 2 (by rfl) ⟨2385996, by rfl⟩ : syracuseStep 6362657 = 4771993) B4771993
theorem B4241771 : Blo 1883435 4241771 := bstep (se 1 (by rfl) ⟨3181328, by rfl⟩ : syracuseStep 4241771 = 6362657) B6362657
theorem B2827847 : Blo 1883435 2827847 := bstep (se 1 (by rfl) ⟨2120885, by rfl⟩ : syracuseStep 2827847 = 4241771) B4241771
theorem B1885231 : Blo 1883435 1885231 := bstep (se 1 (by rfl) ⟨1413923, by rfl⟩ : syracuseStep 1885231 = 2827847) B2827847
theorem B2827853 : Blo 1883435 2827853 := bbase (se 3 (by rfl) ⟨530222, by rfl⟩ : syracuseStep 2827853 = 1060445) (by norm_num)
theorem B1885235 : Blo 1883435 1885235 := bstep (se 1 (by rfl) ⟨1413926, by rfl⟩ : syracuseStep 1885235 = 2827853) B2827853
theorem B4241789 : Blo 1883435 4241789 := bbase (se 3 (by rfl) ⟨795335, by rfl⟩ : syracuseStep 4241789 = 1590671) (by norm_num)
theorem B2827859 : Blo 1883435 2827859 := bstep (se 1 (by rfl) ⟨2120894, by rfl⟩ : syracuseStep 2827859 = 4241789) B4241789
theorem B1885239 : Blo 1883435 1885239 := bstep (se 1 (by rfl) ⟨1413929, by rfl⟩ : syracuseStep 1885239 = 2827859) B2827859
theorem B3181349 : Blo 1883435 3181349 := bbase (se 4 (by rfl) ⟨298251, by rfl⟩ : syracuseStep 3181349 = 596503) (by norm_num)
theorem B2120899 : Blo 1883435 2120899 := bstep (se 1 (by rfl) ⟨1590674, by rfl⟩ : syracuseStep 2120899 = 3181349) B3181349
theorem B2827865 : Blo 1883435 2827865 := bstep (se 2 (by rfl) ⟨1060449, by rfl⟩ : syracuseStep 2827865 = 2120899) B2120899
theorem B1885243 : Blo 1883435 1885243 := bstep (se 1 (by rfl) ⟨1413932, by rfl⟩ : syracuseStep 1885243 = 2827865) B2827865
theorem B2684269 : Blo 1883435 2684269 := bbase (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) (by norm_num)
theorem B14316101 : Blo 1883435 14316101 := bstep (se 4 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 14316101 = 2684269) B2684269
theorem B9544067 : Blo 1883435 9544067 := bstep (se 1 (by rfl) ⟨7158050, by rfl⟩ : syracuseStep 9544067 = 14316101) B14316101
theorem B6362711 : Blo 1883435 6362711 := bstep (se 1 (by rfl) ⟨4772033, by rfl⟩ : syracuseStep 6362711 = 9544067) B9544067
theorem B4241807 : Blo 1883435 4241807 := bstep (se 1 (by rfl) ⟨3181355, by rfl⟩ : syracuseStep 4241807 = 6362711) B6362711
theorem B2827871 : Blo 1883435 2827871 := bstep (se 1 (by rfl) ⟨2120903, by rfl⟩ : syracuseStep 2827871 = 4241807) B4241807
theorem B1885247 : Blo 1883435 1885247 := bstep (se 1 (by rfl) ⟨1413935, by rfl⟩ : syracuseStep 1885247 = 2827871) B2827871
theorem B2827877 : Blo 1883435 2827877 := bbase (se 4 (by rfl) ⟨265113, by rfl⟩ : syracuseStep 2827877 = 530227) (by norm_num)
theorem B1885251 : Blo 1883435 1885251 := bstep (se 1 (by rfl) ⟨1413938, by rfl⟩ : syracuseStep 1885251 = 2827877) B2827877
theorem B5441813 : Blo 1883435 5441813 := bbase (se 6 (by rfl) ⟨127542, by rfl⟩ : syracuseStep 5441813 = 255085) (by norm_num)
theorem B3627875 : Blo 1883435 3627875 := bstep (se 1 (by rfl) ⟨2720906, by rfl⟩ : syracuseStep 3627875 = 5441813) B5441813
theorem B2418583 : Blo 1883435 2418583 := bstep (se 1 (by rfl) ⟨1813937, by rfl⟩ : syracuseStep 2418583 = 3627875) B3627875
theorem B3224777 : Blo 1883435 3224777 := bstep (se 2 (by rfl) ⟨1209291, by rfl⟩ : syracuseStep 3224777 = 2418583) B2418583
theorem B8599405 : Blo 1883435 8599405 := bstep (se 3 (by rfl) ⟨1612388, by rfl⟩ : syracuseStep 8599405 = 3224777) B3224777
theorem B11465873 : Blo 1883435 11465873 := bstep (se 2 (by rfl) ⟨4299702, by rfl⟩ : syracuseStep 11465873 = 8599405) B8599405
theorem B7643915 : Blo 1883435 7643915 := bstep (se 1 (by rfl) ⟨5732936, by rfl⟩ : syracuseStep 7643915 = 11465873) B11465873
theorem B5095943 : Blo 1883435 5095943 := bstep (se 1 (by rfl) ⟨3821957, by rfl⟩ : syracuseStep 5095943 = 7643915) B7643915
theorem B3397295 : Blo 1883435 3397295 := bstep (se 1 (by rfl) ⟨2547971, by rfl⟩ : syracuseStep 3397295 = 5095943) B5095943
theorem B2264863 : Blo 1883435 2264863 := bstep (se 1 (by rfl) ⟨1698647, by rfl⟩ : syracuseStep 2264863 = 3397295) B3397295
theorem B3019817 : Blo 1883435 3019817 := bstep (se 2 (by rfl) ⟨1132431, by rfl⟩ : syracuseStep 3019817 = 2264863) B2264863
theorem B2013211 : Blo 1883435 2013211 := bstep (se 1 (by rfl) ⟨1509908, by rfl⟩ : syracuseStep 2013211 = 3019817) B3019817
theorem B2684281 : Blo 1883435 2684281 := bstep (se 2 (by rfl) ⟨1006605, by rfl⟩ : syracuseStep 2684281 = 2013211) B2013211
theorem B3579041 : Blo 1883435 3579041 := bstep (se 2 (by rfl) ⟨1342140, by rfl⟩ : syracuseStep 3579041 = 2684281) B2684281
theorem B2386027 : Blo 1883435 2386027 := bstep (se 1 (by rfl) ⟨1789520, by rfl⟩ : syracuseStep 2386027 = 3579041) B3579041
theorem B3181369 : Blo 1883435 3181369 := bstep (se 2 (by rfl) ⟨1193013, by rfl⟩ : syracuseStep 3181369 = 2386027) B2386027
theorem B4241825 : Blo 1883435 4241825 := bstep (se 2 (by rfl) ⟨1590684, by rfl⟩ : syracuseStep 4241825 = 3181369) B3181369
theorem B2827883 : Blo 1883435 2827883 := bstep (se 1 (by rfl) ⟨2120912, by rfl⟩ : syracuseStep 2827883 = 4241825) B4241825
theorem B1885255 : Blo 1883435 1885255 := bstep (se 1 (by rfl) ⟨1413941, by rfl⟩ : syracuseStep 1885255 = 2827883) B2827883
theorem B2120917 : Blo 1883435 2120917 := bbase (se 7 (by rfl) ⟨24854, by rfl⟩ : syracuseStep 2120917 = 49709) (by norm_num)
theorem B2827889 : Blo 1883435 2827889 := bstep (se 2 (by rfl) ⟨1060458, by rfl⟩ : syracuseStep 2827889 = 2120917) B2120917
theorem B1885259 : Blo 1883435 1885259 := bstep (se 1 (by rfl) ⟨1413944, by rfl⟩ : syracuseStep 1885259 = 2827889) B2827889
theorem B2386037 : Blo 1883435 2386037 := bbase (se 5 (by rfl) ⟨111845, by rfl⟩ : syracuseStep 2386037 = 223691) (by norm_num)
theorem B6362765 : Blo 1883435 6362765 := bstep (se 3 (by rfl) ⟨1193018, by rfl⟩ : syracuseStep 6362765 = 2386037) B2386037
theorem B4241843 : Blo 1883435 4241843 := bstep (se 1 (by rfl) ⟨3181382, by rfl⟩ : syracuseStep 4241843 = 6362765) B6362765
theorem B2827895 : Blo 1883435 2827895 := bstep (se 1 (by rfl) ⟨2120921, by rfl⟩ : syracuseStep 2827895 = 4241843) B4241843
theorem B1885263 : Blo 1883435 1885263 := bstep (se 1 (by rfl) ⟨1413947, by rfl⟩ : syracuseStep 1885263 = 2827895) B2827895
theorem B2827901 : Blo 1883435 2827901 := bbase (se 3 (by rfl) ⟨530231, by rfl⟩ : syracuseStep 2827901 = 1060463) (by norm_num)
theorem B1885267 : Blo 1883435 1885267 := bstep (se 1 (by rfl) ⟨1413950, by rfl⟩ : syracuseStep 1885267 = 2827901) B2827901
theorem B4241861 : Blo 1883435 4241861 := bbase (se 4 (by rfl) ⟨397674, by rfl⟩ : syracuseStep 4241861 = 795349) (by norm_num)
theorem B2827907 : Blo 1883435 2827907 := bstep (se 1 (by rfl) ⟨2120930, by rfl⟩ : syracuseStep 2827907 = 4241861) B4241861
theorem B1885271 : Blo 1883435 1885271 := bstep (se 1 (by rfl) ⟨1413953, by rfl⟩ : syracuseStep 1885271 = 2827907) B2827907
theorem B4529773 : Blo 1883435 4529773 := bbase (se 3 (by rfl) ⟨849332, by rfl⟩ : syracuseStep 4529773 = 1698665) (by norm_num)
theorem B6039697 : Blo 1883435 6039697 := bstep (se 2 (by rfl) ⟨2264886, by rfl⟩ : syracuseStep 6039697 = 4529773) B4529773
theorem B8052929 : Blo 1883435 8052929 := bstep (se 2 (by rfl) ⟨3019848, by rfl⟩ : syracuseStep 8052929 = 6039697) B6039697
theorem B5368619 : Blo 1883435 5368619 := bstep (se 1 (by rfl) ⟨4026464, by rfl⟩ : syracuseStep 5368619 = 8052929) B8052929
theorem B3579079 : Blo 1883435 3579079 := bstep (se 1 (by rfl) ⟨2684309, by rfl⟩ : syracuseStep 3579079 = 5368619) B5368619
theorem B4772105 : Blo 1883435 4772105 := bstep (se 2 (by rfl) ⟨1789539, by rfl⟩ : syracuseStep 4772105 = 3579079) B3579079
theorem B3181403 : Blo 1883435 3181403 := bstep (se 1 (by rfl) ⟨2386052, by rfl⟩ : syracuseStep 3181403 = 4772105) B4772105
theorem B2120935 : Blo 1883435 2120935 := bstep (se 1 (by rfl) ⟨1590701, by rfl⟩ : syracuseStep 2120935 = 3181403) B3181403
theorem B2827913 : Blo 1883435 2827913 := bstep (se 2 (by rfl) ⟨1060467, by rfl⟩ : syracuseStep 2827913 = 2120935) B2120935
theorem B1885275 : Blo 1883435 1885275 := bstep (se 1 (by rfl) ⟨1413956, by rfl⟩ : syracuseStep 1885275 = 2827913) B2827913
theorem B9544229 : Blo 1883435 9544229 := bbase (se 4 (by rfl) ⟨894771, by rfl⟩ : syracuseStep 9544229 = 1789543) (by norm_num)
theorem B6362819 : Blo 1883435 6362819 := bstep (se 1 (by rfl) ⟨4772114, by rfl⟩ : syracuseStep 6362819 = 9544229) B9544229
theorem B4241879 : Blo 1883435 4241879 := bstep (se 1 (by rfl) ⟨3181409, by rfl⟩ : syracuseStep 4241879 = 6362819) B6362819
theorem B2827919 : Blo 1883435 2827919 := bstep (se 1 (by rfl) ⟨2120939, by rfl⟩ : syracuseStep 2827919 = 4241879) B4241879
theorem B1885279 : Blo 1883435 1885279 := bstep (se 1 (by rfl) ⟨1413959, by rfl⟩ : syracuseStep 1885279 = 2827919) B2827919
theorem B2827925 : Blo 1883435 2827925 := bbase (se 6 (by rfl) ⟨66279, by rfl⟩ : syracuseStep 2827925 = 132559) (by norm_num)
theorem B1885283 : Blo 1883435 1885283 := bstep (se 1 (by rfl) ⟨1413962, by rfl⟩ : syracuseStep 1885283 = 2827925) B2827925
theorem B39225941 : Blo 1883435 39225941 := bbase (se 8 (by rfl) ⟨229839, by rfl⟩ : syracuseStep 39225941 = 459679) (by norm_num)
theorem B26150627 : Blo 1883435 26150627 := bstep (se 1 (by rfl) ⟨19612970, by rfl⟩ : syracuseStep 26150627 = 39225941) B39225941
theorem B17433751 : Blo 1883435 17433751 := bstep (se 1 (by rfl) ⟨13075313, by rfl⟩ : syracuseStep 17433751 = 26150627) B26150627
theorem B23245001 : Blo 1883435 23245001 := bstep (se 2 (by rfl) ⟨8716875, by rfl⟩ : syracuseStep 23245001 = 17433751) B17433751
theorem B15496667 : Blo 1883435 15496667 := bstep (se 1 (by rfl) ⟨11622500, by rfl⟩ : syracuseStep 15496667 = 23245001) B23245001
theorem B10331111 : Blo 1883435 10331111 := bstep (se 1 (by rfl) ⟨7748333, by rfl⟩ : syracuseStep 10331111 = 15496667) B15496667
theorem B27549629 : Blo 1883435 27549629 := bstep (se 3 (by rfl) ⟨5165555, by rfl⟩ : syracuseStep 27549629 = 10331111) B10331111
theorem B18366419 : Blo 1883435 18366419 := bstep (se 1 (by rfl) ⟨13774814, by rfl⟩ : syracuseStep 18366419 = 27549629) B27549629
theorem B12244279 : Blo 1883435 12244279 := bstep (se 1 (by rfl) ⟨9183209, by rfl⟩ : syracuseStep 12244279 = 18366419) B18366419
theorem B16325705 : Blo 1883435 16325705 := bstep (se 2 (by rfl) ⟨6122139, by rfl⟩ : syracuseStep 16325705 = 12244279) B12244279
theorem B10883803 : Blo 1883435 10883803 := bstep (se 1 (by rfl) ⟨8162852, by rfl⟩ : syracuseStep 10883803 = 16325705) B16325705
theorem B14511737 : Blo 1883435 14511737 := bstep (se 2 (by rfl) ⟨5441901, by rfl⟩ : syracuseStep 14511737 = 10883803) B10883803
theorem B9674491 : Blo 1883435 9674491 := bstep (se 1 (by rfl) ⟨7255868, by rfl⟩ : syracuseStep 9674491 = 14511737) B14511737
theorem B12899321 : Blo 1883435 12899321 := bstep (se 2 (by rfl) ⟨4837245, by rfl⟩ : syracuseStep 12899321 = 9674491) B9674491
theorem B8599547 : Blo 1883435 8599547 := bstep (se 1 (by rfl) ⟨6449660, by rfl⟩ : syracuseStep 8599547 = 12899321) B12899321
theorem B5733031 : Blo 1883435 5733031 := bstep (se 1 (by rfl) ⟨4299773, by rfl⟩ : syracuseStep 5733031 = 8599547) B8599547
theorem B7644041 : Blo 1883435 7644041 := bstep (se 2 (by rfl) ⟨2866515, by rfl⟩ : syracuseStep 7644041 = 5733031) B5733031
theorem B5096027 : Blo 1883435 5096027 := bstep (se 1 (by rfl) ⟨3822020, by rfl⟩ : syracuseStep 5096027 = 7644041) B7644041
theorem B3397351 : Blo 1883435 3397351 := bstep (se 1 (by rfl) ⟨2548013, by rfl⟩ : syracuseStep 3397351 = 5096027) B5096027
theorem B4529801 : Blo 1883435 4529801 := bstep (se 2 (by rfl) ⟨1698675, by rfl⟩ : syracuseStep 4529801 = 3397351) B3397351
theorem B12079469 : Blo 1883435 12079469 := bstep (se 3 (by rfl) ⟨2264900, by rfl⟩ : syracuseStep 12079469 = 4529801) B4529801
theorem B8052979 : Blo 1883435 8052979 := bstep (se 1 (by rfl) ⟨6039734, by rfl⟩ : syracuseStep 8052979 = 12079469) B12079469
theorem B10737305 : Blo 1883435 10737305 := bstep (se 2 (by rfl) ⟨4026489, by rfl⟩ : syracuseStep 10737305 = 8052979) B8052979
theorem B7158203 : Blo 1883435 7158203 := bstep (se 1 (by rfl) ⟨5368652, by rfl⟩ : syracuseStep 7158203 = 10737305) B10737305
theorem B4772135 : Blo 1883435 4772135 := bstep (se 1 (by rfl) ⟨3579101, by rfl⟩ : syracuseStep 4772135 = 7158203) B7158203
theorem B3181423 : Blo 1883435 3181423 := bstep (se 1 (by rfl) ⟨2386067, by rfl⟩ : syracuseStep 3181423 = 4772135) B4772135
theorem B4241897 : Blo 1883435 4241897 := bstep (se 2 (by rfl) ⟨1590711, by rfl⟩ : syracuseStep 4241897 = 3181423) B3181423
theorem B2827931 : Blo 1883435 2827931 := bstep (se 1 (by rfl) ⟨2120948, by rfl⟩ : syracuseStep 2827931 = 4241897) B4241897
theorem B1885287 : Blo 1883435 1885287 := bstep (se 1 (by rfl) ⟨1413965, by rfl⟩ : syracuseStep 1885287 = 2827931) B2827931
theorem B2120953 : Blo 1883435 2120953 := bbase (se 2 (by rfl) ⟨795357, by rfl⟩ : syracuseStep 2120953 = 1590715) (by norm_num)
theorem B2827937 : Blo 1883435 2827937 := bstep (se 2 (by rfl) ⟨1060476, by rfl⟩ : syracuseStep 2827937 = 2120953) B2120953
theorem B1885291 : Blo 1883435 1885291 := bstep (se 1 (by rfl) ⟨1413968, by rfl⟩ : syracuseStep 1885291 = 2827937) B2827937
theorem B8053013 : Blo 1883435 8053013 := bbase (se 6 (by rfl) ⟨188742, by rfl⟩ : syracuseStep 8053013 = 377485) (by norm_num)
theorem B5368675 : Blo 1883435 5368675 := bstep (se 1 (by rfl) ⟨4026506, by rfl⟩ : syracuseStep 5368675 = 8053013) B8053013
theorem B7158233 : Blo 1883435 7158233 := bstep (se 2 (by rfl) ⟨2684337, by rfl⟩ : syracuseStep 7158233 = 5368675) B5368675
theorem B4772155 : Blo 1883435 4772155 := bstep (se 1 (by rfl) ⟨3579116, by rfl⟩ : syracuseStep 4772155 = 7158233) B7158233
theorem B6362873 : Blo 1883435 6362873 := bstep (se 2 (by rfl) ⟨2386077, by rfl⟩ : syracuseStep 6362873 = 4772155) B4772155
theorem B4241915 : Blo 1883435 4241915 := bstep (se 1 (by rfl) ⟨3181436, by rfl⟩ : syracuseStep 4241915 = 6362873) B6362873
theorem B2827943 : Blo 1883435 2827943 := bstep (se 1 (by rfl) ⟨2120957, by rfl⟩ : syracuseStep 2827943 = 4241915) B4241915
theorem B1885295 : Blo 1883435 1885295 := bstep (se 1 (by rfl) ⟨1413971, by rfl⟩ : syracuseStep 1885295 = 2827943) B2827943
theorem B2827949 : Blo 1883435 2827949 := bbase (se 3 (by rfl) ⟨530240, by rfl⟩ : syracuseStep 2827949 = 1060481) (by norm_num)
theorem B1885299 : Blo 1883435 1885299 := bstep (se 1 (by rfl) ⟨1413974, by rfl⟩ : syracuseStep 1885299 = 2827949) B2827949
theorem B4241933 : Blo 1883435 4241933 := bbase (se 3 (by rfl) ⟨795362, by rfl⟩ : syracuseStep 4241933 = 1590725) (by norm_num)
theorem B2827955 : Blo 1883435 2827955 := bstep (se 1 (by rfl) ⟨2120966, by rfl⟩ : syracuseStep 2827955 = 4241933) B4241933
theorem B1885303 : Blo 1883435 1885303 := bstep (se 1 (by rfl) ⟨1413977, by rfl⟩ : syracuseStep 1885303 = 2827955) B2827955
theorem B2386093 : Blo 1883435 2386093 := bbase (se 3 (by rfl) ⟨447392, by rfl⟩ : syracuseStep 2386093 = 894785) (by norm_num)
theorem B3181457 : Blo 1883435 3181457 := bstep (se 2 (by rfl) ⟨1193046, by rfl⟩ : syracuseStep 3181457 = 2386093) B2386093
theorem B2120971 : Blo 1883435 2120971 := bstep (se 1 (by rfl) ⟨1590728, by rfl⟩ : syracuseStep 2120971 = 3181457) B3181457
theorem B2827961 : Blo 1883435 2827961 := bstep (se 2 (by rfl) ⟨1060485, by rfl⟩ : syracuseStep 2827961 = 2120971) B2120971
theorem B1885307 : Blo 1883435 1885307 := bstep (se 1 (by rfl) ⟨1413980, by rfl⟩ : syracuseStep 1885307 = 2827961) B2827961
theorem B2264929 : Blo 1883435 2264929 := bbase (se 2 (by rfl) ⟨849348, by rfl⟩ : syracuseStep 2264929 = 1698697) (by norm_num)
theorem B12079621 : Blo 1883435 12079621 := bstep (se 4 (by rfl) ⟨1132464, by rfl⟩ : syracuseStep 12079621 = 2264929) B2264929
theorem B16106161 : Blo 1883435 16106161 := bstep (se 2 (by rfl) ⟨6039810, by rfl⟩ : syracuseStep 16106161 = 12079621) B12079621
theorem B21474881 : Blo 1883435 21474881 := bstep (se 2 (by rfl) ⟨8053080, by rfl⟩ : syracuseStep 21474881 = 16106161) B16106161
theorem B14316587 : Blo 1883435 14316587 := bstep (se 1 (by rfl) ⟨10737440, by rfl⟩ : syracuseStep 14316587 = 21474881) B21474881
theorem B9544391 : Blo 1883435 9544391 := bstep (se 1 (by rfl) ⟨7158293, by rfl⟩ : syracuseStep 9544391 = 14316587) B14316587
theorem B6362927 : Blo 1883435 6362927 := bstep (se 1 (by rfl) ⟨4772195, by rfl⟩ : syracuseStep 6362927 = 9544391) B9544391
theorem B4241951 : Blo 1883435 4241951 := bstep (se 1 (by rfl) ⟨3181463, by rfl⟩ : syracuseStep 4241951 = 6362927) B6362927
theorem B2827967 : Blo 1883435 2827967 := bstep (se 1 (by rfl) ⟨2120975, by rfl⟩ : syracuseStep 2827967 = 4241951) B4241951
theorem B1885311 : Blo 1883435 1885311 := bstep (se 1 (by rfl) ⟨1413983, by rfl⟩ : syracuseStep 1885311 = 2827967) B2827967
theorem B2827973 : Blo 1883435 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B1885315 : Blo 1883435 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B3181477 : Blo 1883435 3181477 := bbase (se 4 (by rfl) ⟨298263, by rfl⟩ : syracuseStep 3181477 = 596527) (by norm_num)
theorem B4241969 : Blo 1883435 4241969 := bstep (se 2 (by rfl) ⟨1590738, by rfl⟩ : syracuseStep 4241969 = 3181477) B3181477
theorem B2827979 : Blo 1883435 2827979 := bstep (se 1 (by rfl) ⟨2120984, by rfl⟩ : syracuseStep 2827979 = 4241969) B4241969
theorem B1885319 : Blo 1883435 1885319 := bstep (se 1 (by rfl) ⟨1413989, by rfl⟩ : syracuseStep 1885319 = 2827979) B2827979
theorem B2120989 : Blo 1883435 2120989 := bbase (se 3 (by rfl) ⟨397685, by rfl⟩ : syracuseStep 2120989 = 795371) (by norm_num)
theorem B2827985 : Blo 1883435 2827985 := bstep (se 2 (by rfl) ⟨1060494, by rfl⟩ : syracuseStep 2827985 = 2120989) B2120989
theorem B1885323 : Blo 1883435 1885323 := bstep (se 1 (by rfl) ⟨1413992, by rfl⟩ : syracuseStep 1885323 = 2827985) B2827985
theorem B6362981 : Blo 1883435 6362981 := bbase (se 4 (by rfl) ⟨596529, by rfl⟩ : syracuseStep 6362981 = 1193059) (by norm_num)
theorem B4241987 : Blo 1883435 4241987 := bstep (se 1 (by rfl) ⟨3181490, by rfl⟩ : syracuseStep 4241987 = 6362981) B6362981
theorem B2827991 : Blo 1883435 2827991 := bstep (se 1 (by rfl) ⟨2120993, by rfl⟩ : syracuseStep 2827991 = 4241987) B4241987
theorem B1885327 : Blo 1883435 1885327 := bstep (se 1 (by rfl) ⟨1413995, by rfl⟩ : syracuseStep 1885327 = 2827991) B2827991
theorem B2827997 : Blo 1883435 2827997 := bbase (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) (by norm_num)
theorem B1885331 : Blo 1883435 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B4242005 : Blo 1883435 4242005 := bbase (se 8 (by rfl) ⟨24855, by rfl⟩ : syracuseStep 4242005 = 49711) (by norm_num)
theorem B2828003 : Blo 1883435 2828003 := bstep (se 1 (by rfl) ⟨2121002, by rfl⟩ : syracuseStep 2828003 = 4242005) B4242005
theorem B1885335 : Blo 1883435 1885335 := bstep (se 1 (by rfl) ⟨1414001, by rfl⟩ : syracuseStep 1885335 = 2828003) B2828003
theorem B4299893 : Blo 1883435 4299893 := bbase (se 5 (by rfl) ⟨201557, by rfl⟩ : syracuseStep 4299893 = 403115) (by norm_num)
theorem B2866595 : Blo 1883435 2866595 := bstep (se 1 (by rfl) ⟨2149946, by rfl⟩ : syracuseStep 2866595 = 4299893) B4299893
theorem B7644253 : Blo 1883435 7644253 := bstep (se 3 (by rfl) ⟨1433297, by rfl⟩ : syracuseStep 7644253 = 2866595) B2866595
theorem B10192337 : Blo 1883435 10192337 := bstep (se 2 (by rfl) ⟨3822126, by rfl⟩ : syracuseStep 10192337 = 7644253) B7644253
theorem B6794891 : Blo 1883435 6794891 := bstep (se 1 (by rfl) ⟨5096168, by rfl⟩ : syracuseStep 6794891 = 10192337) B10192337
theorem B4529927 : Blo 1883435 4529927 := bstep (se 1 (by rfl) ⟨3397445, by rfl⟩ : syracuseStep 4529927 = 6794891) B6794891
theorem B3019951 : Blo 1883435 3019951 := bstep (se 1 (by rfl) ⟨2264963, by rfl⟩ : syracuseStep 3019951 = 4529927) B4529927
theorem B4026601 : Blo 1883435 4026601 := bstep (se 2 (by rfl) ⟨1509975, by rfl⟩ : syracuseStep 4026601 = 3019951) B3019951
theorem B5368801 : Blo 1883435 5368801 := bstep (se 2 (by rfl) ⟨2013300, by rfl⟩ : syracuseStep 5368801 = 4026601) B4026601
theorem B7158401 : Blo 1883435 7158401 := bstep (se 2 (by rfl) ⟨2684400, by rfl⟩ : syracuseStep 7158401 = 5368801) B5368801
theorem B4772267 : Blo 1883435 4772267 := bstep (se 1 (by rfl) ⟨3579200, by rfl⟩ : syracuseStep 4772267 = 7158401) B7158401
theorem B3181511 : Blo 1883435 3181511 := bstep (se 1 (by rfl) ⟨2386133, by rfl⟩ : syracuseStep 3181511 = 4772267) B4772267
theorem B2121007 : Blo 1883435 2121007 := bstep (se 1 (by rfl) ⟨1590755, by rfl⟩ : syracuseStep 2121007 = 3181511) B3181511
theorem B2828009 : Blo 1883435 2828009 := bstep (se 2 (by rfl) ⟨1060503, by rfl⟩ : syracuseStep 2828009 = 2121007) B2121007
theorem B1885339 : Blo 1883435 1885339 := bstep (se 1 (by rfl) ⟨1414004, by rfl⟩ : syracuseStep 1885339 = 2828009) B2828009
theorem B15288533 : Blo 1883435 15288533 := bbase (se 7 (by rfl) ⟨179162, by rfl⟩ : syracuseStep 15288533 = 358325) (by norm_num)
theorem B10192355 : Blo 1883435 10192355 := bstep (se 1 (by rfl) ⟨7644266, by rfl⟩ : syracuseStep 10192355 = 15288533) B15288533
theorem B6794903 : Blo 1883435 6794903 := bstep (se 1 (by rfl) ⟨5096177, by rfl⟩ : syracuseStep 6794903 = 10192355) B10192355
theorem B4529935 : Blo 1883435 4529935 := bstep (se 1 (by rfl) ⟨3397451, by rfl⟩ : syracuseStep 4529935 = 6794903) B6794903
theorem B24159653 : Blo 1883435 24159653 := bstep (se 4 (by rfl) ⟨2264967, by rfl⟩ : syracuseStep 24159653 = 4529935) B4529935
theorem B16106435 : Blo 1883435 16106435 := bstep (se 1 (by rfl) ⟨12079826, by rfl⟩ : syracuseStep 16106435 = 24159653) B24159653
theorem B10737623 : Blo 1883435 10737623 := bstep (se 1 (by rfl) ⟨8053217, by rfl⟩ : syracuseStep 10737623 = 16106435) B16106435
theorem B7158415 : Blo 1883435 7158415 := bstep (se 1 (by rfl) ⟨5368811, by rfl⟩ : syracuseStep 7158415 = 10737623) B10737623
theorem B9544553 : Blo 1883435 9544553 := bstep (se 2 (by rfl) ⟨3579207, by rfl⟩ : syracuseStep 9544553 = 7158415) B7158415
theorem B6363035 : Blo 1883435 6363035 := bstep (se 1 (by rfl) ⟨4772276, by rfl⟩ : syracuseStep 6363035 = 9544553) B9544553
theorem B4242023 : Blo 1883435 4242023 := bstep (se 1 (by rfl) ⟨3181517, by rfl⟩ : syracuseStep 4242023 = 6363035) B6363035
theorem B2828015 : Blo 1883435 2828015 := bstep (se 1 (by rfl) ⟨2121011, by rfl⟩ : syracuseStep 2828015 = 4242023) B4242023
theorem B1885343 : Blo 1883435 1885343 := bstep (se 1 (by rfl) ⟨1414007, by rfl⟩ : syracuseStep 1885343 = 2828015) B2828015
theorem B2828021 : Blo 1883435 2828021 := bbase (se 5 (by rfl) ⟨132563, by rfl⟩ : syracuseStep 2828021 = 265127) (by norm_num)
theorem B1885347 : Blo 1883435 1885347 := bstep (se 1 (by rfl) ⟨1414010, by rfl⟩ : syracuseStep 1885347 = 2828021) B2828021
theorem B8053253 : Blo 1883435 8053253 := bbase (se 4 (by rfl) ⟨754992, by rfl⟩ : syracuseStep 8053253 = 1509985) (by norm_num)
theorem B5368835 : Blo 1883435 5368835 := bstep (se 1 (by rfl) ⟨4026626, by rfl⟩ : syracuseStep 5368835 = 8053253) B8053253
theorem B3579223 : Blo 1883435 3579223 := bstep (se 1 (by rfl) ⟨2684417, by rfl⟩ : syracuseStep 3579223 = 5368835) B5368835
theorem B4772297 : Blo 1883435 4772297 := bstep (se 2 (by rfl) ⟨1789611, by rfl⟩ : syracuseStep 4772297 = 3579223) B3579223
theorem B3181531 : Blo 1883435 3181531 := bstep (se 1 (by rfl) ⟨2386148, by rfl⟩ : syracuseStep 3181531 = 4772297) B4772297
theorem B4242041 : Blo 1883435 4242041 := bstep (se 2 (by rfl) ⟨1590765, by rfl⟩ : syracuseStep 4242041 = 3181531) B3181531
theorem B2828027 : Blo 1883435 2828027 := bstep (se 1 (by rfl) ⟨2121020, by rfl⟩ : syracuseStep 2828027 = 4242041) B4242041
theorem B1885351 : Blo 1883435 1885351 := bstep (se 1 (by rfl) ⟨1414013, by rfl⟩ : syracuseStep 1885351 = 2828027) B2828027
theorem B2121025 : Blo 1883435 2121025 := bbase (se 2 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 2121025 = 1590769) (by norm_num)
theorem B2828033 : Blo 1883435 2828033 := bstep (se 2 (by rfl) ⟨1060512, by rfl⟩ : syracuseStep 2828033 = 2121025) B2121025
theorem B1885355 : Blo 1883435 1885355 := bstep (se 1 (by rfl) ⟨1414016, by rfl⟩ : syracuseStep 1885355 = 2828033) B2828033
theorem B4772317 : Blo 1883435 4772317 := bbase (se 3 (by rfl) ⟨894809, by rfl⟩ : syracuseStep 4772317 = 1789619) (by norm_num)
theorem B6363089 : Blo 1883435 6363089 := bstep (se 2 (by rfl) ⟨2386158, by rfl⟩ : syracuseStep 6363089 = 4772317) B4772317
theorem B4242059 : Blo 1883435 4242059 := bstep (se 1 (by rfl) ⟨3181544, by rfl⟩ : syracuseStep 4242059 = 6363089) B6363089
theorem B2828039 : Blo 1883435 2828039 := bstep (se 1 (by rfl) ⟨2121029, by rfl⟩ : syracuseStep 2828039 = 4242059) B4242059
theorem B1885359 : Blo 1883435 1885359 := bstep (se 1 (by rfl) ⟨1414019, by rfl⟩ : syracuseStep 1885359 = 2828039) B2828039
theorem B2828045 : Blo 1883435 2828045 := bbase (se 3 (by rfl) ⟨530258, by rfl⟩ : syracuseStep 2828045 = 1060517) (by norm_num)
theorem B1885363 : Blo 1883435 1885363 := bstep (se 1 (by rfl) ⟨1414022, by rfl⟩ : syracuseStep 1885363 = 2828045) B2828045
theorem B4242077 : Blo 1883435 4242077 := bbase (se 3 (by rfl) ⟨795389, by rfl⟩ : syracuseStep 4242077 = 1590779) (by norm_num)
theorem B2828051 : Blo 1883435 2828051 := bstep (se 1 (by rfl) ⟨2121038, by rfl⟩ : syracuseStep 2828051 = 4242077) B4242077
theorem B1885367 : Blo 1883435 1885367 := bstep (se 1 (by rfl) ⟨1414025, by rfl⟩ : syracuseStep 1885367 = 2828051) B2828051
theorem B3181565 : Blo 1883435 3181565 := bbase (se 3 (by rfl) ⟨596543, by rfl⟩ : syracuseStep 3181565 = 1193087) (by norm_num)
theorem B2121043 : Blo 1883435 2121043 := bstep (se 1 (by rfl) ⟨1590782, by rfl⟩ : syracuseStep 2121043 = 3181565) B3181565
theorem B2828057 : Blo 1883435 2828057 := bstep (se 2 (by rfl) ⟨1060521, by rfl⟩ : syracuseStep 2828057 = 2121043) B2121043
theorem B1885371 : Blo 1883435 1885371 := bstep (se 1 (by rfl) ⟨1414028, by rfl⟩ : syracuseStep 1885371 = 2828057) B2828057
theorem B4026677 : Blo 1883435 4026677 := bbase (se 5 (by rfl) ⟨188750, by rfl⟩ : syracuseStep 4026677 = 377501) (by norm_num)
theorem B10737805 : Blo 1883435 10737805 := bstep (se 3 (by rfl) ⟨2013338, by rfl⟩ : syracuseStep 10737805 = 4026677) B4026677
theorem B14317073 : Blo 1883435 14317073 := bstep (se 2 (by rfl) ⟨5368902, by rfl⟩ : syracuseStep 14317073 = 10737805) B10737805
theorem B9544715 : Blo 1883435 9544715 := bstep (se 1 (by rfl) ⟨7158536, by rfl⟩ : syracuseStep 9544715 = 14317073) B14317073
theorem B6363143 : Blo 1883435 6363143 := bstep (se 1 (by rfl) ⟨4772357, by rfl⟩ : syracuseStep 6363143 = 9544715) B9544715
theorem B4242095 : Blo 1883435 4242095 := bstep (se 1 (by rfl) ⟨3181571, by rfl⟩ : syracuseStep 4242095 = 6363143) B6363143
theorem B2828063 : Blo 1883435 2828063 := bstep (se 1 (by rfl) ⟨2121047, by rfl⟩ : syracuseStep 2828063 = 4242095) B4242095
theorem B1885375 : Blo 1883435 1885375 := bstep (se 1 (by rfl) ⟨1414031, by rfl⟩ : syracuseStep 1885375 = 2828063) B2828063
theorem B2828069 : Blo 1883435 2828069 := bbase (se 4 (by rfl) ⟨265131, by rfl⟩ : syracuseStep 2828069 = 530263) (by norm_num)
theorem B1885379 : Blo 1883435 1885379 := bstep (se 1 (by rfl) ⟨1414034, by rfl⟩ : syracuseStep 1885379 = 2828069) B2828069
theorem B2386189 : Blo 1883435 2386189 := bbase (se 3 (by rfl) ⟨447410, by rfl⟩ : syracuseStep 2386189 = 894821) (by norm_num)
theorem B3181585 : Blo 1883435 3181585 := bstep (se 2 (by rfl) ⟨1193094, by rfl⟩ : syracuseStep 3181585 = 2386189) B2386189
theorem B4242113 : Blo 1883435 4242113 := bstep (se 2 (by rfl) ⟨1590792, by rfl⟩ : syracuseStep 4242113 = 3181585) B3181585
theorem B2828075 : Blo 1883435 2828075 := bstep (se 1 (by rfl) ⟨2121056, by rfl⟩ : syracuseStep 2828075 = 4242113) B4242113
theorem B1885383 : Blo 1883435 1885383 := bstep (se 1 (by rfl) ⟨1414037, by rfl⟩ : syracuseStep 1885383 = 2828075) B2828075
theorem B2121061 : Blo 1883435 2121061 := bbase (se 4 (by rfl) ⟨198849, by rfl⟩ : syracuseStep 2121061 = 397699) (by norm_num)
theorem B2828081 : Blo 1883435 2828081 := bstep (se 2 (by rfl) ⟨1060530, by rfl⟩ : syracuseStep 2828081 = 2121061) B2121061
theorem B1885387 : Blo 1883435 1885387 := bstep (se 1 (by rfl) ⟨1414040, by rfl⟩ : syracuseStep 1885387 = 2828081) B2828081
theorem B5368949 : Blo 1883435 5368949 := bbase (se 5 (by rfl) ⟨251669, by rfl⟩ : syracuseStep 5368949 = 503339) (by norm_num)
theorem B3579299 : Blo 1883435 3579299 := bstep (se 1 (by rfl) ⟨2684474, by rfl⟩ : syracuseStep 3579299 = 5368949) B5368949
theorem B2386199 : Blo 1883435 2386199 := bstep (se 1 (by rfl) ⟨1789649, by rfl⟩ : syracuseStep 2386199 = 3579299) B3579299
theorem B6363197 : Blo 1883435 6363197 := bstep (se 3 (by rfl) ⟨1193099, by rfl⟩ : syracuseStep 6363197 = 2386199) B2386199
theorem B4242131 : Blo 1883435 4242131 := bstep (se 1 (by rfl) ⟨3181598, by rfl⟩ : syracuseStep 4242131 = 6363197) B6363197
theorem B2828087 : Blo 1883435 2828087 := bstep (se 1 (by rfl) ⟨2121065, by rfl⟩ : syracuseStep 2828087 = 4242131) B4242131
theorem B1885391 : Blo 1883435 1885391 := bstep (se 1 (by rfl) ⟨1414043, by rfl⟩ : syracuseStep 1885391 = 2828087) B2828087
theorem B2828093 : Blo 1883435 2828093 := bbase (se 3 (by rfl) ⟨530267, by rfl⟩ : syracuseStep 2828093 = 1060535) (by norm_num)
theorem B1885395 : Blo 1883435 1885395 := bstep (se 1 (by rfl) ⟨1414046, by rfl⟩ : syracuseStep 1885395 = 2828093) B2828093
theorem B4242149 : Blo 1883435 4242149 := bbase (se 4 (by rfl) ⟨397701, by rfl⟩ : syracuseStep 4242149 = 795403) (by norm_num)
theorem B2828099 : Blo 1883435 2828099 := bstep (se 1 (by rfl) ⟨2121074, by rfl⟩ : syracuseStep 2828099 = 4242149) B4242149
theorem B1885399 : Blo 1883435 1885399 := bstep (se 1 (by rfl) ⟨1414049, by rfl⟩ : syracuseStep 1885399 = 2828099) B2828099
theorem B4772429 : Blo 1883435 4772429 := bbase (se 3 (by rfl) ⟨894830, by rfl⟩ : syracuseStep 4772429 = 1789661) (by norm_num)
theorem B3181619 : Blo 1883435 3181619 := bstep (se 1 (by rfl) ⟨2386214, by rfl⟩ : syracuseStep 3181619 = 4772429) B4772429
theorem B2121079 : Blo 1883435 2121079 := bstep (se 1 (by rfl) ⟨1590809, by rfl⟩ : syracuseStep 2121079 = 3181619) B3181619
theorem B2828105 : Blo 1883435 2828105 := bstep (se 2 (by rfl) ⟨1060539, by rfl⟩ : syracuseStep 2828105 = 2121079) B2121079
theorem B1885403 : Blo 1883435 1885403 := bstep (se 1 (by rfl) ⟨1414052, by rfl⟩ : syracuseStep 1885403 = 2828105) B2828105
theorem B2013373 : Blo 1883435 2013373 := bbase (se 3 (by rfl) ⟨377507, by rfl⟩ : syracuseStep 2013373 = 755015) (by norm_num)
theorem B2684497 : Blo 1883435 2684497 := bstep (se 2 (by rfl) ⟨1006686, by rfl⟩ : syracuseStep 2684497 = 2013373) B2013373
theorem B3579329 : Blo 1883435 3579329 := bstep (se 2 (by rfl) ⟨1342248, by rfl⟩ : syracuseStep 3579329 = 2684497) B2684497
theorem B9544877 : Blo 1883435 9544877 := bstep (se 3 (by rfl) ⟨1789664, by rfl⟩ : syracuseStep 9544877 = 3579329) B3579329
theorem B6363251 : Blo 1883435 6363251 := bstep (se 1 (by rfl) ⟨4772438, by rfl⟩ : syracuseStep 6363251 = 9544877) B9544877
theorem B4242167 : Blo 1883435 4242167 := bstep (se 1 (by rfl) ⟨3181625, by rfl⟩ : syracuseStep 4242167 = 6363251) B6363251
theorem B2828111 : Blo 1883435 2828111 := bstep (se 1 (by rfl) ⟨2121083, by rfl⟩ : syracuseStep 2828111 = 4242167) B4242167
theorem B1885407 : Blo 1883435 1885407 := bstep (se 1 (by rfl) ⟨1414055, by rfl⟩ : syracuseStep 1885407 = 2828111) B2828111
theorem B2828117 : Blo 1883435 2828117 := bbase (se 9 (by rfl) ⟨8285, by rfl⟩ : syracuseStep 2828117 = 16571) (by norm_num)
theorem B1885411 : Blo 1883435 1885411 := bstep (se 1 (by rfl) ⟨1414058, by rfl⟩ : syracuseStep 1885411 = 2828117) B2828117
theorem B4530109 : Blo 1883435 4530109 := bbase (se 3 (by rfl) ⟨849395, by rfl⟩ : syracuseStep 4530109 = 1698791) (by norm_num)
theorem B6040145 : Blo 1883435 6040145 := bstep (se 2 (by rfl) ⟨2265054, by rfl⟩ : syracuseStep 6040145 = 4530109) B4530109
theorem B4026763 : Blo 1883435 4026763 := bstep (se 1 (by rfl) ⟨3020072, by rfl⟩ : syracuseStep 4026763 = 6040145) B6040145
theorem B5369017 : Blo 1883435 5369017 := bstep (se 2 (by rfl) ⟨2013381, by rfl⟩ : syracuseStep 5369017 = 4026763) B4026763
theorem B7158689 : Blo 1883435 7158689 := bstep (se 2 (by rfl) ⟨2684508, by rfl⟩ : syracuseStep 7158689 = 5369017) B5369017
theorem B4772459 : Blo 1883435 4772459 := bstep (se 1 (by rfl) ⟨3579344, by rfl⟩ : syracuseStep 4772459 = 7158689) B7158689
theorem B3181639 : Blo 1883435 3181639 := bstep (se 1 (by rfl) ⟨2386229, by rfl⟩ : syracuseStep 3181639 = 4772459) B4772459
theorem B4242185 : Blo 1883435 4242185 := bstep (se 2 (by rfl) ⟨1590819, by rfl⟩ : syracuseStep 4242185 = 3181639) B3181639
theorem B2828123 : Blo 1883435 2828123 := bstep (se 1 (by rfl) ⟨2121092, by rfl⟩ : syracuseStep 2828123 = 4242185) B4242185
theorem B1885415 : Blo 1883435 1885415 := bstep (se 1 (by rfl) ⟨1414061, by rfl⟩ : syracuseStep 1885415 = 2828123) B2828123
theorem B2121097 : Blo 1883435 2121097 := bbase (se 2 (by rfl) ⟨795411, by rfl⟩ : syracuseStep 2121097 = 1590823) (by norm_num)
theorem B2828129 : Blo 1883435 2828129 := bstep (se 2 (by rfl) ⟨1060548, by rfl⟩ : syracuseStep 2828129 = 2121097) B2121097
theorem B1885419 : Blo 1883435 1885419 := bstep (se 1 (by rfl) ⟨1414064, by rfl⟩ : syracuseStep 1885419 = 2828129) B2828129
theorem B2150041 : Blo 1883435 2150041 := bbase (se 2 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 2150041 = 1612531) (by norm_num)
theorem B45867541 : Blo 1883435 45867541 := bstep (se 6 (by rfl) ⟨1075020, by rfl⟩ : syracuseStep 45867541 = 2150041) B2150041
theorem B61156721 : Blo 1883435 61156721 := bstep (se 2 (by rfl) ⟨22933770, by rfl⟩ : syracuseStep 61156721 = 45867541) B45867541
theorem B40771147 : Blo 1883435 40771147 := bstep (se 1 (by rfl) ⟨30578360, by rfl⟩ : syracuseStep 40771147 = 61156721) B61156721
theorem B54361529 : Blo 1883435 54361529 := bstep (se 2 (by rfl) ⟨20385573, by rfl⟩ : syracuseStep 54361529 = 40771147) B40771147
theorem B36241019 : Blo 1883435 36241019 := bstep (se 1 (by rfl) ⟨27180764, by rfl⟩ : syracuseStep 36241019 = 54361529) B54361529
theorem B24160679 : Blo 1883435 24160679 := bstep (se 1 (by rfl) ⟨18120509, by rfl⟩ : syracuseStep 24160679 = 36241019) B36241019
theorem B16107119 : Blo 1883435 16107119 := bstep (se 1 (by rfl) ⟨12080339, by rfl⟩ : syracuseStep 16107119 = 24160679) B24160679
theorem B10738079 : Blo 1883435 10738079 := bstep (se 1 (by rfl) ⟨8053559, by rfl⟩ : syracuseStep 10738079 = 16107119) B16107119
theorem B7158719 : Blo 1883435 7158719 := bstep (se 1 (by rfl) ⟨5369039, by rfl⟩ : syracuseStep 7158719 = 10738079) B10738079
theorem B4772479 : Blo 1883435 4772479 := bstep (se 1 (by rfl) ⟨3579359, by rfl⟩ : syracuseStep 4772479 = 7158719) B7158719
theorem B6363305 : Blo 1883435 6363305 := bstep (se 2 (by rfl) ⟨2386239, by rfl⟩ : syracuseStep 6363305 = 4772479) B4772479
theorem B4242203 : Blo 1883435 4242203 := bstep (se 1 (by rfl) ⟨3181652, by rfl⟩ : syracuseStep 4242203 = 6363305) B6363305
theorem B2828135 : Blo 1883435 2828135 := bstep (se 1 (by rfl) ⟨2121101, by rfl⟩ : syracuseStep 2828135 = 4242203) B4242203
theorem B1885423 : Blo 1883435 1885423 := bstep (se 1 (by rfl) ⟨1414067, by rfl⟩ : syracuseStep 1885423 = 2828135) B2828135
theorem B2828141 : Blo 1883435 2828141 := bbase (se 3 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 2828141 = 1060553) (by norm_num)
theorem B1885427 : Blo 1883435 1885427 := bstep (se 1 (by rfl) ⟨1414070, by rfl⟩ : syracuseStep 1885427 = 2828141) B2828141
theorem B4242221 : Blo 1883435 4242221 := bbase (se 3 (by rfl) ⟨795416, by rfl⟩ : syracuseStep 4242221 = 1590833) (by norm_num)
theorem B2828147 : Blo 1883435 2828147 := bstep (se 1 (by rfl) ⟨2121110, by rfl⟩ : syracuseStep 2828147 = 4242221) B4242221
theorem B1885431 : Blo 1883435 1885431 := bstep (se 1 (by rfl) ⟨1414073, by rfl⟩ : syracuseStep 1885431 = 2828147) B2828147
theorem B1911161 : Blo 1883435 1911161 := bbase (se 2 (by rfl) ⟨716685, by rfl⟩ : syracuseStep 1911161 = 1433371) (by norm_num)
theorem B5096429 : Blo 1883435 5096429 := bstep (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) B1911161
theorem B3397619 : Blo 1883435 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B2265079 : Blo 1883435 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B3020105 : Blo 1883435 3020105 := bstep (se 2 (by rfl) ⟨1132539, by rfl⟩ : syracuseStep 3020105 = 2265079) B2265079
theorem B8053613 : Blo 1883435 8053613 := bstep (se 3 (by rfl) ⟨1510052, by rfl⟩ : syracuseStep 8053613 = 3020105) B3020105
theorem B5369075 : Blo 1883435 5369075 := bstep (se 1 (by rfl) ⟨4026806, by rfl⟩ : syracuseStep 5369075 = 8053613) B8053613
theorem B3579383 : Blo 1883435 3579383 := bstep (se 1 (by rfl) ⟨2684537, by rfl⟩ : syracuseStep 3579383 = 5369075) B5369075
theorem B2386255 : Blo 1883435 2386255 := bstep (se 1 (by rfl) ⟨1789691, by rfl⟩ : syracuseStep 2386255 = 3579383) B3579383
theorem B3181673 : Blo 1883435 3181673 := bstep (se 2 (by rfl) ⟨1193127, by rfl⟩ : syracuseStep 3181673 = 2386255) B2386255
theorem B2121115 : Blo 1883435 2121115 := bstep (se 1 (by rfl) ⟨1590836, by rfl⟩ : syracuseStep 2121115 = 3181673) B3181673
theorem B2828153 : Blo 1883435 2828153 := bstep (se 2 (by rfl) ⟨1060557, by rfl⟩ : syracuseStep 2828153 = 2121115) B2121115
theorem B1885435 : Blo 1883435 1885435 := bstep (se 1 (by rfl) ⟨1414076, by rfl⟩ : syracuseStep 1885435 = 2828153) B2828153
theorem C0 (j : ℕ) (h1 : 470858 ≤ j) (h2 : j ≤ 471358) : Blo 1883435 (4 * j + 3) := by
  interval_cases j
  · exact B1883435
  · exact B1883439
  · exact B1883443
  · exact B1883447
  · exact B1883451
  · exact B1883455
  · exact B1883459
  · exact B1883463
  · exact B1883467
  · exact B1883471
  · exact B1883475
  · exact B1883479
  · exact B1883483
  · exact B1883487
  · exact B1883491
  · exact B1883495
  · exact B1883499
  · exact B1883503
  · exact B1883507
  · exact B1883511
  · exact B1883515
  · exact B1883519
  · exact B1883523
  · exact B1883527
  · exact B1883531
  · exact B1883535
  · exact B1883539
  · exact B1883543
  · exact B1883547
  · exact B1883551
  · exact B1883555
  · exact B1883559
  · exact B1883563
  · exact B1883567
  · exact B1883571
  · exact B1883575
  · exact B1883579
  · exact B1883583
  · exact B1883587
  · exact B1883591
  · exact B1883595
  · exact B1883599
  · exact B1883603
  · exact B1883607
  · exact B1883611
  · exact B1883615
  · exact B1883619
  · exact B1883623
  · exact B1883627
  · exact B1883631
  · exact B1883635
  · exact B1883639
  · exact B1883643
  · exact B1883647
  · exact B1883651
  · exact B1883655
  · exact B1883659
  · exact B1883663
  · exact B1883667
  · exact B1883671
  · exact B1883675
  · exact B1883679
  · exact B1883683
  · exact B1883687
  · exact B1883691
  · exact B1883695
  · exact B1883699
  · exact B1883703
  · exact B1883707
  · exact B1883711
  · exact B1883715
  · exact B1883719
  · exact B1883723
  · exact B1883727
  · exact B1883731
  · exact B1883735
  · exact B1883739
  · exact B1883743
  · exact B1883747
  · exact B1883751
  · exact B1883755
  · exact B1883759
  · exact B1883763
  · exact B1883767
  · exact B1883771
  · exact B1883775
  · exact B1883779
  · exact B1883783
  · exact B1883787
  · exact B1883791
  · exact B1883795
  · exact B1883799
  · exact B1883803
  · exact B1883807
  · exact B1883811
  · exact B1883815
  · exact B1883819
  · exact B1883823
  · exact B1883827
  · exact B1883831
  · exact B1883835
  · exact B1883839
  · exact B1883843
  · exact B1883847
  · exact B1883851
  · exact B1883855
  · exact B1883859
  · exact B1883863
  · exact B1883867
  · exact B1883871
  · exact B1883875
  · exact B1883879
  · exact B1883883
  · exact B1883887
  · exact B1883891
  · exact B1883895
  · exact B1883899
  · exact B1883903
  · exact B1883907
  · exact B1883911
  · exact B1883915
  · exact B1883919
  · exact B1883923
  · exact B1883927
  · exact B1883931
  · exact B1883935
  · exact B1883939
  · exact B1883943
  · exact B1883947
  · exact B1883951
  · exact B1883955
  · exact B1883959
  · exact B1883963
  · exact B1883967
  · exact B1883971
  · exact B1883975
  · exact B1883979
  · exact B1883983
  · exact B1883987
  · exact B1883991
  · exact B1883995
  · exact B1883999
  · exact B1884003
  · exact B1884007
  · exact B1884011
  · exact B1884015
  · exact B1884019
  · exact B1884023
  · exact B1884027
  · exact B1884031
  · exact B1884035
  · exact B1884039
  · exact B1884043
  · exact B1884047
  · exact B1884051
  · exact B1884055
  · exact B1884059
  · exact B1884063
  · exact B1884067
  · exact B1884071
  · exact B1884075
  · exact B1884079
  · exact B1884083
  · exact B1884087
  · exact B1884091
  · exact B1884095
  · exact B1884099
  · exact B1884103
  · exact B1884107
  · exact B1884111
  · exact B1884115
  · exact B1884119
  · exact B1884123
  · exact B1884127
  · exact B1884131
  · exact B1884135
  · exact B1884139
  · exact B1884143
  · exact B1884147
  · exact B1884151
  · exact B1884155
  · exact B1884159
  · exact B1884163
  · exact B1884167
  · exact B1884171
  · exact B1884175
  · exact B1884179
  · exact B1884183
  · exact B1884187
  · exact B1884191
  · exact B1884195
  · exact B1884199
  · exact B1884203
  · exact B1884207
  · exact B1884211
  · exact B1884215
  · exact B1884219
  · exact B1884223
  · exact B1884227
  · exact B1884231
  · exact B1884235
  · exact B1884239
  · exact B1884243
  · exact B1884247
  · exact B1884251
  · exact B1884255
  · exact B1884259
  · exact B1884263
  · exact B1884267
  · exact B1884271
  · exact B1884275
  · exact B1884279
  · exact B1884283
  · exact B1884287
  · exact B1884291
  · exact B1884295
  · exact B1884299
  · exact B1884303
  · exact B1884307
  · exact B1884311
  · exact B1884315
  · exact B1884319
  · exact B1884323
  · exact B1884327
  · exact B1884331
  · exact B1884335
  · exact B1884339
  · exact B1884343
  · exact B1884347
  · exact B1884351
  · exact B1884355
  · exact B1884359
  · exact B1884363
  · exact B1884367
  · exact B1884371
  · exact B1884375
  · exact B1884379
  · exact B1884383
  · exact B1884387
  · exact B1884391
  · exact B1884395
  · exact B1884399
  · exact B1884403
  · exact B1884407
  · exact B1884411
  · exact B1884415
  · exact B1884419
  · exact B1884423
  · exact B1884427
  · exact B1884431
  · exact B1884435
  · exact B1884439
  · exact B1884443
  · exact B1884447
  · exact B1884451
  · exact B1884455
  · exact B1884459
  · exact B1884463
  · exact B1884467
  · exact B1884471
  · exact B1884475
  · exact B1884479
  · exact B1884483
  · exact B1884487
  · exact B1884491
  · exact B1884495
  · exact B1884499
  · exact B1884503
  · exact B1884507
  · exact B1884511
  · exact B1884515
  · exact B1884519
  · exact B1884523
  · exact B1884527
  · exact B1884531
  · exact B1884535
  · exact B1884539
  · exact B1884543
  · exact B1884547
  · exact B1884551
  · exact B1884555
  · exact B1884559
  · exact B1884563
  · exact B1884567
  · exact B1884571
  · exact B1884575
  · exact B1884579
  · exact B1884583
  · exact B1884587
  · exact B1884591
  · exact B1884595
  · exact B1884599
  · exact B1884603
  · exact B1884607
  · exact B1884611
  · exact B1884615
  · exact B1884619
  · exact B1884623
  · exact B1884627
  · exact B1884631
  · exact B1884635
  · exact B1884639
  · exact B1884643
  · exact B1884647
  · exact B1884651
  · exact B1884655
  · exact B1884659
  · exact B1884663
  · exact B1884667
  · exact B1884671
  · exact B1884675
  · exact B1884679
  · exact B1884683
  · exact B1884687
  · exact B1884691
  · exact B1884695
  · exact B1884699
  · exact B1884703
  · exact B1884707
  · exact B1884711
  · exact B1884715
  · exact B1884719
  · exact B1884723
  · exact B1884727
  · exact B1884731
  · exact B1884735
  · exact B1884739
  · exact B1884743
  · exact B1884747
  · exact B1884751
  · exact B1884755
  · exact B1884759
  · exact B1884763
  · exact B1884767
  · exact B1884771
  · exact B1884775
  · exact B1884779
  · exact B1884783
  · exact B1884787
  · exact B1884791
  · exact B1884795
  · exact B1884799
  · exact B1884803
  · exact B1884807
  · exact B1884811
  · exact B1884815
  · exact B1884819
  · exact B1884823
  · exact B1884827
  · exact B1884831
  · exact B1884835
  · exact B1884839
  · exact B1884843
  · exact B1884847
  · exact B1884851
  · exact B1884855
  · exact B1884859
  · exact B1884863
  · exact B1884867
  · exact B1884871
  · exact B1884875
  · exact B1884879
  · exact B1884883
  · exact B1884887
  · exact B1884891
  · exact B1884895
  · exact B1884899
  · exact B1884903
  · exact B1884907
  · exact B1884911
  · exact B1884915
  · exact B1884919
  · exact B1884923
  · exact B1884927
  · exact B1884931
  · exact B1884935
  · exact B1884939
  · exact B1884943
  · exact B1884947
  · exact B1884951
  · exact B1884955
  · exact B1884959
  · exact B1884963
  · exact B1884967
  · exact B1884971
  · exact B1884975
  · exact B1884979
  · exact B1884983
  · exact B1884987
  · exact B1884991
  · exact B1884995
  · exact B1884999
  · exact B1885003
  · exact B1885007
  · exact B1885011
  · exact B1885015
  · exact B1885019
  · exact B1885023
  · exact B1885027
  · exact B1885031
  · exact B1885035
  · exact B1885039
  · exact B1885043
  · exact B1885047
  · exact B1885051
  · exact B1885055
  · exact B1885059
  · exact B1885063
  · exact B1885067
  · exact B1885071
  · exact B1885075
  · exact B1885079
  · exact B1885083
  · exact B1885087
  · exact B1885091
  · exact B1885095
  · exact B1885099
  · exact B1885103
  · exact B1885107
  · exact B1885111
  · exact B1885115
  · exact B1885119
  · exact B1885123
  · exact B1885127
  · exact B1885131
  · exact B1885135
  · exact B1885139
  · exact B1885143
  · exact B1885147
  · exact B1885151
  · exact B1885155
  · exact B1885159
  · exact B1885163
  · exact B1885167
  · exact B1885171
  · exact B1885175
  · exact B1885179
  · exact B1885183
  · exact B1885187
  · exact B1885191
  · exact B1885195
  · exact B1885199
  · exact B1885203
  · exact B1885207
  · exact B1885211
  · exact B1885215
  · exact B1885219
  · exact B1885223
  · exact B1885227
  · exact B1885231
  · exact B1885235
  · exact B1885239
  · exact B1885243
  · exact B1885247
  · exact B1885251
  · exact B1885255
  · exact B1885259
  · exact B1885263
  · exact B1885267
  · exact B1885271
  · exact B1885275
  · exact B1885279
  · exact B1885283
  · exact B1885287
  · exact B1885291
  · exact B1885295
  · exact B1885299
  · exact B1885303
  · exact B1885307
  · exact B1885311
  · exact B1885315
  · exact B1885319
  · exact B1885323
  · exact B1885327
  · exact B1885331
  · exact B1885335
  · exact B1885339
  · exact B1885343
  · exact B1885347
  · exact B1885351
  · exact B1885355
  · exact B1885359
  · exact B1885363
  · exact B1885367
  · exact B1885371
  · exact B1885375
  · exact B1885379
  · exact B1885383
  · exact B1885387
  · exact B1885391
  · exact B1885395
  · exact B1885399
  · exact B1885403
  · exact B1885407
  · exact B1885411
  · exact B1885415
  · exact B1885419
  · exact B1885423
  · exact B1885427
  · exact B1885431
  · exact B1885435
theorem solution (m : ℕ) (hlo : 1883435 ≤ m) (hhi : m ≤ 1885435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 470858 ≤ j := by omega
    have hj2 : j ≤ 471358 := by omega
    have hb : Blo 1883435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
