-- Prove2me | solution 1 for syracuse_descends_range_2099435_2101435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:33.873875+00:00
-- url     : https://prove2.me/submissions/daa68f87-79b6-41f9-9359-3c874e19c7d4

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

theorem B2361865 : Blo 2099435 2361865 := bbase (se 2 (by rfl) ⟨885699, by rfl⟩ : syracuseStep 2361865 = 1771399) (by norm_num)
theorem B3149153 : Blo 2099435 3149153 := bstep (se 2 (by rfl) ⟨1180932, by rfl⟩ : syracuseStep 3149153 = 2361865) B2361865
theorem B2099435 : Blo 2099435 2099435 := bstep (se 1 (by rfl) ⟨1574576, by rfl⟩ : syracuseStep 2099435 = 3149153) B3149153
theorem B3071365 : Blo 2099435 3071365 := bbase (se 4 (by rfl) ⟨287940, by rfl⟩ : syracuseStep 3071365 = 575881) (by norm_num)
theorem B16380613 : Blo 2099435 16380613 := bstep (se 4 (by rfl) ⟨1535682, by rfl⟩ : syracuseStep 16380613 = 3071365) B3071365
theorem B87363269 : Blo 2099435 87363269 := bstep (se 4 (by rfl) ⟨8190306, by rfl⟩ : syracuseStep 87363269 = 16380613) B16380613
theorem B58242179 : Blo 2099435 58242179 := bstep (se 1 (by rfl) ⟨43681634, by rfl⟩ : syracuseStep 58242179 = 87363269) B87363269
theorem B38828119 : Blo 2099435 38828119 := bstep (se 1 (by rfl) ⟨29121089, by rfl⟩ : syracuseStep 38828119 = 58242179) B58242179
theorem B51770825 : Blo 2099435 51770825 := bstep (se 2 (by rfl) ⟨19414059, by rfl⟩ : syracuseStep 51770825 = 38828119) B38828119
theorem B34513883 : Blo 2099435 34513883 := bstep (se 1 (by rfl) ⟨25885412, by rfl⟩ : syracuseStep 34513883 = 51770825) B51770825
theorem B23009255 : Blo 2099435 23009255 := bstep (se 1 (by rfl) ⟨17256941, by rfl⟩ : syracuseStep 23009255 = 34513883) B34513883
theorem B15339503 : Blo 2099435 15339503 := bstep (se 1 (by rfl) ⟨11504627, by rfl⟩ : syracuseStep 15339503 = 23009255) B23009255
theorem B40905341 : Blo 2099435 40905341 := bstep (se 3 (by rfl) ⟨7669751, by rfl⟩ : syracuseStep 40905341 = 15339503) B15339503
theorem B27270227 : Blo 2099435 27270227 := bstep (se 1 (by rfl) ⟨20452670, by rfl⟩ : syracuseStep 27270227 = 40905341) B40905341
theorem B72720605 : Blo 2099435 72720605 := bstep (se 3 (by rfl) ⟨13635113, by rfl⟩ : syracuseStep 72720605 = 27270227) B27270227
theorem B48480403 : Blo 2099435 48480403 := bstep (se 1 (by rfl) ⟨36360302, by rfl⟩ : syracuseStep 48480403 = 72720605) B72720605
theorem B64640537 : Blo 2099435 64640537 := bstep (se 2 (by rfl) ⟨24240201, by rfl⟩ : syracuseStep 64640537 = 48480403) B48480403
theorem B43093691 : Blo 2099435 43093691 := bstep (se 1 (by rfl) ⟨32320268, by rfl⟩ : syracuseStep 43093691 = 64640537) B64640537
theorem B28729127 : Blo 2099435 28729127 := bstep (se 1 (by rfl) ⟨21546845, by rfl⟩ : syracuseStep 28729127 = 43093691) B43093691
theorem B76611005 : Blo 2099435 76611005 := bstep (se 3 (by rfl) ⟨14364563, by rfl⟩ : syracuseStep 76611005 = 28729127) B28729127
theorem B51074003 : Blo 2099435 51074003 := bstep (se 1 (by rfl) ⟨38305502, by rfl⟩ : syracuseStep 51074003 = 76611005) B76611005
theorem B34049335 : Blo 2099435 34049335 := bstep (se 1 (by rfl) ⟨25537001, by rfl⟩ : syracuseStep 34049335 = 51074003) B51074003
theorem B45399113 : Blo 2099435 45399113 := bstep (se 2 (by rfl) ⟨17024667, by rfl⟩ : syracuseStep 45399113 = 34049335) B34049335
theorem B30266075 : Blo 2099435 30266075 := bstep (se 1 (by rfl) ⟨22699556, by rfl⟩ : syracuseStep 30266075 = 45399113) B45399113
theorem B20177383 : Blo 2099435 20177383 := bstep (se 1 (by rfl) ⟨15133037, by rfl⟩ : syracuseStep 20177383 = 30266075) B30266075
theorem B26903177 : Blo 2099435 26903177 := bstep (se 2 (by rfl) ⟨10088691, by rfl⟩ : syracuseStep 26903177 = 20177383) B20177383
theorem B17935451 : Blo 2099435 17935451 := bstep (se 1 (by rfl) ⟨13451588, by rfl⟩ : syracuseStep 17935451 = 26903177) B26903177
theorem B11956967 : Blo 2099435 11956967 := bstep (se 1 (by rfl) ⟨8967725, by rfl⟩ : syracuseStep 11956967 = 17935451) B17935451
theorem B7971311 : Blo 2099435 7971311 := bstep (se 1 (by rfl) ⟨5978483, by rfl⟩ : syracuseStep 7971311 = 11956967) B11956967
theorem B5314207 : Blo 2099435 5314207 := bstep (se 1 (by rfl) ⟨3985655, by rfl⟩ : syracuseStep 5314207 = 7971311) B7971311
theorem B7085609 : Blo 2099435 7085609 := bstep (se 2 (by rfl) ⟨2657103, by rfl⟩ : syracuseStep 7085609 = 5314207) B5314207
theorem B4723739 : Blo 2099435 4723739 := bstep (se 1 (by rfl) ⟨3542804, by rfl⟩ : syracuseStep 4723739 = 7085609) B7085609
theorem B3149159 : Blo 2099435 3149159 := bstep (se 1 (by rfl) ⟨2361869, by rfl⟩ : syracuseStep 3149159 = 4723739) B4723739
theorem B2099439 : Blo 2099435 2099439 := bstep (se 1 (by rfl) ⟨1574579, by rfl⟩ : syracuseStep 2099439 = 3149159) B3149159
theorem B3149165 : Blo 2099435 3149165 := bbase (se 3 (by rfl) ⟨590468, by rfl⟩ : syracuseStep 3149165 = 1180937) (by norm_num)
theorem B2099443 : Blo 2099435 2099443 := bstep (se 1 (by rfl) ⟨1574582, by rfl⟩ : syracuseStep 2099443 = 3149165) B3149165
theorem B4723757 : Blo 2099435 4723757 := bbase (se 3 (by rfl) ⟨885704, by rfl⟩ : syracuseStep 4723757 = 1771409) (by norm_num)
theorem B3149171 : Blo 2099435 3149171 := bstep (se 1 (by rfl) ⟨2361878, by rfl⟩ : syracuseStep 3149171 = 4723757) B4723757
theorem B2099447 : Blo 2099435 2099447 := bstep (se 1 (by rfl) ⟨1574585, by rfl⟩ : syracuseStep 2099447 = 3149171) B3149171
theorem B13451669 : Blo 2099435 13451669 := bbase (se 6 (by rfl) ⟨315273, by rfl⟩ : syracuseStep 13451669 = 630547) (by norm_num)
theorem B8967779 : Blo 2099435 8967779 := bstep (se 1 (by rfl) ⟨6725834, by rfl⟩ : syracuseStep 8967779 = 13451669) B13451669
theorem B5978519 : Blo 2099435 5978519 := bstep (se 1 (by rfl) ⟨4483889, by rfl⟩ : syracuseStep 5978519 = 8967779) B8967779
theorem B3985679 : Blo 2099435 3985679 := bstep (se 1 (by rfl) ⟨2989259, by rfl⟩ : syracuseStep 3985679 = 5978519) B5978519
theorem B2657119 : Blo 2099435 2657119 := bstep (se 1 (by rfl) ⟨1992839, by rfl⟩ : syracuseStep 2657119 = 3985679) B3985679
theorem B3542825 : Blo 2099435 3542825 := bstep (se 2 (by rfl) ⟨1328559, by rfl⟩ : syracuseStep 3542825 = 2657119) B2657119
theorem B2361883 : Blo 2099435 2361883 := bstep (se 1 (by rfl) ⟨1771412, by rfl⟩ : syracuseStep 2361883 = 3542825) B3542825
theorem B3149177 : Blo 2099435 3149177 := bstep (se 2 (by rfl) ⟨1180941, by rfl⟩ : syracuseStep 3149177 = 2361883) B2361883
theorem B2099451 : Blo 2099435 2099451 := bstep (se 1 (by rfl) ⟨1574588, by rfl⟩ : syracuseStep 2099451 = 3149177) B3149177
theorem B6725845 : Blo 2099435 6725845 := bbase (se 7 (by rfl) ⟨78818, by rfl⟩ : syracuseStep 6725845 = 157637) (by norm_num)
theorem B35871173 : Blo 2099435 35871173 := bstep (se 4 (by rfl) ⟨3362922, by rfl⟩ : syracuseStep 35871173 = 6725845) B6725845
theorem B23914115 : Blo 2099435 23914115 := bstep (se 1 (by rfl) ⟨17935586, by rfl⟩ : syracuseStep 23914115 = 35871173) B35871173
theorem B15942743 : Blo 2099435 15942743 := bstep (se 1 (by rfl) ⟨11957057, by rfl⟩ : syracuseStep 15942743 = 23914115) B23914115
theorem B10628495 : Blo 2099435 10628495 := bstep (se 1 (by rfl) ⟨7971371, by rfl⟩ : syracuseStep 10628495 = 15942743) B15942743
theorem B7085663 : Blo 2099435 7085663 := bstep (se 1 (by rfl) ⟨5314247, by rfl⟩ : syracuseStep 7085663 = 10628495) B10628495
theorem B4723775 : Blo 2099435 4723775 := bstep (se 1 (by rfl) ⟨3542831, by rfl⟩ : syracuseStep 4723775 = 7085663) B7085663
theorem B3149183 : Blo 2099435 3149183 := bstep (se 1 (by rfl) ⟨2361887, by rfl⟩ : syracuseStep 3149183 = 4723775) B4723775
theorem B2099455 : Blo 2099435 2099455 := bstep (se 1 (by rfl) ⟨1574591, by rfl⟩ : syracuseStep 2099455 = 3149183) B3149183
theorem B3149189 : Blo 2099435 3149189 := bbase (se 4 (by rfl) ⟨295236, by rfl⟩ : syracuseStep 3149189 = 590473) (by norm_num)
theorem B2099459 : Blo 2099435 2099459 := bstep (se 1 (by rfl) ⟨1574594, by rfl⟩ : syracuseStep 2099459 = 3149189) B3149189
theorem B3542845 : Blo 2099435 3542845 := bbase (se 3 (by rfl) ⟨664283, by rfl⟩ : syracuseStep 3542845 = 1328567) (by norm_num)
theorem B4723793 : Blo 2099435 4723793 := bstep (se 2 (by rfl) ⟨1771422, by rfl⟩ : syracuseStep 4723793 = 3542845) B3542845
theorem B3149195 : Blo 2099435 3149195 := bstep (se 1 (by rfl) ⟨2361896, by rfl⟩ : syracuseStep 3149195 = 4723793) B4723793
theorem B2099463 : Blo 2099435 2099463 := bstep (se 1 (by rfl) ⟨1574597, by rfl⟩ : syracuseStep 2099463 = 3149195) B3149195
theorem B2361901 : Blo 2099435 2361901 := bbase (se 3 (by rfl) ⟨442856, by rfl⟩ : syracuseStep 2361901 = 885713) (by norm_num)
theorem B3149201 : Blo 2099435 3149201 := bstep (se 2 (by rfl) ⟨1180950, by rfl⟩ : syracuseStep 3149201 = 2361901) B2361901
theorem B2099467 : Blo 2099435 2099467 := bstep (se 1 (by rfl) ⟨1574600, by rfl⟩ : syracuseStep 2099467 = 3149201) B3149201
theorem B7085717 : Blo 2099435 7085717 := bbase (se 6 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 7085717 = 332143) (by norm_num)
theorem B4723811 : Blo 2099435 4723811 := bstep (se 1 (by rfl) ⟨3542858, by rfl⟩ : syracuseStep 4723811 = 7085717) B7085717
theorem B3149207 : Blo 2099435 3149207 := bstep (se 1 (by rfl) ⟨2361905, by rfl⟩ : syracuseStep 3149207 = 4723811) B4723811
theorem B2099471 : Blo 2099435 2099471 := bstep (se 1 (by rfl) ⟨1574603, by rfl⟩ : syracuseStep 2099471 = 3149207) B3149207
theorem B3149213 : Blo 2099435 3149213 := bbase (se 3 (by rfl) ⟨590477, by rfl⟩ : syracuseStep 3149213 = 1180955) (by norm_num)
theorem B2099475 : Blo 2099435 2099475 := bstep (se 1 (by rfl) ⟨1574606, by rfl⟩ : syracuseStep 2099475 = 3149213) B3149213
theorem B4723829 : Blo 2099435 4723829 := bbase (se 5 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 4723829 = 442859) (by norm_num)
theorem B3149219 : Blo 2099435 3149219 := bstep (se 1 (by rfl) ⟨2361914, by rfl⟩ : syracuseStep 3149219 = 4723829) B4723829
theorem B2099479 : Blo 2099435 2099479 := bstep (se 1 (by rfl) ⟨1574609, by rfl⟩ : syracuseStep 2099479 = 3149219) B3149219
theorem B17935829 : Blo 2099435 17935829 := bbase (se 7 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 17935829 = 420371) (by norm_num)
theorem B11957219 : Blo 2099435 11957219 := bstep (se 1 (by rfl) ⟨8967914, by rfl⟩ : syracuseStep 11957219 = 17935829) B17935829
theorem B7971479 : Blo 2099435 7971479 := bstep (se 1 (by rfl) ⟨5978609, by rfl⟩ : syracuseStep 7971479 = 11957219) B11957219
theorem B5314319 : Blo 2099435 5314319 := bstep (se 1 (by rfl) ⟨3985739, by rfl⟩ : syracuseStep 5314319 = 7971479) B7971479
theorem B3542879 : Blo 2099435 3542879 := bstep (se 1 (by rfl) ⟨2657159, by rfl⟩ : syracuseStep 3542879 = 5314319) B5314319
theorem B2361919 : Blo 2099435 2361919 := bstep (se 1 (by rfl) ⟨1771439, by rfl⟩ : syracuseStep 2361919 = 3542879) B3542879
theorem B3149225 : Blo 2099435 3149225 := bstep (se 2 (by rfl) ⟨1180959, by rfl⟩ : syracuseStep 3149225 = 2361919) B2361919
theorem B2099483 : Blo 2099435 2099483 := bstep (se 1 (by rfl) ⟨1574612, by rfl⟩ : syracuseStep 2099483 = 3149225) B3149225
theorem B7971493 : Blo 2099435 7971493 := bbase (se 4 (by rfl) ⟨747327, by rfl⟩ : syracuseStep 7971493 = 1494655) (by norm_num)
theorem B10628657 : Blo 2099435 10628657 := bstep (se 2 (by rfl) ⟨3985746, by rfl⟩ : syracuseStep 10628657 = 7971493) B7971493
theorem B7085771 : Blo 2099435 7085771 := bstep (se 1 (by rfl) ⟨5314328, by rfl⟩ : syracuseStep 7085771 = 10628657) B10628657
theorem B4723847 : Blo 2099435 4723847 := bstep (se 1 (by rfl) ⟨3542885, by rfl⟩ : syracuseStep 4723847 = 7085771) B7085771
theorem B3149231 : Blo 2099435 3149231 := bstep (se 1 (by rfl) ⟨2361923, by rfl⟩ : syracuseStep 3149231 = 4723847) B4723847
theorem B2099487 : Blo 2099435 2099487 := bstep (se 1 (by rfl) ⟨1574615, by rfl⟩ : syracuseStep 2099487 = 3149231) B3149231
theorem B3149237 : Blo 2099435 3149237 := bbase (se 5 (by rfl) ⟨147620, by rfl⟩ : syracuseStep 3149237 = 295241) (by norm_num)
theorem B2099491 : Blo 2099435 2099491 := bstep (se 1 (by rfl) ⟨1574618, by rfl⟩ : syracuseStep 2099491 = 3149237) B3149237
theorem B5314349 : Blo 2099435 5314349 := bbase (se 3 (by rfl) ⟨996440, by rfl⟩ : syracuseStep 5314349 = 1992881) (by norm_num)
theorem B3542899 : Blo 2099435 3542899 := bstep (se 1 (by rfl) ⟨2657174, by rfl⟩ : syracuseStep 3542899 = 5314349) B5314349
theorem B4723865 : Blo 2099435 4723865 := bstep (se 2 (by rfl) ⟨1771449, by rfl⟩ : syracuseStep 4723865 = 3542899) B3542899
theorem B3149243 : Blo 2099435 3149243 := bstep (se 1 (by rfl) ⟨2361932, by rfl⟩ : syracuseStep 3149243 = 4723865) B4723865
theorem B2099495 : Blo 2099435 2099495 := bstep (se 1 (by rfl) ⟨1574621, by rfl⟩ : syracuseStep 2099495 = 3149243) B3149243
theorem B2361937 : Blo 2099435 2361937 := bbase (se 2 (by rfl) ⟨885726, by rfl⟩ : syracuseStep 2361937 = 1771453) (by norm_num)
theorem B3149249 : Blo 2099435 3149249 := bstep (se 2 (by rfl) ⟨1180968, by rfl⟩ : syracuseStep 3149249 = 2361937) B2361937
theorem B2099499 : Blo 2099435 2099499 := bstep (se 1 (by rfl) ⟨1574624, by rfl⟩ : syracuseStep 2099499 = 3149249) B3149249
theorem B2989333 : Blo 2099435 2989333 := bbase (se 6 (by rfl) ⟨70062, by rfl⟩ : syracuseStep 2989333 = 140125) (by norm_num)
theorem B3985777 : Blo 2099435 3985777 := bstep (se 2 (by rfl) ⟨1494666, by rfl⟩ : syracuseStep 3985777 = 2989333) B2989333
theorem B5314369 : Blo 2099435 5314369 := bstep (se 2 (by rfl) ⟨1992888, by rfl⟩ : syracuseStep 5314369 = 3985777) B3985777
theorem B7085825 : Blo 2099435 7085825 := bstep (se 2 (by rfl) ⟨2657184, by rfl⟩ : syracuseStep 7085825 = 5314369) B5314369
theorem B4723883 : Blo 2099435 4723883 := bstep (se 1 (by rfl) ⟨3542912, by rfl⟩ : syracuseStep 4723883 = 7085825) B7085825
theorem B3149255 : Blo 2099435 3149255 := bstep (se 1 (by rfl) ⟨2361941, by rfl⟩ : syracuseStep 3149255 = 4723883) B4723883
theorem B2099503 : Blo 2099435 2099503 := bstep (se 1 (by rfl) ⟨1574627, by rfl⟩ : syracuseStep 2099503 = 3149255) B3149255
theorem B3149261 : Blo 2099435 3149261 := bbase (se 3 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 3149261 = 1180973) (by norm_num)
theorem B2099507 : Blo 2099435 2099507 := bstep (se 1 (by rfl) ⟨1574630, by rfl⟩ : syracuseStep 2099507 = 3149261) B3149261
theorem B4723901 : Blo 2099435 4723901 := bbase (se 3 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 4723901 = 1771463) (by norm_num)
theorem B3149267 : Blo 2099435 3149267 := bstep (se 1 (by rfl) ⟨2361950, by rfl⟩ : syracuseStep 3149267 = 4723901) B4723901
theorem B2099511 : Blo 2099435 2099511 := bstep (se 1 (by rfl) ⟨1574633, by rfl⟩ : syracuseStep 2099511 = 3149267) B3149267
theorem B3542933 : Blo 2099435 3542933 := bbase (se 6 (by rfl) ⟨83037, by rfl⟩ : syracuseStep 3542933 = 166075) (by norm_num)
theorem B2361955 : Blo 2099435 2361955 := bstep (se 1 (by rfl) ⟨1771466, by rfl⟩ : syracuseStep 2361955 = 3542933) B3542933
theorem B3149273 : Blo 2099435 3149273 := bstep (se 2 (by rfl) ⟨1180977, by rfl⟩ : syracuseStep 3149273 = 2361955) B2361955
theorem B2099515 : Blo 2099435 2099515 := bstep (se 1 (by rfl) ⟨1574636, by rfl⟩ : syracuseStep 2099515 = 3149273) B3149273
theorem B2522269 : Blo 2099435 2522269 := bbase (se 3 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 2522269 = 945851) (by norm_num)
theorem B13452101 : Blo 2099435 13452101 := bstep (se 4 (by rfl) ⟨1261134, by rfl⟩ : syracuseStep 13452101 = 2522269) B2522269
theorem B8968067 : Blo 2099435 8968067 := bstep (se 1 (by rfl) ⟨6726050, by rfl⟩ : syracuseStep 8968067 = 13452101) B13452101
theorem B5978711 : Blo 2099435 5978711 := bstep (se 1 (by rfl) ⟨4484033, by rfl⟩ : syracuseStep 5978711 = 8968067) B8968067
theorem B15943229 : Blo 2099435 15943229 := bstep (se 3 (by rfl) ⟨2989355, by rfl⟩ : syracuseStep 15943229 = 5978711) B5978711
theorem B10628819 : Blo 2099435 10628819 := bstep (se 1 (by rfl) ⟨7971614, by rfl⟩ : syracuseStep 10628819 = 15943229) B15943229
theorem B7085879 : Blo 2099435 7085879 := bstep (se 1 (by rfl) ⟨5314409, by rfl⟩ : syracuseStep 7085879 = 10628819) B10628819
theorem B4723919 : Blo 2099435 4723919 := bstep (se 1 (by rfl) ⟨3542939, by rfl⟩ : syracuseStep 4723919 = 7085879) B7085879
theorem B3149279 : Blo 2099435 3149279 := bstep (se 1 (by rfl) ⟨2361959, by rfl⟩ : syracuseStep 3149279 = 4723919) B4723919
theorem B2099519 : Blo 2099435 2099519 := bstep (se 1 (by rfl) ⟨1574639, by rfl⟩ : syracuseStep 2099519 = 3149279) B3149279
theorem B3149285 : Blo 2099435 3149285 := bbase (se 4 (by rfl) ⟨295245, by rfl⟩ : syracuseStep 3149285 = 590491) (by norm_num)
theorem B2099523 : Blo 2099435 2099523 := bstep (se 1 (by rfl) ⟨1574642, by rfl⟩ : syracuseStep 2099523 = 3149285) B3149285
theorem B43095509 : Blo 2099435 43095509 := bbase (se 7 (by rfl) ⟨505025, by rfl⟩ : syracuseStep 43095509 = 1010051) (by norm_num)
theorem B28730339 : Blo 2099435 28730339 := bstep (se 1 (by rfl) ⟨21547754, by rfl⟩ : syracuseStep 28730339 = 43095509) B43095509
theorem B19153559 : Blo 2099435 19153559 := bstep (se 1 (by rfl) ⟨14365169, by rfl⟩ : syracuseStep 19153559 = 28730339) B28730339
theorem B12769039 : Blo 2099435 12769039 := bstep (se 1 (by rfl) ⟨9576779, by rfl⟩ : syracuseStep 12769039 = 19153559) B19153559
theorem B17025385 : Blo 2099435 17025385 := bstep (se 2 (by rfl) ⟨6384519, by rfl⟩ : syracuseStep 17025385 = 12769039) B12769039
theorem B22700513 : Blo 2099435 22700513 := bstep (se 2 (by rfl) ⟨8512692, by rfl⟩ : syracuseStep 22700513 = 17025385) B17025385
theorem B15133675 : Blo 2099435 15133675 := bstep (se 1 (by rfl) ⟨11350256, by rfl⟩ : syracuseStep 15133675 = 22700513) B22700513
theorem B20178233 : Blo 2099435 20178233 := bstep (se 2 (by rfl) ⟨7566837, by rfl⟩ : syracuseStep 20178233 = 15133675) B15133675
theorem B13452155 : Blo 2099435 13452155 := bstep (se 1 (by rfl) ⟨10089116, by rfl⟩ : syracuseStep 13452155 = 20178233) B20178233
theorem B8968103 : Blo 2099435 8968103 := bstep (se 1 (by rfl) ⟨6726077, by rfl⟩ : syracuseStep 8968103 = 13452155) B13452155
theorem B5978735 : Blo 2099435 5978735 := bstep (se 1 (by rfl) ⟨4484051, by rfl⟩ : syracuseStep 5978735 = 8968103) B8968103
theorem B3985823 : Blo 2099435 3985823 := bstep (se 1 (by rfl) ⟨2989367, by rfl⟩ : syracuseStep 3985823 = 5978735) B5978735
theorem B2657215 : Blo 2099435 2657215 := bstep (se 1 (by rfl) ⟨1992911, by rfl⟩ : syracuseStep 2657215 = 3985823) B3985823
theorem B3542953 : Blo 2099435 3542953 := bstep (se 2 (by rfl) ⟨1328607, by rfl⟩ : syracuseStep 3542953 = 2657215) B2657215
theorem B4723937 : Blo 2099435 4723937 := bstep (se 2 (by rfl) ⟨1771476, by rfl⟩ : syracuseStep 4723937 = 3542953) B3542953
theorem B3149291 : Blo 2099435 3149291 := bstep (se 1 (by rfl) ⟨2361968, by rfl⟩ : syracuseStep 3149291 = 4723937) B4723937
theorem B2099527 : Blo 2099435 2099527 := bstep (se 1 (by rfl) ⟨1574645, by rfl⟩ : syracuseStep 2099527 = 3149291) B3149291
theorem B2361973 : Blo 2099435 2361973 := bbase (se 5 (by rfl) ⟨110717, by rfl⟩ : syracuseStep 2361973 = 221435) (by norm_num)
theorem B3149297 : Blo 2099435 3149297 := bstep (se 2 (by rfl) ⟨1180986, by rfl⟩ : syracuseStep 3149297 = 2361973) B2361973
theorem B2099531 : Blo 2099435 2099531 := bstep (se 1 (by rfl) ⟨1574648, by rfl⟩ : syracuseStep 2099531 = 3149297) B3149297
theorem B2657225 : Blo 2099435 2657225 := bbase (se 2 (by rfl) ⟨996459, by rfl⟩ : syracuseStep 2657225 = 1992919) (by norm_num)
theorem B7085933 : Blo 2099435 7085933 := bstep (se 3 (by rfl) ⟨1328612, by rfl⟩ : syracuseStep 7085933 = 2657225) B2657225
theorem B4723955 : Blo 2099435 4723955 := bstep (se 1 (by rfl) ⟨3542966, by rfl⟩ : syracuseStep 4723955 = 7085933) B7085933
theorem B3149303 : Blo 2099435 3149303 := bstep (se 1 (by rfl) ⟨2361977, by rfl⟩ : syracuseStep 3149303 = 4723955) B4723955
theorem B2099535 : Blo 2099435 2099535 := bstep (se 1 (by rfl) ⟨1574651, by rfl⟩ : syracuseStep 2099535 = 3149303) B3149303
theorem B3149309 : Blo 2099435 3149309 := bbase (se 3 (by rfl) ⟨590495, by rfl⟩ : syracuseStep 3149309 = 1180991) (by norm_num)
theorem B2099539 : Blo 2099435 2099539 := bstep (se 1 (by rfl) ⟨1574654, by rfl⟩ : syracuseStep 2099539 = 3149309) B3149309
theorem B4723973 : Blo 2099435 4723973 := bbase (se 4 (by rfl) ⟨442872, by rfl⟩ : syracuseStep 4723973 = 885745) (by norm_num)
theorem B3149315 : Blo 2099435 3149315 := bstep (se 1 (by rfl) ⟨2361986, by rfl⟩ : syracuseStep 3149315 = 4723973) B4723973
theorem B2099543 : Blo 2099435 2099543 := bstep (se 1 (by rfl) ⟨1574657, by rfl⟩ : syracuseStep 2099543 = 3149315) B3149315
theorem B3985861 : Blo 2099435 3985861 := bbase (se 4 (by rfl) ⟨373674, by rfl⟩ : syracuseStep 3985861 = 747349) (by norm_num)
theorem B5314481 : Blo 2099435 5314481 := bstep (se 2 (by rfl) ⟨1992930, by rfl⟩ : syracuseStep 5314481 = 3985861) B3985861
theorem B3542987 : Blo 2099435 3542987 := bstep (se 1 (by rfl) ⟨2657240, by rfl⟩ : syracuseStep 3542987 = 5314481) B5314481
theorem B2361991 : Blo 2099435 2361991 := bstep (se 1 (by rfl) ⟨1771493, by rfl⟩ : syracuseStep 2361991 = 3542987) B3542987
theorem B3149321 : Blo 2099435 3149321 := bstep (se 2 (by rfl) ⟨1180995, by rfl⟩ : syracuseStep 3149321 = 2361991) B2361991
theorem B2099547 : Blo 2099435 2099547 := bstep (se 1 (by rfl) ⟨1574660, by rfl⟩ : syracuseStep 2099547 = 3149321) B3149321
theorem B10628981 : Blo 2099435 10628981 := bbase (se 5 (by rfl) ⟨498233, by rfl⟩ : syracuseStep 10628981 = 996467) (by norm_num)
theorem B7085987 : Blo 2099435 7085987 := bstep (se 1 (by rfl) ⟨5314490, by rfl⟩ : syracuseStep 7085987 = 10628981) B10628981
theorem B4723991 : Blo 2099435 4723991 := bstep (se 1 (by rfl) ⟨3542993, by rfl⟩ : syracuseStep 4723991 = 7085987) B7085987
theorem B3149327 : Blo 2099435 3149327 := bstep (se 1 (by rfl) ⟨2361995, by rfl⟩ : syracuseStep 3149327 = 4723991) B4723991
theorem B2099551 : Blo 2099435 2099551 := bstep (se 1 (by rfl) ⟨1574663, by rfl⟩ : syracuseStep 2099551 = 3149327) B3149327
theorem B3149333 : Blo 2099435 3149333 := bbase (se 6 (by rfl) ⟨73812, by rfl⟩ : syracuseStep 3149333 = 147625) (by norm_num)
theorem B2099555 : Blo 2099435 2099555 := bstep (se 1 (by rfl) ⟨1574666, by rfl⟩ : syracuseStep 2099555 = 3149333) B3149333
theorem B10089269 : Blo 2099435 10089269 := bbase (se 5 (by rfl) ⟨472934, by rfl⟩ : syracuseStep 10089269 = 945869) (by norm_num)
theorem B6726179 : Blo 2099435 6726179 := bstep (se 1 (by rfl) ⟨5044634, by rfl⟩ : syracuseStep 6726179 = 10089269) B10089269
theorem B17936477 : Blo 2099435 17936477 := bstep (se 3 (by rfl) ⟨3363089, by rfl⟩ : syracuseStep 17936477 = 6726179) B6726179
theorem B11957651 : Blo 2099435 11957651 := bstep (se 1 (by rfl) ⟨8968238, by rfl⟩ : syracuseStep 11957651 = 17936477) B17936477
theorem B7971767 : Blo 2099435 7971767 := bstep (se 1 (by rfl) ⟨5978825, by rfl⟩ : syracuseStep 7971767 = 11957651) B11957651
theorem B5314511 : Blo 2099435 5314511 := bstep (se 1 (by rfl) ⟨3985883, by rfl⟩ : syracuseStep 5314511 = 7971767) B7971767
theorem B3543007 : Blo 2099435 3543007 := bstep (se 1 (by rfl) ⟨2657255, by rfl⟩ : syracuseStep 3543007 = 5314511) B5314511
theorem B4724009 : Blo 2099435 4724009 := bstep (se 2 (by rfl) ⟨1771503, by rfl⟩ : syracuseStep 4724009 = 3543007) B3543007
theorem B3149339 : Blo 2099435 3149339 := bstep (se 1 (by rfl) ⟨2362004, by rfl⟩ : syracuseStep 3149339 = 4724009) B4724009
theorem B2099559 : Blo 2099435 2099559 := bstep (se 1 (by rfl) ⟨1574669, by rfl⟩ : syracuseStep 2099559 = 3149339) B3149339
theorem B2362009 : Blo 2099435 2362009 := bbase (se 2 (by rfl) ⟨885753, by rfl⟩ : syracuseStep 2362009 = 1771507) (by norm_num)
theorem B3149345 : Blo 2099435 3149345 := bstep (se 2 (by rfl) ⟨1181004, by rfl⟩ : syracuseStep 3149345 = 2362009) B2362009
theorem B2099563 : Blo 2099435 2099563 := bstep (se 1 (by rfl) ⟨1574672, by rfl⟩ : syracuseStep 2099563 = 3149345) B3149345
theorem B7971797 : Blo 2099435 7971797 := bbase (se 7 (by rfl) ⟨93419, by rfl⟩ : syracuseStep 7971797 = 186839) (by norm_num)
theorem B5314531 : Blo 2099435 5314531 := bstep (se 1 (by rfl) ⟨3985898, by rfl⟩ : syracuseStep 5314531 = 7971797) B7971797
theorem B7086041 : Blo 2099435 7086041 := bstep (se 2 (by rfl) ⟨2657265, by rfl⟩ : syracuseStep 7086041 = 5314531) B5314531
theorem B4724027 : Blo 2099435 4724027 := bstep (se 1 (by rfl) ⟨3543020, by rfl⟩ : syracuseStep 4724027 = 7086041) B7086041
theorem B3149351 : Blo 2099435 3149351 := bstep (se 1 (by rfl) ⟨2362013, by rfl⟩ : syracuseStep 3149351 = 4724027) B4724027
theorem B2099567 : Blo 2099435 2099567 := bstep (se 1 (by rfl) ⟨1574675, by rfl⟩ : syracuseStep 2099567 = 3149351) B3149351
theorem B3149357 : Blo 2099435 3149357 := bbase (se 3 (by rfl) ⟨590504, by rfl⟩ : syracuseStep 3149357 = 1181009) (by norm_num)
theorem B2099571 : Blo 2099435 2099571 := bstep (se 1 (by rfl) ⟨1574678, by rfl⟩ : syracuseStep 2099571 = 3149357) B3149357
theorem B4724045 : Blo 2099435 4724045 := bbase (se 3 (by rfl) ⟨885758, by rfl⟩ : syracuseStep 4724045 = 1771517) (by norm_num)
theorem B3149363 : Blo 2099435 3149363 := bstep (se 1 (by rfl) ⟨2362022, by rfl⟩ : syracuseStep 3149363 = 4724045) B4724045
theorem B2099575 : Blo 2099435 2099575 := bstep (se 1 (by rfl) ⟨1574681, by rfl⟩ : syracuseStep 2099575 = 3149363) B3149363
theorem B2657281 : Blo 2099435 2657281 := bbase (se 2 (by rfl) ⟨996480, by rfl⟩ : syracuseStep 2657281 = 1992961) (by norm_num)
theorem B3543041 : Blo 2099435 3543041 := bstep (se 2 (by rfl) ⟨1328640, by rfl⟩ : syracuseStep 3543041 = 2657281) B2657281
theorem B2362027 : Blo 2099435 2362027 := bstep (se 1 (by rfl) ⟨1771520, by rfl⟩ : syracuseStep 2362027 = 3543041) B3543041
theorem B3149369 : Blo 2099435 3149369 := bstep (se 2 (by rfl) ⟨1181013, by rfl⟩ : syracuseStep 3149369 = 2362027) B2362027
theorem B2099579 : Blo 2099435 2099579 := bstep (se 1 (by rfl) ⟨1574684, by rfl⟩ : syracuseStep 2099579 = 3149369) B3149369
theorem B2242085 : Blo 2099435 2242085 := bbase (se 4 (by rfl) ⟨210195, by rfl⟩ : syracuseStep 2242085 = 420391) (by norm_num)
theorem B23915573 : Blo 2099435 23915573 := bstep (se 5 (by rfl) ⟨1121042, by rfl⟩ : syracuseStep 23915573 = 2242085) B2242085
theorem B15943715 : Blo 2099435 15943715 := bstep (se 1 (by rfl) ⟨11957786, by rfl⟩ : syracuseStep 15943715 = 23915573) B23915573
theorem B10629143 : Blo 2099435 10629143 := bstep (se 1 (by rfl) ⟨7971857, by rfl⟩ : syracuseStep 10629143 = 15943715) B15943715
theorem B7086095 : Blo 2099435 7086095 := bstep (se 1 (by rfl) ⟨5314571, by rfl⟩ : syracuseStep 7086095 = 10629143) B10629143
theorem B4724063 : Blo 2099435 4724063 := bstep (se 1 (by rfl) ⟨3543047, by rfl⟩ : syracuseStep 4724063 = 7086095) B7086095
theorem B3149375 : Blo 2099435 3149375 := bstep (se 1 (by rfl) ⟨2362031, by rfl⟩ : syracuseStep 3149375 = 4724063) B4724063
theorem B2099583 : Blo 2099435 2099583 := bstep (se 1 (by rfl) ⟨1574687, by rfl⟩ : syracuseStep 2099583 = 3149375) B3149375
theorem B3149381 : Blo 2099435 3149381 := bbase (se 4 (by rfl) ⟨295254, by rfl⟩ : syracuseStep 3149381 = 590509) (by norm_num)
theorem B2099587 : Blo 2099435 2099587 := bstep (se 1 (by rfl) ⟨1574690, by rfl⟩ : syracuseStep 2099587 = 3149381) B3149381
theorem B3543061 : Blo 2099435 3543061 := bbase (se 6 (by rfl) ⟨83040, by rfl⟩ : syracuseStep 3543061 = 166081) (by norm_num)
theorem B4724081 : Blo 2099435 4724081 := bstep (se 2 (by rfl) ⟨1771530, by rfl⟩ : syracuseStep 4724081 = 3543061) B3543061
theorem B3149387 : Blo 2099435 3149387 := bstep (se 1 (by rfl) ⟨2362040, by rfl⟩ : syracuseStep 3149387 = 4724081) B4724081
theorem B2099591 : Blo 2099435 2099591 := bstep (se 1 (by rfl) ⟨1574693, by rfl⟩ : syracuseStep 2099591 = 3149387) B3149387
theorem B2362045 : Blo 2099435 2362045 := bbase (se 3 (by rfl) ⟨442883, by rfl⟩ : syracuseStep 2362045 = 885767) (by norm_num)
theorem B3149393 : Blo 2099435 3149393 := bstep (se 2 (by rfl) ⟨1181022, by rfl⟩ : syracuseStep 3149393 = 2362045) B2362045
theorem B2099595 : Blo 2099435 2099595 := bstep (se 1 (by rfl) ⟨1574696, by rfl⟩ : syracuseStep 2099595 = 3149393) B3149393
theorem B7086149 : Blo 2099435 7086149 := bbase (se 4 (by rfl) ⟨664326, by rfl⟩ : syracuseStep 7086149 = 1328653) (by norm_num)
theorem B4724099 : Blo 2099435 4724099 := bstep (se 1 (by rfl) ⟨3543074, by rfl⟩ : syracuseStep 4724099 = 7086149) B7086149
theorem B3149399 : Blo 2099435 3149399 := bstep (se 1 (by rfl) ⟨2362049, by rfl⟩ : syracuseStep 3149399 = 4724099) B4724099
theorem B2099599 : Blo 2099435 2099599 := bstep (se 1 (by rfl) ⟨1574699, by rfl⟩ : syracuseStep 2099599 = 3149399) B3149399
theorem B3149405 : Blo 2099435 3149405 := bbase (se 3 (by rfl) ⟨590513, by rfl⟩ : syracuseStep 3149405 = 1181027) (by norm_num)
theorem B2099603 : Blo 2099435 2099603 := bstep (se 1 (by rfl) ⟨1574702, by rfl⟩ : syracuseStep 2099603 = 3149405) B3149405
theorem B4724117 : Blo 2099435 4724117 := bbase (se 6 (by rfl) ⟨110721, by rfl⟩ : syracuseStep 4724117 = 221443) (by norm_num)
theorem B3149411 : Blo 2099435 3149411 := bstep (se 1 (by rfl) ⟨2362058, by rfl⟩ : syracuseStep 3149411 = 4724117) B4724117
theorem B2099607 : Blo 2099435 2099607 := bstep (se 1 (by rfl) ⟨1574705, by rfl⟩ : syracuseStep 2099607 = 3149411) B3149411
theorem B7567141 : Blo 2099435 7567141 := bbase (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) (by norm_num)
theorem B10089521 : Blo 2099435 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B6726347 : Blo 2099435 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B4484231 : Blo 2099435 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B2989487 : Blo 2099435 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B7971965 : Blo 2099435 7971965 := bstep (se 3 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 7971965 = 2989487) B2989487
theorem B5314643 : Blo 2099435 5314643 := bstep (se 1 (by rfl) ⟨3985982, by rfl⟩ : syracuseStep 5314643 = 7971965) B7971965
theorem B3543095 : Blo 2099435 3543095 := bstep (se 1 (by rfl) ⟨2657321, by rfl⟩ : syracuseStep 3543095 = 5314643) B5314643
theorem B2362063 : Blo 2099435 2362063 := bstep (se 1 (by rfl) ⟨1771547, by rfl⟩ : syracuseStep 2362063 = 3543095) B3543095
theorem B3149417 : Blo 2099435 3149417 := bstep (se 2 (by rfl) ⟨1181031, by rfl⟩ : syracuseStep 3149417 = 2362063) B2362063
theorem B2099611 : Blo 2099435 2099611 := bstep (se 1 (by rfl) ⟨1574708, by rfl⟩ : syracuseStep 2099611 = 3149417) B3149417
theorem B4256525 : Blo 2099435 4256525 := bbase (se 3 (by rfl) ⟨798098, by rfl⟩ : syracuseStep 4256525 = 1596197) (by norm_num)
theorem B2837683 : Blo 2099435 2837683 := bstep (se 1 (by rfl) ⟨2128262, by rfl⟩ : syracuseStep 2837683 = 4256525) B4256525
theorem B3783577 : Blo 2099435 3783577 := bstep (se 2 (by rfl) ⟨1418841, by rfl⟩ : syracuseStep 3783577 = 2837683) B2837683
theorem B5044769 : Blo 2099435 5044769 := bstep (se 2 (by rfl) ⟨1891788, by rfl⟩ : syracuseStep 5044769 = 3783577) B3783577
theorem B3363179 : Blo 2099435 3363179 := bstep (se 1 (by rfl) ⟨2522384, by rfl⟩ : syracuseStep 3363179 = 5044769) B5044769
theorem B8968477 : Blo 2099435 8968477 := bstep (se 3 (by rfl) ⟨1681589, by rfl⟩ : syracuseStep 8968477 = 3363179) B3363179
theorem B11957969 : Blo 2099435 11957969 := bstep (se 2 (by rfl) ⟨4484238, by rfl⟩ : syracuseStep 11957969 = 8968477) B8968477
theorem B7971979 : Blo 2099435 7971979 := bstep (se 1 (by rfl) ⟨5978984, by rfl⟩ : syracuseStep 7971979 = 11957969) B11957969
theorem B10629305 : Blo 2099435 10629305 := bstep (se 2 (by rfl) ⟨3985989, by rfl⟩ : syracuseStep 10629305 = 7971979) B7971979
theorem B7086203 : Blo 2099435 7086203 := bstep (se 1 (by rfl) ⟨5314652, by rfl⟩ : syracuseStep 7086203 = 10629305) B10629305
theorem B4724135 : Blo 2099435 4724135 := bstep (se 1 (by rfl) ⟨3543101, by rfl⟩ : syracuseStep 4724135 = 7086203) B7086203
theorem B3149423 : Blo 2099435 3149423 := bstep (se 1 (by rfl) ⟨2362067, by rfl⟩ : syracuseStep 3149423 = 4724135) B4724135
theorem B2099615 : Blo 2099435 2099615 := bstep (se 1 (by rfl) ⟨1574711, by rfl⟩ : syracuseStep 2099615 = 3149423) B3149423
theorem B3149429 : Blo 2099435 3149429 := bbase (se 5 (by rfl) ⟨147629, by rfl⟩ : syracuseStep 3149429 = 295259) (by norm_num)
theorem B2099619 : Blo 2099435 2099619 := bstep (se 1 (by rfl) ⟨1574714, by rfl⟩ : syracuseStep 2099619 = 3149429) B3149429
theorem B3986005 : Blo 2099435 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B5314673 : Blo 2099435 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B3543115 : Blo 2099435 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B4724153 : Blo 2099435 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B3149435 : Blo 2099435 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B2099623 : Blo 2099435 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B2362081 : Blo 2099435 2362081 := bbase (se 2 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 2362081 = 1771561) (by norm_num)
theorem B3149441 : Blo 2099435 3149441 := bstep (se 2 (by rfl) ⟨1181040, by rfl⟩ : syracuseStep 3149441 = 2362081) B2362081
theorem B2099627 : Blo 2099435 2099627 := bstep (se 1 (by rfl) ⟨1574720, by rfl⟩ : syracuseStep 2099627 = 3149441) B3149441
theorem B5314693 : Blo 2099435 5314693 := bbase (se 4 (by rfl) ⟨498252, by rfl⟩ : syracuseStep 5314693 = 996505) (by norm_num)
theorem B7086257 : Blo 2099435 7086257 := bstep (se 2 (by rfl) ⟨2657346, by rfl⟩ : syracuseStep 7086257 = 5314693) B5314693
theorem B4724171 : Blo 2099435 4724171 := bstep (se 1 (by rfl) ⟨3543128, by rfl⟩ : syracuseStep 4724171 = 7086257) B7086257
theorem B3149447 : Blo 2099435 3149447 := bstep (se 1 (by rfl) ⟨2362085, by rfl⟩ : syracuseStep 3149447 = 4724171) B4724171
theorem B2099631 : Blo 2099435 2099631 := bstep (se 1 (by rfl) ⟨1574723, by rfl⟩ : syracuseStep 2099631 = 3149447) B3149447
theorem B3149453 : Blo 2099435 3149453 := bbase (se 3 (by rfl) ⟨590522, by rfl⟩ : syracuseStep 3149453 = 1181045) (by norm_num)
theorem B2099635 : Blo 2099435 2099635 := bstep (se 1 (by rfl) ⟨1574726, by rfl⟩ : syracuseStep 2099635 = 3149453) B3149453
theorem B4724189 : Blo 2099435 4724189 := bbase (se 3 (by rfl) ⟨885785, by rfl⟩ : syracuseStep 4724189 = 1771571) (by norm_num)
theorem B3149459 : Blo 2099435 3149459 := bstep (se 1 (by rfl) ⟨2362094, by rfl⟩ : syracuseStep 3149459 = 4724189) B4724189
theorem B2099639 : Blo 2099435 2099639 := bstep (se 1 (by rfl) ⟨1574729, by rfl⟩ : syracuseStep 2099639 = 3149459) B3149459
theorem B3543149 : Blo 2099435 3543149 := bbase (se 3 (by rfl) ⟨664340, by rfl⟩ : syracuseStep 3543149 = 1328681) (by norm_num)
theorem B2362099 : Blo 2099435 2362099 := bstep (se 1 (by rfl) ⟨1771574, by rfl⟩ : syracuseStep 2362099 = 3543149) B3543149
theorem B3149465 : Blo 2099435 3149465 := bstep (se 2 (by rfl) ⟨1181049, by rfl⟩ : syracuseStep 3149465 = 2362099) B2362099
theorem B2099643 : Blo 2099435 2099643 := bstep (se 1 (by rfl) ⟨1574732, by rfl⟩ : syracuseStep 2099643 = 3149465) B3149465
theorem B20179381 : Blo 2099435 20179381 := bbase (se 5 (by rfl) ⟨945908, by rfl⟩ : syracuseStep 20179381 = 1891817) (by norm_num)
theorem B26905841 : Blo 2099435 26905841 := bstep (se 2 (by rfl) ⟨10089690, by rfl⟩ : syracuseStep 26905841 = 20179381) B20179381
theorem B17937227 : Blo 2099435 17937227 := bstep (se 1 (by rfl) ⟨13452920, by rfl⟩ : syracuseStep 17937227 = 26905841) B26905841
theorem B11958151 : Blo 2099435 11958151 := bstep (se 1 (by rfl) ⟨8968613, by rfl⟩ : syracuseStep 11958151 = 17937227) B17937227
theorem B15944201 : Blo 2099435 15944201 := bstep (se 2 (by rfl) ⟨5979075, by rfl⟩ : syracuseStep 15944201 = 11958151) B11958151
theorem B10629467 : Blo 2099435 10629467 := bstep (se 1 (by rfl) ⟨7972100, by rfl⟩ : syracuseStep 10629467 = 15944201) B15944201
theorem B7086311 : Blo 2099435 7086311 := bstep (se 1 (by rfl) ⟨5314733, by rfl⟩ : syracuseStep 7086311 = 10629467) B10629467
theorem B4724207 : Blo 2099435 4724207 := bstep (se 1 (by rfl) ⟨3543155, by rfl⟩ : syracuseStep 4724207 = 7086311) B7086311
theorem B3149471 : Blo 2099435 3149471 := bstep (se 1 (by rfl) ⟨2362103, by rfl⟩ : syracuseStep 3149471 = 4724207) B4724207
theorem B2099647 : Blo 2099435 2099647 := bstep (se 1 (by rfl) ⟨1574735, by rfl⟩ : syracuseStep 2099647 = 3149471) B3149471
theorem B3149477 : Blo 2099435 3149477 := bbase (se 4 (by rfl) ⟨295263, by rfl⟩ : syracuseStep 3149477 = 590527) (by norm_num)
theorem B2099651 : Blo 2099435 2099651 := bstep (se 1 (by rfl) ⟨1574738, by rfl⟩ : syracuseStep 2099651 = 3149477) B3149477
theorem B2657377 : Blo 2099435 2657377 := bbase (se 2 (by rfl) ⟨996516, by rfl⟩ : syracuseStep 2657377 = 1993033) (by norm_num)
theorem B3543169 : Blo 2099435 3543169 := bstep (se 2 (by rfl) ⟨1328688, by rfl⟩ : syracuseStep 3543169 = 2657377) B2657377
theorem B4724225 : Blo 2099435 4724225 := bstep (se 2 (by rfl) ⟨1771584, by rfl⟩ : syracuseStep 4724225 = 3543169) B3543169
theorem B3149483 : Blo 2099435 3149483 := bstep (se 1 (by rfl) ⟨2362112, by rfl⟩ : syracuseStep 3149483 = 4724225) B4724225
theorem B2099655 : Blo 2099435 2099655 := bstep (se 1 (by rfl) ⟨1574741, by rfl⟩ : syracuseStep 2099655 = 3149483) B3149483
theorem B2362117 : Blo 2099435 2362117 := bbase (se 4 (by rfl) ⟨221448, by rfl⟩ : syracuseStep 2362117 = 442897) (by norm_num)
theorem B3149489 : Blo 2099435 3149489 := bstep (se 2 (by rfl) ⟨1181058, by rfl⟩ : syracuseStep 3149489 = 2362117) B2362117
theorem B2099659 : Blo 2099435 2099659 := bstep (se 1 (by rfl) ⟨1574744, by rfl⟩ : syracuseStep 2099659 = 3149489) B3149489
theorem B2837749 : Blo 2099435 2837749 := bbase (se 5 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 2837749 = 266039) (by norm_num)
theorem B3783665 : Blo 2099435 3783665 := bstep (se 2 (by rfl) ⟨1418874, by rfl⟩ : syracuseStep 3783665 = 2837749) B2837749
theorem B2522443 : Blo 2099435 2522443 := bstep (se 1 (by rfl) ⟨1891832, by rfl⟩ : syracuseStep 2522443 = 3783665) B3783665
theorem B3363257 : Blo 2099435 3363257 := bstep (se 2 (by rfl) ⟨1261221, by rfl⟩ : syracuseStep 3363257 = 2522443) B2522443
theorem B2242171 : Blo 2099435 2242171 := bstep (se 1 (by rfl) ⟨1681628, by rfl⟩ : syracuseStep 2242171 = 3363257) B3363257
theorem B2989561 : Blo 2099435 2989561 := bstep (se 2 (by rfl) ⟨1121085, by rfl⟩ : syracuseStep 2989561 = 2242171) B2242171
theorem B3986081 : Blo 2099435 3986081 := bstep (se 2 (by rfl) ⟨1494780, by rfl⟩ : syracuseStep 3986081 = 2989561) B2989561
theorem B2657387 : Blo 2099435 2657387 := bstep (se 1 (by rfl) ⟨1993040, by rfl⟩ : syracuseStep 2657387 = 3986081) B3986081
theorem B7086365 : Blo 2099435 7086365 := bstep (se 3 (by rfl) ⟨1328693, by rfl⟩ : syracuseStep 7086365 = 2657387) B2657387
theorem B4724243 : Blo 2099435 4724243 := bstep (se 1 (by rfl) ⟨3543182, by rfl⟩ : syracuseStep 4724243 = 7086365) B7086365
theorem B3149495 : Blo 2099435 3149495 := bstep (se 1 (by rfl) ⟨2362121, by rfl⟩ : syracuseStep 3149495 = 4724243) B4724243
theorem B2099663 : Blo 2099435 2099663 := bstep (se 1 (by rfl) ⟨1574747, by rfl⟩ : syracuseStep 2099663 = 3149495) B3149495
theorem B3149501 : Blo 2099435 3149501 := bbase (se 3 (by rfl) ⟨590531, by rfl⟩ : syracuseStep 3149501 = 1181063) (by norm_num)
theorem B2099667 : Blo 2099435 2099667 := bstep (se 1 (by rfl) ⟨1574750, by rfl⟩ : syracuseStep 2099667 = 3149501) B3149501
theorem B4724261 : Blo 2099435 4724261 := bbase (se 4 (by rfl) ⟨442899, by rfl⟩ : syracuseStep 4724261 = 885799) (by norm_num)
theorem B3149507 : Blo 2099435 3149507 := bstep (se 1 (by rfl) ⟨2362130, by rfl⟩ : syracuseStep 3149507 = 4724261) B4724261
theorem B2099671 : Blo 2099435 2099671 := bstep (se 1 (by rfl) ⟨1574753, by rfl⟩ : syracuseStep 2099671 = 3149507) B3149507
theorem B5314805 : Blo 2099435 5314805 := bbase (se 5 (by rfl) ⟨249131, by rfl⟩ : syracuseStep 5314805 = 498263) (by norm_num)
theorem B3543203 : Blo 2099435 3543203 := bstep (se 1 (by rfl) ⟨2657402, by rfl⟩ : syracuseStep 3543203 = 5314805) B5314805
theorem B2362135 : Blo 2099435 2362135 := bstep (se 1 (by rfl) ⟨1771601, by rfl⟩ : syracuseStep 2362135 = 3543203) B3543203
theorem B3149513 : Blo 2099435 3149513 := bstep (se 2 (by rfl) ⟨1181067, by rfl⟩ : syracuseStep 3149513 = 2362135) B2362135
theorem B2099675 : Blo 2099435 2099675 := bstep (se 1 (by rfl) ⟨1574756, by rfl⟩ : syracuseStep 2099675 = 3149513) B3149513
theorem B5610853 : Blo 2099435 5610853 := bbase (se 4 (by rfl) ⟨526017, by rfl⟩ : syracuseStep 5610853 = 1052035) (by norm_num)
theorem B29924549 : Blo 2099435 29924549 := bstep (se 4 (by rfl) ⟨2805426, by rfl⟩ : syracuseStep 29924549 = 5610853) B5610853
theorem B19949699 : Blo 2099435 19949699 := bstep (se 1 (by rfl) ⟨14962274, by rfl⟩ : syracuseStep 19949699 = 29924549) B29924549
theorem B53199197 : Blo 2099435 53199197 := bstep (se 3 (by rfl) ⟨9974849, by rfl⟩ : syracuseStep 53199197 = 19949699) B19949699
theorem B35466131 : Blo 2099435 35466131 := bstep (se 1 (by rfl) ⟨26599598, by rfl⟩ : syracuseStep 35466131 = 53199197) B53199197
theorem B94576349 : Blo 2099435 94576349 := bstep (se 3 (by rfl) ⟨17733065, by rfl⟩ : syracuseStep 94576349 = 35466131) B35466131
theorem B63050899 : Blo 2099435 63050899 := bstep (se 1 (by rfl) ⟨47288174, by rfl⟩ : syracuseStep 63050899 = 94576349) B94576349
theorem B84067865 : Blo 2099435 84067865 := bstep (se 2 (by rfl) ⟨31525449, by rfl⟩ : syracuseStep 84067865 = 63050899) B63050899
theorem B56045243 : Blo 2099435 56045243 := bstep (se 1 (by rfl) ⟨42033932, by rfl⟩ : syracuseStep 56045243 = 84067865) B84067865
theorem B149453981 : Blo 2099435 149453981 := bstep (se 3 (by rfl) ⟨28022621, by rfl⟩ : syracuseStep 149453981 = 56045243) B56045243
theorem B99635987 : Blo 2099435 99635987 := bstep (se 1 (by rfl) ⟨74726990, by rfl⟩ : syracuseStep 99635987 = 149453981) B149453981
theorem B265695965 : Blo 2099435 265695965 := bstep (se 3 (by rfl) ⟨49817993, by rfl⟩ : syracuseStep 265695965 = 99635987) B99635987
theorem B177130643 : Blo 2099435 177130643 := bstep (se 1 (by rfl) ⟨132847982, by rfl⟩ : syracuseStep 177130643 = 265695965) B265695965
theorem B472348381 : Blo 2099435 472348381 := bstep (se 3 (by rfl) ⟨88565321, by rfl⟩ : syracuseStep 472348381 = 177130643) B177130643
theorem B629797841 : Blo 2099435 629797841 := bstep (se 2 (by rfl) ⟨236174190, by rfl⟩ : syracuseStep 629797841 = 472348381) B472348381
theorem B419865227 : Blo 2099435 419865227 := bstep (se 1 (by rfl) ⟨314898920, by rfl⟩ : syracuseStep 419865227 = 629797841) B629797841
theorem B279910151 : Blo 2099435 279910151 := bstep (se 1 (by rfl) ⟨209932613, by rfl⟩ : syracuseStep 279910151 = 419865227) B419865227
theorem B186606767 : Blo 2099435 186606767 := bstep (se 1 (by rfl) ⟨139955075, by rfl⟩ : syracuseStep 186606767 = 279910151) B279910151
theorem B124404511 : Blo 2099435 124404511 := bstep (se 1 (by rfl) ⟨93303383, by rfl⟩ : syracuseStep 124404511 = 186606767) B186606767
theorem B165872681 : Blo 2099435 165872681 := bstep (se 2 (by rfl) ⟨62202255, by rfl⟩ : syracuseStep 165872681 = 124404511) B124404511
theorem B110581787 : Blo 2099435 110581787 := bstep (se 1 (by rfl) ⟨82936340, by rfl⟩ : syracuseStep 110581787 = 165872681) B165872681
theorem B73721191 : Blo 2099435 73721191 := bstep (se 1 (by rfl) ⟨55290893, by rfl⟩ : syracuseStep 73721191 = 110581787) B110581787
theorem B98294921 : Blo 2099435 98294921 := bstep (se 2 (by rfl) ⟨36860595, by rfl⟩ : syracuseStep 98294921 = 73721191) B73721191
theorem B65529947 : Blo 2099435 65529947 := bstep (se 1 (by rfl) ⟨49147460, by rfl⟩ : syracuseStep 65529947 = 98294921) B98294921
theorem B43686631 : Blo 2099435 43686631 := bstep (se 1 (by rfl) ⟨32764973, by rfl⟩ : syracuseStep 43686631 = 65529947) B65529947
theorem B58248841 : Blo 2099435 58248841 := bstep (se 2 (by rfl) ⟨21843315, by rfl⟩ : syracuseStep 58248841 = 43686631) B43686631
theorem B77665121 : Blo 2099435 77665121 := bstep (se 2 (by rfl) ⟨29124420, by rfl⟩ : syracuseStep 77665121 = 58248841) B58248841
theorem B51776747 : Blo 2099435 51776747 := bstep (se 1 (by rfl) ⟨38832560, by rfl⟩ : syracuseStep 51776747 = 77665121) B77665121
theorem B34517831 : Blo 2099435 34517831 := bstep (se 1 (by rfl) ⟨25888373, by rfl⟩ : syracuseStep 34517831 = 51776747) B51776747
theorem B368190197 : Blo 2099435 368190197 := bstep (se 5 (by rfl) ⟨17258915, by rfl⟩ : syracuseStep 368190197 = 34517831) B34517831
theorem B245460131 : Blo 2099435 245460131 := bstep (se 1 (by rfl) ⟨184095098, by rfl⟩ : syracuseStep 245460131 = 368190197) B368190197
theorem B163640087 : Blo 2099435 163640087 := bstep (se 1 (by rfl) ⟨122730065, by rfl⟩ : syracuseStep 163640087 = 245460131) B245460131
theorem B109093391 : Blo 2099435 109093391 := bstep (se 1 (by rfl) ⟨81820043, by rfl⟩ : syracuseStep 109093391 = 163640087) B163640087
theorem B72728927 : Blo 2099435 72728927 := bstep (se 1 (by rfl) ⟨54546695, by rfl⟩ : syracuseStep 72728927 = 109093391) B109093391
theorem B48485951 : Blo 2099435 48485951 := bstep (se 1 (by rfl) ⟨36364463, by rfl⟩ : syracuseStep 48485951 = 72728927) B72728927
theorem B32323967 : Blo 2099435 32323967 := bstep (se 1 (by rfl) ⟨24242975, by rfl⟩ : syracuseStep 32323967 = 48485951) B48485951
theorem B21549311 : Blo 2099435 21549311 := bstep (se 1 (by rfl) ⟨16161983, by rfl⟩ : syracuseStep 21549311 = 32323967) B32323967
theorem B14366207 : Blo 2099435 14366207 := bstep (se 1 (by rfl) ⟨10774655, by rfl⟩ : syracuseStep 14366207 = 21549311) B21549311
theorem B38309885 : Blo 2099435 38309885 := bstep (se 3 (by rfl) ⟨7183103, by rfl⟩ : syracuseStep 38309885 = 14366207) B14366207
theorem B25539923 : Blo 2099435 25539923 := bstep (se 1 (by rfl) ⟨19154942, by rfl⟩ : syracuseStep 25539923 = 38309885) B38309885
theorem B17026615 : Blo 2099435 17026615 := bstep (se 1 (by rfl) ⟨12769961, by rfl⟩ : syracuseStep 17026615 = 25539923) B25539923
theorem B22702153 : Blo 2099435 22702153 := bstep (se 2 (by rfl) ⟨8513307, by rfl⟩ : syracuseStep 22702153 = 17026615) B17026615
theorem B30269537 : Blo 2099435 30269537 := bstep (se 2 (by rfl) ⟨11351076, by rfl⟩ : syracuseStep 30269537 = 22702153) B22702153
theorem B20179691 : Blo 2099435 20179691 := bstep (se 1 (by rfl) ⟨15134768, by rfl⟩ : syracuseStep 20179691 = 30269537) B30269537
theorem B13453127 : Blo 2099435 13453127 := bstep (se 1 (by rfl) ⟨10089845, by rfl⟩ : syracuseStep 13453127 = 20179691) B20179691
theorem B8968751 : Blo 2099435 8968751 := bstep (se 1 (by rfl) ⟨6726563, by rfl⟩ : syracuseStep 8968751 = 13453127) B13453127
theorem B5979167 : Blo 2099435 5979167 := bstep (se 1 (by rfl) ⟨4484375, by rfl⟩ : syracuseStep 5979167 = 8968751) B8968751
theorem B3986111 : Blo 2099435 3986111 := bstep (se 1 (by rfl) ⟨2989583, by rfl⟩ : syracuseStep 3986111 = 5979167) B5979167
theorem B10629629 : Blo 2099435 10629629 := bstep (se 3 (by rfl) ⟨1993055, by rfl⟩ : syracuseStep 10629629 = 3986111) B3986111
theorem B7086419 : Blo 2099435 7086419 := bstep (se 1 (by rfl) ⟨5314814, by rfl⟩ : syracuseStep 7086419 = 10629629) B10629629
theorem B4724279 : Blo 2099435 4724279 := bstep (se 1 (by rfl) ⟨3543209, by rfl⟩ : syracuseStep 4724279 = 7086419) B7086419
theorem B3149519 : Blo 2099435 3149519 := bstep (se 1 (by rfl) ⟨2362139, by rfl⟩ : syracuseStep 3149519 = 4724279) B4724279
theorem B2099679 : Blo 2099435 2099679 := bstep (se 1 (by rfl) ⟨1574759, by rfl⟩ : syracuseStep 2099679 = 3149519) B3149519
theorem B3149525 : Blo 2099435 3149525 := bbase (se 7 (by rfl) ⟨36908, by rfl⟩ : syracuseStep 3149525 = 73817) (by norm_num)
theorem B2099683 : Blo 2099435 2099683 := bstep (se 1 (by rfl) ⟨1574762, by rfl⟩ : syracuseStep 2099683 = 3149525) B3149525
theorem B12944245 : Blo 2099435 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B17258993 : Blo 2099435 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B11505995 : Blo 2099435 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B7670663 : Blo 2099435 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B5113775 : Blo 2099435 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B3409183 : Blo 2099435 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B4545577 : Blo 2099435 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B24243077 : Blo 2099435 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B16162051 : Blo 2099435 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B21549401 : Blo 2099435 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B14366267 : Blo 2099435 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B9577511 : Blo 2099435 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B6385007 : Blo 2099435 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B17026685 : Blo 2099435 17026685 := bstep (se 3 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 17026685 = 6385007) B6385007
theorem B11351123 : Blo 2099435 11351123 := bstep (se 1 (by rfl) ⟨8513342, by rfl⟩ : syracuseStep 11351123 = 17026685) B17026685
theorem B7567415 : Blo 2099435 7567415 := bstep (se 1 (by rfl) ⟨5675561, by rfl⟩ : syracuseStep 7567415 = 11351123) B11351123
theorem B5044943 : Blo 2099435 5044943 := bstep (se 1 (by rfl) ⟨3783707, by rfl⟩ : syracuseStep 5044943 = 7567415) B7567415
theorem B3363295 : Blo 2099435 3363295 := bstep (se 1 (by rfl) ⟨2522471, by rfl⟩ : syracuseStep 3363295 = 5044943) B5044943
theorem B4484393 : Blo 2099435 4484393 := bstep (se 2 (by rfl) ⟨1681647, by rfl⟩ : syracuseStep 4484393 = 3363295) B3363295
theorem B2989595 : Blo 2099435 2989595 := bstep (se 1 (by rfl) ⟨2242196, by rfl⟩ : syracuseStep 2989595 = 4484393) B4484393
theorem B7972253 : Blo 2099435 7972253 := bstep (se 3 (by rfl) ⟨1494797, by rfl⟩ : syracuseStep 7972253 = 2989595) B2989595
theorem B5314835 : Blo 2099435 5314835 := bstep (se 1 (by rfl) ⟨3986126, by rfl⟩ : syracuseStep 5314835 = 7972253) B7972253
theorem B3543223 : Blo 2099435 3543223 := bstep (se 1 (by rfl) ⟨2657417, by rfl⟩ : syracuseStep 3543223 = 5314835) B5314835
theorem B4724297 : Blo 2099435 4724297 := bstep (se 2 (by rfl) ⟨1771611, by rfl⟩ : syracuseStep 4724297 = 3543223) B3543223
theorem B3149531 : Blo 2099435 3149531 := bstep (se 1 (by rfl) ⟨2362148, by rfl⟩ : syracuseStep 3149531 = 4724297) B4724297
theorem B2099687 : Blo 2099435 2099687 := bstep (se 1 (by rfl) ⟨1574765, by rfl⟩ : syracuseStep 2099687 = 3149531) B3149531
theorem B2362153 : Blo 2099435 2362153 := bbase (se 2 (by rfl) ⟨885807, by rfl⟩ : syracuseStep 2362153 = 1771615) (by norm_num)
theorem B3149537 : Blo 2099435 3149537 := bstep (se 2 (by rfl) ⟨1181076, by rfl⟩ : syracuseStep 3149537 = 2362153) B2362153
theorem B2099691 : Blo 2099435 2099691 := bstep (se 1 (by rfl) ⟨1574768, by rfl⟩ : syracuseStep 2099691 = 3149537) B3149537
theorem B10774741 : Blo 2099435 10774741 := bbase (se 7 (by rfl) ⟨126266, by rfl⟩ : syracuseStep 10774741 = 252533) (by norm_num)
theorem B14366321 : Blo 2099435 14366321 := bstep (se 2 (by rfl) ⟨5387370, by rfl⟩ : syracuseStep 14366321 = 10774741) B10774741
theorem B9577547 : Blo 2099435 9577547 := bstep (se 1 (by rfl) ⟨7183160, by rfl⟩ : syracuseStep 9577547 = 14366321) B14366321
theorem B6385031 : Blo 2099435 6385031 := bstep (se 1 (by rfl) ⟨4788773, by rfl⟩ : syracuseStep 6385031 = 9577547) B9577547
theorem B4256687 : Blo 2099435 4256687 := bstep (se 1 (by rfl) ⟨3192515, by rfl⟩ : syracuseStep 4256687 = 6385031) B6385031
theorem B2837791 : Blo 2099435 2837791 := bstep (se 1 (by rfl) ⟨2128343, by rfl⟩ : syracuseStep 2837791 = 4256687) B4256687
theorem B3783721 : Blo 2099435 3783721 := bstep (se 2 (by rfl) ⟨1418895, by rfl⟩ : syracuseStep 3783721 = 2837791) B2837791
theorem B5044961 : Blo 2099435 5044961 := bstep (se 2 (by rfl) ⟨1891860, by rfl⟩ : syracuseStep 5044961 = 3783721) B3783721
theorem B13453229 : Blo 2099435 13453229 := bstep (se 3 (by rfl) ⟨2522480, by rfl⟩ : syracuseStep 13453229 = 5044961) B5044961
theorem B8968819 : Blo 2099435 8968819 := bstep (se 1 (by rfl) ⟨6726614, by rfl⟩ : syracuseStep 8968819 = 13453229) B13453229
theorem B11958425 : Blo 2099435 11958425 := bstep (se 2 (by rfl) ⟨4484409, by rfl⟩ : syracuseStep 11958425 = 8968819) B8968819
theorem B7972283 : Blo 2099435 7972283 := bstep (se 1 (by rfl) ⟨5979212, by rfl⟩ : syracuseStep 7972283 = 11958425) B11958425
theorem B5314855 : Blo 2099435 5314855 := bstep (se 1 (by rfl) ⟨3986141, by rfl⟩ : syracuseStep 5314855 = 7972283) B7972283
theorem B7086473 : Blo 2099435 7086473 := bstep (se 2 (by rfl) ⟨2657427, by rfl⟩ : syracuseStep 7086473 = 5314855) B5314855
theorem B4724315 : Blo 2099435 4724315 := bstep (se 1 (by rfl) ⟨3543236, by rfl⟩ : syracuseStep 4724315 = 7086473) B7086473
theorem B3149543 : Blo 2099435 3149543 := bstep (se 1 (by rfl) ⟨2362157, by rfl⟩ : syracuseStep 3149543 = 4724315) B4724315
theorem B2099695 : Blo 2099435 2099695 := bstep (se 1 (by rfl) ⟨1574771, by rfl⟩ : syracuseStep 2099695 = 3149543) B3149543
theorem B3149549 : Blo 2099435 3149549 := bbase (se 3 (by rfl) ⟨590540, by rfl⟩ : syracuseStep 3149549 = 1181081) (by norm_num)
theorem B2099699 : Blo 2099435 2099699 := bstep (se 1 (by rfl) ⟨1574774, by rfl⟩ : syracuseStep 2099699 = 3149549) B3149549
theorem B4724333 : Blo 2099435 4724333 := bbase (se 3 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 4724333 = 1771625) (by norm_num)
theorem B3149555 : Blo 2099435 3149555 := bstep (se 1 (by rfl) ⟨2362166, by rfl⟩ : syracuseStep 3149555 = 4724333) B4724333
theorem B2099703 : Blo 2099435 2099703 := bstep (se 1 (by rfl) ⟨1574777, by rfl⟩ : syracuseStep 2099703 = 3149555) B3149555
theorem B3986165 : Blo 2099435 3986165 := bbase (se 5 (by rfl) ⟨186851, by rfl⟩ : syracuseStep 3986165 = 373703) (by norm_num)
theorem B2657443 : Blo 2099435 2657443 := bstep (se 1 (by rfl) ⟨1993082, by rfl⟩ : syracuseStep 2657443 = 3986165) B3986165
theorem B3543257 : Blo 2099435 3543257 := bstep (se 2 (by rfl) ⟨1328721, by rfl⟩ : syracuseStep 3543257 = 2657443) B2657443
theorem B2362171 : Blo 2099435 2362171 := bstep (se 1 (by rfl) ⟨1771628, by rfl⟩ : syracuseStep 2362171 = 3543257) B3543257
theorem B3149561 : Blo 2099435 3149561 := bstep (se 2 (by rfl) ⟨1181085, by rfl⟩ : syracuseStep 3149561 = 2362171) B2362171
theorem B2099707 : Blo 2099435 2099707 := bstep (se 1 (by rfl) ⟨1574780, by rfl⟩ : syracuseStep 2099707 = 3149561) B3149561
theorem B2157397 : Blo 2099435 2157397 := bbase (se 9 (by rfl) ⟨6320, by rfl⟩ : syracuseStep 2157397 = 12641) (by norm_num)
theorem B11506117 : Blo 2099435 11506117 := bstep (se 4 (by rfl) ⟨1078698, by rfl⟩ : syracuseStep 11506117 = 2157397) B2157397
theorem B15341489 : Blo 2099435 15341489 := bstep (se 2 (by rfl) ⟨5753058, by rfl⟩ : syracuseStep 15341489 = 11506117) B11506117
theorem B10227659 : Blo 2099435 10227659 := bstep (se 1 (by rfl) ⟨7670744, by rfl⟩ : syracuseStep 10227659 = 15341489) B15341489
theorem B27273757 : Blo 2099435 27273757 := bstep (se 3 (by rfl) ⟨5113829, by rfl⟩ : syracuseStep 27273757 = 10227659) B10227659
theorem B36365009 : Blo 2099435 36365009 := bstep (se 2 (by rfl) ⟨13636878, by rfl⟩ : syracuseStep 36365009 = 27273757) B27273757
theorem B96973357 : Blo 2099435 96973357 := bstep (se 3 (by rfl) ⟨18182504, by rfl⟩ : syracuseStep 96973357 = 36365009) B36365009
theorem B129297809 : Blo 2099435 129297809 := bstep (se 2 (by rfl) ⟨48486678, by rfl⟩ : syracuseStep 129297809 = 96973357) B96973357
theorem B86198539 : Blo 2099435 86198539 := bstep (se 1 (by rfl) ⟨64648904, by rfl⟩ : syracuseStep 86198539 = 129297809) B129297809
theorem B114931385 : Blo 2099435 114931385 := bstep (se 2 (by rfl) ⟨43099269, by rfl⟩ : syracuseStep 114931385 = 86198539) B86198539
theorem B76620923 : Blo 2099435 76620923 := bstep (se 1 (by rfl) ⟨57465692, by rfl⟩ : syracuseStep 76620923 = 114931385) B114931385
theorem B51080615 : Blo 2099435 51080615 := bstep (se 1 (by rfl) ⟨38310461, by rfl⟩ : syracuseStep 51080615 = 76620923) B76620923
theorem B34053743 : Blo 2099435 34053743 := bstep (se 1 (by rfl) ⟨25540307, by rfl⟩ : syracuseStep 34053743 = 51080615) B51080615
theorem B90809981 : Blo 2099435 90809981 := bstep (se 3 (by rfl) ⟨17026871, by rfl⟩ : syracuseStep 90809981 = 34053743) B34053743
theorem B60539987 : Blo 2099435 60539987 := bstep (se 1 (by rfl) ⟨45404990, by rfl⟩ : syracuseStep 60539987 = 90809981) B90809981
theorem B40359991 : Blo 2099435 40359991 := bstep (se 1 (by rfl) ⟨30269993, by rfl⟩ : syracuseStep 40359991 = 60539987) B60539987
theorem B53813321 : Blo 2099435 53813321 := bstep (se 2 (by rfl) ⟨20179995, by rfl⟩ : syracuseStep 53813321 = 40359991) B40359991
theorem B35875547 : Blo 2099435 35875547 := bstep (se 1 (by rfl) ⟨26906660, by rfl⟩ : syracuseStep 35875547 = 53813321) B53813321
theorem B23917031 : Blo 2099435 23917031 := bstep (se 1 (by rfl) ⟨17937773, by rfl⟩ : syracuseStep 23917031 = 35875547) B35875547
theorem B15944687 : Blo 2099435 15944687 := bstep (se 1 (by rfl) ⟨11958515, by rfl⟩ : syracuseStep 15944687 = 23917031) B23917031
theorem B10629791 : Blo 2099435 10629791 := bstep (se 1 (by rfl) ⟨7972343, by rfl⟩ : syracuseStep 10629791 = 15944687) B15944687
theorem B7086527 : Blo 2099435 7086527 := bstep (se 1 (by rfl) ⟨5314895, by rfl⟩ : syracuseStep 7086527 = 10629791) B10629791
theorem B4724351 : Blo 2099435 4724351 := bstep (se 1 (by rfl) ⟨3543263, by rfl⟩ : syracuseStep 4724351 = 7086527) B7086527
theorem B3149567 : Blo 2099435 3149567 := bstep (se 1 (by rfl) ⟨2362175, by rfl⟩ : syracuseStep 3149567 = 4724351) B4724351
theorem B2099711 : Blo 2099435 2099711 := bstep (se 1 (by rfl) ⟨1574783, by rfl⟩ : syracuseStep 2099711 = 3149567) B3149567
theorem B3149573 : Blo 2099435 3149573 := bbase (se 4 (by rfl) ⟨295272, by rfl⟩ : syracuseStep 3149573 = 590545) (by norm_num)
theorem B2099715 : Blo 2099435 2099715 := bstep (se 1 (by rfl) ⟨1574786, by rfl⟩ : syracuseStep 2099715 = 3149573) B3149573
theorem B3543277 : Blo 2099435 3543277 := bbase (se 3 (by rfl) ⟨664364, by rfl⟩ : syracuseStep 3543277 = 1328729) (by norm_num)
theorem B4724369 : Blo 2099435 4724369 := bstep (se 2 (by rfl) ⟨1771638, by rfl⟩ : syracuseStep 4724369 = 3543277) B3543277
theorem B3149579 : Blo 2099435 3149579 := bstep (se 1 (by rfl) ⟨2362184, by rfl⟩ : syracuseStep 3149579 = 4724369) B4724369
theorem B2099719 : Blo 2099435 2099719 := bstep (se 1 (by rfl) ⟨1574789, by rfl⟩ : syracuseStep 2099719 = 3149579) B3149579
theorem B2362189 : Blo 2099435 2362189 := bbase (se 3 (by rfl) ⟨442910, by rfl⟩ : syracuseStep 2362189 = 885821) (by norm_num)
theorem B3149585 : Blo 2099435 3149585 := bstep (se 2 (by rfl) ⟨1181094, by rfl⟩ : syracuseStep 3149585 = 2362189) B2362189
theorem B2099723 : Blo 2099435 2099723 := bstep (se 1 (by rfl) ⟨1574792, by rfl⟩ : syracuseStep 2099723 = 3149585) B3149585
theorem B7086581 : Blo 2099435 7086581 := bbase (se 5 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 7086581 = 664367) (by norm_num)
theorem B4724387 : Blo 2099435 4724387 := bstep (se 1 (by rfl) ⟨3543290, by rfl⟩ : syracuseStep 4724387 = 7086581) B7086581
theorem B3149591 : Blo 2099435 3149591 := bstep (se 1 (by rfl) ⟨2362193, by rfl⟩ : syracuseStep 3149591 = 4724387) B4724387
theorem B2099727 : Blo 2099435 2099727 := bstep (se 1 (by rfl) ⟨1574795, by rfl⟩ : syracuseStep 2099727 = 3149591) B3149591
theorem B3149597 : Blo 2099435 3149597 := bbase (se 3 (by rfl) ⟨590549, by rfl⟩ : syracuseStep 3149597 = 1181099) (by norm_num)
theorem B2099731 : Blo 2099435 2099731 := bstep (se 1 (by rfl) ⟨1574798, by rfl⟩ : syracuseStep 2099731 = 3149597) B3149597
theorem B4724405 : Blo 2099435 4724405 := bbase (se 5 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 4724405 = 442913) (by norm_num)
theorem B3149603 : Blo 2099435 3149603 := bstep (se 1 (by rfl) ⟨2362202, by rfl⟩ : syracuseStep 3149603 = 4724405) B4724405
theorem B2099735 : Blo 2099435 2099735 := bstep (se 1 (by rfl) ⟨1574801, by rfl⟩ : syracuseStep 2099735 = 3149603) B3149603
theorem B11958677 : Blo 2099435 11958677 := bbase (se 6 (by rfl) ⟨280281, by rfl⟩ : syracuseStep 11958677 = 560563) (by norm_num)
theorem B7972451 : Blo 2099435 7972451 := bstep (se 1 (by rfl) ⟨5979338, by rfl⟩ : syracuseStep 7972451 = 11958677) B11958677
theorem B5314967 : Blo 2099435 5314967 := bstep (se 1 (by rfl) ⟨3986225, by rfl⟩ : syracuseStep 5314967 = 7972451) B7972451
theorem B3543311 : Blo 2099435 3543311 := bstep (se 1 (by rfl) ⟨2657483, by rfl⟩ : syracuseStep 3543311 = 5314967) B5314967
theorem B2362207 : Blo 2099435 2362207 := bstep (se 1 (by rfl) ⟨1771655, by rfl⟩ : syracuseStep 2362207 = 3543311) B3543311
theorem B3149609 : Blo 2099435 3149609 := bstep (se 2 (by rfl) ⟨1181103, by rfl⟩ : syracuseStep 3149609 = 2362207) B2362207
theorem B2099739 : Blo 2099435 2099739 := bstep (se 1 (by rfl) ⟨1574804, by rfl⟩ : syracuseStep 2099739 = 3149609) B3149609
theorem B5979349 : Blo 2099435 5979349 := bbase (se 7 (by rfl) ⟨70070, by rfl⟩ : syracuseStep 5979349 = 140141) (by norm_num)
theorem B7972465 : Blo 2099435 7972465 := bstep (se 2 (by rfl) ⟨2989674, by rfl⟩ : syracuseStep 7972465 = 5979349) B5979349
theorem B10629953 : Blo 2099435 10629953 := bstep (se 2 (by rfl) ⟨3986232, by rfl⟩ : syracuseStep 10629953 = 7972465) B7972465
theorem B7086635 : Blo 2099435 7086635 := bstep (se 1 (by rfl) ⟨5314976, by rfl⟩ : syracuseStep 7086635 = 10629953) B10629953
theorem B4724423 : Blo 2099435 4724423 := bstep (se 1 (by rfl) ⟨3543317, by rfl⟩ : syracuseStep 4724423 = 7086635) B7086635
theorem B3149615 : Blo 2099435 3149615 := bstep (se 1 (by rfl) ⟨2362211, by rfl⟩ : syracuseStep 3149615 = 4724423) B4724423
theorem B2099743 : Blo 2099435 2099743 := bstep (se 1 (by rfl) ⟨1574807, by rfl⟩ : syracuseStep 2099743 = 3149615) B3149615
theorem B3149621 : Blo 2099435 3149621 := bbase (se 5 (by rfl) ⟨147638, by rfl⟩ : syracuseStep 3149621 = 295277) (by norm_num)
theorem B2099747 : Blo 2099435 2099747 := bstep (se 1 (by rfl) ⟨1574810, by rfl⟩ : syracuseStep 2099747 = 3149621) B3149621
theorem B5314997 : Blo 2099435 5314997 := bbase (se 5 (by rfl) ⟨249140, by rfl⟩ : syracuseStep 5314997 = 498281) (by norm_num)
theorem B3543331 : Blo 2099435 3543331 := bstep (se 1 (by rfl) ⟨2657498, by rfl⟩ : syracuseStep 3543331 = 5314997) B5314997
theorem B4724441 : Blo 2099435 4724441 := bstep (se 2 (by rfl) ⟨1771665, by rfl⟩ : syracuseStep 4724441 = 3543331) B3543331
theorem B3149627 : Blo 2099435 3149627 := bstep (se 1 (by rfl) ⟨2362220, by rfl⟩ : syracuseStep 3149627 = 4724441) B4724441
theorem B2099751 : Blo 2099435 2099751 := bstep (se 1 (by rfl) ⟨1574813, by rfl⟩ : syracuseStep 2099751 = 3149627) B3149627
theorem B2362225 : Blo 2099435 2362225 := bbase (se 2 (by rfl) ⟨885834, by rfl⟩ : syracuseStep 2362225 = 1771669) (by norm_num)
theorem B3149633 : Blo 2099435 3149633 := bstep (se 2 (by rfl) ⟨1181112, by rfl⟩ : syracuseStep 3149633 = 2362225) B2362225
theorem B2099755 : Blo 2099435 2099755 := bstep (se 1 (by rfl) ⟨1574816, by rfl⟩ : syracuseStep 2099755 = 3149633) B3149633
theorem B8969093 : Blo 2099435 8969093 := bbase (se 4 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 8969093 = 1681705) (by norm_num)
theorem B5979395 : Blo 2099435 5979395 := bstep (se 1 (by rfl) ⟨4484546, by rfl⟩ : syracuseStep 5979395 = 8969093) B8969093
theorem B3986263 : Blo 2099435 3986263 := bstep (se 1 (by rfl) ⟨2989697, by rfl⟩ : syracuseStep 3986263 = 5979395) B5979395
theorem B5315017 : Blo 2099435 5315017 := bstep (se 2 (by rfl) ⟨1993131, by rfl⟩ : syracuseStep 5315017 = 3986263) B3986263
theorem B7086689 : Blo 2099435 7086689 := bstep (se 2 (by rfl) ⟨2657508, by rfl⟩ : syracuseStep 7086689 = 5315017) B5315017
theorem B4724459 : Blo 2099435 4724459 := bstep (se 1 (by rfl) ⟨3543344, by rfl⟩ : syracuseStep 4724459 = 7086689) B7086689
theorem B3149639 : Blo 2099435 3149639 := bstep (se 1 (by rfl) ⟨2362229, by rfl⟩ : syracuseStep 3149639 = 4724459) B4724459
theorem B2099759 : Blo 2099435 2099759 := bstep (se 1 (by rfl) ⟨1574819, by rfl⟩ : syracuseStep 2099759 = 3149639) B3149639
theorem B3149645 : Blo 2099435 3149645 := bbase (se 3 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 3149645 = 1181117) (by norm_num)
theorem B2099763 : Blo 2099435 2099763 := bstep (se 1 (by rfl) ⟨1574822, by rfl⟩ : syracuseStep 2099763 = 3149645) B3149645
theorem B4724477 : Blo 2099435 4724477 := bbase (se 3 (by rfl) ⟨885839, by rfl⟩ : syracuseStep 4724477 = 1771679) (by norm_num)
theorem B3149651 : Blo 2099435 3149651 := bstep (se 1 (by rfl) ⟨2362238, by rfl⟩ : syracuseStep 3149651 = 4724477) B4724477
theorem B2099767 : Blo 2099435 2099767 := bstep (se 1 (by rfl) ⟨1574825, by rfl⟩ : syracuseStep 2099767 = 3149651) B3149651
theorem B3543365 : Blo 2099435 3543365 := bbase (se 4 (by rfl) ⟨332190, by rfl⟩ : syracuseStep 3543365 = 664381) (by norm_num)
theorem B2362243 : Blo 2099435 2362243 := bstep (se 1 (by rfl) ⟨1771682, by rfl⟩ : syracuseStep 2362243 = 3543365) B3543365
theorem B3149657 : Blo 2099435 3149657 := bstep (se 2 (by rfl) ⟨1181121, by rfl⟩ : syracuseStep 3149657 = 2362243) B2362243
theorem B2099771 : Blo 2099435 2099771 := bstep (se 1 (by rfl) ⟨1574828, by rfl⟩ : syracuseStep 2099771 = 3149657) B3149657
theorem B15945173 : Blo 2099435 15945173 := bbase (se 7 (by rfl) ⟨186857, by rfl⟩ : syracuseStep 15945173 = 373715) (by norm_num)
theorem B10630115 : Blo 2099435 10630115 := bstep (se 1 (by rfl) ⟨7972586, by rfl⟩ : syracuseStep 10630115 = 15945173) B15945173
theorem B7086743 : Blo 2099435 7086743 := bstep (se 1 (by rfl) ⟨5315057, by rfl⟩ : syracuseStep 7086743 = 10630115) B10630115
theorem B4724495 : Blo 2099435 4724495 := bstep (se 1 (by rfl) ⟨3543371, by rfl⟩ : syracuseStep 4724495 = 7086743) B7086743
theorem B3149663 : Blo 2099435 3149663 := bstep (se 1 (by rfl) ⟨2362247, by rfl⟩ : syracuseStep 3149663 = 4724495) B4724495
theorem B2099775 : Blo 2099435 2099775 := bstep (se 1 (by rfl) ⟨1574831, by rfl⟩ : syracuseStep 2099775 = 3149663) B3149663
theorem B3149669 : Blo 2099435 3149669 := bbase (se 4 (by rfl) ⟨295281, by rfl⟩ : syracuseStep 3149669 = 590563) (by norm_num)
theorem B2099779 : Blo 2099435 2099779 := bstep (se 1 (by rfl) ⟨1574834, by rfl⟩ : syracuseStep 2099779 = 3149669) B3149669
theorem B3986309 : Blo 2099435 3986309 := bbase (se 4 (by rfl) ⟨373716, by rfl⟩ : syracuseStep 3986309 = 747433) (by norm_num)
theorem B2657539 : Blo 2099435 2657539 := bstep (se 1 (by rfl) ⟨1993154, by rfl⟩ : syracuseStep 2657539 = 3986309) B3986309
theorem B3543385 : Blo 2099435 3543385 := bstep (se 2 (by rfl) ⟨1328769, by rfl⟩ : syracuseStep 3543385 = 2657539) B2657539
theorem B4724513 : Blo 2099435 4724513 := bstep (se 2 (by rfl) ⟨1771692, by rfl⟩ : syracuseStep 4724513 = 3543385) B3543385
theorem B3149675 : Blo 2099435 3149675 := bstep (se 1 (by rfl) ⟨2362256, by rfl⟩ : syracuseStep 3149675 = 4724513) B4724513
theorem B2099783 : Blo 2099435 2099783 := bstep (se 1 (by rfl) ⟨1574837, by rfl⟩ : syracuseStep 2099783 = 3149675) B3149675
theorem B2362261 : Blo 2099435 2362261 := bbase (se 6 (by rfl) ⟨55365, by rfl⟩ : syracuseStep 2362261 = 110731) (by norm_num)
theorem B3149681 : Blo 2099435 3149681 := bstep (se 2 (by rfl) ⟨1181130, by rfl⟩ : syracuseStep 3149681 = 2362261) B2362261
theorem B2099787 : Blo 2099435 2099787 := bstep (se 1 (by rfl) ⟨1574840, by rfl⟩ : syracuseStep 2099787 = 3149681) B3149681
theorem B2657549 : Blo 2099435 2657549 := bbase (se 3 (by rfl) ⟨498290, by rfl⟩ : syracuseStep 2657549 = 996581) (by norm_num)
theorem B7086797 : Blo 2099435 7086797 := bstep (se 3 (by rfl) ⟨1328774, by rfl⟩ : syracuseStep 7086797 = 2657549) B2657549
theorem B4724531 : Blo 2099435 4724531 := bstep (se 1 (by rfl) ⟨3543398, by rfl⟩ : syracuseStep 4724531 = 7086797) B7086797
theorem B3149687 : Blo 2099435 3149687 := bstep (se 1 (by rfl) ⟨2362265, by rfl⟩ : syracuseStep 3149687 = 4724531) B4724531
theorem B2099791 : Blo 2099435 2099791 := bstep (se 1 (by rfl) ⟨1574843, by rfl⟩ : syracuseStep 2099791 = 3149687) B3149687
theorem B3149693 : Blo 2099435 3149693 := bbase (se 3 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 3149693 = 1181135) (by norm_num)
theorem B2099795 : Blo 2099435 2099795 := bstep (se 1 (by rfl) ⟨1574846, by rfl⟩ : syracuseStep 2099795 = 3149693) B3149693
theorem B4724549 : Blo 2099435 4724549 := bbase (se 4 (by rfl) ⟨442926, by rfl⟩ : syracuseStep 4724549 = 885853) (by norm_num)
theorem B3149699 : Blo 2099435 3149699 := bstep (se 1 (by rfl) ⟨2362274, by rfl⟩ : syracuseStep 3149699 = 4724549) B4724549
theorem B2099799 : Blo 2099435 2099799 := bstep (se 1 (by rfl) ⟨1574849, by rfl⟩ : syracuseStep 2099799 = 3149699) B3149699
theorem B3783917 : Blo 2099435 3783917 := bbase (se 3 (by rfl) ⟨709484, by rfl⟩ : syracuseStep 3783917 = 1418969) (by norm_num)
theorem B2522611 : Blo 2099435 2522611 := bstep (se 1 (by rfl) ⟨1891958, by rfl⟩ : syracuseStep 2522611 = 3783917) B3783917
theorem B3363481 : Blo 2099435 3363481 := bstep (se 2 (by rfl) ⟨1261305, by rfl⟩ : syracuseStep 3363481 = 2522611) B2522611
theorem B4484641 : Blo 2099435 4484641 := bstep (se 2 (by rfl) ⟨1681740, by rfl⟩ : syracuseStep 4484641 = 3363481) B3363481
theorem B5979521 : Blo 2099435 5979521 := bstep (se 2 (by rfl) ⟨2242320, by rfl⟩ : syracuseStep 5979521 = 4484641) B4484641
theorem B3986347 : Blo 2099435 3986347 := bstep (se 1 (by rfl) ⟨2989760, by rfl⟩ : syracuseStep 3986347 = 5979521) B5979521
theorem B5315129 : Blo 2099435 5315129 := bstep (se 2 (by rfl) ⟨1993173, by rfl⟩ : syracuseStep 5315129 = 3986347) B3986347
theorem B3543419 : Blo 2099435 3543419 := bstep (se 1 (by rfl) ⟨2657564, by rfl⟩ : syracuseStep 3543419 = 5315129) B5315129
theorem B2362279 : Blo 2099435 2362279 := bstep (se 1 (by rfl) ⟨1771709, by rfl⟩ : syracuseStep 2362279 = 3543419) B3543419
theorem B3149705 : Blo 2099435 3149705 := bstep (se 2 (by rfl) ⟨1181139, by rfl⟩ : syracuseStep 3149705 = 2362279) B2362279
theorem B2099803 : Blo 2099435 2099803 := bstep (se 1 (by rfl) ⟨1574852, by rfl⟩ : syracuseStep 2099803 = 3149705) B3149705
theorem B10630277 : Blo 2099435 10630277 := bbase (se 4 (by rfl) ⟨996588, by rfl⟩ : syracuseStep 10630277 = 1993177) (by norm_num)
theorem B7086851 : Blo 2099435 7086851 := bstep (se 1 (by rfl) ⟨5315138, by rfl⟩ : syracuseStep 7086851 = 10630277) B10630277
theorem B4724567 : Blo 2099435 4724567 := bstep (se 1 (by rfl) ⟨3543425, by rfl⟩ : syracuseStep 4724567 = 7086851) B7086851
theorem B3149711 : Blo 2099435 3149711 := bstep (se 1 (by rfl) ⟨2362283, by rfl⟩ : syracuseStep 3149711 = 4724567) B4724567
theorem B2099807 : Blo 2099435 2099807 := bstep (se 1 (by rfl) ⟨1574855, by rfl⟩ : syracuseStep 2099807 = 3149711) B3149711
theorem B3149717 : Blo 2099435 3149717 := bbase (se 6 (by rfl) ⟨73821, by rfl⟩ : syracuseStep 3149717 = 147643) (by norm_num)
theorem B2099811 : Blo 2099435 2099811 := bstep (se 1 (by rfl) ⟨1574858, by rfl⟩ : syracuseStep 2099811 = 3149717) B3149717
theorem B2242333 : Blo 2099435 2242333 := bbase (se 3 (by rfl) ⟨420437, by rfl⟩ : syracuseStep 2242333 = 840875) (by norm_num)
theorem B11959109 : Blo 2099435 11959109 := bstep (se 4 (by rfl) ⟨1121166, by rfl⟩ : syracuseStep 11959109 = 2242333) B2242333
theorem B7972739 : Blo 2099435 7972739 := bstep (se 1 (by rfl) ⟨5979554, by rfl⟩ : syracuseStep 7972739 = 11959109) B11959109
theorem B5315159 : Blo 2099435 5315159 := bstep (se 1 (by rfl) ⟨3986369, by rfl⟩ : syracuseStep 5315159 = 7972739) B7972739
theorem B3543439 : Blo 2099435 3543439 := bstep (se 1 (by rfl) ⟨2657579, by rfl⟩ : syracuseStep 3543439 = 5315159) B5315159
theorem B4724585 : Blo 2099435 4724585 := bstep (se 2 (by rfl) ⟨1771719, by rfl⟩ : syracuseStep 4724585 = 3543439) B3543439
theorem B3149723 : Blo 2099435 3149723 := bstep (se 1 (by rfl) ⟨2362292, by rfl⟩ : syracuseStep 3149723 = 4724585) B4724585
theorem B2099815 : Blo 2099435 2099815 := bstep (se 1 (by rfl) ⟨1574861, by rfl⟩ : syracuseStep 2099815 = 3149723) B3149723
theorem B2362297 : Blo 2099435 2362297 := bbase (se 2 (by rfl) ⟨885861, by rfl⟩ : syracuseStep 2362297 = 1771723) (by norm_num)
theorem B3149729 : Blo 2099435 3149729 := bstep (se 2 (by rfl) ⟨1181148, by rfl⟩ : syracuseStep 3149729 = 2362297) B2362297
theorem B2099819 : Blo 2099435 2099819 := bstep (se 1 (by rfl) ⟨1574864, by rfl⟩ : syracuseStep 2099819 = 3149729) B3149729
theorem B5045269 : Blo 2099435 5045269 := bbase (se 6 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 5045269 = 236497) (by norm_num)
theorem B6727025 : Blo 2099435 6727025 := bstep (se 2 (by rfl) ⟨2522634, by rfl⟩ : syracuseStep 6727025 = 5045269) B5045269
theorem B4484683 : Blo 2099435 4484683 := bstep (se 1 (by rfl) ⟨3363512, by rfl⟩ : syracuseStep 4484683 = 6727025) B6727025
theorem B5979577 : Blo 2099435 5979577 := bstep (se 2 (by rfl) ⟨2242341, by rfl⟩ : syracuseStep 5979577 = 4484683) B4484683
theorem B7972769 : Blo 2099435 7972769 := bstep (se 2 (by rfl) ⟨2989788, by rfl⟩ : syracuseStep 7972769 = 5979577) B5979577
theorem B5315179 : Blo 2099435 5315179 := bstep (se 1 (by rfl) ⟨3986384, by rfl⟩ : syracuseStep 5315179 = 7972769) B7972769
theorem B7086905 : Blo 2099435 7086905 := bstep (se 2 (by rfl) ⟨2657589, by rfl⟩ : syracuseStep 7086905 = 5315179) B5315179
theorem B4724603 : Blo 2099435 4724603 := bstep (se 1 (by rfl) ⟨3543452, by rfl⟩ : syracuseStep 4724603 = 7086905) B7086905
theorem B3149735 : Blo 2099435 3149735 := bstep (se 1 (by rfl) ⟨2362301, by rfl⟩ : syracuseStep 3149735 = 4724603) B4724603
theorem B2099823 : Blo 2099435 2099823 := bstep (se 1 (by rfl) ⟨1574867, by rfl⟩ : syracuseStep 2099823 = 3149735) B3149735
theorem B3149741 : Blo 2099435 3149741 := bbase (se 3 (by rfl) ⟨590576, by rfl⟩ : syracuseStep 3149741 = 1181153) (by norm_num)
theorem B2099827 : Blo 2099435 2099827 := bstep (se 1 (by rfl) ⟨1574870, by rfl⟩ : syracuseStep 2099827 = 3149741) B3149741
theorem B4724621 : Blo 2099435 4724621 := bbase (se 3 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 4724621 = 1771733) (by norm_num)
theorem B3149747 : Blo 2099435 3149747 := bstep (se 1 (by rfl) ⟨2362310, by rfl⟩ : syracuseStep 3149747 = 4724621) B4724621
theorem B2099831 : Blo 2099435 2099831 := bstep (se 1 (by rfl) ⟨1574873, by rfl⟩ : syracuseStep 2099831 = 3149747) B3149747
theorem B2657605 : Blo 2099435 2657605 := bbase (se 4 (by rfl) ⟨249150, by rfl⟩ : syracuseStep 2657605 = 498301) (by norm_num)
theorem B3543473 : Blo 2099435 3543473 := bstep (se 2 (by rfl) ⟨1328802, by rfl⟩ : syracuseStep 3543473 = 2657605) B2657605
theorem B2362315 : Blo 2099435 2362315 := bstep (se 1 (by rfl) ⟨1771736, by rfl⟩ : syracuseStep 2362315 = 3543473) B3543473
theorem B3149753 : Blo 2099435 3149753 := bstep (se 2 (by rfl) ⟨1181157, by rfl⟩ : syracuseStep 3149753 = 2362315) B2362315
theorem B2099835 : Blo 2099435 2099835 := bstep (se 1 (by rfl) ⟨1574876, by rfl⟩ : syracuseStep 2099835 = 3149753) B3149753
theorem B10090613 : Blo 2099435 10090613 := bbase (se 5 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 10090613 = 945995) (by norm_num)
theorem B26908301 : Blo 2099435 26908301 := bstep (se 3 (by rfl) ⟨5045306, by rfl⟩ : syracuseStep 26908301 = 10090613) B10090613
theorem B17938867 : Blo 2099435 17938867 := bstep (se 1 (by rfl) ⟨13454150, by rfl⟩ : syracuseStep 17938867 = 26908301) B26908301
theorem B23918489 : Blo 2099435 23918489 := bstep (se 2 (by rfl) ⟨8969433, by rfl⟩ : syracuseStep 23918489 = 17938867) B17938867
theorem B15945659 : Blo 2099435 15945659 := bstep (se 1 (by rfl) ⟨11959244, by rfl⟩ : syracuseStep 15945659 = 23918489) B23918489
theorem B10630439 : Blo 2099435 10630439 := bstep (se 1 (by rfl) ⟨7972829, by rfl⟩ : syracuseStep 10630439 = 15945659) B15945659
theorem B7086959 : Blo 2099435 7086959 := bstep (se 1 (by rfl) ⟨5315219, by rfl⟩ : syracuseStep 7086959 = 10630439) B10630439
theorem B4724639 : Blo 2099435 4724639 := bstep (se 1 (by rfl) ⟨3543479, by rfl⟩ : syracuseStep 4724639 = 7086959) B7086959
theorem B3149759 : Blo 2099435 3149759 := bstep (se 1 (by rfl) ⟨2362319, by rfl⟩ : syracuseStep 3149759 = 4724639) B4724639
theorem B2099839 : Blo 2099435 2099839 := bstep (se 1 (by rfl) ⟨1574879, by rfl⟩ : syracuseStep 2099839 = 3149759) B3149759
theorem B3149765 : Blo 2099435 3149765 := bbase (se 4 (by rfl) ⟨295290, by rfl⟩ : syracuseStep 3149765 = 590581) (by norm_num)
theorem B2099843 : Blo 2099435 2099843 := bstep (se 1 (by rfl) ⟨1574882, by rfl⟩ : syracuseStep 2099843 = 3149765) B3149765
theorem B3543493 : Blo 2099435 3543493 := bbase (se 4 (by rfl) ⟨332202, by rfl⟩ : syracuseStep 3543493 = 664405) (by norm_num)
theorem B4724657 : Blo 2099435 4724657 := bstep (se 2 (by rfl) ⟨1771746, by rfl⟩ : syracuseStep 4724657 = 3543493) B3543493
theorem B3149771 : Blo 2099435 3149771 := bstep (se 1 (by rfl) ⟨2362328, by rfl⟩ : syracuseStep 3149771 = 4724657) B4724657
theorem B2099847 : Blo 2099435 2099847 := bstep (se 1 (by rfl) ⟨1574885, by rfl⟩ : syracuseStep 2099847 = 3149771) B3149771
theorem B2362333 : Blo 2099435 2362333 := bbase (se 3 (by rfl) ⟨442937, by rfl⟩ : syracuseStep 2362333 = 885875) (by norm_num)
theorem B3149777 : Blo 2099435 3149777 := bstep (se 2 (by rfl) ⟨1181166, by rfl⟩ : syracuseStep 3149777 = 2362333) B2362333
theorem B2099851 : Blo 2099435 2099851 := bstep (se 1 (by rfl) ⟨1574888, by rfl⟩ : syracuseStep 2099851 = 3149777) B3149777
theorem B7087013 : Blo 2099435 7087013 := bbase (se 4 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 7087013 = 1328815) (by norm_num)
theorem B4724675 : Blo 2099435 4724675 := bstep (se 1 (by rfl) ⟨3543506, by rfl⟩ : syracuseStep 4724675 = 7087013) B7087013
theorem B3149783 : Blo 2099435 3149783 := bstep (se 1 (by rfl) ⟨2362337, by rfl⟩ : syracuseStep 3149783 = 4724675) B4724675
theorem B2099855 : Blo 2099435 2099855 := bstep (se 1 (by rfl) ⟨1574891, by rfl⟩ : syracuseStep 2099855 = 3149783) B3149783
theorem B3149789 : Blo 2099435 3149789 := bbase (se 3 (by rfl) ⟨590585, by rfl⟩ : syracuseStep 3149789 = 1181171) (by norm_num)
theorem B2099859 : Blo 2099435 2099859 := bstep (se 1 (by rfl) ⟨1574894, by rfl⟩ : syracuseStep 2099859 = 3149789) B3149789
theorem B4724693 : Blo 2099435 4724693 := bbase (se 7 (by rfl) ⟨55367, by rfl⟩ : syracuseStep 4724693 = 110735) (by norm_num)
theorem B3149795 : Blo 2099435 3149795 := bstep (se 1 (by rfl) ⟨2362346, by rfl⟩ : syracuseStep 3149795 = 4724693) B4724693
theorem B2099863 : Blo 2099435 2099863 := bstep (se 1 (by rfl) ⟨1574897, by rfl⟩ : syracuseStep 2099863 = 3149795) B3149795
theorem B2427253 : Blo 2099435 2427253 := bbase (se 5 (by rfl) ⟨113777, by rfl⟩ : syracuseStep 2427253 = 227555) (by norm_num)
theorem B12945349 : Blo 2099435 12945349 := bstep (se 4 (by rfl) ⟨1213626, by rfl⟩ : syracuseStep 12945349 = 2427253) B2427253
theorem B17260465 : Blo 2099435 17260465 := bstep (se 2 (by rfl) ⟨6472674, by rfl⟩ : syracuseStep 17260465 = 12945349) B12945349
theorem B23013953 : Blo 2099435 23013953 := bstep (se 2 (by rfl) ⟨8630232, by rfl⟩ : syracuseStep 23013953 = 17260465) B17260465
theorem B15342635 : Blo 2099435 15342635 := bstep (se 1 (by rfl) ⟨11506976, by rfl⟩ : syracuseStep 15342635 = 23013953) B23013953
theorem B40913693 : Blo 2099435 40913693 := bstep (se 3 (by rfl) ⟨7671317, by rfl⟩ : syracuseStep 40913693 = 15342635) B15342635
theorem B27275795 : Blo 2099435 27275795 := bstep (se 1 (by rfl) ⟨20456846, by rfl⟩ : syracuseStep 27275795 = 40913693) B40913693
theorem B18183863 : Blo 2099435 18183863 := bstep (se 1 (by rfl) ⟨13637897, by rfl⟩ : syracuseStep 18183863 = 27275795) B27275795
theorem B48490301 : Blo 2099435 48490301 := bstep (se 3 (by rfl) ⟨9091931, by rfl⟩ : syracuseStep 48490301 = 18183863) B18183863
theorem B32326867 : Blo 2099435 32326867 := bstep (se 1 (by rfl) ⟨24245150, by rfl⟩ : syracuseStep 32326867 = 48490301) B48490301
theorem B43102489 : Blo 2099435 43102489 := bstep (se 2 (by rfl) ⟨16163433, by rfl⟩ : syracuseStep 43102489 = 32326867) B32326867
theorem B57469985 : Blo 2099435 57469985 := bstep (se 2 (by rfl) ⟨21551244, by rfl⟩ : syracuseStep 57469985 = 43102489) B43102489
theorem B38313323 : Blo 2099435 38313323 := bstep (se 1 (by rfl) ⟨28734992, by rfl⟩ : syracuseStep 38313323 = 57469985) B57469985
theorem B25542215 : Blo 2099435 25542215 := bstep (se 1 (by rfl) ⟨19156661, by rfl⟩ : syracuseStep 25542215 = 38313323) B38313323
theorem B17028143 : Blo 2099435 17028143 := bstep (se 1 (by rfl) ⟨12771107, by rfl⟩ : syracuseStep 17028143 = 25542215) B25542215
theorem B11352095 : Blo 2099435 11352095 := bstep (se 1 (by rfl) ⟨8514071, by rfl⟩ : syracuseStep 11352095 = 17028143) B17028143
theorem B7568063 : Blo 2099435 7568063 := bstep (se 1 (by rfl) ⟨5676047, by rfl⟩ : syracuseStep 7568063 = 11352095) B11352095
theorem B5045375 : Blo 2099435 5045375 := bstep (se 1 (by rfl) ⟨3784031, by rfl⟩ : syracuseStep 5045375 = 7568063) B7568063
theorem B13454333 : Blo 2099435 13454333 := bstep (se 3 (by rfl) ⟨2522687, by rfl⟩ : syracuseStep 13454333 = 5045375) B5045375
theorem B8969555 : Blo 2099435 8969555 := bstep (se 1 (by rfl) ⟨6727166, by rfl⟩ : syracuseStep 8969555 = 13454333) B13454333
theorem B5979703 : Blo 2099435 5979703 := bstep (se 1 (by rfl) ⟨4484777, by rfl⟩ : syracuseStep 5979703 = 8969555) B8969555
theorem B7972937 : Blo 2099435 7972937 := bstep (se 2 (by rfl) ⟨2989851, by rfl⟩ : syracuseStep 7972937 = 5979703) B5979703
theorem B5315291 : Blo 2099435 5315291 := bstep (se 1 (by rfl) ⟨3986468, by rfl⟩ : syracuseStep 5315291 = 7972937) B7972937
theorem B3543527 : Blo 2099435 3543527 := bstep (se 1 (by rfl) ⟨2657645, by rfl⟩ : syracuseStep 3543527 = 5315291) B5315291
theorem B2362351 : Blo 2099435 2362351 := bstep (se 1 (by rfl) ⟨1771763, by rfl⟩ : syracuseStep 2362351 = 3543527) B3543527
theorem B3149801 : Blo 2099435 3149801 := bstep (se 2 (by rfl) ⟨1181175, by rfl⟩ : syracuseStep 3149801 = 2362351) B2362351
theorem B2099867 : Blo 2099435 2099867 := bstep (se 1 (by rfl) ⟨1574900, by rfl⟩ : syracuseStep 2099867 = 3149801) B3149801
theorem B3363589 : Blo 2099435 3363589 := bbase (se 4 (by rfl) ⟨315336, by rfl⟩ : syracuseStep 3363589 = 630673) (by norm_num)
theorem B17939141 : Blo 2099435 17939141 := bstep (se 4 (by rfl) ⟨1681794, by rfl⟩ : syracuseStep 17939141 = 3363589) B3363589
theorem B11959427 : Blo 2099435 11959427 := bstep (se 1 (by rfl) ⟨8969570, by rfl⟩ : syracuseStep 11959427 = 17939141) B17939141
theorem B7972951 : Blo 2099435 7972951 := bstep (se 1 (by rfl) ⟨5979713, by rfl⟩ : syracuseStep 7972951 = 11959427) B11959427
theorem B10630601 : Blo 2099435 10630601 := bstep (se 2 (by rfl) ⟨3986475, by rfl⟩ : syracuseStep 10630601 = 7972951) B7972951
theorem B7087067 : Blo 2099435 7087067 := bstep (se 1 (by rfl) ⟨5315300, by rfl⟩ : syracuseStep 7087067 = 10630601) B10630601
theorem B4724711 : Blo 2099435 4724711 := bstep (se 1 (by rfl) ⟨3543533, by rfl⟩ : syracuseStep 4724711 = 7087067) B7087067
theorem B3149807 : Blo 2099435 3149807 := bstep (se 1 (by rfl) ⟨2362355, by rfl⟩ : syracuseStep 3149807 = 4724711) B4724711
theorem B2099871 : Blo 2099435 2099871 := bstep (se 1 (by rfl) ⟨1574903, by rfl⟩ : syracuseStep 2099871 = 3149807) B3149807
theorem B3149813 : Blo 2099435 3149813 := bbase (se 5 (by rfl) ⟨147647, by rfl⟩ : syracuseStep 3149813 = 295295) (by norm_num)
theorem B2099875 : Blo 2099435 2099875 := bstep (se 1 (by rfl) ⟨1574906, by rfl⟩ : syracuseStep 2099875 = 3149813) B3149813
theorem B6727205 : Blo 2099435 6727205 := bbase (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) (by norm_num)
theorem B4484803 : Blo 2099435 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B5979737 : Blo 2099435 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B3986491 : Blo 2099435 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B5315321 : Blo 2099435 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B3543547 : Blo 2099435 3543547 := bstep (se 1 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 3543547 = 5315321) B5315321
theorem B4724729 : Blo 2099435 4724729 := bstep (se 2 (by rfl) ⟨1771773, by rfl⟩ : syracuseStep 4724729 = 3543547) B3543547
theorem B3149819 : Blo 2099435 3149819 := bstep (se 1 (by rfl) ⟨2362364, by rfl⟩ : syracuseStep 3149819 = 4724729) B4724729
theorem B2099879 : Blo 2099435 2099879 := bstep (se 1 (by rfl) ⟨1574909, by rfl⟩ : syracuseStep 2099879 = 3149819) B3149819
theorem B2362369 : Blo 2099435 2362369 := bbase (se 2 (by rfl) ⟨885888, by rfl⟩ : syracuseStep 2362369 = 1771777) (by norm_num)
theorem B3149825 : Blo 2099435 3149825 := bstep (se 2 (by rfl) ⟨1181184, by rfl⟩ : syracuseStep 3149825 = 2362369) B2362369
theorem B2099883 : Blo 2099435 2099883 := bstep (se 1 (by rfl) ⟨1574912, by rfl⟩ : syracuseStep 2099883 = 3149825) B3149825
theorem B5315341 : Blo 2099435 5315341 := bbase (se 3 (by rfl) ⟨996626, by rfl⟩ : syracuseStep 5315341 = 1993253) (by norm_num)
theorem B7087121 : Blo 2099435 7087121 := bstep (se 2 (by rfl) ⟨2657670, by rfl⟩ : syracuseStep 7087121 = 5315341) B5315341
theorem B4724747 : Blo 2099435 4724747 := bstep (se 1 (by rfl) ⟨3543560, by rfl⟩ : syracuseStep 4724747 = 7087121) B7087121
theorem B3149831 : Blo 2099435 3149831 := bstep (se 1 (by rfl) ⟨2362373, by rfl⟩ : syracuseStep 3149831 = 4724747) B4724747
theorem B2099887 : Blo 2099435 2099887 := bstep (se 1 (by rfl) ⟨1574915, by rfl⟩ : syracuseStep 2099887 = 3149831) B3149831
theorem B3149837 : Blo 2099435 3149837 := bbase (se 3 (by rfl) ⟨590594, by rfl⟩ : syracuseStep 3149837 = 1181189) (by norm_num)
theorem B2099891 : Blo 2099435 2099891 := bstep (se 1 (by rfl) ⟨1574918, by rfl⟩ : syracuseStep 2099891 = 3149837) B3149837
theorem B4724765 : Blo 2099435 4724765 := bbase (se 3 (by rfl) ⟨885893, by rfl⟩ : syracuseStep 4724765 = 1771787) (by norm_num)
theorem B3149843 : Blo 2099435 3149843 := bstep (se 1 (by rfl) ⟨2362382, by rfl⟩ : syracuseStep 3149843 = 4724765) B4724765
theorem B2099895 : Blo 2099435 2099895 := bstep (se 1 (by rfl) ⟨1574921, by rfl⟩ : syracuseStep 2099895 = 3149843) B3149843
theorem B3543581 : Blo 2099435 3543581 := bbase (se 3 (by rfl) ⟨664421, by rfl⟩ : syracuseStep 3543581 = 1328843) (by norm_num)
theorem B2362387 : Blo 2099435 2362387 := bstep (se 1 (by rfl) ⟨1771790, by rfl⟩ : syracuseStep 2362387 = 3543581) B3543581
theorem B3149849 : Blo 2099435 3149849 := bstep (se 2 (by rfl) ⟨1181193, by rfl⟩ : syracuseStep 3149849 = 2362387) B2362387
theorem B2099899 : Blo 2099435 2099899 := bstep (se 1 (by rfl) ⟨1574924, by rfl⟩ : syracuseStep 2099899 = 3149849) B3149849
theorem B28025621 : Blo 2099435 28025621 := bbase (se 6 (by rfl) ⟨656850, by rfl⟩ : syracuseStep 28025621 = 1313701) (by norm_num)
theorem B18683747 : Blo 2099435 18683747 := bstep (se 1 (by rfl) ⟨14012810, by rfl⟩ : syracuseStep 18683747 = 28025621) B28025621
theorem B12455831 : Blo 2099435 12455831 := bstep (se 1 (by rfl) ⟨9341873, by rfl⟩ : syracuseStep 12455831 = 18683747) B18683747
theorem B8303887 : Blo 2099435 8303887 := bstep (se 1 (by rfl) ⟨6227915, by rfl⟩ : syracuseStep 8303887 = 12455831) B12455831
theorem B11071849 : Blo 2099435 11071849 := bstep (se 2 (by rfl) ⟨4151943, by rfl⟩ : syracuseStep 11071849 = 8303887) B8303887
theorem B14762465 : Blo 2099435 14762465 := bstep (se 2 (by rfl) ⟨5535924, by rfl⟩ : syracuseStep 14762465 = 11071849) B11071849
theorem B9841643 : Blo 2099435 9841643 := bstep (se 1 (by rfl) ⟨7381232, by rfl⟩ : syracuseStep 9841643 = 14762465) B14762465
theorem B6561095 : Blo 2099435 6561095 := bstep (se 1 (by rfl) ⟨4920821, by rfl⟩ : syracuseStep 6561095 = 9841643) B9841643
theorem B17496253 : Blo 2099435 17496253 := bstep (se 3 (by rfl) ⟨3280547, by rfl⟩ : syracuseStep 17496253 = 6561095) B6561095
theorem B23328337 : Blo 2099435 23328337 := bstep (se 2 (by rfl) ⟨8748126, by rfl⟩ : syracuseStep 23328337 = 17496253) B17496253
theorem B31104449 : Blo 2099435 31104449 := bstep (se 2 (by rfl) ⟨11664168, by rfl⟩ : syracuseStep 31104449 = 23328337) B23328337
theorem B20736299 : Blo 2099435 20736299 := bstep (se 1 (by rfl) ⟨15552224, by rfl⟩ : syracuseStep 20736299 = 31104449) B31104449
theorem B13824199 : Blo 2099435 13824199 := bstep (se 1 (by rfl) ⟨10368149, by rfl⟩ : syracuseStep 13824199 = 20736299) B20736299
theorem B73729061 : Blo 2099435 73729061 := bstep (se 4 (by rfl) ⟨6912099, by rfl⟩ : syracuseStep 73729061 = 13824199) B13824199
theorem B49152707 : Blo 2099435 49152707 := bstep (se 1 (by rfl) ⟨36864530, by rfl⟩ : syracuseStep 49152707 = 73729061) B73729061
theorem B32768471 : Blo 2099435 32768471 := bstep (se 1 (by rfl) ⟨24576353, by rfl⟩ : syracuseStep 32768471 = 49152707) B49152707
theorem B21845647 : Blo 2099435 21845647 := bstep (se 1 (by rfl) ⟨16384235, by rfl⟩ : syracuseStep 21845647 = 32768471) B32768471
theorem B29127529 : Blo 2099435 29127529 := bstep (se 2 (by rfl) ⟨10922823, by rfl⟩ : syracuseStep 29127529 = 21845647) B21845647
theorem B38836705 : Blo 2099435 38836705 := bstep (se 2 (by rfl) ⟨14563764, by rfl⟩ : syracuseStep 38836705 = 29127529) B29127529
theorem B51782273 : Blo 2099435 51782273 := bstep (se 2 (by rfl) ⟨19418352, by rfl⟩ : syracuseStep 51782273 = 38836705) B38836705
theorem B34521515 : Blo 2099435 34521515 := bstep (se 1 (by rfl) ⟨25891136, by rfl⟩ : syracuseStep 34521515 = 51782273) B51782273
theorem B23014343 : Blo 2099435 23014343 := bstep (se 1 (by rfl) ⟨17260757, by rfl⟩ : syracuseStep 23014343 = 34521515) B34521515
theorem B15342895 : Blo 2099435 15342895 := bstep (se 1 (by rfl) ⟨11507171, by rfl⟩ : syracuseStep 15342895 = 23014343) B23014343
theorem B20457193 : Blo 2099435 20457193 := bstep (se 2 (by rfl) ⟨7671447, by rfl⟩ : syracuseStep 20457193 = 15342895) B15342895
theorem B27276257 : Blo 2099435 27276257 := bstep (se 2 (by rfl) ⟨10228596, by rfl⟩ : syracuseStep 27276257 = 20457193) B20457193
theorem B18184171 : Blo 2099435 18184171 := bstep (se 1 (by rfl) ⟨13638128, by rfl⟩ : syracuseStep 18184171 = 27276257) B27276257
theorem B24245561 : Blo 2099435 24245561 := bstep (se 2 (by rfl) ⟨9092085, by rfl⟩ : syracuseStep 24245561 = 18184171) B18184171
theorem B16163707 : Blo 2099435 16163707 := bstep (se 1 (by rfl) ⟨12122780, by rfl⟩ : syracuseStep 16163707 = 24245561) B24245561
theorem B21551609 : Blo 2099435 21551609 := bstep (se 2 (by rfl) ⟨8081853, by rfl⟩ : syracuseStep 21551609 = 16163707) B16163707
theorem B57470957 : Blo 2099435 57470957 := bstep (se 3 (by rfl) ⟨10775804, by rfl⟩ : syracuseStep 57470957 = 21551609) B21551609
theorem B38313971 : Blo 2099435 38313971 := bstep (se 1 (by rfl) ⟨28735478, by rfl⟩ : syracuseStep 38313971 = 57470957) B57470957
theorem B25542647 : Blo 2099435 25542647 := bstep (se 1 (by rfl) ⟨19156985, by rfl⟩ : syracuseStep 25542647 = 38313971) B38313971
theorem B17028431 : Blo 2099435 17028431 := bstep (se 1 (by rfl) ⟨12771323, by rfl⟩ : syracuseStep 17028431 = 25542647) B25542647
theorem B11352287 : Blo 2099435 11352287 := bstep (se 1 (by rfl) ⟨8514215, by rfl⟩ : syracuseStep 11352287 = 17028431) B17028431
theorem B7568191 : Blo 2099435 7568191 := bstep (se 1 (by rfl) ⟨5676143, by rfl⟩ : syracuseStep 7568191 = 11352287) B11352287
theorem B10090921 : Blo 2099435 10090921 := bstep (se 2 (by rfl) ⟨3784095, by rfl⟩ : syracuseStep 10090921 = 7568191) B7568191
theorem B13454561 : Blo 2099435 13454561 := bstep (se 2 (by rfl) ⟨5045460, by rfl⟩ : syracuseStep 13454561 = 10090921) B10090921
theorem B8969707 : Blo 2099435 8969707 := bstep (se 1 (by rfl) ⟨6727280, by rfl⟩ : syracuseStep 8969707 = 13454561) B13454561
theorem B11959609 : Blo 2099435 11959609 := bstep (se 2 (by rfl) ⟨4484853, by rfl⟩ : syracuseStep 11959609 = 8969707) B8969707
theorem B15946145 : Blo 2099435 15946145 := bstep (se 2 (by rfl) ⟨5979804, by rfl⟩ : syracuseStep 15946145 = 11959609) B11959609
theorem B10630763 : Blo 2099435 10630763 := bstep (se 1 (by rfl) ⟨7973072, by rfl⟩ : syracuseStep 10630763 = 15946145) B15946145
theorem B7087175 : Blo 2099435 7087175 := bstep (se 1 (by rfl) ⟨5315381, by rfl⟩ : syracuseStep 7087175 = 10630763) B10630763
theorem B4724783 : Blo 2099435 4724783 := bstep (se 1 (by rfl) ⟨3543587, by rfl⟩ : syracuseStep 4724783 = 7087175) B7087175
theorem B3149855 : Blo 2099435 3149855 := bstep (se 1 (by rfl) ⟨2362391, by rfl⟩ : syracuseStep 3149855 = 4724783) B4724783
theorem B2099903 : Blo 2099435 2099903 := bstep (se 1 (by rfl) ⟨1574927, by rfl⟩ : syracuseStep 2099903 = 3149855) B3149855
theorem B3149861 : Blo 2099435 3149861 := bbase (se 4 (by rfl) ⟨295299, by rfl⟩ : syracuseStep 3149861 = 590599) (by norm_num)
theorem B2099907 : Blo 2099435 2099907 := bstep (se 1 (by rfl) ⟨1574930, by rfl⟩ : syracuseStep 2099907 = 3149861) B3149861
theorem B2657701 : Blo 2099435 2657701 := bbase (se 4 (by rfl) ⟨249159, by rfl⟩ : syracuseStep 2657701 = 498319) (by norm_num)
theorem B3543601 : Blo 2099435 3543601 := bstep (se 2 (by rfl) ⟨1328850, by rfl⟩ : syracuseStep 3543601 = 2657701) B2657701
theorem B4724801 : Blo 2099435 4724801 := bstep (se 2 (by rfl) ⟨1771800, by rfl⟩ : syracuseStep 4724801 = 3543601) B3543601
theorem B3149867 : Blo 2099435 3149867 := bstep (se 1 (by rfl) ⟨2362400, by rfl⟩ : syracuseStep 3149867 = 4724801) B4724801
theorem B2099911 : Blo 2099435 2099911 := bstep (se 1 (by rfl) ⟨1574933, by rfl⟩ : syracuseStep 2099911 = 3149867) B3149867
theorem B2362405 : Blo 2099435 2362405 := bbase (se 4 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 2362405 = 442951) (by norm_num)
theorem B3149873 : Blo 2099435 3149873 := bstep (se 2 (by rfl) ⟨1181202, by rfl⟩ : syracuseStep 3149873 = 2362405) B2362405
theorem B2099915 : Blo 2099435 2099915 := bstep (se 1 (by rfl) ⟨1574936, by rfl⟩ : syracuseStep 2099915 = 3149873) B3149873
theorem B6727333 : Blo 2099435 6727333 := bbase (se 4 (by rfl) ⟨630687, by rfl⟩ : syracuseStep 6727333 = 1261375) (by norm_num)
theorem B8969777 : Blo 2099435 8969777 := bstep (se 2 (by rfl) ⟨3363666, by rfl⟩ : syracuseStep 8969777 = 6727333) B6727333
theorem B5979851 : Blo 2099435 5979851 := bstep (se 1 (by rfl) ⟨4484888, by rfl⟩ : syracuseStep 5979851 = 8969777) B8969777
theorem B3986567 : Blo 2099435 3986567 := bstep (se 1 (by rfl) ⟨2989925, by rfl⟩ : syracuseStep 3986567 = 5979851) B5979851
theorem B2657711 : Blo 2099435 2657711 := bstep (se 1 (by rfl) ⟨1993283, by rfl⟩ : syracuseStep 2657711 = 3986567) B3986567
theorem B7087229 : Blo 2099435 7087229 := bstep (se 3 (by rfl) ⟨1328855, by rfl⟩ : syracuseStep 7087229 = 2657711) B2657711
theorem B4724819 : Blo 2099435 4724819 := bstep (se 1 (by rfl) ⟨3543614, by rfl⟩ : syracuseStep 4724819 = 7087229) B7087229
theorem B3149879 : Blo 2099435 3149879 := bstep (se 1 (by rfl) ⟨2362409, by rfl⟩ : syracuseStep 3149879 = 4724819) B4724819
theorem B2099919 : Blo 2099435 2099919 := bstep (se 1 (by rfl) ⟨1574939, by rfl⟩ : syracuseStep 2099919 = 3149879) B3149879
theorem B3149885 : Blo 2099435 3149885 := bbase (se 3 (by rfl) ⟨590603, by rfl⟩ : syracuseStep 3149885 = 1181207) (by norm_num)
theorem B2099923 : Blo 2099435 2099923 := bstep (se 1 (by rfl) ⟨1574942, by rfl⟩ : syracuseStep 2099923 = 3149885) B3149885
theorem B4724837 : Blo 2099435 4724837 := bbase (se 4 (by rfl) ⟨442953, by rfl⟩ : syracuseStep 4724837 = 885907) (by norm_num)
theorem B3149891 : Blo 2099435 3149891 := bstep (se 1 (by rfl) ⟨2362418, by rfl⟩ : syracuseStep 3149891 = 4724837) B4724837
theorem B2099927 : Blo 2099435 2099927 := bstep (se 1 (by rfl) ⟨1574945, by rfl⟩ : syracuseStep 2099927 = 3149891) B3149891
theorem B5315453 : Blo 2099435 5315453 := bbase (se 3 (by rfl) ⟨996647, by rfl⟩ : syracuseStep 5315453 = 1993295) (by norm_num)
theorem B3543635 : Blo 2099435 3543635 := bstep (se 1 (by rfl) ⟨2657726, by rfl⟩ : syracuseStep 3543635 = 5315453) B5315453
theorem B2362423 : Blo 2099435 2362423 := bstep (se 1 (by rfl) ⟨1771817, by rfl⟩ : syracuseStep 2362423 = 3543635) B3543635
theorem B3149897 : Blo 2099435 3149897 := bstep (se 2 (by rfl) ⟨1181211, by rfl⟩ : syracuseStep 3149897 = 2362423) B2362423
theorem B2099931 : Blo 2099435 2099931 := bstep (se 1 (by rfl) ⟨1574948, by rfl⟩ : syracuseStep 2099931 = 3149897) B3149897
theorem B3986597 : Blo 2099435 3986597 := bbase (se 4 (by rfl) ⟨373743, by rfl⟩ : syracuseStep 3986597 = 747487) (by norm_num)
theorem B10630925 : Blo 2099435 10630925 := bstep (se 3 (by rfl) ⟨1993298, by rfl⟩ : syracuseStep 10630925 = 3986597) B3986597
theorem B7087283 : Blo 2099435 7087283 := bstep (se 1 (by rfl) ⟨5315462, by rfl⟩ : syracuseStep 7087283 = 10630925) B10630925
theorem B4724855 : Blo 2099435 4724855 := bstep (se 1 (by rfl) ⟨3543641, by rfl⟩ : syracuseStep 4724855 = 7087283) B7087283
theorem B3149903 : Blo 2099435 3149903 := bstep (se 1 (by rfl) ⟨2362427, by rfl⟩ : syracuseStep 3149903 = 4724855) B4724855
theorem B2099935 : Blo 2099435 2099935 := bstep (se 1 (by rfl) ⟨1574951, by rfl⟩ : syracuseStep 2099935 = 3149903) B3149903
theorem B3149909 : Blo 2099435 3149909 := bbase (se 8 (by rfl) ⟨18456, by rfl⟩ : syracuseStep 3149909 = 36913) (by norm_num)
theorem B2099939 : Blo 2099435 2099939 := bstep (se 1 (by rfl) ⟨1574954, by rfl⟩ : syracuseStep 2099939 = 3149909) B3149909
theorem B20182229 : Blo 2099435 20182229 := bbase (se 7 (by rfl) ⟨236510, by rfl⟩ : syracuseStep 20182229 = 473021) (by norm_num)
theorem B13454819 : Blo 2099435 13454819 := bstep (se 1 (by rfl) ⟨10091114, by rfl⟩ : syracuseStep 13454819 = 20182229) B20182229
theorem B8969879 : Blo 2099435 8969879 := bstep (se 1 (by rfl) ⟨6727409, by rfl⟩ : syracuseStep 8969879 = 13454819) B13454819
theorem B5979919 : Blo 2099435 5979919 := bstep (se 1 (by rfl) ⟨4484939, by rfl⟩ : syracuseStep 5979919 = 8969879) B8969879
theorem B7973225 : Blo 2099435 7973225 := bstep (se 2 (by rfl) ⟨2989959, by rfl⟩ : syracuseStep 7973225 = 5979919) B5979919
theorem B5315483 : Blo 2099435 5315483 := bstep (se 1 (by rfl) ⟨3986612, by rfl⟩ : syracuseStep 5315483 = 7973225) B7973225
theorem B3543655 : Blo 2099435 3543655 := bstep (se 1 (by rfl) ⟨2657741, by rfl⟩ : syracuseStep 3543655 = 5315483) B5315483
theorem B4724873 : Blo 2099435 4724873 := bstep (se 2 (by rfl) ⟨1771827, by rfl⟩ : syracuseStep 4724873 = 3543655) B3543655
theorem B3149915 : Blo 2099435 3149915 := bstep (se 1 (by rfl) ⟨2362436, by rfl⟩ : syracuseStep 3149915 = 4724873) B4724873
theorem B2099943 : Blo 2099435 2099943 := bstep (se 1 (by rfl) ⟨1574957, by rfl⟩ : syracuseStep 2099943 = 3149915) B3149915
theorem B2362441 : Blo 2099435 2362441 := bbase (se 2 (by rfl) ⟨885915, by rfl⟩ : syracuseStep 2362441 = 1771831) (by norm_num)
theorem B3149921 : Blo 2099435 3149921 := bstep (se 2 (by rfl) ⟨1181220, by rfl⟩ : syracuseStep 3149921 = 2362441) B2362441
theorem B2099947 : Blo 2099435 2099947 := bstep (se 1 (by rfl) ⟨1574960, by rfl⟩ : syracuseStep 2099947 = 3149921) B3149921
theorem B13454869 : Blo 2099435 13454869 := bbase (se 6 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 13454869 = 630697) (by norm_num)
theorem B17939825 : Blo 2099435 17939825 := bstep (se 2 (by rfl) ⟨6727434, by rfl⟩ : syracuseStep 17939825 = 13454869) B13454869
theorem B11959883 : Blo 2099435 11959883 := bstep (se 1 (by rfl) ⟨8969912, by rfl⟩ : syracuseStep 11959883 = 17939825) B17939825
theorem B7973255 : Blo 2099435 7973255 := bstep (se 1 (by rfl) ⟨5979941, by rfl⟩ : syracuseStep 7973255 = 11959883) B11959883
theorem B5315503 : Blo 2099435 5315503 := bstep (se 1 (by rfl) ⟨3986627, by rfl⟩ : syracuseStep 5315503 = 7973255) B7973255
theorem B7087337 : Blo 2099435 7087337 := bstep (se 2 (by rfl) ⟨2657751, by rfl⟩ : syracuseStep 7087337 = 5315503) B5315503
theorem B4724891 : Blo 2099435 4724891 := bstep (se 1 (by rfl) ⟨3543668, by rfl⟩ : syracuseStep 4724891 = 7087337) B7087337
theorem B3149927 : Blo 2099435 3149927 := bstep (se 1 (by rfl) ⟨2362445, by rfl⟩ : syracuseStep 3149927 = 4724891) B4724891
theorem B2099951 : Blo 2099435 2099951 := bstep (se 1 (by rfl) ⟨1574963, by rfl⟩ : syracuseStep 2099951 = 3149927) B3149927
theorem B3149933 : Blo 2099435 3149933 := bbase (se 3 (by rfl) ⟨590612, by rfl⟩ : syracuseStep 3149933 = 1181225) (by norm_num)
theorem B2099955 : Blo 2099435 2099955 := bstep (se 1 (by rfl) ⟨1574966, by rfl⟩ : syracuseStep 2099955 = 3149933) B3149933
theorem B4724909 : Blo 2099435 4724909 := bbase (se 3 (by rfl) ⟨885920, by rfl⟩ : syracuseStep 4724909 = 1771841) (by norm_num)
theorem B3149939 : Blo 2099435 3149939 := bstep (se 1 (by rfl) ⟨2362454, by rfl⟩ : syracuseStep 3149939 = 4724909) B4724909
theorem B2099959 : Blo 2099435 2099959 := bstep (se 1 (by rfl) ⟨1574969, by rfl⟩ : syracuseStep 2099959 = 3149939) B3149939
theorem B3784205 : Blo 2099435 3784205 := bbase (se 3 (by rfl) ⟨709538, by rfl⟩ : syracuseStep 3784205 = 1419077) (by norm_num)
theorem B10091213 : Blo 2099435 10091213 := bstep (se 3 (by rfl) ⟨1892102, by rfl⟩ : syracuseStep 10091213 = 3784205) B3784205
theorem B6727475 : Blo 2099435 6727475 := bstep (se 1 (by rfl) ⟨5045606, by rfl⟩ : syracuseStep 6727475 = 10091213) B10091213
theorem B4484983 : Blo 2099435 4484983 := bstep (se 1 (by rfl) ⟨3363737, by rfl⟩ : syracuseStep 4484983 = 6727475) B6727475
theorem B5979977 : Blo 2099435 5979977 := bstep (se 2 (by rfl) ⟨2242491, by rfl⟩ : syracuseStep 5979977 = 4484983) B4484983
theorem B3986651 : Blo 2099435 3986651 := bstep (se 1 (by rfl) ⟨2989988, by rfl⟩ : syracuseStep 3986651 = 5979977) B5979977
theorem B2657767 : Blo 2099435 2657767 := bstep (se 1 (by rfl) ⟨1993325, by rfl⟩ : syracuseStep 2657767 = 3986651) B3986651
theorem B3543689 : Blo 2099435 3543689 := bstep (se 2 (by rfl) ⟨1328883, by rfl⟩ : syracuseStep 3543689 = 2657767) B2657767
theorem B2362459 : Blo 2099435 2362459 := bstep (se 1 (by rfl) ⟨1771844, by rfl⟩ : syracuseStep 2362459 = 3543689) B3543689
theorem B3149945 : Blo 2099435 3149945 := bstep (se 2 (by rfl) ⟨1181229, by rfl⟩ : syracuseStep 3149945 = 2362459) B2362459
theorem B2099963 : Blo 2099435 2099963 := bstep (se 1 (by rfl) ⟨1574972, by rfl⟩ : syracuseStep 2099963 = 3149945) B3149945
theorem B2394697 : Blo 2099435 2394697 := bbase (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) (by norm_num)
theorem B3192929 : Blo 2099435 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B2128619 : Blo 2099435 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B5676317 : Blo 2099435 5676317 := bstep (se 3 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 5676317 = 2128619) B2128619
theorem B3784211 : Blo 2099435 3784211 := bstep (se 1 (by rfl) ⟨2838158, by rfl⟩ : syracuseStep 3784211 = 5676317) B5676317
theorem B2522807 : Blo 2099435 2522807 := bstep (se 1 (by rfl) ⟨1892105, by rfl⟩ : syracuseStep 2522807 = 3784211) B3784211
theorem B26909941 : Blo 2099435 26909941 := bstep (se 5 (by rfl) ⟨1261403, by rfl⟩ : syracuseStep 26909941 = 2522807) B2522807
theorem B35879921 : Blo 2099435 35879921 := bstep (se 2 (by rfl) ⟨13454970, by rfl⟩ : syracuseStep 35879921 = 26909941) B26909941
theorem B23919947 : Blo 2099435 23919947 := bstep (se 1 (by rfl) ⟨17939960, by rfl⟩ : syracuseStep 23919947 = 35879921) B35879921
theorem B15946631 : Blo 2099435 15946631 := bstep (se 1 (by rfl) ⟨11959973, by rfl⟩ : syracuseStep 15946631 = 23919947) B23919947
theorem B10631087 : Blo 2099435 10631087 := bstep (se 1 (by rfl) ⟨7973315, by rfl⟩ : syracuseStep 10631087 = 15946631) B15946631
theorem B7087391 : Blo 2099435 7087391 := bstep (se 1 (by rfl) ⟨5315543, by rfl⟩ : syracuseStep 7087391 = 10631087) B10631087
theorem B4724927 : Blo 2099435 4724927 := bstep (se 1 (by rfl) ⟨3543695, by rfl⟩ : syracuseStep 4724927 = 7087391) B7087391
theorem B3149951 : Blo 2099435 3149951 := bstep (se 1 (by rfl) ⟨2362463, by rfl⟩ : syracuseStep 3149951 = 4724927) B4724927
theorem B2099967 : Blo 2099435 2099967 := bstep (se 1 (by rfl) ⟨1574975, by rfl⟩ : syracuseStep 2099967 = 3149951) B3149951
theorem B3149957 : Blo 2099435 3149957 := bbase (se 4 (by rfl) ⟨295308, by rfl⟩ : syracuseStep 3149957 = 590617) (by norm_num)
theorem B2099971 : Blo 2099435 2099971 := bstep (se 1 (by rfl) ⟨1574978, by rfl⟩ : syracuseStep 2099971 = 3149957) B3149957
theorem B3543709 : Blo 2099435 3543709 := bbase (se 3 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 3543709 = 1328891) (by norm_num)
theorem B4724945 : Blo 2099435 4724945 := bstep (se 2 (by rfl) ⟨1771854, by rfl⟩ : syracuseStep 4724945 = 3543709) B3543709
theorem B3149963 : Blo 2099435 3149963 := bstep (se 1 (by rfl) ⟨2362472, by rfl⟩ : syracuseStep 3149963 = 4724945) B4724945
theorem B2099975 : Blo 2099435 2099975 := bstep (se 1 (by rfl) ⟨1574981, by rfl⟩ : syracuseStep 2099975 = 3149963) B3149963
theorem B2362477 : Blo 2099435 2362477 := bbase (se 3 (by rfl) ⟨442964, by rfl⟩ : syracuseStep 2362477 = 885929) (by norm_num)
theorem B3149969 : Blo 2099435 3149969 := bstep (se 2 (by rfl) ⟨1181238, by rfl⟩ : syracuseStep 3149969 = 2362477) B2362477
theorem B2099979 : Blo 2099435 2099979 := bstep (se 1 (by rfl) ⟨1574984, by rfl⟩ : syracuseStep 2099979 = 3149969) B3149969
theorem B7087445 : Blo 2099435 7087445 := bbase (se 12 (by rfl) ⟨2595, by rfl⟩ : syracuseStep 7087445 = 5191) (by norm_num)
theorem B4724963 : Blo 2099435 4724963 := bstep (se 1 (by rfl) ⟨3543722, by rfl⟩ : syracuseStep 4724963 = 7087445) B7087445
theorem B3149975 : Blo 2099435 3149975 := bstep (se 1 (by rfl) ⟨2362481, by rfl⟩ : syracuseStep 3149975 = 4724963) B4724963
theorem B2099983 : Blo 2099435 2099983 := bstep (se 1 (by rfl) ⟨1574987, by rfl⟩ : syracuseStep 2099983 = 3149975) B3149975
theorem B3149981 : Blo 2099435 3149981 := bbase (se 3 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 3149981 = 1181243) (by norm_num)
theorem B2099987 : Blo 2099435 2099987 := bstep (se 1 (by rfl) ⟨1574990, by rfl⟩ : syracuseStep 2099987 = 3149981) B3149981
theorem B4724981 : Blo 2099435 4724981 := bbase (se 5 (by rfl) ⟨221483, by rfl⟩ : syracuseStep 4724981 = 442967) (by norm_num)
theorem B3149987 : Blo 2099435 3149987 := bstep (se 1 (by rfl) ⟨2362490, by rfl⟩ : syracuseStep 3149987 = 4724981) B4724981
theorem B2099991 : Blo 2099435 2099991 := bstep (se 1 (by rfl) ⟨1574993, by rfl⟩ : syracuseStep 2099991 = 3149987) B3149987
theorem B3592093 : Blo 2099435 3592093 := bbase (se 3 (by rfl) ⟨673517, by rfl⟩ : syracuseStep 3592093 = 1347035) (by norm_num)
theorem B4789457 : Blo 2099435 4789457 := bstep (se 2 (by rfl) ⟨1796046, by rfl⟩ : syracuseStep 4789457 = 3592093) B3592093
theorem B3192971 : Blo 2099435 3192971 := bstep (se 1 (by rfl) ⟨2394728, by rfl⟩ : syracuseStep 3192971 = 4789457) B4789457
theorem B34058357 : Blo 2099435 34058357 := bstep (se 5 (by rfl) ⟨1596485, by rfl⟩ : syracuseStep 34058357 = 3192971) B3192971
theorem B22705571 : Blo 2099435 22705571 := bstep (se 1 (by rfl) ⟨17029178, by rfl⟩ : syracuseStep 22705571 = 34058357) B34058357
theorem B15137047 : Blo 2099435 15137047 := bstep (se 1 (by rfl) ⟨11352785, by rfl⟩ : syracuseStep 15137047 = 22705571) B22705571
theorem B20182729 : Blo 2099435 20182729 := bstep (se 2 (by rfl) ⟨7568523, by rfl⟩ : syracuseStep 20182729 = 15137047) B15137047
theorem B26910305 : Blo 2099435 26910305 := bstep (se 2 (by rfl) ⟨10091364, by rfl⟩ : syracuseStep 26910305 = 20182729) B20182729
theorem B17940203 : Blo 2099435 17940203 := bstep (se 1 (by rfl) ⟨13455152, by rfl⟩ : syracuseStep 17940203 = 26910305) B26910305
theorem B11960135 : Blo 2099435 11960135 := bstep (se 1 (by rfl) ⟨8970101, by rfl⟩ : syracuseStep 11960135 = 17940203) B17940203
theorem B7973423 : Blo 2099435 7973423 := bstep (se 1 (by rfl) ⟨5980067, by rfl⟩ : syracuseStep 7973423 = 11960135) B11960135
theorem B5315615 : Blo 2099435 5315615 := bstep (se 1 (by rfl) ⟨3986711, by rfl⟩ : syracuseStep 5315615 = 7973423) B7973423
theorem B3543743 : Blo 2099435 3543743 := bstep (se 1 (by rfl) ⟨2657807, by rfl⟩ : syracuseStep 3543743 = 5315615) B5315615
theorem B2362495 : Blo 2099435 2362495 := bstep (se 1 (by rfl) ⟨1771871, by rfl⟩ : syracuseStep 2362495 = 3543743) B3543743
theorem B3149993 : Blo 2099435 3149993 := bstep (se 2 (by rfl) ⟨1181247, by rfl⟩ : syracuseStep 3149993 = 2362495) B2362495
theorem B2099995 : Blo 2099435 2099995 := bstep (se 1 (by rfl) ⟨1574996, by rfl⟩ : syracuseStep 2099995 = 3149993) B3149993
theorem B6727589 : Blo 2099435 6727589 := bbase (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) (by norm_num)
theorem B4485059 : Blo 2099435 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B2990039 : Blo 2099435 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B7973437 : Blo 2099435 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B10631249 : Blo 2099435 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B7087499 : Blo 2099435 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B4724999 : Blo 2099435 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B3149999 : Blo 2099435 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B2099999 : Blo 2099435 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B3150005 : Blo 2099435 3150005 := bbase (se 5 (by rfl) ⟨147656, by rfl⟩ : syracuseStep 3150005 = 295313) (by norm_num)
theorem B2100003 : Blo 2099435 2100003 := bstep (se 1 (by rfl) ⟨1575002, by rfl⟩ : syracuseStep 2100003 = 3150005) B3150005
theorem B5315645 : Blo 2099435 5315645 := bbase (se 3 (by rfl) ⟨996683, by rfl⟩ : syracuseStep 5315645 = 1993367) (by norm_num)
theorem B3543763 : Blo 2099435 3543763 := bstep (se 1 (by rfl) ⟨2657822, by rfl⟩ : syracuseStep 3543763 = 5315645) B5315645
theorem B4725017 : Blo 2099435 4725017 := bstep (se 2 (by rfl) ⟨1771881, by rfl⟩ : syracuseStep 4725017 = 3543763) B3543763
theorem B3150011 : Blo 2099435 3150011 := bstep (se 1 (by rfl) ⟨2362508, by rfl⟩ : syracuseStep 3150011 = 4725017) B4725017
theorem B2100007 : Blo 2099435 2100007 := bstep (se 1 (by rfl) ⟨1575005, by rfl⟩ : syracuseStep 2100007 = 3150011) B3150011
theorem B2362513 : Blo 2099435 2362513 := bbase (se 2 (by rfl) ⟨885942, by rfl⟩ : syracuseStep 2362513 = 1771885) (by norm_num)
theorem B3150017 : Blo 2099435 3150017 := bstep (se 2 (by rfl) ⟨1181256, by rfl⟩ : syracuseStep 3150017 = 2362513) B2362513
theorem B2100011 : Blo 2099435 2100011 := bstep (se 1 (by rfl) ⟨1575008, by rfl⟩ : syracuseStep 2100011 = 3150017) B3150017
theorem B3986749 : Blo 2099435 3986749 := bbase (se 3 (by rfl) ⟨747515, by rfl⟩ : syracuseStep 3986749 = 1495031) (by norm_num)
theorem B5315665 : Blo 2099435 5315665 := bstep (se 2 (by rfl) ⟨1993374, by rfl⟩ : syracuseStep 5315665 = 3986749) B3986749
theorem B7087553 : Blo 2099435 7087553 := bstep (se 2 (by rfl) ⟨2657832, by rfl⟩ : syracuseStep 7087553 = 5315665) B5315665
theorem B4725035 : Blo 2099435 4725035 := bstep (se 1 (by rfl) ⟨3543776, by rfl⟩ : syracuseStep 4725035 = 7087553) B7087553
theorem B3150023 : Blo 2099435 3150023 := bstep (se 1 (by rfl) ⟨2362517, by rfl⟩ : syracuseStep 3150023 = 4725035) B4725035
theorem B2100015 : Blo 2099435 2100015 := bstep (se 1 (by rfl) ⟨1575011, by rfl⟩ : syracuseStep 2100015 = 3150023) B3150023
theorem B3150029 : Blo 2099435 3150029 := bbase (se 3 (by rfl) ⟨590630, by rfl⟩ : syracuseStep 3150029 = 1181261) (by norm_num)
theorem B2100019 : Blo 2099435 2100019 := bstep (se 1 (by rfl) ⟨1575014, by rfl⟩ : syracuseStep 2100019 = 3150029) B3150029
theorem B4725053 : Blo 2099435 4725053 := bbase (se 3 (by rfl) ⟨885947, by rfl⟩ : syracuseStep 4725053 = 1771895) (by norm_num)
theorem B3150035 : Blo 2099435 3150035 := bstep (se 1 (by rfl) ⟨2362526, by rfl⟩ : syracuseStep 3150035 = 4725053) B4725053
theorem B2100023 : Blo 2099435 2100023 := bstep (se 1 (by rfl) ⟨1575017, by rfl⟩ : syracuseStep 2100023 = 3150035) B3150035
theorem B3543797 : Blo 2099435 3543797 := bbase (se 5 (by rfl) ⟨166115, by rfl⟩ : syracuseStep 3543797 = 332231) (by norm_num)
theorem B2362531 : Blo 2099435 2362531 := bstep (se 1 (by rfl) ⟨1771898, by rfl⟩ : syracuseStep 2362531 = 3543797) B3543797
theorem B3150041 : Blo 2099435 3150041 := bstep (se 2 (by rfl) ⟨1181265, by rfl⟩ : syracuseStep 3150041 = 2362531) B2362531
theorem B2100027 : Blo 2099435 2100027 := bstep (se 1 (by rfl) ⟨1575020, by rfl⟩ : syracuseStep 2100027 = 3150041) B3150041
theorem B2838245 : Blo 2099435 2838245 := bbase (se 4 (by rfl) ⟨266085, by rfl⟩ : syracuseStep 2838245 = 532171) (by norm_num)
theorem B7568653 : Blo 2099435 7568653 := bstep (se 3 (by rfl) ⟨1419122, by rfl⟩ : syracuseStep 7568653 = 2838245) B2838245
theorem B10091537 : Blo 2099435 10091537 := bstep (se 2 (by rfl) ⟨3784326, by rfl⟩ : syracuseStep 10091537 = 7568653) B7568653
theorem B6727691 : Blo 2099435 6727691 := bstep (se 1 (by rfl) ⟨5045768, by rfl⟩ : syracuseStep 6727691 = 10091537) B10091537
theorem B4485127 : Blo 2099435 4485127 := bstep (se 1 (by rfl) ⟨3363845, by rfl⟩ : syracuseStep 4485127 = 6727691) B6727691
theorem B5980169 : Blo 2099435 5980169 := bstep (se 2 (by rfl) ⟨2242563, by rfl⟩ : syracuseStep 5980169 = 4485127) B4485127
theorem B15947117 : Blo 2099435 15947117 := bstep (se 3 (by rfl) ⟨2990084, by rfl⟩ : syracuseStep 15947117 = 5980169) B5980169
theorem B10631411 : Blo 2099435 10631411 := bstep (se 1 (by rfl) ⟨7973558, by rfl⟩ : syracuseStep 10631411 = 15947117) B15947117
theorem B7087607 : Blo 2099435 7087607 := bstep (se 1 (by rfl) ⟨5315705, by rfl⟩ : syracuseStep 7087607 = 10631411) B10631411
theorem B4725071 : Blo 2099435 4725071 := bstep (se 1 (by rfl) ⟨3543803, by rfl⟩ : syracuseStep 4725071 = 7087607) B7087607
theorem B3150047 : Blo 2099435 3150047 := bstep (se 1 (by rfl) ⟨2362535, by rfl⟩ : syracuseStep 3150047 = 4725071) B4725071
theorem B2100031 : Blo 2099435 2100031 := bstep (se 1 (by rfl) ⟨1575023, by rfl⟩ : syracuseStep 2100031 = 3150047) B3150047
theorem B3150053 : Blo 2099435 3150053 := bbase (se 4 (by rfl) ⟨295317, by rfl⟩ : syracuseStep 3150053 = 590635) (by norm_num)
theorem B2100035 : Blo 2099435 2100035 := bstep (se 1 (by rfl) ⟨1575026, by rfl⟩ : syracuseStep 2100035 = 3150053) B3150053
theorem B5045789 : Blo 2099435 5045789 := bbase (se 3 (by rfl) ⟨946085, by rfl⟩ : syracuseStep 5045789 = 1892171) (by norm_num)
theorem B3363859 : Blo 2099435 3363859 := bstep (se 1 (by rfl) ⟨2522894, by rfl⟩ : syracuseStep 3363859 = 5045789) B5045789
theorem B4485145 : Blo 2099435 4485145 := bstep (se 2 (by rfl) ⟨1681929, by rfl⟩ : syracuseStep 4485145 = 3363859) B3363859
theorem B5980193 : Blo 2099435 5980193 := bstep (se 2 (by rfl) ⟨2242572, by rfl⟩ : syracuseStep 5980193 = 4485145) B4485145
theorem B3986795 : Blo 2099435 3986795 := bstep (se 1 (by rfl) ⟨2990096, by rfl⟩ : syracuseStep 3986795 = 5980193) B5980193
theorem B2657863 : Blo 2099435 2657863 := bstep (se 1 (by rfl) ⟨1993397, by rfl⟩ : syracuseStep 2657863 = 3986795) B3986795
theorem B3543817 : Blo 2099435 3543817 := bstep (se 2 (by rfl) ⟨1328931, by rfl⟩ : syracuseStep 3543817 = 2657863) B2657863
theorem B4725089 : Blo 2099435 4725089 := bstep (se 2 (by rfl) ⟨1771908, by rfl⟩ : syracuseStep 4725089 = 3543817) B3543817
theorem B3150059 : Blo 2099435 3150059 := bstep (se 1 (by rfl) ⟨2362544, by rfl⟩ : syracuseStep 3150059 = 4725089) B4725089
theorem B2100039 : Blo 2099435 2100039 := bstep (se 1 (by rfl) ⟨1575029, by rfl⟩ : syracuseStep 2100039 = 3150059) B3150059
theorem B2362549 : Blo 2099435 2362549 := bbase (se 5 (by rfl) ⟨110744, by rfl⟩ : syracuseStep 2362549 = 221489) (by norm_num)
theorem B3150065 : Blo 2099435 3150065 := bstep (se 2 (by rfl) ⟨1181274, by rfl⟩ : syracuseStep 3150065 = 2362549) B2362549
theorem B2100043 : Blo 2099435 2100043 := bstep (se 1 (by rfl) ⟨1575032, by rfl⟩ : syracuseStep 2100043 = 3150065) B3150065
theorem B2657873 : Blo 2099435 2657873 := bbase (se 2 (by rfl) ⟨996702, by rfl⟩ : syracuseStep 2657873 = 1993405) (by norm_num)
theorem B7087661 : Blo 2099435 7087661 := bstep (se 3 (by rfl) ⟨1328936, by rfl⟩ : syracuseStep 7087661 = 2657873) B2657873
theorem B4725107 : Blo 2099435 4725107 := bstep (se 1 (by rfl) ⟨3543830, by rfl⟩ : syracuseStep 4725107 = 7087661) B7087661
theorem B3150071 : Blo 2099435 3150071 := bstep (se 1 (by rfl) ⟨2362553, by rfl⟩ : syracuseStep 3150071 = 4725107) B4725107
theorem B2100047 : Blo 2099435 2100047 := bstep (se 1 (by rfl) ⟨1575035, by rfl⟩ : syracuseStep 2100047 = 3150071) B3150071
theorem B3150077 : Blo 2099435 3150077 := bbase (se 3 (by rfl) ⟨590639, by rfl⟩ : syracuseStep 3150077 = 1181279) (by norm_num)
theorem B2100051 : Blo 2099435 2100051 := bstep (se 1 (by rfl) ⟨1575038, by rfl⟩ : syracuseStep 2100051 = 3150077) B3150077
theorem B4725125 : Blo 2099435 4725125 := bbase (se 4 (by rfl) ⟨442980, by rfl⟩ : syracuseStep 4725125 = 885961) (by norm_num)
theorem B3150083 : Blo 2099435 3150083 := bstep (se 1 (by rfl) ⟨2362562, by rfl⟩ : syracuseStep 3150083 = 4725125) B4725125
theorem B2100055 : Blo 2099435 2100055 := bstep (se 1 (by rfl) ⟨1575041, by rfl⟩ : syracuseStep 2100055 = 3150083) B3150083
theorem B2990125 : Blo 2099435 2990125 := bbase (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) (by norm_num)
theorem B3986833 : Blo 2099435 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B5315777 : Blo 2099435 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B3543851 : Blo 2099435 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B2362567 : Blo 2099435 2362567 := bstep (se 1 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 2362567 = 3543851) B3543851
theorem B3150089 : Blo 2099435 3150089 := bstep (se 2 (by rfl) ⟨1181283, by rfl⟩ : syracuseStep 3150089 = 2362567) B2362567
theorem B2100059 : Blo 2099435 2100059 := bstep (se 1 (by rfl) ⟨1575044, by rfl⟩ : syracuseStep 2100059 = 3150089) B3150089
theorem B10631573 : Blo 2099435 10631573 := bbase (se 6 (by rfl) ⟨249177, by rfl⟩ : syracuseStep 10631573 = 498355) (by norm_num)
theorem B7087715 : Blo 2099435 7087715 := bstep (se 1 (by rfl) ⟨5315786, by rfl⟩ : syracuseStep 7087715 = 10631573) B10631573
theorem B4725143 : Blo 2099435 4725143 := bstep (se 1 (by rfl) ⟨3543857, by rfl⟩ : syracuseStep 4725143 = 7087715) B7087715
theorem B3150095 : Blo 2099435 3150095 := bstep (se 1 (by rfl) ⟨2362571, by rfl⟩ : syracuseStep 3150095 = 4725143) B4725143
theorem B2100063 : Blo 2099435 2100063 := bstep (se 1 (by rfl) ⟨1575047, by rfl⟩ : syracuseStep 2100063 = 3150095) B3150095
theorem B3150101 : Blo 2099435 3150101 := bbase (se 6 (by rfl) ⟨73830, by rfl⟩ : syracuseStep 3150101 = 147661) (by norm_num)
theorem B2100067 : Blo 2099435 2100067 := bstep (se 1 (by rfl) ⟨1575050, by rfl⟩ : syracuseStep 2100067 = 3150101) B3150101
theorem B7282469 : Blo 2099435 7282469 := bbase (se 4 (by rfl) ⟨682731, by rfl⟩ : syracuseStep 7282469 = 1365463) (by norm_num)
theorem B4854979 : Blo 2099435 4854979 := bstep (se 1 (by rfl) ⟨3641234, by rfl⟩ : syracuseStep 4854979 = 7282469) B7282469
theorem B6473305 : Blo 2099435 6473305 := bstep (se 2 (by rfl) ⟨2427489, by rfl⟩ : syracuseStep 6473305 = 4854979) B4854979
theorem B8631073 : Blo 2099435 8631073 := bstep (se 2 (by rfl) ⟨3236652, by rfl⟩ : syracuseStep 8631073 = 6473305) B6473305
theorem B11508097 : Blo 2099435 11508097 := bstep (se 2 (by rfl) ⟨4315536, by rfl⟩ : syracuseStep 11508097 = 8631073) B8631073
theorem B15344129 : Blo 2099435 15344129 := bstep (se 2 (by rfl) ⟨5754048, by rfl⟩ : syracuseStep 15344129 = 11508097) B11508097
theorem B10229419 : Blo 2099435 10229419 := bstep (se 1 (by rfl) ⟨7672064, by rfl⟩ : syracuseStep 10229419 = 15344129) B15344129
theorem B54556901 : Blo 2099435 54556901 := bstep (se 4 (by rfl) ⟨5114709, by rfl⟩ : syracuseStep 54556901 = 10229419) B10229419
theorem B36371267 : Blo 2099435 36371267 := bstep (se 1 (by rfl) ⟨27278450, by rfl⟩ : syracuseStep 36371267 = 54556901) B54556901
theorem B24247511 : Blo 2099435 24247511 := bstep (se 1 (by rfl) ⟨18185633, by rfl⟩ : syracuseStep 24247511 = 36371267) B36371267
theorem B16165007 : Blo 2099435 16165007 := bstep (se 1 (by rfl) ⟨12123755, by rfl⟩ : syracuseStep 16165007 = 24247511) B24247511
theorem B10776671 : Blo 2099435 10776671 := bstep (se 1 (by rfl) ⟨8082503, by rfl⟩ : syracuseStep 10776671 = 16165007) B16165007
theorem B7184447 : Blo 2099435 7184447 := bstep (se 1 (by rfl) ⟨5388335, by rfl⟩ : syracuseStep 7184447 = 10776671) B10776671
theorem B4789631 : Blo 2099435 4789631 := bstep (se 1 (by rfl) ⟨3592223, by rfl⟩ : syracuseStep 4789631 = 7184447) B7184447
theorem B3193087 : Blo 2099435 3193087 := bstep (se 1 (by rfl) ⟨2394815, by rfl⟩ : syracuseStep 3193087 = 4789631) B4789631
theorem B4257449 : Blo 2099435 4257449 := bstep (se 2 (by rfl) ⟨1596543, by rfl⟩ : syracuseStep 4257449 = 3193087) B3193087
theorem B2838299 : Blo 2099435 2838299 := bstep (se 1 (by rfl) ⟨2128724, by rfl⟩ : syracuseStep 2838299 = 4257449) B4257449
theorem B7568797 : Blo 2099435 7568797 := bstep (se 3 (by rfl) ⟨1419149, by rfl⟩ : syracuseStep 7568797 = 2838299) B2838299
theorem B10091729 : Blo 2099435 10091729 := bstep (se 2 (by rfl) ⟨3784398, by rfl⟩ : syracuseStep 10091729 = 7568797) B7568797
theorem B26911277 : Blo 2099435 26911277 := bstep (se 3 (by rfl) ⟨5045864, by rfl⟩ : syracuseStep 26911277 = 10091729) B10091729
theorem B17940851 : Blo 2099435 17940851 := bstep (se 1 (by rfl) ⟨13455638, by rfl⟩ : syracuseStep 17940851 = 26911277) B26911277
theorem B11960567 : Blo 2099435 11960567 := bstep (se 1 (by rfl) ⟨8970425, by rfl⟩ : syracuseStep 11960567 = 17940851) B17940851
theorem B7973711 : Blo 2099435 7973711 := bstep (se 1 (by rfl) ⟨5980283, by rfl⟩ : syracuseStep 7973711 = 11960567) B11960567
theorem B5315807 : Blo 2099435 5315807 := bstep (se 1 (by rfl) ⟨3986855, by rfl⟩ : syracuseStep 5315807 = 7973711) B7973711
theorem B3543871 : Blo 2099435 3543871 := bstep (se 1 (by rfl) ⟨2657903, by rfl⟩ : syracuseStep 3543871 = 5315807) B5315807
theorem B4725161 : Blo 2099435 4725161 := bstep (se 2 (by rfl) ⟨1771935, by rfl⟩ : syracuseStep 4725161 = 3543871) B3543871
theorem B3150107 : Blo 2099435 3150107 := bstep (se 1 (by rfl) ⟨2362580, by rfl⟩ : syracuseStep 3150107 = 4725161) B4725161
theorem B2100071 : Blo 2099435 2100071 := bstep (se 1 (by rfl) ⟨1575053, by rfl⟩ : syracuseStep 2100071 = 3150107) B3150107
theorem B2362585 : Blo 2099435 2362585 := bbase (se 2 (by rfl) ⟨885969, by rfl⟩ : syracuseStep 2362585 = 1771939) (by norm_num)
theorem B3150113 : Blo 2099435 3150113 := bstep (se 2 (by rfl) ⟨1181292, by rfl⟩ : syracuseStep 3150113 = 2362585) B2362585
theorem B2100075 : Blo 2099435 2100075 := bstep (se 1 (by rfl) ⟨1575056, by rfl⟩ : syracuseStep 2100075 = 3150113) B3150113
theorem B5045885 : Blo 2099435 5045885 := bbase (se 3 (by rfl) ⟨946103, by rfl⟩ : syracuseStep 5045885 = 1892207) (by norm_num)
theorem B3363923 : Blo 2099435 3363923 := bstep (se 1 (by rfl) ⟨2522942, by rfl⟩ : syracuseStep 3363923 = 5045885) B5045885
theorem B2242615 : Blo 2099435 2242615 := bstep (se 1 (by rfl) ⟨1681961, by rfl⟩ : syracuseStep 2242615 = 3363923) B3363923
theorem B2990153 : Blo 2099435 2990153 := bstep (se 2 (by rfl) ⟨1121307, by rfl⟩ : syracuseStep 2990153 = 2242615) B2242615
theorem B7973741 : Blo 2099435 7973741 := bstep (se 3 (by rfl) ⟨1495076, by rfl⟩ : syracuseStep 7973741 = 2990153) B2990153
theorem B5315827 : Blo 2099435 5315827 := bstep (se 1 (by rfl) ⟨3986870, by rfl⟩ : syracuseStep 5315827 = 7973741) B7973741
theorem B7087769 : Blo 2099435 7087769 := bstep (se 2 (by rfl) ⟨2657913, by rfl⟩ : syracuseStep 7087769 = 5315827) B5315827
theorem B4725179 : Blo 2099435 4725179 := bstep (se 1 (by rfl) ⟨3543884, by rfl⟩ : syracuseStep 4725179 = 7087769) B7087769
theorem B3150119 : Blo 2099435 3150119 := bstep (se 1 (by rfl) ⟨2362589, by rfl⟩ : syracuseStep 3150119 = 4725179) B4725179
theorem B2100079 : Blo 2099435 2100079 := bstep (se 1 (by rfl) ⟨1575059, by rfl⟩ : syracuseStep 2100079 = 3150119) B3150119
theorem B3150125 : Blo 2099435 3150125 := bbase (se 3 (by rfl) ⟨590648, by rfl⟩ : syracuseStep 3150125 = 1181297) (by norm_num)
theorem B2100083 : Blo 2099435 2100083 := bstep (se 1 (by rfl) ⟨1575062, by rfl⟩ : syracuseStep 2100083 = 3150125) B3150125
theorem B4725197 : Blo 2099435 4725197 := bbase (se 3 (by rfl) ⟨885974, by rfl⟩ : syracuseStep 4725197 = 1771949) (by norm_num)
theorem B3150131 : Blo 2099435 3150131 := bstep (se 1 (by rfl) ⟨2362598, by rfl⟩ : syracuseStep 3150131 = 4725197) B4725197
theorem B2100087 : Blo 2099435 2100087 := bstep (se 1 (by rfl) ⟨1575065, by rfl⟩ : syracuseStep 2100087 = 3150131) B3150131
theorem B2657929 : Blo 2099435 2657929 := bbase (se 2 (by rfl) ⟨996723, by rfl⟩ : syracuseStep 2657929 = 1993447) (by norm_num)
theorem B3543905 : Blo 2099435 3543905 := bstep (se 2 (by rfl) ⟨1328964, by rfl⟩ : syracuseStep 3543905 = 2657929) B2657929
theorem B2362603 : Blo 2099435 2362603 := bstep (se 1 (by rfl) ⟨1771952, by rfl⟩ : syracuseStep 2362603 = 3543905) B3543905
theorem B3150137 : Blo 2099435 3150137 := bstep (se 2 (by rfl) ⟨1181301, by rfl⟩ : syracuseStep 3150137 = 2362603) B2362603
theorem B2100091 : Blo 2099435 2100091 := bstep (se 1 (by rfl) ⟨1575068, by rfl⟩ : syracuseStep 2100091 = 3150137) B3150137
theorem B6386245 : Blo 2099435 6386245 := bbase (se 4 (by rfl) ⟨598710, by rfl⟩ : syracuseStep 6386245 = 1197421) (by norm_num)
theorem B34059973 : Blo 2099435 34059973 := bstep (se 4 (by rfl) ⟨3193122, by rfl⟩ : syracuseStep 34059973 = 6386245) B6386245
theorem B45413297 : Blo 2099435 45413297 := bstep (se 2 (by rfl) ⟨17029986, by rfl⟩ : syracuseStep 45413297 = 34059973) B34059973
theorem B30275531 : Blo 2099435 30275531 := bstep (se 1 (by rfl) ⟨22706648, by rfl⟩ : syracuseStep 30275531 = 45413297) B45413297
theorem B20183687 : Blo 2099435 20183687 := bstep (se 1 (by rfl) ⟨15137765, by rfl⟩ : syracuseStep 20183687 = 30275531) B30275531
theorem B13455791 : Blo 2099435 13455791 := bstep (se 1 (by rfl) ⟨10091843, by rfl⟩ : syracuseStep 13455791 = 20183687) B20183687
theorem B8970527 : Blo 2099435 8970527 := bstep (se 1 (by rfl) ⟨6727895, by rfl⟩ : syracuseStep 8970527 = 13455791) B13455791
theorem B23921405 : Blo 2099435 23921405 := bstep (se 3 (by rfl) ⟨4485263, by rfl⟩ : syracuseStep 23921405 = 8970527) B8970527
theorem B15947603 : Blo 2099435 15947603 := bstep (se 1 (by rfl) ⟨11960702, by rfl⟩ : syracuseStep 15947603 = 23921405) B23921405
theorem B10631735 : Blo 2099435 10631735 := bstep (se 1 (by rfl) ⟨7973801, by rfl⟩ : syracuseStep 10631735 = 15947603) B15947603
theorem B7087823 : Blo 2099435 7087823 := bstep (se 1 (by rfl) ⟨5315867, by rfl⟩ : syracuseStep 7087823 = 10631735) B10631735
theorem B4725215 : Blo 2099435 4725215 := bstep (se 1 (by rfl) ⟨3543911, by rfl⟩ : syracuseStep 4725215 = 7087823) B7087823
theorem B3150143 : Blo 2099435 3150143 := bstep (se 1 (by rfl) ⟨2362607, by rfl⟩ : syracuseStep 3150143 = 4725215) B4725215
theorem B2100095 : Blo 2099435 2100095 := bstep (se 1 (by rfl) ⟨1575071, by rfl⟩ : syracuseStep 2100095 = 3150143) B3150143
theorem B3150149 : Blo 2099435 3150149 := bbase (se 4 (by rfl) ⟨295326, by rfl⟩ : syracuseStep 3150149 = 590653) (by norm_num)
theorem B2100099 : Blo 2099435 2100099 := bstep (se 1 (by rfl) ⟨1575074, by rfl⟩ : syracuseStep 2100099 = 3150149) B3150149
theorem B3543925 : Blo 2099435 3543925 := bbase (se 5 (by rfl) ⟨166121, by rfl⟩ : syracuseStep 3543925 = 332243) (by norm_num)
theorem B4725233 : Blo 2099435 4725233 := bstep (se 2 (by rfl) ⟨1771962, by rfl⟩ : syracuseStep 4725233 = 3543925) B3543925
theorem B3150155 : Blo 2099435 3150155 := bstep (se 1 (by rfl) ⟨2362616, by rfl⟩ : syracuseStep 3150155 = 4725233) B4725233
theorem B2100103 : Blo 2099435 2100103 := bstep (se 1 (by rfl) ⟨1575077, by rfl⟩ : syracuseStep 2100103 = 3150155) B3150155
theorem B2362621 : Blo 2099435 2362621 := bbase (se 3 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 2362621 = 885983) (by norm_num)
theorem B3150161 : Blo 2099435 3150161 := bstep (se 2 (by rfl) ⟨1181310, by rfl⟩ : syracuseStep 3150161 = 2362621) B2362621
theorem B2100107 : Blo 2099435 2100107 := bstep (se 1 (by rfl) ⟨1575080, by rfl⟩ : syracuseStep 2100107 = 3150161) B3150161
theorem B7087877 : Blo 2099435 7087877 := bbase (se 4 (by rfl) ⟨664488, by rfl⟩ : syracuseStep 7087877 = 1328977) (by norm_num)
theorem B4725251 : Blo 2099435 4725251 := bstep (se 1 (by rfl) ⟨3543938, by rfl⟩ : syracuseStep 4725251 = 7087877) B7087877
theorem B3150167 : Blo 2099435 3150167 := bstep (se 1 (by rfl) ⟨2362625, by rfl⟩ : syracuseStep 3150167 = 4725251) B4725251
theorem B2100111 : Blo 2099435 2100111 := bstep (se 1 (by rfl) ⟨1575083, by rfl⟩ : syracuseStep 2100111 = 3150167) B3150167
theorem B3150173 : Blo 2099435 3150173 := bbase (se 3 (by rfl) ⟨590657, by rfl⟩ : syracuseStep 3150173 = 1181315) (by norm_num)
theorem B2100115 : Blo 2099435 2100115 := bstep (se 1 (by rfl) ⟨1575086, by rfl⟩ : syracuseStep 2100115 = 3150173) B3150173
theorem B4725269 : Blo 2099435 4725269 := bbase (se 6 (by rfl) ⟨110748, by rfl⟩ : syracuseStep 4725269 = 221497) (by norm_num)
theorem B3150179 : Blo 2099435 3150179 := bstep (se 1 (by rfl) ⟨2362634, by rfl⟩ : syracuseStep 3150179 = 4725269) B4725269
theorem B2100119 : Blo 2099435 2100119 := bstep (se 1 (by rfl) ⟨1575089, by rfl⟩ : syracuseStep 2100119 = 3150179) B3150179
theorem B7973909 : Blo 2099435 7973909 := bbase (se 6 (by rfl) ⟨186888, by rfl⟩ : syracuseStep 7973909 = 373777) (by norm_num)
theorem B5315939 : Blo 2099435 5315939 := bstep (se 1 (by rfl) ⟨3986954, by rfl⟩ : syracuseStep 5315939 = 7973909) B7973909
theorem B3543959 : Blo 2099435 3543959 := bstep (se 1 (by rfl) ⟨2657969, by rfl⟩ : syracuseStep 3543959 = 5315939) B5315939
theorem B2362639 : Blo 2099435 2362639 := bstep (se 1 (by rfl) ⟨1771979, by rfl⟩ : syracuseStep 2362639 = 3543959) B3543959
theorem B3150185 : Blo 2099435 3150185 := bstep (se 2 (by rfl) ⟨1181319, by rfl⟩ : syracuseStep 3150185 = 2362639) B2362639
theorem B2100123 : Blo 2099435 2100123 := bstep (se 1 (by rfl) ⟨1575092, by rfl⟩ : syracuseStep 2100123 = 3150185) B3150185
theorem B11960885 : Blo 2099435 11960885 := bbase (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) (by norm_num)
theorem B7973923 : Blo 2099435 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B10631897 : Blo 2099435 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B7087931 : Blo 2099435 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B4725287 : Blo 2099435 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B3150191 : Blo 2099435 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B2100127 : Blo 2099435 2100127 := bstep (se 1 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 2100127 = 3150191) B3150191
theorem B3150197 : Blo 2099435 3150197 := bbase (se 5 (by rfl) ⟨147665, by rfl⟩ : syracuseStep 3150197 = 295331) (by norm_num)
theorem B2100131 : Blo 2099435 2100131 := bstep (se 1 (by rfl) ⟨1575098, by rfl⟩ : syracuseStep 2100131 = 3150197) B3150197
theorem B3364013 : Blo 2099435 3364013 := bbase (se 3 (by rfl) ⟨630752, by rfl⟩ : syracuseStep 3364013 = 1261505) (by norm_num)
theorem B2242675 : Blo 2099435 2242675 := bstep (se 1 (by rfl) ⟨1682006, by rfl⟩ : syracuseStep 2242675 = 3364013) B3364013
theorem B2990233 : Blo 2099435 2990233 := bstep (se 2 (by rfl) ⟨1121337, by rfl⟩ : syracuseStep 2990233 = 2242675) B2242675
theorem B3986977 : Blo 2099435 3986977 := bstep (se 2 (by rfl) ⟨1495116, by rfl⟩ : syracuseStep 3986977 = 2990233) B2990233
theorem B5315969 : Blo 2099435 5315969 := bstep (se 2 (by rfl) ⟨1993488, by rfl⟩ : syracuseStep 5315969 = 3986977) B3986977
theorem B3543979 : Blo 2099435 3543979 := bstep (se 1 (by rfl) ⟨2657984, by rfl⟩ : syracuseStep 3543979 = 5315969) B5315969
theorem B4725305 : Blo 2099435 4725305 := bstep (se 2 (by rfl) ⟨1771989, by rfl⟩ : syracuseStep 4725305 = 3543979) B3543979
theorem B3150203 : Blo 2099435 3150203 := bstep (se 1 (by rfl) ⟨2362652, by rfl⟩ : syracuseStep 3150203 = 4725305) B4725305
theorem B2100135 : Blo 2099435 2100135 := bstep (se 1 (by rfl) ⟨1575101, by rfl⟩ : syracuseStep 2100135 = 3150203) B3150203
theorem B2362657 : Blo 2099435 2362657 := bbase (se 2 (by rfl) ⟨885996, by rfl⟩ : syracuseStep 2362657 = 1771993) (by norm_num)
theorem B3150209 : Blo 2099435 3150209 := bstep (se 2 (by rfl) ⟨1181328, by rfl⟩ : syracuseStep 3150209 = 2362657) B2362657
theorem B2100139 : Blo 2099435 2100139 := bstep (se 1 (by rfl) ⟨1575104, by rfl⟩ : syracuseStep 2100139 = 3150209) B3150209
theorem B5315989 : Blo 2099435 5315989 := bbase (se 6 (by rfl) ⟨124593, by rfl⟩ : syracuseStep 5315989 = 249187) (by norm_num)
theorem B7087985 : Blo 2099435 7087985 := bstep (se 2 (by rfl) ⟨2657994, by rfl⟩ : syracuseStep 7087985 = 5315989) B5315989
theorem B4725323 : Blo 2099435 4725323 := bstep (se 1 (by rfl) ⟨3543992, by rfl⟩ : syracuseStep 4725323 = 7087985) B7087985
theorem B3150215 : Blo 2099435 3150215 := bstep (se 1 (by rfl) ⟨2362661, by rfl⟩ : syracuseStep 3150215 = 4725323) B4725323
theorem B2100143 : Blo 2099435 2100143 := bstep (se 1 (by rfl) ⟨1575107, by rfl⟩ : syracuseStep 2100143 = 3150215) B3150215
theorem B3150221 : Blo 2099435 3150221 := bbase (se 3 (by rfl) ⟨590666, by rfl⟩ : syracuseStep 3150221 = 1181333) (by norm_num)
theorem B2100147 : Blo 2099435 2100147 := bstep (se 1 (by rfl) ⟨1575110, by rfl⟩ : syracuseStep 2100147 = 3150221) B3150221
theorem B4725341 : Blo 2099435 4725341 := bbase (se 3 (by rfl) ⟨886001, by rfl⟩ : syracuseStep 4725341 = 1772003) (by norm_num)
theorem B3150227 : Blo 2099435 3150227 := bstep (se 1 (by rfl) ⟨2362670, by rfl⟩ : syracuseStep 3150227 = 4725341) B4725341
theorem B2100151 : Blo 2099435 2100151 := bstep (se 1 (by rfl) ⟨1575113, by rfl⟩ : syracuseStep 2100151 = 3150227) B3150227
theorem B3544013 : Blo 2099435 3544013 := bbase (se 3 (by rfl) ⟨664502, by rfl⟩ : syracuseStep 3544013 = 1329005) (by norm_num)
theorem B2362675 : Blo 2099435 2362675 := bstep (se 1 (by rfl) ⟨1772006, by rfl⟩ : syracuseStep 2362675 = 3544013) B3544013
theorem B3150233 : Blo 2099435 3150233 := bstep (se 2 (by rfl) ⟨1181337, by rfl⟩ : syracuseStep 3150233 = 2362675) B2362675
theorem B2100155 : Blo 2099435 2100155 := bstep (se 1 (by rfl) ⟨1575116, by rfl⟩ : syracuseStep 2100155 = 3150233) B3150233
theorem B8515253 : Blo 2099435 8515253 := bbase (se 5 (by rfl) ⟨399152, by rfl⟩ : syracuseStep 8515253 = 798305) (by norm_num)
theorem B22707341 : Blo 2099435 22707341 := bstep (se 3 (by rfl) ⟨4257626, by rfl⟩ : syracuseStep 22707341 = 8515253) B8515253
theorem B15138227 : Blo 2099435 15138227 := bstep (se 1 (by rfl) ⟨11353670, by rfl⟩ : syracuseStep 15138227 = 22707341) B22707341
theorem B10092151 : Blo 2099435 10092151 := bstep (se 1 (by rfl) ⟨7569113, by rfl⟩ : syracuseStep 10092151 = 15138227) B15138227
theorem B13456201 : Blo 2099435 13456201 := bstep (se 2 (by rfl) ⟨5046075, by rfl⟩ : syracuseStep 13456201 = 10092151) B10092151
theorem B17941601 : Blo 2099435 17941601 := bstep (se 2 (by rfl) ⟨6728100, by rfl⟩ : syracuseStep 17941601 = 13456201) B13456201
theorem B11961067 : Blo 2099435 11961067 := bstep (se 1 (by rfl) ⟨8970800, by rfl⟩ : syracuseStep 11961067 = 17941601) B17941601
theorem B15948089 : Blo 2099435 15948089 := bstep (se 2 (by rfl) ⟨5980533, by rfl⟩ : syracuseStep 15948089 = 11961067) B11961067
theorem B10632059 : Blo 2099435 10632059 := bstep (se 1 (by rfl) ⟨7974044, by rfl⟩ : syracuseStep 10632059 = 15948089) B15948089
theorem B7088039 : Blo 2099435 7088039 := bstep (se 1 (by rfl) ⟨5316029, by rfl⟩ : syracuseStep 7088039 = 10632059) B10632059
theorem B4725359 : Blo 2099435 4725359 := bstep (se 1 (by rfl) ⟨3544019, by rfl⟩ : syracuseStep 4725359 = 7088039) B7088039
theorem B3150239 : Blo 2099435 3150239 := bstep (se 1 (by rfl) ⟨2362679, by rfl⟩ : syracuseStep 3150239 = 4725359) B4725359
theorem B2100159 : Blo 2099435 2100159 := bstep (se 1 (by rfl) ⟨1575119, by rfl⟩ : syracuseStep 2100159 = 3150239) B3150239
theorem B3150245 : Blo 2099435 3150245 := bbase (se 4 (by rfl) ⟨295335, by rfl⟩ : syracuseStep 3150245 = 590671) (by norm_num)
theorem B2100163 : Blo 2099435 2100163 := bstep (se 1 (by rfl) ⟨1575122, by rfl⟩ : syracuseStep 2100163 = 3150245) B3150245
theorem B2658025 : Blo 2099435 2658025 := bbase (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) (by norm_num)
theorem B3544033 : Blo 2099435 3544033 := bstep (se 2 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 3544033 = 2658025) B2658025
theorem B4725377 : Blo 2099435 4725377 := bstep (se 2 (by rfl) ⟨1772016, by rfl⟩ : syracuseStep 4725377 = 3544033) B3544033
theorem B3150251 : Blo 2099435 3150251 := bstep (se 1 (by rfl) ⟨2362688, by rfl⟩ : syracuseStep 3150251 = 4725377) B4725377
theorem B2100167 : Blo 2099435 2100167 := bstep (se 1 (by rfl) ⟨1575125, by rfl⟩ : syracuseStep 2100167 = 3150251) B3150251
theorem B2362693 : Blo 2099435 2362693 := bbase (se 4 (by rfl) ⟨221502, by rfl⟩ : syracuseStep 2362693 = 443005) (by norm_num)
theorem B3150257 : Blo 2099435 3150257 := bstep (se 2 (by rfl) ⟨1181346, by rfl⟩ : syracuseStep 3150257 = 2362693) B2362693
theorem B2100171 : Blo 2099435 2100171 := bstep (se 1 (by rfl) ⟨1575128, by rfl⟩ : syracuseStep 2100171 = 3150257) B3150257
theorem B3987053 : Blo 2099435 3987053 := bbase (se 3 (by rfl) ⟨747572, by rfl⟩ : syracuseStep 3987053 = 1495145) (by norm_num)
theorem B2658035 : Blo 2099435 2658035 := bstep (se 1 (by rfl) ⟨1993526, by rfl⟩ : syracuseStep 2658035 = 3987053) B3987053
theorem B7088093 : Blo 2099435 7088093 := bstep (se 3 (by rfl) ⟨1329017, by rfl⟩ : syracuseStep 7088093 = 2658035) B2658035
theorem B4725395 : Blo 2099435 4725395 := bstep (se 1 (by rfl) ⟨3544046, by rfl⟩ : syracuseStep 4725395 = 7088093) B7088093
theorem B3150263 : Blo 2099435 3150263 := bstep (se 1 (by rfl) ⟨2362697, by rfl⟩ : syracuseStep 3150263 = 4725395) B4725395
theorem B2100175 : Blo 2099435 2100175 := bstep (se 1 (by rfl) ⟨1575131, by rfl⟩ : syracuseStep 2100175 = 3150263) B3150263
theorem B3150269 : Blo 2099435 3150269 := bbase (se 3 (by rfl) ⟨590675, by rfl⟩ : syracuseStep 3150269 = 1181351) (by norm_num)
theorem B2100179 : Blo 2099435 2100179 := bstep (se 1 (by rfl) ⟨1575134, by rfl⟩ : syracuseStep 2100179 = 3150269) B3150269
theorem B4725413 : Blo 2099435 4725413 := bbase (se 4 (by rfl) ⟨443007, by rfl⟩ : syracuseStep 4725413 = 886015) (by norm_num)
theorem B3150275 : Blo 2099435 3150275 := bstep (se 1 (by rfl) ⟨2362706, by rfl⟩ : syracuseStep 3150275 = 4725413) B4725413
theorem B2100183 : Blo 2099435 2100183 := bstep (se 1 (by rfl) ⟨1575137, by rfl⟩ : syracuseStep 2100183 = 3150275) B3150275
theorem B5316101 : Blo 2099435 5316101 := bbase (se 4 (by rfl) ⟨498384, by rfl⟩ : syracuseStep 5316101 = 996769) (by norm_num)
theorem B3544067 : Blo 2099435 3544067 := bstep (se 1 (by rfl) ⟨2658050, by rfl⟩ : syracuseStep 3544067 = 5316101) B5316101
theorem B2362711 : Blo 2099435 2362711 := bstep (se 1 (by rfl) ⟨1772033, by rfl⟩ : syracuseStep 2362711 = 3544067) B3544067
theorem B3150281 : Blo 2099435 3150281 := bstep (se 2 (by rfl) ⟨1181355, by rfl⟩ : syracuseStep 3150281 = 2362711) B2362711
theorem B2100187 : Blo 2099435 2100187 := bstep (se 1 (by rfl) ⟨1575140, by rfl⟩ : syracuseStep 2100187 = 3150281) B3150281
theorem B4485469 : Blo 2099435 4485469 := bbase (se 3 (by rfl) ⟨841025, by rfl⟩ : syracuseStep 4485469 = 1682051) (by norm_num)
theorem B5980625 : Blo 2099435 5980625 := bstep (se 2 (by rfl) ⟨2242734, by rfl⟩ : syracuseStep 5980625 = 4485469) B4485469
theorem B3987083 : Blo 2099435 3987083 := bstep (se 1 (by rfl) ⟨2990312, by rfl⟩ : syracuseStep 3987083 = 5980625) B5980625
theorem B10632221 : Blo 2099435 10632221 := bstep (se 3 (by rfl) ⟨1993541, by rfl⟩ : syracuseStep 10632221 = 3987083) B3987083
theorem B7088147 : Blo 2099435 7088147 := bstep (se 1 (by rfl) ⟨5316110, by rfl⟩ : syracuseStep 7088147 = 10632221) B10632221
theorem B4725431 : Blo 2099435 4725431 := bstep (se 1 (by rfl) ⟨3544073, by rfl⟩ : syracuseStep 4725431 = 7088147) B7088147
theorem B3150287 : Blo 2099435 3150287 := bstep (se 1 (by rfl) ⟨2362715, by rfl⟩ : syracuseStep 3150287 = 4725431) B4725431
theorem B2100191 : Blo 2099435 2100191 := bstep (se 1 (by rfl) ⟨1575143, by rfl⟩ : syracuseStep 2100191 = 3150287) B3150287
theorem B3150293 : Blo 2099435 3150293 := bbase (se 7 (by rfl) ⟨36917, by rfl⟩ : syracuseStep 3150293 = 73835) (by norm_num)
theorem B2100195 : Blo 2099435 2100195 := bstep (se 1 (by rfl) ⟨1575146, by rfl⟩ : syracuseStep 2100195 = 3150293) B3150293
theorem B7974197 : Blo 2099435 7974197 := bbase (se 5 (by rfl) ⟨373790, by rfl⟩ : syracuseStep 7974197 = 747581) (by norm_num)
theorem B5316131 : Blo 2099435 5316131 := bstep (se 1 (by rfl) ⟨3987098, by rfl⟩ : syracuseStep 5316131 = 7974197) B7974197
theorem B3544087 : Blo 2099435 3544087 := bstep (se 1 (by rfl) ⟨2658065, by rfl⟩ : syracuseStep 3544087 = 5316131) B5316131
theorem B4725449 : Blo 2099435 4725449 := bstep (se 2 (by rfl) ⟨1772043, by rfl⟩ : syracuseStep 4725449 = 3544087) B3544087
theorem B3150299 : Blo 2099435 3150299 := bstep (se 1 (by rfl) ⟨2362724, by rfl⟩ : syracuseStep 3150299 = 4725449) B4725449
theorem B2100199 : Blo 2099435 2100199 := bstep (se 1 (by rfl) ⟨1575149, by rfl⟩ : syracuseStep 2100199 = 3150299) B3150299
theorem B2362729 : Blo 2099435 2362729 := bbase (se 2 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 2362729 = 1772047) (by norm_num)
theorem B3150305 : Blo 2099435 3150305 := bstep (se 2 (by rfl) ⟨1181364, by rfl⟩ : syracuseStep 3150305 = 2362729) B2362729
theorem B2100203 : Blo 2099435 2100203 := bstep (se 1 (by rfl) ⟨1575152, by rfl⟩ : syracuseStep 2100203 = 3150305) B3150305
theorem B51092693 : Blo 2099435 51092693 := bbase (se 7 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 51092693 = 1197485) (by norm_num)
theorem B34061795 : Blo 2099435 34061795 := bstep (se 1 (by rfl) ⟨25546346, by rfl⟩ : syracuseStep 34061795 = 51092693) B51092693
theorem B22707863 : Blo 2099435 22707863 := bstep (se 1 (by rfl) ⟨17030897, by rfl⟩ : syracuseStep 22707863 = 34061795) B34061795
theorem B15138575 : Blo 2099435 15138575 := bstep (se 1 (by rfl) ⟨11353931, by rfl⟩ : syracuseStep 15138575 = 22707863) B22707863
theorem B10092383 : Blo 2099435 10092383 := bstep (se 1 (by rfl) ⟨7569287, by rfl⟩ : syracuseStep 10092383 = 15138575) B15138575
theorem B6728255 : Blo 2099435 6728255 := bstep (se 1 (by rfl) ⟨5046191, by rfl⟩ : syracuseStep 6728255 = 10092383) B10092383
theorem B4485503 : Blo 2099435 4485503 := bstep (se 1 (by rfl) ⟨3364127, by rfl⟩ : syracuseStep 4485503 = 6728255) B6728255
theorem B11961341 : Blo 2099435 11961341 := bstep (se 3 (by rfl) ⟨2242751, by rfl⟩ : syracuseStep 11961341 = 4485503) B4485503
theorem B7974227 : Blo 2099435 7974227 := bstep (se 1 (by rfl) ⟨5980670, by rfl⟩ : syracuseStep 7974227 = 11961341) B11961341
theorem B5316151 : Blo 2099435 5316151 := bstep (se 1 (by rfl) ⟨3987113, by rfl⟩ : syracuseStep 5316151 = 7974227) B7974227
theorem B7088201 : Blo 2099435 7088201 := bstep (se 2 (by rfl) ⟨2658075, by rfl⟩ : syracuseStep 7088201 = 5316151) B5316151
theorem B4725467 : Blo 2099435 4725467 := bstep (se 1 (by rfl) ⟨3544100, by rfl⟩ : syracuseStep 4725467 = 7088201) B7088201
theorem B3150311 : Blo 2099435 3150311 := bstep (se 1 (by rfl) ⟨2362733, by rfl⟩ : syracuseStep 3150311 = 4725467) B4725467
theorem B2100207 : Blo 2099435 2100207 := bstep (se 1 (by rfl) ⟨1575155, by rfl⟩ : syracuseStep 2100207 = 3150311) B3150311
theorem B3150317 : Blo 2099435 3150317 := bbase (se 3 (by rfl) ⟨590684, by rfl⟩ : syracuseStep 3150317 = 1181369) (by norm_num)
theorem B2100211 : Blo 2099435 2100211 := bstep (se 1 (by rfl) ⟨1575158, by rfl⟩ : syracuseStep 2100211 = 3150317) B3150317
theorem B4725485 : Blo 2099435 4725485 := bbase (se 3 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 4725485 = 1772057) (by norm_num)
theorem B3150323 : Blo 2099435 3150323 := bstep (se 1 (by rfl) ⟨2362742, by rfl⟩ : syracuseStep 3150323 = 4725485) B4725485
theorem B2100215 : Blo 2099435 2100215 := bstep (se 1 (by rfl) ⟨1575161, by rfl⟩ : syracuseStep 2100215 = 3150323) B3150323
theorem B2242765 : Blo 2099435 2242765 := bbase (se 3 (by rfl) ⟨420518, by rfl⟩ : syracuseStep 2242765 = 841037) (by norm_num)
theorem B2990353 : Blo 2099435 2990353 := bstep (se 2 (by rfl) ⟨1121382, by rfl⟩ : syracuseStep 2990353 = 2242765) B2242765
theorem B3987137 : Blo 2099435 3987137 := bstep (se 2 (by rfl) ⟨1495176, by rfl⟩ : syracuseStep 3987137 = 2990353) B2990353
theorem B2658091 : Blo 2099435 2658091 := bstep (se 1 (by rfl) ⟨1993568, by rfl⟩ : syracuseStep 2658091 = 3987137) B3987137
theorem B3544121 : Blo 2099435 3544121 := bstep (se 2 (by rfl) ⟨1329045, by rfl⟩ : syracuseStep 3544121 = 2658091) B2658091
theorem B2362747 : Blo 2099435 2362747 := bstep (se 1 (by rfl) ⟨1772060, by rfl⟩ : syracuseStep 2362747 = 3544121) B3544121
theorem B3150329 : Blo 2099435 3150329 := bstep (se 2 (by rfl) ⟨1181373, by rfl⟩ : syracuseStep 3150329 = 2362747) B2362747
theorem B2100219 : Blo 2099435 2100219 := bstep (se 1 (by rfl) ⟨1575164, by rfl⟩ : syracuseStep 2100219 = 3150329) B3150329
theorem B5115077 : Blo 2099435 5115077 := bbase (se 4 (by rfl) ⟨479538, by rfl⟩ : syracuseStep 5115077 = 959077) (by norm_num)
theorem B3410051 : Blo 2099435 3410051 := bstep (se 1 (by rfl) ⟨2557538, by rfl⟩ : syracuseStep 3410051 = 5115077) B5115077
theorem B36373877 : Blo 2099435 36373877 := bstep (se 5 (by rfl) ⟨1705025, by rfl⟩ : syracuseStep 36373877 = 3410051) B3410051
theorem B24249251 : Blo 2099435 24249251 := bstep (se 1 (by rfl) ⟨18186938, by rfl⟩ : syracuseStep 24249251 = 36373877) B36373877
theorem B64664669 : Blo 2099435 64664669 := bstep (se 3 (by rfl) ⟨12124625, by rfl⟩ : syracuseStep 64664669 = 24249251) B24249251
theorem B172439117 : Blo 2099435 172439117 := bstep (se 3 (by rfl) ⟨32332334, by rfl⟩ : syracuseStep 172439117 = 64664669) B64664669
theorem B114959411 : Blo 2099435 114959411 := bstep (se 1 (by rfl) ⟨86219558, by rfl⟩ : syracuseStep 114959411 = 172439117) B172439117
theorem B76639607 : Blo 2099435 76639607 := bstep (se 1 (by rfl) ⟨57479705, by rfl⟩ : syracuseStep 76639607 = 114959411) B114959411
theorem B51093071 : Blo 2099435 51093071 := bstep (se 1 (by rfl) ⟨38319803, by rfl⟩ : syracuseStep 51093071 = 76639607) B76639607
theorem B34062047 : Blo 2099435 34062047 := bstep (se 1 (by rfl) ⟨25546535, by rfl⟩ : syracuseStep 34062047 = 51093071) B51093071
theorem B22708031 : Blo 2099435 22708031 := bstep (se 1 (by rfl) ⟨17031023, by rfl⟩ : syracuseStep 22708031 = 34062047) B34062047
theorem B60554749 : Blo 2099435 60554749 := bstep (se 3 (by rfl) ⟨11354015, by rfl⟩ : syracuseStep 60554749 = 22708031) B22708031
theorem B80739665 : Blo 2099435 80739665 := bstep (se 2 (by rfl) ⟨30277374, by rfl⟩ : syracuseStep 80739665 = 60554749) B60554749
theorem B53826443 : Blo 2099435 53826443 := bstep (se 1 (by rfl) ⟨40369832, by rfl⟩ : syracuseStep 53826443 = 80739665) B80739665
theorem B35884295 : Blo 2099435 35884295 := bstep (se 1 (by rfl) ⟨26913221, by rfl⟩ : syracuseStep 35884295 = 53826443) B53826443
theorem B23922863 : Blo 2099435 23922863 := bstep (se 1 (by rfl) ⟨17942147, by rfl⟩ : syracuseStep 23922863 = 35884295) B35884295
theorem B15948575 : Blo 2099435 15948575 := bstep (se 1 (by rfl) ⟨11961431, by rfl⟩ : syracuseStep 15948575 = 23922863) B23922863
theorem B10632383 : Blo 2099435 10632383 := bstep (se 1 (by rfl) ⟨7974287, by rfl⟩ : syracuseStep 10632383 = 15948575) B15948575
theorem B7088255 : Blo 2099435 7088255 := bstep (se 1 (by rfl) ⟨5316191, by rfl⟩ : syracuseStep 7088255 = 10632383) B10632383
theorem B4725503 : Blo 2099435 4725503 := bstep (se 1 (by rfl) ⟨3544127, by rfl⟩ : syracuseStep 4725503 = 7088255) B7088255
theorem B3150335 : Blo 2099435 3150335 := bstep (se 1 (by rfl) ⟨2362751, by rfl⟩ : syracuseStep 3150335 = 4725503) B4725503
theorem B2100223 : Blo 2099435 2100223 := bstep (se 1 (by rfl) ⟨1575167, by rfl⟩ : syracuseStep 2100223 = 3150335) B3150335
theorem B3150341 : Blo 2099435 3150341 := bbase (se 4 (by rfl) ⟨295344, by rfl⟩ : syracuseStep 3150341 = 590689) (by norm_num)
theorem B2100227 : Blo 2099435 2100227 := bstep (se 1 (by rfl) ⟨1575170, by rfl⟩ : syracuseStep 2100227 = 3150341) B3150341
theorem B3544141 : Blo 2099435 3544141 := bbase (se 3 (by rfl) ⟨664526, by rfl⟩ : syracuseStep 3544141 = 1329053) (by norm_num)
theorem B4725521 : Blo 2099435 4725521 := bstep (se 2 (by rfl) ⟨1772070, by rfl⟩ : syracuseStep 4725521 = 3544141) B3544141
theorem B3150347 : Blo 2099435 3150347 := bstep (se 1 (by rfl) ⟨2362760, by rfl⟩ : syracuseStep 3150347 = 4725521) B4725521
theorem B2100231 : Blo 2099435 2100231 := bstep (se 1 (by rfl) ⟨1575173, by rfl⟩ : syracuseStep 2100231 = 3150347) B3150347
theorem B2362765 : Blo 2099435 2362765 := bbase (se 3 (by rfl) ⟨443018, by rfl⟩ : syracuseStep 2362765 = 886037) (by norm_num)
theorem B3150353 : Blo 2099435 3150353 := bstep (se 2 (by rfl) ⟨1181382, by rfl⟩ : syracuseStep 3150353 = 2362765) B2362765
theorem B2100235 : Blo 2099435 2100235 := bstep (se 1 (by rfl) ⟨1575176, by rfl⟩ : syracuseStep 2100235 = 3150353) B3150353
theorem B7088309 : Blo 2099435 7088309 := bbase (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) (by norm_num)
theorem B4725539 : Blo 2099435 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B3150359 : Blo 2099435 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B2100239 : Blo 2099435 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B3150365 : Blo 2099435 3150365 := bbase (se 3 (by rfl) ⟨590693, by rfl⟩ : syracuseStep 3150365 = 1181387) (by norm_num)
theorem B2100243 : Blo 2099435 2100243 := bstep (se 1 (by rfl) ⟨1575182, by rfl⟩ : syracuseStep 2100243 = 3150365) B3150365
theorem B4725557 : Blo 2099435 4725557 := bbase (se 5 (by rfl) ⟨221510, by rfl⟩ : syracuseStep 4725557 = 443021) (by norm_num)
theorem B3150371 : Blo 2099435 3150371 := bstep (se 1 (by rfl) ⟨2362778, by rfl⟩ : syracuseStep 3150371 = 4725557) B4725557
theorem B2100247 : Blo 2099435 2100247 := bstep (se 1 (by rfl) ⟨1575185, by rfl⟩ : syracuseStep 2100247 = 3150371) B3150371
theorem B2395021 : Blo 2099435 2395021 := bbase (se 3 (by rfl) ⟨449066, by rfl⟩ : syracuseStep 2395021 = 898133) (by norm_num)
theorem B3193361 : Blo 2099435 3193361 := bstep (se 2 (by rfl) ⟨1197510, by rfl⟩ : syracuseStep 3193361 = 2395021) B2395021
theorem B2128907 : Blo 2099435 2128907 := bstep (se 1 (by rfl) ⟨1596680, by rfl⟩ : syracuseStep 2128907 = 3193361) B3193361
theorem B5677085 : Blo 2099435 5677085 := bstep (se 3 (by rfl) ⟨1064453, by rfl⟩ : syracuseStep 5677085 = 2128907) B2128907
theorem B15138893 : Blo 2099435 15138893 := bstep (se 3 (by rfl) ⟨2838542, by rfl⟩ : syracuseStep 15138893 = 5677085) B5677085
theorem B10092595 : Blo 2099435 10092595 := bstep (se 1 (by rfl) ⟨7569446, by rfl⟩ : syracuseStep 10092595 = 15138893) B15138893
theorem B13456793 : Blo 2099435 13456793 := bstep (se 2 (by rfl) ⟨5046297, by rfl⟩ : syracuseStep 13456793 = 10092595) B10092595
theorem B8971195 : Blo 2099435 8971195 := bstep (se 1 (by rfl) ⟨6728396, by rfl⟩ : syracuseStep 8971195 = 13456793) B13456793
theorem B11961593 : Blo 2099435 11961593 := bstep (se 2 (by rfl) ⟨4485597, by rfl⟩ : syracuseStep 11961593 = 8971195) B8971195
theorem B7974395 : Blo 2099435 7974395 := bstep (se 1 (by rfl) ⟨5980796, by rfl⟩ : syracuseStep 7974395 = 11961593) B11961593
theorem B5316263 : Blo 2099435 5316263 := bstep (se 1 (by rfl) ⟨3987197, by rfl⟩ : syracuseStep 5316263 = 7974395) B7974395
theorem B3544175 : Blo 2099435 3544175 := bstep (se 1 (by rfl) ⟨2658131, by rfl⟩ : syracuseStep 3544175 = 5316263) B5316263
theorem B2362783 : Blo 2099435 2362783 := bstep (se 1 (by rfl) ⟨1772087, by rfl⟩ : syracuseStep 2362783 = 3544175) B3544175
theorem B3150377 : Blo 2099435 3150377 := bstep (se 2 (by rfl) ⟨1181391, by rfl⟩ : syracuseStep 3150377 = 2362783) B2362783
theorem B2100251 : Blo 2099435 2100251 := bstep (se 1 (by rfl) ⟨1575188, by rfl⟩ : syracuseStep 2100251 = 3150377) B3150377
theorem B10092613 : Blo 2099435 10092613 := bbase (se 4 (by rfl) ⟨946182, by rfl⟩ : syracuseStep 10092613 = 1892365) (by norm_num)
theorem B13456817 : Blo 2099435 13456817 := bstep (se 2 (by rfl) ⟨5046306, by rfl⟩ : syracuseStep 13456817 = 10092613) B10092613
theorem B8971211 : Blo 2099435 8971211 := bstep (se 1 (by rfl) ⟨6728408, by rfl⟩ : syracuseStep 8971211 = 13456817) B13456817
theorem B5980807 : Blo 2099435 5980807 := bstep (se 1 (by rfl) ⟨4485605, by rfl⟩ : syracuseStep 5980807 = 8971211) B8971211
theorem B7974409 : Blo 2099435 7974409 := bstep (se 2 (by rfl) ⟨2990403, by rfl⟩ : syracuseStep 7974409 = 5980807) B5980807
theorem B10632545 : Blo 2099435 10632545 := bstep (se 2 (by rfl) ⟨3987204, by rfl⟩ : syracuseStep 10632545 = 7974409) B7974409
theorem B7088363 : Blo 2099435 7088363 := bstep (se 1 (by rfl) ⟨5316272, by rfl⟩ : syracuseStep 7088363 = 10632545) B10632545
theorem B4725575 : Blo 2099435 4725575 := bstep (se 1 (by rfl) ⟨3544181, by rfl⟩ : syracuseStep 4725575 = 7088363) B7088363
theorem B3150383 : Blo 2099435 3150383 := bstep (se 1 (by rfl) ⟨2362787, by rfl⟩ : syracuseStep 3150383 = 4725575) B4725575
theorem B2100255 : Blo 2099435 2100255 := bstep (se 1 (by rfl) ⟨1575191, by rfl⟩ : syracuseStep 2100255 = 3150383) B3150383
theorem B3150389 : Blo 2099435 3150389 := bbase (se 5 (by rfl) ⟨147674, by rfl⟩ : syracuseStep 3150389 = 295349) (by norm_num)
theorem B2100259 : Blo 2099435 2100259 := bstep (se 1 (by rfl) ⟨1575194, by rfl⟩ : syracuseStep 2100259 = 3150389) B3150389
theorem B5316293 : Blo 2099435 5316293 := bbase (se 4 (by rfl) ⟨498402, by rfl⟩ : syracuseStep 5316293 = 996805) (by norm_num)
theorem B3544195 : Blo 2099435 3544195 := bstep (se 1 (by rfl) ⟨2658146, by rfl⟩ : syracuseStep 3544195 = 5316293) B5316293
theorem B4725593 : Blo 2099435 4725593 := bstep (se 2 (by rfl) ⟨1772097, by rfl⟩ : syracuseStep 4725593 = 3544195) B3544195
theorem B3150395 : Blo 2099435 3150395 := bstep (se 1 (by rfl) ⟨2362796, by rfl⟩ : syracuseStep 3150395 = 4725593) B4725593
theorem B2100263 : Blo 2099435 2100263 := bstep (se 1 (by rfl) ⟨1575197, by rfl⟩ : syracuseStep 2100263 = 3150395) B3150395
theorem B2362801 : Blo 2099435 2362801 := bbase (se 2 (by rfl) ⟨886050, by rfl⟩ : syracuseStep 2362801 = 1772101) (by norm_num)
theorem B3150401 : Blo 2099435 3150401 := bstep (se 2 (by rfl) ⟨1181400, by rfl⟩ : syracuseStep 3150401 = 2362801) B2362801
theorem B2100267 : Blo 2099435 2100267 := bstep (se 1 (by rfl) ⟨1575200, by rfl⟩ : syracuseStep 2100267 = 3150401) B3150401
theorem B5980853 : Blo 2099435 5980853 := bbase (se 5 (by rfl) ⟨280352, by rfl⟩ : syracuseStep 5980853 = 560705) (by norm_num)
theorem B3987235 : Blo 2099435 3987235 := bstep (se 1 (by rfl) ⟨2990426, by rfl⟩ : syracuseStep 3987235 = 5980853) B5980853
theorem B5316313 : Blo 2099435 5316313 := bstep (se 2 (by rfl) ⟨1993617, by rfl⟩ : syracuseStep 5316313 = 3987235) B3987235
theorem B7088417 : Blo 2099435 7088417 := bstep (se 2 (by rfl) ⟨2658156, by rfl⟩ : syracuseStep 7088417 = 5316313) B5316313
theorem B4725611 : Blo 2099435 4725611 := bstep (se 1 (by rfl) ⟨3544208, by rfl⟩ : syracuseStep 4725611 = 7088417) B7088417
theorem B3150407 : Blo 2099435 3150407 := bstep (se 1 (by rfl) ⟨2362805, by rfl⟩ : syracuseStep 3150407 = 4725611) B4725611
theorem B2100271 : Blo 2099435 2100271 := bstep (se 1 (by rfl) ⟨1575203, by rfl⟩ : syracuseStep 2100271 = 3150407) B3150407
theorem B3150413 : Blo 2099435 3150413 := bbase (se 3 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 3150413 = 1181405) (by norm_num)
theorem B2100275 : Blo 2099435 2100275 := bstep (se 1 (by rfl) ⟨1575206, by rfl⟩ : syracuseStep 2100275 = 3150413) B3150413
theorem B4725629 : Blo 2099435 4725629 := bbase (se 3 (by rfl) ⟨886055, by rfl⟩ : syracuseStep 4725629 = 1772111) (by norm_num)
theorem B3150419 : Blo 2099435 3150419 := bstep (se 1 (by rfl) ⟨2362814, by rfl⟩ : syracuseStep 3150419 = 4725629) B4725629
theorem B2100279 : Blo 2099435 2100279 := bstep (se 1 (by rfl) ⟨1575209, by rfl⟩ : syracuseStep 2100279 = 3150419) B3150419
theorem B3544229 : Blo 2099435 3544229 := bbase (se 4 (by rfl) ⟨332271, by rfl⟩ : syracuseStep 3544229 = 664543) (by norm_num)
theorem B2362819 : Blo 2099435 2362819 := bstep (se 1 (by rfl) ⟨1772114, by rfl⟩ : syracuseStep 2362819 = 3544229) B3544229
theorem B3150425 : Blo 2099435 3150425 := bstep (se 2 (by rfl) ⟨1181409, by rfl⟩ : syracuseStep 3150425 = 2362819) B2362819
theorem B2100283 : Blo 2099435 2100283 := bstep (se 1 (by rfl) ⟨1575212, by rfl⟩ : syracuseStep 2100283 = 3150425) B3150425
theorem B2242837 : Blo 2099435 2242837 := bbase (se 6 (by rfl) ⟨52566, by rfl⟩ : syracuseStep 2242837 = 105133) (by norm_num)
theorem B2990449 : Blo 2099435 2990449 := bstep (se 2 (by rfl) ⟨1121418, by rfl⟩ : syracuseStep 2990449 = 2242837) B2242837
theorem B15949061 : Blo 2099435 15949061 := bstep (se 4 (by rfl) ⟨1495224, by rfl⟩ : syracuseStep 15949061 = 2990449) B2990449
theorem B10632707 : Blo 2099435 10632707 := bstep (se 1 (by rfl) ⟨7974530, by rfl⟩ : syracuseStep 10632707 = 15949061) B15949061
theorem B7088471 : Blo 2099435 7088471 := bstep (se 1 (by rfl) ⟨5316353, by rfl⟩ : syracuseStep 7088471 = 10632707) B10632707
theorem B4725647 : Blo 2099435 4725647 := bstep (se 1 (by rfl) ⟨3544235, by rfl⟩ : syracuseStep 4725647 = 7088471) B7088471
theorem B3150431 : Blo 2099435 3150431 := bstep (se 1 (by rfl) ⟨2362823, by rfl⟩ : syracuseStep 3150431 = 4725647) B4725647
theorem B2100287 : Blo 2099435 2100287 := bstep (se 1 (by rfl) ⟨1575215, by rfl⟩ : syracuseStep 2100287 = 3150431) B3150431
theorem B3150437 : Blo 2099435 3150437 := bbase (se 4 (by rfl) ⟨295353, by rfl⟩ : syracuseStep 3150437 = 590707) (by norm_num)
theorem B2100291 : Blo 2099435 2100291 := bstep (se 1 (by rfl) ⟨1575218, by rfl⟩ : syracuseStep 2100291 = 3150437) B3150437
theorem B2990461 : Blo 2099435 2990461 := bbase (se 3 (by rfl) ⟨560711, by rfl⟩ : syracuseStep 2990461 = 1121423) (by norm_num)
theorem B3987281 : Blo 2099435 3987281 := bstep (se 2 (by rfl) ⟨1495230, by rfl⟩ : syracuseStep 3987281 = 2990461) B2990461
theorem B2658187 : Blo 2099435 2658187 := bstep (se 1 (by rfl) ⟨1993640, by rfl⟩ : syracuseStep 2658187 = 3987281) B3987281
theorem B3544249 : Blo 2099435 3544249 := bstep (se 2 (by rfl) ⟨1329093, by rfl⟩ : syracuseStep 3544249 = 2658187) B2658187
theorem B4725665 : Blo 2099435 4725665 := bstep (se 2 (by rfl) ⟨1772124, by rfl⟩ : syracuseStep 4725665 = 3544249) B3544249
theorem B3150443 : Blo 2099435 3150443 := bstep (se 1 (by rfl) ⟨2362832, by rfl⟩ : syracuseStep 3150443 = 4725665) B4725665
theorem B2100295 : Blo 2099435 2100295 := bstep (se 1 (by rfl) ⟨1575221, by rfl⟩ : syracuseStep 2100295 = 3150443) B3150443
theorem B2362837 : Blo 2099435 2362837 := bbase (se 7 (by rfl) ⟨27689, by rfl⟩ : syracuseStep 2362837 = 55379) (by norm_num)
theorem B3150449 : Blo 2099435 3150449 := bstep (se 2 (by rfl) ⟨1181418, by rfl⟩ : syracuseStep 3150449 = 2362837) B2362837
theorem B2100299 : Blo 2099435 2100299 := bstep (se 1 (by rfl) ⟨1575224, by rfl⟩ : syracuseStep 2100299 = 3150449) B3150449
theorem B2658197 : Blo 2099435 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B7088525 : Blo 2099435 7088525 := bstep (se 3 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 7088525 = 2658197) B2658197
theorem B4725683 : Blo 2099435 4725683 := bstep (se 1 (by rfl) ⟨3544262, by rfl⟩ : syracuseStep 4725683 = 7088525) B7088525
theorem B3150455 : Blo 2099435 3150455 := bstep (se 1 (by rfl) ⟨2362841, by rfl⟩ : syracuseStep 3150455 = 4725683) B4725683
theorem B2100303 : Blo 2099435 2100303 := bstep (se 1 (by rfl) ⟨1575227, by rfl⟩ : syracuseStep 2100303 = 3150455) B3150455
theorem B3150461 : Blo 2099435 3150461 := bbase (se 3 (by rfl) ⟨590711, by rfl⟩ : syracuseStep 3150461 = 1181423) (by norm_num)
theorem B2100307 : Blo 2099435 2100307 := bstep (se 1 (by rfl) ⟨1575230, by rfl⟩ : syracuseStep 2100307 = 3150461) B3150461
theorem B4725701 : Blo 2099435 4725701 := bbase (se 4 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 4725701 = 886069) (by norm_num)
theorem B3150467 : Blo 2099435 3150467 := bstep (se 1 (by rfl) ⟨2362850, by rfl⟩ : syracuseStep 3150467 = 4725701) B4725701
theorem B2100311 : Blo 2099435 2100311 := bstep (se 1 (by rfl) ⟨1575233, by rfl⟩ : syracuseStep 2100311 = 3150467) B3150467
theorem B3364301 : Blo 2099435 3364301 := bbase (se 3 (by rfl) ⟨630806, by rfl⟩ : syracuseStep 3364301 = 1261613) (by norm_num)
theorem B8971469 : Blo 2099435 8971469 := bstep (se 3 (by rfl) ⟨1682150, by rfl⟩ : syracuseStep 8971469 = 3364301) B3364301
theorem B5980979 : Blo 2099435 5980979 := bstep (se 1 (by rfl) ⟨4485734, by rfl⟩ : syracuseStep 5980979 = 8971469) B8971469
theorem B3987319 : Blo 2099435 3987319 := bstep (se 1 (by rfl) ⟨2990489, by rfl⟩ : syracuseStep 3987319 = 5980979) B5980979
theorem B5316425 : Blo 2099435 5316425 := bstep (se 2 (by rfl) ⟨1993659, by rfl⟩ : syracuseStep 5316425 = 3987319) B3987319
theorem B3544283 : Blo 2099435 3544283 := bstep (se 1 (by rfl) ⟨2658212, by rfl⟩ : syracuseStep 3544283 = 5316425) B5316425
theorem B2362855 : Blo 2099435 2362855 := bstep (se 1 (by rfl) ⟨1772141, by rfl⟩ : syracuseStep 2362855 = 3544283) B3544283
theorem B3150473 : Blo 2099435 3150473 := bstep (se 2 (by rfl) ⟨1181427, by rfl⟩ : syracuseStep 3150473 = 2362855) B2362855
theorem B2100315 : Blo 2099435 2100315 := bstep (se 1 (by rfl) ⟨1575236, by rfl⟩ : syracuseStep 2100315 = 3150473) B3150473
theorem B10632869 : Blo 2099435 10632869 := bbase (se 4 (by rfl) ⟨996831, by rfl⟩ : syracuseStep 10632869 = 1993663) (by norm_num)
theorem B7088579 : Blo 2099435 7088579 := bstep (se 1 (by rfl) ⟨5316434, by rfl⟩ : syracuseStep 7088579 = 10632869) B10632869
theorem B4725719 : Blo 2099435 4725719 := bstep (se 1 (by rfl) ⟨3544289, by rfl⟩ : syracuseStep 4725719 = 7088579) B7088579
theorem B3150479 : Blo 2099435 3150479 := bstep (se 1 (by rfl) ⟨2362859, by rfl⟩ : syracuseStep 3150479 = 4725719) B4725719
theorem B2100319 : Blo 2099435 2100319 := bstep (se 1 (by rfl) ⟨1575239, by rfl⟩ : syracuseStep 2100319 = 3150479) B3150479
theorem B3150485 : Blo 2099435 3150485 := bbase (se 6 (by rfl) ⟨73839, by rfl⟩ : syracuseStep 3150485 = 147679) (by norm_num)
theorem B2100323 : Blo 2099435 2100323 := bstep (se 1 (by rfl) ⟨1575242, by rfl⟩ : syracuseStep 2100323 = 3150485) B3150485
theorem B3410221 : Blo 2099435 3410221 := bbase (se 3 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 3410221 = 1278833) (by norm_num)
theorem B4546961 : Blo 2099435 4546961 := bstep (se 2 (by rfl) ⟨1705110, by rfl⟩ : syracuseStep 4546961 = 3410221) B3410221
theorem B3031307 : Blo 2099435 3031307 := bstep (se 1 (by rfl) ⟨2273480, by rfl⟩ : syracuseStep 3031307 = 4546961) B4546961
theorem B32333941 : Blo 2099435 32333941 := bstep (se 5 (by rfl) ⟨1515653, by rfl⟩ : syracuseStep 32333941 = 3031307) B3031307
theorem B43111921 : Blo 2099435 43111921 := bstep (se 2 (by rfl) ⟨16166970, by rfl⟩ : syracuseStep 43111921 = 32333941) B32333941
theorem B57482561 : Blo 2099435 57482561 := bstep (se 2 (by rfl) ⟨21555960, by rfl⟩ : syracuseStep 57482561 = 43111921) B43111921
theorem B153286829 : Blo 2099435 153286829 := bstep (se 3 (by rfl) ⟨28741280, by rfl⟩ : syracuseStep 153286829 = 57482561) B57482561
theorem B102191219 : Blo 2099435 102191219 := bstep (se 1 (by rfl) ⟨76643414, by rfl⟩ : syracuseStep 102191219 = 153286829) B153286829
theorem B68127479 : Blo 2099435 68127479 := bstep (se 1 (by rfl) ⟨51095609, by rfl⟩ : syracuseStep 68127479 = 102191219) B102191219
theorem B45418319 : Blo 2099435 45418319 := bstep (se 1 (by rfl) ⟨34063739, by rfl⟩ : syracuseStep 45418319 = 68127479) B68127479
theorem B30278879 : Blo 2099435 30278879 := bstep (se 1 (by rfl) ⟨22709159, by rfl⟩ : syracuseStep 30278879 = 45418319) B45418319
theorem B20185919 : Blo 2099435 20185919 := bstep (se 1 (by rfl) ⟨15139439, by rfl⟩ : syracuseStep 20185919 = 30278879) B30278879
theorem B13457279 : Blo 2099435 13457279 := bstep (se 1 (by rfl) ⟨10092959, by rfl⟩ : syracuseStep 13457279 = 20185919) B20185919
theorem B8971519 : Blo 2099435 8971519 := bstep (se 1 (by rfl) ⟨6728639, by rfl⟩ : syracuseStep 8971519 = 13457279) B13457279
theorem B11962025 : Blo 2099435 11962025 := bstep (se 2 (by rfl) ⟨4485759, by rfl⟩ : syracuseStep 11962025 = 8971519) B8971519
theorem B7974683 : Blo 2099435 7974683 := bstep (se 1 (by rfl) ⟨5981012, by rfl⟩ : syracuseStep 7974683 = 11962025) B11962025
theorem B5316455 : Blo 2099435 5316455 := bstep (se 1 (by rfl) ⟨3987341, by rfl⟩ : syracuseStep 5316455 = 7974683) B7974683
theorem B3544303 : Blo 2099435 3544303 := bstep (se 1 (by rfl) ⟨2658227, by rfl⟩ : syracuseStep 3544303 = 5316455) B5316455
theorem B4725737 : Blo 2099435 4725737 := bstep (se 2 (by rfl) ⟨1772151, by rfl⟩ : syracuseStep 4725737 = 3544303) B3544303
theorem B3150491 : Blo 2099435 3150491 := bstep (se 1 (by rfl) ⟨2362868, by rfl⟩ : syracuseStep 3150491 = 4725737) B4725737
theorem B2100327 : Blo 2099435 2100327 := bstep (se 1 (by rfl) ⟨1575245, by rfl⟩ : syracuseStep 2100327 = 3150491) B3150491
theorem B2362873 : Blo 2099435 2362873 := bbase (se 2 (by rfl) ⟨886077, by rfl⟩ : syracuseStep 2362873 = 1772155) (by norm_num)
theorem B3150497 : Blo 2099435 3150497 := bstep (se 2 (by rfl) ⟨1181436, by rfl⟩ : syracuseStep 3150497 = 2362873) B2362873
theorem B2100331 : Blo 2099435 2100331 := bstep (se 1 (by rfl) ⟨1575248, by rfl⟩ : syracuseStep 2100331 = 3150497) B3150497
theorem B7569749 : Blo 2099435 7569749 := bbase (se 10 (by rfl) ⟨11088, by rfl⟩ : syracuseStep 7569749 = 22177) (by norm_num)
theorem B5046499 : Blo 2099435 5046499 := bstep (se 1 (by rfl) ⟨3784874, by rfl⟩ : syracuseStep 5046499 = 7569749) B7569749
theorem B6728665 : Blo 2099435 6728665 := bstep (se 2 (by rfl) ⟨2523249, by rfl⟩ : syracuseStep 6728665 = 5046499) B5046499
theorem B8971553 : Blo 2099435 8971553 := bstep (se 2 (by rfl) ⟨3364332, by rfl⟩ : syracuseStep 8971553 = 6728665) B6728665
theorem B5981035 : Blo 2099435 5981035 := bstep (se 1 (by rfl) ⟨4485776, by rfl⟩ : syracuseStep 5981035 = 8971553) B8971553
theorem B7974713 : Blo 2099435 7974713 := bstep (se 2 (by rfl) ⟨2990517, by rfl⟩ : syracuseStep 7974713 = 5981035) B5981035
theorem B5316475 : Blo 2099435 5316475 := bstep (se 1 (by rfl) ⟨3987356, by rfl⟩ : syracuseStep 5316475 = 7974713) B7974713
theorem B7088633 : Blo 2099435 7088633 := bstep (se 2 (by rfl) ⟨2658237, by rfl⟩ : syracuseStep 7088633 = 5316475) B5316475
theorem B4725755 : Blo 2099435 4725755 := bstep (se 1 (by rfl) ⟨3544316, by rfl⟩ : syracuseStep 4725755 = 7088633) B7088633
theorem B3150503 : Blo 2099435 3150503 := bstep (se 1 (by rfl) ⟨2362877, by rfl⟩ : syracuseStep 3150503 = 4725755) B4725755
theorem B2100335 : Blo 2099435 2100335 := bstep (se 1 (by rfl) ⟨1575251, by rfl⟩ : syracuseStep 2100335 = 3150503) B3150503
theorem B3150509 : Blo 2099435 3150509 := bbase (se 3 (by rfl) ⟨590720, by rfl⟩ : syracuseStep 3150509 = 1181441) (by norm_num)
theorem B2100339 : Blo 2099435 2100339 := bstep (se 1 (by rfl) ⟨1575254, by rfl⟩ : syracuseStep 2100339 = 3150509) B3150509
theorem B4725773 : Blo 2099435 4725773 := bbase (se 3 (by rfl) ⟨886082, by rfl⟩ : syracuseStep 4725773 = 1772165) (by norm_num)
theorem B3150515 : Blo 2099435 3150515 := bstep (se 1 (by rfl) ⟨2362886, by rfl⟩ : syracuseStep 3150515 = 4725773) B4725773
theorem B2100343 : Blo 2099435 2100343 := bstep (se 1 (by rfl) ⟨1575257, by rfl⟩ : syracuseStep 2100343 = 3150515) B3150515
theorem B2658253 : Blo 2099435 2658253 := bbase (se 3 (by rfl) ⟨498422, by rfl⟩ : syracuseStep 2658253 = 996845) (by norm_num)
theorem B3544337 : Blo 2099435 3544337 := bstep (se 2 (by rfl) ⟨1329126, by rfl⟩ : syracuseStep 3544337 = 2658253) B2658253
theorem B2362891 : Blo 2099435 2362891 := bstep (se 1 (by rfl) ⟨1772168, by rfl⟩ : syracuseStep 2362891 = 3544337) B3544337
theorem B3150521 : Blo 2099435 3150521 := bstep (se 2 (by rfl) ⟨1181445, by rfl⟩ : syracuseStep 3150521 = 2362891) B2362891
theorem B2100347 : Blo 2099435 2100347 := bstep (se 1 (by rfl) ⟨1575260, by rfl⟩ : syracuseStep 2100347 = 3150521) B3150521
theorem B2838677 : Blo 2099435 2838677 := bbase (se 6 (by rfl) ⟨66531, by rfl⟩ : syracuseStep 2838677 = 133063) (by norm_num)
theorem B30279221 : Blo 2099435 30279221 := bstep (se 5 (by rfl) ⟨1419338, by rfl⟩ : syracuseStep 30279221 = 2838677) B2838677
theorem B20186147 : Blo 2099435 20186147 := bstep (se 1 (by rfl) ⟨15139610, by rfl⟩ : syracuseStep 20186147 = 30279221) B30279221
theorem B13457431 : Blo 2099435 13457431 := bstep (se 1 (by rfl) ⟨10093073, by rfl⟩ : syracuseStep 13457431 = 20186147) B20186147
theorem B17943241 : Blo 2099435 17943241 := bstep (se 2 (by rfl) ⟨6728715, by rfl⟩ : syracuseStep 17943241 = 13457431) B13457431
theorem B23924321 : Blo 2099435 23924321 := bstep (se 2 (by rfl) ⟨8971620, by rfl⟩ : syracuseStep 23924321 = 17943241) B17943241
theorem B15949547 : Blo 2099435 15949547 := bstep (se 1 (by rfl) ⟨11962160, by rfl⟩ : syracuseStep 15949547 = 23924321) B23924321
theorem B10633031 : Blo 2099435 10633031 := bstep (se 1 (by rfl) ⟨7974773, by rfl⟩ : syracuseStep 10633031 = 15949547) B15949547
theorem B7088687 : Blo 2099435 7088687 := bstep (se 1 (by rfl) ⟨5316515, by rfl⟩ : syracuseStep 7088687 = 10633031) B10633031
theorem B4725791 : Blo 2099435 4725791 := bstep (se 1 (by rfl) ⟨3544343, by rfl⟩ : syracuseStep 4725791 = 7088687) B7088687
theorem B3150527 : Blo 2099435 3150527 := bstep (se 1 (by rfl) ⟨2362895, by rfl⟩ : syracuseStep 3150527 = 4725791) B4725791
theorem B2100351 : Blo 2099435 2100351 := bstep (se 1 (by rfl) ⟨1575263, by rfl⟩ : syracuseStep 2100351 = 3150527) B3150527
theorem B3150533 : Blo 2099435 3150533 := bbase (se 4 (by rfl) ⟨295362, by rfl⟩ : syracuseStep 3150533 = 590725) (by norm_num)
theorem B2100355 : Blo 2099435 2100355 := bstep (se 1 (by rfl) ⟨1575266, by rfl⟩ : syracuseStep 2100355 = 3150533) B3150533
theorem B3544357 : Blo 2099435 3544357 := bbase (se 4 (by rfl) ⟨332283, by rfl⟩ : syracuseStep 3544357 = 664567) (by norm_num)
theorem B4725809 : Blo 2099435 4725809 := bstep (se 2 (by rfl) ⟨1772178, by rfl⟩ : syracuseStep 4725809 = 3544357) B3544357
theorem B3150539 : Blo 2099435 3150539 := bstep (se 1 (by rfl) ⟨2362904, by rfl⟩ : syracuseStep 3150539 = 4725809) B4725809
theorem B2100359 : Blo 2099435 2100359 := bstep (se 1 (by rfl) ⟨1575269, by rfl⟩ : syracuseStep 2100359 = 3150539) B3150539
theorem B2362909 : Blo 2099435 2362909 := bbase (se 3 (by rfl) ⟨443045, by rfl⟩ : syracuseStep 2362909 = 886091) (by norm_num)
theorem B3150545 : Blo 2099435 3150545 := bstep (se 2 (by rfl) ⟨1181454, by rfl⟩ : syracuseStep 3150545 = 2362909) B2362909
theorem B2100363 : Blo 2099435 2100363 := bstep (se 1 (by rfl) ⟨1575272, by rfl⟩ : syracuseStep 2100363 = 3150545) B3150545
theorem B7088741 : Blo 2099435 7088741 := bbase (se 4 (by rfl) ⟨664569, by rfl⟩ : syracuseStep 7088741 = 1329139) (by norm_num)
theorem B4725827 : Blo 2099435 4725827 := bstep (se 1 (by rfl) ⟨3544370, by rfl⟩ : syracuseStep 4725827 = 7088741) B7088741
theorem B3150551 : Blo 2099435 3150551 := bstep (se 1 (by rfl) ⟨2362913, by rfl⟩ : syracuseStep 3150551 = 4725827) B4725827
theorem B2100367 : Blo 2099435 2100367 := bstep (se 1 (by rfl) ⟨1575275, by rfl⟩ : syracuseStep 2100367 = 3150551) B3150551
theorem B3150557 : Blo 2099435 3150557 := bbase (se 3 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 3150557 = 1181459) (by norm_num)
theorem B2100371 : Blo 2099435 2100371 := bstep (se 1 (by rfl) ⟨1575278, by rfl⟩ : syracuseStep 2100371 = 3150557) B3150557
theorem B4725845 : Blo 2099435 4725845 := bbase (se 8 (by rfl) ⟨27690, by rfl⟩ : syracuseStep 4725845 = 55381) (by norm_num)
theorem B3150563 : Blo 2099435 3150563 := bstep (se 1 (by rfl) ⟨2362922, by rfl⟩ : syracuseStep 3150563 = 4725845) B4725845
theorem B2100375 : Blo 2099435 2100375 := bstep (se 1 (by rfl) ⟨1575281, by rfl⟩ : syracuseStep 2100375 = 3150563) B3150563
theorem B10230917 : Blo 2099435 10230917 := bbase (se 4 (by rfl) ⟨959148, by rfl⟩ : syracuseStep 10230917 = 1918297) (by norm_num)
theorem B109129781 : Blo 2099435 109129781 := bstep (se 5 (by rfl) ⟨5115458, by rfl⟩ : syracuseStep 109129781 = 10230917) B10230917
theorem B72753187 : Blo 2099435 72753187 := bstep (se 1 (by rfl) ⟨54564890, by rfl⟩ : syracuseStep 72753187 = 109129781) B109129781
theorem B97004249 : Blo 2099435 97004249 := bstep (se 2 (by rfl) ⟨36376593, by rfl⟩ : syracuseStep 97004249 = 72753187) B72753187
theorem B64669499 : Blo 2099435 64669499 := bstep (se 1 (by rfl) ⟨48502124, by rfl⟩ : syracuseStep 64669499 = 97004249) B97004249
theorem B43112999 : Blo 2099435 43112999 := bstep (se 1 (by rfl) ⟨32334749, by rfl⟩ : syracuseStep 43112999 = 64669499) B64669499
theorem B28741999 : Blo 2099435 28741999 := bstep (se 1 (by rfl) ⟨21556499, by rfl⟩ : syracuseStep 28741999 = 43112999) B43112999
theorem B38322665 : Blo 2099435 38322665 := bstep (se 2 (by rfl) ⟨14370999, by rfl⟩ : syracuseStep 38322665 = 28741999) B28741999
theorem B25548443 : Blo 2099435 25548443 := bstep (se 1 (by rfl) ⟨19161332, by rfl⟩ : syracuseStep 25548443 = 38322665) B38322665
theorem B17032295 : Blo 2099435 17032295 := bstep (se 1 (by rfl) ⟨12774221, by rfl⟩ : syracuseStep 17032295 = 25548443) B25548443
theorem B11354863 : Blo 2099435 11354863 := bstep (se 1 (by rfl) ⟨8516147, by rfl⟩ : syracuseStep 11354863 = 17032295) B17032295
theorem B15139817 : Blo 2099435 15139817 := bstep (se 2 (by rfl) ⟨5677431, by rfl⟩ : syracuseStep 15139817 = 11354863) B11354863
theorem B10093211 : Blo 2099435 10093211 := bstep (se 1 (by rfl) ⟨7569908, by rfl⟩ : syracuseStep 10093211 = 15139817) B15139817
theorem B6728807 : Blo 2099435 6728807 := bstep (se 1 (by rfl) ⟨5046605, by rfl⟩ : syracuseStep 6728807 = 10093211) B10093211
theorem B4485871 : Blo 2099435 4485871 := bstep (se 1 (by rfl) ⟨3364403, by rfl⟩ : syracuseStep 4485871 = 6728807) B6728807
theorem B5981161 : Blo 2099435 5981161 := bstep (se 2 (by rfl) ⟨2242935, by rfl⟩ : syracuseStep 5981161 = 4485871) B4485871
theorem B7974881 : Blo 2099435 7974881 := bstep (se 2 (by rfl) ⟨2990580, by rfl⟩ : syracuseStep 7974881 = 5981161) B5981161
theorem B5316587 : Blo 2099435 5316587 := bstep (se 1 (by rfl) ⟨3987440, by rfl⟩ : syracuseStep 5316587 = 7974881) B7974881
theorem B3544391 : Blo 2099435 3544391 := bstep (se 1 (by rfl) ⟨2658293, by rfl⟩ : syracuseStep 3544391 = 5316587) B5316587
theorem B2362927 : Blo 2099435 2362927 := bstep (se 1 (by rfl) ⟨1772195, by rfl⟩ : syracuseStep 2362927 = 3544391) B3544391
theorem B3150569 : Blo 2099435 3150569 := bstep (se 2 (by rfl) ⟨1181463, by rfl⟩ : syracuseStep 3150569 = 2362927) B2362927
theorem B2100379 : Blo 2099435 2100379 := bstep (se 1 (by rfl) ⟨1575284, by rfl⟩ : syracuseStep 2100379 = 3150569) B3150569
theorem B4790341 : Blo 2099435 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B6387121 : Blo 2099435 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B8516161 : Blo 2099435 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B45419525 : Blo 2099435 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B30279683 : Blo 2099435 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B20186455 : Blo 2099435 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B26915273 : Blo 2099435 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B17943515 : Blo 2099435 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B11962343 : Blo 2099435 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B7974895 : Blo 2099435 7974895 := bstep (se 1 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 7974895 = 11962343) B11962343
theorem B10633193 : Blo 2099435 10633193 := bstep (se 2 (by rfl) ⟨3987447, by rfl⟩ : syracuseStep 10633193 = 7974895) B7974895
theorem B7088795 : Blo 2099435 7088795 := bstep (se 1 (by rfl) ⟨5316596, by rfl⟩ : syracuseStep 7088795 = 10633193) B10633193
theorem B4725863 : Blo 2099435 4725863 := bstep (se 1 (by rfl) ⟨3544397, by rfl⟩ : syracuseStep 4725863 = 7088795) B7088795
theorem B3150575 : Blo 2099435 3150575 := bstep (se 1 (by rfl) ⟨2362931, by rfl⟩ : syracuseStep 3150575 = 4725863) B4725863
theorem B2100383 : Blo 2099435 2100383 := bstep (se 1 (by rfl) ⟨1575287, by rfl⟩ : syracuseStep 2100383 = 3150575) B3150575
theorem B3150581 : Blo 2099435 3150581 := bbase (se 5 (by rfl) ⟨147683, by rfl⟩ : syracuseStep 3150581 = 295367) (by norm_num)
theorem B2100387 : Blo 2099435 2100387 := bstep (se 1 (by rfl) ⟨1575290, by rfl⟩ : syracuseStep 2100387 = 3150581) B3150581
theorem B2523317 : Blo 2099435 2523317 := bbase (se 5 (by rfl) ⟨118280, by rfl⟩ : syracuseStep 2523317 = 236561) (by norm_num)
theorem B6728845 : Blo 2099435 6728845 := bstep (se 3 (by rfl) ⟨1261658, by rfl⟩ : syracuseStep 6728845 = 2523317) B2523317
theorem B8971793 : Blo 2099435 8971793 := bstep (se 2 (by rfl) ⟨3364422, by rfl⟩ : syracuseStep 8971793 = 6728845) B6728845
theorem B5981195 : Blo 2099435 5981195 := bstep (se 1 (by rfl) ⟨4485896, by rfl⟩ : syracuseStep 5981195 = 8971793) B8971793
theorem B3987463 : Blo 2099435 3987463 := bstep (se 1 (by rfl) ⟨2990597, by rfl⟩ : syracuseStep 3987463 = 5981195) B5981195
theorem B5316617 : Blo 2099435 5316617 := bstep (se 2 (by rfl) ⟨1993731, by rfl⟩ : syracuseStep 5316617 = 3987463) B3987463
theorem B3544411 : Blo 2099435 3544411 := bstep (se 1 (by rfl) ⟨2658308, by rfl⟩ : syracuseStep 3544411 = 5316617) B5316617
theorem B4725881 : Blo 2099435 4725881 := bstep (se 2 (by rfl) ⟨1772205, by rfl⟩ : syracuseStep 4725881 = 3544411) B3544411
theorem B3150587 : Blo 2099435 3150587 := bstep (se 1 (by rfl) ⟨2362940, by rfl⟩ : syracuseStep 3150587 = 4725881) B4725881
theorem B2100391 : Blo 2099435 2100391 := bstep (se 1 (by rfl) ⟨1575293, by rfl⟩ : syracuseStep 2100391 = 3150587) B3150587
theorem B2362945 : Blo 2099435 2362945 := bbase (se 2 (by rfl) ⟨886104, by rfl⟩ : syracuseStep 2362945 = 1772209) (by norm_num)
theorem B3150593 : Blo 2099435 3150593 := bstep (se 2 (by rfl) ⟨1181472, by rfl⟩ : syracuseStep 3150593 = 2362945) B2362945
theorem B2100395 : Blo 2099435 2100395 := bstep (se 1 (by rfl) ⟨1575296, by rfl⟩ : syracuseStep 2100395 = 3150593) B3150593
theorem B5316637 : Blo 2099435 5316637 := bbase (se 3 (by rfl) ⟨996869, by rfl⟩ : syracuseStep 5316637 = 1993739) (by norm_num)
theorem B7088849 : Blo 2099435 7088849 := bstep (se 2 (by rfl) ⟨2658318, by rfl⟩ : syracuseStep 7088849 = 5316637) B5316637
theorem B4725899 : Blo 2099435 4725899 := bstep (se 1 (by rfl) ⟨3544424, by rfl⟩ : syracuseStep 4725899 = 7088849) B7088849
theorem B3150599 : Blo 2099435 3150599 := bstep (se 1 (by rfl) ⟨2362949, by rfl⟩ : syracuseStep 3150599 = 4725899) B4725899
theorem B2100399 : Blo 2099435 2100399 := bstep (se 1 (by rfl) ⟨1575299, by rfl⟩ : syracuseStep 2100399 = 3150599) B3150599
theorem B3150605 : Blo 2099435 3150605 := bbase (se 3 (by rfl) ⟨590738, by rfl⟩ : syracuseStep 3150605 = 1181477) (by norm_num)
theorem B2100403 : Blo 2099435 2100403 := bstep (se 1 (by rfl) ⟨1575302, by rfl⟩ : syracuseStep 2100403 = 3150605) B3150605
theorem B4725917 : Blo 2099435 4725917 := bbase (se 3 (by rfl) ⟨886109, by rfl⟩ : syracuseStep 4725917 = 1772219) (by norm_num)
theorem B3150611 : Blo 2099435 3150611 := bstep (se 1 (by rfl) ⟨2362958, by rfl⟩ : syracuseStep 3150611 = 4725917) B4725917
theorem B2100407 : Blo 2099435 2100407 := bstep (se 1 (by rfl) ⟨1575305, by rfl⟩ : syracuseStep 2100407 = 3150611) B3150611
theorem B3544445 : Blo 2099435 3544445 := bbase (se 3 (by rfl) ⟨664583, by rfl⟩ : syracuseStep 3544445 = 1329167) (by norm_num)
theorem B2362963 : Blo 2099435 2362963 := bstep (se 1 (by rfl) ⟨1772222, by rfl⟩ : syracuseStep 2362963 = 3544445) B3544445
theorem B3150617 : Blo 2099435 3150617 := bstep (se 2 (by rfl) ⟨1181481, by rfl⟩ : syracuseStep 3150617 = 2362963) B2362963
theorem B2100411 : Blo 2099435 2100411 := bstep (se 1 (by rfl) ⟨1575308, by rfl⟩ : syracuseStep 2100411 = 3150617) B3150617
theorem B7570037 : Blo 2099435 7570037 := bbase (se 5 (by rfl) ⟨354845, by rfl⟩ : syracuseStep 7570037 = 709691) (by norm_num)
theorem B5046691 : Blo 2099435 5046691 := bstep (se 1 (by rfl) ⟨3785018, by rfl⟩ : syracuseStep 5046691 = 7570037) B7570037
theorem B6728921 : Blo 2099435 6728921 := bstep (se 2 (by rfl) ⟨2523345, by rfl⟩ : syracuseStep 6728921 = 5046691) B5046691
theorem B4485947 : Blo 2099435 4485947 := bstep (se 1 (by rfl) ⟨3364460, by rfl⟩ : syracuseStep 4485947 = 6728921) B6728921
theorem B11962525 : Blo 2099435 11962525 := bstep (se 3 (by rfl) ⟨2242973, by rfl⟩ : syracuseStep 11962525 = 4485947) B4485947
theorem B15950033 : Blo 2099435 15950033 := bstep (se 2 (by rfl) ⟨5981262, by rfl⟩ : syracuseStep 15950033 = 11962525) B11962525
theorem B10633355 : Blo 2099435 10633355 := bstep (se 1 (by rfl) ⟨7975016, by rfl⟩ : syracuseStep 10633355 = 15950033) B15950033
theorem B7088903 : Blo 2099435 7088903 := bstep (se 1 (by rfl) ⟨5316677, by rfl⟩ : syracuseStep 7088903 = 10633355) B10633355
theorem B4725935 : Blo 2099435 4725935 := bstep (se 1 (by rfl) ⟨3544451, by rfl⟩ : syracuseStep 4725935 = 7088903) B7088903
theorem B3150623 : Blo 2099435 3150623 := bstep (se 1 (by rfl) ⟨2362967, by rfl⟩ : syracuseStep 3150623 = 4725935) B4725935
theorem B2100415 : Blo 2099435 2100415 := bstep (se 1 (by rfl) ⟨1575311, by rfl⟩ : syracuseStep 2100415 = 3150623) B3150623
theorem B3150629 : Blo 2099435 3150629 := bbase (se 4 (by rfl) ⟨295371, by rfl⟩ : syracuseStep 3150629 = 590743) (by norm_num)
theorem B2100419 : Blo 2099435 2100419 := bstep (se 1 (by rfl) ⟨1575314, by rfl⟩ : syracuseStep 2100419 = 3150629) B3150629
theorem B2658349 : Blo 2099435 2658349 := bbase (se 3 (by rfl) ⟨498440, by rfl⟩ : syracuseStep 2658349 = 996881) (by norm_num)
theorem B3544465 : Blo 2099435 3544465 := bstep (se 2 (by rfl) ⟨1329174, by rfl⟩ : syracuseStep 3544465 = 2658349) B2658349
theorem B4725953 : Blo 2099435 4725953 := bstep (se 2 (by rfl) ⟨1772232, by rfl⟩ : syracuseStep 4725953 = 3544465) B3544465
theorem B3150635 : Blo 2099435 3150635 := bstep (se 1 (by rfl) ⟨2362976, by rfl⟩ : syracuseStep 3150635 = 4725953) B4725953
theorem B2100423 : Blo 2099435 2100423 := bstep (se 1 (by rfl) ⟨1575317, by rfl⟩ : syracuseStep 2100423 = 3150635) B3150635
theorem B2362981 : Blo 2099435 2362981 := bbase (se 4 (by rfl) ⟨221529, by rfl⟩ : syracuseStep 2362981 = 443059) (by norm_num)
theorem B3150641 : Blo 2099435 3150641 := bstep (se 2 (by rfl) ⟨1181490, by rfl⟩ : syracuseStep 3150641 = 2362981) B2362981
theorem B2100427 : Blo 2099435 2100427 := bstep (se 1 (by rfl) ⟨1575320, by rfl⟩ : syracuseStep 2100427 = 3150641) B3150641
theorem B5677573 : Blo 2099435 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B7570097 : Blo 2099435 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B5046731 : Blo 2099435 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B3364487 : Blo 2099435 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2242991 : Blo 2099435 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B5981309 : Blo 2099435 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B3987539 : Blo 2099435 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B2658359 : Blo 2099435 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B7088957 : Blo 2099435 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B4725971 : Blo 2099435 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B3150647 : Blo 2099435 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B2100431 : Blo 2099435 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B3150653 : Blo 2099435 3150653 := bbase (se 3 (by rfl) ⟨590747, by rfl⟩ : syracuseStep 3150653 = 1181495) (by norm_num)
theorem B2100435 : Blo 2099435 2100435 := bstep (se 1 (by rfl) ⟨1575326, by rfl⟩ : syracuseStep 2100435 = 3150653) B3150653
theorem B4725989 : Blo 2099435 4725989 := bbase (se 4 (by rfl) ⟨443061, by rfl⟩ : syracuseStep 4725989 = 886123) (by norm_num)
theorem B3150659 : Blo 2099435 3150659 := bstep (se 1 (by rfl) ⟨2362994, by rfl⟩ : syracuseStep 3150659 = 4725989) B4725989
theorem B2100439 : Blo 2099435 2100439 := bstep (se 1 (by rfl) ⟨1575329, by rfl⟩ : syracuseStep 2100439 = 3150659) B3150659
theorem B5316749 : Blo 2099435 5316749 := bbase (se 3 (by rfl) ⟨996890, by rfl⟩ : syracuseStep 5316749 = 1993781) (by norm_num)
theorem B3544499 : Blo 2099435 3544499 := bstep (se 1 (by rfl) ⟨2658374, by rfl⟩ : syracuseStep 3544499 = 5316749) B5316749
theorem B2362999 : Blo 2099435 2362999 := bstep (se 1 (by rfl) ⟨1772249, by rfl⟩ : syracuseStep 2362999 = 3544499) B3544499
theorem B3150665 : Blo 2099435 3150665 := bstep (se 2 (by rfl) ⟨1181499, by rfl⟩ : syracuseStep 3150665 = 2362999) B2362999
theorem B2100443 : Blo 2099435 2100443 := bstep (se 1 (by rfl) ⟨1575332, by rfl⟩ : syracuseStep 2100443 = 3150665) B3150665
theorem B2990677 : Blo 2099435 2990677 := bbase (se 8 (by rfl) ⟨17523, by rfl⟩ : syracuseStep 2990677 = 35047) (by norm_num)
theorem B3987569 : Blo 2099435 3987569 := bstep (se 2 (by rfl) ⟨1495338, by rfl⟩ : syracuseStep 3987569 = 2990677) B2990677
theorem B10633517 : Blo 2099435 10633517 := bstep (se 3 (by rfl) ⟨1993784, by rfl⟩ : syracuseStep 10633517 = 3987569) B3987569
theorem B7089011 : Blo 2099435 7089011 := bstep (se 1 (by rfl) ⟨5316758, by rfl⟩ : syracuseStep 7089011 = 10633517) B10633517
theorem B4726007 : Blo 2099435 4726007 := bstep (se 1 (by rfl) ⟨3544505, by rfl⟩ : syracuseStep 4726007 = 7089011) B7089011
theorem B3150671 : Blo 2099435 3150671 := bstep (se 1 (by rfl) ⟨2363003, by rfl⟩ : syracuseStep 3150671 = 4726007) B4726007
theorem B2100447 : Blo 2099435 2100447 := bstep (se 1 (by rfl) ⟨1575335, by rfl⟩ : syracuseStep 2100447 = 3150671) B3150671
theorem B3150677 : Blo 2099435 3150677 := bbase (se 9 (by rfl) ⟨9230, by rfl⟩ : syracuseStep 3150677 = 18461) (by norm_num)
theorem B2100451 : Blo 2099435 2100451 := bstep (se 1 (by rfl) ⟨1575338, by rfl⟩ : syracuseStep 2100451 = 3150677) B3150677
theorem B3364525 : Blo 2099435 3364525 := bbase (se 3 (by rfl) ⟨630848, by rfl⟩ : syracuseStep 3364525 = 1261697) (by norm_num)
theorem B4486033 : Blo 2099435 4486033 := bstep (se 2 (by rfl) ⟨1682262, by rfl⟩ : syracuseStep 4486033 = 3364525) B3364525
theorem B5981377 : Blo 2099435 5981377 := bstep (se 2 (by rfl) ⟨2243016, by rfl⟩ : syracuseStep 5981377 = 4486033) B4486033
theorem B7975169 : Blo 2099435 7975169 := bstep (se 2 (by rfl) ⟨2990688, by rfl⟩ : syracuseStep 7975169 = 5981377) B5981377
theorem B5316779 : Blo 2099435 5316779 := bstep (se 1 (by rfl) ⟨3987584, by rfl⟩ : syracuseStep 5316779 = 7975169) B7975169
theorem B3544519 : Blo 2099435 3544519 := bstep (se 1 (by rfl) ⟨2658389, by rfl⟩ : syracuseStep 3544519 = 5316779) B5316779
theorem B4726025 : Blo 2099435 4726025 := bstep (se 2 (by rfl) ⟨1772259, by rfl⟩ : syracuseStep 4726025 = 3544519) B3544519
theorem B3150683 : Blo 2099435 3150683 := bstep (se 1 (by rfl) ⟨2363012, by rfl⟩ : syracuseStep 3150683 = 4726025) B4726025
theorem B2100455 : Blo 2099435 2100455 := bstep (se 1 (by rfl) ⟨1575341, by rfl⟩ : syracuseStep 2100455 = 3150683) B3150683
theorem B2363017 : Blo 2099435 2363017 := bbase (se 2 (by rfl) ⟨886131, by rfl⟩ : syracuseStep 2363017 = 1772263) (by norm_num)
theorem B3150689 : Blo 2099435 3150689 := bstep (se 2 (by rfl) ⟨1181508, by rfl⟩ : syracuseStep 3150689 = 2363017) B2363017
theorem B2100459 : Blo 2099435 2100459 := bstep (se 1 (by rfl) ⟨1575344, by rfl⟩ : syracuseStep 2100459 = 3150689) B3150689
theorem B6387365 : Blo 2099435 6387365 := bbase (se 4 (by rfl) ⟨598815, by rfl⟩ : syracuseStep 6387365 = 1197631) (by norm_num)
theorem B4258243 : Blo 2099435 4258243 := bstep (se 1 (by rfl) ⟨3193682, by rfl⟩ : syracuseStep 4258243 = 6387365) B6387365
theorem B5677657 : Blo 2099435 5677657 := bstep (se 2 (by rfl) ⟨2129121, by rfl⟩ : syracuseStep 5677657 = 4258243) B4258243
theorem B30280837 : Blo 2099435 30280837 := bstep (se 4 (by rfl) ⟨2838828, by rfl⟩ : syracuseStep 30280837 = 5677657) B5677657
theorem B40374449 : Blo 2099435 40374449 := bstep (se 2 (by rfl) ⟨15140418, by rfl⟩ : syracuseStep 40374449 = 30280837) B30280837
theorem B26916299 : Blo 2099435 26916299 := bstep (se 1 (by rfl) ⟨20187224, by rfl⟩ : syracuseStep 26916299 = 40374449) B40374449
theorem B17944199 : Blo 2099435 17944199 := bstep (se 1 (by rfl) ⟨13458149, by rfl⟩ : syracuseStep 17944199 = 26916299) B26916299
theorem B11962799 : Blo 2099435 11962799 := bstep (se 1 (by rfl) ⟨8972099, by rfl⟩ : syracuseStep 11962799 = 17944199) B17944199
theorem B7975199 : Blo 2099435 7975199 := bstep (se 1 (by rfl) ⟨5981399, by rfl⟩ : syracuseStep 7975199 = 11962799) B11962799
theorem B5316799 : Blo 2099435 5316799 := bstep (se 1 (by rfl) ⟨3987599, by rfl⟩ : syracuseStep 5316799 = 7975199) B7975199
theorem B7089065 : Blo 2099435 7089065 := bstep (se 2 (by rfl) ⟨2658399, by rfl⟩ : syracuseStep 7089065 = 5316799) B5316799
theorem B4726043 : Blo 2099435 4726043 := bstep (se 1 (by rfl) ⟨3544532, by rfl⟩ : syracuseStep 4726043 = 7089065) B7089065
theorem B3150695 : Blo 2099435 3150695 := bstep (se 1 (by rfl) ⟨2363021, by rfl⟩ : syracuseStep 3150695 = 4726043) B4726043
theorem B2100463 : Blo 2099435 2100463 := bstep (se 1 (by rfl) ⟨1575347, by rfl⟩ : syracuseStep 2100463 = 3150695) B3150695
theorem B3150701 : Blo 2099435 3150701 := bbase (se 3 (by rfl) ⟨590756, by rfl⟩ : syracuseStep 3150701 = 1181513) (by norm_num)
theorem B2100467 : Blo 2099435 2100467 := bstep (se 1 (by rfl) ⟨1575350, by rfl⟩ : syracuseStep 2100467 = 3150701) B3150701
theorem B4726061 : Blo 2099435 4726061 := bbase (se 3 (by rfl) ⟨886136, by rfl⟩ : syracuseStep 4726061 = 1772273) (by norm_num)
theorem B3150707 : Blo 2099435 3150707 := bstep (se 1 (by rfl) ⟨2363030, by rfl⟩ : syracuseStep 3150707 = 4726061) B4726061
theorem B2100471 : Blo 2099435 2100471 := bstep (se 1 (by rfl) ⟨1575353, by rfl⟩ : syracuseStep 2100471 = 3150707) B3150707
theorem B7185829 : Blo 2099435 7185829 := bbase (se 4 (by rfl) ⟨673671, by rfl⟩ : syracuseStep 7185829 = 1347343) (by norm_num)
theorem B9581105 : Blo 2099435 9581105 := bstep (se 2 (by rfl) ⟨3592914, by rfl⟩ : syracuseStep 9581105 = 7185829) B7185829
theorem B25549613 : Blo 2099435 25549613 := bstep (se 3 (by rfl) ⟨4790552, by rfl⟩ : syracuseStep 25549613 = 9581105) B9581105
theorem B17033075 : Blo 2099435 17033075 := bstep (se 1 (by rfl) ⟨12774806, by rfl⟩ : syracuseStep 17033075 = 25549613) B25549613
theorem B11355383 : Blo 2099435 11355383 := bstep (se 1 (by rfl) ⟨8516537, by rfl⟩ : syracuseStep 11355383 = 17033075) B17033075
theorem B7570255 : Blo 2099435 7570255 := bstep (se 1 (by rfl) ⟨5677691, by rfl⟩ : syracuseStep 7570255 = 11355383) B11355383
theorem B10093673 : Blo 2099435 10093673 := bstep (se 2 (by rfl) ⟨3785127, by rfl⟩ : syracuseStep 10093673 = 7570255) B7570255
theorem B6729115 : Blo 2099435 6729115 := bstep (se 1 (by rfl) ⟨5046836, by rfl⟩ : syracuseStep 6729115 = 10093673) B10093673
theorem B8972153 : Blo 2099435 8972153 := bstep (se 2 (by rfl) ⟨3364557, by rfl⟩ : syracuseStep 8972153 = 6729115) B6729115
theorem B5981435 : Blo 2099435 5981435 := bstep (se 1 (by rfl) ⟨4486076, by rfl⟩ : syracuseStep 5981435 = 8972153) B8972153
theorem B3987623 : Blo 2099435 3987623 := bstep (se 1 (by rfl) ⟨2990717, by rfl⟩ : syracuseStep 3987623 = 5981435) B5981435
theorem B2658415 : Blo 2099435 2658415 := bstep (se 1 (by rfl) ⟨1993811, by rfl⟩ : syracuseStep 2658415 = 3987623) B3987623
theorem B3544553 : Blo 2099435 3544553 := bstep (se 2 (by rfl) ⟨1329207, by rfl⟩ : syracuseStep 3544553 = 2658415) B2658415
theorem B2363035 : Blo 2099435 2363035 := bstep (se 1 (by rfl) ⟨1772276, by rfl⟩ : syracuseStep 2363035 = 3544553) B3544553
theorem B3150713 : Blo 2099435 3150713 := bstep (se 2 (by rfl) ⟨1181517, by rfl⟩ : syracuseStep 3150713 = 2363035) B2363035
theorem B2100475 : Blo 2099435 2100475 := bstep (se 1 (by rfl) ⟨1575356, by rfl⟩ : syracuseStep 2100475 = 3150713) B3150713
theorem B15140533 : Blo 2099435 15140533 := bbase (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) (by norm_num)
theorem B20187377 : Blo 2099435 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B13458251 : Blo 2099435 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B35888669 : Blo 2099435 35888669 := bstep (se 3 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 35888669 = 13458251) B13458251
theorem B23925779 : Blo 2099435 23925779 := bstep (se 1 (by rfl) ⟨17944334, by rfl⟩ : syracuseStep 23925779 = 35888669) B35888669
theorem B15950519 : Blo 2099435 15950519 := bstep (se 1 (by rfl) ⟨11962889, by rfl⟩ : syracuseStep 15950519 = 23925779) B23925779
theorem B10633679 : Blo 2099435 10633679 := bstep (se 1 (by rfl) ⟨7975259, by rfl⟩ : syracuseStep 10633679 = 15950519) B15950519
theorem B7089119 : Blo 2099435 7089119 := bstep (se 1 (by rfl) ⟨5316839, by rfl⟩ : syracuseStep 7089119 = 10633679) B10633679
theorem B4726079 : Blo 2099435 4726079 := bstep (se 1 (by rfl) ⟨3544559, by rfl⟩ : syracuseStep 4726079 = 7089119) B7089119
theorem B3150719 : Blo 2099435 3150719 := bstep (se 1 (by rfl) ⟨2363039, by rfl⟩ : syracuseStep 3150719 = 4726079) B4726079
theorem B2100479 : Blo 2099435 2100479 := bstep (se 1 (by rfl) ⟨1575359, by rfl⟩ : syracuseStep 2100479 = 3150719) B3150719
theorem B3150725 : Blo 2099435 3150725 := bbase (se 4 (by rfl) ⟨295380, by rfl⟩ : syracuseStep 3150725 = 590761) (by norm_num)
theorem B2100483 : Blo 2099435 2100483 := bstep (se 1 (by rfl) ⟨1575362, by rfl⟩ : syracuseStep 2100483 = 3150725) B3150725
theorem B3544573 : Blo 2099435 3544573 := bbase (se 3 (by rfl) ⟨664607, by rfl⟩ : syracuseStep 3544573 = 1329215) (by norm_num)
theorem B4726097 : Blo 2099435 4726097 := bstep (se 2 (by rfl) ⟨1772286, by rfl⟩ : syracuseStep 4726097 = 3544573) B3544573
theorem B3150731 : Blo 2099435 3150731 := bstep (se 1 (by rfl) ⟨2363048, by rfl⟩ : syracuseStep 3150731 = 4726097) B4726097
theorem B2100487 : Blo 2099435 2100487 := bstep (se 1 (by rfl) ⟨1575365, by rfl⟩ : syracuseStep 2100487 = 3150731) B3150731
theorem B2363053 : Blo 2099435 2363053 := bbase (se 3 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 2363053 = 886145) (by norm_num)
theorem B3150737 : Blo 2099435 3150737 := bstep (se 2 (by rfl) ⟨1181526, by rfl⟩ : syracuseStep 3150737 = 2363053) B2363053
theorem B2100491 : Blo 2099435 2100491 := bstep (se 1 (by rfl) ⟨1575368, by rfl⟩ : syracuseStep 2100491 = 3150737) B3150737
theorem B7089173 : Blo 2099435 7089173 := bbase (se 6 (by rfl) ⟨166152, by rfl⟩ : syracuseStep 7089173 = 332305) (by norm_num)
theorem B4726115 : Blo 2099435 4726115 := bstep (se 1 (by rfl) ⟨3544586, by rfl⟩ : syracuseStep 4726115 = 7089173) B7089173
theorem B3150743 : Blo 2099435 3150743 := bstep (se 1 (by rfl) ⟨2363057, by rfl⟩ : syracuseStep 3150743 = 4726115) B4726115
theorem B2100495 : Blo 2099435 2100495 := bstep (se 1 (by rfl) ⟨1575371, by rfl⟩ : syracuseStep 2100495 = 3150743) B3150743
theorem B3150749 : Blo 2099435 3150749 := bbase (se 3 (by rfl) ⟨590765, by rfl⟩ : syracuseStep 3150749 = 1181531) (by norm_num)
theorem B2100499 : Blo 2099435 2100499 := bstep (se 1 (by rfl) ⟨1575374, by rfl⟩ : syracuseStep 2100499 = 3150749) B3150749
theorem B4726133 : Blo 2099435 4726133 := bbase (se 5 (by rfl) ⟨221537, by rfl⟩ : syracuseStep 4726133 = 443075) (by norm_num)
theorem B3150755 : Blo 2099435 3150755 := bstep (se 1 (by rfl) ⟨2363066, by rfl⟩ : syracuseStep 3150755 = 4726133) B4726133
theorem B2100503 : Blo 2099435 2100503 := bstep (se 1 (by rfl) ⟨1575377, by rfl⟩ : syracuseStep 2100503 = 3150755) B3150755
theorem B4258333 : Blo 2099435 4258333 := bbase (se 3 (by rfl) ⟨798437, by rfl⟩ : syracuseStep 4258333 = 1596875) (by norm_num)
theorem B5677777 : Blo 2099435 5677777 := bstep (se 2 (by rfl) ⟨2129166, by rfl⟩ : syracuseStep 5677777 = 4258333) B4258333
theorem B7570369 : Blo 2099435 7570369 := bstep (se 2 (by rfl) ⟨2838888, by rfl⟩ : syracuseStep 7570369 = 5677777) B5677777
theorem B10093825 : Blo 2099435 10093825 := bstep (se 2 (by rfl) ⟨3785184, by rfl⟩ : syracuseStep 10093825 = 7570369) B7570369
theorem B13458433 : Blo 2099435 13458433 := bstep (se 2 (by rfl) ⟨5046912, by rfl⟩ : syracuseStep 13458433 = 10093825) B10093825
theorem B17944577 : Blo 2099435 17944577 := bstep (se 2 (by rfl) ⟨6729216, by rfl⟩ : syracuseStep 17944577 = 13458433) B13458433
theorem B11963051 : Blo 2099435 11963051 := bstep (se 1 (by rfl) ⟨8972288, by rfl⟩ : syracuseStep 11963051 = 17944577) B17944577
theorem B7975367 : Blo 2099435 7975367 := bstep (se 1 (by rfl) ⟨5981525, by rfl⟩ : syracuseStep 7975367 = 11963051) B11963051
theorem B5316911 : Blo 2099435 5316911 := bstep (se 1 (by rfl) ⟨3987683, by rfl⟩ : syracuseStep 5316911 = 7975367) B7975367
theorem B3544607 : Blo 2099435 3544607 := bstep (se 1 (by rfl) ⟨2658455, by rfl⟩ : syracuseStep 3544607 = 5316911) B5316911
theorem B2363071 : Blo 2099435 2363071 := bstep (se 1 (by rfl) ⟨1772303, by rfl⟩ : syracuseStep 2363071 = 3544607) B3544607
theorem B3150761 : Blo 2099435 3150761 := bstep (se 2 (by rfl) ⟨1181535, by rfl⟩ : syracuseStep 3150761 = 2363071) B2363071
theorem B2100507 : Blo 2099435 2100507 := bstep (se 1 (by rfl) ⟨1575380, by rfl⟩ : syracuseStep 2100507 = 3150761) B3150761
theorem B7975381 : Blo 2099435 7975381 := bbase (se 7 (by rfl) ⟨93461, by rfl⟩ : syracuseStep 7975381 = 186923) (by norm_num)
theorem B10633841 : Blo 2099435 10633841 := bstep (se 2 (by rfl) ⟨3987690, by rfl⟩ : syracuseStep 10633841 = 7975381) B7975381
theorem B7089227 : Blo 2099435 7089227 := bstep (se 1 (by rfl) ⟨5316920, by rfl⟩ : syracuseStep 7089227 = 10633841) B10633841
theorem B4726151 : Blo 2099435 4726151 := bstep (se 1 (by rfl) ⟨3544613, by rfl⟩ : syracuseStep 4726151 = 7089227) B7089227
theorem B3150767 : Blo 2099435 3150767 := bstep (se 1 (by rfl) ⟨2363075, by rfl⟩ : syracuseStep 3150767 = 4726151) B4726151
theorem B2100511 : Blo 2099435 2100511 := bstep (se 1 (by rfl) ⟨1575383, by rfl⟩ : syracuseStep 2100511 = 3150767) B3150767
theorem B3150773 : Blo 2099435 3150773 := bbase (se 5 (by rfl) ⟨147692, by rfl⟩ : syracuseStep 3150773 = 295385) (by norm_num)
theorem B2100515 : Blo 2099435 2100515 := bstep (se 1 (by rfl) ⟨1575386, by rfl⟩ : syracuseStep 2100515 = 3150773) B3150773
theorem B5316941 : Blo 2099435 5316941 := bbase (se 3 (by rfl) ⟨996926, by rfl⟩ : syracuseStep 5316941 = 1993853) (by norm_num)
theorem B3544627 : Blo 2099435 3544627 := bstep (se 1 (by rfl) ⟨2658470, by rfl⟩ : syracuseStep 3544627 = 5316941) B5316941
theorem B4726169 : Blo 2099435 4726169 := bstep (se 2 (by rfl) ⟨1772313, by rfl⟩ : syracuseStep 4726169 = 3544627) B3544627
theorem B3150779 : Blo 2099435 3150779 := bstep (se 1 (by rfl) ⟨2363084, by rfl⟩ : syracuseStep 3150779 = 4726169) B4726169
theorem B2100519 : Blo 2099435 2100519 := bstep (se 1 (by rfl) ⟨1575389, by rfl⟩ : syracuseStep 2100519 = 3150779) B3150779
theorem B2363089 : Blo 2099435 2363089 := bbase (se 2 (by rfl) ⟨886158, by rfl⟩ : syracuseStep 2363089 = 1772317) (by norm_num)
theorem B3150785 : Blo 2099435 3150785 := bstep (se 2 (by rfl) ⟨1181544, by rfl⟩ : syracuseStep 3150785 = 2363089) B2363089
theorem B2100523 : Blo 2099435 2100523 := bstep (se 1 (by rfl) ⟨1575392, by rfl⟩ : syracuseStep 2100523 = 3150785) B3150785
theorem B3785221 : Blo 2099435 3785221 := bbase (se 4 (by rfl) ⟨354864, by rfl⟩ : syracuseStep 3785221 = 709729) (by norm_num)
theorem B5046961 : Blo 2099435 5046961 := bstep (se 2 (by rfl) ⟨1892610, by rfl⟩ : syracuseStep 5046961 = 3785221) B3785221
theorem B6729281 : Blo 2099435 6729281 := bstep (se 2 (by rfl) ⟨2523480, by rfl⟩ : syracuseStep 6729281 = 5046961) B5046961
theorem B4486187 : Blo 2099435 4486187 := bstep (se 1 (by rfl) ⟨3364640, by rfl⟩ : syracuseStep 4486187 = 6729281) B6729281
theorem B2990791 : Blo 2099435 2990791 := bstep (se 1 (by rfl) ⟨2243093, by rfl⟩ : syracuseStep 2990791 = 4486187) B4486187
theorem B3987721 : Blo 2099435 3987721 := bstep (se 2 (by rfl) ⟨1495395, by rfl⟩ : syracuseStep 3987721 = 2990791) B2990791
theorem B5316961 : Blo 2099435 5316961 := bstep (se 2 (by rfl) ⟨1993860, by rfl⟩ : syracuseStep 5316961 = 3987721) B3987721
theorem B7089281 : Blo 2099435 7089281 := bstep (se 2 (by rfl) ⟨2658480, by rfl⟩ : syracuseStep 7089281 = 5316961) B5316961
theorem B4726187 : Blo 2099435 4726187 := bstep (se 1 (by rfl) ⟨3544640, by rfl⟩ : syracuseStep 4726187 = 7089281) B7089281
theorem B3150791 : Blo 2099435 3150791 := bstep (se 1 (by rfl) ⟨2363093, by rfl⟩ : syracuseStep 3150791 = 4726187) B4726187
theorem B2100527 : Blo 2099435 2100527 := bstep (se 1 (by rfl) ⟨1575395, by rfl⟩ : syracuseStep 2100527 = 3150791) B3150791
theorem B3150797 : Blo 2099435 3150797 := bbase (se 3 (by rfl) ⟨590774, by rfl⟩ : syracuseStep 3150797 = 1181549) (by norm_num)
theorem B2100531 : Blo 2099435 2100531 := bstep (se 1 (by rfl) ⟨1575398, by rfl⟩ : syracuseStep 2100531 = 3150797) B3150797
theorem B4726205 : Blo 2099435 4726205 := bbase (se 3 (by rfl) ⟨886163, by rfl⟩ : syracuseStep 4726205 = 1772327) (by norm_num)
theorem B3150803 : Blo 2099435 3150803 := bstep (se 1 (by rfl) ⟨2363102, by rfl⟩ : syracuseStep 3150803 = 4726205) B4726205
theorem B2100535 : Blo 2099435 2100535 := bstep (se 1 (by rfl) ⟨1575401, by rfl⟩ : syracuseStep 2100535 = 3150803) B3150803
theorem B3544661 : Blo 2099435 3544661 := bbase (se 8 (by rfl) ⟨20769, by rfl⟩ : syracuseStep 3544661 = 41539) (by norm_num)
theorem B2363107 : Blo 2099435 2363107 := bstep (se 1 (by rfl) ⟨1772330, by rfl⟩ : syracuseStep 2363107 = 3544661) B3544661
theorem B3150809 : Blo 2099435 3150809 := bstep (se 2 (by rfl) ⟨1181553, by rfl⟩ : syracuseStep 3150809 = 2363107) B2363107
theorem B2100539 : Blo 2099435 2100539 := bstep (se 1 (by rfl) ⟨1575404, by rfl⟩ : syracuseStep 2100539 = 3150809) B3150809
theorem B3193805 : Blo 2099435 3193805 := bbase (se 3 (by rfl) ⟨598838, by rfl⟩ : syracuseStep 3193805 = 1197677) (by norm_num)
theorem B2129203 : Blo 2099435 2129203 := bstep (se 1 (by rfl) ⟨1596902, by rfl⟩ : syracuseStep 2129203 = 3193805) B3193805
theorem B2838937 : Blo 2099435 2838937 := bstep (se 2 (by rfl) ⟨1064601, by rfl⟩ : syracuseStep 2838937 = 2129203) B2129203
theorem B3785249 : Blo 2099435 3785249 := bstep (se 2 (by rfl) ⟨1419468, by rfl⟩ : syracuseStep 3785249 = 2838937) B2838937
theorem B10093997 : Blo 2099435 10093997 := bstep (se 3 (by rfl) ⟨1892624, by rfl⟩ : syracuseStep 10093997 = 3785249) B3785249
theorem B6729331 : Blo 2099435 6729331 := bstep (se 1 (by rfl) ⟨5046998, by rfl⟩ : syracuseStep 6729331 = 10093997) B10093997
theorem B8972441 : Blo 2099435 8972441 := bstep (se 2 (by rfl) ⟨3364665, by rfl⟩ : syracuseStep 8972441 = 6729331) B6729331
theorem B5981627 : Blo 2099435 5981627 := bstep (se 1 (by rfl) ⟨4486220, by rfl⟩ : syracuseStep 5981627 = 8972441) B8972441
theorem B15951005 : Blo 2099435 15951005 := bstep (se 3 (by rfl) ⟨2990813, by rfl⟩ : syracuseStep 15951005 = 5981627) B5981627
theorem B10634003 : Blo 2099435 10634003 := bstep (se 1 (by rfl) ⟨7975502, by rfl⟩ : syracuseStep 10634003 = 15951005) B15951005
theorem B7089335 : Blo 2099435 7089335 := bstep (se 1 (by rfl) ⟨5317001, by rfl⟩ : syracuseStep 7089335 = 10634003) B10634003
theorem B4726223 : Blo 2099435 4726223 := bstep (se 1 (by rfl) ⟨3544667, by rfl⟩ : syracuseStep 4726223 = 7089335) B7089335
theorem B3150815 : Blo 2099435 3150815 := bstep (se 1 (by rfl) ⟨2363111, by rfl⟩ : syracuseStep 3150815 = 4726223) B4726223
theorem B2100543 : Blo 2099435 2100543 := bstep (se 1 (by rfl) ⟨1575407, by rfl⟩ : syracuseStep 2100543 = 3150815) B3150815
theorem B3150821 : Blo 2099435 3150821 := bbase (se 4 (by rfl) ⟨295389, by rfl⟩ : syracuseStep 3150821 = 590779) (by norm_num)
theorem B2100547 : Blo 2099435 2100547 := bstep (se 1 (by rfl) ⟨1575410, by rfl⟩ : syracuseStep 2100547 = 3150821) B3150821
theorem B3593045 : Blo 2099435 3593045 := bbase (se 9 (by rfl) ⟨10526, by rfl⟩ : syracuseStep 3593045 = 21053) (by norm_num)
theorem B9581453 : Blo 2099435 9581453 := bstep (se 3 (by rfl) ⟨1796522, by rfl⟩ : syracuseStep 9581453 = 3593045) B3593045
theorem B6387635 : Blo 2099435 6387635 := bstep (se 1 (by rfl) ⟨4790726, by rfl⟩ : syracuseStep 6387635 = 9581453) B9581453
theorem B4258423 : Blo 2099435 4258423 := bstep (se 1 (by rfl) ⟨3193817, by rfl⟩ : syracuseStep 4258423 = 6387635) B6387635
theorem B5677897 : Blo 2099435 5677897 := bstep (se 2 (by rfl) ⟨2129211, by rfl⟩ : syracuseStep 5677897 = 4258423) B4258423
theorem B7570529 : Blo 2099435 7570529 := bstep (se 2 (by rfl) ⟨2838948, by rfl⟩ : syracuseStep 7570529 = 5677897) B5677897
theorem B5047019 : Blo 2099435 5047019 := bstep (se 1 (by rfl) ⟨3785264, by rfl⟩ : syracuseStep 5047019 = 7570529) B7570529
theorem B3364679 : Blo 2099435 3364679 := bstep (se 1 (by rfl) ⟨2523509, by rfl⟩ : syracuseStep 3364679 = 5047019) B5047019
theorem B8972477 : Blo 2099435 8972477 := bstep (se 3 (by rfl) ⟨1682339, by rfl⟩ : syracuseStep 8972477 = 3364679) B3364679
theorem B5981651 : Blo 2099435 5981651 := bstep (se 1 (by rfl) ⟨4486238, by rfl⟩ : syracuseStep 5981651 = 8972477) B8972477
theorem B3987767 : Blo 2099435 3987767 := bstep (se 1 (by rfl) ⟨2990825, by rfl⟩ : syracuseStep 3987767 = 5981651) B5981651
theorem B2658511 : Blo 2099435 2658511 := bstep (se 1 (by rfl) ⟨1993883, by rfl⟩ : syracuseStep 2658511 = 3987767) B3987767
theorem B3544681 : Blo 2099435 3544681 := bstep (se 2 (by rfl) ⟨1329255, by rfl⟩ : syracuseStep 3544681 = 2658511) B2658511
theorem B4726241 : Blo 2099435 4726241 := bstep (se 2 (by rfl) ⟨1772340, by rfl⟩ : syracuseStep 4726241 = 3544681) B3544681
theorem B3150827 : Blo 2099435 3150827 := bstep (se 1 (by rfl) ⟨2363120, by rfl⟩ : syracuseStep 3150827 = 4726241) B4726241
theorem B2100551 : Blo 2099435 2100551 := bstep (se 1 (by rfl) ⟨1575413, by rfl⟩ : syracuseStep 2100551 = 3150827) B3150827
theorem B2363125 : Blo 2099435 2363125 := bbase (se 5 (by rfl) ⟨110771, by rfl⟩ : syracuseStep 2363125 = 221543) (by norm_num)
theorem B3150833 : Blo 2099435 3150833 := bstep (se 2 (by rfl) ⟨1181562, by rfl⟩ : syracuseStep 3150833 = 2363125) B2363125
theorem B2100555 : Blo 2099435 2100555 := bstep (se 1 (by rfl) ⟨1575416, by rfl⟩ : syracuseStep 2100555 = 3150833) B3150833
theorem B2658521 : Blo 2099435 2658521 := bbase (se 2 (by rfl) ⟨996945, by rfl⟩ : syracuseStep 2658521 = 1993891) (by norm_num)
theorem B7089389 : Blo 2099435 7089389 := bstep (se 3 (by rfl) ⟨1329260, by rfl⟩ : syracuseStep 7089389 = 2658521) B2658521
theorem B4726259 : Blo 2099435 4726259 := bstep (se 1 (by rfl) ⟨3544694, by rfl⟩ : syracuseStep 4726259 = 7089389) B7089389
theorem B3150839 : Blo 2099435 3150839 := bstep (se 1 (by rfl) ⟨2363129, by rfl⟩ : syracuseStep 3150839 = 4726259) B4726259
theorem B2100559 : Blo 2099435 2100559 := bstep (se 1 (by rfl) ⟨1575419, by rfl⟩ : syracuseStep 2100559 = 3150839) B3150839
theorem B3150845 : Blo 2099435 3150845 := bbase (se 3 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 3150845 = 1181567) (by norm_num)
theorem B2100563 : Blo 2099435 2100563 := bstep (se 1 (by rfl) ⟨1575422, by rfl⟩ : syracuseStep 2100563 = 3150845) B3150845
theorem B4726277 : Blo 2099435 4726277 := bbase (se 4 (by rfl) ⟨443088, by rfl⟩ : syracuseStep 4726277 = 886177) (by norm_num)
theorem B3150851 : Blo 2099435 3150851 := bstep (se 1 (by rfl) ⟨2363138, by rfl⟩ : syracuseStep 3150851 = 4726277) B4726277
theorem B2100567 : Blo 2099435 2100567 := bstep (se 1 (by rfl) ⟨1575425, by rfl⟩ : syracuseStep 2100567 = 3150851) B3150851
theorem B3987805 : Blo 2099435 3987805 := bbase (se 3 (by rfl) ⟨747713, by rfl⟩ : syracuseStep 3987805 = 1495427) (by norm_num)
theorem B5317073 : Blo 2099435 5317073 := bstep (se 2 (by rfl) ⟨1993902, by rfl⟩ : syracuseStep 5317073 = 3987805) B3987805
theorem B3544715 : Blo 2099435 3544715 := bstep (se 1 (by rfl) ⟨2658536, by rfl⟩ : syracuseStep 3544715 = 5317073) B5317073
theorem B2363143 : Blo 2099435 2363143 := bstep (se 1 (by rfl) ⟨1772357, by rfl⟩ : syracuseStep 2363143 = 3544715) B3544715
theorem B3150857 : Blo 2099435 3150857 := bstep (se 2 (by rfl) ⟨1181571, by rfl⟩ : syracuseStep 3150857 = 2363143) B2363143
theorem B2100571 : Blo 2099435 2100571 := bstep (se 1 (by rfl) ⟨1575428, by rfl⟩ : syracuseStep 2100571 = 3150857) B3150857
theorem B10634165 : Blo 2099435 10634165 := bbase (se 5 (by rfl) ⟨498476, by rfl⟩ : syracuseStep 10634165 = 996953) (by norm_num)
theorem B7089443 : Blo 2099435 7089443 := bstep (se 1 (by rfl) ⟨5317082, by rfl⟩ : syracuseStep 7089443 = 10634165) B10634165
theorem B4726295 : Blo 2099435 4726295 := bstep (se 1 (by rfl) ⟨3544721, by rfl⟩ : syracuseStep 4726295 = 7089443) B7089443
theorem B3150863 : Blo 2099435 3150863 := bstep (se 1 (by rfl) ⟨2363147, by rfl⟩ : syracuseStep 3150863 = 4726295) B4726295
theorem B2100575 : Blo 2099435 2100575 := bstep (se 1 (by rfl) ⟨1575431, by rfl⟩ : syracuseStep 2100575 = 3150863) B3150863
theorem B3150869 : Blo 2099435 3150869 := bbase (se 6 (by rfl) ⟨73848, by rfl⟩ : syracuseStep 3150869 = 147697) (by norm_num)
theorem B2100579 : Blo 2099435 2100579 := bstep (se 1 (by rfl) ⟨1575434, by rfl⟩ : syracuseStep 2100579 = 3150869) B3150869
theorem B19163189 : Blo 2099435 19163189 := bbase (se 5 (by rfl) ⟨898274, by rfl⟩ : syracuseStep 19163189 = 1796549) (by norm_num)
theorem B51101837 : Blo 2099435 51101837 := bstep (se 3 (by rfl) ⟨9581594, by rfl⟩ : syracuseStep 51101837 = 19163189) B19163189
theorem B34067891 : Blo 2099435 34067891 := bstep (se 1 (by rfl) ⟨25550918, by rfl⟩ : syracuseStep 34067891 = 51101837) B51101837
theorem B22711927 : Blo 2099435 22711927 := bstep (se 1 (by rfl) ⟨17033945, by rfl⟩ : syracuseStep 22711927 = 34067891) B34067891
theorem B30282569 : Blo 2099435 30282569 := bstep (se 2 (by rfl) ⟨11355963, by rfl⟩ : syracuseStep 30282569 = 22711927) B22711927
theorem B20188379 : Blo 2099435 20188379 := bstep (se 1 (by rfl) ⟨15141284, by rfl⟩ : syracuseStep 20188379 = 30282569) B30282569
theorem B13458919 : Blo 2099435 13458919 := bstep (se 1 (by rfl) ⟨10094189, by rfl⟩ : syracuseStep 13458919 = 20188379) B20188379
theorem B17945225 : Blo 2099435 17945225 := bstep (se 2 (by rfl) ⟨6729459, by rfl⟩ : syracuseStep 17945225 = 13458919) B13458919
theorem B11963483 : Blo 2099435 11963483 := bstep (se 1 (by rfl) ⟨8972612, by rfl⟩ : syracuseStep 11963483 = 17945225) B17945225
theorem B7975655 : Blo 2099435 7975655 := bstep (se 1 (by rfl) ⟨5981741, by rfl⟩ : syracuseStep 7975655 = 11963483) B11963483
theorem B5317103 : Blo 2099435 5317103 := bstep (se 1 (by rfl) ⟨3987827, by rfl⟩ : syracuseStep 5317103 = 7975655) B7975655
theorem B3544735 : Blo 2099435 3544735 := bstep (se 1 (by rfl) ⟨2658551, by rfl⟩ : syracuseStep 3544735 = 5317103) B5317103
theorem B4726313 : Blo 2099435 4726313 := bstep (se 2 (by rfl) ⟨1772367, by rfl⟩ : syracuseStep 4726313 = 3544735) B3544735
theorem B3150875 : Blo 2099435 3150875 := bstep (se 1 (by rfl) ⟨2363156, by rfl⟩ : syracuseStep 3150875 = 4726313) B4726313
theorem B2100583 : Blo 2099435 2100583 := bstep (se 1 (by rfl) ⟨1575437, by rfl⟩ : syracuseStep 2100583 = 3150875) B3150875
theorem B2363161 : Blo 2099435 2363161 := bbase (se 2 (by rfl) ⟨886185, by rfl⟩ : syracuseStep 2363161 = 1772371) (by norm_num)
theorem B3150881 : Blo 2099435 3150881 := bstep (se 2 (by rfl) ⟨1181580, by rfl⟩ : syracuseStep 3150881 = 2363161) B2363161
theorem B2100587 : Blo 2099435 2100587 := bstep (se 1 (by rfl) ⟨1575440, by rfl⟩ : syracuseStep 2100587 = 3150881) B3150881
theorem B7975685 : Blo 2099435 7975685 := bbase (se 4 (by rfl) ⟨747720, by rfl⟩ : syracuseStep 7975685 = 1495441) (by norm_num)
theorem B5317123 : Blo 2099435 5317123 := bstep (se 1 (by rfl) ⟨3987842, by rfl⟩ : syracuseStep 5317123 = 7975685) B7975685
theorem B7089497 : Blo 2099435 7089497 := bstep (se 2 (by rfl) ⟨2658561, by rfl⟩ : syracuseStep 7089497 = 5317123) B5317123
theorem B4726331 : Blo 2099435 4726331 := bstep (se 1 (by rfl) ⟨3544748, by rfl⟩ : syracuseStep 4726331 = 7089497) B7089497
theorem B3150887 : Blo 2099435 3150887 := bstep (se 1 (by rfl) ⟨2363165, by rfl⟩ : syracuseStep 3150887 = 4726331) B4726331
theorem B2100591 : Blo 2099435 2100591 := bstep (se 1 (by rfl) ⟨1575443, by rfl⟩ : syracuseStep 2100591 = 3150887) B3150887
theorem B3150893 : Blo 2099435 3150893 := bbase (se 3 (by rfl) ⟨590792, by rfl⟩ : syracuseStep 3150893 = 1181585) (by norm_num)
theorem B2100595 : Blo 2099435 2100595 := bstep (se 1 (by rfl) ⟨1575446, by rfl⟩ : syracuseStep 2100595 = 3150893) B3150893
theorem B4726349 : Blo 2099435 4726349 := bbase (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) (by norm_num)
theorem B3150899 : Blo 2099435 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B2100599 : Blo 2099435 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B2658577 : Blo 2099435 2658577 := bbase (se 2 (by rfl) ⟨996966, by rfl⟩ : syracuseStep 2658577 = 1993933) (by norm_num)
theorem B3544769 : Blo 2099435 3544769 := bstep (se 2 (by rfl) ⟨1329288, by rfl⟩ : syracuseStep 3544769 = 2658577) B2658577
theorem B2363179 : Blo 2099435 2363179 := bstep (se 1 (by rfl) ⟨1772384, by rfl⟩ : syracuseStep 2363179 = 3544769) B3544769
theorem B3150905 : Blo 2099435 3150905 := bstep (se 2 (by rfl) ⟨1181589, by rfl⟩ : syracuseStep 3150905 = 2363179) B2363179
theorem B2100603 : Blo 2099435 2100603 := bstep (se 1 (by rfl) ⟨1575452, by rfl⟩ : syracuseStep 2100603 = 3150905) B3150905
theorem B4486357 : Blo 2099435 4486357 := bbase (se 7 (by rfl) ⟨52574, by rfl⟩ : syracuseStep 4486357 = 105149) (by norm_num)
theorem B23927237 : Blo 2099435 23927237 := bstep (se 4 (by rfl) ⟨2243178, by rfl⟩ : syracuseStep 23927237 = 4486357) B4486357
theorem B15951491 : Blo 2099435 15951491 := bstep (se 1 (by rfl) ⟨11963618, by rfl⟩ : syracuseStep 15951491 = 23927237) B23927237
theorem B10634327 : Blo 2099435 10634327 := bstep (se 1 (by rfl) ⟨7975745, by rfl⟩ : syracuseStep 10634327 = 15951491) B15951491
theorem B7089551 : Blo 2099435 7089551 := bstep (se 1 (by rfl) ⟨5317163, by rfl⟩ : syracuseStep 7089551 = 10634327) B10634327
theorem B4726367 : Blo 2099435 4726367 := bstep (se 1 (by rfl) ⟨3544775, by rfl⟩ : syracuseStep 4726367 = 7089551) B7089551
theorem B3150911 : Blo 2099435 3150911 := bstep (se 1 (by rfl) ⟨2363183, by rfl⟩ : syracuseStep 3150911 = 4726367) B4726367
theorem B2100607 : Blo 2099435 2100607 := bstep (se 1 (by rfl) ⟨1575455, by rfl⟩ : syracuseStep 2100607 = 3150911) B3150911
theorem B3150917 : Blo 2099435 3150917 := bbase (se 4 (by rfl) ⟨295398, by rfl⟩ : syracuseStep 3150917 = 590797) (by norm_num)
theorem B2100611 : Blo 2099435 2100611 := bstep (se 1 (by rfl) ⟨1575458, by rfl⟩ : syracuseStep 2100611 = 3150917) B3150917
theorem B3544789 : Blo 2099435 3544789 := bbase (se 7 (by rfl) ⟨41540, by rfl⟩ : syracuseStep 3544789 = 83081) (by norm_num)
theorem B4726385 : Blo 2099435 4726385 := bstep (se 2 (by rfl) ⟨1772394, by rfl⟩ : syracuseStep 4726385 = 3544789) B3544789
theorem B3150923 : Blo 2099435 3150923 := bstep (se 1 (by rfl) ⟨2363192, by rfl⟩ : syracuseStep 3150923 = 4726385) B4726385
theorem B2100615 : Blo 2099435 2100615 := bstep (se 1 (by rfl) ⟨1575461, by rfl⟩ : syracuseStep 2100615 = 3150923) B3150923
theorem B2363197 : Blo 2099435 2363197 := bbase (se 3 (by rfl) ⟨443099, by rfl⟩ : syracuseStep 2363197 = 886199) (by norm_num)
theorem B3150929 : Blo 2099435 3150929 := bstep (se 2 (by rfl) ⟨1181598, by rfl⟩ : syracuseStep 3150929 = 2363197) B2363197
theorem B2100619 : Blo 2099435 2100619 := bstep (se 1 (by rfl) ⟨1575464, by rfl⟩ : syracuseStep 2100619 = 3150929) B3150929
theorem B7089605 : Blo 2099435 7089605 := bbase (se 4 (by rfl) ⟨664650, by rfl⟩ : syracuseStep 7089605 = 1329301) (by norm_num)
theorem B4726403 : Blo 2099435 4726403 := bstep (se 1 (by rfl) ⟨3544802, by rfl⟩ : syracuseStep 4726403 = 7089605) B7089605
theorem B3150935 : Blo 2099435 3150935 := bstep (se 1 (by rfl) ⟨2363201, by rfl⟩ : syracuseStep 3150935 = 4726403) B4726403
theorem B2100623 : Blo 2099435 2100623 := bstep (se 1 (by rfl) ⟨1575467, by rfl⟩ : syracuseStep 2100623 = 3150935) B3150935
theorem B3150941 : Blo 2099435 3150941 := bbase (se 3 (by rfl) ⟨590801, by rfl⟩ : syracuseStep 3150941 = 1181603) (by norm_num)
theorem B2100627 : Blo 2099435 2100627 := bstep (se 1 (by rfl) ⟨1575470, by rfl⟩ : syracuseStep 2100627 = 3150941) B3150941
theorem B4726421 : Blo 2099435 4726421 := bbase (se 6 (by rfl) ⟨110775, by rfl⟩ : syracuseStep 4726421 = 221551) (by norm_num)
theorem B3150947 : Blo 2099435 3150947 := bstep (se 1 (by rfl) ⟨2363210, by rfl⟩ : syracuseStep 3150947 = 4726421) B4726421
theorem B2100631 : Blo 2099435 2100631 := bstep (se 1 (by rfl) ⟨1575473, by rfl⟩ : syracuseStep 2100631 = 3150947) B3150947
theorem B2243209 : Blo 2099435 2243209 := bbase (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) (by norm_num)
theorem B2990945 : Blo 2099435 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B7975853 : Blo 2099435 7975853 := bstep (se 3 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 7975853 = 2990945) B2990945
theorem B5317235 : Blo 2099435 5317235 := bstep (se 1 (by rfl) ⟨3987926, by rfl⟩ : syracuseStep 5317235 = 7975853) B7975853
theorem B3544823 : Blo 2099435 3544823 := bstep (se 1 (by rfl) ⟨2658617, by rfl⟩ : syracuseStep 3544823 = 5317235) B5317235
theorem B2363215 : Blo 2099435 2363215 := bstep (se 1 (by rfl) ⟨1772411, by rfl⟩ : syracuseStep 2363215 = 3544823) B3544823
theorem B3150953 : Blo 2099435 3150953 := bstep (se 2 (by rfl) ⟨1181607, by rfl⟩ : syracuseStep 3150953 = 2363215) B2363215
theorem B2100635 : Blo 2099435 2100635 := bstep (se 1 (by rfl) ⟨1575476, by rfl⟩ : syracuseStep 2100635 = 3150953) B3150953
theorem B5047229 : Blo 2099435 5047229 := bbase (se 3 (by rfl) ⟨946355, by rfl⟩ : syracuseStep 5047229 = 1892711) (by norm_num)
theorem B13459277 : Blo 2099435 13459277 := bstep (se 3 (by rfl) ⟨2523614, by rfl⟩ : syracuseStep 13459277 = 5047229) B5047229
theorem B8972851 : Blo 2099435 8972851 := bstep (se 1 (by rfl) ⟨6729638, by rfl⟩ : syracuseStep 8972851 = 13459277) B13459277
theorem B11963801 : Blo 2099435 11963801 := bstep (se 2 (by rfl) ⟨4486425, by rfl⟩ : syracuseStep 11963801 = 8972851) B8972851
theorem B7975867 : Blo 2099435 7975867 := bstep (se 1 (by rfl) ⟨5981900, by rfl⟩ : syracuseStep 7975867 = 11963801) B11963801
theorem B10634489 : Blo 2099435 10634489 := bstep (se 2 (by rfl) ⟨3987933, by rfl⟩ : syracuseStep 10634489 = 7975867) B7975867
theorem B7089659 : Blo 2099435 7089659 := bstep (se 1 (by rfl) ⟨5317244, by rfl⟩ : syracuseStep 7089659 = 10634489) B10634489
theorem B4726439 : Blo 2099435 4726439 := bstep (se 1 (by rfl) ⟨3544829, by rfl⟩ : syracuseStep 4726439 = 7089659) B7089659
theorem B3150959 : Blo 2099435 3150959 := bstep (se 1 (by rfl) ⟨2363219, by rfl⟩ : syracuseStep 3150959 = 4726439) B4726439
theorem B2100639 : Blo 2099435 2100639 := bstep (se 1 (by rfl) ⟨1575479, by rfl⟩ : syracuseStep 2100639 = 3150959) B3150959
theorem B3150965 : Blo 2099435 3150965 := bbase (se 5 (by rfl) ⟨147701, by rfl⟩ : syracuseStep 3150965 = 295403) (by norm_num)
theorem B2100643 : Blo 2099435 2100643 := bstep (se 1 (by rfl) ⟨1575482, by rfl⟩ : syracuseStep 2100643 = 3150965) B3150965
theorem B3987949 : Blo 2099435 3987949 := bbase (se 3 (by rfl) ⟨747740, by rfl⟩ : syracuseStep 3987949 = 1495481) (by norm_num)
theorem B5317265 : Blo 2099435 5317265 := bstep (se 2 (by rfl) ⟨1993974, by rfl⟩ : syracuseStep 5317265 = 3987949) B3987949
theorem B3544843 : Blo 2099435 3544843 := bstep (se 1 (by rfl) ⟨2658632, by rfl⟩ : syracuseStep 3544843 = 5317265) B5317265
theorem B4726457 : Blo 2099435 4726457 := bstep (se 2 (by rfl) ⟨1772421, by rfl⟩ : syracuseStep 4726457 = 3544843) B3544843
theorem B3150971 : Blo 2099435 3150971 := bstep (se 1 (by rfl) ⟨2363228, by rfl⟩ : syracuseStep 3150971 = 4726457) B4726457
theorem B2100647 : Blo 2099435 2100647 := bstep (se 1 (by rfl) ⟨1575485, by rfl⟩ : syracuseStep 2100647 = 3150971) B3150971
theorem B2363233 : Blo 2099435 2363233 := bbase (se 2 (by rfl) ⟨886212, by rfl⟩ : syracuseStep 2363233 = 1772425) (by norm_num)
theorem B3150977 : Blo 2099435 3150977 := bstep (se 2 (by rfl) ⟨1181616, by rfl⟩ : syracuseStep 3150977 = 2363233) B2363233
theorem B2100651 : Blo 2099435 2100651 := bstep (se 1 (by rfl) ⟨1575488, by rfl⟩ : syracuseStep 2100651 = 3150977) B3150977
theorem B5317285 : Blo 2099435 5317285 := bbase (se 4 (by rfl) ⟨498495, by rfl⟩ : syracuseStep 5317285 = 996991) (by norm_num)
theorem B7089713 : Blo 2099435 7089713 := bstep (se 2 (by rfl) ⟨2658642, by rfl⟩ : syracuseStep 7089713 = 5317285) B5317285
theorem B4726475 : Blo 2099435 4726475 := bstep (se 1 (by rfl) ⟨3544856, by rfl⟩ : syracuseStep 4726475 = 7089713) B7089713
theorem B3150983 : Blo 2099435 3150983 := bstep (se 1 (by rfl) ⟨2363237, by rfl⟩ : syracuseStep 3150983 = 4726475) B4726475
theorem B2100655 : Blo 2099435 2100655 := bstep (se 1 (by rfl) ⟨1575491, by rfl⟩ : syracuseStep 2100655 = 3150983) B3150983
theorem B3150989 : Blo 2099435 3150989 := bbase (se 3 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 3150989 = 1181621) (by norm_num)
theorem B2100659 : Blo 2099435 2100659 := bstep (se 1 (by rfl) ⟨1575494, by rfl⟩ : syracuseStep 2100659 = 3150989) B3150989
theorem B4726493 : Blo 2099435 4726493 := bbase (se 3 (by rfl) ⟨886217, by rfl⟩ : syracuseStep 4726493 = 1772435) (by norm_num)
theorem B3150995 : Blo 2099435 3150995 := bstep (se 1 (by rfl) ⟨2363246, by rfl⟩ : syracuseStep 3150995 = 4726493) B4726493
theorem B2100663 : Blo 2099435 2100663 := bstep (se 1 (by rfl) ⟨1575497, by rfl⟩ : syracuseStep 2100663 = 3150995) B3150995
theorem B3544877 : Blo 2099435 3544877 := bbase (se 3 (by rfl) ⟨664664, by rfl⟩ : syracuseStep 3544877 = 1329329) (by norm_num)
theorem B2363251 : Blo 2099435 2363251 := bstep (se 1 (by rfl) ⟨1772438, by rfl⟩ : syracuseStep 2363251 = 3544877) B3544877
theorem B3151001 : Blo 2099435 3151001 := bstep (se 2 (by rfl) ⟨1181625, by rfl⟩ : syracuseStep 3151001 = 2363251) B2363251
theorem B2100667 : Blo 2099435 2100667 := bstep (se 1 (by rfl) ⟨1575500, by rfl⟩ : syracuseStep 2100667 = 3151001) B3151001
theorem B2694937 : Blo 2099435 2694937 := bbase (se 2 (by rfl) ⟨1010601, by rfl⟩ : syracuseStep 2694937 = 2021203) (by norm_num)
theorem B3593249 : Blo 2099435 3593249 := bstep (se 2 (by rfl) ⟨1347468, by rfl⟩ : syracuseStep 3593249 = 2694937) B2694937
theorem B2395499 : Blo 2099435 2395499 := bstep (se 1 (by rfl) ⟨1796624, by rfl⟩ : syracuseStep 2395499 = 3593249) B3593249
theorem B6387997 : Blo 2099435 6387997 := bstep (se 3 (by rfl) ⟨1197749, by rfl⟩ : syracuseStep 6387997 = 2395499) B2395499
theorem B8517329 : Blo 2099435 8517329 := bstep (se 2 (by rfl) ⟨3193998, by rfl⟩ : syracuseStep 8517329 = 6387997) B6387997
theorem B5678219 : Blo 2099435 5678219 := bstep (se 1 (by rfl) ⟨4258664, by rfl⟩ : syracuseStep 5678219 = 8517329) B8517329
theorem B15141917 : Blo 2099435 15141917 := bstep (se 3 (by rfl) ⟨2839109, by rfl⟩ : syracuseStep 15141917 = 5678219) B5678219
theorem B40378445 : Blo 2099435 40378445 := bstep (se 3 (by rfl) ⟨7570958, by rfl⟩ : syracuseStep 40378445 = 15141917) B15141917
theorem B26918963 : Blo 2099435 26918963 := bstep (se 1 (by rfl) ⟨20189222, by rfl⟩ : syracuseStep 26918963 = 40378445) B40378445
theorem B17945975 : Blo 2099435 17945975 := bstep (se 1 (by rfl) ⟨13459481, by rfl⟩ : syracuseStep 17945975 = 26918963) B26918963
theorem B11963983 : Blo 2099435 11963983 := bstep (se 1 (by rfl) ⟨8972987, by rfl⟩ : syracuseStep 11963983 = 17945975) B17945975
theorem B15951977 : Blo 2099435 15951977 := bstep (se 2 (by rfl) ⟨5981991, by rfl⟩ : syracuseStep 15951977 = 11963983) B11963983
theorem B10634651 : Blo 2099435 10634651 := bstep (se 1 (by rfl) ⟨7975988, by rfl⟩ : syracuseStep 10634651 = 15951977) B15951977
theorem B7089767 : Blo 2099435 7089767 := bstep (se 1 (by rfl) ⟨5317325, by rfl⟩ : syracuseStep 7089767 = 10634651) B10634651
theorem B4726511 : Blo 2099435 4726511 := bstep (se 1 (by rfl) ⟨3544883, by rfl⟩ : syracuseStep 4726511 = 7089767) B7089767
theorem B3151007 : Blo 2099435 3151007 := bstep (se 1 (by rfl) ⟨2363255, by rfl⟩ : syracuseStep 3151007 = 4726511) B4726511
theorem B2100671 : Blo 2099435 2100671 := bstep (se 1 (by rfl) ⟨1575503, by rfl⟩ : syracuseStep 2100671 = 3151007) B3151007
theorem B3151013 : Blo 2099435 3151013 := bbase (se 4 (by rfl) ⟨295407, by rfl⟩ : syracuseStep 3151013 = 590815) (by norm_num)
theorem B2100675 : Blo 2099435 2100675 := bstep (se 1 (by rfl) ⟨1575506, by rfl⟩ : syracuseStep 2100675 = 3151013) B3151013
theorem B2658673 : Blo 2099435 2658673 := bbase (se 2 (by rfl) ⟨997002, by rfl⟩ : syracuseStep 2658673 = 1994005) (by norm_num)
theorem B3544897 : Blo 2099435 3544897 := bstep (se 2 (by rfl) ⟨1329336, by rfl⟩ : syracuseStep 3544897 = 2658673) B2658673
theorem B4726529 : Blo 2099435 4726529 := bstep (se 2 (by rfl) ⟨1772448, by rfl⟩ : syracuseStep 4726529 = 3544897) B3544897
theorem B3151019 : Blo 2099435 3151019 := bstep (se 1 (by rfl) ⟨2363264, by rfl⟩ : syracuseStep 3151019 = 4726529) B4726529
theorem B2100679 : Blo 2099435 2100679 := bstep (se 1 (by rfl) ⟨1575509, by rfl⟩ : syracuseStep 2100679 = 3151019) B3151019
theorem B2363269 : Blo 2099435 2363269 := bbase (se 4 (by rfl) ⟨221556, by rfl⟩ : syracuseStep 2363269 = 443113) (by norm_num)
theorem B3151025 : Blo 2099435 3151025 := bstep (se 2 (by rfl) ⟨1181634, by rfl⟩ : syracuseStep 3151025 = 2363269) B2363269
theorem B2100683 : Blo 2099435 2100683 := bstep (se 1 (by rfl) ⟨1575512, by rfl⟩ : syracuseStep 2100683 = 3151025) B3151025
theorem B2523673 : Blo 2099435 2523673 := bbase (se 2 (by rfl) ⟨946377, by rfl⟩ : syracuseStep 2523673 = 1892755) (by norm_num)
theorem B3364897 : Blo 2099435 3364897 := bstep (se 2 (by rfl) ⟨1261836, by rfl⟩ : syracuseStep 3364897 = 2523673) B2523673
theorem B4486529 : Blo 2099435 4486529 := bstep (se 2 (by rfl) ⟨1682448, by rfl⟩ : syracuseStep 4486529 = 3364897) B3364897
theorem B2991019 : Blo 2099435 2991019 := bstep (se 1 (by rfl) ⟨2243264, by rfl⟩ : syracuseStep 2991019 = 4486529) B4486529
theorem B3988025 : Blo 2099435 3988025 := bstep (se 2 (by rfl) ⟨1495509, by rfl⟩ : syracuseStep 3988025 = 2991019) B2991019
theorem B2658683 : Blo 2099435 2658683 := bstep (se 1 (by rfl) ⟨1994012, by rfl⟩ : syracuseStep 2658683 = 3988025) B3988025
theorem B7089821 : Blo 2099435 7089821 := bstep (se 3 (by rfl) ⟨1329341, by rfl⟩ : syracuseStep 7089821 = 2658683) B2658683
theorem B4726547 : Blo 2099435 4726547 := bstep (se 1 (by rfl) ⟨3544910, by rfl⟩ : syracuseStep 4726547 = 7089821) B7089821
theorem B3151031 : Blo 2099435 3151031 := bstep (se 1 (by rfl) ⟨2363273, by rfl⟩ : syracuseStep 3151031 = 4726547) B4726547
theorem B2100687 : Blo 2099435 2100687 := bstep (se 1 (by rfl) ⟨1575515, by rfl⟩ : syracuseStep 2100687 = 3151031) B3151031
theorem B3151037 : Blo 2099435 3151037 := bbase (se 3 (by rfl) ⟨590819, by rfl⟩ : syracuseStep 3151037 = 1181639) (by norm_num)
theorem B2100691 : Blo 2099435 2100691 := bstep (se 1 (by rfl) ⟨1575518, by rfl⟩ : syracuseStep 2100691 = 3151037) B3151037
theorem B4726565 : Blo 2099435 4726565 := bbase (se 4 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 4726565 = 886231) (by norm_num)
theorem B3151043 : Blo 2099435 3151043 := bstep (se 1 (by rfl) ⟨2363282, by rfl⟩ : syracuseStep 3151043 = 4726565) B4726565
theorem B2100695 : Blo 2099435 2100695 := bstep (se 1 (by rfl) ⟨1575521, by rfl⟩ : syracuseStep 2100695 = 3151043) B3151043
theorem B5317397 : Blo 2099435 5317397 := bbase (se 6 (by rfl) ⟨124626, by rfl⟩ : syracuseStep 5317397 = 249253) (by norm_num)
theorem B3544931 : Blo 2099435 3544931 := bstep (se 1 (by rfl) ⟨2658698, by rfl⟩ : syracuseStep 3544931 = 5317397) B5317397
theorem B2363287 : Blo 2099435 2363287 := bstep (se 1 (by rfl) ⟨1772465, by rfl⟩ : syracuseStep 2363287 = 3544931) B3544931
theorem B3151049 : Blo 2099435 3151049 := bstep (se 2 (by rfl) ⟨1181643, by rfl⟩ : syracuseStep 3151049 = 2363287) B2363287
theorem B2100699 : Blo 2099435 2100699 := bstep (se 1 (by rfl) ⟨1575524, by rfl⟩ : syracuseStep 2100699 = 3151049) B3151049
theorem B8973125 : Blo 2099435 8973125 := bbase (se 4 (by rfl) ⟨841230, by rfl⟩ : syracuseStep 8973125 = 1682461) (by norm_num)
theorem B5982083 : Blo 2099435 5982083 := bstep (se 1 (by rfl) ⟨4486562, by rfl⟩ : syracuseStep 5982083 = 8973125) B8973125
theorem B3988055 : Blo 2099435 3988055 := bstep (se 1 (by rfl) ⟨2991041, by rfl⟩ : syracuseStep 3988055 = 5982083) B5982083
theorem B10634813 : Blo 2099435 10634813 := bstep (se 3 (by rfl) ⟨1994027, by rfl⟩ : syracuseStep 10634813 = 3988055) B3988055
theorem B7089875 : Blo 2099435 7089875 := bstep (se 1 (by rfl) ⟨5317406, by rfl⟩ : syracuseStep 7089875 = 10634813) B10634813
theorem B4726583 : Blo 2099435 4726583 := bstep (se 1 (by rfl) ⟨3544937, by rfl⟩ : syracuseStep 4726583 = 7089875) B7089875
theorem B3151055 : Blo 2099435 3151055 := bstep (se 1 (by rfl) ⟨2363291, by rfl⟩ : syracuseStep 3151055 = 4726583) B4726583
theorem B2100703 : Blo 2099435 2100703 := bstep (se 1 (by rfl) ⟨1575527, by rfl⟩ : syracuseStep 2100703 = 3151055) B3151055
theorem B3151061 : Blo 2099435 3151061 := bbase (se 7 (by rfl) ⟨36926, by rfl⟩ : syracuseStep 3151061 = 73853) (by norm_num)
theorem B2100707 : Blo 2099435 2100707 := bstep (se 1 (by rfl) ⟨1575530, by rfl⟩ : syracuseStep 2100707 = 3151061) B3151061
theorem B2991053 : Blo 2099435 2991053 := bbase (se 3 (by rfl) ⟨560822, by rfl⟩ : syracuseStep 2991053 = 1121645) (by norm_num)
theorem B7976141 : Blo 2099435 7976141 := bstep (se 3 (by rfl) ⟨1495526, by rfl⟩ : syracuseStep 7976141 = 2991053) B2991053
theorem B5317427 : Blo 2099435 5317427 := bstep (se 1 (by rfl) ⟨3988070, by rfl⟩ : syracuseStep 5317427 = 7976141) B7976141
theorem B3544951 : Blo 2099435 3544951 := bstep (se 1 (by rfl) ⟨2658713, by rfl⟩ : syracuseStep 3544951 = 5317427) B5317427
theorem B4726601 : Blo 2099435 4726601 := bstep (se 2 (by rfl) ⟨1772475, by rfl⟩ : syracuseStep 4726601 = 3544951) B3544951
theorem B3151067 : Blo 2099435 3151067 := bstep (se 1 (by rfl) ⟨2363300, by rfl⟩ : syracuseStep 3151067 = 4726601) B4726601
theorem B2100711 : Blo 2099435 2100711 := bstep (se 1 (by rfl) ⟨1575533, by rfl⟩ : syracuseStep 2100711 = 3151067) B3151067
theorem B2363305 : Blo 2099435 2363305 := bbase (se 2 (by rfl) ⟨886239, by rfl⟩ : syracuseStep 2363305 = 1772479) (by norm_num)
theorem B3151073 : Blo 2099435 3151073 := bstep (se 2 (by rfl) ⟨1181652, by rfl⟩ : syracuseStep 3151073 = 2363305) B2363305
theorem B2100715 : Blo 2099435 2100715 := bstep (se 1 (by rfl) ⟨1575536, by rfl⟩ : syracuseStep 2100715 = 3151073) B3151073
theorem B2273905 : Blo 2099435 2273905 := bbase (se 2 (by rfl) ⟨852714, by rfl⟩ : syracuseStep 2273905 = 1705429) (by norm_num)
theorem B3031873 : Blo 2099435 3031873 := bstep (se 2 (by rfl) ⟨1136952, by rfl⟩ : syracuseStep 3031873 = 2273905) B2273905
theorem B64679957 : Blo 2099435 64679957 := bstep (se 6 (by rfl) ⟨1515936, by rfl⟩ : syracuseStep 64679957 = 3031873) B3031873
theorem B43119971 : Blo 2099435 43119971 := bstep (se 1 (by rfl) ⟨32339978, by rfl⟩ : syracuseStep 43119971 = 64679957) B64679957
theorem B28746647 : Blo 2099435 28746647 := bstep (se 1 (by rfl) ⟨21559985, by rfl⟩ : syracuseStep 28746647 = 43119971) B43119971
theorem B19164431 : Blo 2099435 19164431 := bstep (se 1 (by rfl) ⟨14373323, by rfl⟩ : syracuseStep 19164431 = 28746647) B28746647
theorem B12776287 : Blo 2099435 12776287 := bstep (se 1 (by rfl) ⟨9582215, by rfl⟩ : syracuseStep 12776287 = 19164431) B19164431
theorem B17035049 : Blo 2099435 17035049 := bstep (se 2 (by rfl) ⟨6388143, by rfl⟩ : syracuseStep 17035049 = 12776287) B12776287
theorem B11356699 : Blo 2099435 11356699 := bstep (se 1 (by rfl) ⟨8517524, by rfl⟩ : syracuseStep 11356699 = 17035049) B17035049
theorem B15142265 : Blo 2099435 15142265 := bstep (se 2 (by rfl) ⟨5678349, by rfl⟩ : syracuseStep 15142265 = 11356699) B11356699
theorem B10094843 : Blo 2099435 10094843 := bstep (se 1 (by rfl) ⟨7571132, by rfl⟩ : syracuseStep 10094843 = 15142265) B15142265
theorem B6729895 : Blo 2099435 6729895 := bstep (se 1 (by rfl) ⟨5047421, by rfl⟩ : syracuseStep 6729895 = 10094843) B10094843
theorem B8973193 : Blo 2099435 8973193 := bstep (se 2 (by rfl) ⟨3364947, by rfl⟩ : syracuseStep 8973193 = 6729895) B6729895
theorem B11964257 : Blo 2099435 11964257 := bstep (se 2 (by rfl) ⟨4486596, by rfl⟩ : syracuseStep 11964257 = 8973193) B8973193
theorem B7976171 : Blo 2099435 7976171 := bstep (se 1 (by rfl) ⟨5982128, by rfl⟩ : syracuseStep 7976171 = 11964257) B11964257
theorem B5317447 : Blo 2099435 5317447 := bstep (se 1 (by rfl) ⟨3988085, by rfl⟩ : syracuseStep 5317447 = 7976171) B7976171
theorem B7089929 : Blo 2099435 7089929 := bstep (se 2 (by rfl) ⟨2658723, by rfl⟩ : syracuseStep 7089929 = 5317447) B5317447
theorem B4726619 : Blo 2099435 4726619 := bstep (se 1 (by rfl) ⟨3544964, by rfl⟩ : syracuseStep 4726619 = 7089929) B7089929
theorem B3151079 : Blo 2099435 3151079 := bstep (se 1 (by rfl) ⟨2363309, by rfl⟩ : syracuseStep 3151079 = 4726619) B4726619
theorem B2100719 : Blo 2099435 2100719 := bstep (se 1 (by rfl) ⟨1575539, by rfl⟩ : syracuseStep 2100719 = 3151079) B3151079
theorem B3151085 : Blo 2099435 3151085 := bbase (se 3 (by rfl) ⟨590828, by rfl⟩ : syracuseStep 3151085 = 1181657) (by norm_num)
theorem B2100723 : Blo 2099435 2100723 := bstep (se 1 (by rfl) ⟨1575542, by rfl⟩ : syracuseStep 2100723 = 3151085) B3151085
theorem B4726637 : Blo 2099435 4726637 := bbase (se 3 (by rfl) ⟨886244, by rfl⟩ : syracuseStep 4726637 = 1772489) (by norm_num)
theorem B3151091 : Blo 2099435 3151091 := bstep (se 1 (by rfl) ⟨2363318, by rfl⟩ : syracuseStep 3151091 = 4726637) B4726637
theorem B2100727 : Blo 2099435 2100727 := bstep (se 1 (by rfl) ⟨1575545, by rfl⟩ : syracuseStep 2100727 = 3151091) B3151091
theorem B3988109 : Blo 2099435 3988109 := bbase (se 3 (by rfl) ⟨747770, by rfl⟩ : syracuseStep 3988109 = 1495541) (by norm_num)
theorem B2658739 : Blo 2099435 2658739 := bstep (se 1 (by rfl) ⟨1994054, by rfl⟩ : syracuseStep 2658739 = 3988109) B3988109
theorem B3544985 : Blo 2099435 3544985 := bstep (se 2 (by rfl) ⟨1329369, by rfl⟩ : syracuseStep 3544985 = 2658739) B2658739
theorem B2363323 : Blo 2099435 2363323 := bstep (se 1 (by rfl) ⟨1772492, by rfl⟩ : syracuseStep 2363323 = 3544985) B3544985
theorem B3151097 : Blo 2099435 3151097 := bstep (se 2 (by rfl) ⟨1181661, by rfl⟩ : syracuseStep 3151097 = 2363323) B2363323
theorem B2100731 : Blo 2099435 2100731 := bstep (se 1 (by rfl) ⟨1575548, by rfl⟩ : syracuseStep 2100731 = 3151097) B3151097
theorem B7571189 : Blo 2099435 7571189 := bbase (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) (by norm_num)
theorem B20189837 : Blo 2099435 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B53839565 : Blo 2099435 53839565 := bstep (se 3 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 53839565 = 20189837) B20189837
theorem B35893043 : Blo 2099435 35893043 := bstep (se 1 (by rfl) ⟨26919782, by rfl⟩ : syracuseStep 35893043 = 53839565) B53839565
theorem B23928695 : Blo 2099435 23928695 := bstep (se 1 (by rfl) ⟨17946521, by rfl⟩ : syracuseStep 23928695 = 35893043) B35893043
theorem B15952463 : Blo 2099435 15952463 := bstep (se 1 (by rfl) ⟨11964347, by rfl⟩ : syracuseStep 15952463 = 23928695) B23928695
theorem B10634975 : Blo 2099435 10634975 := bstep (se 1 (by rfl) ⟨7976231, by rfl⟩ : syracuseStep 10634975 = 15952463) B15952463
theorem B7089983 : Blo 2099435 7089983 := bstep (se 1 (by rfl) ⟨5317487, by rfl⟩ : syracuseStep 7089983 = 10634975) B10634975
theorem B4726655 : Blo 2099435 4726655 := bstep (se 1 (by rfl) ⟨3544991, by rfl⟩ : syracuseStep 4726655 = 7089983) B7089983
theorem B3151103 : Blo 2099435 3151103 := bstep (se 1 (by rfl) ⟨2363327, by rfl⟩ : syracuseStep 3151103 = 4726655) B4726655
theorem B2100735 : Blo 2099435 2100735 := bstep (se 1 (by rfl) ⟨1575551, by rfl⟩ : syracuseStep 2100735 = 3151103) B3151103
theorem B3151109 : Blo 2099435 3151109 := bbase (se 4 (by rfl) ⟨295416, by rfl⟩ : syracuseStep 3151109 = 590833) (by norm_num)
theorem B2100739 : Blo 2099435 2100739 := bstep (se 1 (by rfl) ⟨1575554, by rfl⟩ : syracuseStep 2100739 = 3151109) B3151109
theorem B3545005 : Blo 2099435 3545005 := bbase (se 3 (by rfl) ⟨664688, by rfl⟩ : syracuseStep 3545005 = 1329377) (by norm_num)
theorem B4726673 : Blo 2099435 4726673 := bstep (se 2 (by rfl) ⟨1772502, by rfl⟩ : syracuseStep 4726673 = 3545005) B3545005
theorem B3151115 : Blo 2099435 3151115 := bstep (se 1 (by rfl) ⟨2363336, by rfl⟩ : syracuseStep 3151115 = 4726673) B4726673
theorem B2100743 : Blo 2099435 2100743 := bstep (se 1 (by rfl) ⟨1575557, by rfl⟩ : syracuseStep 2100743 = 3151115) B3151115
theorem B2363341 : Blo 2099435 2363341 := bbase (se 3 (by rfl) ⟨443126, by rfl⟩ : syracuseStep 2363341 = 886253) (by norm_num)
theorem B3151121 : Blo 2099435 3151121 := bstep (se 2 (by rfl) ⟨1181670, by rfl⟩ : syracuseStep 3151121 = 2363341) B2363341
theorem B2100747 : Blo 2099435 2100747 := bstep (se 1 (by rfl) ⟨1575560, by rfl⟩ : syracuseStep 2100747 = 3151121) B3151121
theorem B7090037 : Blo 2099435 7090037 := bbase (se 5 (by rfl) ⟨332345, by rfl⟩ : syracuseStep 7090037 = 664691) (by norm_num)
theorem B4726691 : Blo 2099435 4726691 := bstep (se 1 (by rfl) ⟨3545018, by rfl⟩ : syracuseStep 4726691 = 7090037) B7090037
theorem B3151127 : Blo 2099435 3151127 := bstep (se 1 (by rfl) ⟨2363345, by rfl⟩ : syracuseStep 3151127 = 4726691) B4726691
theorem B2100751 : Blo 2099435 2100751 := bstep (se 1 (by rfl) ⟨1575563, by rfl⟩ : syracuseStep 2100751 = 3151127) B3151127
theorem B3151133 : Blo 2099435 3151133 := bbase (se 3 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 3151133 = 1181675) (by norm_num)
theorem B2100755 : Blo 2099435 2100755 := bstep (se 1 (by rfl) ⟨1575566, by rfl⟩ : syracuseStep 2100755 = 3151133) B3151133
theorem B4726709 : Blo 2099435 4726709 := bbase (se 5 (by rfl) ⟨221564, by rfl⟩ : syracuseStep 4726709 = 443129) (by norm_num)
theorem B3151139 : Blo 2099435 3151139 := bstep (se 1 (by rfl) ⟨2363354, by rfl⟩ : syracuseStep 3151139 = 4726709) B4726709
theorem B2100759 : Blo 2099435 2100759 := bstep (se 1 (by rfl) ⟨1575569, by rfl⟩ : syracuseStep 2100759 = 3151139) B3151139
theorem B6730037 : Blo 2099435 6730037 := bbase (se 5 (by rfl) ⟨315470, by rfl⟩ : syracuseStep 6730037 = 630941) (by norm_num)
theorem B4486691 : Blo 2099435 4486691 := bstep (se 1 (by rfl) ⟨3365018, by rfl⟩ : syracuseStep 4486691 = 6730037) B6730037
theorem B11964509 : Blo 2099435 11964509 := bstep (se 3 (by rfl) ⟨2243345, by rfl⟩ : syracuseStep 11964509 = 4486691) B4486691
theorem B7976339 : Blo 2099435 7976339 := bstep (se 1 (by rfl) ⟨5982254, by rfl⟩ : syracuseStep 7976339 = 11964509) B11964509
theorem B5317559 : Blo 2099435 5317559 := bstep (se 1 (by rfl) ⟨3988169, by rfl⟩ : syracuseStep 5317559 = 7976339) B7976339
theorem B3545039 : Blo 2099435 3545039 := bstep (se 1 (by rfl) ⟨2658779, by rfl⟩ : syracuseStep 3545039 = 5317559) B5317559
theorem B2363359 : Blo 2099435 2363359 := bstep (se 1 (by rfl) ⟨1772519, by rfl⟩ : syracuseStep 2363359 = 3545039) B3545039
theorem B3151145 : Blo 2099435 3151145 := bstep (se 2 (by rfl) ⟨1181679, by rfl⟩ : syracuseStep 3151145 = 2363359) B2363359
theorem B2100763 : Blo 2099435 2100763 := bstep (se 1 (by rfl) ⟨1575572, by rfl⟩ : syracuseStep 2100763 = 3151145) B3151145
theorem B3785653 : Blo 2099435 3785653 := bbase (se 5 (by rfl) ⟨177452, by rfl⟩ : syracuseStep 3785653 = 354905) (by norm_num)
theorem B5047537 : Blo 2099435 5047537 := bstep (se 2 (by rfl) ⟨1892826, by rfl⟩ : syracuseStep 5047537 = 3785653) B3785653
theorem B6730049 : Blo 2099435 6730049 := bstep (se 2 (by rfl) ⟨2523768, by rfl⟩ : syracuseStep 6730049 = 5047537) B5047537
theorem B4486699 : Blo 2099435 4486699 := bstep (se 1 (by rfl) ⟨3365024, by rfl⟩ : syracuseStep 4486699 = 6730049) B6730049
theorem B5982265 : Blo 2099435 5982265 := bstep (se 2 (by rfl) ⟨2243349, by rfl⟩ : syracuseStep 5982265 = 4486699) B4486699
theorem B7976353 : Blo 2099435 7976353 := bstep (se 2 (by rfl) ⟨2991132, by rfl⟩ : syracuseStep 7976353 = 5982265) B5982265
theorem B10635137 : Blo 2099435 10635137 := bstep (se 2 (by rfl) ⟨3988176, by rfl⟩ : syracuseStep 10635137 = 7976353) B7976353
theorem B7090091 : Blo 2099435 7090091 := bstep (se 1 (by rfl) ⟨5317568, by rfl⟩ : syracuseStep 7090091 = 10635137) B10635137
theorem B4726727 : Blo 2099435 4726727 := bstep (se 1 (by rfl) ⟨3545045, by rfl⟩ : syracuseStep 4726727 = 7090091) B7090091
theorem B3151151 : Blo 2099435 3151151 := bstep (se 1 (by rfl) ⟨2363363, by rfl⟩ : syracuseStep 3151151 = 4726727) B4726727
theorem B2100767 : Blo 2099435 2100767 := bstep (se 1 (by rfl) ⟨1575575, by rfl⟩ : syracuseStep 2100767 = 3151151) B3151151
theorem B3151157 : Blo 2099435 3151157 := bbase (se 5 (by rfl) ⟨147710, by rfl⟩ : syracuseStep 3151157 = 295421) (by norm_num)
theorem B2100771 : Blo 2099435 2100771 := bstep (se 1 (by rfl) ⟨1575578, by rfl⟩ : syracuseStep 2100771 = 3151157) B3151157
theorem B5317589 : Blo 2099435 5317589 := bbase (se 7 (by rfl) ⟨62315, by rfl⟩ : syracuseStep 5317589 = 124631) (by norm_num)
theorem B3545059 : Blo 2099435 3545059 := bstep (se 1 (by rfl) ⟨2658794, by rfl⟩ : syracuseStep 3545059 = 5317589) B5317589
theorem B4726745 : Blo 2099435 4726745 := bstep (se 2 (by rfl) ⟨1772529, by rfl⟩ : syracuseStep 4726745 = 3545059) B3545059
theorem B3151163 : Blo 2099435 3151163 := bstep (se 1 (by rfl) ⟨2363372, by rfl⟩ : syracuseStep 3151163 = 4726745) B4726745
theorem B2100775 : Blo 2099435 2100775 := bstep (se 1 (by rfl) ⟨1575581, by rfl⟩ : syracuseStep 2100775 = 3151163) B3151163
theorem B2363377 : Blo 2099435 2363377 := bbase (se 2 (by rfl) ⟨886266, by rfl⟩ : syracuseStep 2363377 = 1772533) (by norm_num)
theorem B3151169 : Blo 2099435 3151169 := bstep (se 2 (by rfl) ⟨1181688, by rfl⟩ : syracuseStep 3151169 = 2363377) B2363377
theorem B2100779 : Blo 2099435 2100779 := bstep (se 1 (by rfl) ⟨1575584, by rfl⟩ : syracuseStep 2100779 = 3151169) B3151169
theorem B10232885 : Blo 2099435 10232885 := bbase (se 5 (by rfl) ⟨479666, by rfl⟩ : syracuseStep 10232885 = 959333) (by norm_num)
theorem B6821923 : Blo 2099435 6821923 := bstep (se 1 (by rfl) ⟨5116442, by rfl⟩ : syracuseStep 6821923 = 10232885) B10232885
theorem B9095897 : Blo 2099435 9095897 := bstep (se 2 (by rfl) ⟨3410961, by rfl⟩ : syracuseStep 9095897 = 6821923) B6821923
theorem B6063931 : Blo 2099435 6063931 := bstep (se 1 (by rfl) ⟨4547948, by rfl⟩ : syracuseStep 6063931 = 9095897) B9095897
theorem B8085241 : Blo 2099435 8085241 := bstep (se 2 (by rfl) ⟨3031965, by rfl⟩ : syracuseStep 8085241 = 6063931) B6063931
theorem B43121285 : Blo 2099435 43121285 := bstep (se 4 (by rfl) ⟨4042620, by rfl⟩ : syracuseStep 43121285 = 8085241) B8085241
theorem B28747523 : Blo 2099435 28747523 := bstep (se 1 (by rfl) ⟨21560642, by rfl⟩ : syracuseStep 28747523 = 43121285) B43121285
theorem B19165015 : Blo 2099435 19165015 := bstep (se 1 (by rfl) ⟨14373761, by rfl⟩ : syracuseStep 19165015 = 28747523) B28747523
theorem B25553353 : Blo 2099435 25553353 := bstep (se 2 (by rfl) ⟨9582507, by rfl⟩ : syracuseStep 25553353 = 19165015) B19165015
theorem B34071137 : Blo 2099435 34071137 := bstep (se 2 (by rfl) ⟨12776676, by rfl⟩ : syracuseStep 34071137 = 25553353) B25553353
theorem B22714091 : Blo 2099435 22714091 := bstep (se 1 (by rfl) ⟨17035568, by rfl⟩ : syracuseStep 22714091 = 34071137) B34071137
theorem B15142727 : Blo 2099435 15142727 := bstep (se 1 (by rfl) ⟨11357045, by rfl⟩ : syracuseStep 15142727 = 22714091) B22714091
theorem B10095151 : Blo 2099435 10095151 := bstep (se 1 (by rfl) ⟨7571363, by rfl⟩ : syracuseStep 10095151 = 15142727) B15142727
theorem B13460201 : Blo 2099435 13460201 := bstep (se 2 (by rfl) ⟨5047575, by rfl⟩ : syracuseStep 13460201 = 10095151) B10095151
theorem B8973467 : Blo 2099435 8973467 := bstep (se 1 (by rfl) ⟨6730100, by rfl⟩ : syracuseStep 8973467 = 13460201) B13460201
theorem B5982311 : Blo 2099435 5982311 := bstep (se 1 (by rfl) ⟨4486733, by rfl⟩ : syracuseStep 5982311 = 8973467) B8973467
theorem B3988207 : Blo 2099435 3988207 := bstep (se 1 (by rfl) ⟨2991155, by rfl⟩ : syracuseStep 3988207 = 5982311) B5982311
theorem B5317609 : Blo 2099435 5317609 := bstep (se 2 (by rfl) ⟨1994103, by rfl⟩ : syracuseStep 5317609 = 3988207) B3988207
theorem B7090145 : Blo 2099435 7090145 := bstep (se 2 (by rfl) ⟨2658804, by rfl⟩ : syracuseStep 7090145 = 5317609) B5317609
theorem B4726763 : Blo 2099435 4726763 := bstep (se 1 (by rfl) ⟨3545072, by rfl⟩ : syracuseStep 4726763 = 7090145) B7090145
theorem B3151175 : Blo 2099435 3151175 := bstep (se 1 (by rfl) ⟨2363381, by rfl⟩ : syracuseStep 3151175 = 4726763) B4726763
theorem B2100783 : Blo 2099435 2100783 := bstep (se 1 (by rfl) ⟨1575587, by rfl⟩ : syracuseStep 2100783 = 3151175) B3151175
theorem B3151181 : Blo 2099435 3151181 := bbase (se 3 (by rfl) ⟨590846, by rfl⟩ : syracuseStep 3151181 = 1181693) (by norm_num)
theorem B2100787 : Blo 2099435 2100787 := bstep (se 1 (by rfl) ⟨1575590, by rfl⟩ : syracuseStep 2100787 = 3151181) B3151181
theorem B4726781 : Blo 2099435 4726781 := bbase (se 3 (by rfl) ⟨886271, by rfl⟩ : syracuseStep 4726781 = 1772543) (by norm_num)
theorem B3151187 : Blo 2099435 3151187 := bstep (se 1 (by rfl) ⟨2363390, by rfl⟩ : syracuseStep 3151187 = 4726781) B4726781
theorem B2100791 : Blo 2099435 2100791 := bstep (se 1 (by rfl) ⟨1575593, by rfl⟩ : syracuseStep 2100791 = 3151187) B3151187
theorem B3545093 : Blo 2099435 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B2363395 : Blo 2099435 2363395 := bstep (se 1 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 2363395 = 3545093) B3545093
theorem B3151193 : Blo 2099435 3151193 := bstep (se 2 (by rfl) ⟨1181697, by rfl⟩ : syracuseStep 3151193 = 2363395) B2363395
theorem B2100795 : Blo 2099435 2100795 := bstep (se 1 (by rfl) ⟨1575596, by rfl⟩ : syracuseStep 2100795 = 3151193) B3151193
theorem B15952949 : Blo 2099435 15952949 := bbase (se 5 (by rfl) ⟨747794, by rfl⟩ : syracuseStep 15952949 = 1495589) (by norm_num)
theorem B10635299 : Blo 2099435 10635299 := bstep (se 1 (by rfl) ⟨7976474, by rfl⟩ : syracuseStep 10635299 = 15952949) B15952949
theorem B7090199 : Blo 2099435 7090199 := bstep (se 1 (by rfl) ⟨5317649, by rfl⟩ : syracuseStep 7090199 = 10635299) B10635299
theorem B4726799 : Blo 2099435 4726799 := bstep (se 1 (by rfl) ⟨3545099, by rfl⟩ : syracuseStep 4726799 = 7090199) B7090199
theorem B3151199 : Blo 2099435 3151199 := bstep (se 1 (by rfl) ⟨2363399, by rfl⟩ : syracuseStep 3151199 = 4726799) B4726799
theorem B2100799 : Blo 2099435 2100799 := bstep (se 1 (by rfl) ⟨1575599, by rfl⟩ : syracuseStep 2100799 = 3151199) B3151199
theorem B3151205 : Blo 2099435 3151205 := bbase (se 4 (by rfl) ⟨295425, by rfl⟩ : syracuseStep 3151205 = 590851) (by norm_num)
theorem B2100803 : Blo 2099435 2100803 := bstep (se 1 (by rfl) ⟨1575602, by rfl⟩ : syracuseStep 2100803 = 3151205) B3151205
theorem B3988253 : Blo 2099435 3988253 := bbase (se 3 (by rfl) ⟨747797, by rfl⟩ : syracuseStep 3988253 = 1495595) (by norm_num)
theorem B2658835 : Blo 2099435 2658835 := bstep (se 1 (by rfl) ⟨1994126, by rfl⟩ : syracuseStep 2658835 = 3988253) B3988253
theorem B3545113 : Blo 2099435 3545113 := bstep (se 2 (by rfl) ⟨1329417, by rfl⟩ : syracuseStep 3545113 = 2658835) B2658835
theorem B4726817 : Blo 2099435 4726817 := bstep (se 2 (by rfl) ⟨1772556, by rfl⟩ : syracuseStep 4726817 = 3545113) B3545113
theorem B3151211 : Blo 2099435 3151211 := bstep (se 1 (by rfl) ⟨2363408, by rfl⟩ : syracuseStep 3151211 = 4726817) B4726817
theorem B2100807 : Blo 2099435 2100807 := bstep (se 1 (by rfl) ⟨1575605, by rfl⟩ : syracuseStep 2100807 = 3151211) B3151211
theorem B2363413 : Blo 2099435 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B3151217 : Blo 2099435 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B2100811 : Blo 2099435 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B2658845 : Blo 2099435 2658845 := bbase (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) (by norm_num)
theorem B7090253 : Blo 2099435 7090253 := bstep (se 3 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 7090253 = 2658845) B2658845
theorem B4726835 : Blo 2099435 4726835 := bstep (se 1 (by rfl) ⟨3545126, by rfl⟩ : syracuseStep 4726835 = 7090253) B7090253
theorem B3151223 : Blo 2099435 3151223 := bstep (se 1 (by rfl) ⟨2363417, by rfl⟩ : syracuseStep 3151223 = 4726835) B4726835
theorem B2100815 : Blo 2099435 2100815 := bstep (se 1 (by rfl) ⟨1575611, by rfl⟩ : syracuseStep 2100815 = 3151223) B3151223
theorem B3151229 : Blo 2099435 3151229 := bbase (se 3 (by rfl) ⟨590855, by rfl⟩ : syracuseStep 3151229 = 1181711) (by norm_num)
theorem B2100819 : Blo 2099435 2100819 := bstep (se 1 (by rfl) ⟨1575614, by rfl⟩ : syracuseStep 2100819 = 3151229) B3151229
theorem B4726853 : Blo 2099435 4726853 := bbase (se 4 (by rfl) ⟨443142, by rfl⟩ : syracuseStep 4726853 = 886285) (by norm_num)
theorem B3151235 : Blo 2099435 3151235 := bstep (se 1 (by rfl) ⟨2363426, by rfl⟩ : syracuseStep 3151235 = 4726853) B4726853
theorem B2100823 : Blo 2099435 2100823 := bstep (se 1 (by rfl) ⟨1575617, by rfl⟩ : syracuseStep 2100823 = 3151235) B3151235
theorem B5982437 : Blo 2099435 5982437 := bbase (se 4 (by rfl) ⟨560853, by rfl⟩ : syracuseStep 5982437 = 1121707) (by norm_num)
theorem B3988291 : Blo 2099435 3988291 := bstep (se 1 (by rfl) ⟨2991218, by rfl⟩ : syracuseStep 3988291 = 5982437) B5982437
theorem B5317721 : Blo 2099435 5317721 := bstep (se 2 (by rfl) ⟨1994145, by rfl⟩ : syracuseStep 5317721 = 3988291) B3988291
theorem B3545147 : Blo 2099435 3545147 := bstep (se 1 (by rfl) ⟨2658860, by rfl⟩ : syracuseStep 3545147 = 5317721) B5317721
theorem B2363431 : Blo 2099435 2363431 := bstep (se 1 (by rfl) ⟨1772573, by rfl⟩ : syracuseStep 2363431 = 3545147) B3545147
theorem B3151241 : Blo 2099435 3151241 := bstep (se 2 (by rfl) ⟨1181715, by rfl⟩ : syracuseStep 3151241 = 2363431) B2363431
theorem B2100827 : Blo 2099435 2100827 := bstep (se 1 (by rfl) ⟨1575620, by rfl⟩ : syracuseStep 2100827 = 3151241) B3151241
theorem B10635461 : Blo 2099435 10635461 := bbase (se 4 (by rfl) ⟨997074, by rfl⟩ : syracuseStep 10635461 = 1994149) (by norm_num)
theorem B7090307 : Blo 2099435 7090307 := bstep (se 1 (by rfl) ⟨5317730, by rfl⟩ : syracuseStep 7090307 = 10635461) B10635461
theorem B4726871 : Blo 2099435 4726871 := bstep (se 1 (by rfl) ⟨3545153, by rfl⟩ : syracuseStep 4726871 = 7090307) B7090307
theorem B3151247 : Blo 2099435 3151247 := bstep (se 1 (by rfl) ⟨2363435, by rfl⟩ : syracuseStep 3151247 = 4726871) B4726871
theorem B2100831 : Blo 2099435 2100831 := bstep (se 1 (by rfl) ⟨1575623, by rfl⟩ : syracuseStep 2100831 = 3151247) B3151247
theorem B3151253 : Blo 2099435 3151253 := bbase (se 6 (by rfl) ⟨73857, by rfl⟩ : syracuseStep 3151253 = 147715) (by norm_num)
theorem B2100835 : Blo 2099435 2100835 := bstep (se 1 (by rfl) ⟨1575626, by rfl⟩ : syracuseStep 2100835 = 3151253) B3151253
theorem B4486853 : Blo 2099435 4486853 := bbase (se 4 (by rfl) ⟨420642, by rfl⟩ : syracuseStep 4486853 = 841285) (by norm_num)
theorem B11964941 : Blo 2099435 11964941 := bstep (se 3 (by rfl) ⟨2243426, by rfl⟩ : syracuseStep 11964941 = 4486853) B4486853
theorem B7976627 : Blo 2099435 7976627 := bstep (se 1 (by rfl) ⟨5982470, by rfl⟩ : syracuseStep 7976627 = 11964941) B11964941
theorem B5317751 : Blo 2099435 5317751 := bstep (se 1 (by rfl) ⟨3988313, by rfl⟩ : syracuseStep 5317751 = 7976627) B7976627
theorem B3545167 : Blo 2099435 3545167 := bstep (se 1 (by rfl) ⟨2658875, by rfl⟩ : syracuseStep 3545167 = 5317751) B5317751
theorem B4726889 : Blo 2099435 4726889 := bstep (se 2 (by rfl) ⟨1772583, by rfl⟩ : syracuseStep 4726889 = 3545167) B3545167
theorem B3151259 : Blo 2099435 3151259 := bstep (se 1 (by rfl) ⟨2363444, by rfl⟩ : syracuseStep 3151259 = 4726889) B4726889
theorem B2100839 : Blo 2099435 2100839 := bstep (se 1 (by rfl) ⟨1575629, by rfl⟩ : syracuseStep 2100839 = 3151259) B3151259
theorem B2363449 : Blo 2099435 2363449 := bbase (se 2 (by rfl) ⟨886293, by rfl⟩ : syracuseStep 2363449 = 1772587) (by norm_num)
theorem B3151265 : Blo 2099435 3151265 := bstep (se 2 (by rfl) ⟨1181724, by rfl⟩ : syracuseStep 3151265 = 2363449) B2363449
theorem B2100843 : Blo 2099435 2100843 := bstep (se 1 (by rfl) ⟨1575632, by rfl⟩ : syracuseStep 2100843 = 3151265) B3151265
theorem B2523865 : Blo 2099435 2523865 := bbase (se 2 (by rfl) ⟨946449, by rfl⟩ : syracuseStep 2523865 = 1892899) (by norm_num)
theorem B3365153 : Blo 2099435 3365153 := bstep (se 2 (by rfl) ⟨1261932, by rfl⟩ : syracuseStep 3365153 = 2523865) B2523865
theorem B2243435 : Blo 2099435 2243435 := bstep (se 1 (by rfl) ⟨1682576, by rfl⟩ : syracuseStep 2243435 = 3365153) B3365153
theorem B5982493 : Blo 2099435 5982493 := bstep (se 3 (by rfl) ⟨1121717, by rfl⟩ : syracuseStep 5982493 = 2243435) B2243435
theorem B7976657 : Blo 2099435 7976657 := bstep (se 2 (by rfl) ⟨2991246, by rfl⟩ : syracuseStep 7976657 = 5982493) B5982493
theorem B5317771 : Blo 2099435 5317771 := bstep (se 1 (by rfl) ⟨3988328, by rfl⟩ : syracuseStep 5317771 = 7976657) B7976657
theorem B7090361 : Blo 2099435 7090361 := bstep (se 2 (by rfl) ⟨2658885, by rfl⟩ : syracuseStep 7090361 = 5317771) B5317771
theorem B4726907 : Blo 2099435 4726907 := bstep (se 1 (by rfl) ⟨3545180, by rfl⟩ : syracuseStep 4726907 = 7090361) B7090361
theorem B3151271 : Blo 2099435 3151271 := bstep (se 1 (by rfl) ⟨2363453, by rfl⟩ : syracuseStep 3151271 = 4726907) B4726907
theorem B2100847 : Blo 2099435 2100847 := bstep (se 1 (by rfl) ⟨1575635, by rfl⟩ : syracuseStep 2100847 = 3151271) B3151271
theorem B3151277 : Blo 2099435 3151277 := bbase (se 3 (by rfl) ⟨590864, by rfl⟩ : syracuseStep 3151277 = 1181729) (by norm_num)
theorem B2100851 : Blo 2099435 2100851 := bstep (se 1 (by rfl) ⟨1575638, by rfl⟩ : syracuseStep 2100851 = 3151277) B3151277
theorem B4726925 : Blo 2099435 4726925 := bbase (se 3 (by rfl) ⟨886298, by rfl⟩ : syracuseStep 4726925 = 1772597) (by norm_num)
theorem B3151283 : Blo 2099435 3151283 := bstep (se 1 (by rfl) ⟨2363462, by rfl⟩ : syracuseStep 3151283 = 4726925) B4726925
theorem B2100855 : Blo 2099435 2100855 := bstep (se 1 (by rfl) ⟨1575641, by rfl⟩ : syracuseStep 2100855 = 3151283) B3151283
theorem B2658901 : Blo 2099435 2658901 := bbase (se 8 (by rfl) ⟨15579, by rfl⟩ : syracuseStep 2658901 = 31159) (by norm_num)
theorem B3545201 : Blo 2099435 3545201 := bstep (se 2 (by rfl) ⟨1329450, by rfl⟩ : syracuseStep 3545201 = 2658901) B2658901
theorem B2363467 : Blo 2099435 2363467 := bstep (se 1 (by rfl) ⟨1772600, by rfl⟩ : syracuseStep 2363467 = 3545201) B3545201
theorem B3151289 : Blo 2099435 3151289 := bstep (se 2 (by rfl) ⟨1181733, by rfl⟩ : syracuseStep 3151289 = 2363467) B2363467
theorem B2100859 : Blo 2099435 2100859 := bstep (se 1 (by rfl) ⟨1575644, by rfl⟩ : syracuseStep 2100859 = 3151289) B3151289
theorem B6822181 : Blo 2099435 6822181 := bbase (se 4 (by rfl) ⟨639579, by rfl⟩ : syracuseStep 6822181 = 1279159) (by norm_num)
theorem B9096241 : Blo 2099435 9096241 := bstep (se 2 (by rfl) ⟨3411090, by rfl⟩ : syracuseStep 9096241 = 6822181) B6822181
theorem B12128321 : Blo 2099435 12128321 := bstep (se 2 (by rfl) ⟨4548120, by rfl⟩ : syracuseStep 12128321 = 9096241) B9096241
theorem B8085547 : Blo 2099435 8085547 := bstep (se 1 (by rfl) ⟨6064160, by rfl⟩ : syracuseStep 8085547 = 12128321) B12128321
theorem B43122917 : Blo 2099435 43122917 := bstep (se 4 (by rfl) ⟨4042773, by rfl⟩ : syracuseStep 43122917 = 8085547) B8085547
theorem B28748611 : Blo 2099435 28748611 := bstep (se 1 (by rfl) ⟨21561458, by rfl⟩ : syracuseStep 28748611 = 43122917) B43122917
theorem B38331481 : Blo 2099435 38331481 := bstep (se 2 (by rfl) ⟨14374305, by rfl⟩ : syracuseStep 38331481 = 28748611) B28748611
theorem B51108641 : Blo 2099435 51108641 := bstep (se 2 (by rfl) ⟨19165740, by rfl⟩ : syracuseStep 51108641 = 38331481) B38331481
theorem B34072427 : Blo 2099435 34072427 := bstep (se 1 (by rfl) ⟨25554320, by rfl⟩ : syracuseStep 34072427 = 51108641) B51108641
theorem B90859805 : Blo 2099435 90859805 := bstep (se 3 (by rfl) ⟨17036213, by rfl⟩ : syracuseStep 90859805 = 34072427) B34072427
theorem B60573203 : Blo 2099435 60573203 := bstep (se 1 (by rfl) ⟨45429902, by rfl⟩ : syracuseStep 60573203 = 90859805) B90859805
theorem B40382135 : Blo 2099435 40382135 := bstep (se 1 (by rfl) ⟨30286601, by rfl⟩ : syracuseStep 40382135 = 60573203) B60573203
theorem B26921423 : Blo 2099435 26921423 := bstep (se 1 (by rfl) ⟨20191067, by rfl⟩ : syracuseStep 26921423 = 40382135) B40382135
theorem B17947615 : Blo 2099435 17947615 := bstep (se 1 (by rfl) ⟨13460711, by rfl⟩ : syracuseStep 17947615 = 26921423) B26921423
theorem B23930153 : Blo 2099435 23930153 := bstep (se 2 (by rfl) ⟨8973807, by rfl⟩ : syracuseStep 23930153 = 17947615) B17947615
theorem B15953435 : Blo 2099435 15953435 := bstep (se 1 (by rfl) ⟨11965076, by rfl⟩ : syracuseStep 15953435 = 23930153) B23930153
theorem B10635623 : Blo 2099435 10635623 := bstep (se 1 (by rfl) ⟨7976717, by rfl⟩ : syracuseStep 10635623 = 15953435) B15953435
theorem B7090415 : Blo 2099435 7090415 := bstep (se 1 (by rfl) ⟨5317811, by rfl⟩ : syracuseStep 7090415 = 10635623) B10635623
theorem B4726943 : Blo 2099435 4726943 := bstep (se 1 (by rfl) ⟨3545207, by rfl⟩ : syracuseStep 4726943 = 7090415) B7090415
theorem B3151295 : Blo 2099435 3151295 := bstep (se 1 (by rfl) ⟨2363471, by rfl⟩ : syracuseStep 3151295 = 4726943) B4726943
theorem B2100863 : Blo 2099435 2100863 := bstep (se 1 (by rfl) ⟨1575647, by rfl⟩ : syracuseStep 2100863 = 3151295) B3151295
theorem B3151301 : Blo 2099435 3151301 := bbase (se 4 (by rfl) ⟨295434, by rfl⟩ : syracuseStep 3151301 = 590869) (by norm_num)
theorem B2100867 : Blo 2099435 2100867 := bstep (se 1 (by rfl) ⟨1575650, by rfl⟩ : syracuseStep 2100867 = 3151301) B3151301
theorem B3545221 : Blo 2099435 3545221 := bbase (se 4 (by rfl) ⟨332364, by rfl⟩ : syracuseStep 3545221 = 664729) (by norm_num)
theorem B4726961 : Blo 2099435 4726961 := bstep (se 2 (by rfl) ⟨1772610, by rfl⟩ : syracuseStep 4726961 = 3545221) B3545221
theorem B3151307 : Blo 2099435 3151307 := bstep (se 1 (by rfl) ⟨2363480, by rfl⟩ : syracuseStep 3151307 = 4726961) B4726961
theorem B2100871 : Blo 2099435 2100871 := bstep (se 1 (by rfl) ⟨1575653, by rfl⟩ : syracuseStep 2100871 = 3151307) B3151307
theorem B2363485 : Blo 2099435 2363485 := bbase (se 3 (by rfl) ⟨443153, by rfl⟩ : syracuseStep 2363485 = 886307) (by norm_num)
theorem B3151313 : Blo 2099435 3151313 := bstep (se 2 (by rfl) ⟨1181742, by rfl⟩ : syracuseStep 3151313 = 2363485) B2363485
theorem B2100875 : Blo 2099435 2100875 := bstep (se 1 (by rfl) ⟨1575656, by rfl⟩ : syracuseStep 2100875 = 3151313) B3151313
theorem B7090469 : Blo 2099435 7090469 := bbase (se 4 (by rfl) ⟨664731, by rfl⟩ : syracuseStep 7090469 = 1329463) (by norm_num)
theorem B4726979 : Blo 2099435 4726979 := bstep (se 1 (by rfl) ⟨3545234, by rfl⟩ : syracuseStep 4726979 = 7090469) B7090469
theorem B3151319 : Blo 2099435 3151319 := bstep (se 1 (by rfl) ⟨2363489, by rfl⟩ : syracuseStep 3151319 = 4726979) B4726979
theorem B2100879 : Blo 2099435 2100879 := bstep (se 1 (by rfl) ⟨1575659, by rfl⟩ : syracuseStep 2100879 = 3151319) B3151319
theorem B3151325 : Blo 2099435 3151325 := bbase (se 3 (by rfl) ⟨590873, by rfl⟩ : syracuseStep 3151325 = 1181747) (by norm_num)
theorem B2100883 : Blo 2099435 2100883 := bstep (se 1 (by rfl) ⟨1575662, by rfl⟩ : syracuseStep 2100883 = 3151325) B3151325
theorem B4726997 : Blo 2099435 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B3151331 : Blo 2099435 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B2100887 : Blo 2099435 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B4042829 : Blo 2099435 4042829 := bbase (se 3 (by rfl) ⟨758030, by rfl⟩ : syracuseStep 4042829 = 1516061) (by norm_num)
theorem B10780877 : Blo 2099435 10780877 := bstep (se 3 (by rfl) ⟨2021414, by rfl⟩ : syracuseStep 10780877 = 4042829) B4042829
theorem B28749005 : Blo 2099435 28749005 := bstep (se 3 (by rfl) ⟨5390438, by rfl⟩ : syracuseStep 28749005 = 10780877) B10780877
theorem B19166003 : Blo 2099435 19166003 := bstep (se 1 (by rfl) ⟨14374502, by rfl⟩ : syracuseStep 19166003 = 28749005) B28749005
theorem B12777335 : Blo 2099435 12777335 := bstep (se 1 (by rfl) ⟨9583001, by rfl⟩ : syracuseStep 12777335 = 19166003) B19166003
theorem B8518223 : Blo 2099435 8518223 := bstep (se 1 (by rfl) ⟨6388667, by rfl⟩ : syracuseStep 8518223 = 12777335) B12777335
theorem B22715261 : Blo 2099435 22715261 := bstep (se 3 (by rfl) ⟨4259111, by rfl⟩ : syracuseStep 22715261 = 8518223) B8518223
theorem B15143507 : Blo 2099435 15143507 := bstep (se 1 (by rfl) ⟨11357630, by rfl⟩ : syracuseStep 15143507 = 22715261) B22715261
theorem B10095671 : Blo 2099435 10095671 := bstep (se 1 (by rfl) ⟨7571753, by rfl⟩ : syracuseStep 10095671 = 15143507) B15143507
theorem B6730447 : Blo 2099435 6730447 := bstep (se 1 (by rfl) ⟨5047835, by rfl⟩ : syracuseStep 6730447 = 10095671) B10095671
theorem B8973929 : Blo 2099435 8973929 := bstep (se 2 (by rfl) ⟨3365223, by rfl⟩ : syracuseStep 8973929 = 6730447) B6730447
theorem B5982619 : Blo 2099435 5982619 := bstep (se 1 (by rfl) ⟨4486964, by rfl⟩ : syracuseStep 5982619 = 8973929) B8973929
theorem B7976825 : Blo 2099435 7976825 := bstep (se 2 (by rfl) ⟨2991309, by rfl⟩ : syracuseStep 7976825 = 5982619) B5982619
theorem B5317883 : Blo 2099435 5317883 := bstep (se 1 (by rfl) ⟨3988412, by rfl⟩ : syracuseStep 5317883 = 7976825) B7976825
theorem B3545255 : Blo 2099435 3545255 := bstep (se 1 (by rfl) ⟨2658941, by rfl⟩ : syracuseStep 3545255 = 5317883) B5317883
theorem B2363503 : Blo 2099435 2363503 := bstep (se 1 (by rfl) ⟨1772627, by rfl⟩ : syracuseStep 2363503 = 3545255) B3545255
theorem B3151337 : Blo 2099435 3151337 := bstep (se 2 (by rfl) ⟨1181751, by rfl⟩ : syracuseStep 3151337 = 2363503) B2363503
theorem B2100891 : Blo 2099435 2100891 := bstep (se 1 (by rfl) ⟨1575668, by rfl⟩ : syracuseStep 2100891 = 3151337) B3151337
theorem B13460917 : Blo 2099435 13460917 := bbase (se 5 (by rfl) ⟨630980, by rfl⟩ : syracuseStep 13460917 = 1261961) (by norm_num)
theorem B17947889 : Blo 2099435 17947889 := bstep (se 2 (by rfl) ⟨6730458, by rfl⟩ : syracuseStep 17947889 = 13460917) B13460917
theorem B11965259 : Blo 2099435 11965259 := bstep (se 1 (by rfl) ⟨8973944, by rfl⟩ : syracuseStep 11965259 = 17947889) B17947889
theorem B7976839 : Blo 2099435 7976839 := bstep (se 1 (by rfl) ⟨5982629, by rfl⟩ : syracuseStep 7976839 = 11965259) B11965259
theorem B10635785 : Blo 2099435 10635785 := bstep (se 2 (by rfl) ⟨3988419, by rfl⟩ : syracuseStep 10635785 = 7976839) B7976839
theorem B7090523 : Blo 2099435 7090523 := bstep (se 1 (by rfl) ⟨5317892, by rfl⟩ : syracuseStep 7090523 = 10635785) B10635785
theorem B4727015 : Blo 2099435 4727015 := bstep (se 1 (by rfl) ⟨3545261, by rfl⟩ : syracuseStep 4727015 = 7090523) B7090523
theorem B3151343 : Blo 2099435 3151343 := bstep (se 1 (by rfl) ⟨2363507, by rfl⟩ : syracuseStep 3151343 = 4727015) B4727015
theorem B2100895 : Blo 2099435 2100895 := bstep (se 1 (by rfl) ⟨1575671, by rfl⟩ : syracuseStep 2100895 = 3151343) B3151343
theorem B3151349 : Blo 2099435 3151349 := bbase (se 5 (by rfl) ⟨147719, by rfl⟩ : syracuseStep 3151349 = 295439) (by norm_num)
theorem B2100899 : Blo 2099435 2100899 := bstep (se 1 (by rfl) ⟨1575674, by rfl⟩ : syracuseStep 2100899 = 3151349) B3151349
theorem B2395765 : Blo 2099435 2395765 := bbase (se 5 (by rfl) ⟨112301, by rfl⟩ : syracuseStep 2395765 = 224603) (by norm_num)
theorem B3194353 : Blo 2099435 3194353 := bstep (se 2 (by rfl) ⟨1197882, by rfl⟩ : syracuseStep 3194353 = 2395765) B2395765
theorem B4259137 : Blo 2099435 4259137 := bstep (se 2 (by rfl) ⟨1597176, by rfl⟩ : syracuseStep 4259137 = 3194353) B3194353
theorem B5678849 : Blo 2099435 5678849 := bstep (se 2 (by rfl) ⟨2129568, by rfl⟩ : syracuseStep 5678849 = 4259137) B4259137
theorem B3785899 : Blo 2099435 3785899 := bstep (se 1 (by rfl) ⟨2839424, by rfl⟩ : syracuseStep 3785899 = 5678849) B5678849
theorem B5047865 : Blo 2099435 5047865 := bstep (se 2 (by rfl) ⟨1892949, by rfl⟩ : syracuseStep 5047865 = 3785899) B3785899
theorem B3365243 : Blo 2099435 3365243 := bstep (se 1 (by rfl) ⟨2523932, by rfl⟩ : syracuseStep 3365243 = 5047865) B5047865
theorem B2243495 : Blo 2099435 2243495 := bstep (se 1 (by rfl) ⟨1682621, by rfl⟩ : syracuseStep 2243495 = 3365243) B3365243
theorem B5982653 : Blo 2099435 5982653 := bstep (se 3 (by rfl) ⟨1121747, by rfl⟩ : syracuseStep 5982653 = 2243495) B2243495
theorem B3988435 : Blo 2099435 3988435 := bstep (se 1 (by rfl) ⟨2991326, by rfl⟩ : syracuseStep 3988435 = 5982653) B5982653
theorem B5317913 : Blo 2099435 5317913 := bstep (se 2 (by rfl) ⟨1994217, by rfl⟩ : syracuseStep 5317913 = 3988435) B3988435
theorem B3545275 : Blo 2099435 3545275 := bstep (se 1 (by rfl) ⟨2658956, by rfl⟩ : syracuseStep 3545275 = 5317913) B5317913
theorem B4727033 : Blo 2099435 4727033 := bstep (se 2 (by rfl) ⟨1772637, by rfl⟩ : syracuseStep 4727033 = 3545275) B3545275
theorem B3151355 : Blo 2099435 3151355 := bstep (se 1 (by rfl) ⟨2363516, by rfl⟩ : syracuseStep 3151355 = 4727033) B4727033
theorem B2100903 : Blo 2099435 2100903 := bstep (se 1 (by rfl) ⟨1575677, by rfl⟩ : syracuseStep 2100903 = 3151355) B3151355
theorem B2363521 : Blo 2099435 2363521 := bbase (se 2 (by rfl) ⟨886320, by rfl⟩ : syracuseStep 2363521 = 1772641) (by norm_num)
theorem B3151361 : Blo 2099435 3151361 := bstep (se 2 (by rfl) ⟨1181760, by rfl⟩ : syracuseStep 3151361 = 2363521) B2363521
theorem B2100907 : Blo 2099435 2100907 := bstep (se 1 (by rfl) ⟨1575680, by rfl⟩ : syracuseStep 2100907 = 3151361) B3151361
theorem B5317933 : Blo 2099435 5317933 := bbase (se 3 (by rfl) ⟨997112, by rfl⟩ : syracuseStep 5317933 = 1994225) (by norm_num)
theorem B7090577 : Blo 2099435 7090577 := bstep (se 2 (by rfl) ⟨2658966, by rfl⟩ : syracuseStep 7090577 = 5317933) B5317933
theorem B4727051 : Blo 2099435 4727051 := bstep (se 1 (by rfl) ⟨3545288, by rfl⟩ : syracuseStep 4727051 = 7090577) B7090577
theorem B3151367 : Blo 2099435 3151367 := bstep (se 1 (by rfl) ⟨2363525, by rfl⟩ : syracuseStep 3151367 = 4727051) B4727051
theorem B2100911 : Blo 2099435 2100911 := bstep (se 1 (by rfl) ⟨1575683, by rfl⟩ : syracuseStep 2100911 = 3151367) B3151367
theorem B3151373 : Blo 2099435 3151373 := bbase (se 3 (by rfl) ⟨590882, by rfl⟩ : syracuseStep 3151373 = 1181765) (by norm_num)
theorem B2100915 : Blo 2099435 2100915 := bstep (se 1 (by rfl) ⟨1575686, by rfl⟩ : syracuseStep 2100915 = 3151373) B3151373
theorem B4727069 : Blo 2099435 4727069 := bbase (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) (by norm_num)
theorem B3151379 : Blo 2099435 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B2100919 : Blo 2099435 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B3545309 : Blo 2099435 3545309 := bbase (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) (by norm_num)
theorem B2363539 : Blo 2099435 2363539 := bstep (se 1 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 2363539 = 3545309) B3545309
theorem B3151385 : Blo 2099435 3151385 := bstep (se 2 (by rfl) ⟨1181769, by rfl⟩ : syracuseStep 3151385 = 2363539) B2363539
theorem B2100923 : Blo 2099435 2100923 := bstep (se 1 (by rfl) ⟨1575692, by rfl⟩ : syracuseStep 2100923 = 3151385) B3151385
theorem B3785941 : Blo 2099435 3785941 := bbase (se 7 (by rfl) ⟨44366, by rfl⟩ : syracuseStep 3785941 = 88733) (by norm_num)
theorem B5047921 : Blo 2099435 5047921 := bstep (se 2 (by rfl) ⟨1892970, by rfl⟩ : syracuseStep 5047921 = 3785941) B3785941
theorem B6730561 : Blo 2099435 6730561 := bstep (se 2 (by rfl) ⟨2523960, by rfl⟩ : syracuseStep 6730561 = 5047921) B5047921
theorem B8974081 : Blo 2099435 8974081 := bstep (se 2 (by rfl) ⟨3365280, by rfl⟩ : syracuseStep 8974081 = 6730561) B6730561
theorem B11965441 : Blo 2099435 11965441 := bstep (se 2 (by rfl) ⟨4487040, by rfl⟩ : syracuseStep 11965441 = 8974081) B8974081
theorem B15953921 : Blo 2099435 15953921 := bstep (se 2 (by rfl) ⟨5982720, by rfl⟩ : syracuseStep 15953921 = 11965441) B11965441
theorem B10635947 : Blo 2099435 10635947 := bstep (se 1 (by rfl) ⟨7976960, by rfl⟩ : syracuseStep 10635947 = 15953921) B15953921
theorem B7090631 : Blo 2099435 7090631 := bstep (se 1 (by rfl) ⟨5317973, by rfl⟩ : syracuseStep 7090631 = 10635947) B10635947
theorem B4727087 : Blo 2099435 4727087 := bstep (se 1 (by rfl) ⟨3545315, by rfl⟩ : syracuseStep 4727087 = 7090631) B7090631
theorem B3151391 : Blo 2099435 3151391 := bstep (se 1 (by rfl) ⟨2363543, by rfl⟩ : syracuseStep 3151391 = 4727087) B4727087
theorem B2100927 : Blo 2099435 2100927 := bstep (se 1 (by rfl) ⟨1575695, by rfl⟩ : syracuseStep 2100927 = 3151391) B3151391
theorem B3151397 : Blo 2099435 3151397 := bbase (se 4 (by rfl) ⟨295443, by rfl⟩ : syracuseStep 3151397 = 590887) (by norm_num)
theorem B2100931 : Blo 2099435 2100931 := bstep (se 1 (by rfl) ⟨1575698, by rfl⟩ : syracuseStep 2100931 = 3151397) B3151397
theorem B2658997 : Blo 2099435 2658997 := bbase (se 5 (by rfl) ⟨124640, by rfl⟩ : syracuseStep 2658997 = 249281) (by norm_num)
theorem B3545329 : Blo 2099435 3545329 := bstep (se 2 (by rfl) ⟨1329498, by rfl⟩ : syracuseStep 3545329 = 2658997) B2658997
theorem B4727105 : Blo 2099435 4727105 := bstep (se 2 (by rfl) ⟨1772664, by rfl⟩ : syracuseStep 4727105 = 3545329) B3545329
theorem B3151403 : Blo 2099435 3151403 := bstep (se 1 (by rfl) ⟨2363552, by rfl⟩ : syracuseStep 3151403 = 4727105) B4727105
theorem B2100935 : Blo 2099435 2100935 := bstep (se 1 (by rfl) ⟨1575701, by rfl⟩ : syracuseStep 2100935 = 3151403) B3151403
theorem B2363557 : Blo 2099435 2363557 := bbase (se 4 (by rfl) ⟨221583, by rfl⟩ : syracuseStep 2363557 = 443167) (by norm_num)
theorem B3151409 : Blo 2099435 3151409 := bstep (se 2 (by rfl) ⟨1181778, by rfl⟩ : syracuseStep 3151409 = 2363557) B2363557
theorem B2100939 : Blo 2099435 2100939 := bstep (se 1 (by rfl) ⟨1575704, by rfl⟩ : syracuseStep 2100939 = 3151409) B3151409
theorem B7187429 : Blo 2099435 7187429 := bbase (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) (by norm_num)
theorem B4791619 : Blo 2099435 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B25555301 : Blo 2099435 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B17036867 : Blo 2099435 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B11357911 : Blo 2099435 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B15143881 : Blo 2099435 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B20191841 : Blo 2099435 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B13461227 : Blo 2099435 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B8974151 : Blo 2099435 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B5982767 : Blo 2099435 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B3988511 : Blo 2099435 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B2659007 : Blo 2099435 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B7090685 : Blo 2099435 7090685 := bstep (se 3 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 7090685 = 2659007) B2659007
theorem B4727123 : Blo 2099435 4727123 := bstep (se 1 (by rfl) ⟨3545342, by rfl⟩ : syracuseStep 4727123 = 7090685) B7090685
theorem B3151415 : Blo 2099435 3151415 := bstep (se 1 (by rfl) ⟨2363561, by rfl⟩ : syracuseStep 3151415 = 4727123) B4727123
theorem B2100943 : Blo 2099435 2100943 := bstep (se 1 (by rfl) ⟨1575707, by rfl⟩ : syracuseStep 2100943 = 3151415) B3151415
theorem B3151421 : Blo 2099435 3151421 := bbase (se 3 (by rfl) ⟨590891, by rfl⟩ : syracuseStep 3151421 = 1181783) (by norm_num)
theorem B2100947 : Blo 2099435 2100947 := bstep (se 1 (by rfl) ⟨1575710, by rfl⟩ : syracuseStep 2100947 = 3151421) B3151421
theorem B4727141 : Blo 2099435 4727141 := bbase (se 4 (by rfl) ⟨443169, by rfl⟩ : syracuseStep 4727141 = 886339) (by norm_num)
theorem B3151427 : Blo 2099435 3151427 := bstep (se 1 (by rfl) ⟨2363570, by rfl⟩ : syracuseStep 3151427 = 4727141) B4727141
theorem B2100951 : Blo 2099435 2100951 := bstep (se 1 (by rfl) ⟨1575713, by rfl⟩ : syracuseStep 2100951 = 3151427) B3151427
theorem B5318045 : Blo 2099435 5318045 := bbase (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) (by norm_num)
theorem B3545363 : Blo 2099435 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B2363575 : Blo 2099435 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B3151433 : Blo 2099435 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B2100955 : Blo 2099435 2100955 := bstep (se 1 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 2100955 = 3151433) B3151433
theorem B3988541 : Blo 2099435 3988541 := bbase (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) (by norm_num)
theorem B10636109 : Blo 2099435 10636109 := bstep (se 3 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 10636109 = 3988541) B3988541
theorem B7090739 : Blo 2099435 7090739 := bstep (se 1 (by rfl) ⟨5318054, by rfl⟩ : syracuseStep 7090739 = 10636109) B10636109
theorem B4727159 : Blo 2099435 4727159 := bstep (se 1 (by rfl) ⟨3545369, by rfl⟩ : syracuseStep 4727159 = 7090739) B7090739
theorem B3151439 : Blo 2099435 3151439 := bstep (se 1 (by rfl) ⟨2363579, by rfl⟩ : syracuseStep 3151439 = 4727159) B4727159
theorem B2100959 : Blo 2099435 2100959 := bstep (se 1 (by rfl) ⟨1575719, by rfl⟩ : syracuseStep 2100959 = 3151439) B3151439
theorem B3151445 : Blo 2099435 3151445 := bbase (se 8 (by rfl) ⟨18465, by rfl⟩ : syracuseStep 3151445 = 36931) (by norm_num)
theorem B2100963 : Blo 2099435 2100963 := bstep (se 1 (by rfl) ⟨1575722, by rfl⟩ : syracuseStep 2100963 = 3151445) B3151445
theorem B2524009 : Blo 2099435 2524009 := bbase (se 2 (by rfl) ⟨946503, by rfl⟩ : syracuseStep 2524009 = 1893007) (by norm_num)
theorem B3365345 : Blo 2099435 3365345 := bstep (se 2 (by rfl) ⟨1262004, by rfl⟩ : syracuseStep 3365345 = 2524009) B2524009
theorem B8974253 : Blo 2099435 8974253 := bstep (se 3 (by rfl) ⟨1682672, by rfl⟩ : syracuseStep 8974253 = 3365345) B3365345
theorem B5982835 : Blo 2099435 5982835 := bstep (se 1 (by rfl) ⟨4487126, by rfl⟩ : syracuseStep 5982835 = 8974253) B8974253
theorem B7977113 : Blo 2099435 7977113 := bstep (se 2 (by rfl) ⟨2991417, by rfl⟩ : syracuseStep 7977113 = 5982835) B5982835
theorem B5318075 : Blo 2099435 5318075 := bstep (se 1 (by rfl) ⟨3988556, by rfl⟩ : syracuseStep 5318075 = 7977113) B7977113
theorem B3545383 : Blo 2099435 3545383 := bstep (se 1 (by rfl) ⟨2659037, by rfl⟩ : syracuseStep 3545383 = 5318075) B5318075
theorem B4727177 : Blo 2099435 4727177 := bstep (se 2 (by rfl) ⟨1772691, by rfl⟩ : syracuseStep 4727177 = 3545383) B3545383
theorem B3151451 : Blo 2099435 3151451 := bstep (se 1 (by rfl) ⟨2363588, by rfl⟩ : syracuseStep 3151451 = 4727177) B4727177
theorem B2100967 : Blo 2099435 2100967 := bstep (se 1 (by rfl) ⟨1575725, by rfl⟩ : syracuseStep 2100967 = 3151451) B3151451
theorem B2363593 : Blo 2099435 2363593 := bbase (se 2 (by rfl) ⟨886347, by rfl⟩ : syracuseStep 2363593 = 1772695) (by norm_num)
theorem B3151457 : Blo 2099435 3151457 := bstep (se 2 (by rfl) ⟨1181796, by rfl⟩ : syracuseStep 3151457 = 2363593) B2363593
theorem B2100971 : Blo 2099435 2100971 := bstep (se 1 (by rfl) ⟨1575728, by rfl⟩ : syracuseStep 2100971 = 3151457) B3151457
theorem B3194461 : Blo 2099435 3194461 := bbase (se 3 (by rfl) ⟨598961, by rfl⟩ : syracuseStep 3194461 = 1197923) (by norm_num)
theorem B17037125 : Blo 2099435 17037125 := bstep (se 4 (by rfl) ⟨1597230, by rfl⟩ : syracuseStep 17037125 = 3194461) B3194461
theorem B11358083 : Blo 2099435 11358083 := bstep (se 1 (by rfl) ⟨8518562, by rfl⟩ : syracuseStep 11358083 = 17037125) B17037125
theorem B7572055 : Blo 2099435 7572055 := bstep (se 1 (by rfl) ⟨5679041, by rfl⟩ : syracuseStep 7572055 = 11358083) B11358083
theorem B10096073 : Blo 2099435 10096073 := bstep (se 2 (by rfl) ⟨3786027, by rfl⟩ : syracuseStep 10096073 = 7572055) B7572055
theorem B6730715 : Blo 2099435 6730715 := bstep (se 1 (by rfl) ⟨5048036, by rfl⟩ : syracuseStep 6730715 = 10096073) B10096073
theorem B17948573 : Blo 2099435 17948573 := bstep (se 3 (by rfl) ⟨3365357, by rfl⟩ : syracuseStep 17948573 = 6730715) B6730715
theorem B11965715 : Blo 2099435 11965715 := bstep (se 1 (by rfl) ⟨8974286, by rfl⟩ : syracuseStep 11965715 = 17948573) B17948573
theorem B7977143 : Blo 2099435 7977143 := bstep (se 1 (by rfl) ⟨5982857, by rfl⟩ : syracuseStep 7977143 = 11965715) B11965715
theorem B5318095 : Blo 2099435 5318095 := bstep (se 1 (by rfl) ⟨3988571, by rfl⟩ : syracuseStep 5318095 = 7977143) B7977143
theorem B7090793 : Blo 2099435 7090793 := bstep (se 2 (by rfl) ⟨2659047, by rfl⟩ : syracuseStep 7090793 = 5318095) B5318095
theorem B4727195 : Blo 2099435 4727195 := bstep (se 1 (by rfl) ⟨3545396, by rfl⟩ : syracuseStep 4727195 = 7090793) B7090793
theorem B3151463 : Blo 2099435 3151463 := bstep (se 1 (by rfl) ⟨2363597, by rfl⟩ : syracuseStep 3151463 = 4727195) B4727195
theorem B2100975 : Blo 2099435 2100975 := bstep (se 1 (by rfl) ⟨1575731, by rfl⟩ : syracuseStep 2100975 = 3151463) B3151463
theorem B3151469 : Blo 2099435 3151469 := bbase (se 3 (by rfl) ⟨590900, by rfl⟩ : syracuseStep 3151469 = 1181801) (by norm_num)
theorem B2100979 : Blo 2099435 2100979 := bstep (se 1 (by rfl) ⟨1575734, by rfl⟩ : syracuseStep 2100979 = 3151469) B3151469
theorem B4727213 : Blo 2099435 4727213 := bbase (se 3 (by rfl) ⟨886352, by rfl⟩ : syracuseStep 4727213 = 1772705) (by norm_num)
theorem B3151475 : Blo 2099435 3151475 := bstep (se 1 (by rfl) ⟨2363606, by rfl⟩ : syracuseStep 3151475 = 4727213) B4727213
theorem B2100983 : Blo 2099435 2100983 := bstep (se 1 (by rfl) ⟨1575737, by rfl⟩ : syracuseStep 2100983 = 3151475) B3151475
theorem B2243585 : Blo 2099435 2243585 := bbase (se 2 (by rfl) ⟨841344, by rfl⟩ : syracuseStep 2243585 = 1682689) (by norm_num)
theorem B5982893 : Blo 2099435 5982893 := bstep (se 3 (by rfl) ⟨1121792, by rfl⟩ : syracuseStep 5982893 = 2243585) B2243585
theorem B3988595 : Blo 2099435 3988595 := bstep (se 1 (by rfl) ⟨2991446, by rfl⟩ : syracuseStep 3988595 = 5982893) B5982893
theorem B2659063 : Blo 2099435 2659063 := bstep (se 1 (by rfl) ⟨1994297, by rfl⟩ : syracuseStep 2659063 = 3988595) B3988595
theorem B3545417 : Blo 2099435 3545417 := bstep (se 2 (by rfl) ⟨1329531, by rfl⟩ : syracuseStep 3545417 = 2659063) B2659063
theorem B2363611 : Blo 2099435 2363611 := bstep (se 1 (by rfl) ⟨1772708, by rfl⟩ : syracuseStep 2363611 = 3545417) B3545417
theorem B3151481 : Blo 2099435 3151481 := bstep (se 2 (by rfl) ⟨1181805, by rfl⟩ : syracuseStep 3151481 = 2363611) B2363611
theorem B2100987 : Blo 2099435 2100987 := bstep (se 1 (by rfl) ⟨1575740, by rfl⟩ : syracuseStep 2100987 = 3151481) B3151481
theorem B5390693 : Blo 2099435 5390693 := bbase (se 4 (by rfl) ⟨505377, by rfl⟩ : syracuseStep 5390693 = 1010755) (by norm_num)
theorem B57500725 : Blo 2099435 57500725 := bstep (se 5 (by rfl) ⟨2695346, by rfl⟩ : syracuseStep 57500725 = 5390693) B5390693
theorem B76667633 : Blo 2099435 76667633 := bstep (se 2 (by rfl) ⟨28750362, by rfl⟩ : syracuseStep 76667633 = 57500725) B57500725
theorem B51111755 : Blo 2099435 51111755 := bstep (se 1 (by rfl) ⟨38333816, by rfl⟩ : syracuseStep 51111755 = 76667633) B76667633
theorem B34074503 : Blo 2099435 34074503 := bstep (se 1 (by rfl) ⟨25555877, by rfl⟩ : syracuseStep 34074503 = 51111755) B51111755
theorem B22716335 : Blo 2099435 22716335 := bstep (se 1 (by rfl) ⟨17037251, by rfl⟩ : syracuseStep 22716335 = 34074503) B34074503
theorem B60576893 : Blo 2099435 60576893 := bstep (se 3 (by rfl) ⟨11358167, by rfl⟩ : syracuseStep 60576893 = 22716335) B22716335
theorem B40384595 : Blo 2099435 40384595 := bstep (se 1 (by rfl) ⟨30288446, by rfl⟩ : syracuseStep 40384595 = 60576893) B60576893
theorem B26923063 : Blo 2099435 26923063 := bstep (se 1 (by rfl) ⟨20192297, by rfl⟩ : syracuseStep 26923063 = 40384595) B40384595
theorem B35897417 : Blo 2099435 35897417 := bstep (se 2 (by rfl) ⟨13461531, by rfl⟩ : syracuseStep 35897417 = 26923063) B26923063
theorem B23931611 : Blo 2099435 23931611 := bstep (se 1 (by rfl) ⟨17948708, by rfl⟩ : syracuseStep 23931611 = 35897417) B35897417
theorem B15954407 : Blo 2099435 15954407 := bstep (se 1 (by rfl) ⟨11965805, by rfl⟩ : syracuseStep 15954407 = 23931611) B23931611
theorem B10636271 : Blo 2099435 10636271 := bstep (se 1 (by rfl) ⟨7977203, by rfl⟩ : syracuseStep 10636271 = 15954407) B15954407
theorem B7090847 : Blo 2099435 7090847 := bstep (se 1 (by rfl) ⟨5318135, by rfl⟩ : syracuseStep 7090847 = 10636271) B10636271
theorem B4727231 : Blo 2099435 4727231 := bstep (se 1 (by rfl) ⟨3545423, by rfl⟩ : syracuseStep 4727231 = 7090847) B7090847
theorem B3151487 : Blo 2099435 3151487 := bstep (se 1 (by rfl) ⟨2363615, by rfl⟩ : syracuseStep 3151487 = 4727231) B4727231
theorem B2100991 : Blo 2099435 2100991 := bstep (se 1 (by rfl) ⟨1575743, by rfl⟩ : syracuseStep 2100991 = 3151487) B3151487
theorem B3151493 : Blo 2099435 3151493 := bbase (se 4 (by rfl) ⟨295452, by rfl⟩ : syracuseStep 3151493 = 590905) (by norm_num)
theorem B2100995 : Blo 2099435 2100995 := bstep (se 1 (by rfl) ⟨1575746, by rfl⟩ : syracuseStep 2100995 = 3151493) B3151493
theorem B3545437 : Blo 2099435 3545437 := bbase (se 3 (by rfl) ⟨664769, by rfl⟩ : syracuseStep 3545437 = 1329539) (by norm_num)
theorem B4727249 : Blo 2099435 4727249 := bstep (se 2 (by rfl) ⟨1772718, by rfl⟩ : syracuseStep 4727249 = 3545437) B3545437
theorem B3151499 : Blo 2099435 3151499 := bstep (se 1 (by rfl) ⟨2363624, by rfl⟩ : syracuseStep 3151499 = 4727249) B4727249
theorem B2100999 : Blo 2099435 2100999 := bstep (se 1 (by rfl) ⟨1575749, by rfl⟩ : syracuseStep 2100999 = 3151499) B3151499
theorem B2363629 : Blo 2099435 2363629 := bbase (se 3 (by rfl) ⟨443180, by rfl⟩ : syracuseStep 2363629 = 886361) (by norm_num)
theorem B3151505 : Blo 2099435 3151505 := bstep (se 2 (by rfl) ⟨1181814, by rfl⟩ : syracuseStep 3151505 = 2363629) B2363629
theorem B2101003 : Blo 2099435 2101003 := bstep (se 1 (by rfl) ⟨1575752, by rfl⟩ : syracuseStep 2101003 = 3151505) B3151505
theorem B7090901 : Blo 2099435 7090901 := bbase (se 7 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 7090901 = 166193) (by norm_num)
theorem B4727267 : Blo 2099435 4727267 := bstep (se 1 (by rfl) ⟨3545450, by rfl⟩ : syracuseStep 4727267 = 7090901) B7090901
theorem B3151511 : Blo 2099435 3151511 := bstep (se 1 (by rfl) ⟨2363633, by rfl⟩ : syracuseStep 3151511 = 4727267) B4727267
theorem B2101007 : Blo 2099435 2101007 := bstep (se 1 (by rfl) ⟨1575755, by rfl⟩ : syracuseStep 2101007 = 3151511) B3151511
theorem B3151517 : Blo 2099435 3151517 := bbase (se 3 (by rfl) ⟨590909, by rfl⟩ : syracuseStep 3151517 = 1181819) (by norm_num)
theorem B2101011 : Blo 2099435 2101011 := bstep (se 1 (by rfl) ⟨1575758, by rfl⟩ : syracuseStep 2101011 = 3151517) B3151517
theorem B4727285 : Blo 2099435 4727285 := bbase (se 5 (by rfl) ⟨221591, by rfl⟩ : syracuseStep 4727285 = 443183) (by norm_num)
theorem B3151523 : Blo 2099435 3151523 := bstep (se 1 (by rfl) ⟨2363642, by rfl⟩ : syracuseStep 3151523 = 4727285) B4727285
theorem B2101015 : Blo 2099435 2101015 := bstep (se 1 (by rfl) ⟨1575761, by rfl⟩ : syracuseStep 2101015 = 3151523) B3151523
theorem B3593845 : Blo 2099435 3593845 := bbase (se 5 (by rfl) ⟨168461, by rfl⟩ : syracuseStep 3593845 = 336923) (by norm_num)
theorem B4791793 : Blo 2099435 4791793 := bstep (se 2 (by rfl) ⟨1796922, by rfl⟩ : syracuseStep 4791793 = 3593845) B3593845
theorem B6389057 : Blo 2099435 6389057 := bstep (se 2 (by rfl) ⟨2395896, by rfl⟩ : syracuseStep 6389057 = 4791793) B4791793
theorem B4259371 : Blo 2099435 4259371 := bstep (se 1 (by rfl) ⟨3194528, by rfl⟩ : syracuseStep 4259371 = 6389057) B6389057
theorem B5679161 : Blo 2099435 5679161 := bstep (se 2 (by rfl) ⟨2129685, by rfl⟩ : syracuseStep 5679161 = 4259371) B4259371
theorem B3786107 : Blo 2099435 3786107 := bstep (se 1 (by rfl) ⟨2839580, by rfl⟩ : syracuseStep 3786107 = 5679161) B5679161
theorem B40385141 : Blo 2099435 40385141 := bstep (se 5 (by rfl) ⟨1893053, by rfl⟩ : syracuseStep 40385141 = 3786107) B3786107
theorem B26923427 : Blo 2099435 26923427 := bstep (se 1 (by rfl) ⟨20192570, by rfl⟩ : syracuseStep 26923427 = 40385141) B40385141
theorem B17948951 : Blo 2099435 17948951 := bstep (se 1 (by rfl) ⟨13461713, by rfl⟩ : syracuseStep 17948951 = 26923427) B26923427
theorem B11965967 : Blo 2099435 11965967 := bstep (se 1 (by rfl) ⟨8974475, by rfl⟩ : syracuseStep 11965967 = 17948951) B17948951
theorem B7977311 : Blo 2099435 7977311 := bstep (se 1 (by rfl) ⟨5982983, by rfl⟩ : syracuseStep 7977311 = 11965967) B11965967
theorem B5318207 : Blo 2099435 5318207 := bstep (se 1 (by rfl) ⟨3988655, by rfl⟩ : syracuseStep 5318207 = 7977311) B7977311
theorem B3545471 : Blo 2099435 3545471 := bstep (se 1 (by rfl) ⟨2659103, by rfl⟩ : syracuseStep 3545471 = 5318207) B5318207
theorem B2363647 : Blo 2099435 2363647 := bstep (se 1 (by rfl) ⟨1772735, by rfl⟩ : syracuseStep 2363647 = 3545471) B3545471
theorem B3151529 : Blo 2099435 3151529 := bstep (se 2 (by rfl) ⟨1181823, by rfl⟩ : syracuseStep 3151529 = 2363647) B2363647
theorem B2101019 : Blo 2099435 2101019 := bstep (se 1 (by rfl) ⟨1575764, by rfl⟩ : syracuseStep 2101019 = 3151529) B3151529
theorem B5679173 : Blo 2099435 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B3786115 : Blo 2099435 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B5048153 : Blo 2099435 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3365435 : Blo 2099435 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B2243623 : Blo 2099435 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2991497 : Blo 2099435 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B7977325 : Blo 2099435 7977325 := bstep (se 3 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 7977325 = 2991497) B2991497
theorem B10636433 : Blo 2099435 10636433 := bstep (se 2 (by rfl) ⟨3988662, by rfl⟩ : syracuseStep 10636433 = 7977325) B7977325
theorem B7090955 : Blo 2099435 7090955 := bstep (se 1 (by rfl) ⟨5318216, by rfl⟩ : syracuseStep 7090955 = 10636433) B10636433
theorem B4727303 : Blo 2099435 4727303 := bstep (se 1 (by rfl) ⟨3545477, by rfl⟩ : syracuseStep 4727303 = 7090955) B7090955
theorem B3151535 : Blo 2099435 3151535 := bstep (se 1 (by rfl) ⟨2363651, by rfl⟩ : syracuseStep 3151535 = 4727303) B4727303
theorem B2101023 : Blo 2099435 2101023 := bstep (se 1 (by rfl) ⟨1575767, by rfl⟩ : syracuseStep 2101023 = 3151535) B3151535
theorem B3151541 : Blo 2099435 3151541 := bbase (se 5 (by rfl) ⟨147728, by rfl⟩ : syracuseStep 3151541 = 295457) (by norm_num)
theorem B2101027 : Blo 2099435 2101027 := bstep (se 1 (by rfl) ⟨1575770, by rfl⟩ : syracuseStep 2101027 = 3151541) B3151541
theorem B5318237 : Blo 2099435 5318237 := bbase (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) (by norm_num)
theorem B3545491 : Blo 2099435 3545491 := bstep (se 1 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 3545491 = 5318237) B5318237
theorem B4727321 : Blo 2099435 4727321 := bstep (se 2 (by rfl) ⟨1772745, by rfl⟩ : syracuseStep 4727321 = 3545491) B3545491
theorem B3151547 : Blo 2099435 3151547 := bstep (se 1 (by rfl) ⟨2363660, by rfl⟩ : syracuseStep 3151547 = 4727321) B4727321
theorem B2101031 : Blo 2099435 2101031 := bstep (se 1 (by rfl) ⟨1575773, by rfl⟩ : syracuseStep 2101031 = 3151547) B3151547
theorem B2363665 : Blo 2099435 2363665 := bbase (se 2 (by rfl) ⟨886374, by rfl⟩ : syracuseStep 2363665 = 1772749) (by norm_num)
theorem B3151553 : Blo 2099435 3151553 := bstep (se 2 (by rfl) ⟨1181832, by rfl⟩ : syracuseStep 3151553 = 2363665) B2363665
theorem B2101035 : Blo 2099435 2101035 := bstep (se 1 (by rfl) ⟨1575776, by rfl⟩ : syracuseStep 2101035 = 3151553) B3151553
theorem B3988693 : Blo 2099435 3988693 := bbase (se 7 (by rfl) ⟨46742, by rfl⟩ : syracuseStep 3988693 = 93485) (by norm_num)
theorem B5318257 : Blo 2099435 5318257 := bstep (se 2 (by rfl) ⟨1994346, by rfl⟩ : syracuseStep 5318257 = 3988693) B3988693
theorem B7091009 : Blo 2099435 7091009 := bstep (se 2 (by rfl) ⟨2659128, by rfl⟩ : syracuseStep 7091009 = 5318257) B5318257
theorem B4727339 : Blo 2099435 4727339 := bstep (se 1 (by rfl) ⟨3545504, by rfl⟩ : syracuseStep 4727339 = 7091009) B7091009
theorem B3151559 : Blo 2099435 3151559 := bstep (se 1 (by rfl) ⟨2363669, by rfl⟩ : syracuseStep 3151559 = 4727339) B4727339
theorem B2101039 : Blo 2099435 2101039 := bstep (se 1 (by rfl) ⟨1575779, by rfl⟩ : syracuseStep 2101039 = 3151559) B3151559
theorem B3151565 : Blo 2099435 3151565 := bbase (se 3 (by rfl) ⟨590918, by rfl⟩ : syracuseStep 3151565 = 1181837) (by norm_num)
theorem B2101043 : Blo 2099435 2101043 := bstep (se 1 (by rfl) ⟨1575782, by rfl⟩ : syracuseStep 2101043 = 3151565) B3151565
theorem B4727357 : Blo 2099435 4727357 := bbase (se 3 (by rfl) ⟨886379, by rfl⟩ : syracuseStep 4727357 = 1772759) (by norm_num)
theorem B3151571 : Blo 2099435 3151571 := bstep (se 1 (by rfl) ⟨2363678, by rfl⟩ : syracuseStep 3151571 = 4727357) B4727357
theorem B2101047 : Blo 2099435 2101047 := bstep (se 1 (by rfl) ⟨1575785, by rfl⟩ : syracuseStep 2101047 = 3151571) B3151571
theorem B3545525 : Blo 2099435 3545525 := bbase (se 5 (by rfl) ⟨166196, by rfl⟩ : syracuseStep 3545525 = 332393) (by norm_num)
theorem B2363683 : Blo 2099435 2363683 := bstep (se 1 (by rfl) ⟨1772762, by rfl⟩ : syracuseStep 2363683 = 3545525) B3545525
theorem B3151577 : Blo 2099435 3151577 := bstep (se 2 (by rfl) ⟨1181841, by rfl⟩ : syracuseStep 3151577 = 2363683) B2363683
theorem B2101051 : Blo 2099435 2101051 := bstep (se 1 (by rfl) ⟨1575788, by rfl⟩ : syracuseStep 2101051 = 3151577) B3151577
theorem B2243657 : Blo 2099435 2243657 := bbase (se 2 (by rfl) ⟨841371, by rfl⟩ : syracuseStep 2243657 = 1682743) (by norm_num)
theorem B5983085 : Blo 2099435 5983085 := bstep (se 3 (by rfl) ⟨1121828, by rfl⟩ : syracuseStep 5983085 = 2243657) B2243657
theorem B15954893 : Blo 2099435 15954893 := bstep (se 3 (by rfl) ⟨2991542, by rfl⟩ : syracuseStep 15954893 = 5983085) B5983085
theorem B10636595 : Blo 2099435 10636595 := bstep (se 1 (by rfl) ⟨7977446, by rfl⟩ : syracuseStep 10636595 = 15954893) B15954893
theorem B7091063 : Blo 2099435 7091063 := bstep (se 1 (by rfl) ⟨5318297, by rfl⟩ : syracuseStep 7091063 = 10636595) B10636595
theorem B4727375 : Blo 2099435 4727375 := bstep (se 1 (by rfl) ⟨3545531, by rfl⟩ : syracuseStep 4727375 = 7091063) B7091063
theorem B3151583 : Blo 2099435 3151583 := bstep (se 1 (by rfl) ⟨2363687, by rfl⟩ : syracuseStep 3151583 = 4727375) B4727375
theorem B2101055 : Blo 2099435 2101055 := bstep (se 1 (by rfl) ⟨1575791, by rfl⟩ : syracuseStep 2101055 = 3151583) B3151583
theorem B3151589 : Blo 2099435 3151589 := bbase (se 4 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 3151589 = 590923) (by norm_num)
theorem B2101059 : Blo 2099435 2101059 := bstep (se 1 (by rfl) ⟨1575794, by rfl⟩ : syracuseStep 2101059 = 3151589) B3151589
theorem B5983109 : Blo 2099435 5983109 := bbase (se 4 (by rfl) ⟨560916, by rfl⟩ : syracuseStep 5983109 = 1121833) (by norm_num)
theorem B3988739 : Blo 2099435 3988739 := bstep (se 1 (by rfl) ⟨2991554, by rfl⟩ : syracuseStep 3988739 = 5983109) B5983109
theorem B2659159 : Blo 2099435 2659159 := bstep (se 1 (by rfl) ⟨1994369, by rfl⟩ : syracuseStep 2659159 = 3988739) B3988739
theorem B3545545 : Blo 2099435 3545545 := bstep (se 2 (by rfl) ⟨1329579, by rfl⟩ : syracuseStep 3545545 = 2659159) B2659159
theorem B4727393 : Blo 2099435 4727393 := bstep (se 2 (by rfl) ⟨1772772, by rfl⟩ : syracuseStep 4727393 = 3545545) B3545545
theorem B3151595 : Blo 2099435 3151595 := bstep (se 1 (by rfl) ⟨2363696, by rfl⟩ : syracuseStep 3151595 = 4727393) B4727393
theorem B2101063 : Blo 2099435 2101063 := bstep (se 1 (by rfl) ⟨1575797, by rfl⟩ : syracuseStep 2101063 = 3151595) B3151595
theorem B2363701 : Blo 2099435 2363701 := bbase (se 5 (by rfl) ⟨110798, by rfl⟩ : syracuseStep 2363701 = 221597) (by norm_num)
theorem B3151601 : Blo 2099435 3151601 := bstep (se 2 (by rfl) ⟨1181850, by rfl⟩ : syracuseStep 3151601 = 2363701) B2363701
theorem B2101067 : Blo 2099435 2101067 := bstep (se 1 (by rfl) ⟨1575800, by rfl⟩ : syracuseStep 2101067 = 3151601) B3151601
theorem B2659169 : Blo 2099435 2659169 := bbase (se 2 (by rfl) ⟨997188, by rfl⟩ : syracuseStep 2659169 = 1994377) (by norm_num)
theorem B7091117 : Blo 2099435 7091117 := bstep (se 3 (by rfl) ⟨1329584, by rfl⟩ : syracuseStep 7091117 = 2659169) B2659169
theorem B4727411 : Blo 2099435 4727411 := bstep (se 1 (by rfl) ⟨3545558, by rfl⟩ : syracuseStep 4727411 = 7091117) B7091117
theorem B3151607 : Blo 2099435 3151607 := bstep (se 1 (by rfl) ⟨2363705, by rfl⟩ : syracuseStep 3151607 = 4727411) B4727411
theorem B2101071 : Blo 2099435 2101071 := bstep (se 1 (by rfl) ⟨1575803, by rfl⟩ : syracuseStep 2101071 = 3151607) B3151607
theorem B3151613 : Blo 2099435 3151613 := bbase (se 3 (by rfl) ⟨590927, by rfl⟩ : syracuseStep 3151613 = 1181855) (by norm_num)
theorem B2101075 : Blo 2099435 2101075 := bstep (se 1 (by rfl) ⟨1575806, by rfl⟩ : syracuseStep 2101075 = 3151613) B3151613
theorem B4727429 : Blo 2099435 4727429 := bbase (se 4 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 4727429 = 886393) (by norm_num)
theorem B3151619 : Blo 2099435 3151619 := bstep (se 1 (by rfl) ⟨2363714, by rfl⟩ : syracuseStep 3151619 = 4727429) B4727429
theorem B2101079 : Blo 2099435 2101079 := bstep (se 1 (by rfl) ⟨1575809, by rfl⟩ : syracuseStep 2101079 = 3151619) B3151619
theorem B3642989 : Blo 2099435 3642989 := bbase (se 3 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 3642989 = 1366121) (by norm_num)
theorem B9714637 : Blo 2099435 9714637 := bstep (se 3 (by rfl) ⟨1821494, by rfl⟩ : syracuseStep 9714637 = 3642989) B3642989
theorem B51811397 : Blo 2099435 51811397 := bstep (se 4 (by rfl) ⟨4857318, by rfl⟩ : syracuseStep 51811397 = 9714637) B9714637
theorem B34540931 : Blo 2099435 34540931 := bstep (se 1 (by rfl) ⟨25905698, by rfl⟩ : syracuseStep 34540931 = 51811397) B51811397
theorem B23027287 : Blo 2099435 23027287 := bstep (se 1 (by rfl) ⟨17270465, by rfl⟩ : syracuseStep 23027287 = 34540931) B34540931
theorem B30703049 : Blo 2099435 30703049 := bstep (se 2 (by rfl) ⟨11513643, by rfl⟩ : syracuseStep 30703049 = 23027287) B23027287
theorem B20468699 : Blo 2099435 20468699 := bstep (se 1 (by rfl) ⟨15351524, by rfl⟩ : syracuseStep 20468699 = 30703049) B30703049
theorem B13645799 : Blo 2099435 13645799 := bstep (se 1 (by rfl) ⟨10234349, by rfl⟩ : syracuseStep 13645799 = 20468699) B20468699
theorem B9097199 : Blo 2099435 9097199 := bstep (se 1 (by rfl) ⟨6822899, by rfl⟩ : syracuseStep 9097199 = 13645799) B13645799
theorem B6064799 : Blo 2099435 6064799 := bstep (se 1 (by rfl) ⟨4548599, by rfl⟩ : syracuseStep 6064799 = 9097199) B9097199
theorem B16172797 : Blo 2099435 16172797 := bstep (se 3 (by rfl) ⟨3032399, by rfl⟩ : syracuseStep 16172797 = 6064799) B6064799
theorem B21563729 : Blo 2099435 21563729 := bstep (se 2 (by rfl) ⟨8086398, by rfl⟩ : syracuseStep 21563729 = 16172797) B16172797
theorem B14375819 : Blo 2099435 14375819 := bstep (se 1 (by rfl) ⟨10781864, by rfl⟩ : syracuseStep 14375819 = 21563729) B21563729
theorem B9583879 : Blo 2099435 9583879 := bstep (se 1 (by rfl) ⟨7187909, by rfl⟩ : syracuseStep 9583879 = 14375819) B14375819
theorem B12778505 : Blo 2099435 12778505 := bstep (se 2 (by rfl) ⟨4791939, by rfl⟩ : syracuseStep 12778505 = 9583879) B9583879
theorem B8519003 : Blo 2099435 8519003 := bstep (se 1 (by rfl) ⟨6389252, by rfl⟩ : syracuseStep 8519003 = 12778505) B12778505
theorem B5679335 : Blo 2099435 5679335 := bstep (se 1 (by rfl) ⟨4259501, by rfl⟩ : syracuseStep 5679335 = 8519003) B8519003
theorem B15144893 : Blo 2099435 15144893 := bstep (se 3 (by rfl) ⟨2839667, by rfl⟩ : syracuseStep 15144893 = 5679335) B5679335
theorem B10096595 : Blo 2099435 10096595 := bstep (se 1 (by rfl) ⟨7572446, by rfl⟩ : syracuseStep 10096595 = 15144893) B15144893
theorem B6731063 : Blo 2099435 6731063 := bstep (se 1 (by rfl) ⟨5048297, by rfl⟩ : syracuseStep 6731063 = 10096595) B10096595
theorem B4487375 : Blo 2099435 4487375 := bstep (se 1 (by rfl) ⟨3365531, by rfl⟩ : syracuseStep 4487375 = 6731063) B6731063
theorem B2991583 : Blo 2099435 2991583 := bstep (se 1 (by rfl) ⟨2243687, by rfl⟩ : syracuseStep 2991583 = 4487375) B4487375
theorem B3988777 : Blo 2099435 3988777 := bstep (se 2 (by rfl) ⟨1495791, by rfl⟩ : syracuseStep 3988777 = 2991583) B2991583
theorem B5318369 : Blo 2099435 5318369 := bstep (se 2 (by rfl) ⟨1994388, by rfl⟩ : syracuseStep 5318369 = 3988777) B3988777
theorem B3545579 : Blo 2099435 3545579 := bstep (se 1 (by rfl) ⟨2659184, by rfl⟩ : syracuseStep 3545579 = 5318369) B5318369
theorem B2363719 : Blo 2099435 2363719 := bstep (se 1 (by rfl) ⟨1772789, by rfl⟩ : syracuseStep 2363719 = 3545579) B3545579
theorem B3151625 : Blo 2099435 3151625 := bstep (se 2 (by rfl) ⟨1181859, by rfl⟩ : syracuseStep 3151625 = 2363719) B2363719
theorem B2101083 : Blo 2099435 2101083 := bstep (se 1 (by rfl) ⟨1575812, by rfl⟩ : syracuseStep 2101083 = 3151625) B3151625
theorem B10636757 : Blo 2099435 10636757 := bbase (se 7 (by rfl) ⟨124649, by rfl⟩ : syracuseStep 10636757 = 249299) (by norm_num)
theorem B7091171 : Blo 2099435 7091171 := bstep (se 1 (by rfl) ⟨5318378, by rfl⟩ : syracuseStep 7091171 = 10636757) B10636757
theorem B4727447 : Blo 2099435 4727447 := bstep (se 1 (by rfl) ⟨3545585, by rfl⟩ : syracuseStep 4727447 = 7091171) B7091171
theorem B3151631 : Blo 2099435 3151631 := bstep (se 1 (by rfl) ⟨2363723, by rfl⟩ : syracuseStep 3151631 = 4727447) B4727447
theorem B2101087 : Blo 2099435 2101087 := bstep (se 1 (by rfl) ⟨1575815, by rfl⟩ : syracuseStep 2101087 = 3151631) B3151631
theorem B3151637 : Blo 2099435 3151637 := bbase (se 6 (by rfl) ⟨73866, by rfl⟩ : syracuseStep 3151637 = 147733) (by norm_num)
theorem B2101091 : Blo 2099435 2101091 := bstep (se 1 (by rfl) ⟨1575818, by rfl⟩ : syracuseStep 2101091 = 3151637) B3151637
theorem B9221365 : Blo 2099435 9221365 := bbase (se 5 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 9221365 = 864503) (by norm_num)
theorem B12295153 : Blo 2099435 12295153 := bstep (se 2 (by rfl) ⟨4610682, by rfl⟩ : syracuseStep 12295153 = 9221365) B9221365
theorem B16393537 : Blo 2099435 16393537 := bstep (se 2 (by rfl) ⟨6147576, by rfl⟩ : syracuseStep 16393537 = 12295153) B12295153
theorem B21858049 : Blo 2099435 21858049 := bstep (se 2 (by rfl) ⟨8196768, by rfl⟩ : syracuseStep 21858049 = 16393537) B16393537
theorem B29144065 : Blo 2099435 29144065 := bstep (se 2 (by rfl) ⟨10929024, by rfl⟩ : syracuseStep 29144065 = 21858049) B21858049
theorem B38858753 : Blo 2099435 38858753 := bstep (se 2 (by rfl) ⟨14572032, by rfl⟩ : syracuseStep 38858753 = 29144065) B29144065
theorem B25905835 : Blo 2099435 25905835 := bstep (se 1 (by rfl) ⟨19429376, by rfl⟩ : syracuseStep 25905835 = 38858753) B38858753
theorem B34541113 : Blo 2099435 34541113 := bstep (se 2 (by rfl) ⟨12952917, by rfl⟩ : syracuseStep 34541113 = 25905835) B25905835
theorem B46054817 : Blo 2099435 46054817 := bstep (se 2 (by rfl) ⟨17270556, by rfl⟩ : syracuseStep 46054817 = 34541113) B34541113
theorem B30703211 : Blo 2099435 30703211 := bstep (se 1 (by rfl) ⟨23027408, by rfl⟩ : syracuseStep 30703211 = 46054817) B46054817
theorem B20468807 : Blo 2099435 20468807 := bstep (se 1 (by rfl) ⟨15351605, by rfl⟩ : syracuseStep 20468807 = 30703211) B30703211
theorem B13645871 : Blo 2099435 13645871 := bstep (se 1 (by rfl) ⟨10234403, by rfl⟩ : syracuseStep 13645871 = 20468807) B20468807
theorem B9097247 : Blo 2099435 9097247 := bstep (se 1 (by rfl) ⟨6822935, by rfl⟩ : syracuseStep 9097247 = 13645871) B13645871
theorem B6064831 : Blo 2099435 6064831 := bstep (se 1 (by rfl) ⟨4548623, by rfl⟩ : syracuseStep 6064831 = 9097247) B9097247
theorem B8086441 : Blo 2099435 8086441 := bstep (se 2 (by rfl) ⟨3032415, by rfl⟩ : syracuseStep 8086441 = 6064831) B6064831
theorem B10781921 : Blo 2099435 10781921 := bstep (se 2 (by rfl) ⟨4043220, by rfl⟩ : syracuseStep 10781921 = 8086441) B8086441
theorem B28751789 : Blo 2099435 28751789 := bstep (se 3 (by rfl) ⟨5390960, by rfl⟩ : syracuseStep 28751789 = 10781921) B10781921
theorem B19167859 : Blo 2099435 19167859 := bstep (se 1 (by rfl) ⟨14375894, by rfl⟩ : syracuseStep 19167859 = 28751789) B28751789
theorem B102228581 : Blo 2099435 102228581 := bstep (se 4 (by rfl) ⟨9583929, by rfl⟩ : syracuseStep 102228581 = 19167859) B19167859
theorem B68152387 : Blo 2099435 68152387 := bstep (se 1 (by rfl) ⟨51114290, by rfl⟩ : syracuseStep 68152387 = 102228581) B102228581
theorem B90869849 : Blo 2099435 90869849 := bstep (se 2 (by rfl) ⟨34076193, by rfl⟩ : syracuseStep 90869849 = 68152387) B68152387
theorem B60579899 : Blo 2099435 60579899 := bstep (se 1 (by rfl) ⟨45434924, by rfl⟩ : syracuseStep 60579899 = 90869849) B90869849
theorem B40386599 : Blo 2099435 40386599 := bstep (se 1 (by rfl) ⟨30289949, by rfl⟩ : syracuseStep 40386599 = 60579899) B60579899
theorem B26924399 : Blo 2099435 26924399 := bstep (se 1 (by rfl) ⟨20193299, by rfl⟩ : syracuseStep 26924399 = 40386599) B40386599
theorem B17949599 : Blo 2099435 17949599 := bstep (se 1 (by rfl) ⟨13462199, by rfl⟩ : syracuseStep 17949599 = 26924399) B26924399
theorem B11966399 : Blo 2099435 11966399 := bstep (se 1 (by rfl) ⟨8974799, by rfl⟩ : syracuseStep 11966399 = 17949599) B17949599
theorem B7977599 : Blo 2099435 7977599 := bstep (se 1 (by rfl) ⟨5983199, by rfl⟩ : syracuseStep 7977599 = 11966399) B11966399
theorem B5318399 : Blo 2099435 5318399 := bstep (se 1 (by rfl) ⟨3988799, by rfl⟩ : syracuseStep 5318399 = 7977599) B7977599
theorem B3545599 : Blo 2099435 3545599 := bstep (se 1 (by rfl) ⟨2659199, by rfl⟩ : syracuseStep 3545599 = 5318399) B5318399
theorem B4727465 : Blo 2099435 4727465 := bstep (se 2 (by rfl) ⟨1772799, by rfl⟩ : syracuseStep 4727465 = 3545599) B3545599
theorem B3151643 : Blo 2099435 3151643 := bstep (se 1 (by rfl) ⟨2363732, by rfl⟩ : syracuseStep 3151643 = 4727465) B4727465
theorem B2101095 : Blo 2099435 2101095 := bstep (se 1 (by rfl) ⟨1575821, by rfl⟩ : syracuseStep 2101095 = 3151643) B3151643
theorem B2363737 : Blo 2099435 2363737 := bbase (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) (by norm_num)
theorem B3151649 : Blo 2099435 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B2101099 : Blo 2099435 2101099 := bstep (se 1 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 2101099 = 3151649) B3151649
theorem B2395993 : Blo 2099435 2395993 := bbase (se 2 (by rfl) ⟨898497, by rfl⟩ : syracuseStep 2395993 = 1796995) (by norm_num)
theorem B3194657 : Blo 2099435 3194657 := bstep (se 2 (by rfl) ⟨1197996, by rfl⟩ : syracuseStep 3194657 = 2395993) B2395993
theorem B2129771 : Blo 2099435 2129771 := bstep (se 1 (by rfl) ⟨1597328, by rfl⟩ : syracuseStep 2129771 = 3194657) B3194657
theorem B5679389 : Blo 2099435 5679389 := bstep (se 3 (by rfl) ⟨1064885, by rfl⟩ : syracuseStep 5679389 = 2129771) B2129771
theorem B3786259 : Blo 2099435 3786259 := bstep (se 1 (by rfl) ⟨2839694, by rfl⟩ : syracuseStep 3786259 = 5679389) B5679389
theorem B5048345 : Blo 2099435 5048345 := bstep (se 2 (by rfl) ⟨1893129, by rfl⟩ : syracuseStep 5048345 = 3786259) B3786259
theorem B3365563 : Blo 2099435 3365563 := bstep (se 1 (by rfl) ⟨2524172, by rfl⟩ : syracuseStep 3365563 = 5048345) B5048345
theorem B4487417 : Blo 2099435 4487417 := bstep (se 2 (by rfl) ⟨1682781, by rfl⟩ : syracuseStep 4487417 = 3365563) B3365563
theorem B2991611 : Blo 2099435 2991611 := bstep (se 1 (by rfl) ⟨2243708, by rfl⟩ : syracuseStep 2991611 = 4487417) B4487417
theorem B7977629 : Blo 2099435 7977629 := bstep (se 3 (by rfl) ⟨1495805, by rfl⟩ : syracuseStep 7977629 = 2991611) B2991611
theorem B5318419 : Blo 2099435 5318419 := bstep (se 1 (by rfl) ⟨3988814, by rfl⟩ : syracuseStep 5318419 = 7977629) B7977629
theorem B7091225 : Blo 2099435 7091225 := bstep (se 2 (by rfl) ⟨2659209, by rfl⟩ : syracuseStep 7091225 = 5318419) B5318419
theorem B4727483 : Blo 2099435 4727483 := bstep (se 1 (by rfl) ⟨3545612, by rfl⟩ : syracuseStep 4727483 = 7091225) B7091225
theorem B3151655 : Blo 2099435 3151655 := bstep (se 1 (by rfl) ⟨2363741, by rfl⟩ : syracuseStep 3151655 = 4727483) B4727483
theorem B2101103 : Blo 2099435 2101103 := bstep (se 1 (by rfl) ⟨1575827, by rfl⟩ : syracuseStep 2101103 = 3151655) B3151655
theorem B3151661 : Blo 2099435 3151661 := bbase (se 3 (by rfl) ⟨590936, by rfl⟩ : syracuseStep 3151661 = 1181873) (by norm_num)
theorem B2101107 : Blo 2099435 2101107 := bstep (se 1 (by rfl) ⟨1575830, by rfl⟩ : syracuseStep 2101107 = 3151661) B3151661
theorem B4727501 : Blo 2099435 4727501 := bbase (se 3 (by rfl) ⟨886406, by rfl⟩ : syracuseStep 4727501 = 1772813) (by norm_num)
theorem B3151667 : Blo 2099435 3151667 := bstep (se 1 (by rfl) ⟨2363750, by rfl⟩ : syracuseStep 3151667 = 4727501) B4727501
theorem B2101111 : Blo 2099435 2101111 := bstep (se 1 (by rfl) ⟨1575833, by rfl⟩ : syracuseStep 2101111 = 3151667) B3151667
theorem B2659225 : Blo 2099435 2659225 := bbase (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) (by norm_num)
theorem B3545633 : Blo 2099435 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B2363755 : Blo 2099435 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B3151673 : Blo 2099435 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B2101115 : Blo 2099435 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B8974901 : Blo 2099435 8974901 := bbase (se 5 (by rfl) ⟨420698, by rfl⟩ : syracuseStep 8974901 = 841397) (by norm_num)
theorem B23933069 : Blo 2099435 23933069 := bstep (se 3 (by rfl) ⟨4487450, by rfl⟩ : syracuseStep 23933069 = 8974901) B8974901
theorem B15955379 : Blo 2099435 15955379 := bstep (se 1 (by rfl) ⟨11966534, by rfl⟩ : syracuseStep 15955379 = 23933069) B23933069
theorem B10636919 : Blo 2099435 10636919 := bstep (se 1 (by rfl) ⟨7977689, by rfl⟩ : syracuseStep 10636919 = 15955379) B15955379
theorem B7091279 : Blo 2099435 7091279 := bstep (se 1 (by rfl) ⟨5318459, by rfl⟩ : syracuseStep 7091279 = 10636919) B10636919
theorem B4727519 : Blo 2099435 4727519 := bstep (se 1 (by rfl) ⟨3545639, by rfl⟩ : syracuseStep 4727519 = 7091279) B7091279
theorem B3151679 : Blo 2099435 3151679 := bstep (se 1 (by rfl) ⟨2363759, by rfl⟩ : syracuseStep 3151679 = 4727519) B4727519
theorem B2101119 : Blo 2099435 2101119 := bstep (se 1 (by rfl) ⟨1575839, by rfl⟩ : syracuseStep 2101119 = 3151679) B3151679
theorem B3151685 : Blo 2099435 3151685 := bbase (se 4 (by rfl) ⟨295470, by rfl⟩ : syracuseStep 3151685 = 590941) (by norm_num)
theorem B2101123 : Blo 2099435 2101123 := bstep (se 1 (by rfl) ⟨1575842, by rfl⟩ : syracuseStep 2101123 = 3151685) B3151685
theorem B3545653 : Blo 2099435 3545653 := bbase (se 5 (by rfl) ⟨166202, by rfl⟩ : syracuseStep 3545653 = 332405) (by norm_num)
theorem B4727537 : Blo 2099435 4727537 := bstep (se 2 (by rfl) ⟨1772826, by rfl⟩ : syracuseStep 4727537 = 3545653) B3545653
theorem B3151691 : Blo 2099435 3151691 := bstep (se 1 (by rfl) ⟨2363768, by rfl⟩ : syracuseStep 3151691 = 4727537) B4727537
theorem B2101127 : Blo 2099435 2101127 := bstep (se 1 (by rfl) ⟨1575845, by rfl⟩ : syracuseStep 2101127 = 3151691) B3151691
theorem B2363773 : Blo 2099435 2363773 := bbase (se 3 (by rfl) ⟨443207, by rfl⟩ : syracuseStep 2363773 = 886415) (by norm_num)
theorem B3151697 : Blo 2099435 3151697 := bstep (se 2 (by rfl) ⟨1181886, by rfl⟩ : syracuseStep 3151697 = 2363773) B2363773
theorem B2101131 : Blo 2099435 2101131 := bstep (se 1 (by rfl) ⟨1575848, by rfl⟩ : syracuseStep 2101131 = 3151697) B3151697
theorem B7091333 : Blo 2099435 7091333 := bbase (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) (by norm_num)
theorem B4727555 : Blo 2099435 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B3151703 : Blo 2099435 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B2101135 : Blo 2099435 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B3151709 : Blo 2099435 3151709 := bbase (se 3 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 3151709 = 1181891) (by norm_num)
theorem B2101139 : Blo 2099435 2101139 := bstep (se 1 (by rfl) ⟨1575854, by rfl⟩ : syracuseStep 2101139 = 3151709) B3151709
theorem B4727573 : Blo 2099435 4727573 := bbase (se 6 (by rfl) ⟨110802, by rfl⟩ : syracuseStep 4727573 = 221605) (by norm_num)
theorem B3151715 : Blo 2099435 3151715 := bstep (se 1 (by rfl) ⟨2363786, by rfl⟩ : syracuseStep 3151715 = 4727573) B4727573
theorem B2101143 : Blo 2099435 2101143 := bstep (se 1 (by rfl) ⟨1575857, by rfl⟩ : syracuseStep 2101143 = 3151715) B3151715
theorem B7977797 : Blo 2099435 7977797 := bbase (se 4 (by rfl) ⟨747918, by rfl⟩ : syracuseStep 7977797 = 1495837) (by norm_num)
theorem B5318531 : Blo 2099435 5318531 := bstep (se 1 (by rfl) ⟨3988898, by rfl⟩ : syracuseStep 5318531 = 7977797) B7977797
theorem B3545687 : Blo 2099435 3545687 := bstep (se 1 (by rfl) ⟨2659265, by rfl⟩ : syracuseStep 3545687 = 5318531) B5318531
theorem B2363791 : Blo 2099435 2363791 := bstep (se 1 (by rfl) ⟨1772843, by rfl⟩ : syracuseStep 2363791 = 3545687) B3545687
theorem B3151721 : Blo 2099435 3151721 := bstep (se 2 (by rfl) ⟨1181895, by rfl⟩ : syracuseStep 3151721 = 2363791) B2363791
theorem B2101147 : Blo 2099435 2101147 := bstep (se 1 (by rfl) ⟨1575860, by rfl⟩ : syracuseStep 2101147 = 3151721) B3151721
theorem B8086661 : Blo 2099435 8086661 := bbase (se 4 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 8086661 = 1516249) (by norm_num)
theorem B5391107 : Blo 2099435 5391107 := bstep (se 1 (by rfl) ⟨4043330, by rfl⟩ : syracuseStep 5391107 = 8086661) B8086661
theorem B3594071 : Blo 2099435 3594071 := bstep (se 1 (by rfl) ⟨2695553, by rfl⟩ : syracuseStep 3594071 = 5391107) B5391107
theorem B2396047 : Blo 2099435 2396047 := bstep (se 1 (by rfl) ⟨1797035, by rfl⟩ : syracuseStep 2396047 = 3594071) B3594071
theorem B3194729 : Blo 2099435 3194729 := bstep (se 2 (by rfl) ⟨1198023, by rfl⟩ : syracuseStep 3194729 = 2396047) B2396047
theorem B2129819 : Blo 2099435 2129819 := bstep (se 1 (by rfl) ⟨1597364, by rfl⟩ : syracuseStep 2129819 = 3194729) B3194729
theorem B22718069 : Blo 2099435 22718069 := bstep (se 5 (by rfl) ⟨1064909, by rfl⟩ : syracuseStep 22718069 = 2129819) B2129819
theorem B15145379 : Blo 2099435 15145379 := bstep (se 1 (by rfl) ⟨11359034, by rfl⟩ : syracuseStep 15145379 = 22718069) B22718069
theorem B10096919 : Blo 2099435 10096919 := bstep (se 1 (by rfl) ⟨7572689, by rfl⟩ : syracuseStep 10096919 = 15145379) B15145379
theorem B6731279 : Blo 2099435 6731279 := bstep (se 1 (by rfl) ⟨5048459, by rfl⟩ : syracuseStep 6731279 = 10096919) B10096919
theorem B4487519 : Blo 2099435 4487519 := bstep (se 1 (by rfl) ⟨3365639, by rfl⟩ : syracuseStep 4487519 = 6731279) B6731279
theorem B11966717 : Blo 2099435 11966717 := bstep (se 3 (by rfl) ⟨2243759, by rfl⟩ : syracuseStep 11966717 = 4487519) B4487519
theorem B7977811 : Blo 2099435 7977811 := bstep (se 1 (by rfl) ⟨5983358, by rfl⟩ : syracuseStep 7977811 = 11966717) B11966717
theorem B10637081 : Blo 2099435 10637081 := bstep (se 2 (by rfl) ⟨3988905, by rfl⟩ : syracuseStep 10637081 = 7977811) B7977811
theorem B7091387 : Blo 2099435 7091387 := bstep (se 1 (by rfl) ⟨5318540, by rfl⟩ : syracuseStep 7091387 = 10637081) B10637081
theorem B4727591 : Blo 2099435 4727591 := bstep (se 1 (by rfl) ⟨3545693, by rfl⟩ : syracuseStep 4727591 = 7091387) B7091387
theorem B3151727 : Blo 2099435 3151727 := bstep (se 1 (by rfl) ⟨2363795, by rfl⟩ : syracuseStep 3151727 = 4727591) B4727591
theorem B2101151 : Blo 2099435 2101151 := bstep (se 1 (by rfl) ⟨1575863, by rfl⟩ : syracuseStep 2101151 = 3151727) B3151727
theorem B3151733 : Blo 2099435 3151733 := bbase (se 5 (by rfl) ⟨147737, by rfl⟩ : syracuseStep 3151733 = 295475) (by norm_num)
theorem B2101155 : Blo 2099435 2101155 := bstep (se 1 (by rfl) ⟨1575866, by rfl⟩ : syracuseStep 2101155 = 3151733) B3151733
theorem B3365653 : Blo 2099435 3365653 := bbase (se 6 (by rfl) ⟨78882, by rfl⟩ : syracuseStep 3365653 = 157765) (by norm_num)
theorem B4487537 : Blo 2099435 4487537 := bstep (se 2 (by rfl) ⟨1682826, by rfl⟩ : syracuseStep 4487537 = 3365653) B3365653
theorem B2991691 : Blo 2099435 2991691 := bstep (se 1 (by rfl) ⟨2243768, by rfl⟩ : syracuseStep 2991691 = 4487537) B4487537
theorem B3988921 : Blo 2099435 3988921 := bstep (se 2 (by rfl) ⟨1495845, by rfl⟩ : syracuseStep 3988921 = 2991691) B2991691
theorem B5318561 : Blo 2099435 5318561 := bstep (se 2 (by rfl) ⟨1994460, by rfl⟩ : syracuseStep 5318561 = 3988921) B3988921
theorem B3545707 : Blo 2099435 3545707 := bstep (se 1 (by rfl) ⟨2659280, by rfl⟩ : syracuseStep 3545707 = 5318561) B5318561
theorem B4727609 : Blo 2099435 4727609 := bstep (se 2 (by rfl) ⟨1772853, by rfl⟩ : syracuseStep 4727609 = 3545707) B3545707
theorem B3151739 : Blo 2099435 3151739 := bstep (se 1 (by rfl) ⟨2363804, by rfl⟩ : syracuseStep 3151739 = 4727609) B4727609
theorem B2101159 : Blo 2099435 2101159 := bstep (se 1 (by rfl) ⟨1575869, by rfl⟩ : syracuseStep 2101159 = 3151739) B3151739
theorem B2363809 : Blo 2099435 2363809 := bbase (se 2 (by rfl) ⟨886428, by rfl⟩ : syracuseStep 2363809 = 1772857) (by norm_num)
theorem B3151745 : Blo 2099435 3151745 := bstep (se 2 (by rfl) ⟨1181904, by rfl⟩ : syracuseStep 3151745 = 2363809) B2363809
theorem B2101163 : Blo 2099435 2101163 := bstep (se 1 (by rfl) ⟨1575872, by rfl⟩ : syracuseStep 2101163 = 3151745) B3151745
theorem B5318581 : Blo 2099435 5318581 := bbase (se 5 (by rfl) ⟨249308, by rfl⟩ : syracuseStep 5318581 = 498617) (by norm_num)
theorem B7091441 : Blo 2099435 7091441 := bstep (se 2 (by rfl) ⟨2659290, by rfl⟩ : syracuseStep 7091441 = 5318581) B5318581
theorem B4727627 : Blo 2099435 4727627 := bstep (se 1 (by rfl) ⟨3545720, by rfl⟩ : syracuseStep 4727627 = 7091441) B7091441
theorem B3151751 : Blo 2099435 3151751 := bstep (se 1 (by rfl) ⟨2363813, by rfl⟩ : syracuseStep 3151751 = 4727627) B4727627
theorem B2101167 : Blo 2099435 2101167 := bstep (se 1 (by rfl) ⟨1575875, by rfl⟩ : syracuseStep 2101167 = 3151751) B3151751
theorem B3151757 : Blo 2099435 3151757 := bbase (se 3 (by rfl) ⟨590954, by rfl⟩ : syracuseStep 3151757 = 1181909) (by norm_num)
theorem B2101171 : Blo 2099435 2101171 := bstep (se 1 (by rfl) ⟨1575878, by rfl⟩ : syracuseStep 2101171 = 3151757) B3151757
theorem B4727645 : Blo 2099435 4727645 := bbase (se 3 (by rfl) ⟨886433, by rfl⟩ : syracuseStep 4727645 = 1772867) (by norm_num)
theorem B3151763 : Blo 2099435 3151763 := bstep (se 1 (by rfl) ⟨2363822, by rfl⟩ : syracuseStep 3151763 = 4727645) B4727645
theorem B2101175 : Blo 2099435 2101175 := bstep (se 1 (by rfl) ⟨1575881, by rfl⟩ : syracuseStep 2101175 = 3151763) B3151763
theorem B3545741 : Blo 2099435 3545741 := bbase (se 3 (by rfl) ⟨664826, by rfl⟩ : syracuseStep 3545741 = 1329653) (by norm_num)
theorem B2363827 : Blo 2099435 2363827 := bstep (se 1 (by rfl) ⟨1772870, by rfl⟩ : syracuseStep 2363827 = 3545741) B3545741
theorem B3151769 : Blo 2099435 3151769 := bstep (se 2 (by rfl) ⟨1181913, by rfl⟩ : syracuseStep 3151769 = 2363827) B2363827
theorem B2101179 : Blo 2099435 2101179 := bstep (se 1 (by rfl) ⟨1575884, by rfl⟩ : syracuseStep 2101179 = 3151769) B3151769
theorem B6731381 : Blo 2099435 6731381 := bbase (se 5 (by rfl) ⟨315533, by rfl⟩ : syracuseStep 6731381 = 631067) (by norm_num)
theorem B17950349 : Blo 2099435 17950349 := bstep (se 3 (by rfl) ⟨3365690, by rfl⟩ : syracuseStep 17950349 = 6731381) B6731381
theorem B11966899 : Blo 2099435 11966899 := bstep (se 1 (by rfl) ⟨8975174, by rfl⟩ : syracuseStep 11966899 = 17950349) B17950349
theorem B15955865 : Blo 2099435 15955865 := bstep (se 2 (by rfl) ⟨5983449, by rfl⟩ : syracuseStep 15955865 = 11966899) B11966899
theorem B10637243 : Blo 2099435 10637243 := bstep (se 1 (by rfl) ⟨7977932, by rfl⟩ : syracuseStep 10637243 = 15955865) B15955865
theorem B7091495 : Blo 2099435 7091495 := bstep (se 1 (by rfl) ⟨5318621, by rfl⟩ : syracuseStep 7091495 = 10637243) B10637243
theorem B4727663 : Blo 2099435 4727663 := bstep (se 1 (by rfl) ⟨3545747, by rfl⟩ : syracuseStep 4727663 = 7091495) B7091495
theorem B3151775 : Blo 2099435 3151775 := bstep (se 1 (by rfl) ⟨2363831, by rfl⟩ : syracuseStep 3151775 = 4727663) B4727663
theorem B2101183 : Blo 2099435 2101183 := bstep (se 1 (by rfl) ⟨1575887, by rfl⟩ : syracuseStep 2101183 = 3151775) B3151775
theorem B3151781 : Blo 2099435 3151781 := bbase (se 4 (by rfl) ⟨295479, by rfl⟩ : syracuseStep 3151781 = 590959) (by norm_num)
theorem B2101187 : Blo 2099435 2101187 := bstep (se 1 (by rfl) ⟨1575890, by rfl⟩ : syracuseStep 2101187 = 3151781) B3151781
theorem B2659321 : Blo 2099435 2659321 := bbase (se 2 (by rfl) ⟨997245, by rfl⟩ : syracuseStep 2659321 = 1994491) (by norm_num)
theorem B3545761 : Blo 2099435 3545761 := bstep (se 2 (by rfl) ⟨1329660, by rfl⟩ : syracuseStep 3545761 = 2659321) B2659321
theorem B4727681 : Blo 2099435 4727681 := bstep (se 2 (by rfl) ⟨1772880, by rfl⟩ : syracuseStep 4727681 = 3545761) B3545761
theorem B3151787 : Blo 2099435 3151787 := bstep (se 1 (by rfl) ⟨2363840, by rfl⟩ : syracuseStep 3151787 = 4727681) B4727681
theorem B2101191 : Blo 2099435 2101191 := bstep (se 1 (by rfl) ⟨1575893, by rfl⟩ : syracuseStep 2101191 = 3151787) B3151787
theorem B2363845 : Blo 2099435 2363845 := bbase (se 4 (by rfl) ⟨221610, by rfl⟩ : syracuseStep 2363845 = 443221) (by norm_num)
theorem B3151793 : Blo 2099435 3151793 := bstep (se 2 (by rfl) ⟨1181922, by rfl⟩ : syracuseStep 3151793 = 2363845) B2363845
theorem B2101195 : Blo 2099435 2101195 := bstep (se 1 (by rfl) ⟨1575896, by rfl⟩ : syracuseStep 2101195 = 3151793) B3151793
theorem B3988997 : Blo 2099435 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B2659331 : Blo 2099435 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B7091549 : Blo 2099435 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B4727699 : Blo 2099435 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B3151799 : Blo 2099435 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B2101199 : Blo 2099435 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B3151805 : Blo 2099435 3151805 := bbase (se 3 (by rfl) ⟨590963, by rfl⟩ : syracuseStep 3151805 = 1181927) (by norm_num)
theorem B2101203 : Blo 2099435 2101203 := bstep (se 1 (by rfl) ⟨1575902, by rfl⟩ : syracuseStep 2101203 = 3151805) B3151805
theorem B4727717 : Blo 2099435 4727717 := bbase (se 4 (by rfl) ⟨443223, by rfl⟩ : syracuseStep 4727717 = 886447) (by norm_num)
theorem B3151811 : Blo 2099435 3151811 := bstep (se 1 (by rfl) ⟨2363858, by rfl⟩ : syracuseStep 3151811 = 4727717) B4727717
theorem B2101207 : Blo 2099435 2101207 := bstep (se 1 (by rfl) ⟨1575905, by rfl⟩ : syracuseStep 2101207 = 3151811) B3151811
theorem B5318693 : Blo 2099435 5318693 := bbase (se 4 (by rfl) ⟨498627, by rfl⟩ : syracuseStep 5318693 = 997255) (by norm_num)
theorem B3545795 : Blo 2099435 3545795 := bstep (se 1 (by rfl) ⟨2659346, by rfl⟩ : syracuseStep 3545795 = 5318693) B5318693
theorem B2363863 : Blo 2099435 2363863 := bstep (se 1 (by rfl) ⟨1772897, by rfl⟩ : syracuseStep 2363863 = 3545795) B3545795
theorem B3151817 : Blo 2099435 3151817 := bstep (se 2 (by rfl) ⟨1181931, by rfl⟩ : syracuseStep 3151817 = 2363863) B2363863
theorem B2101211 : Blo 2099435 2101211 := bstep (se 1 (by rfl) ⟨1575908, by rfl⟩ : syracuseStep 2101211 = 3151817) B3151817
theorem B5983541 : Blo 2099435 5983541 := bbase (se 5 (by rfl) ⟨280478, by rfl⟩ : syracuseStep 5983541 = 560957) (by norm_num)
theorem B3989027 : Blo 2099435 3989027 := bstep (se 1 (by rfl) ⟨2991770, by rfl⟩ : syracuseStep 3989027 = 5983541) B5983541
theorem B10637405 : Blo 2099435 10637405 := bstep (se 3 (by rfl) ⟨1994513, by rfl⟩ : syracuseStep 10637405 = 3989027) B3989027
theorem B7091603 : Blo 2099435 7091603 := bstep (se 1 (by rfl) ⟨5318702, by rfl⟩ : syracuseStep 7091603 = 10637405) B10637405
theorem B4727735 : Blo 2099435 4727735 := bstep (se 1 (by rfl) ⟨3545801, by rfl⟩ : syracuseStep 4727735 = 7091603) B7091603
theorem B3151823 : Blo 2099435 3151823 := bstep (se 1 (by rfl) ⟨2363867, by rfl⟩ : syracuseStep 3151823 = 4727735) B4727735
theorem B2101215 : Blo 2099435 2101215 := bstep (se 1 (by rfl) ⟨1575911, by rfl⟩ : syracuseStep 2101215 = 3151823) B3151823
theorem B3151829 : Blo 2099435 3151829 := bbase (se 7 (by rfl) ⟨36935, by rfl⟩ : syracuseStep 3151829 = 73871) (by norm_num)
theorem B2101219 : Blo 2099435 2101219 := bstep (se 1 (by rfl) ⟨1575914, by rfl⟩ : syracuseStep 2101219 = 3151829) B3151829
theorem B7978085 : Blo 2099435 7978085 := bbase (se 4 (by rfl) ⟨747945, by rfl⟩ : syracuseStep 7978085 = 1495891) (by norm_num)
theorem B5318723 : Blo 2099435 5318723 := bstep (se 1 (by rfl) ⟨3989042, by rfl⟩ : syracuseStep 5318723 = 7978085) B7978085
theorem B3545815 : Blo 2099435 3545815 := bstep (se 1 (by rfl) ⟨2659361, by rfl⟩ : syracuseStep 3545815 = 5318723) B5318723
theorem B4727753 : Blo 2099435 4727753 := bstep (se 2 (by rfl) ⟨1772907, by rfl⟩ : syracuseStep 4727753 = 3545815) B3545815
theorem B3151835 : Blo 2099435 3151835 := bstep (se 1 (by rfl) ⟨2363876, by rfl⟩ : syracuseStep 3151835 = 4727753) B4727753
theorem B2101223 : Blo 2099435 2101223 := bstep (se 1 (by rfl) ⟨1575917, by rfl⟩ : syracuseStep 2101223 = 3151835) B3151835
theorem B2363881 : Blo 2099435 2363881 := bbase (se 2 (by rfl) ⟨886455, by rfl⟩ : syracuseStep 2363881 = 1772911) (by norm_num)
theorem B3151841 : Blo 2099435 3151841 := bstep (se 2 (by rfl) ⟨1181940, by rfl⟩ : syracuseStep 3151841 = 2363881) B2363881
theorem B2101227 : Blo 2099435 2101227 := bstep (se 1 (by rfl) ⟨1575920, by rfl⟩ : syracuseStep 2101227 = 3151841) B3151841
theorem B2243845 : Blo 2099435 2243845 := bbase (se 4 (by rfl) ⟨210360, by rfl⟩ : syracuseStep 2243845 = 420721) (by norm_num)
theorem B11967173 : Blo 2099435 11967173 := bstep (se 4 (by rfl) ⟨1121922, by rfl⟩ : syracuseStep 11967173 = 2243845) B2243845
theorem B7978115 : Blo 2099435 7978115 := bstep (se 1 (by rfl) ⟨5983586, by rfl⟩ : syracuseStep 7978115 = 11967173) B11967173
theorem B5318743 : Blo 2099435 5318743 := bstep (se 1 (by rfl) ⟨3989057, by rfl⟩ : syracuseStep 5318743 = 7978115) B7978115
theorem B7091657 : Blo 2099435 7091657 := bstep (se 2 (by rfl) ⟨2659371, by rfl⟩ : syracuseStep 7091657 = 5318743) B5318743
theorem B4727771 : Blo 2099435 4727771 := bstep (se 1 (by rfl) ⟨3545828, by rfl⟩ : syracuseStep 4727771 = 7091657) B7091657
theorem B3151847 : Blo 2099435 3151847 := bstep (se 1 (by rfl) ⟨2363885, by rfl⟩ : syracuseStep 3151847 = 4727771) B4727771
theorem B2101231 : Blo 2099435 2101231 := bstep (se 1 (by rfl) ⟨1575923, by rfl⟩ : syracuseStep 2101231 = 3151847) B3151847
theorem B3151853 : Blo 2099435 3151853 := bbase (se 3 (by rfl) ⟨590972, by rfl⟩ : syracuseStep 3151853 = 1181945) (by norm_num)
theorem B2101235 : Blo 2099435 2101235 := bstep (se 1 (by rfl) ⟨1575926, by rfl⟩ : syracuseStep 2101235 = 3151853) B3151853
theorem B4727789 : Blo 2099435 4727789 := bbase (se 3 (by rfl) ⟨886460, by rfl⟩ : syracuseStep 4727789 = 1772921) (by norm_num)
theorem B3151859 : Blo 2099435 3151859 := bstep (se 1 (by rfl) ⟨2363894, by rfl⟩ : syracuseStep 3151859 = 4727789) B4727789
theorem B2101239 : Blo 2099435 2101239 := bstep (se 1 (by rfl) ⟨1575929, by rfl⟩ : syracuseStep 2101239 = 3151859) B3151859
theorem B4487717 : Blo 2099435 4487717 := bbase (se 4 (by rfl) ⟨420723, by rfl⟩ : syracuseStep 4487717 = 841447) (by norm_num)
theorem B2991811 : Blo 2099435 2991811 := bstep (se 1 (by rfl) ⟨2243858, by rfl⟩ : syracuseStep 2991811 = 4487717) B4487717
theorem B3989081 : Blo 2099435 3989081 := bstep (se 2 (by rfl) ⟨1495905, by rfl⟩ : syracuseStep 3989081 = 2991811) B2991811
theorem B2659387 : Blo 2099435 2659387 := bstep (se 1 (by rfl) ⟨1994540, by rfl⟩ : syracuseStep 2659387 = 3989081) B3989081
theorem B3545849 : Blo 2099435 3545849 := bstep (se 2 (by rfl) ⟨1329693, by rfl⟩ : syracuseStep 3545849 = 2659387) B2659387
theorem B2363899 : Blo 2099435 2363899 := bstep (se 1 (by rfl) ⟨1772924, by rfl⟩ : syracuseStep 2363899 = 3545849) B3545849
theorem B3151865 : Blo 2099435 3151865 := bstep (se 2 (by rfl) ⟨1181949, by rfl⟩ : syracuseStep 3151865 = 2363899) B2363899
theorem B2101243 : Blo 2099435 2101243 := bstep (se 1 (by rfl) ⟨1575932, by rfl⟩ : syracuseStep 2101243 = 3151865) B3151865
theorem B24592085 : Blo 2099435 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B16394723 : Blo 2099435 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B10929815 : Blo 2099435 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B7286543 : Blo 2099435 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B4857695 : Blo 2099435 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B3238463 : Blo 2099435 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B8635901 : Blo 2099435 8635901 := bstep (se 3 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 8635901 = 3238463) B3238463
theorem B23029069 : Blo 2099435 23029069 := bstep (se 3 (by rfl) ⟨4317950, by rfl⟩ : syracuseStep 23029069 = 8635901) B8635901
theorem B30705425 : Blo 2099435 30705425 := bstep (se 2 (by rfl) ⟨11514534, by rfl⟩ : syracuseStep 30705425 = 23029069) B23029069
theorem B20470283 : Blo 2099435 20470283 := bstep (se 1 (by rfl) ⟨15352712, by rfl⟩ : syracuseStep 20470283 = 30705425) B30705425
theorem B13646855 : Blo 2099435 13646855 := bstep (se 1 (by rfl) ⟨10235141, by rfl⟩ : syracuseStep 13646855 = 20470283) B20470283
theorem B9097903 : Blo 2099435 9097903 := bstep (se 1 (by rfl) ⟨6823427, by rfl⟩ : syracuseStep 9097903 = 13646855) B13646855
theorem B48522149 : Blo 2099435 48522149 := bstep (se 4 (by rfl) ⟨4548951, by rfl⟩ : syracuseStep 48522149 = 9097903) B9097903
theorem B32348099 : Blo 2099435 32348099 := bstep (se 1 (by rfl) ⟨24261074, by rfl⟩ : syracuseStep 32348099 = 48522149) B48522149
theorem B86261597 : Blo 2099435 86261597 := bstep (se 3 (by rfl) ⟨16174049, by rfl⟩ : syracuseStep 86261597 = 32348099) B32348099
theorem B57507731 : Blo 2099435 57507731 := bstep (se 1 (by rfl) ⟨43130798, by rfl⟩ : syracuseStep 57507731 = 86261597) B86261597
theorem B38338487 : Blo 2099435 38338487 := bstep (se 1 (by rfl) ⟨28753865, by rfl⟩ : syracuseStep 38338487 = 57507731) B57507731
theorem B25558991 : Blo 2099435 25558991 := bstep (se 1 (by rfl) ⟨19169243, by rfl⟩ : syracuseStep 25558991 = 38338487) B38338487
theorem B17039327 : Blo 2099435 17039327 := bstep (se 1 (by rfl) ⟨12779495, by rfl⟩ : syracuseStep 17039327 = 25558991) B25558991
theorem B181752821 : Blo 2099435 181752821 := bstep (se 5 (by rfl) ⟨8519663, by rfl⟩ : syracuseStep 181752821 = 17039327) B17039327
theorem B121168547 : Blo 2099435 121168547 := bstep (se 1 (by rfl) ⟨90876410, by rfl⟩ : syracuseStep 121168547 = 181752821) B181752821
theorem B80779031 : Blo 2099435 80779031 := bstep (se 1 (by rfl) ⟨60584273, by rfl⟩ : syracuseStep 80779031 = 121168547) B121168547
theorem B53852687 : Blo 2099435 53852687 := bstep (se 1 (by rfl) ⟨40389515, by rfl⟩ : syracuseStep 53852687 = 80779031) B80779031
theorem B35901791 : Blo 2099435 35901791 := bstep (se 1 (by rfl) ⟨26926343, by rfl⟩ : syracuseStep 35901791 = 53852687) B53852687
theorem B23934527 : Blo 2099435 23934527 := bstep (se 1 (by rfl) ⟨17950895, by rfl⟩ : syracuseStep 23934527 = 35901791) B35901791
theorem B15956351 : Blo 2099435 15956351 := bstep (se 1 (by rfl) ⟨11967263, by rfl⟩ : syracuseStep 15956351 = 23934527) B23934527
theorem B10637567 : Blo 2099435 10637567 := bstep (se 1 (by rfl) ⟨7978175, by rfl⟩ : syracuseStep 10637567 = 15956351) B15956351
theorem B7091711 : Blo 2099435 7091711 := bstep (se 1 (by rfl) ⟨5318783, by rfl⟩ : syracuseStep 7091711 = 10637567) B10637567
theorem B4727807 : Blo 2099435 4727807 := bstep (se 1 (by rfl) ⟨3545855, by rfl⟩ : syracuseStep 4727807 = 7091711) B7091711
theorem B3151871 : Blo 2099435 3151871 := bstep (se 1 (by rfl) ⟨2363903, by rfl⟩ : syracuseStep 3151871 = 4727807) B4727807
theorem B2101247 : Blo 2099435 2101247 := bstep (se 1 (by rfl) ⟨1575935, by rfl⟩ : syracuseStep 2101247 = 3151871) B3151871
theorem B3151877 : Blo 2099435 3151877 := bbase (se 4 (by rfl) ⟨295488, by rfl⟩ : syracuseStep 3151877 = 590977) (by norm_num)
theorem B2101251 : Blo 2099435 2101251 := bstep (se 1 (by rfl) ⟨1575938, by rfl⟩ : syracuseStep 2101251 = 3151877) B3151877
theorem B3545869 : Blo 2099435 3545869 := bbase (se 3 (by rfl) ⟨664850, by rfl⟩ : syracuseStep 3545869 = 1329701) (by norm_num)
theorem B4727825 : Blo 2099435 4727825 := bstep (se 2 (by rfl) ⟨1772934, by rfl⟩ : syracuseStep 4727825 = 3545869) B3545869
theorem B3151883 : Blo 2099435 3151883 := bstep (se 1 (by rfl) ⟨2363912, by rfl⟩ : syracuseStep 3151883 = 4727825) B4727825
theorem B2101255 : Blo 2099435 2101255 := bstep (se 1 (by rfl) ⟨1575941, by rfl⟩ : syracuseStep 2101255 = 3151883) B3151883
theorem B2363917 : Blo 2099435 2363917 := bbase (se 3 (by rfl) ⟨443234, by rfl⟩ : syracuseStep 2363917 = 886469) (by norm_num)
theorem B3151889 : Blo 2099435 3151889 := bstep (se 2 (by rfl) ⟨1181958, by rfl⟩ : syracuseStep 3151889 = 2363917) B2363917
theorem B2101259 : Blo 2099435 2101259 := bstep (se 1 (by rfl) ⟨1575944, by rfl⟩ : syracuseStep 2101259 = 3151889) B3151889
theorem B7091765 : Blo 2099435 7091765 := bbase (se 5 (by rfl) ⟨332426, by rfl⟩ : syracuseStep 7091765 = 664853) (by norm_num)
theorem B4727843 : Blo 2099435 4727843 := bstep (se 1 (by rfl) ⟨3545882, by rfl⟩ : syracuseStep 4727843 = 7091765) B7091765
theorem B3151895 : Blo 2099435 3151895 := bstep (se 1 (by rfl) ⟨2363921, by rfl⟩ : syracuseStep 3151895 = 4727843) B4727843
theorem B2101263 : Blo 2099435 2101263 := bstep (se 1 (by rfl) ⟨1575947, by rfl⟩ : syracuseStep 2101263 = 3151895) B3151895
theorem B3151901 : Blo 2099435 3151901 := bbase (se 3 (by rfl) ⟨590981, by rfl⟩ : syracuseStep 3151901 = 1181963) (by norm_num)
theorem B2101267 : Blo 2099435 2101267 := bstep (se 1 (by rfl) ⟨1575950, by rfl⟩ : syracuseStep 2101267 = 3151901) B3151901
theorem B4727861 : Blo 2099435 4727861 := bbase (se 5 (by rfl) ⟨221618, by rfl⟩ : syracuseStep 4727861 = 443237) (by norm_num)
theorem B3151907 : Blo 2099435 3151907 := bstep (se 1 (by rfl) ⟨2363930, by rfl⟩ : syracuseStep 3151907 = 4727861) B4727861
theorem B2101271 : Blo 2099435 2101271 := bstep (se 1 (by rfl) ⟨1575953, by rfl⟩ : syracuseStep 2101271 = 3151907) B3151907
theorem B2396189 : Blo 2099435 2396189 := bbase (se 3 (by rfl) ⟨449285, by rfl⟩ : syracuseStep 2396189 = 898571) (by norm_num)
theorem B6389837 : Blo 2099435 6389837 := bstep (se 3 (by rfl) ⟨1198094, by rfl⟩ : syracuseStep 6389837 = 2396189) B2396189
theorem B4259891 : Blo 2099435 4259891 := bstep (se 1 (by rfl) ⟨3194918, by rfl⟩ : syracuseStep 4259891 = 6389837) B6389837
theorem B2839927 : Blo 2099435 2839927 := bstep (se 1 (by rfl) ⟨2129945, by rfl⟩ : syracuseStep 2839927 = 4259891) B4259891
theorem B3786569 : Blo 2099435 3786569 := bstep (se 2 (by rfl) ⟨1419963, by rfl⟩ : syracuseStep 3786569 = 2839927) B2839927
theorem B2524379 : Blo 2099435 2524379 := bstep (se 1 (by rfl) ⟨1893284, by rfl⟩ : syracuseStep 2524379 = 3786569) B3786569
theorem B6731677 : Blo 2099435 6731677 := bstep (se 3 (by rfl) ⟨1262189, by rfl⟩ : syracuseStep 6731677 = 2524379) B2524379
theorem B8975569 : Blo 2099435 8975569 := bstep (se 2 (by rfl) ⟨3365838, by rfl⟩ : syracuseStep 8975569 = 6731677) B6731677
theorem B11967425 : Blo 2099435 11967425 := bstep (se 2 (by rfl) ⟨4487784, by rfl⟩ : syracuseStep 11967425 = 8975569) B8975569
theorem B7978283 : Blo 2099435 7978283 := bstep (se 1 (by rfl) ⟨5983712, by rfl⟩ : syracuseStep 7978283 = 11967425) B11967425
theorem B5318855 : Blo 2099435 5318855 := bstep (se 1 (by rfl) ⟨3989141, by rfl⟩ : syracuseStep 5318855 = 7978283) B7978283
theorem B3545903 : Blo 2099435 3545903 := bstep (se 1 (by rfl) ⟨2659427, by rfl⟩ : syracuseStep 3545903 = 5318855) B5318855
theorem B2363935 : Blo 2099435 2363935 := bstep (se 1 (by rfl) ⟨1772951, by rfl⟩ : syracuseStep 2363935 = 3545903) B3545903
theorem B3151913 : Blo 2099435 3151913 := bstep (se 2 (by rfl) ⟨1181967, by rfl⟩ : syracuseStep 3151913 = 2363935) B2363935
theorem B2101275 : Blo 2099435 2101275 := bstep (se 1 (by rfl) ⟨1575956, by rfl⟩ : syracuseStep 2101275 = 3151913) B3151913
theorem B6477029 : Blo 2099435 6477029 := bbase (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) (by norm_num)
theorem B4318019 : Blo 2099435 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B2878679 : Blo 2099435 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B7676477 : Blo 2099435 7676477 := bstep (se 3 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 7676477 = 2878679) B2878679
theorem B5117651 : Blo 2099435 5117651 := bstep (se 1 (by rfl) ⟨3838238, by rfl⟩ : syracuseStep 5117651 = 7676477) B7676477
theorem B3411767 : Blo 2099435 3411767 := bstep (se 1 (by rfl) ⟨2558825, by rfl⟩ : syracuseStep 3411767 = 5117651) B5117651
theorem B2274511 : Blo 2099435 2274511 := bstep (se 1 (by rfl) ⟨1705883, by rfl⟩ : syracuseStep 2274511 = 3411767) B3411767
theorem B48522901 : Blo 2099435 48522901 := bstep (se 6 (by rfl) ⟨1137255, by rfl⟩ : syracuseStep 48522901 = 2274511) B2274511
theorem B64697201 : Blo 2099435 64697201 := bstep (se 2 (by rfl) ⟨24261450, by rfl⟩ : syracuseStep 64697201 = 48522901) B48522901
theorem B43131467 : Blo 2099435 43131467 := bstep (se 1 (by rfl) ⟨32348600, by rfl⟩ : syracuseStep 43131467 = 64697201) B64697201
theorem B28754311 : Blo 2099435 28754311 := bstep (se 1 (by rfl) ⟨21565733, by rfl⟩ : syracuseStep 28754311 = 43131467) B43131467
theorem B38339081 : Blo 2099435 38339081 := bstep (se 2 (by rfl) ⟨14377155, by rfl⟩ : syracuseStep 38339081 = 28754311) B28754311
theorem B25559387 : Blo 2099435 25559387 := bstep (se 1 (by rfl) ⟨19169540, by rfl⟩ : syracuseStep 25559387 = 38339081) B38339081
theorem B17039591 : Blo 2099435 17039591 := bstep (se 1 (by rfl) ⟨12779693, by rfl⟩ : syracuseStep 17039591 = 25559387) B25559387
theorem B11359727 : Blo 2099435 11359727 := bstep (se 1 (by rfl) ⟨8519795, by rfl⟩ : syracuseStep 11359727 = 17039591) B17039591
theorem B7573151 : Blo 2099435 7573151 := bstep (se 1 (by rfl) ⟨5679863, by rfl⟩ : syracuseStep 7573151 = 11359727) B11359727
theorem B5048767 : Blo 2099435 5048767 := bstep (se 1 (by rfl) ⟨3786575, by rfl⟩ : syracuseStep 5048767 = 7573151) B7573151
theorem B6731689 : Blo 2099435 6731689 := bstep (se 2 (by rfl) ⟨2524383, by rfl⟩ : syracuseStep 6731689 = 5048767) B5048767
theorem B8975585 : Blo 2099435 8975585 := bstep (se 2 (by rfl) ⟨3365844, by rfl⟩ : syracuseStep 8975585 = 6731689) B6731689
theorem B5983723 : Blo 2099435 5983723 := bstep (se 1 (by rfl) ⟨4487792, by rfl⟩ : syracuseStep 5983723 = 8975585) B8975585
theorem B7978297 : Blo 2099435 7978297 := bstep (se 2 (by rfl) ⟨2991861, by rfl⟩ : syracuseStep 7978297 = 5983723) B5983723
theorem B10637729 : Blo 2099435 10637729 := bstep (se 2 (by rfl) ⟨3989148, by rfl⟩ : syracuseStep 10637729 = 7978297) B7978297
theorem B7091819 : Blo 2099435 7091819 := bstep (se 1 (by rfl) ⟨5318864, by rfl⟩ : syracuseStep 7091819 = 10637729) B10637729
theorem B4727879 : Blo 2099435 4727879 := bstep (se 1 (by rfl) ⟨3545909, by rfl⟩ : syracuseStep 4727879 = 7091819) B7091819
theorem B3151919 : Blo 2099435 3151919 := bstep (se 1 (by rfl) ⟨2363939, by rfl⟩ : syracuseStep 3151919 = 4727879) B4727879
theorem B2101279 : Blo 2099435 2101279 := bstep (se 1 (by rfl) ⟨1575959, by rfl⟩ : syracuseStep 2101279 = 3151919) B3151919
theorem B3151925 : Blo 2099435 3151925 := bbase (se 5 (by rfl) ⟨147746, by rfl⟩ : syracuseStep 3151925 = 295493) (by norm_num)
theorem B2101283 : Blo 2099435 2101283 := bstep (se 1 (by rfl) ⟨1575962, by rfl⟩ : syracuseStep 2101283 = 3151925) B3151925
theorem B5318885 : Blo 2099435 5318885 := bbase (se 4 (by rfl) ⟨498645, by rfl⟩ : syracuseStep 5318885 = 997291) (by norm_num)
theorem B3545923 : Blo 2099435 3545923 := bstep (se 1 (by rfl) ⟨2659442, by rfl⟩ : syracuseStep 3545923 = 5318885) B5318885
theorem B4727897 : Blo 2099435 4727897 := bstep (se 2 (by rfl) ⟨1772961, by rfl⟩ : syracuseStep 4727897 = 3545923) B3545923
theorem B3151931 : Blo 2099435 3151931 := bstep (se 1 (by rfl) ⟨2363948, by rfl⟩ : syracuseStep 3151931 = 4727897) B4727897
theorem B2101287 : Blo 2099435 2101287 := bstep (se 1 (by rfl) ⟨1575965, by rfl⟩ : syracuseStep 2101287 = 3151931) B3151931
theorem B2363953 : Blo 2099435 2363953 := bbase (se 2 (by rfl) ⟨886482, by rfl⟩ : syracuseStep 2363953 = 1772965) (by norm_num)
theorem B3151937 : Blo 2099435 3151937 := bstep (se 2 (by rfl) ⟨1181976, by rfl⟩ : syracuseStep 3151937 = 2363953) B2363953
theorem B2101291 : Blo 2099435 2101291 := bstep (se 1 (by rfl) ⟨1575968, by rfl⟩ : syracuseStep 2101291 = 3151937) B3151937
theorem B3786605 : Blo 2099435 3786605 := bbase (se 3 (by rfl) ⟨709988, by rfl⟩ : syracuseStep 3786605 = 1419977) (by norm_num)
theorem B2524403 : Blo 2099435 2524403 := bstep (se 1 (by rfl) ⟨1893302, by rfl⟩ : syracuseStep 2524403 = 3786605) B3786605
theorem B6731741 : Blo 2099435 6731741 := bstep (se 3 (by rfl) ⟨1262201, by rfl⟩ : syracuseStep 6731741 = 2524403) B2524403
theorem B4487827 : Blo 2099435 4487827 := bstep (se 1 (by rfl) ⟨3365870, by rfl⟩ : syracuseStep 4487827 = 6731741) B6731741
theorem B5983769 : Blo 2099435 5983769 := bstep (se 2 (by rfl) ⟨2243913, by rfl⟩ : syracuseStep 5983769 = 4487827) B4487827
theorem B3989179 : Blo 2099435 3989179 := bstep (se 1 (by rfl) ⟨2991884, by rfl⟩ : syracuseStep 3989179 = 5983769) B5983769
theorem B5318905 : Blo 2099435 5318905 := bstep (se 2 (by rfl) ⟨1994589, by rfl⟩ : syracuseStep 5318905 = 3989179) B3989179
theorem B7091873 : Blo 2099435 7091873 := bstep (se 2 (by rfl) ⟨2659452, by rfl⟩ : syracuseStep 7091873 = 5318905) B5318905
theorem B4727915 : Blo 2099435 4727915 := bstep (se 1 (by rfl) ⟨3545936, by rfl⟩ : syracuseStep 4727915 = 7091873) B7091873
theorem B3151943 : Blo 2099435 3151943 := bstep (se 1 (by rfl) ⟨2363957, by rfl⟩ : syracuseStep 3151943 = 4727915) B4727915
theorem B2101295 : Blo 2099435 2101295 := bstep (se 1 (by rfl) ⟨1575971, by rfl⟩ : syracuseStep 2101295 = 3151943) B3151943
theorem B3151949 : Blo 2099435 3151949 := bbase (se 3 (by rfl) ⟨590990, by rfl⟩ : syracuseStep 3151949 = 1181981) (by norm_num)
theorem B2101299 : Blo 2099435 2101299 := bstep (se 1 (by rfl) ⟨1575974, by rfl⟩ : syracuseStep 2101299 = 3151949) B3151949
theorem B4727933 : Blo 2099435 4727933 := bbase (se 3 (by rfl) ⟨886487, by rfl⟩ : syracuseStep 4727933 = 1772975) (by norm_num)
theorem B3151955 : Blo 2099435 3151955 := bstep (se 1 (by rfl) ⟨2363966, by rfl⟩ : syracuseStep 3151955 = 4727933) B4727933
theorem B2101303 : Blo 2099435 2101303 := bstep (se 1 (by rfl) ⟨1575977, by rfl⟩ : syracuseStep 2101303 = 3151955) B3151955
theorem B3545957 : Blo 2099435 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B2363971 : Blo 2099435 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B3151961 : Blo 2099435 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B2101307 : Blo 2099435 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B4487861 : Blo 2099435 4487861 := bbase (se 5 (by rfl) ⟨210368, by rfl⟩ : syracuseStep 4487861 = 420737) (by norm_num)
theorem B2991907 : Blo 2099435 2991907 := bstep (se 1 (by rfl) ⟨2243930, by rfl⟩ : syracuseStep 2991907 = 4487861) B4487861
theorem B15956837 : Blo 2099435 15956837 := bstep (se 4 (by rfl) ⟨1495953, by rfl⟩ : syracuseStep 15956837 = 2991907) B2991907
theorem B10637891 : Blo 2099435 10637891 := bstep (se 1 (by rfl) ⟨7978418, by rfl⟩ : syracuseStep 10637891 = 15956837) B15956837
theorem B7091927 : Blo 2099435 7091927 := bstep (se 1 (by rfl) ⟨5318945, by rfl⟩ : syracuseStep 7091927 = 10637891) B10637891
theorem B4727951 : Blo 2099435 4727951 := bstep (se 1 (by rfl) ⟨3545963, by rfl⟩ : syracuseStep 4727951 = 7091927) B7091927
theorem B3151967 : Blo 2099435 3151967 := bstep (se 1 (by rfl) ⟨2363975, by rfl⟩ : syracuseStep 3151967 = 4727951) B4727951
theorem B2101311 : Blo 2099435 2101311 := bstep (se 1 (by rfl) ⟨1575983, by rfl⟩ : syracuseStep 2101311 = 3151967) B3151967
theorem B3151973 : Blo 2099435 3151973 := bbase (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) (by norm_num)
theorem B2101315 : Blo 2099435 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B5679973 : Blo 2099435 5679973 := bbase (se 4 (by rfl) ⟨532497, by rfl⟩ : syracuseStep 5679973 = 1064995) (by norm_num)
theorem B7573297 : Blo 2099435 7573297 := bstep (se 2 (by rfl) ⟨2839986, by rfl⟩ : syracuseStep 7573297 = 5679973) B5679973
theorem B10097729 : Blo 2099435 10097729 := bstep (se 2 (by rfl) ⟨3786648, by rfl⟩ : syracuseStep 10097729 = 7573297) B7573297
theorem B6731819 : Blo 2099435 6731819 := bstep (se 1 (by rfl) ⟨5048864, by rfl⟩ : syracuseStep 6731819 = 10097729) B10097729
theorem B4487879 : Blo 2099435 4487879 := bstep (se 1 (by rfl) ⟨3365909, by rfl⟩ : syracuseStep 4487879 = 6731819) B6731819
theorem B2991919 : Blo 2099435 2991919 := bstep (se 1 (by rfl) ⟨2243939, by rfl⟩ : syracuseStep 2991919 = 4487879) B4487879
theorem B3989225 : Blo 2099435 3989225 := bstep (se 2 (by rfl) ⟨1495959, by rfl⟩ : syracuseStep 3989225 = 2991919) B2991919
theorem B2659483 : Blo 2099435 2659483 := bstep (se 1 (by rfl) ⟨1994612, by rfl⟩ : syracuseStep 2659483 = 3989225) B3989225
theorem B3545977 : Blo 2099435 3545977 := bstep (se 2 (by rfl) ⟨1329741, by rfl⟩ : syracuseStep 3545977 = 2659483) B2659483
theorem B4727969 : Blo 2099435 4727969 := bstep (se 2 (by rfl) ⟨1772988, by rfl⟩ : syracuseStep 4727969 = 3545977) B3545977
theorem B3151979 : Blo 2099435 3151979 := bstep (se 1 (by rfl) ⟨2363984, by rfl⟩ : syracuseStep 3151979 = 4727969) B4727969
theorem B2101319 : Blo 2099435 2101319 := bstep (se 1 (by rfl) ⟨1575989, by rfl⟩ : syracuseStep 2101319 = 3151979) B3151979
theorem B2363989 : Blo 2099435 2363989 := bbase (se 8 (by rfl) ⟨13851, by rfl⟩ : syracuseStep 2363989 = 27703) (by norm_num)
theorem B3151985 : Blo 2099435 3151985 := bstep (se 2 (by rfl) ⟨1181994, by rfl⟩ : syracuseStep 3151985 = 2363989) B2363989
theorem B2101323 : Blo 2099435 2101323 := bstep (se 1 (by rfl) ⟨1575992, by rfl⟩ : syracuseStep 2101323 = 3151985) B3151985
theorem B2659493 : Blo 2099435 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B7091981 : Blo 2099435 7091981 := bstep (se 3 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 7091981 = 2659493) B2659493
theorem B4727987 : Blo 2099435 4727987 := bstep (se 1 (by rfl) ⟨3545990, by rfl⟩ : syracuseStep 4727987 = 7091981) B7091981
theorem B3151991 : Blo 2099435 3151991 := bstep (se 1 (by rfl) ⟨2363993, by rfl⟩ : syracuseStep 3151991 = 4727987) B4727987
theorem B2101327 : Blo 2099435 2101327 := bstep (se 1 (by rfl) ⟨1575995, by rfl⟩ : syracuseStep 2101327 = 3151991) B3151991
theorem B3151997 : Blo 2099435 3151997 := bbase (se 3 (by rfl) ⟨590999, by rfl⟩ : syracuseStep 3151997 = 1181999) (by norm_num)
theorem B2101331 : Blo 2099435 2101331 := bstep (se 1 (by rfl) ⟨1575998, by rfl⟩ : syracuseStep 2101331 = 3151997) B3151997
theorem B4728005 : Blo 2099435 4728005 := bbase (se 4 (by rfl) ⟨443250, by rfl⟩ : syracuseStep 4728005 = 886501) (by norm_num)
theorem B3152003 : Blo 2099435 3152003 := bstep (se 1 (by rfl) ⟨2364002, by rfl⟩ : syracuseStep 3152003 = 4728005) B4728005
theorem B2101335 : Blo 2099435 2101335 := bstep (se 1 (by rfl) ⟨1576001, by rfl⟩ : syracuseStep 2101335 = 3152003) B3152003
theorem B13463765 : Blo 2099435 13463765 := bbase (se 7 (by rfl) ⟨157778, by rfl⟩ : syracuseStep 13463765 = 315557) (by norm_num)
theorem B8975843 : Blo 2099435 8975843 := bstep (se 1 (by rfl) ⟨6731882, by rfl⟩ : syracuseStep 8975843 = 13463765) B13463765
theorem B5983895 : Blo 2099435 5983895 := bstep (se 1 (by rfl) ⟨4487921, by rfl⟩ : syracuseStep 5983895 = 8975843) B8975843
theorem B3989263 : Blo 2099435 3989263 := bstep (se 1 (by rfl) ⟨2991947, by rfl⟩ : syracuseStep 3989263 = 5983895) B5983895
theorem B5319017 : Blo 2099435 5319017 := bstep (se 2 (by rfl) ⟨1994631, by rfl⟩ : syracuseStep 5319017 = 3989263) B3989263
theorem B3546011 : Blo 2099435 3546011 := bstep (se 1 (by rfl) ⟨2659508, by rfl⟩ : syracuseStep 3546011 = 5319017) B5319017
theorem B2364007 : Blo 2099435 2364007 := bstep (se 1 (by rfl) ⟨1773005, by rfl⟩ : syracuseStep 2364007 = 3546011) B3546011
theorem B3152009 : Blo 2099435 3152009 := bstep (se 2 (by rfl) ⟨1182003, by rfl⟩ : syracuseStep 3152009 = 2364007) B2364007
theorem B2101339 : Blo 2099435 2101339 := bstep (se 1 (by rfl) ⟨1576004, by rfl⟩ : syracuseStep 2101339 = 3152009) B3152009
theorem B10638053 : Blo 2099435 10638053 := bbase (se 4 (by rfl) ⟨997317, by rfl⟩ : syracuseStep 10638053 = 1994635) (by norm_num)
theorem B7092035 : Blo 2099435 7092035 := bstep (se 1 (by rfl) ⟨5319026, by rfl⟩ : syracuseStep 7092035 = 10638053) B10638053
theorem B4728023 : Blo 2099435 4728023 := bstep (se 1 (by rfl) ⟨3546017, by rfl⟩ : syracuseStep 4728023 = 7092035) B7092035
theorem B3152015 : Blo 2099435 3152015 := bstep (se 1 (by rfl) ⟨2364011, by rfl⟩ : syracuseStep 3152015 = 4728023) B4728023
theorem B2101343 : Blo 2099435 2101343 := bstep (se 1 (by rfl) ⟨1576007, by rfl⟩ : syracuseStep 2101343 = 3152015) B3152015
theorem B3152021 : Blo 2099435 3152021 := bbase (se 6 (by rfl) ⟨73875, by rfl⟩ : syracuseStep 3152021 = 147751) (by norm_num)
theorem B2101347 : Blo 2099435 2101347 := bstep (se 1 (by rfl) ⟨1576010, by rfl⟩ : syracuseStep 2101347 = 3152021) B3152021
theorem B8975893 : Blo 2099435 8975893 := bbase (se 6 (by rfl) ⟨210372, by rfl⟩ : syracuseStep 8975893 = 420745) (by norm_num)
theorem B11967857 : Blo 2099435 11967857 := bstep (se 2 (by rfl) ⟨4487946, by rfl⟩ : syracuseStep 11967857 = 8975893) B8975893
theorem B7978571 : Blo 2099435 7978571 := bstep (se 1 (by rfl) ⟨5983928, by rfl⟩ : syracuseStep 7978571 = 11967857) B11967857
theorem B5319047 : Blo 2099435 5319047 := bstep (se 1 (by rfl) ⟨3989285, by rfl⟩ : syracuseStep 5319047 = 7978571) B7978571
theorem B3546031 : Blo 2099435 3546031 := bstep (se 1 (by rfl) ⟨2659523, by rfl⟩ : syracuseStep 3546031 = 5319047) B5319047
theorem B4728041 : Blo 2099435 4728041 := bstep (se 2 (by rfl) ⟨1773015, by rfl⟩ : syracuseStep 4728041 = 3546031) B3546031
theorem B3152027 : Blo 2099435 3152027 := bstep (se 1 (by rfl) ⟨2364020, by rfl⟩ : syracuseStep 3152027 = 4728041) B4728041
theorem B2101351 : Blo 2099435 2101351 := bstep (se 1 (by rfl) ⟨1576013, by rfl⟩ : syracuseStep 2101351 = 3152027) B3152027
theorem B2364025 : Blo 2099435 2364025 := bbase (se 2 (by rfl) ⟨886509, by rfl⟩ : syracuseStep 2364025 = 1773019) (by norm_num)
theorem B3152033 : Blo 2099435 3152033 := bstep (se 2 (by rfl) ⟨1182012, by rfl⟩ : syracuseStep 3152033 = 2364025) B2364025
theorem B2101355 : Blo 2099435 2101355 := bstep (se 1 (by rfl) ⟨1576016, by rfl⟩ : syracuseStep 2101355 = 3152033) B3152033
theorem B5117845 : Blo 2099435 5117845 := bbase (se 6 (by rfl) ⟨119949, by rfl⟩ : syracuseStep 5117845 = 239899) (by norm_num)
theorem B6823793 : Blo 2099435 6823793 := bstep (se 2 (by rfl) ⟨2558922, by rfl⟩ : syracuseStep 6823793 = 5117845) B5117845
theorem B4549195 : Blo 2099435 4549195 := bstep (se 1 (by rfl) ⟨3411896, by rfl⟩ : syracuseStep 4549195 = 6823793) B6823793
theorem B24262373 : Blo 2099435 24262373 := bstep (se 4 (by rfl) ⟨2274597, by rfl⟩ : syracuseStep 24262373 = 4549195) B4549195
theorem B64699661 : Blo 2099435 64699661 := bstep (se 3 (by rfl) ⟨12131186, by rfl⟩ : syracuseStep 64699661 = 24262373) B24262373
theorem B43133107 : Blo 2099435 43133107 := bstep (se 1 (by rfl) ⟨32349830, by rfl⟩ : syracuseStep 43133107 = 64699661) B64699661
theorem B57510809 : Blo 2099435 57510809 := bstep (se 2 (by rfl) ⟨21566553, by rfl⟩ : syracuseStep 57510809 = 43133107) B43133107
theorem B38340539 : Blo 2099435 38340539 := bstep (se 1 (by rfl) ⟨28755404, by rfl⟩ : syracuseStep 38340539 = 57510809) B57510809
theorem B25560359 : Blo 2099435 25560359 := bstep (se 1 (by rfl) ⟨19170269, by rfl⟩ : syracuseStep 25560359 = 38340539) B38340539
theorem B17040239 : Blo 2099435 17040239 := bstep (se 1 (by rfl) ⟨12780179, by rfl⟩ : syracuseStep 17040239 = 25560359) B25560359
theorem B11360159 : Blo 2099435 11360159 := bstep (se 1 (by rfl) ⟨8520119, by rfl⟩ : syracuseStep 11360159 = 17040239) B17040239
theorem B7573439 : Blo 2099435 7573439 := bstep (se 1 (by rfl) ⟨5680079, by rfl⟩ : syracuseStep 7573439 = 11360159) B11360159
theorem B20195837 : Blo 2099435 20195837 := bstep (se 3 (by rfl) ⟨3786719, by rfl⟩ : syracuseStep 20195837 = 7573439) B7573439
theorem B13463891 : Blo 2099435 13463891 := bstep (se 1 (by rfl) ⟨10097918, by rfl⟩ : syracuseStep 13463891 = 20195837) B20195837
theorem B8975927 : Blo 2099435 8975927 := bstep (se 1 (by rfl) ⟨6731945, by rfl⟩ : syracuseStep 8975927 = 13463891) B13463891
theorem B5983951 : Blo 2099435 5983951 := bstep (se 1 (by rfl) ⟨4487963, by rfl⟩ : syracuseStep 5983951 = 8975927) B8975927
theorem B7978601 : Blo 2099435 7978601 := bstep (se 2 (by rfl) ⟨2991975, by rfl⟩ : syracuseStep 7978601 = 5983951) B5983951
theorem B5319067 : Blo 2099435 5319067 := bstep (se 1 (by rfl) ⟨3989300, by rfl⟩ : syracuseStep 5319067 = 7978601) B7978601
theorem B7092089 : Blo 2099435 7092089 := bstep (se 2 (by rfl) ⟨2659533, by rfl⟩ : syracuseStep 7092089 = 5319067) B5319067
theorem B4728059 : Blo 2099435 4728059 := bstep (se 1 (by rfl) ⟨3546044, by rfl⟩ : syracuseStep 4728059 = 7092089) B7092089
theorem B3152039 : Blo 2099435 3152039 := bstep (se 1 (by rfl) ⟨2364029, by rfl⟩ : syracuseStep 3152039 = 4728059) B4728059
theorem B2101359 : Blo 2099435 2101359 := bstep (se 1 (by rfl) ⟨1576019, by rfl⟩ : syracuseStep 2101359 = 3152039) B3152039
theorem B3152045 : Blo 2099435 3152045 := bbase (se 3 (by rfl) ⟨591008, by rfl⟩ : syracuseStep 3152045 = 1182017) (by norm_num)
theorem B2101363 : Blo 2099435 2101363 := bstep (se 1 (by rfl) ⟨1576022, by rfl⟩ : syracuseStep 2101363 = 3152045) B3152045
theorem B4728077 : Blo 2099435 4728077 := bbase (se 3 (by rfl) ⟨886514, by rfl⟩ : syracuseStep 4728077 = 1773029) (by norm_num)
theorem B3152051 : Blo 2099435 3152051 := bstep (se 1 (by rfl) ⟨2364038, by rfl⟩ : syracuseStep 3152051 = 4728077) B4728077
theorem B2101367 : Blo 2099435 2101367 := bstep (se 1 (by rfl) ⟨1576025, by rfl⟩ : syracuseStep 2101367 = 3152051) B3152051
theorem B2659549 : Blo 2099435 2659549 := bbase (se 3 (by rfl) ⟨498665, by rfl⟩ : syracuseStep 2659549 = 997331) (by norm_num)
theorem B3546065 : Blo 2099435 3546065 := bstep (se 2 (by rfl) ⟨1329774, by rfl⟩ : syracuseStep 3546065 = 2659549) B2659549
theorem B2364043 : Blo 2099435 2364043 := bstep (se 1 (by rfl) ⟨1773032, by rfl⟩ : syracuseStep 2364043 = 3546065) B3546065
theorem B3152057 : Blo 2099435 3152057 := bstep (se 2 (by rfl) ⟨1182021, by rfl⟩ : syracuseStep 3152057 = 2364043) B2364043
theorem B2101371 : Blo 2099435 2101371 := bstep (se 1 (by rfl) ⟨1576028, by rfl⟩ : syracuseStep 2101371 = 3152057) B3152057
theorem B17951989 : Blo 2099435 17951989 := bbase (se 5 (by rfl) ⟨841499, by rfl⟩ : syracuseStep 17951989 = 1682999) (by norm_num)
theorem B23935985 : Blo 2099435 23935985 := bstep (se 2 (by rfl) ⟨8975994, by rfl⟩ : syracuseStep 23935985 = 17951989) B17951989
theorem B15957323 : Blo 2099435 15957323 := bstep (se 1 (by rfl) ⟨11967992, by rfl⟩ : syracuseStep 15957323 = 23935985) B23935985
theorem B10638215 : Blo 2099435 10638215 := bstep (se 1 (by rfl) ⟨7978661, by rfl⟩ : syracuseStep 10638215 = 15957323) B15957323
theorem B7092143 : Blo 2099435 7092143 := bstep (se 1 (by rfl) ⟨5319107, by rfl⟩ : syracuseStep 7092143 = 10638215) B10638215
theorem B4728095 : Blo 2099435 4728095 := bstep (se 1 (by rfl) ⟨3546071, by rfl⟩ : syracuseStep 4728095 = 7092143) B7092143
theorem B3152063 : Blo 2099435 3152063 := bstep (se 1 (by rfl) ⟨2364047, by rfl⟩ : syracuseStep 3152063 = 4728095) B4728095
theorem B2101375 : Blo 2099435 2101375 := bstep (se 1 (by rfl) ⟨1576031, by rfl⟩ : syracuseStep 2101375 = 3152063) B3152063
theorem B3152069 : Blo 2099435 3152069 := bbase (se 4 (by rfl) ⟨295506, by rfl⟩ : syracuseStep 3152069 = 591013) (by norm_num)
theorem B2101379 : Blo 2099435 2101379 := bstep (se 1 (by rfl) ⟨1576034, by rfl⟩ : syracuseStep 2101379 = 3152069) B3152069
theorem B3546085 : Blo 2099435 3546085 := bbase (se 4 (by rfl) ⟨332445, by rfl⟩ : syracuseStep 3546085 = 664891) (by norm_num)
theorem B4728113 : Blo 2099435 4728113 := bstep (se 2 (by rfl) ⟨1773042, by rfl⟩ : syracuseStep 4728113 = 3546085) B3546085
theorem B3152075 : Blo 2099435 3152075 := bstep (se 1 (by rfl) ⟨2364056, by rfl⟩ : syracuseStep 3152075 = 4728113) B4728113
theorem B2101383 : Blo 2099435 2101383 := bstep (se 1 (by rfl) ⟨1576037, by rfl⟩ : syracuseStep 2101383 = 3152075) B3152075
theorem B2364061 : Blo 2099435 2364061 := bbase (se 3 (by rfl) ⟨443261, by rfl⟩ : syracuseStep 2364061 = 886523) (by norm_num)
theorem B3152081 : Blo 2099435 3152081 := bstep (se 2 (by rfl) ⟨1182030, by rfl⟩ : syracuseStep 3152081 = 2364061) B2364061
theorem B2101387 : Blo 2099435 2101387 := bstep (se 1 (by rfl) ⟨1576040, by rfl⟩ : syracuseStep 2101387 = 3152081) B3152081
theorem B7092197 : Blo 2099435 7092197 := bbase (se 4 (by rfl) ⟨664893, by rfl⟩ : syracuseStep 7092197 = 1329787) (by norm_num)
theorem B4728131 : Blo 2099435 4728131 := bstep (se 1 (by rfl) ⟨3546098, by rfl⟩ : syracuseStep 4728131 = 7092197) B7092197
theorem B3152087 : Blo 2099435 3152087 := bstep (se 1 (by rfl) ⟨2364065, by rfl⟩ : syracuseStep 3152087 = 4728131) B4728131
theorem B2101391 : Blo 2099435 2101391 := bstep (se 1 (by rfl) ⟨1576043, by rfl⟩ : syracuseStep 2101391 = 3152087) B3152087
theorem B3152093 : Blo 2099435 3152093 := bbase (se 3 (by rfl) ⟨591017, by rfl⟩ : syracuseStep 3152093 = 1182035) (by norm_num)
theorem B2101395 : Blo 2099435 2101395 := bstep (se 1 (by rfl) ⟨1576046, by rfl⟩ : syracuseStep 2101395 = 3152093) B3152093
theorem B4728149 : Blo 2099435 4728149 := bbase (se 12 (by rfl) ⟨1731, by rfl⟩ : syracuseStep 4728149 = 3463) (by norm_num)
theorem B3152099 : Blo 2099435 3152099 := bstep (se 1 (by rfl) ⟨2364074, by rfl⟩ : syracuseStep 3152099 = 4728149) B4728149
theorem B2101399 : Blo 2099435 2101399 := bstep (se 1 (by rfl) ⟨1576049, by rfl⟩ : syracuseStep 2101399 = 3152099) B3152099
theorem B2244029 : Blo 2099435 2244029 := bbase (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) (by norm_num)
theorem B5984077 : Blo 2099435 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B7978769 : Blo 2099435 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B5319179 : Blo 2099435 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B3546119 : Blo 2099435 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B2364079 : Blo 2099435 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B3152105 : Blo 2099435 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B2101403 : Blo 2099435 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B16175285 : Blo 2099435 16175285 := bbase (se 5 (by rfl) ⟨758216, by rfl⟩ : syracuseStep 16175285 = 1516433) (by norm_num)
theorem B10783523 : Blo 2099435 10783523 := bstep (se 1 (by rfl) ⟨8087642, by rfl⟩ : syracuseStep 10783523 = 16175285) B16175285
theorem B7189015 : Blo 2099435 7189015 := bstep (se 1 (by rfl) ⟨5391761, by rfl⟩ : syracuseStep 7189015 = 10783523) B10783523
theorem B9585353 : Blo 2099435 9585353 := bstep (se 2 (by rfl) ⟨3594507, by rfl⟩ : syracuseStep 9585353 = 7189015) B7189015
theorem B6390235 : Blo 2099435 6390235 := bstep (se 1 (by rfl) ⟨4792676, by rfl⟩ : syracuseStep 6390235 = 9585353) B9585353
theorem B8520313 : Blo 2099435 8520313 := bstep (se 2 (by rfl) ⟨3195117, by rfl⟩ : syracuseStep 8520313 = 6390235) B6390235
theorem B11360417 : Blo 2099435 11360417 := bstep (se 2 (by rfl) ⟨4260156, by rfl⟩ : syracuseStep 11360417 = 8520313) B8520313
theorem B30294445 : Blo 2099435 30294445 := bstep (se 3 (by rfl) ⟨5680208, by rfl⟩ : syracuseStep 30294445 = 11360417) B11360417
theorem B40392593 : Blo 2099435 40392593 := bstep (se 2 (by rfl) ⟨15147222, by rfl⟩ : syracuseStep 40392593 = 30294445) B30294445
theorem B26928395 : Blo 2099435 26928395 := bstep (se 1 (by rfl) ⟨20196296, by rfl⟩ : syracuseStep 26928395 = 40392593) B40392593
theorem B17952263 : Blo 2099435 17952263 := bstep (se 1 (by rfl) ⟨13464197, by rfl⟩ : syracuseStep 17952263 = 26928395) B26928395
theorem B11968175 : Blo 2099435 11968175 := bstep (se 1 (by rfl) ⟨8976131, by rfl⟩ : syracuseStep 11968175 = 17952263) B17952263
theorem B7978783 : Blo 2099435 7978783 := bstep (se 1 (by rfl) ⟨5984087, by rfl⟩ : syracuseStep 7978783 = 11968175) B11968175
theorem B10638377 : Blo 2099435 10638377 := bstep (se 2 (by rfl) ⟨3989391, by rfl⟩ : syracuseStep 10638377 = 7978783) B7978783
theorem B7092251 : Blo 2099435 7092251 := bstep (se 1 (by rfl) ⟨5319188, by rfl⟩ : syracuseStep 7092251 = 10638377) B10638377
theorem B4728167 : Blo 2099435 4728167 := bstep (se 1 (by rfl) ⟨3546125, by rfl⟩ : syracuseStep 4728167 = 7092251) B7092251
theorem B3152111 : Blo 2099435 3152111 := bstep (se 1 (by rfl) ⟨2364083, by rfl⟩ : syracuseStep 3152111 = 4728167) B4728167
theorem B2101407 : Blo 2099435 2101407 := bstep (se 1 (by rfl) ⟨1576055, by rfl⟩ : syracuseStep 2101407 = 3152111) B3152111
theorem B3152117 : Blo 2099435 3152117 := bbase (se 5 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 3152117 = 295511) (by norm_num)
theorem B2101411 : Blo 2099435 2101411 := bstep (se 1 (by rfl) ⟨1576058, by rfl⟩ : syracuseStep 2101411 = 3152117) B3152117
theorem B4858085 : Blo 2099435 4858085 := bbase (se 4 (by rfl) ⟨455445, by rfl⟩ : syracuseStep 4858085 = 910891) (by norm_num)
theorem B3238723 : Blo 2099435 3238723 := bstep (se 1 (by rfl) ⟨2429042, by rfl⟩ : syracuseStep 3238723 = 4858085) B4858085
theorem B4318297 : Blo 2099435 4318297 := bstep (se 2 (by rfl) ⟨1619361, by rfl⟩ : syracuseStep 4318297 = 3238723) B3238723
theorem B92123669 : Blo 2099435 92123669 := bstep (se 6 (by rfl) ⟨2159148, by rfl⟩ : syracuseStep 92123669 = 4318297) B4318297
theorem B61415779 : Blo 2099435 61415779 := bstep (se 1 (by rfl) ⟨46061834, by rfl⟩ : syracuseStep 61415779 = 92123669) B92123669
theorem B81887705 : Blo 2099435 81887705 := bstep (se 2 (by rfl) ⟨30707889, by rfl⟩ : syracuseStep 81887705 = 61415779) B61415779
theorem B54591803 : Blo 2099435 54591803 := bstep (se 1 (by rfl) ⟨40943852, by rfl⟩ : syracuseStep 54591803 = 81887705) B81887705
theorem B36394535 : Blo 2099435 36394535 := bstep (se 1 (by rfl) ⟨27295901, by rfl⟩ : syracuseStep 36394535 = 54591803) B54591803
theorem B24263023 : Blo 2099435 24263023 := bstep (se 1 (by rfl) ⟨18197267, by rfl⟩ : syracuseStep 24263023 = 36394535) B36394535
theorem B32350697 : Blo 2099435 32350697 := bstep (se 2 (by rfl) ⟨12131511, by rfl⟩ : syracuseStep 32350697 = 24263023) B24263023
theorem B21567131 : Blo 2099435 21567131 := bstep (se 1 (by rfl) ⟨16175348, by rfl⟩ : syracuseStep 21567131 = 32350697) B32350697
theorem B14378087 : Blo 2099435 14378087 := bstep (se 1 (by rfl) ⟨10783565, by rfl⟩ : syracuseStep 14378087 = 21567131) B21567131
theorem B9585391 : Blo 2099435 9585391 := bstep (se 1 (by rfl) ⟨7189043, by rfl⟩ : syracuseStep 9585391 = 14378087) B14378087
theorem B12780521 : Blo 2099435 12780521 := bstep (se 2 (by rfl) ⟨4792695, by rfl⟩ : syracuseStep 12780521 = 9585391) B9585391
theorem B8520347 : Blo 2099435 8520347 := bstep (se 1 (by rfl) ⟨6390260, by rfl⟩ : syracuseStep 8520347 = 12780521) B12780521
theorem B22720925 : Blo 2099435 22720925 := bstep (se 3 (by rfl) ⟨4260173, by rfl⟩ : syracuseStep 22720925 = 8520347) B8520347
theorem B15147283 : Blo 2099435 15147283 := bstep (se 1 (by rfl) ⟨11360462, by rfl⟩ : syracuseStep 15147283 = 22720925) B22720925
theorem B20196377 : Blo 2099435 20196377 := bstep (se 2 (by rfl) ⟨7573641, by rfl⟩ : syracuseStep 20196377 = 15147283) B15147283
theorem B13464251 : Blo 2099435 13464251 := bstep (se 1 (by rfl) ⟨10098188, by rfl⟩ : syracuseStep 13464251 = 20196377) B20196377
theorem B8976167 : Blo 2099435 8976167 := bstep (se 1 (by rfl) ⟨6732125, by rfl⟩ : syracuseStep 8976167 = 13464251) B13464251
theorem B5984111 : Blo 2099435 5984111 := bstep (se 1 (by rfl) ⟨4488083, by rfl⟩ : syracuseStep 5984111 = 8976167) B8976167
theorem B3989407 : Blo 2099435 3989407 := bstep (se 1 (by rfl) ⟨2992055, by rfl⟩ : syracuseStep 3989407 = 5984111) B5984111
theorem B5319209 : Blo 2099435 5319209 := bstep (se 2 (by rfl) ⟨1994703, by rfl⟩ : syracuseStep 5319209 = 3989407) B3989407
theorem B3546139 : Blo 2099435 3546139 := bstep (se 1 (by rfl) ⟨2659604, by rfl⟩ : syracuseStep 3546139 = 5319209) B5319209
theorem B4728185 : Blo 2099435 4728185 := bstep (se 2 (by rfl) ⟨1773069, by rfl⟩ : syracuseStep 4728185 = 3546139) B3546139
theorem B3152123 : Blo 2099435 3152123 := bstep (se 1 (by rfl) ⟨2364092, by rfl⟩ : syracuseStep 3152123 = 4728185) B4728185
theorem B2101415 : Blo 2099435 2101415 := bstep (se 1 (by rfl) ⟨1576061, by rfl⟩ : syracuseStep 2101415 = 3152123) B3152123
theorem B2364097 : Blo 2099435 2364097 := bbase (se 2 (by rfl) ⟨886536, by rfl⟩ : syracuseStep 2364097 = 1773073) (by norm_num)
theorem B3152129 : Blo 2099435 3152129 := bstep (se 2 (by rfl) ⟨1182048, by rfl⟩ : syracuseStep 3152129 = 2364097) B2364097
theorem B2101419 : Blo 2099435 2101419 := bstep (se 1 (by rfl) ⟨1576064, by rfl⟩ : syracuseStep 2101419 = 3152129) B3152129
theorem B5319229 : Blo 2099435 5319229 := bbase (se 3 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 5319229 = 1994711) (by norm_num)
theorem B7092305 : Blo 2099435 7092305 := bstep (se 2 (by rfl) ⟨2659614, by rfl⟩ : syracuseStep 7092305 = 5319229) B5319229
theorem B4728203 : Blo 2099435 4728203 := bstep (se 1 (by rfl) ⟨3546152, by rfl⟩ : syracuseStep 4728203 = 7092305) B7092305
theorem B3152135 : Blo 2099435 3152135 := bstep (se 1 (by rfl) ⟨2364101, by rfl⟩ : syracuseStep 3152135 = 4728203) B4728203
theorem B2101423 : Blo 2099435 2101423 := bstep (se 1 (by rfl) ⟨1576067, by rfl⟩ : syracuseStep 2101423 = 3152135) B3152135
theorem B3152141 : Blo 2099435 3152141 := bbase (se 3 (by rfl) ⟨591026, by rfl⟩ : syracuseStep 3152141 = 1182053) (by norm_num)
theorem B2101427 : Blo 2099435 2101427 := bstep (se 1 (by rfl) ⟨1576070, by rfl⟩ : syracuseStep 2101427 = 3152141) B3152141
theorem B4728221 : Blo 2099435 4728221 := bbase (se 3 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 4728221 = 1773083) (by norm_num)
theorem B3152147 : Blo 2099435 3152147 := bstep (se 1 (by rfl) ⟨2364110, by rfl⟩ : syracuseStep 3152147 = 4728221) B4728221
theorem B2101431 : Blo 2099435 2101431 := bstep (se 1 (by rfl) ⟨1576073, by rfl⟩ : syracuseStep 2101431 = 3152147) B3152147
theorem B3546173 : Blo 2099435 3546173 := bbase (se 3 (by rfl) ⟨664907, by rfl⟩ : syracuseStep 3546173 = 1329815) (by norm_num)
theorem B2364115 : Blo 2099435 2364115 := bstep (se 1 (by rfl) ⟨1773086, by rfl⟩ : syracuseStep 2364115 = 3546173) B3546173
theorem B3152153 : Blo 2099435 3152153 := bstep (se 2 (by rfl) ⟨1182057, by rfl⟩ : syracuseStep 3152153 = 2364115) B2364115
theorem B2101435 : Blo 2099435 2101435 := bstep (se 1 (by rfl) ⟨1576076, by rfl⟩ : syracuseStep 2101435 = 3152153) B3152153
theorem C0 (j : ℕ) (h1 : 524858 ≤ j) (h2 : j ≤ 525358) : Blo 2099435 (4 * j + 3) := by
  interval_cases j
  · exact B2099435
  · exact B2099439
  · exact B2099443
  · exact B2099447
  · exact B2099451
  · exact B2099455
  · exact B2099459
  · exact B2099463
  · exact B2099467
  · exact B2099471
  · exact B2099475
  · exact B2099479
  · exact B2099483
  · exact B2099487
  · exact B2099491
  · exact B2099495
  · exact B2099499
  · exact B2099503
  · exact B2099507
  · exact B2099511
  · exact B2099515
  · exact B2099519
  · exact B2099523
  · exact B2099527
  · exact B2099531
  · exact B2099535
  · exact B2099539
  · exact B2099543
  · exact B2099547
  · exact B2099551
  · exact B2099555
  · exact B2099559
  · exact B2099563
  · exact B2099567
  · exact B2099571
  · exact B2099575
  · exact B2099579
  · exact B2099583
  · exact B2099587
  · exact B2099591
  · exact B2099595
  · exact B2099599
  · exact B2099603
  · exact B2099607
  · exact B2099611
  · exact B2099615
  · exact B2099619
  · exact B2099623
  · exact B2099627
  · exact B2099631
  · exact B2099635
  · exact B2099639
  · exact B2099643
  · exact B2099647
  · exact B2099651
  · exact B2099655
  · exact B2099659
  · exact B2099663
  · exact B2099667
  · exact B2099671
  · exact B2099675
  · exact B2099679
  · exact B2099683
  · exact B2099687
  · exact B2099691
  · exact B2099695
  · exact B2099699
  · exact B2099703
  · exact B2099707
  · exact B2099711
  · exact B2099715
  · exact B2099719
  · exact B2099723
  · exact B2099727
  · exact B2099731
  · exact B2099735
  · exact B2099739
  · exact B2099743
  · exact B2099747
  · exact B2099751
  · exact B2099755
  · exact B2099759
  · exact B2099763
  · exact B2099767
  · exact B2099771
  · exact B2099775
  · exact B2099779
  · exact B2099783
  · exact B2099787
  · exact B2099791
  · exact B2099795
  · exact B2099799
  · exact B2099803
  · exact B2099807
  · exact B2099811
  · exact B2099815
  · exact B2099819
  · exact B2099823
  · exact B2099827
  · exact B2099831
  · exact B2099835
  · exact B2099839
  · exact B2099843
  · exact B2099847
  · exact B2099851
  · exact B2099855
  · exact B2099859
  · exact B2099863
  · exact B2099867
  · exact B2099871
  · exact B2099875
  · exact B2099879
  · exact B2099883
  · exact B2099887
  · exact B2099891
  · exact B2099895
  · exact B2099899
  · exact B2099903
  · exact B2099907
  · exact B2099911
  · exact B2099915
  · exact B2099919
  · exact B2099923
  · exact B2099927
  · exact B2099931
  · exact B2099935
  · exact B2099939
  · exact B2099943
  · exact B2099947
  · exact B2099951
  · exact B2099955
  · exact B2099959
  · exact B2099963
  · exact B2099967
  · exact B2099971
  · exact B2099975
  · exact B2099979
  · exact B2099983
  · exact B2099987
  · exact B2099991
  · exact B2099995
  · exact B2099999
  · exact B2100003
  · exact B2100007
  · exact B2100011
  · exact B2100015
  · exact B2100019
  · exact B2100023
  · exact B2100027
  · exact B2100031
  · exact B2100035
  · exact B2100039
  · exact B2100043
  · exact B2100047
  · exact B2100051
  · exact B2100055
  · exact B2100059
  · exact B2100063
  · exact B2100067
  · exact B2100071
  · exact B2100075
  · exact B2100079
  · exact B2100083
  · exact B2100087
  · exact B2100091
  · exact B2100095
  · exact B2100099
  · exact B2100103
  · exact B2100107
  · exact B2100111
  · exact B2100115
  · exact B2100119
  · exact B2100123
  · exact B2100127
  · exact B2100131
  · exact B2100135
  · exact B2100139
  · exact B2100143
  · exact B2100147
  · exact B2100151
  · exact B2100155
  · exact B2100159
  · exact B2100163
  · exact B2100167
  · exact B2100171
  · exact B2100175
  · exact B2100179
  · exact B2100183
  · exact B2100187
  · exact B2100191
  · exact B2100195
  · exact B2100199
  · exact B2100203
  · exact B2100207
  · exact B2100211
  · exact B2100215
  · exact B2100219
  · exact B2100223
  · exact B2100227
  · exact B2100231
  · exact B2100235
  · exact B2100239
  · exact B2100243
  · exact B2100247
  · exact B2100251
  · exact B2100255
  · exact B2100259
  · exact B2100263
  · exact B2100267
  · exact B2100271
  · exact B2100275
  · exact B2100279
  · exact B2100283
  · exact B2100287
  · exact B2100291
  · exact B2100295
  · exact B2100299
  · exact B2100303
  · exact B2100307
  · exact B2100311
  · exact B2100315
  · exact B2100319
  · exact B2100323
  · exact B2100327
  · exact B2100331
  · exact B2100335
  · exact B2100339
  · exact B2100343
  · exact B2100347
  · exact B2100351
  · exact B2100355
  · exact B2100359
  · exact B2100363
  · exact B2100367
  · exact B2100371
  · exact B2100375
  · exact B2100379
  · exact B2100383
  · exact B2100387
  · exact B2100391
  · exact B2100395
  · exact B2100399
  · exact B2100403
  · exact B2100407
  · exact B2100411
  · exact B2100415
  · exact B2100419
  · exact B2100423
  · exact B2100427
  · exact B2100431
  · exact B2100435
  · exact B2100439
  · exact B2100443
  · exact B2100447
  · exact B2100451
  · exact B2100455
  · exact B2100459
  · exact B2100463
  · exact B2100467
  · exact B2100471
  · exact B2100475
  · exact B2100479
  · exact B2100483
  · exact B2100487
  · exact B2100491
  · exact B2100495
  · exact B2100499
  · exact B2100503
  · exact B2100507
  · exact B2100511
  · exact B2100515
  · exact B2100519
  · exact B2100523
  · exact B2100527
  · exact B2100531
  · exact B2100535
  · exact B2100539
  · exact B2100543
  · exact B2100547
  · exact B2100551
  · exact B2100555
  · exact B2100559
  · exact B2100563
  · exact B2100567
  · exact B2100571
  · exact B2100575
  · exact B2100579
  · exact B2100583
  · exact B2100587
  · exact B2100591
  · exact B2100595
  · exact B2100599
  · exact B2100603
  · exact B2100607
  · exact B2100611
  · exact B2100615
  · exact B2100619
  · exact B2100623
  · exact B2100627
  · exact B2100631
  · exact B2100635
  · exact B2100639
  · exact B2100643
  · exact B2100647
  · exact B2100651
  · exact B2100655
  · exact B2100659
  · exact B2100663
  · exact B2100667
  · exact B2100671
  · exact B2100675
  · exact B2100679
  · exact B2100683
  · exact B2100687
  · exact B2100691
  · exact B2100695
  · exact B2100699
  · exact B2100703
  · exact B2100707
  · exact B2100711
  · exact B2100715
  · exact B2100719
  · exact B2100723
  · exact B2100727
  · exact B2100731
  · exact B2100735
  · exact B2100739
  · exact B2100743
  · exact B2100747
  · exact B2100751
  · exact B2100755
  · exact B2100759
  · exact B2100763
  · exact B2100767
  · exact B2100771
  · exact B2100775
  · exact B2100779
  · exact B2100783
  · exact B2100787
  · exact B2100791
  · exact B2100795
  · exact B2100799
  · exact B2100803
  · exact B2100807
  · exact B2100811
  · exact B2100815
  · exact B2100819
  · exact B2100823
  · exact B2100827
  · exact B2100831
  · exact B2100835
  · exact B2100839
  · exact B2100843
  · exact B2100847
  · exact B2100851
  · exact B2100855
  · exact B2100859
  · exact B2100863
  · exact B2100867
  · exact B2100871
  · exact B2100875
  · exact B2100879
  · exact B2100883
  · exact B2100887
  · exact B2100891
  · exact B2100895
  · exact B2100899
  · exact B2100903
  · exact B2100907
  · exact B2100911
  · exact B2100915
  · exact B2100919
  · exact B2100923
  · exact B2100927
  · exact B2100931
  · exact B2100935
  · exact B2100939
  · exact B2100943
  · exact B2100947
  · exact B2100951
  · exact B2100955
  · exact B2100959
  · exact B2100963
  · exact B2100967
  · exact B2100971
  · exact B2100975
  · exact B2100979
  · exact B2100983
  · exact B2100987
  · exact B2100991
  · exact B2100995
  · exact B2100999
  · exact B2101003
  · exact B2101007
  · exact B2101011
  · exact B2101015
  · exact B2101019
  · exact B2101023
  · exact B2101027
  · exact B2101031
  · exact B2101035
  · exact B2101039
  · exact B2101043
  · exact B2101047
  · exact B2101051
  · exact B2101055
  · exact B2101059
  · exact B2101063
  · exact B2101067
  · exact B2101071
  · exact B2101075
  · exact B2101079
  · exact B2101083
  · exact B2101087
  · exact B2101091
  · exact B2101095
  · exact B2101099
  · exact B2101103
  · exact B2101107
  · exact B2101111
  · exact B2101115
  · exact B2101119
  · exact B2101123
  · exact B2101127
  · exact B2101131
  · exact B2101135
  · exact B2101139
  · exact B2101143
  · exact B2101147
  · exact B2101151
  · exact B2101155
  · exact B2101159
  · exact B2101163
  · exact B2101167
  · exact B2101171
  · exact B2101175
  · exact B2101179
  · exact B2101183
  · exact B2101187
  · exact B2101191
  · exact B2101195
  · exact B2101199
  · exact B2101203
  · exact B2101207
  · exact B2101211
  · exact B2101215
  · exact B2101219
  · exact B2101223
  · exact B2101227
  · exact B2101231
  · exact B2101235
  · exact B2101239
  · exact B2101243
  · exact B2101247
  · exact B2101251
  · exact B2101255
  · exact B2101259
  · exact B2101263
  · exact B2101267
  · exact B2101271
  · exact B2101275
  · exact B2101279
  · exact B2101283
  · exact B2101287
  · exact B2101291
  · exact B2101295
  · exact B2101299
  · exact B2101303
  · exact B2101307
  · exact B2101311
  · exact B2101315
  · exact B2101319
  · exact B2101323
  · exact B2101327
  · exact B2101331
  · exact B2101335
  · exact B2101339
  · exact B2101343
  · exact B2101347
  · exact B2101351
  · exact B2101355
  · exact B2101359
  · exact B2101363
  · exact B2101367
  · exact B2101371
  · exact B2101375
  · exact B2101379
  · exact B2101383
  · exact B2101387
  · exact B2101391
  · exact B2101395
  · exact B2101399
  · exact B2101403
  · exact B2101407
  · exact B2101411
  · exact B2101415
  · exact B2101419
  · exact B2101423
  · exact B2101427
  · exact B2101431
  · exact B2101435
theorem solution (m : ℕ) (hlo : 2099435 ≤ m) (hhi : m ≤ 2101435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 524858 ≤ j := by omega
    have hj2 : j ≤ 525358 := by omega
    have hb : Blo 2099435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
