-- Prove2me | solution 1 for syracuse_descends_range_2201435_2203435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:18.991333+00:00
-- url     : https://prove2.me/submissions/a083c4d5-6c16-4b51-9bbb-55615cdbca05

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

theorem B4701701 : Blo 2201435 4701701 := bbase (se 4 (by rfl) ⟨440784, by rfl⟩ : syracuseStep 4701701 = 881569) (by norm_num)
theorem B3134467 : Blo 2201435 3134467 := bstep (se 1 (by rfl) ⟨2350850, by rfl⟩ : syracuseStep 3134467 = 4701701) B4701701
theorem B4179289 : Blo 2201435 4179289 := bstep (se 2 (by rfl) ⟨1567233, by rfl⟩ : syracuseStep 4179289 = 3134467) B3134467
theorem B5572385 : Blo 2201435 5572385 := bstep (se 2 (by rfl) ⟨2089644, by rfl⟩ : syracuseStep 5572385 = 4179289) B4179289
theorem B3714923 : Blo 2201435 3714923 := bstep (se 1 (by rfl) ⟨2786192, by rfl⟩ : syracuseStep 3714923 = 5572385) B5572385
theorem B2476615 : Blo 2201435 2476615 := bstep (se 1 (by rfl) ⟨1857461, by rfl⟩ : syracuseStep 2476615 = 3714923) B3714923
theorem B3302153 : Blo 2201435 3302153 := bstep (se 2 (by rfl) ⟨1238307, by rfl⟩ : syracuseStep 3302153 = 2476615) B2476615
theorem B2201435 : Blo 2201435 2201435 := bstep (se 1 (by rfl) ⟨1651076, by rfl⟩ : syracuseStep 2201435 = 3302153) B3302153
theorem B11144789 : Blo 2201435 11144789 := bbase (se 8 (by rfl) ⟨65301, by rfl⟩ : syracuseStep 11144789 = 130603) (by norm_num)
theorem B7429859 : Blo 2201435 7429859 := bstep (se 1 (by rfl) ⟨5572394, by rfl⟩ : syracuseStep 7429859 = 11144789) B11144789
theorem B4953239 : Blo 2201435 4953239 := bstep (se 1 (by rfl) ⟨3714929, by rfl⟩ : syracuseStep 4953239 = 7429859) B7429859
theorem B3302159 : Blo 2201435 3302159 := bstep (se 1 (by rfl) ⟨2476619, by rfl⟩ : syracuseStep 3302159 = 4953239) B4953239
theorem B2201439 : Blo 2201435 2201439 := bstep (se 1 (by rfl) ⟨1651079, by rfl⟩ : syracuseStep 2201439 = 3302159) B3302159
theorem B3302165 : Blo 2201435 3302165 := bbase (se 6 (by rfl) ⟨77394, by rfl⟩ : syracuseStep 3302165 = 154789) (by norm_num)
theorem B2201443 : Blo 2201435 2201443 := bstep (se 1 (by rfl) ⟨1651082, by rfl⟩ : syracuseStep 2201443 = 3302165) B3302165
theorem B3765629 : Blo 2201435 3765629 := bbase (se 3 (by rfl) ⟨706055, by rfl⟩ : syracuseStep 3765629 = 1412111) (by norm_num)
theorem B10041677 : Blo 2201435 10041677 := bstep (se 3 (by rfl) ⟨1882814, by rfl⟩ : syracuseStep 10041677 = 3765629) B3765629
theorem B6694451 : Blo 2201435 6694451 := bstep (se 1 (by rfl) ⟨5020838, by rfl⟩ : syracuseStep 6694451 = 10041677) B10041677
theorem B4462967 : Blo 2201435 4462967 := bstep (se 1 (by rfl) ⟨3347225, by rfl⟩ : syracuseStep 4462967 = 6694451) B6694451
theorem B2975311 : Blo 2201435 2975311 := bstep (se 1 (by rfl) ⟨2231483, by rfl⟩ : syracuseStep 2975311 = 4462967) B4462967
theorem B15868325 : Blo 2201435 15868325 := bstep (se 4 (by rfl) ⟨1487655, by rfl⟩ : syracuseStep 15868325 = 2975311) B2975311
theorem B42315533 : Blo 2201435 42315533 := bstep (se 3 (by rfl) ⟨7934162, by rfl⟩ : syracuseStep 42315533 = 15868325) B15868325
theorem B28210355 : Blo 2201435 28210355 := bstep (se 1 (by rfl) ⟨21157766, by rfl⟩ : syracuseStep 28210355 = 42315533) B42315533
theorem B18806903 : Blo 2201435 18806903 := bstep (se 1 (by rfl) ⟨14105177, by rfl⟩ : syracuseStep 18806903 = 28210355) B28210355
theorem B12537935 : Blo 2201435 12537935 := bstep (se 1 (by rfl) ⟨9403451, by rfl⟩ : syracuseStep 12537935 = 18806903) B18806903
theorem B8358623 : Blo 2201435 8358623 := bstep (se 1 (by rfl) ⟨6268967, by rfl⟩ : syracuseStep 8358623 = 12537935) B12537935
theorem B5572415 : Blo 2201435 5572415 := bstep (se 1 (by rfl) ⟨4179311, by rfl⟩ : syracuseStep 5572415 = 8358623) B8358623
theorem B3714943 : Blo 2201435 3714943 := bstep (se 1 (by rfl) ⟨2786207, by rfl⟩ : syracuseStep 3714943 = 5572415) B5572415
theorem B4953257 : Blo 2201435 4953257 := bstep (se 2 (by rfl) ⟨1857471, by rfl⟩ : syracuseStep 4953257 = 3714943) B3714943
theorem B3302171 : Blo 2201435 3302171 := bstep (se 1 (by rfl) ⟨2476628, by rfl⟩ : syracuseStep 3302171 = 4953257) B4953257
theorem B2201447 : Blo 2201435 2201447 := bstep (se 1 (by rfl) ⟨1651085, by rfl⟩ : syracuseStep 2201447 = 3302171) B3302171
theorem B2476633 : Blo 2201435 2476633 := bbase (se 2 (by rfl) ⟨928737, by rfl⟩ : syracuseStep 2476633 = 1857475) (by norm_num)
theorem B3302177 : Blo 2201435 3302177 := bstep (se 2 (by rfl) ⟨1238316, by rfl⟩ : syracuseStep 3302177 = 2476633) B2476633
theorem B2201451 : Blo 2201435 2201451 := bstep (se 1 (by rfl) ⟨1651088, by rfl⟩ : syracuseStep 2201451 = 3302177) B3302177
theorem B30125141 : Blo 2201435 30125141 := bbase (se 8 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 30125141 = 353029) (by norm_num)
theorem B20083427 : Blo 2201435 20083427 := bstep (se 1 (by rfl) ⟨15062570, by rfl⟩ : syracuseStep 20083427 = 30125141) B30125141
theorem B13388951 : Blo 2201435 13388951 := bstep (se 1 (by rfl) ⟨10041713, by rfl⟩ : syracuseStep 13388951 = 20083427) B20083427
theorem B8925967 : Blo 2201435 8925967 := bstep (se 1 (by rfl) ⟨6694475, by rfl⟩ : syracuseStep 8925967 = 13388951) B13388951
theorem B11901289 : Blo 2201435 11901289 := bstep (se 2 (by rfl) ⟨4462983, by rfl⟩ : syracuseStep 11901289 = 8925967) B8925967
theorem B15868385 : Blo 2201435 15868385 := bstep (se 2 (by rfl) ⟨5950644, by rfl⟩ : syracuseStep 15868385 = 11901289) B11901289
theorem B10578923 : Blo 2201435 10578923 := bstep (se 1 (by rfl) ⟨7934192, by rfl⟩ : syracuseStep 10578923 = 15868385) B15868385
theorem B7052615 : Blo 2201435 7052615 := bstep (se 1 (by rfl) ⟨5289461, by rfl⟩ : syracuseStep 7052615 = 10578923) B10578923
theorem B4701743 : Blo 2201435 4701743 := bstep (se 1 (by rfl) ⟨3526307, by rfl⟩ : syracuseStep 4701743 = 7052615) B7052615
theorem B3134495 : Blo 2201435 3134495 := bstep (se 1 (by rfl) ⟨2350871, by rfl⟩ : syracuseStep 3134495 = 4701743) B4701743
theorem B8358653 : Blo 2201435 8358653 := bstep (se 3 (by rfl) ⟨1567247, by rfl⟩ : syracuseStep 8358653 = 3134495) B3134495
theorem B5572435 : Blo 2201435 5572435 := bstep (se 1 (by rfl) ⟨4179326, by rfl⟩ : syracuseStep 5572435 = 8358653) B8358653
theorem B7429913 : Blo 2201435 7429913 := bstep (se 2 (by rfl) ⟨2786217, by rfl⟩ : syracuseStep 7429913 = 5572435) B5572435
theorem B4953275 : Blo 2201435 4953275 := bstep (se 1 (by rfl) ⟨3714956, by rfl⟩ : syracuseStep 4953275 = 7429913) B7429913
theorem B3302183 : Blo 2201435 3302183 := bstep (se 1 (by rfl) ⟨2476637, by rfl⟩ : syracuseStep 3302183 = 4953275) B4953275
theorem B2201455 : Blo 2201435 2201455 := bstep (se 1 (by rfl) ⟨1651091, by rfl⟩ : syracuseStep 2201455 = 3302183) B3302183
theorem B3302189 : Blo 2201435 3302189 := bbase (se 3 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 3302189 = 1238321) (by norm_num)
theorem B2201459 : Blo 2201435 2201459 := bstep (se 1 (by rfl) ⟨1651094, by rfl⟩ : syracuseStep 2201459 = 3302189) B3302189
theorem B4953293 : Blo 2201435 4953293 := bbase (se 3 (by rfl) ⟨928742, by rfl⟩ : syracuseStep 4953293 = 1857485) (by norm_num)
theorem B3302195 : Blo 2201435 3302195 := bstep (se 1 (by rfl) ⟨2476646, by rfl⟩ : syracuseStep 3302195 = 4953293) B4953293
theorem B2201463 : Blo 2201435 2201463 := bstep (se 1 (by rfl) ⟨1651097, by rfl⟩ : syracuseStep 2201463 = 3302195) B3302195
theorem B2786233 : Blo 2201435 2786233 := bbase (se 2 (by rfl) ⟨1044837, by rfl⟩ : syracuseStep 2786233 = 2089675) (by norm_num)
theorem B3714977 : Blo 2201435 3714977 := bstep (se 2 (by rfl) ⟨1393116, by rfl⟩ : syracuseStep 3714977 = 2786233) B2786233
theorem B2476651 : Blo 2201435 2476651 := bstep (se 1 (by rfl) ⟨1857488, by rfl⟩ : syracuseStep 2476651 = 3714977) B3714977
theorem B3302201 : Blo 2201435 3302201 := bstep (se 2 (by rfl) ⟨1238325, by rfl⟩ : syracuseStep 3302201 = 2476651) B2476651
theorem B2201467 : Blo 2201435 2201467 := bstep (se 1 (by rfl) ⟨1651100, by rfl⟩ : syracuseStep 2201467 = 3302201) B3302201
theorem B8472757 : Blo 2201435 8472757 := bbase (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) (by norm_num)
theorem B11297009 : Blo 2201435 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B30125357 : Blo 2201435 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B20083571 : Blo 2201435 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B13389047 : Blo 2201435 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B8926031 : Blo 2201435 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B5950687 : Blo 2201435 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B7934249 : Blo 2201435 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B5289499 : Blo 2201435 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B7052665 : Blo 2201435 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B9403553 : Blo 2201435 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B25076141 : Blo 2201435 25076141 := bstep (se 3 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 25076141 = 9403553) B9403553
theorem B16717427 : Blo 2201435 16717427 := bstep (se 1 (by rfl) ⟨12538070, by rfl⟩ : syracuseStep 16717427 = 25076141) B25076141
theorem B11144951 : Blo 2201435 11144951 := bstep (se 1 (by rfl) ⟨8358713, by rfl⟩ : syracuseStep 11144951 = 16717427) B16717427
theorem B7429967 : Blo 2201435 7429967 := bstep (se 1 (by rfl) ⟨5572475, by rfl⟩ : syracuseStep 7429967 = 11144951) B11144951
theorem B4953311 : Blo 2201435 4953311 := bstep (se 1 (by rfl) ⟨3714983, by rfl⟩ : syracuseStep 4953311 = 7429967) B7429967
theorem B3302207 : Blo 2201435 3302207 := bstep (se 1 (by rfl) ⟨2476655, by rfl⟩ : syracuseStep 3302207 = 4953311) B4953311
theorem B2201471 : Blo 2201435 2201471 := bstep (se 1 (by rfl) ⟨1651103, by rfl⟩ : syracuseStep 2201471 = 3302207) B3302207
theorem B3302213 : Blo 2201435 3302213 := bbase (se 4 (by rfl) ⟨309582, by rfl⟩ : syracuseStep 3302213 = 619165) (by norm_num)
theorem B2201475 : Blo 2201435 2201475 := bstep (se 1 (by rfl) ⟨1651106, by rfl⟩ : syracuseStep 2201475 = 3302213) B3302213
theorem B3714997 : Blo 2201435 3714997 := bbase (se 5 (by rfl) ⟨174140, by rfl⟩ : syracuseStep 3714997 = 348281) (by norm_num)
theorem B4953329 : Blo 2201435 4953329 := bstep (se 2 (by rfl) ⟨1857498, by rfl⟩ : syracuseStep 4953329 = 3714997) B3714997
theorem B3302219 : Blo 2201435 3302219 := bstep (se 1 (by rfl) ⟨2476664, by rfl⟩ : syracuseStep 3302219 = 4953329) B4953329
theorem B2201479 : Blo 2201435 2201479 := bstep (se 1 (by rfl) ⟨1651109, by rfl⟩ : syracuseStep 2201479 = 3302219) B3302219
theorem B2476669 : Blo 2201435 2476669 := bbase (se 3 (by rfl) ⟨464375, by rfl⟩ : syracuseStep 2476669 = 928751) (by norm_num)
theorem B3302225 : Blo 2201435 3302225 := bstep (se 2 (by rfl) ⟨1238334, by rfl⟩ : syracuseStep 3302225 = 2476669) B2476669
theorem B2201483 : Blo 2201435 2201483 := bstep (se 1 (by rfl) ⟨1651112, by rfl⟩ : syracuseStep 2201483 = 3302225) B3302225
theorem B7430021 : Blo 2201435 7430021 := bbase (se 4 (by rfl) ⟨696564, by rfl⟩ : syracuseStep 7430021 = 1393129) (by norm_num)
theorem B4953347 : Blo 2201435 4953347 := bstep (se 1 (by rfl) ⟨3715010, by rfl⟩ : syracuseStep 4953347 = 7430021) B7430021
theorem B3302231 : Blo 2201435 3302231 := bstep (se 1 (by rfl) ⟨2476673, by rfl⟩ : syracuseStep 3302231 = 4953347) B4953347
theorem B2201487 : Blo 2201435 2201487 := bstep (se 1 (by rfl) ⟨1651115, by rfl⟩ : syracuseStep 2201487 = 3302231) B3302231
theorem B3302237 : Blo 2201435 3302237 := bbase (se 3 (by rfl) ⟨619169, by rfl⟩ : syracuseStep 3302237 = 1238339) (by norm_num)
theorem B2201491 : Blo 2201435 2201491 := bstep (se 1 (by rfl) ⟨1651118, by rfl⟩ : syracuseStep 2201491 = 3302237) B3302237
theorem B4953365 : Blo 2201435 4953365 := bbase (se 6 (by rfl) ⟨116094, by rfl⟩ : syracuseStep 4953365 = 232189) (by norm_num)
theorem B3302243 : Blo 2201435 3302243 := bstep (se 1 (by rfl) ⟨2476682, by rfl⟩ : syracuseStep 3302243 = 4953365) B4953365
theorem B2201495 : Blo 2201435 2201495 := bstep (se 1 (by rfl) ⟨1651121, by rfl⟩ : syracuseStep 2201495 = 3302243) B3302243
theorem B8358821 : Blo 2201435 8358821 := bbase (se 4 (by rfl) ⟨783639, by rfl⟩ : syracuseStep 8358821 = 1567279) (by norm_num)
theorem B5572547 : Blo 2201435 5572547 := bstep (se 1 (by rfl) ⟨4179410, by rfl⟩ : syracuseStep 5572547 = 8358821) B8358821
theorem B3715031 : Blo 2201435 3715031 := bstep (se 1 (by rfl) ⟨2786273, by rfl⟩ : syracuseStep 3715031 = 5572547) B5572547
theorem B2476687 : Blo 2201435 2476687 := bstep (se 1 (by rfl) ⟨1857515, by rfl⟩ : syracuseStep 2476687 = 3715031) B3715031
theorem B3302249 : Blo 2201435 3302249 := bstep (se 2 (by rfl) ⟨1238343, by rfl⟩ : syracuseStep 3302249 = 2476687) B2476687
theorem B2201499 : Blo 2201435 2201499 := bstep (se 1 (by rfl) ⟨1651124, by rfl⟩ : syracuseStep 2201499 = 3302249) B3302249
theorem B4701845 : Blo 2201435 4701845 := bbase (se 6 (by rfl) ⟨110199, by rfl⟩ : syracuseStep 4701845 = 220399) (by norm_num)
theorem B12538253 : Blo 2201435 12538253 := bstep (se 3 (by rfl) ⟨2350922, by rfl⟩ : syracuseStep 12538253 = 4701845) B4701845
theorem B8358835 : Blo 2201435 8358835 := bstep (se 1 (by rfl) ⟨6269126, by rfl⟩ : syracuseStep 8358835 = 12538253) B12538253
theorem B11145113 : Blo 2201435 11145113 := bstep (se 2 (by rfl) ⟨4179417, by rfl⟩ : syracuseStep 11145113 = 8358835) B8358835
theorem B7430075 : Blo 2201435 7430075 := bstep (se 1 (by rfl) ⟨5572556, by rfl⟩ : syracuseStep 7430075 = 11145113) B11145113
theorem B4953383 : Blo 2201435 4953383 := bstep (se 1 (by rfl) ⟨3715037, by rfl⟩ : syracuseStep 4953383 = 7430075) B7430075
theorem B3302255 : Blo 2201435 3302255 := bstep (se 1 (by rfl) ⟨2476691, by rfl⟩ : syracuseStep 3302255 = 4953383) B4953383
theorem B2201503 : Blo 2201435 2201503 := bstep (se 1 (by rfl) ⟨1651127, by rfl⟩ : syracuseStep 2201503 = 3302255) B3302255
theorem B3302261 : Blo 2201435 3302261 := bbase (se 5 (by rfl) ⟨154793, by rfl⟩ : syracuseStep 3302261 = 309587) (by norm_num)
theorem B2201507 : Blo 2201435 2201507 := bstep (se 1 (by rfl) ⟨1651130, by rfl⟩ : syracuseStep 2201507 = 3302261) B3302261
theorem B22902709 : Blo 2201435 22902709 := bbase (se 5 (by rfl) ⟨1073564, by rfl⟩ : syracuseStep 22902709 = 2147129) (by norm_num)
theorem B30536945 : Blo 2201435 30536945 := bstep (se 2 (by rfl) ⟨11451354, by rfl⟩ : syracuseStep 30536945 = 22902709) B22902709
theorem B20357963 : Blo 2201435 20357963 := bstep (se 1 (by rfl) ⟨15268472, by rfl⟩ : syracuseStep 20357963 = 30536945) B30536945
theorem B13571975 : Blo 2201435 13571975 := bstep (se 1 (by rfl) ⟨10178981, by rfl⟩ : syracuseStep 13571975 = 20357963) B20357963
theorem B36191933 : Blo 2201435 36191933 := bstep (se 3 (by rfl) ⟨6785987, by rfl⟩ : syracuseStep 36191933 = 13571975) B13571975
theorem B24127955 : Blo 2201435 24127955 := bstep (se 1 (by rfl) ⟨18095966, by rfl⟩ : syracuseStep 24127955 = 36191933) B36191933
theorem B16085303 : Blo 2201435 16085303 := bstep (se 1 (by rfl) ⟨12063977, by rfl⟩ : syracuseStep 16085303 = 24127955) B24127955
theorem B10723535 : Blo 2201435 10723535 := bstep (se 1 (by rfl) ⟨8042651, by rfl⟩ : syracuseStep 10723535 = 16085303) B16085303
theorem B7149023 : Blo 2201435 7149023 := bstep (se 1 (by rfl) ⟨5361767, by rfl⟩ : syracuseStep 7149023 = 10723535) B10723535
theorem B4766015 : Blo 2201435 4766015 := bstep (se 1 (by rfl) ⟨3574511, by rfl⟩ : syracuseStep 4766015 = 7149023) B7149023
theorem B3177343 : Blo 2201435 3177343 := bstep (se 1 (by rfl) ⟨2383007, by rfl⟩ : syracuseStep 3177343 = 4766015) B4766015
theorem B4236457 : Blo 2201435 4236457 := bstep (se 2 (by rfl) ⟨1588671, by rfl⟩ : syracuseStep 4236457 = 3177343) B3177343
theorem B5648609 : Blo 2201435 5648609 := bstep (se 2 (by rfl) ⟨2118228, by rfl⟩ : syracuseStep 5648609 = 4236457) B4236457
theorem B3765739 : Blo 2201435 3765739 := bstep (se 1 (by rfl) ⟨2824304, by rfl⟩ : syracuseStep 3765739 = 5648609) B5648609
theorem B5020985 : Blo 2201435 5020985 := bstep (se 2 (by rfl) ⟨1882869, by rfl⟩ : syracuseStep 5020985 = 3765739) B3765739
theorem B13389293 : Blo 2201435 13389293 := bstep (se 3 (by rfl) ⟨2510492, by rfl⟩ : syracuseStep 13389293 = 5020985) B5020985
theorem B8926195 : Blo 2201435 8926195 := bstep (se 1 (by rfl) ⟨6694646, by rfl⟩ : syracuseStep 8926195 = 13389293) B13389293
theorem B11901593 : Blo 2201435 11901593 := bstep (se 2 (by rfl) ⟨4463097, by rfl⟩ : syracuseStep 11901593 = 8926195) B8926195
theorem B7934395 : Blo 2201435 7934395 := bstep (se 1 (by rfl) ⟨5950796, by rfl⟩ : syracuseStep 7934395 = 11901593) B11901593
theorem B10579193 : Blo 2201435 10579193 := bstep (se 2 (by rfl) ⟨3967197, by rfl⟩ : syracuseStep 10579193 = 7934395) B7934395
theorem B7052795 : Blo 2201435 7052795 := bstep (se 1 (by rfl) ⟨5289596, by rfl⟩ : syracuseStep 7052795 = 10579193) B10579193
theorem B4701863 : Blo 2201435 4701863 := bstep (se 1 (by rfl) ⟨3526397, by rfl⟩ : syracuseStep 4701863 = 7052795) B7052795
theorem B3134575 : Blo 2201435 3134575 := bstep (se 1 (by rfl) ⟨2350931, by rfl⟩ : syracuseStep 3134575 = 4701863) B4701863
theorem B4179433 : Blo 2201435 4179433 := bstep (se 2 (by rfl) ⟨1567287, by rfl⟩ : syracuseStep 4179433 = 3134575) B3134575
theorem B5572577 : Blo 2201435 5572577 := bstep (se 2 (by rfl) ⟨2089716, by rfl⟩ : syracuseStep 5572577 = 4179433) B4179433
theorem B3715051 : Blo 2201435 3715051 := bstep (se 1 (by rfl) ⟨2786288, by rfl⟩ : syracuseStep 3715051 = 5572577) B5572577
theorem B4953401 : Blo 2201435 4953401 := bstep (se 2 (by rfl) ⟨1857525, by rfl⟩ : syracuseStep 4953401 = 3715051) B3715051
theorem B3302267 : Blo 2201435 3302267 := bstep (se 1 (by rfl) ⟨2476700, by rfl⟩ : syracuseStep 3302267 = 4953401) B4953401
theorem B2201511 : Blo 2201435 2201511 := bstep (se 1 (by rfl) ⟨1651133, by rfl⟩ : syracuseStep 2201511 = 3302267) B3302267
theorem B2476705 : Blo 2201435 2476705 := bbase (se 2 (by rfl) ⟨928764, by rfl⟩ : syracuseStep 2476705 = 1857529) (by norm_num)
theorem B3302273 : Blo 2201435 3302273 := bstep (se 2 (by rfl) ⟨1238352, by rfl⟩ : syracuseStep 3302273 = 2476705) B2476705
theorem B2201515 : Blo 2201435 2201515 := bstep (se 1 (by rfl) ⟨1651136, by rfl⟩ : syracuseStep 2201515 = 3302273) B3302273
theorem B5572597 : Blo 2201435 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B7430129 : Blo 2201435 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B4953419 : Blo 2201435 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B3302279 : Blo 2201435 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B2201519 : Blo 2201435 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B3302285 : Blo 2201435 3302285 := bbase (se 3 (by rfl) ⟨619178, by rfl⟩ : syracuseStep 3302285 = 1238357) (by norm_num)
theorem B2201523 : Blo 2201435 2201523 := bstep (se 1 (by rfl) ⟨1651142, by rfl⟩ : syracuseStep 2201523 = 3302285) B3302285
theorem B4953437 : Blo 2201435 4953437 := bbase (se 3 (by rfl) ⟨928769, by rfl⟩ : syracuseStep 4953437 = 1857539) (by norm_num)
theorem B3302291 : Blo 2201435 3302291 := bstep (se 1 (by rfl) ⟨2476718, by rfl⟩ : syracuseStep 3302291 = 4953437) B4953437
theorem B2201527 : Blo 2201435 2201527 := bstep (se 1 (by rfl) ⟨1651145, by rfl⟩ : syracuseStep 2201527 = 3302291) B3302291
theorem B3715085 : Blo 2201435 3715085 := bbase (se 3 (by rfl) ⟨696578, by rfl⟩ : syracuseStep 3715085 = 1393157) (by norm_num)
theorem B2476723 : Blo 2201435 2476723 := bstep (se 1 (by rfl) ⟨1857542, by rfl⟩ : syracuseStep 2476723 = 3715085) B3715085
theorem B3302297 : Blo 2201435 3302297 := bstep (se 2 (by rfl) ⟨1238361, by rfl⟩ : syracuseStep 3302297 = 2476723) B2476723
theorem B2201531 : Blo 2201435 2201531 := bstep (se 1 (by rfl) ⟨1651148, by rfl⟩ : syracuseStep 2201531 = 3302297) B3302297
theorem B5289653 : Blo 2201435 5289653 := bbase (se 5 (by rfl) ⟨247952, by rfl⟩ : syracuseStep 5289653 = 495905) (by norm_num)
theorem B3526435 : Blo 2201435 3526435 := bstep (se 1 (by rfl) ⟨2644826, by rfl⟩ : syracuseStep 3526435 = 5289653) B5289653
theorem B18807653 : Blo 2201435 18807653 := bstep (se 4 (by rfl) ⟨1763217, by rfl⟩ : syracuseStep 18807653 = 3526435) B3526435
theorem B12538435 : Blo 2201435 12538435 := bstep (se 1 (by rfl) ⟨9403826, by rfl⟩ : syracuseStep 12538435 = 18807653) B18807653
theorem B16717913 : Blo 2201435 16717913 := bstep (se 2 (by rfl) ⟨6269217, by rfl⟩ : syracuseStep 16717913 = 12538435) B12538435
theorem B11145275 : Blo 2201435 11145275 := bstep (se 1 (by rfl) ⟨8358956, by rfl⟩ : syracuseStep 11145275 = 16717913) B16717913
theorem B7430183 : Blo 2201435 7430183 := bstep (se 1 (by rfl) ⟨5572637, by rfl⟩ : syracuseStep 7430183 = 11145275) B11145275
theorem B4953455 : Blo 2201435 4953455 := bstep (se 1 (by rfl) ⟨3715091, by rfl⟩ : syracuseStep 4953455 = 7430183) B7430183
theorem B3302303 : Blo 2201435 3302303 := bstep (se 1 (by rfl) ⟨2476727, by rfl⟩ : syracuseStep 3302303 = 4953455) B4953455
theorem B2201535 : Blo 2201435 2201535 := bstep (se 1 (by rfl) ⟨1651151, by rfl⟩ : syracuseStep 2201535 = 3302303) B3302303
theorem B3302309 : Blo 2201435 3302309 := bbase (se 4 (by rfl) ⟨309591, by rfl⟩ : syracuseStep 3302309 = 619183) (by norm_num)
theorem B2201539 : Blo 2201435 2201539 := bstep (se 1 (by rfl) ⟨1651154, by rfl⟩ : syracuseStep 2201539 = 3302309) B3302309
theorem B2786329 : Blo 2201435 2786329 := bbase (se 2 (by rfl) ⟨1044873, by rfl⟩ : syracuseStep 2786329 = 2089747) (by norm_num)
theorem B3715105 : Blo 2201435 3715105 := bstep (se 2 (by rfl) ⟨1393164, by rfl⟩ : syracuseStep 3715105 = 2786329) B2786329
theorem B4953473 : Blo 2201435 4953473 := bstep (se 2 (by rfl) ⟨1857552, by rfl⟩ : syracuseStep 4953473 = 3715105) B3715105
theorem B3302315 : Blo 2201435 3302315 := bstep (se 1 (by rfl) ⟨2476736, by rfl⟩ : syracuseStep 3302315 = 4953473) B4953473
theorem B2201543 : Blo 2201435 2201543 := bstep (se 1 (by rfl) ⟨1651157, by rfl⟩ : syracuseStep 2201543 = 3302315) B3302315
theorem B2476741 : Blo 2201435 2476741 := bbase (se 4 (by rfl) ⟨232194, by rfl⟩ : syracuseStep 2476741 = 464389) (by norm_num)
theorem B3302321 : Blo 2201435 3302321 := bstep (se 2 (by rfl) ⟨1238370, by rfl⟩ : syracuseStep 3302321 = 2476741) B2476741
theorem B2201547 : Blo 2201435 2201547 := bstep (se 1 (by rfl) ⟨1651160, by rfl⟩ : syracuseStep 2201547 = 3302321) B3302321
theorem B4179509 : Blo 2201435 4179509 := bbase (se 5 (by rfl) ⟨195914, by rfl⟩ : syracuseStep 4179509 = 391829) (by norm_num)
theorem B2786339 : Blo 2201435 2786339 := bstep (se 1 (by rfl) ⟨2089754, by rfl⟩ : syracuseStep 2786339 = 4179509) B4179509
theorem B7430237 : Blo 2201435 7430237 := bstep (se 3 (by rfl) ⟨1393169, by rfl⟩ : syracuseStep 7430237 = 2786339) B2786339
theorem B4953491 : Blo 2201435 4953491 := bstep (se 1 (by rfl) ⟨3715118, by rfl⟩ : syracuseStep 4953491 = 7430237) B7430237
theorem B3302327 : Blo 2201435 3302327 := bstep (se 1 (by rfl) ⟨2476745, by rfl⟩ : syracuseStep 3302327 = 4953491) B4953491
theorem B2201551 : Blo 2201435 2201551 := bstep (se 1 (by rfl) ⟨1651163, by rfl⟩ : syracuseStep 2201551 = 3302327) B3302327
theorem B3302333 : Blo 2201435 3302333 := bbase (se 3 (by rfl) ⟨619187, by rfl⟩ : syracuseStep 3302333 = 1238375) (by norm_num)
theorem B2201555 : Blo 2201435 2201555 := bstep (se 1 (by rfl) ⟨1651166, by rfl⟩ : syracuseStep 2201555 = 3302333) B3302333
theorem B4953509 : Blo 2201435 4953509 := bbase (se 4 (by rfl) ⟨464391, by rfl⟩ : syracuseStep 4953509 = 928783) (by norm_num)
theorem B3302339 : Blo 2201435 3302339 := bstep (se 1 (by rfl) ⟨2476754, by rfl⟩ : syracuseStep 3302339 = 4953509) B4953509
theorem B2201559 : Blo 2201435 2201559 := bstep (se 1 (by rfl) ⟨1651169, by rfl⟩ : syracuseStep 2201559 = 3302339) B3302339
theorem B5572709 : Blo 2201435 5572709 := bbase (se 4 (by rfl) ⟨522441, by rfl⟩ : syracuseStep 5572709 = 1044883) (by norm_num)
theorem B3715139 : Blo 2201435 3715139 := bstep (se 1 (by rfl) ⟨2786354, by rfl⟩ : syracuseStep 3715139 = 5572709) B5572709
theorem B2476759 : Blo 2201435 2476759 := bstep (se 1 (by rfl) ⟨1857569, by rfl⟩ : syracuseStep 2476759 = 3715139) B3715139
theorem B3302345 : Blo 2201435 3302345 := bstep (se 2 (by rfl) ⟨1238379, by rfl⟩ : syracuseStep 3302345 = 2476759) B2476759
theorem B2201563 : Blo 2201435 2201563 := bstep (se 1 (by rfl) ⟨1651172, by rfl⟩ : syracuseStep 2201563 = 3302345) B3302345
theorem B7934597 : Blo 2201435 7934597 := bbase (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) (by norm_num)
theorem B5289731 : Blo 2201435 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B3526487 : Blo 2201435 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B2350991 : Blo 2201435 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B6269309 : Blo 2201435 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B4179539 : Blo 2201435 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B11145437 : Blo 2201435 11145437 := bstep (se 3 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 11145437 = 4179539) B4179539
theorem B7430291 : Blo 2201435 7430291 := bstep (se 1 (by rfl) ⟨5572718, by rfl⟩ : syracuseStep 7430291 = 11145437) B11145437
theorem B4953527 : Blo 2201435 4953527 := bstep (se 1 (by rfl) ⟨3715145, by rfl⟩ : syracuseStep 4953527 = 7430291) B7430291
theorem B3302351 : Blo 2201435 3302351 := bstep (se 1 (by rfl) ⟨2476763, by rfl⟩ : syracuseStep 3302351 = 4953527) B4953527
theorem B2201567 : Blo 2201435 2201567 := bstep (se 1 (by rfl) ⟨1651175, by rfl⟩ : syracuseStep 2201567 = 3302351) B3302351
theorem B3302357 : Blo 2201435 3302357 := bbase (se 7 (by rfl) ⟨38699, by rfl⟩ : syracuseStep 3302357 = 77399) (by norm_num)
theorem B2201571 : Blo 2201435 2201571 := bstep (se 1 (by rfl) ⟨1651178, by rfl⟩ : syracuseStep 2201571 = 3302357) B3302357
theorem B8359109 : Blo 2201435 8359109 := bbase (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) (by norm_num)
theorem B5572739 : Blo 2201435 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B3715159 : Blo 2201435 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B4953545 : Blo 2201435 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B3302363 : Blo 2201435 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B2201575 : Blo 2201435 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B2476777 : Blo 2201435 2476777 := bbase (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) (by norm_num)
theorem B3302369 : Blo 2201435 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B2201579 : Blo 2201435 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B12538709 : Blo 2201435 12538709 := bbase (se 9 (by rfl) ⟨36734, by rfl⟩ : syracuseStep 12538709 = 73469) (by norm_num)
theorem B8359139 : Blo 2201435 8359139 := bstep (se 1 (by rfl) ⟨6269354, by rfl⟩ : syracuseStep 8359139 = 12538709) B12538709
theorem B5572759 : Blo 2201435 5572759 := bstep (se 1 (by rfl) ⟨4179569, by rfl⟩ : syracuseStep 5572759 = 8359139) B8359139
theorem B7430345 : Blo 2201435 7430345 := bstep (se 2 (by rfl) ⟨2786379, by rfl⟩ : syracuseStep 7430345 = 5572759) B5572759
theorem B4953563 : Blo 2201435 4953563 := bstep (se 1 (by rfl) ⟨3715172, by rfl⟩ : syracuseStep 4953563 = 7430345) B7430345
theorem B3302375 : Blo 2201435 3302375 := bstep (se 1 (by rfl) ⟨2476781, by rfl⟩ : syracuseStep 3302375 = 4953563) B4953563
theorem B2201583 : Blo 2201435 2201583 := bstep (se 1 (by rfl) ⟨1651187, by rfl⟩ : syracuseStep 2201583 = 3302375) B3302375
theorem B3302381 : Blo 2201435 3302381 := bbase (se 3 (by rfl) ⟨619196, by rfl⟩ : syracuseStep 3302381 = 1238393) (by norm_num)
theorem B2201587 : Blo 2201435 2201587 := bstep (se 1 (by rfl) ⟨1651190, by rfl⟩ : syracuseStep 2201587 = 3302381) B3302381
theorem B4953581 : Blo 2201435 4953581 := bbase (se 3 (by rfl) ⟨928796, by rfl⟩ : syracuseStep 4953581 = 1857593) (by norm_num)
theorem B3302387 : Blo 2201435 3302387 := bstep (se 1 (by rfl) ⟨2476790, by rfl⟩ : syracuseStep 3302387 = 4953581) B4953581
theorem B2201591 : Blo 2201435 2201591 := bstep (se 1 (by rfl) ⟨1651193, by rfl⟩ : syracuseStep 2201591 = 3302387) B3302387
theorem B4766197 : Blo 2201435 4766197 := bbase (se 5 (by rfl) ⟨223415, by rfl⟩ : syracuseStep 4766197 = 446831) (by norm_num)
theorem B6354929 : Blo 2201435 6354929 := bstep (se 2 (by rfl) ⟨2383098, by rfl⟩ : syracuseStep 6354929 = 4766197) B4766197
theorem B4236619 : Blo 2201435 4236619 := bstep (se 1 (by rfl) ⟨3177464, by rfl⟩ : syracuseStep 4236619 = 6354929) B6354929
theorem B5648825 : Blo 2201435 5648825 := bstep (se 2 (by rfl) ⟨2118309, by rfl⟩ : syracuseStep 5648825 = 4236619) B4236619
theorem B15063533 : Blo 2201435 15063533 := bstep (se 3 (by rfl) ⟨2824412, by rfl⟩ : syracuseStep 15063533 = 5648825) B5648825
theorem B10042355 : Blo 2201435 10042355 := bstep (se 1 (by rfl) ⟨7531766, by rfl⟩ : syracuseStep 10042355 = 15063533) B15063533
theorem B6694903 : Blo 2201435 6694903 := bstep (se 1 (by rfl) ⟨5021177, by rfl⟩ : syracuseStep 6694903 = 10042355) B10042355
theorem B8926537 : Blo 2201435 8926537 := bstep (se 2 (by rfl) ⟨3347451, by rfl⟩ : syracuseStep 8926537 = 6694903) B6694903
theorem B11902049 : Blo 2201435 11902049 := bstep (se 2 (by rfl) ⟨4463268, by rfl⟩ : syracuseStep 11902049 = 8926537) B8926537
theorem B7934699 : Blo 2201435 7934699 := bstep (se 1 (by rfl) ⟨5951024, by rfl⟩ : syracuseStep 7934699 = 11902049) B11902049
theorem B5289799 : Blo 2201435 5289799 := bstep (se 1 (by rfl) ⟨3967349, by rfl⟩ : syracuseStep 5289799 = 7934699) B7934699
theorem B7053065 : Blo 2201435 7053065 := bstep (se 2 (by rfl) ⟨2644899, by rfl⟩ : syracuseStep 7053065 = 5289799) B5289799
theorem B4702043 : Blo 2201435 4702043 := bstep (se 1 (by rfl) ⟨3526532, by rfl⟩ : syracuseStep 4702043 = 7053065) B7053065
theorem B3134695 : Blo 2201435 3134695 := bstep (se 1 (by rfl) ⟨2351021, by rfl⟩ : syracuseStep 3134695 = 4702043) B4702043
theorem B4179593 : Blo 2201435 4179593 := bstep (se 2 (by rfl) ⟨1567347, by rfl⟩ : syracuseStep 4179593 = 3134695) B3134695
theorem B2786395 : Blo 2201435 2786395 := bstep (se 1 (by rfl) ⟨2089796, by rfl⟩ : syracuseStep 2786395 = 4179593) B4179593
theorem B3715193 : Blo 2201435 3715193 := bstep (se 2 (by rfl) ⟨1393197, by rfl⟩ : syracuseStep 3715193 = 2786395) B2786395
theorem B2476795 : Blo 2201435 2476795 := bstep (se 1 (by rfl) ⟨1857596, by rfl⟩ : syracuseStep 2476795 = 3715193) B3715193
theorem B3302393 : Blo 2201435 3302393 := bstep (se 2 (by rfl) ⟨1238397, by rfl⟩ : syracuseStep 3302393 = 2476795) B2476795
theorem B2201595 : Blo 2201435 2201595 := bstep (se 1 (by rfl) ⟨1651196, by rfl⟩ : syracuseStep 2201595 = 3302393) B3302393
theorem B126955349 : Blo 2201435 126955349 := bbase (se 9 (by rfl) ⟨371939, by rfl⟩ : syracuseStep 126955349 = 743879) (by norm_num)
theorem B84636899 : Blo 2201435 84636899 := bstep (se 1 (by rfl) ⟨63477674, by rfl⟩ : syracuseStep 84636899 = 126955349) B126955349
theorem B56424599 : Blo 2201435 56424599 := bstep (se 1 (by rfl) ⟨42318449, by rfl⟩ : syracuseStep 56424599 = 84636899) B84636899
theorem B37616399 : Blo 2201435 37616399 := bstep (se 1 (by rfl) ⟨28212299, by rfl⟩ : syracuseStep 37616399 = 56424599) B56424599
theorem B25077599 : Blo 2201435 25077599 := bstep (se 1 (by rfl) ⟨18808199, by rfl⟩ : syracuseStep 25077599 = 37616399) B37616399
theorem B16718399 : Blo 2201435 16718399 := bstep (se 1 (by rfl) ⟨12538799, by rfl⟩ : syracuseStep 16718399 = 25077599) B25077599
theorem B11145599 : Blo 2201435 11145599 := bstep (se 1 (by rfl) ⟨8359199, by rfl⟩ : syracuseStep 11145599 = 16718399) B16718399
theorem B7430399 : Blo 2201435 7430399 := bstep (se 1 (by rfl) ⟨5572799, by rfl⟩ : syracuseStep 7430399 = 11145599) B11145599
theorem B4953599 : Blo 2201435 4953599 := bstep (se 1 (by rfl) ⟨3715199, by rfl⟩ : syracuseStep 4953599 = 7430399) B7430399
theorem B3302399 : Blo 2201435 3302399 := bstep (se 1 (by rfl) ⟨2476799, by rfl⟩ : syracuseStep 3302399 = 4953599) B4953599
theorem B2201599 : Blo 2201435 2201599 := bstep (se 1 (by rfl) ⟨1651199, by rfl⟩ : syracuseStep 2201599 = 3302399) B3302399
theorem B3302405 : Blo 2201435 3302405 := bbase (se 4 (by rfl) ⟨309600, by rfl⟩ : syracuseStep 3302405 = 619201) (by norm_num)
theorem B2201603 : Blo 2201435 2201603 := bstep (se 1 (by rfl) ⟨1651202, by rfl⟩ : syracuseStep 2201603 = 3302405) B3302405
theorem B3715213 : Blo 2201435 3715213 := bbase (se 3 (by rfl) ⟨696602, by rfl⟩ : syracuseStep 3715213 = 1393205) (by norm_num)
theorem B4953617 : Blo 2201435 4953617 := bstep (se 2 (by rfl) ⟨1857606, by rfl⟩ : syracuseStep 4953617 = 3715213) B3715213
theorem B3302411 : Blo 2201435 3302411 := bstep (se 1 (by rfl) ⟨2476808, by rfl⟩ : syracuseStep 3302411 = 4953617) B4953617
theorem B2201607 : Blo 2201435 2201607 := bstep (se 1 (by rfl) ⟨1651205, by rfl⟩ : syracuseStep 2201607 = 3302411) B3302411
theorem B2476813 : Blo 2201435 2476813 := bbase (se 3 (by rfl) ⟨464402, by rfl⟩ : syracuseStep 2476813 = 928805) (by norm_num)
theorem B3302417 : Blo 2201435 3302417 := bstep (se 2 (by rfl) ⟨1238406, by rfl⟩ : syracuseStep 3302417 = 2476813) B2476813
theorem B2201611 : Blo 2201435 2201611 := bstep (se 1 (by rfl) ⟨1651208, by rfl⟩ : syracuseStep 2201611 = 3302417) B3302417
theorem B7430453 : Blo 2201435 7430453 := bbase (se 5 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 7430453 = 696605) (by norm_num)
theorem B4953635 : Blo 2201435 4953635 := bstep (se 1 (by rfl) ⟨3715226, by rfl⟩ : syracuseStep 4953635 = 7430453) B7430453
theorem B3302423 : Blo 2201435 3302423 := bstep (se 1 (by rfl) ⟨2476817, by rfl⟩ : syracuseStep 3302423 = 4953635) B4953635
theorem B2201615 : Blo 2201435 2201615 := bstep (se 1 (by rfl) ⟨1651211, by rfl⟩ : syracuseStep 2201615 = 3302423) B3302423
theorem B3302429 : Blo 2201435 3302429 := bbase (se 3 (by rfl) ⟨619205, by rfl⟩ : syracuseStep 3302429 = 1238411) (by norm_num)
theorem B2201619 : Blo 2201435 2201619 := bstep (se 1 (by rfl) ⟨1651214, by rfl⟩ : syracuseStep 2201619 = 3302429) B3302429
theorem B4953653 : Blo 2201435 4953653 := bbase (se 5 (by rfl) ⟨232202, by rfl⟩ : syracuseStep 4953653 = 464405) (by norm_num)
theorem B3302435 : Blo 2201435 3302435 := bstep (se 1 (by rfl) ⟨2476826, by rfl⟩ : syracuseStep 3302435 = 4953653) B4953653
theorem B2201623 : Blo 2201435 2201623 := bstep (se 1 (by rfl) ⟨1651217, by rfl⟩ : syracuseStep 2201623 = 3302435) B3302435
theorem B4463333 : Blo 2201435 4463333 := bbase (se 4 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 4463333 = 836875) (by norm_num)
theorem B2975555 : Blo 2201435 2975555 := bstep (se 1 (by rfl) ⟨2231666, by rfl⟩ : syracuseStep 2975555 = 4463333) B4463333
theorem B7934813 : Blo 2201435 7934813 := bstep (se 3 (by rfl) ⟨1487777, by rfl⟩ : syracuseStep 7934813 = 2975555) B2975555
theorem B5289875 : Blo 2201435 5289875 := bstep (se 1 (by rfl) ⟨3967406, by rfl⟩ : syracuseStep 5289875 = 7934813) B7934813
theorem B3526583 : Blo 2201435 3526583 := bstep (se 1 (by rfl) ⟨2644937, by rfl⟩ : syracuseStep 3526583 = 5289875) B5289875
theorem B9404221 : Blo 2201435 9404221 := bstep (se 3 (by rfl) ⟨1763291, by rfl⟩ : syracuseStep 9404221 = 3526583) B3526583
theorem B12538961 : Blo 2201435 12538961 := bstep (se 2 (by rfl) ⟨4702110, by rfl⟩ : syracuseStep 12538961 = 9404221) B9404221
theorem B8359307 : Blo 2201435 8359307 := bstep (se 1 (by rfl) ⟨6269480, by rfl⟩ : syracuseStep 8359307 = 12538961) B12538961
theorem B5572871 : Blo 2201435 5572871 := bstep (se 1 (by rfl) ⟨4179653, by rfl⟩ : syracuseStep 5572871 = 8359307) B8359307
theorem B3715247 : Blo 2201435 3715247 := bstep (se 1 (by rfl) ⟨2786435, by rfl⟩ : syracuseStep 3715247 = 5572871) B5572871
theorem B2476831 : Blo 2201435 2476831 := bstep (se 1 (by rfl) ⟨1857623, by rfl⟩ : syracuseStep 2476831 = 3715247) B3715247
theorem B3302441 : Blo 2201435 3302441 := bstep (se 2 (by rfl) ⟨1238415, by rfl⟩ : syracuseStep 3302441 = 2476831) B2476831
theorem B2201627 : Blo 2201435 2201627 := bstep (se 1 (by rfl) ⟨1651220, by rfl⟩ : syracuseStep 2201627 = 3302441) B3302441
theorem B3526589 : Blo 2201435 3526589 := bbase (se 3 (by rfl) ⟨661235, by rfl⟩ : syracuseStep 3526589 = 1322471) (by norm_num)
theorem B9404237 : Blo 2201435 9404237 := bstep (se 3 (by rfl) ⟨1763294, by rfl⟩ : syracuseStep 9404237 = 3526589) B3526589
theorem B6269491 : Blo 2201435 6269491 := bstep (se 1 (by rfl) ⟨4702118, by rfl⟩ : syracuseStep 6269491 = 9404237) B9404237
theorem B8359321 : Blo 2201435 8359321 := bstep (se 2 (by rfl) ⟨3134745, by rfl⟩ : syracuseStep 8359321 = 6269491) B6269491
theorem B11145761 : Blo 2201435 11145761 := bstep (se 2 (by rfl) ⟨4179660, by rfl⟩ : syracuseStep 11145761 = 8359321) B8359321
theorem B7430507 : Blo 2201435 7430507 := bstep (se 1 (by rfl) ⟨5572880, by rfl⟩ : syracuseStep 7430507 = 11145761) B11145761
theorem B4953671 : Blo 2201435 4953671 := bstep (se 1 (by rfl) ⟨3715253, by rfl⟩ : syracuseStep 4953671 = 7430507) B7430507
theorem B3302447 : Blo 2201435 3302447 := bstep (se 1 (by rfl) ⟨2476835, by rfl⟩ : syracuseStep 3302447 = 4953671) B4953671
theorem B2201631 : Blo 2201435 2201631 := bstep (se 1 (by rfl) ⟨1651223, by rfl⟩ : syracuseStep 2201631 = 3302447) B3302447
theorem B3302453 : Blo 2201435 3302453 := bbase (se 5 (by rfl) ⟨154802, by rfl⟩ : syracuseStep 3302453 = 309605) (by norm_num)
theorem B2201635 : Blo 2201435 2201635 := bstep (se 1 (by rfl) ⟨1651226, by rfl⟩ : syracuseStep 2201635 = 3302453) B3302453
theorem B5572901 : Blo 2201435 5572901 := bbase (se 4 (by rfl) ⟨522459, by rfl⟩ : syracuseStep 5572901 = 1044919) (by norm_num)
theorem B3715267 : Blo 2201435 3715267 := bstep (se 1 (by rfl) ⟨2786450, by rfl⟩ : syracuseStep 3715267 = 5572901) B5572901
theorem B4953689 : Blo 2201435 4953689 := bstep (se 2 (by rfl) ⟨1857633, by rfl⟩ : syracuseStep 4953689 = 3715267) B3715267
theorem B3302459 : Blo 2201435 3302459 := bstep (se 1 (by rfl) ⟨2476844, by rfl⟩ : syracuseStep 3302459 = 4953689) B4953689
theorem B2201639 : Blo 2201435 2201639 := bstep (se 1 (by rfl) ⟨1651229, by rfl⟩ : syracuseStep 2201639 = 3302459) B3302459
theorem B2476849 : Blo 2201435 2476849 := bbase (se 2 (by rfl) ⟨928818, by rfl⟩ : syracuseStep 2476849 = 1857637) (by norm_num)
theorem B3302465 : Blo 2201435 3302465 := bstep (se 2 (by rfl) ⟨1238424, by rfl⟩ : syracuseStep 3302465 = 2476849) B2476849
theorem B2201643 : Blo 2201435 2201643 := bstep (se 1 (by rfl) ⟨1651232, by rfl⟩ : syracuseStep 2201643 = 3302465) B3302465
theorem B7934885 : Blo 2201435 7934885 := bbase (se 4 (by rfl) ⟨743895, by rfl⟩ : syracuseStep 7934885 = 1487791) (by norm_num)
theorem B5289923 : Blo 2201435 5289923 := bstep (se 1 (by rfl) ⟨3967442, by rfl⟩ : syracuseStep 5289923 = 7934885) B7934885
theorem B3526615 : Blo 2201435 3526615 := bstep (se 1 (by rfl) ⟨2644961, by rfl⟩ : syracuseStep 3526615 = 5289923) B5289923
theorem B4702153 : Blo 2201435 4702153 := bstep (se 2 (by rfl) ⟨1763307, by rfl⟩ : syracuseStep 4702153 = 3526615) B3526615
theorem B6269537 : Blo 2201435 6269537 := bstep (se 2 (by rfl) ⟨2351076, by rfl⟩ : syracuseStep 6269537 = 4702153) B4702153
theorem B4179691 : Blo 2201435 4179691 := bstep (se 1 (by rfl) ⟨3134768, by rfl⟩ : syracuseStep 4179691 = 6269537) B6269537
theorem B5572921 : Blo 2201435 5572921 := bstep (se 2 (by rfl) ⟨2089845, by rfl⟩ : syracuseStep 5572921 = 4179691) B4179691
theorem B7430561 : Blo 2201435 7430561 := bstep (se 2 (by rfl) ⟨2786460, by rfl⟩ : syracuseStep 7430561 = 5572921) B5572921
theorem B4953707 : Blo 2201435 4953707 := bstep (se 1 (by rfl) ⟨3715280, by rfl⟩ : syracuseStep 4953707 = 7430561) B7430561
theorem B3302471 : Blo 2201435 3302471 := bstep (se 1 (by rfl) ⟨2476853, by rfl⟩ : syracuseStep 3302471 = 4953707) B4953707
theorem B2201647 : Blo 2201435 2201647 := bstep (se 1 (by rfl) ⟨1651235, by rfl⟩ : syracuseStep 2201647 = 3302471) B3302471
theorem B3302477 : Blo 2201435 3302477 := bbase (se 3 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 3302477 = 1238429) (by norm_num)
theorem B2201651 : Blo 2201435 2201651 := bstep (se 1 (by rfl) ⟨1651238, by rfl⟩ : syracuseStep 2201651 = 3302477) B3302477
theorem B4953725 : Blo 2201435 4953725 := bbase (se 3 (by rfl) ⟨928823, by rfl⟩ : syracuseStep 4953725 = 1857647) (by norm_num)
theorem B3302483 : Blo 2201435 3302483 := bstep (se 1 (by rfl) ⟨2476862, by rfl⟩ : syracuseStep 3302483 = 4953725) B4953725
theorem B2201655 : Blo 2201435 2201655 := bstep (se 1 (by rfl) ⟨1651241, by rfl⟩ : syracuseStep 2201655 = 3302483) B3302483
theorem B3715301 : Blo 2201435 3715301 := bbase (se 4 (by rfl) ⟨348309, by rfl⟩ : syracuseStep 3715301 = 696619) (by norm_num)
theorem B2476867 : Blo 2201435 2476867 := bstep (se 1 (by rfl) ⟨1857650, by rfl⟩ : syracuseStep 2476867 = 3715301) B3715301
theorem B3302489 : Blo 2201435 3302489 := bstep (se 2 (by rfl) ⟨1238433, by rfl⟩ : syracuseStep 3302489 = 2476867) B2476867
theorem B2201659 : Blo 2201435 2201659 := bstep (se 1 (by rfl) ⟨1651244, by rfl⟩ : syracuseStep 2201659 = 3302489) B3302489
theorem B3574757 : Blo 2201435 3574757 := bbase (se 4 (by rfl) ⟨335133, by rfl⟩ : syracuseStep 3574757 = 670267) (by norm_num)
theorem B9532685 : Blo 2201435 9532685 := bstep (se 3 (by rfl) ⟨1787378, by rfl⟩ : syracuseStep 9532685 = 3574757) B3574757
theorem B25420493 : Blo 2201435 25420493 := bstep (se 3 (by rfl) ⟨4766342, by rfl⟩ : syracuseStep 25420493 = 9532685) B9532685
theorem B16946995 : Blo 2201435 16946995 := bstep (se 1 (by rfl) ⟨12710246, by rfl⟩ : syracuseStep 16946995 = 25420493) B25420493
theorem B22595993 : Blo 2201435 22595993 := bstep (se 2 (by rfl) ⟨8473497, by rfl⟩ : syracuseStep 22595993 = 16946995) B16946995
theorem B15063995 : Blo 2201435 15063995 := bstep (se 1 (by rfl) ⟨11297996, by rfl⟩ : syracuseStep 15063995 = 22595993) B22595993
theorem B10042663 : Blo 2201435 10042663 := bstep (se 1 (by rfl) ⟨7531997, by rfl⟩ : syracuseStep 10042663 = 15063995) B15063995
theorem B13390217 : Blo 2201435 13390217 := bstep (se 2 (by rfl) ⟨5021331, by rfl⟩ : syracuseStep 13390217 = 10042663) B10042663
theorem B8926811 : Blo 2201435 8926811 := bstep (se 1 (by rfl) ⟨6695108, by rfl⟩ : syracuseStep 8926811 = 13390217) B13390217
theorem B5951207 : Blo 2201435 5951207 := bstep (se 1 (by rfl) ⟨4463405, by rfl⟩ : syracuseStep 5951207 = 8926811) B8926811
theorem B3967471 : Blo 2201435 3967471 := bstep (se 1 (by rfl) ⟨2975603, by rfl⟩ : syracuseStep 3967471 = 5951207) B5951207
theorem B5289961 : Blo 2201435 5289961 := bstep (se 2 (by rfl) ⟨1983735, by rfl⟩ : syracuseStep 5289961 = 3967471) B3967471
theorem B7053281 : Blo 2201435 7053281 := bstep (se 2 (by rfl) ⟨2644980, by rfl⟩ : syracuseStep 7053281 = 5289961) B5289961
theorem B4702187 : Blo 2201435 4702187 := bstep (se 1 (by rfl) ⟨3526640, by rfl⟩ : syracuseStep 4702187 = 7053281) B7053281
theorem B3134791 : Blo 2201435 3134791 := bstep (se 1 (by rfl) ⟨2351093, by rfl⟩ : syracuseStep 3134791 = 4702187) B4702187
theorem B16718885 : Blo 2201435 16718885 := bstep (se 4 (by rfl) ⟨1567395, by rfl⟩ : syracuseStep 16718885 = 3134791) B3134791
theorem B11145923 : Blo 2201435 11145923 := bstep (se 1 (by rfl) ⟨8359442, by rfl⟩ : syracuseStep 11145923 = 16718885) B16718885
theorem B7430615 : Blo 2201435 7430615 := bstep (se 1 (by rfl) ⟨5572961, by rfl⟩ : syracuseStep 7430615 = 11145923) B11145923
theorem B4953743 : Blo 2201435 4953743 := bstep (se 1 (by rfl) ⟨3715307, by rfl⟩ : syracuseStep 4953743 = 7430615) B7430615
theorem B3302495 : Blo 2201435 3302495 := bstep (se 1 (by rfl) ⟨2476871, by rfl⟩ : syracuseStep 3302495 = 4953743) B4953743
theorem B2201663 : Blo 2201435 2201663 := bstep (se 1 (by rfl) ⟨1651247, by rfl⟩ : syracuseStep 2201663 = 3302495) B3302495
theorem B3302501 : Blo 2201435 3302501 := bbase (se 4 (by rfl) ⟨309609, by rfl⟩ : syracuseStep 3302501 = 619219) (by norm_num)
theorem B2201667 : Blo 2201435 2201667 := bstep (se 1 (by rfl) ⟨1651250, by rfl⟩ : syracuseStep 2201667 = 3302501) B3302501
theorem B4702205 : Blo 2201435 4702205 := bbase (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) (by norm_num)
theorem B3134803 : Blo 2201435 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B4179737 : Blo 2201435 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B2786491 : Blo 2201435 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B3715321 : Blo 2201435 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B4953761 : Blo 2201435 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B3302507 : Blo 2201435 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B2201671 : Blo 2201435 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B2476885 : Blo 2201435 2476885 := bbase (se 9 (by rfl) ⟨7256, by rfl⟩ : syracuseStep 2476885 = 14513) (by norm_num)
theorem B3302513 : Blo 2201435 3302513 := bstep (se 2 (by rfl) ⟨1238442, by rfl⟩ : syracuseStep 3302513 = 2476885) B2476885
theorem B2201675 : Blo 2201435 2201675 := bstep (se 1 (by rfl) ⟨1651256, by rfl⟩ : syracuseStep 2201675 = 3302513) B3302513
theorem B2786501 : Blo 2201435 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B7430669 : Blo 2201435 7430669 := bstep (se 3 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 7430669 = 2786501) B2786501
theorem B4953779 : Blo 2201435 4953779 := bstep (se 1 (by rfl) ⟨3715334, by rfl⟩ : syracuseStep 4953779 = 7430669) B7430669
theorem B3302519 : Blo 2201435 3302519 := bstep (se 1 (by rfl) ⟨2476889, by rfl⟩ : syracuseStep 3302519 = 4953779) B4953779
theorem B2201679 : Blo 2201435 2201679 := bstep (se 1 (by rfl) ⟨1651259, by rfl⟩ : syracuseStep 2201679 = 3302519) B3302519
theorem B3302525 : Blo 2201435 3302525 := bbase (se 3 (by rfl) ⟨619223, by rfl⟩ : syracuseStep 3302525 = 1238447) (by norm_num)
theorem B2201683 : Blo 2201435 2201683 := bstep (se 1 (by rfl) ⟨1651262, by rfl⟩ : syracuseStep 2201683 = 3302525) B3302525
theorem B4953797 : Blo 2201435 4953797 := bbase (se 4 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 4953797 = 928837) (by norm_num)
theorem B3302531 : Blo 2201435 3302531 := bstep (se 1 (by rfl) ⟨2476898, by rfl⟩ : syracuseStep 3302531 = 4953797) B4953797
theorem B2201687 : Blo 2201435 2201687 := bstep (se 1 (by rfl) ⟨1651265, by rfl⟩ : syracuseStep 2201687 = 3302531) B3302531
theorem B3347597 : Blo 2201435 3347597 := bbase (se 3 (by rfl) ⟨627674, by rfl⟩ : syracuseStep 3347597 = 1255349) (by norm_num)
theorem B2231731 : Blo 2201435 2231731 := bstep (se 1 (by rfl) ⟨1673798, by rfl⟩ : syracuseStep 2231731 = 3347597) B3347597
theorem B11902565 : Blo 2201435 11902565 := bstep (se 4 (by rfl) ⟨1115865, by rfl⟩ : syracuseStep 11902565 = 2231731) B2231731
theorem B31740173 : Blo 2201435 31740173 := bstep (se 3 (by rfl) ⟨5951282, by rfl⟩ : syracuseStep 31740173 = 11902565) B11902565
theorem B21160115 : Blo 2201435 21160115 := bstep (se 1 (by rfl) ⟨15870086, by rfl⟩ : syracuseStep 21160115 = 31740173) B31740173
theorem B14106743 : Blo 2201435 14106743 := bstep (se 1 (by rfl) ⟨10580057, by rfl⟩ : syracuseStep 14106743 = 21160115) B21160115
theorem B9404495 : Blo 2201435 9404495 := bstep (se 1 (by rfl) ⟨7053371, by rfl⟩ : syracuseStep 9404495 = 14106743) B14106743
theorem B6269663 : Blo 2201435 6269663 := bstep (se 1 (by rfl) ⟨4702247, by rfl⟩ : syracuseStep 6269663 = 9404495) B9404495
theorem B4179775 : Blo 2201435 4179775 := bstep (se 1 (by rfl) ⟨3134831, by rfl⟩ : syracuseStep 4179775 = 6269663) B6269663
theorem B5573033 : Blo 2201435 5573033 := bstep (se 2 (by rfl) ⟨2089887, by rfl⟩ : syracuseStep 5573033 = 4179775) B4179775
theorem B3715355 : Blo 2201435 3715355 := bstep (se 1 (by rfl) ⟨2786516, by rfl⟩ : syracuseStep 3715355 = 5573033) B5573033
theorem B2476903 : Blo 2201435 2476903 := bstep (se 1 (by rfl) ⟨1857677, by rfl⟩ : syracuseStep 2476903 = 3715355) B3715355
theorem B3302537 : Blo 2201435 3302537 := bstep (se 2 (by rfl) ⟨1238451, by rfl⟩ : syracuseStep 3302537 = 2476903) B2476903
theorem B2201691 : Blo 2201435 2201691 := bstep (se 1 (by rfl) ⟨1651268, by rfl⟩ : syracuseStep 2201691 = 3302537) B3302537
theorem B11146085 : Blo 2201435 11146085 := bbase (se 4 (by rfl) ⟨1044945, by rfl⟩ : syracuseStep 11146085 = 2089891) (by norm_num)
theorem B7430723 : Blo 2201435 7430723 := bstep (se 1 (by rfl) ⟨5573042, by rfl⟩ : syracuseStep 7430723 = 11146085) B11146085
theorem B4953815 : Blo 2201435 4953815 := bstep (se 1 (by rfl) ⟨3715361, by rfl⟩ : syracuseStep 4953815 = 7430723) B7430723
theorem B3302543 : Blo 2201435 3302543 := bstep (se 1 (by rfl) ⟨2476907, by rfl⟩ : syracuseStep 3302543 = 4953815) B4953815
theorem B2201695 : Blo 2201435 2201695 := bstep (se 1 (by rfl) ⟨1651271, by rfl⟩ : syracuseStep 2201695 = 3302543) B3302543
theorem B3302549 : Blo 2201435 3302549 := bbase (se 6 (by rfl) ⟨77403, by rfl⟩ : syracuseStep 3302549 = 154807) (by norm_num)
theorem B2201699 : Blo 2201435 2201699 := bstep (se 1 (by rfl) ⟨1651274, by rfl⟩ : syracuseStep 2201699 = 3302549) B3302549
theorem B5159381 : Blo 2201435 5159381 := bbase (se 7 (by rfl) ⟨60461, by rfl⟩ : syracuseStep 5159381 = 120923) (by norm_num)
theorem B13758349 : Blo 2201435 13758349 := bstep (se 3 (by rfl) ⟨2579690, by rfl⟩ : syracuseStep 13758349 = 5159381) B5159381
theorem B18344465 : Blo 2201435 18344465 := bstep (se 2 (by rfl) ⟨6879174, by rfl⟩ : syracuseStep 18344465 = 13758349) B13758349
theorem B12229643 : Blo 2201435 12229643 := bstep (se 1 (by rfl) ⟨9172232, by rfl⟩ : syracuseStep 12229643 = 18344465) B18344465
theorem B8153095 : Blo 2201435 8153095 := bstep (se 1 (by rfl) ⟨6114821, by rfl⟩ : syracuseStep 8153095 = 12229643) B12229643
theorem B10870793 : Blo 2201435 10870793 := bstep (se 2 (by rfl) ⟨4076547, by rfl⟩ : syracuseStep 10870793 = 8153095) B8153095
theorem B7247195 : Blo 2201435 7247195 := bstep (se 1 (by rfl) ⟨5435396, by rfl⟩ : syracuseStep 7247195 = 10870793) B10870793
theorem B4831463 : Blo 2201435 4831463 := bstep (se 1 (by rfl) ⟨3623597, by rfl⟩ : syracuseStep 4831463 = 7247195) B7247195
theorem B3220975 : Blo 2201435 3220975 := bstep (se 1 (by rfl) ⟨2415731, by rfl⟩ : syracuseStep 3220975 = 4831463) B4831463
theorem B4294633 : Blo 2201435 4294633 := bstep (se 2 (by rfl) ⟨1610487, by rfl⟩ : syracuseStep 4294633 = 3220975) B3220975
theorem B5726177 : Blo 2201435 5726177 := bstep (se 2 (by rfl) ⟨2147316, by rfl⟩ : syracuseStep 5726177 = 4294633) B4294633
theorem B3817451 : Blo 2201435 3817451 := bstep (se 1 (by rfl) ⟨2863088, by rfl⟩ : syracuseStep 3817451 = 5726177) B5726177
theorem B2544967 : Blo 2201435 2544967 := bstep (se 1 (by rfl) ⟨1908725, by rfl⟩ : syracuseStep 2544967 = 3817451) B3817451
theorem B3393289 : Blo 2201435 3393289 := bstep (se 2 (by rfl) ⟨1272483, by rfl⟩ : syracuseStep 3393289 = 2544967) B2544967
theorem B4524385 : Blo 2201435 4524385 := bstep (se 2 (by rfl) ⟨1696644, by rfl⟩ : syracuseStep 4524385 = 3393289) B3393289
theorem B6032513 : Blo 2201435 6032513 := bstep (se 2 (by rfl) ⟨2262192, by rfl⟩ : syracuseStep 6032513 = 4524385) B4524385
theorem B16086701 : Blo 2201435 16086701 := bstep (se 3 (by rfl) ⟨3016256, by rfl⟩ : syracuseStep 16086701 = 6032513) B6032513
theorem B42897869 : Blo 2201435 42897869 := bstep (se 3 (by rfl) ⟨8043350, by rfl⟩ : syracuseStep 42897869 = 16086701) B16086701
theorem B28598579 : Blo 2201435 28598579 := bstep (se 1 (by rfl) ⟨21448934, by rfl⟩ : syracuseStep 28598579 = 42897869) B42897869
theorem B19065719 : Blo 2201435 19065719 := bstep (se 1 (by rfl) ⟨14299289, by rfl⟩ : syracuseStep 19065719 = 28598579) B28598579
theorem B12710479 : Blo 2201435 12710479 := bstep (se 1 (by rfl) ⟨9532859, by rfl⟩ : syracuseStep 12710479 = 19065719) B19065719
theorem B16947305 : Blo 2201435 16947305 := bstep (se 2 (by rfl) ⟨6355239, by rfl⟩ : syracuseStep 16947305 = 12710479) B12710479
theorem B11298203 : Blo 2201435 11298203 := bstep (se 1 (by rfl) ⟨8473652, by rfl⟩ : syracuseStep 11298203 = 16947305) B16947305
theorem B7532135 : Blo 2201435 7532135 := bstep (se 1 (by rfl) ⟨5649101, by rfl⟩ : syracuseStep 7532135 = 11298203) B11298203
theorem B5021423 : Blo 2201435 5021423 := bstep (se 1 (by rfl) ⟨3766067, by rfl⟩ : syracuseStep 5021423 = 7532135) B7532135
theorem B3347615 : Blo 2201435 3347615 := bstep (se 1 (by rfl) ⟨2510711, by rfl⟩ : syracuseStep 3347615 = 5021423) B5021423
theorem B8926973 : Blo 2201435 8926973 := bstep (se 3 (by rfl) ⟨1673807, by rfl⟩ : syracuseStep 8926973 = 3347615) B3347615
theorem B5951315 : Blo 2201435 5951315 := bstep (se 1 (by rfl) ⟨4463486, by rfl⟩ : syracuseStep 5951315 = 8926973) B8926973
theorem B3967543 : Blo 2201435 3967543 := bstep (se 1 (by rfl) ⟨2975657, by rfl⟩ : syracuseStep 3967543 = 5951315) B5951315
theorem B5290057 : Blo 2201435 5290057 := bstep (se 2 (by rfl) ⟨1983771, by rfl⟩ : syracuseStep 5290057 = 3967543) B3967543
theorem B7053409 : Blo 2201435 7053409 := bstep (se 2 (by rfl) ⟨2645028, by rfl⟩ : syracuseStep 7053409 = 5290057) B5290057
theorem B9404545 : Blo 2201435 9404545 := bstep (se 2 (by rfl) ⟨3526704, by rfl⟩ : syracuseStep 9404545 = 7053409) B7053409
theorem B12539393 : Blo 2201435 12539393 := bstep (se 2 (by rfl) ⟨4702272, by rfl⟩ : syracuseStep 12539393 = 9404545) B9404545
theorem B8359595 : Blo 2201435 8359595 := bstep (se 1 (by rfl) ⟨6269696, by rfl⟩ : syracuseStep 8359595 = 12539393) B12539393
theorem B5573063 : Blo 2201435 5573063 := bstep (se 1 (by rfl) ⟨4179797, by rfl⟩ : syracuseStep 5573063 = 8359595) B8359595
theorem B3715375 : Blo 2201435 3715375 := bstep (se 1 (by rfl) ⟨2786531, by rfl⟩ : syracuseStep 3715375 = 5573063) B5573063
theorem B4953833 : Blo 2201435 4953833 := bstep (se 2 (by rfl) ⟨1857687, by rfl⟩ : syracuseStep 4953833 = 3715375) B3715375
theorem B3302555 : Blo 2201435 3302555 := bstep (se 1 (by rfl) ⟨2476916, by rfl⟩ : syracuseStep 3302555 = 4953833) B4953833
theorem B2201703 : Blo 2201435 2201703 := bstep (se 1 (by rfl) ⟨1651277, by rfl⟩ : syracuseStep 2201703 = 3302555) B3302555
theorem B2476921 : Blo 2201435 2476921 := bbase (se 2 (by rfl) ⟨928845, by rfl⟩ : syracuseStep 2476921 = 1857691) (by norm_num)
theorem B3302561 : Blo 2201435 3302561 := bstep (se 2 (by rfl) ⟨1238460, by rfl⟩ : syracuseStep 3302561 = 2476921) B2476921
theorem B2201707 : Blo 2201435 2201707 := bstep (se 1 (by rfl) ⟨1651280, by rfl⟩ : syracuseStep 2201707 = 3302561) B3302561
theorem B14106869 : Blo 2201435 14106869 := bbase (se 5 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 14106869 = 1322519) (by norm_num)
theorem B9404579 : Blo 2201435 9404579 := bstep (se 1 (by rfl) ⟨7053434, by rfl⟩ : syracuseStep 9404579 = 14106869) B14106869
theorem B6269719 : Blo 2201435 6269719 := bstep (se 1 (by rfl) ⟨4702289, by rfl⟩ : syracuseStep 6269719 = 9404579) B9404579
theorem B8359625 : Blo 2201435 8359625 := bstep (se 2 (by rfl) ⟨3134859, by rfl⟩ : syracuseStep 8359625 = 6269719) B6269719
theorem B5573083 : Blo 2201435 5573083 := bstep (se 1 (by rfl) ⟨4179812, by rfl⟩ : syracuseStep 5573083 = 8359625) B8359625
theorem B7430777 : Blo 2201435 7430777 := bstep (se 2 (by rfl) ⟨2786541, by rfl⟩ : syracuseStep 7430777 = 5573083) B5573083
theorem B4953851 : Blo 2201435 4953851 := bstep (se 1 (by rfl) ⟨3715388, by rfl⟩ : syracuseStep 4953851 = 7430777) B7430777
theorem B3302567 : Blo 2201435 3302567 := bstep (se 1 (by rfl) ⟨2476925, by rfl⟩ : syracuseStep 3302567 = 4953851) B4953851
theorem B2201711 : Blo 2201435 2201711 := bstep (se 1 (by rfl) ⟨1651283, by rfl⟩ : syracuseStep 2201711 = 3302567) B3302567
theorem B3302573 : Blo 2201435 3302573 := bbase (se 3 (by rfl) ⟨619232, by rfl⟩ : syracuseStep 3302573 = 1238465) (by norm_num)
theorem B2201715 : Blo 2201435 2201715 := bstep (se 1 (by rfl) ⟨1651286, by rfl⟩ : syracuseStep 2201715 = 3302573) B3302573
theorem B4953869 : Blo 2201435 4953869 := bbase (se 3 (by rfl) ⟨928850, by rfl⟩ : syracuseStep 4953869 = 1857701) (by norm_num)
theorem B3302579 : Blo 2201435 3302579 := bstep (se 1 (by rfl) ⟨2476934, by rfl⟩ : syracuseStep 3302579 = 4953869) B4953869
theorem B2201719 : Blo 2201435 2201719 := bstep (se 1 (by rfl) ⟨1651289, by rfl⟩ : syracuseStep 2201719 = 3302579) B3302579
theorem B2786557 : Blo 2201435 2786557 := bbase (se 3 (by rfl) ⟨522479, by rfl⟩ : syracuseStep 2786557 = 1044959) (by norm_num)
theorem B3715409 : Blo 2201435 3715409 := bstep (se 2 (by rfl) ⟨1393278, by rfl⟩ : syracuseStep 3715409 = 2786557) B2786557
theorem B2476939 : Blo 2201435 2476939 := bstep (se 1 (by rfl) ⟨1857704, by rfl⟩ : syracuseStep 2476939 = 3715409) B3715409
theorem B3302585 : Blo 2201435 3302585 := bstep (se 2 (by rfl) ⟨1238469, by rfl⟩ : syracuseStep 3302585 = 2476939) B2476939
theorem B2201723 : Blo 2201435 2201723 := bstep (se 1 (by rfl) ⟨1651292, by rfl⟩ : syracuseStep 2201723 = 3302585) B3302585
theorem B2645057 : Blo 2201435 2645057 := bbase (se 2 (by rfl) ⟨991896, by rfl⟩ : syracuseStep 2645057 = 1983793) (by norm_num)
theorem B7053485 : Blo 2201435 7053485 := bstep (se 3 (by rfl) ⟨1322528, by rfl⟩ : syracuseStep 7053485 = 2645057) B2645057
theorem B18809293 : Blo 2201435 18809293 := bstep (se 3 (by rfl) ⟨3526742, by rfl⟩ : syracuseStep 18809293 = 7053485) B7053485
theorem B25079057 : Blo 2201435 25079057 := bstep (se 2 (by rfl) ⟨9404646, by rfl⟩ : syracuseStep 25079057 = 18809293) B18809293
theorem B16719371 : Blo 2201435 16719371 := bstep (se 1 (by rfl) ⟨12539528, by rfl⟩ : syracuseStep 16719371 = 25079057) B25079057
theorem B11146247 : Blo 2201435 11146247 := bstep (se 1 (by rfl) ⟨8359685, by rfl⟩ : syracuseStep 11146247 = 16719371) B16719371
theorem B7430831 : Blo 2201435 7430831 := bstep (se 1 (by rfl) ⟨5573123, by rfl⟩ : syracuseStep 7430831 = 11146247) B11146247
theorem B4953887 : Blo 2201435 4953887 := bstep (se 1 (by rfl) ⟨3715415, by rfl⟩ : syracuseStep 4953887 = 7430831) B7430831
theorem B3302591 : Blo 2201435 3302591 := bstep (se 1 (by rfl) ⟨2476943, by rfl⟩ : syracuseStep 3302591 = 4953887) B4953887
theorem B2201727 : Blo 2201435 2201727 := bstep (se 1 (by rfl) ⟨1651295, by rfl⟩ : syracuseStep 2201727 = 3302591) B3302591
theorem B3302597 : Blo 2201435 3302597 := bbase (se 4 (by rfl) ⟨309618, by rfl⟩ : syracuseStep 3302597 = 619237) (by norm_num)
theorem B2201731 : Blo 2201435 2201731 := bstep (se 1 (by rfl) ⟨1651298, by rfl⟩ : syracuseStep 2201731 = 3302597) B3302597
theorem B3715429 : Blo 2201435 3715429 := bbase (se 4 (by rfl) ⟨348321, by rfl⟩ : syracuseStep 3715429 = 696643) (by norm_num)
theorem B4953905 : Blo 2201435 4953905 := bstep (se 2 (by rfl) ⟨1857714, by rfl⟩ : syracuseStep 4953905 = 3715429) B3715429
theorem B3302603 : Blo 2201435 3302603 := bstep (se 1 (by rfl) ⟨2476952, by rfl⟩ : syracuseStep 3302603 = 4953905) B4953905
theorem B2201735 : Blo 2201435 2201735 := bstep (se 1 (by rfl) ⟨1651301, by rfl⟩ : syracuseStep 2201735 = 3302603) B3302603
theorem B2476957 : Blo 2201435 2476957 := bbase (se 3 (by rfl) ⟨464429, by rfl⟩ : syracuseStep 2476957 = 928859) (by norm_num)
theorem B3302609 : Blo 2201435 3302609 := bstep (se 2 (by rfl) ⟨1238478, by rfl⟩ : syracuseStep 3302609 = 2476957) B2476957
theorem B2201739 : Blo 2201435 2201739 := bstep (se 1 (by rfl) ⟨1651304, by rfl⟩ : syracuseStep 2201739 = 3302609) B3302609
theorem B7430885 : Blo 2201435 7430885 := bbase (se 4 (by rfl) ⟨696645, by rfl⟩ : syracuseStep 7430885 = 1393291) (by norm_num)
theorem B4953923 : Blo 2201435 4953923 := bstep (se 1 (by rfl) ⟨3715442, by rfl⟩ : syracuseStep 4953923 = 7430885) B7430885
theorem B3302615 : Blo 2201435 3302615 := bstep (se 1 (by rfl) ⟨2476961, by rfl⟩ : syracuseStep 3302615 = 4953923) B4953923
theorem B2201743 : Blo 2201435 2201743 := bstep (se 1 (by rfl) ⟨1651307, by rfl⟩ : syracuseStep 2201743 = 3302615) B3302615
theorem B3302621 : Blo 2201435 3302621 := bbase (se 3 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 3302621 = 1238483) (by norm_num)
theorem B2201747 : Blo 2201435 2201747 := bstep (se 1 (by rfl) ⟨1651310, by rfl⟩ : syracuseStep 2201747 = 3302621) B3302621
theorem B4953941 : Blo 2201435 4953941 := bbase (se 9 (by rfl) ⟨14513, by rfl⟩ : syracuseStep 4953941 = 29027) (by norm_num)
theorem B3302627 : Blo 2201435 3302627 := bstep (se 1 (by rfl) ⟨2476970, by rfl⟩ : syracuseStep 3302627 = 4953941) B4953941
theorem B2201751 : Blo 2201435 2201751 := bstep (se 1 (by rfl) ⟨1651313, by rfl⟩ : syracuseStep 2201751 = 3302627) B3302627
theorem B6269845 : Blo 2201435 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B8359793 : Blo 2201435 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B5573195 : Blo 2201435 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B3715463 : Blo 2201435 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B2476975 : Blo 2201435 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B3302633 : Blo 2201435 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B2201755 : Blo 2201435 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B5021549 : Blo 2201435 5021549 := bbase (se 3 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 5021549 = 1883081) (by norm_num)
theorem B3347699 : Blo 2201435 3347699 := bstep (se 1 (by rfl) ⟨2510774, by rfl⟩ : syracuseStep 3347699 = 5021549) B5021549
theorem B35708789 : Blo 2201435 35708789 := bstep (se 5 (by rfl) ⟨1673849, by rfl⟩ : syracuseStep 35708789 = 3347699) B3347699
theorem B95223437 : Blo 2201435 95223437 := bstep (se 3 (by rfl) ⟨17854394, by rfl⟩ : syracuseStep 95223437 = 35708789) B35708789
theorem B63482291 : Blo 2201435 63482291 := bstep (se 1 (by rfl) ⟨47611718, by rfl⟩ : syracuseStep 63482291 = 95223437) B95223437
theorem B42321527 : Blo 2201435 42321527 := bstep (se 1 (by rfl) ⟨31741145, by rfl⟩ : syracuseStep 42321527 = 63482291) B63482291
theorem B28214351 : Blo 2201435 28214351 := bstep (se 1 (by rfl) ⟨21160763, by rfl⟩ : syracuseStep 28214351 = 42321527) B42321527
theorem B18809567 : Blo 2201435 18809567 := bstep (se 1 (by rfl) ⟨14107175, by rfl⟩ : syracuseStep 18809567 = 28214351) B28214351
theorem B12539711 : Blo 2201435 12539711 := bstep (se 1 (by rfl) ⟨9404783, by rfl⟩ : syracuseStep 12539711 = 18809567) B18809567
theorem B8359807 : Blo 2201435 8359807 := bstep (se 1 (by rfl) ⟨6269855, by rfl⟩ : syracuseStep 8359807 = 12539711) B12539711
theorem B11146409 : Blo 2201435 11146409 := bstep (se 2 (by rfl) ⟨4179903, by rfl⟩ : syracuseStep 11146409 = 8359807) B8359807
theorem B7430939 : Blo 2201435 7430939 := bstep (se 1 (by rfl) ⟨5573204, by rfl⟩ : syracuseStep 7430939 = 11146409) B11146409
theorem B4953959 : Blo 2201435 4953959 := bstep (se 1 (by rfl) ⟨3715469, by rfl⟩ : syracuseStep 4953959 = 7430939) B7430939
theorem B3302639 : Blo 2201435 3302639 := bstep (se 1 (by rfl) ⟨2476979, by rfl⟩ : syracuseStep 3302639 = 4953959) B4953959
theorem B2201759 : Blo 2201435 2201759 := bstep (se 1 (by rfl) ⟨1651319, by rfl⟩ : syracuseStep 2201759 = 3302639) B3302639
theorem B3302645 : Blo 2201435 3302645 := bbase (se 5 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 3302645 = 309623) (by norm_num)
theorem B2201763 : Blo 2201435 2201763 := bstep (se 1 (by rfl) ⟨1651322, by rfl⟩ : syracuseStep 2201763 = 3302645) B3302645
theorem B7935317 : Blo 2201435 7935317 := bbase (se 14 (by rfl) ⟨726, by rfl⟩ : syracuseStep 7935317 = 1453) (by norm_num)
theorem B5290211 : Blo 2201435 5290211 := bstep (se 1 (by rfl) ⟨3967658, by rfl⟩ : syracuseStep 5290211 = 7935317) B7935317
theorem B14107229 : Blo 2201435 14107229 := bstep (se 3 (by rfl) ⟨2645105, by rfl⟩ : syracuseStep 14107229 = 5290211) B5290211
theorem B9404819 : Blo 2201435 9404819 := bstep (se 1 (by rfl) ⟨7053614, by rfl⟩ : syracuseStep 9404819 = 14107229) B14107229
theorem B6269879 : Blo 2201435 6269879 := bstep (se 1 (by rfl) ⟨4702409, by rfl⟩ : syracuseStep 6269879 = 9404819) B9404819
theorem B4179919 : Blo 2201435 4179919 := bstep (se 1 (by rfl) ⟨3134939, by rfl⟩ : syracuseStep 4179919 = 6269879) B6269879
theorem B5573225 : Blo 2201435 5573225 := bstep (se 2 (by rfl) ⟨2089959, by rfl⟩ : syracuseStep 5573225 = 4179919) B4179919
theorem B3715483 : Blo 2201435 3715483 := bstep (se 1 (by rfl) ⟨2786612, by rfl⟩ : syracuseStep 3715483 = 5573225) B5573225
theorem B4953977 : Blo 2201435 4953977 := bstep (se 2 (by rfl) ⟨1857741, by rfl⟩ : syracuseStep 4953977 = 3715483) B3715483
theorem B3302651 : Blo 2201435 3302651 := bstep (se 1 (by rfl) ⟨2476988, by rfl⟩ : syracuseStep 3302651 = 4953977) B4953977
theorem B2201767 : Blo 2201435 2201767 := bstep (se 1 (by rfl) ⟨1651325, by rfl⟩ : syracuseStep 2201767 = 3302651) B3302651
theorem B2476993 : Blo 2201435 2476993 := bbase (se 2 (by rfl) ⟨928872, by rfl⟩ : syracuseStep 2476993 = 1857745) (by norm_num)
theorem B3302657 : Blo 2201435 3302657 := bstep (se 2 (by rfl) ⟨1238496, by rfl⟩ : syracuseStep 3302657 = 2476993) B2476993
theorem B2201771 : Blo 2201435 2201771 := bstep (se 1 (by rfl) ⟨1651328, by rfl⟩ : syracuseStep 2201771 = 3302657) B3302657
theorem B5573245 : Blo 2201435 5573245 := bbase (se 3 (by rfl) ⟨1044983, by rfl⟩ : syracuseStep 5573245 = 2089967) (by norm_num)
theorem B7430993 : Blo 2201435 7430993 := bstep (se 2 (by rfl) ⟨2786622, by rfl⟩ : syracuseStep 7430993 = 5573245) B5573245
theorem B4953995 : Blo 2201435 4953995 := bstep (se 1 (by rfl) ⟨3715496, by rfl⟩ : syracuseStep 4953995 = 7430993) B7430993
theorem B3302663 : Blo 2201435 3302663 := bstep (se 1 (by rfl) ⟨2476997, by rfl⟩ : syracuseStep 3302663 = 4953995) B4953995
theorem B2201775 : Blo 2201435 2201775 := bstep (se 1 (by rfl) ⟨1651331, by rfl⟩ : syracuseStep 2201775 = 3302663) B3302663
theorem B3302669 : Blo 2201435 3302669 := bbase (se 3 (by rfl) ⟨619250, by rfl⟩ : syracuseStep 3302669 = 1238501) (by norm_num)
theorem B2201779 : Blo 2201435 2201779 := bstep (se 1 (by rfl) ⟨1651334, by rfl⟩ : syracuseStep 2201779 = 3302669) B3302669
theorem B4954013 : Blo 2201435 4954013 := bbase (se 3 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 4954013 = 1857755) (by norm_num)
theorem B3302675 : Blo 2201435 3302675 := bstep (se 1 (by rfl) ⟨2477006, by rfl⟩ : syracuseStep 3302675 = 4954013) B4954013
theorem B2201783 : Blo 2201435 2201783 := bstep (se 1 (by rfl) ⟨1651337, by rfl⟩ : syracuseStep 2201783 = 3302675) B3302675
theorem B3715517 : Blo 2201435 3715517 := bbase (se 3 (by rfl) ⟨696659, by rfl⟩ : syracuseStep 3715517 = 1393319) (by norm_num)
theorem B2477011 : Blo 2201435 2477011 := bstep (se 1 (by rfl) ⟨1857758, by rfl⟩ : syracuseStep 2477011 = 3715517) B3715517
theorem B3302681 : Blo 2201435 3302681 := bstep (se 2 (by rfl) ⟨1238505, by rfl⟩ : syracuseStep 3302681 = 2477011) B2477011
theorem B2201787 : Blo 2201435 2201787 := bstep (se 1 (by rfl) ⟨1651340, by rfl⟩ : syracuseStep 2201787 = 3302681) B3302681
theorem B12539893 : Blo 2201435 12539893 := bbase (se 5 (by rfl) ⟨587807, by rfl⟩ : syracuseStep 12539893 = 1175615) (by norm_num)
theorem B16719857 : Blo 2201435 16719857 := bstep (se 2 (by rfl) ⟨6269946, by rfl⟩ : syracuseStep 16719857 = 12539893) B12539893
theorem B11146571 : Blo 2201435 11146571 := bstep (se 1 (by rfl) ⟨8359928, by rfl⟩ : syracuseStep 11146571 = 16719857) B16719857
theorem B7431047 : Blo 2201435 7431047 := bstep (se 1 (by rfl) ⟨5573285, by rfl⟩ : syracuseStep 7431047 = 11146571) B11146571
theorem B4954031 : Blo 2201435 4954031 := bstep (se 1 (by rfl) ⟨3715523, by rfl⟩ : syracuseStep 4954031 = 7431047) B7431047
theorem B3302687 : Blo 2201435 3302687 := bstep (se 1 (by rfl) ⟨2477015, by rfl⟩ : syracuseStep 3302687 = 4954031) B4954031
theorem B2201791 : Blo 2201435 2201791 := bstep (se 1 (by rfl) ⟨1651343, by rfl⟩ : syracuseStep 2201791 = 3302687) B3302687
theorem B3302693 : Blo 2201435 3302693 := bbase (se 4 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 3302693 = 619255) (by norm_num)
theorem B2201795 : Blo 2201435 2201795 := bstep (se 1 (by rfl) ⟨1651346, by rfl⟩ : syracuseStep 2201795 = 3302693) B3302693
theorem B2786653 : Blo 2201435 2786653 := bbase (se 3 (by rfl) ⟨522497, by rfl⟩ : syracuseStep 2786653 = 1044995) (by norm_num)
theorem B3715537 : Blo 2201435 3715537 := bstep (se 2 (by rfl) ⟨1393326, by rfl⟩ : syracuseStep 3715537 = 2786653) B2786653
theorem B4954049 : Blo 2201435 4954049 := bstep (se 2 (by rfl) ⟨1857768, by rfl⟩ : syracuseStep 4954049 = 3715537) B3715537
theorem B3302699 : Blo 2201435 3302699 := bstep (se 1 (by rfl) ⟨2477024, by rfl⟩ : syracuseStep 3302699 = 4954049) B4954049
theorem B2201799 : Blo 2201435 2201799 := bstep (se 1 (by rfl) ⟨1651349, by rfl⟩ : syracuseStep 2201799 = 3302699) B3302699
theorem B2477029 : Blo 2201435 2477029 := bbase (se 4 (by rfl) ⟨232221, by rfl⟩ : syracuseStep 2477029 = 464443) (by norm_num)
theorem B3302705 : Blo 2201435 3302705 := bstep (se 2 (by rfl) ⟨1238514, by rfl⟩ : syracuseStep 3302705 = 2477029) B2477029
theorem B2201803 : Blo 2201435 2201803 := bstep (se 1 (by rfl) ⟨1651352, by rfl⟩ : syracuseStep 2201803 = 3302705) B3302705
theorem B3347773 : Blo 2201435 3347773 := bbase (se 3 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 3347773 = 1255415) (by norm_num)
theorem B17854789 : Blo 2201435 17854789 := bstep (se 4 (by rfl) ⟨1673886, by rfl⟩ : syracuseStep 17854789 = 3347773) B3347773
theorem B23806385 : Blo 2201435 23806385 := bstep (se 2 (by rfl) ⟨8927394, by rfl⟩ : syracuseStep 23806385 = 17854789) B17854789
theorem B15870923 : Blo 2201435 15870923 := bstep (se 1 (by rfl) ⟨11903192, by rfl⟩ : syracuseStep 15870923 = 23806385) B23806385
theorem B10580615 : Blo 2201435 10580615 := bstep (se 1 (by rfl) ⟨7935461, by rfl⟩ : syracuseStep 10580615 = 15870923) B15870923
theorem B7053743 : Blo 2201435 7053743 := bstep (se 1 (by rfl) ⟨5290307, by rfl⟩ : syracuseStep 7053743 = 10580615) B10580615
theorem B4702495 : Blo 2201435 4702495 := bstep (se 1 (by rfl) ⟨3526871, by rfl⟩ : syracuseStep 4702495 = 7053743) B7053743
theorem B6269993 : Blo 2201435 6269993 := bstep (se 2 (by rfl) ⟨2351247, by rfl⟩ : syracuseStep 6269993 = 4702495) B4702495
theorem B4179995 : Blo 2201435 4179995 := bstep (se 1 (by rfl) ⟨3134996, by rfl⟩ : syracuseStep 4179995 = 6269993) B6269993
theorem B2786663 : Blo 2201435 2786663 := bstep (se 1 (by rfl) ⟨2089997, by rfl⟩ : syracuseStep 2786663 = 4179995) B4179995
theorem B7431101 : Blo 2201435 7431101 := bstep (se 3 (by rfl) ⟨1393331, by rfl⟩ : syracuseStep 7431101 = 2786663) B2786663
theorem B4954067 : Blo 2201435 4954067 := bstep (se 1 (by rfl) ⟨3715550, by rfl⟩ : syracuseStep 4954067 = 7431101) B7431101
theorem B3302711 : Blo 2201435 3302711 := bstep (se 1 (by rfl) ⟨2477033, by rfl⟩ : syracuseStep 3302711 = 4954067) B4954067
theorem B2201807 : Blo 2201435 2201807 := bstep (se 1 (by rfl) ⟨1651355, by rfl⟩ : syracuseStep 2201807 = 3302711) B3302711
theorem B3302717 : Blo 2201435 3302717 := bbase (se 3 (by rfl) ⟨619259, by rfl⟩ : syracuseStep 3302717 = 1238519) (by norm_num)
theorem B2201811 : Blo 2201435 2201811 := bstep (se 1 (by rfl) ⟨1651358, by rfl⟩ : syracuseStep 2201811 = 3302717) B3302717
theorem B4954085 : Blo 2201435 4954085 := bbase (se 4 (by rfl) ⟨464445, by rfl⟩ : syracuseStep 4954085 = 928891) (by norm_num)
theorem B3302723 : Blo 2201435 3302723 := bstep (se 1 (by rfl) ⟨2477042, by rfl⟩ : syracuseStep 3302723 = 4954085) B4954085
theorem B2201815 : Blo 2201435 2201815 := bstep (se 1 (by rfl) ⟨1651361, by rfl⟩ : syracuseStep 2201815 = 3302723) B3302723
theorem B5573357 : Blo 2201435 5573357 := bbase (se 3 (by rfl) ⟨1045004, by rfl⟩ : syracuseStep 5573357 = 2090009) (by norm_num)
theorem B3715571 : Blo 2201435 3715571 := bstep (se 1 (by rfl) ⟨2786678, by rfl⟩ : syracuseStep 3715571 = 5573357) B5573357
theorem B2477047 : Blo 2201435 2477047 := bstep (se 1 (by rfl) ⟨1857785, by rfl⟩ : syracuseStep 2477047 = 3715571) B3715571
theorem B3302729 : Blo 2201435 3302729 := bstep (se 2 (by rfl) ⟨1238523, by rfl⟩ : syracuseStep 3302729 = 2477047) B2477047
theorem B2201819 : Blo 2201435 2201819 := bstep (se 1 (by rfl) ⟨1651364, by rfl⟩ : syracuseStep 2201819 = 3302729) B3302729
theorem B2645173 : Blo 2201435 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B3526897 : Blo 2201435 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B4702529 : Blo 2201435 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B3135019 : Blo 2201435 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B4180025 : Blo 2201435 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B11146733 : Blo 2201435 11146733 := bstep (se 3 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 11146733 = 4180025) B4180025
theorem B7431155 : Blo 2201435 7431155 := bstep (se 1 (by rfl) ⟨5573366, by rfl⟩ : syracuseStep 7431155 = 11146733) B11146733
theorem B4954103 : Blo 2201435 4954103 := bstep (se 1 (by rfl) ⟨3715577, by rfl⟩ : syracuseStep 4954103 = 7431155) B7431155
theorem B3302735 : Blo 2201435 3302735 := bstep (se 1 (by rfl) ⟨2477051, by rfl⟩ : syracuseStep 3302735 = 4954103) B4954103
theorem B2201823 : Blo 2201435 2201823 := bstep (se 1 (by rfl) ⟨1651367, by rfl⟩ : syracuseStep 2201823 = 3302735) B3302735
theorem B3302741 : Blo 2201435 3302741 := bbase (se 12 (by rfl) ⟨1209, by rfl⟩ : syracuseStep 3302741 = 2419) (by norm_num)
theorem B2201827 : Blo 2201435 2201827 := bstep (se 1 (by rfl) ⟨1651370, by rfl⟩ : syracuseStep 2201827 = 3302741) B3302741
theorem B2351273 : Blo 2201435 2351273 := bbase (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) (by norm_num)
theorem B6270061 : Blo 2201435 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B8360081 : Blo 2201435 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B5573387 : Blo 2201435 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B3715591 : Blo 2201435 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B4954121 : Blo 2201435 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B3302747 : Blo 2201435 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B2201831 : Blo 2201435 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B2477065 : Blo 2201435 2477065 := bbase (se 2 (by rfl) ⟨928899, by rfl⟩ : syracuseStep 2477065 = 1857799) (by norm_num)
theorem B3302753 : Blo 2201435 3302753 := bstep (se 2 (by rfl) ⟨1238532, by rfl⟩ : syracuseStep 3302753 = 2477065) B2477065
theorem B2201835 : Blo 2201435 2201835 := bstep (se 1 (by rfl) ⟨1651376, by rfl⟩ : syracuseStep 2201835 = 3302753) B3302753
theorem B3347821 : Blo 2201435 3347821 := bbase (se 3 (by rfl) ⟨627716, by rfl⟩ : syracuseStep 3347821 = 1255433) (by norm_num)
theorem B17855045 : Blo 2201435 17855045 := bstep (se 4 (by rfl) ⟨1673910, by rfl⟩ : syracuseStep 17855045 = 3347821) B3347821
theorem B11903363 : Blo 2201435 11903363 := bstep (se 1 (by rfl) ⟨8927522, by rfl⟩ : syracuseStep 11903363 = 17855045) B17855045
theorem B7935575 : Blo 2201435 7935575 := bstep (se 1 (by rfl) ⟨5951681, by rfl⟩ : syracuseStep 7935575 = 11903363) B11903363
theorem B21161533 : Blo 2201435 21161533 := bstep (se 3 (by rfl) ⟨3967787, by rfl⟩ : syracuseStep 21161533 = 7935575) B7935575
theorem B28215377 : Blo 2201435 28215377 := bstep (se 2 (by rfl) ⟨10580766, by rfl⟩ : syracuseStep 28215377 = 21161533) B21161533
theorem B18810251 : Blo 2201435 18810251 := bstep (se 1 (by rfl) ⟨14107688, by rfl⟩ : syracuseStep 18810251 = 28215377) B28215377
theorem B12540167 : Blo 2201435 12540167 := bstep (se 1 (by rfl) ⟨9405125, by rfl⟩ : syracuseStep 12540167 = 18810251) B18810251
theorem B8360111 : Blo 2201435 8360111 := bstep (se 1 (by rfl) ⟨6270083, by rfl⟩ : syracuseStep 8360111 = 12540167) B12540167
theorem B5573407 : Blo 2201435 5573407 := bstep (se 1 (by rfl) ⟨4180055, by rfl⟩ : syracuseStep 5573407 = 8360111) B8360111
theorem B7431209 : Blo 2201435 7431209 := bstep (se 2 (by rfl) ⟨2786703, by rfl⟩ : syracuseStep 7431209 = 5573407) B5573407
theorem B4954139 : Blo 2201435 4954139 := bstep (se 1 (by rfl) ⟨3715604, by rfl⟩ : syracuseStep 4954139 = 7431209) B7431209
theorem B3302759 : Blo 2201435 3302759 := bstep (se 1 (by rfl) ⟨2477069, by rfl⟩ : syracuseStep 3302759 = 4954139) B4954139
theorem B2201839 : Blo 2201435 2201839 := bstep (se 1 (by rfl) ⟨1651379, by rfl⟩ : syracuseStep 2201839 = 3302759) B3302759
theorem B3302765 : Blo 2201435 3302765 := bbase (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) (by norm_num)
theorem B2201843 : Blo 2201435 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B4954157 : Blo 2201435 4954157 := bbase (se 3 (by rfl) ⟨928904, by rfl⟩ : syracuseStep 4954157 = 1857809) (by norm_num)
theorem B3302771 : Blo 2201435 3302771 := bstep (se 1 (by rfl) ⟨2477078, by rfl⟩ : syracuseStep 3302771 = 4954157) B4954157
theorem B2201847 : Blo 2201435 2201847 := bstep (se 1 (by rfl) ⟨1651385, by rfl⟩ : syracuseStep 2201847 = 3302771) B3302771
theorem B8043893 : Blo 2201435 8043893 := bbase (se 5 (by rfl) ⟨377057, by rfl⟩ : syracuseStep 8043893 = 754115) (by norm_num)
theorem B5362595 : Blo 2201435 5362595 := bstep (se 1 (by rfl) ⟨4021946, by rfl⟩ : syracuseStep 5362595 = 8043893) B8043893
theorem B3575063 : Blo 2201435 3575063 := bstep (se 1 (by rfl) ⟨2681297, by rfl⟩ : syracuseStep 3575063 = 5362595) B5362595
theorem B2383375 : Blo 2201435 2383375 := bstep (se 1 (by rfl) ⟨1787531, by rfl⟩ : syracuseStep 2383375 = 3575063) B3575063
theorem B3177833 : Blo 2201435 3177833 := bstep (se 2 (by rfl) ⟨1191687, by rfl⟩ : syracuseStep 3177833 = 2383375) B2383375
theorem B8474221 : Blo 2201435 8474221 := bstep (se 3 (by rfl) ⟨1588916, by rfl⟩ : syracuseStep 8474221 = 3177833) B3177833
theorem B11298961 : Blo 2201435 11298961 := bstep (se 2 (by rfl) ⟨4237110, by rfl⟩ : syracuseStep 11298961 = 8474221) B8474221
theorem B15065281 : Blo 2201435 15065281 := bstep (se 2 (by rfl) ⟨5649480, by rfl⟩ : syracuseStep 15065281 = 11298961) B11298961
theorem B20087041 : Blo 2201435 20087041 := bstep (se 2 (by rfl) ⟨7532640, by rfl⟩ : syracuseStep 20087041 = 15065281) B15065281
theorem B26782721 : Blo 2201435 26782721 := bstep (se 2 (by rfl) ⟨10043520, by rfl⟩ : syracuseStep 26782721 = 20087041) B20087041
theorem B17855147 : Blo 2201435 17855147 := bstep (se 1 (by rfl) ⟨13391360, by rfl⟩ : syracuseStep 17855147 = 26782721) B26782721
theorem B11903431 : Blo 2201435 11903431 := bstep (se 1 (by rfl) ⟨8927573, by rfl⟩ : syracuseStep 11903431 = 17855147) B17855147
theorem B15871241 : Blo 2201435 15871241 := bstep (se 2 (by rfl) ⟨5951715, by rfl⟩ : syracuseStep 15871241 = 11903431) B11903431
theorem B10580827 : Blo 2201435 10580827 := bstep (se 1 (by rfl) ⟨7935620, by rfl⟩ : syracuseStep 10580827 = 15871241) B15871241
theorem B14107769 : Blo 2201435 14107769 := bstep (se 2 (by rfl) ⟨5290413, by rfl⟩ : syracuseStep 14107769 = 10580827) B10580827
theorem B9405179 : Blo 2201435 9405179 := bstep (se 1 (by rfl) ⟨7053884, by rfl⟩ : syracuseStep 9405179 = 14107769) B14107769
theorem B6270119 : Blo 2201435 6270119 := bstep (se 1 (by rfl) ⟨4702589, by rfl⟩ : syracuseStep 6270119 = 9405179) B9405179
theorem B4180079 : Blo 2201435 4180079 := bstep (se 1 (by rfl) ⟨3135059, by rfl⟩ : syracuseStep 4180079 = 6270119) B6270119
theorem B2786719 : Blo 2201435 2786719 := bstep (se 1 (by rfl) ⟨2090039, by rfl⟩ : syracuseStep 2786719 = 4180079) B4180079
theorem B3715625 : Blo 2201435 3715625 := bstep (se 2 (by rfl) ⟨1393359, by rfl⟩ : syracuseStep 3715625 = 2786719) B2786719
theorem B2477083 : Blo 2201435 2477083 := bstep (se 1 (by rfl) ⟨1857812, by rfl⟩ : syracuseStep 2477083 = 3715625) B3715625
theorem B3302777 : Blo 2201435 3302777 := bstep (se 2 (by rfl) ⟨1238541, by rfl⟩ : syracuseStep 3302777 = 2477083) B2477083
theorem B2201851 : Blo 2201435 2201851 := bstep (se 1 (by rfl) ⟨1651388, by rfl⟩ : syracuseStep 2201851 = 3302777) B3302777
theorem B13391381 : Blo 2201435 13391381 := bbase (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) (by norm_num)
theorem B8927587 : Blo 2201435 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B11903449 : Blo 2201435 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B15871265 : Blo 2201435 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B10580843 : Blo 2201435 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B7053895 : Blo 2201435 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B37620773 : Blo 2201435 37620773 := bstep (se 4 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 37620773 = 7053895) B7053895
theorem B25080515 : Blo 2201435 25080515 := bstep (se 1 (by rfl) ⟨18810386, by rfl⟩ : syracuseStep 25080515 = 37620773) B37620773
theorem B16720343 : Blo 2201435 16720343 := bstep (se 1 (by rfl) ⟨12540257, by rfl⟩ : syracuseStep 16720343 = 25080515) B25080515
theorem B11146895 : Blo 2201435 11146895 := bstep (se 1 (by rfl) ⟨8360171, by rfl⟩ : syracuseStep 11146895 = 16720343) B16720343
theorem B7431263 : Blo 2201435 7431263 := bstep (se 1 (by rfl) ⟨5573447, by rfl⟩ : syracuseStep 7431263 = 11146895) B11146895
theorem B4954175 : Blo 2201435 4954175 := bstep (se 1 (by rfl) ⟨3715631, by rfl⟩ : syracuseStep 4954175 = 7431263) B7431263
theorem B3302783 : Blo 2201435 3302783 := bstep (se 1 (by rfl) ⟨2477087, by rfl⟩ : syracuseStep 3302783 = 4954175) B4954175
theorem B2201855 : Blo 2201435 2201855 := bstep (se 1 (by rfl) ⟨1651391, by rfl⟩ : syracuseStep 2201855 = 3302783) B3302783
theorem B3302789 : Blo 2201435 3302789 := bbase (se 4 (by rfl) ⟨309636, by rfl⟩ : syracuseStep 3302789 = 619273) (by norm_num)
theorem B2201859 : Blo 2201435 2201859 := bstep (se 1 (by rfl) ⟨1651394, by rfl⟩ : syracuseStep 2201859 = 3302789) B3302789
theorem B3715645 : Blo 2201435 3715645 := bbase (se 3 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 3715645 = 1393367) (by norm_num)
theorem B4954193 : Blo 2201435 4954193 := bstep (se 2 (by rfl) ⟨1857822, by rfl⟩ : syracuseStep 4954193 = 3715645) B3715645
theorem B3302795 : Blo 2201435 3302795 := bstep (se 1 (by rfl) ⟨2477096, by rfl⟩ : syracuseStep 3302795 = 4954193) B4954193
theorem B2201863 : Blo 2201435 2201863 := bstep (se 1 (by rfl) ⟨1651397, by rfl⟩ : syracuseStep 2201863 = 3302795) B3302795
theorem B2477101 : Blo 2201435 2477101 := bbase (se 3 (by rfl) ⟨464456, by rfl⟩ : syracuseStep 2477101 = 928913) (by norm_num)
theorem B3302801 : Blo 2201435 3302801 := bstep (se 2 (by rfl) ⟨1238550, by rfl⟩ : syracuseStep 3302801 = 2477101) B2477101
theorem B2201867 : Blo 2201435 2201867 := bstep (se 1 (by rfl) ⟨1651400, by rfl⟩ : syracuseStep 2201867 = 3302801) B3302801
theorem B7431317 : Blo 2201435 7431317 := bbase (se 6 (by rfl) ⟨174171, by rfl⟩ : syracuseStep 7431317 = 348343) (by norm_num)
theorem B4954211 : Blo 2201435 4954211 := bstep (se 1 (by rfl) ⟨3715658, by rfl⟩ : syracuseStep 4954211 = 7431317) B7431317
theorem B3302807 : Blo 2201435 3302807 := bstep (se 1 (by rfl) ⟨2477105, by rfl⟩ : syracuseStep 3302807 = 4954211) B4954211
theorem B2201871 : Blo 2201435 2201871 := bstep (se 1 (by rfl) ⟨1651403, by rfl⟩ : syracuseStep 2201871 = 3302807) B3302807
theorem B3302813 : Blo 2201435 3302813 := bbase (se 3 (by rfl) ⟨619277, by rfl⟩ : syracuseStep 3302813 = 1238555) (by norm_num)
theorem B2201875 : Blo 2201435 2201875 := bstep (se 1 (by rfl) ⟨1651406, by rfl⟩ : syracuseStep 2201875 = 3302813) B3302813
theorem B4954229 : Blo 2201435 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B3302819 : Blo 2201435 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B2201879 : Blo 2201435 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B2645245 : Blo 2201435 2645245 := bbase (se 3 (by rfl) ⟨495983, by rfl⟩ : syracuseStep 2645245 = 991967) (by norm_num)
theorem B3526993 : Blo 2201435 3526993 := bstep (se 2 (by rfl) ⟨1322622, by rfl⟩ : syracuseStep 3526993 = 2645245) B2645245
theorem B18810629 : Blo 2201435 18810629 := bstep (se 4 (by rfl) ⟨1763496, by rfl⟩ : syracuseStep 18810629 = 3526993) B3526993
theorem B12540419 : Blo 2201435 12540419 := bstep (se 1 (by rfl) ⟨9405314, by rfl⟩ : syracuseStep 12540419 = 18810629) B18810629
theorem B8360279 : Blo 2201435 8360279 := bstep (se 1 (by rfl) ⟨6270209, by rfl⟩ : syracuseStep 8360279 = 12540419) B12540419
theorem B5573519 : Blo 2201435 5573519 := bstep (se 1 (by rfl) ⟨4180139, by rfl⟩ : syracuseStep 5573519 = 8360279) B8360279
theorem B3715679 : Blo 2201435 3715679 := bstep (se 1 (by rfl) ⟨2786759, by rfl⟩ : syracuseStep 3715679 = 5573519) B5573519
theorem B2477119 : Blo 2201435 2477119 := bstep (se 1 (by rfl) ⟨1857839, by rfl⟩ : syracuseStep 2477119 = 3715679) B3715679
theorem B3302825 : Blo 2201435 3302825 := bstep (se 2 (by rfl) ⟨1238559, by rfl⟩ : syracuseStep 3302825 = 2477119) B2477119
theorem B2201883 : Blo 2201435 2201883 := bstep (se 1 (by rfl) ⟨1651412, by rfl⟩ : syracuseStep 2201883 = 3302825) B3302825
theorem B8360293 : Blo 2201435 8360293 := bbase (se 4 (by rfl) ⟨783777, by rfl⟩ : syracuseStep 8360293 = 1567555) (by norm_num)
theorem B11147057 : Blo 2201435 11147057 := bstep (se 2 (by rfl) ⟨4180146, by rfl⟩ : syracuseStep 11147057 = 8360293) B8360293
theorem B7431371 : Blo 2201435 7431371 := bstep (se 1 (by rfl) ⟨5573528, by rfl⟩ : syracuseStep 7431371 = 11147057) B11147057
theorem B4954247 : Blo 2201435 4954247 := bstep (se 1 (by rfl) ⟨3715685, by rfl⟩ : syracuseStep 4954247 = 7431371) B7431371
theorem B3302831 : Blo 2201435 3302831 := bstep (se 1 (by rfl) ⟨2477123, by rfl⟩ : syracuseStep 3302831 = 4954247) B4954247
theorem B2201887 : Blo 2201435 2201887 := bstep (se 1 (by rfl) ⟨1651415, by rfl⟩ : syracuseStep 2201887 = 3302831) B3302831
theorem B3302837 : Blo 2201435 3302837 := bbase (se 5 (by rfl) ⟨154820, by rfl⟩ : syracuseStep 3302837 = 309641) (by norm_num)
theorem B2201891 : Blo 2201435 2201891 := bstep (se 1 (by rfl) ⟨1651418, by rfl⟩ : syracuseStep 2201891 = 3302837) B3302837
theorem B5573549 : Blo 2201435 5573549 := bbase (se 3 (by rfl) ⟨1045040, by rfl⟩ : syracuseStep 5573549 = 2090081) (by norm_num)
theorem B3715699 : Blo 2201435 3715699 := bstep (se 1 (by rfl) ⟨2786774, by rfl⟩ : syracuseStep 3715699 = 5573549) B5573549
theorem B4954265 : Blo 2201435 4954265 := bstep (se 2 (by rfl) ⟨1857849, by rfl⟩ : syracuseStep 4954265 = 3715699) B3715699
theorem B3302843 : Blo 2201435 3302843 := bstep (se 1 (by rfl) ⟨2477132, by rfl⟩ : syracuseStep 3302843 = 4954265) B4954265
theorem B2201895 : Blo 2201435 2201895 := bstep (se 1 (by rfl) ⟨1651421, by rfl⟩ : syracuseStep 2201895 = 3302843) B3302843
theorem B2477137 : Blo 2201435 2477137 := bbase (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) (by norm_num)
theorem B3302849 : Blo 2201435 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B2201899 : Blo 2201435 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B3135133 : Blo 2201435 3135133 := bbase (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) (by norm_num)
theorem B4180177 : Blo 2201435 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B5573569 : Blo 2201435 5573569 := bstep (se 2 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 5573569 = 4180177) B4180177
theorem B7431425 : Blo 2201435 7431425 := bstep (se 2 (by rfl) ⟨2786784, by rfl⟩ : syracuseStep 7431425 = 5573569) B5573569
theorem B4954283 : Blo 2201435 4954283 := bstep (se 1 (by rfl) ⟨3715712, by rfl⟩ : syracuseStep 4954283 = 7431425) B7431425
theorem B3302855 : Blo 2201435 3302855 := bstep (se 1 (by rfl) ⟨2477141, by rfl⟩ : syracuseStep 3302855 = 4954283) B4954283
theorem B2201903 : Blo 2201435 2201903 := bstep (se 1 (by rfl) ⟨1651427, by rfl⟩ : syracuseStep 2201903 = 3302855) B3302855
theorem B3302861 : Blo 2201435 3302861 := bbase (se 3 (by rfl) ⟨619286, by rfl⟩ : syracuseStep 3302861 = 1238573) (by norm_num)
theorem B2201907 : Blo 2201435 2201907 := bstep (se 1 (by rfl) ⟨1651430, by rfl⟩ : syracuseStep 2201907 = 3302861) B3302861
theorem B4954301 : Blo 2201435 4954301 := bbase (se 3 (by rfl) ⟨928931, by rfl⟩ : syracuseStep 4954301 = 1857863) (by norm_num)
theorem B3302867 : Blo 2201435 3302867 := bstep (se 1 (by rfl) ⟨2477150, by rfl⟩ : syracuseStep 3302867 = 4954301) B4954301
theorem B2201911 : Blo 2201435 2201911 := bstep (se 1 (by rfl) ⟨1651433, by rfl⟩ : syracuseStep 2201911 = 3302867) B3302867
theorem B3715733 : Blo 2201435 3715733 := bbase (se 6 (by rfl) ⟨87087, by rfl⟩ : syracuseStep 3715733 = 174175) (by norm_num)
theorem B2477155 : Blo 2201435 2477155 := bstep (se 1 (by rfl) ⟨1857866, by rfl⟩ : syracuseStep 2477155 = 3715733) B3715733
theorem B3302873 : Blo 2201435 3302873 := bstep (se 2 (by rfl) ⟨1238577, by rfl⟩ : syracuseStep 3302873 = 2477155) B2477155
theorem B2201915 : Blo 2201435 2201915 := bstep (se 1 (by rfl) ⟨1651436, by rfl⟩ : syracuseStep 2201915 = 3302873) B3302873
theorem B43487381 : Blo 2201435 43487381 := bbase (se 6 (by rfl) ⟨1019235, by rfl⟩ : syracuseStep 43487381 = 2038471) (by norm_num)
theorem B28991587 : Blo 2201435 28991587 := bstep (se 1 (by rfl) ⟨21743690, by rfl⟩ : syracuseStep 28991587 = 43487381) B43487381
theorem B38655449 : Blo 2201435 38655449 := bstep (se 2 (by rfl) ⟨14495793, by rfl⟩ : syracuseStep 38655449 = 28991587) B28991587
theorem B25770299 : Blo 2201435 25770299 := bstep (se 1 (by rfl) ⟨19327724, by rfl⟩ : syracuseStep 25770299 = 38655449) B38655449
theorem B68720797 : Blo 2201435 68720797 := bstep (se 3 (by rfl) ⟨12885149, by rfl⟩ : syracuseStep 68720797 = 25770299) B25770299
theorem B91627729 : Blo 2201435 91627729 := bstep (se 2 (by rfl) ⟨34360398, by rfl⟩ : syracuseStep 91627729 = 68720797) B68720797
theorem B488681221 : Blo 2201435 488681221 := bstep (se 4 (by rfl) ⟨45813864, by rfl⟩ : syracuseStep 488681221 = 91627729) B91627729
theorem B651574961 : Blo 2201435 651574961 := bstep (se 2 (by rfl) ⟨244340610, by rfl⟩ : syracuseStep 651574961 = 488681221) B488681221
theorem B434383307 : Blo 2201435 434383307 := bstep (se 1 (by rfl) ⟨325787480, by rfl⟩ : syracuseStep 434383307 = 651574961) B651574961
theorem B289588871 : Blo 2201435 289588871 := bstep (se 1 (by rfl) ⟨217191653, by rfl⟩ : syracuseStep 289588871 = 434383307) B434383307
theorem B193059247 : Blo 2201435 193059247 := bstep (se 1 (by rfl) ⟨144794435, by rfl⟩ : syracuseStep 193059247 = 289588871) B289588871
theorem B257412329 : Blo 2201435 257412329 := bstep (se 2 (by rfl) ⟨96529623, by rfl⟩ : syracuseStep 257412329 = 193059247) B193059247
theorem B171608219 : Blo 2201435 171608219 := bstep (se 1 (by rfl) ⟨128706164, by rfl⟩ : syracuseStep 171608219 = 257412329) B257412329
theorem B114405479 : Blo 2201435 114405479 := bstep (se 1 (by rfl) ⟨85804109, by rfl⟩ : syracuseStep 114405479 = 171608219) B171608219
theorem B76270319 : Blo 2201435 76270319 := bstep (se 1 (by rfl) ⟨57202739, by rfl⟩ : syracuseStep 76270319 = 114405479) B114405479
theorem B50846879 : Blo 2201435 50846879 := bstep (se 1 (by rfl) ⟨38135159, by rfl⟩ : syracuseStep 50846879 = 76270319) B76270319
theorem B135591677 : Blo 2201435 135591677 := bstep (se 3 (by rfl) ⟨25423439, by rfl⟩ : syracuseStep 135591677 = 50846879) B50846879
theorem B90394451 : Blo 2201435 90394451 := bstep (se 1 (by rfl) ⟨67795838, by rfl⟩ : syracuseStep 90394451 = 135591677) B135591677
theorem B60262967 : Blo 2201435 60262967 := bstep (se 1 (by rfl) ⟨45197225, by rfl⟩ : syracuseStep 60262967 = 90394451) B90394451
theorem B40175311 : Blo 2201435 40175311 := bstep (se 1 (by rfl) ⟨30131483, by rfl⟩ : syracuseStep 40175311 = 60262967) B60262967
theorem B53567081 : Blo 2201435 53567081 := bstep (se 2 (by rfl) ⟨20087655, by rfl⟩ : syracuseStep 53567081 = 40175311) B40175311
theorem B35711387 : Blo 2201435 35711387 := bstep (se 1 (by rfl) ⟨26783540, by rfl⟩ : syracuseStep 35711387 = 53567081) B53567081
theorem B23807591 : Blo 2201435 23807591 := bstep (se 1 (by rfl) ⟨17855693, by rfl⟩ : syracuseStep 23807591 = 35711387) B35711387
theorem B15871727 : Blo 2201435 15871727 := bstep (se 1 (by rfl) ⟨11903795, by rfl⟩ : syracuseStep 15871727 = 23807591) B23807591
theorem B10581151 : Blo 2201435 10581151 := bstep (se 1 (by rfl) ⟨7935863, by rfl⟩ : syracuseStep 10581151 = 15871727) B15871727
theorem B14108201 : Blo 2201435 14108201 := bstep (se 2 (by rfl) ⟨5290575, by rfl⟩ : syracuseStep 14108201 = 10581151) B10581151
theorem B9405467 : Blo 2201435 9405467 := bstep (se 1 (by rfl) ⟨7054100, by rfl⟩ : syracuseStep 9405467 = 14108201) B14108201
theorem B6270311 : Blo 2201435 6270311 := bstep (se 1 (by rfl) ⟨4702733, by rfl⟩ : syracuseStep 6270311 = 9405467) B9405467
theorem B16720829 : Blo 2201435 16720829 := bstep (se 3 (by rfl) ⟨3135155, by rfl⟩ : syracuseStep 16720829 = 6270311) B6270311
theorem B11147219 : Blo 2201435 11147219 := bstep (se 1 (by rfl) ⟨8360414, by rfl⟩ : syracuseStep 11147219 = 16720829) B16720829
theorem B7431479 : Blo 2201435 7431479 := bstep (se 1 (by rfl) ⟨5573609, by rfl⟩ : syracuseStep 7431479 = 11147219) B11147219
theorem B4954319 : Blo 2201435 4954319 := bstep (se 1 (by rfl) ⟨3715739, by rfl⟩ : syracuseStep 4954319 = 7431479) B7431479
theorem B3302879 : Blo 2201435 3302879 := bstep (se 1 (by rfl) ⟨2477159, by rfl⟩ : syracuseStep 3302879 = 4954319) B4954319
theorem B2201919 : Blo 2201435 2201919 := bstep (se 1 (by rfl) ⟨1651439, by rfl⟩ : syracuseStep 2201919 = 3302879) B3302879
theorem B3302885 : Blo 2201435 3302885 := bbase (se 4 (by rfl) ⟨309645, by rfl⟩ : syracuseStep 3302885 = 619291) (by norm_num)
theorem B2201923 : Blo 2201435 2201923 := bstep (se 1 (by rfl) ⟨1651442, by rfl⟩ : syracuseStep 2201923 = 3302885) B3302885
theorem B5021933 : Blo 2201435 5021933 := bbase (se 3 (by rfl) ⟨941612, by rfl⟩ : syracuseStep 5021933 = 1883225) (by norm_num)
theorem B13391821 : Blo 2201435 13391821 := bstep (se 3 (by rfl) ⟨2510966, by rfl⟩ : syracuseStep 13391821 = 5021933) B5021933
theorem B71423045 : Blo 2201435 71423045 := bstep (se 4 (by rfl) ⟨6695910, by rfl⟩ : syracuseStep 71423045 = 13391821) B13391821
theorem B47615363 : Blo 2201435 47615363 := bstep (se 1 (by rfl) ⟨35711522, by rfl⟩ : syracuseStep 47615363 = 71423045) B71423045
theorem B31743575 : Blo 2201435 31743575 := bstep (se 1 (by rfl) ⟨23807681, by rfl⟩ : syracuseStep 31743575 = 47615363) B47615363
theorem B21162383 : Blo 2201435 21162383 := bstep (se 1 (by rfl) ⟨15871787, by rfl⟩ : syracuseStep 21162383 = 31743575) B31743575
theorem B14108255 : Blo 2201435 14108255 := bstep (se 1 (by rfl) ⟨10581191, by rfl⟩ : syracuseStep 14108255 = 21162383) B21162383
theorem B9405503 : Blo 2201435 9405503 := bstep (se 1 (by rfl) ⟨7054127, by rfl⟩ : syracuseStep 9405503 = 14108255) B14108255
theorem B6270335 : Blo 2201435 6270335 := bstep (se 1 (by rfl) ⟨4702751, by rfl⟩ : syracuseStep 6270335 = 9405503) B9405503
theorem B4180223 : Blo 2201435 4180223 := bstep (se 1 (by rfl) ⟨3135167, by rfl⟩ : syracuseStep 4180223 = 6270335) B6270335
theorem B2786815 : Blo 2201435 2786815 := bstep (se 1 (by rfl) ⟨2090111, by rfl⟩ : syracuseStep 2786815 = 4180223) B4180223
theorem B3715753 : Blo 2201435 3715753 := bstep (se 2 (by rfl) ⟨1393407, by rfl⟩ : syracuseStep 3715753 = 2786815) B2786815
theorem B4954337 : Blo 2201435 4954337 := bstep (se 2 (by rfl) ⟨1857876, by rfl⟩ : syracuseStep 4954337 = 3715753) B3715753
theorem B3302891 : Blo 2201435 3302891 := bstep (se 1 (by rfl) ⟨2477168, by rfl⟩ : syracuseStep 3302891 = 4954337) B4954337
theorem B2201927 : Blo 2201435 2201927 := bstep (se 1 (by rfl) ⟨1651445, by rfl⟩ : syracuseStep 2201927 = 3302891) B3302891
theorem B2477173 : Blo 2201435 2477173 := bbase (se 5 (by rfl) ⟨116117, by rfl⟩ : syracuseStep 2477173 = 232235) (by norm_num)
theorem B3302897 : Blo 2201435 3302897 := bstep (se 2 (by rfl) ⟨1238586, by rfl⟩ : syracuseStep 3302897 = 2477173) B2477173
theorem B2201931 : Blo 2201435 2201931 := bstep (se 1 (by rfl) ⟨1651448, by rfl⟩ : syracuseStep 2201931 = 3302897) B3302897
theorem B2786825 : Blo 2201435 2786825 := bbase (se 2 (by rfl) ⟨1045059, by rfl⟩ : syracuseStep 2786825 = 2090119) (by norm_num)
theorem B7431533 : Blo 2201435 7431533 := bstep (se 3 (by rfl) ⟨1393412, by rfl⟩ : syracuseStep 7431533 = 2786825) B2786825
theorem B4954355 : Blo 2201435 4954355 := bstep (se 1 (by rfl) ⟨3715766, by rfl⟩ : syracuseStep 4954355 = 7431533) B7431533
theorem B3302903 : Blo 2201435 3302903 := bstep (se 1 (by rfl) ⟨2477177, by rfl⟩ : syracuseStep 3302903 = 4954355) B4954355
theorem B2201935 : Blo 2201435 2201935 := bstep (se 1 (by rfl) ⟨1651451, by rfl⟩ : syracuseStep 2201935 = 3302903) B3302903
theorem B3302909 : Blo 2201435 3302909 := bbase (se 3 (by rfl) ⟨619295, by rfl⟩ : syracuseStep 3302909 = 1238591) (by norm_num)
theorem B2201939 : Blo 2201435 2201939 := bstep (se 1 (by rfl) ⟨1651454, by rfl⟩ : syracuseStep 2201939 = 3302909) B3302909
theorem B4954373 : Blo 2201435 4954373 := bbase (se 4 (by rfl) ⟨464472, by rfl⟩ : syracuseStep 4954373 = 928945) (by norm_num)
theorem B3302915 : Blo 2201435 3302915 := bstep (se 1 (by rfl) ⟨2477186, by rfl⟩ : syracuseStep 3302915 = 4954373) B4954373
theorem B2201943 : Blo 2201435 2201943 := bstep (se 1 (by rfl) ⟨1651457, by rfl⟩ : syracuseStep 2201943 = 3302915) B3302915
theorem B4180261 : Blo 2201435 4180261 := bbase (se 4 (by rfl) ⟨391899, by rfl⟩ : syracuseStep 4180261 = 783799) (by norm_num)
theorem B5573681 : Blo 2201435 5573681 := bstep (se 2 (by rfl) ⟨2090130, by rfl⟩ : syracuseStep 5573681 = 4180261) B4180261
theorem B3715787 : Blo 2201435 3715787 := bstep (se 1 (by rfl) ⟨2786840, by rfl⟩ : syracuseStep 3715787 = 5573681) B5573681
theorem B2477191 : Blo 2201435 2477191 := bstep (se 1 (by rfl) ⟨1857893, by rfl⟩ : syracuseStep 2477191 = 3715787) B3715787
theorem B3302921 : Blo 2201435 3302921 := bstep (se 2 (by rfl) ⟨1238595, by rfl⟩ : syracuseStep 3302921 = 2477191) B2477191
theorem B2201947 : Blo 2201435 2201947 := bstep (se 1 (by rfl) ⟨1651460, by rfl⟩ : syracuseStep 2201947 = 3302921) B3302921
theorem B11147381 : Blo 2201435 11147381 := bbase (se 5 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 11147381 = 1045067) (by norm_num)
theorem B7431587 : Blo 2201435 7431587 := bstep (se 1 (by rfl) ⟨5573690, by rfl⟩ : syracuseStep 7431587 = 11147381) B11147381
theorem B4954391 : Blo 2201435 4954391 := bstep (se 1 (by rfl) ⟨3715793, by rfl⟩ : syracuseStep 4954391 = 7431587) B7431587
theorem B3302927 : Blo 2201435 3302927 := bstep (se 1 (by rfl) ⟨2477195, by rfl⟩ : syracuseStep 3302927 = 4954391) B4954391
theorem B2201951 : Blo 2201435 2201951 := bstep (se 1 (by rfl) ⟨1651463, by rfl⟩ : syracuseStep 2201951 = 3302927) B3302927
theorem B3302933 : Blo 2201435 3302933 := bbase (se 6 (by rfl) ⟨77412, by rfl⟩ : syracuseStep 3302933 = 154825) (by norm_num)
theorem B2201955 : Blo 2201435 2201955 := bstep (se 1 (by rfl) ⟨1651466, by rfl⟩ : syracuseStep 2201955 = 3302933) B3302933
theorem B7054229 : Blo 2201435 7054229 := bbase (se 6 (by rfl) ⟨165333, by rfl⟩ : syracuseStep 7054229 = 330667) (by norm_num)
theorem B18811277 : Blo 2201435 18811277 := bstep (se 3 (by rfl) ⟨3527114, by rfl⟩ : syracuseStep 18811277 = 7054229) B7054229
theorem B12540851 : Blo 2201435 12540851 := bstep (se 1 (by rfl) ⟨9405638, by rfl⟩ : syracuseStep 12540851 = 18811277) B18811277
theorem B8360567 : Blo 2201435 8360567 := bstep (se 1 (by rfl) ⟨6270425, by rfl⟩ : syracuseStep 8360567 = 12540851) B12540851
theorem B5573711 : Blo 2201435 5573711 := bstep (se 1 (by rfl) ⟨4180283, by rfl⟩ : syracuseStep 5573711 = 8360567) B8360567
theorem B3715807 : Blo 2201435 3715807 := bstep (se 1 (by rfl) ⟨2786855, by rfl⟩ : syracuseStep 3715807 = 5573711) B5573711
theorem B4954409 : Blo 2201435 4954409 := bstep (se 2 (by rfl) ⟨1857903, by rfl⟩ : syracuseStep 4954409 = 3715807) B3715807
theorem B3302939 : Blo 2201435 3302939 := bstep (se 1 (by rfl) ⟨2477204, by rfl⟩ : syracuseStep 3302939 = 4954409) B4954409
theorem B2201959 : Blo 2201435 2201959 := bstep (se 1 (by rfl) ⟨1651469, by rfl⟩ : syracuseStep 2201959 = 3302939) B3302939
theorem B2477209 : Blo 2201435 2477209 := bbase (se 2 (by rfl) ⟨928953, by rfl⟩ : syracuseStep 2477209 = 1857907) (by norm_num)
theorem B3302945 : Blo 2201435 3302945 := bstep (se 2 (by rfl) ⟨1238604, by rfl⟩ : syracuseStep 3302945 = 2477209) B2477209
theorem B2201963 : Blo 2201435 2201963 := bstep (se 1 (by rfl) ⟨1651472, by rfl⟩ : syracuseStep 2201963 = 3302945) B3302945
theorem B8360597 : Blo 2201435 8360597 := bbase (se 6 (by rfl) ⟨195951, by rfl⟩ : syracuseStep 8360597 = 391903) (by norm_num)
theorem B5573731 : Blo 2201435 5573731 := bstep (se 1 (by rfl) ⟨4180298, by rfl⟩ : syracuseStep 5573731 = 8360597) B8360597
theorem B7431641 : Blo 2201435 7431641 := bstep (se 2 (by rfl) ⟨2786865, by rfl⟩ : syracuseStep 7431641 = 5573731) B5573731
theorem B4954427 : Blo 2201435 4954427 := bstep (se 1 (by rfl) ⟨3715820, by rfl⟩ : syracuseStep 4954427 = 7431641) B7431641
theorem B3302951 : Blo 2201435 3302951 := bstep (se 1 (by rfl) ⟨2477213, by rfl⟩ : syracuseStep 3302951 = 4954427) B4954427
theorem B2201967 : Blo 2201435 2201967 := bstep (se 1 (by rfl) ⟨1651475, by rfl⟩ : syracuseStep 2201967 = 3302951) B3302951
theorem B3302957 : Blo 2201435 3302957 := bbase (se 3 (by rfl) ⟨619304, by rfl⟩ : syracuseStep 3302957 = 1238609) (by norm_num)
theorem B2201971 : Blo 2201435 2201971 := bstep (se 1 (by rfl) ⟨1651478, by rfl⟩ : syracuseStep 2201971 = 3302957) B3302957
theorem B4954445 : Blo 2201435 4954445 := bbase (se 3 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 4954445 = 1857917) (by norm_num)
theorem B3302963 : Blo 2201435 3302963 := bstep (se 1 (by rfl) ⟨2477222, by rfl⟩ : syracuseStep 3302963 = 4954445) B4954445
theorem B2201975 : Blo 2201435 2201975 := bstep (se 1 (by rfl) ⟨1651481, by rfl⟩ : syracuseStep 2201975 = 3302963) B3302963
theorem B2786881 : Blo 2201435 2786881 := bbase (se 2 (by rfl) ⟨1045080, by rfl⟩ : syracuseStep 2786881 = 2090161) (by norm_num)
theorem B3715841 : Blo 2201435 3715841 := bstep (se 2 (by rfl) ⟨1393440, by rfl⟩ : syracuseStep 3715841 = 2786881) B2786881
theorem B2477227 : Blo 2201435 2477227 := bstep (se 1 (by rfl) ⟨1857920, by rfl⟩ : syracuseStep 2477227 = 3715841) B3715841
theorem B3302969 : Blo 2201435 3302969 := bstep (se 2 (by rfl) ⟨1238613, by rfl⟩ : syracuseStep 3302969 = 2477227) B2477227
theorem B2201979 : Blo 2201435 2201979 := bstep (se 1 (by rfl) ⟨1651484, by rfl⟩ : syracuseStep 2201979 = 3302969) B3302969
theorem B2645365 : Blo 2201435 2645365 := bbase (se 5 (by rfl) ⟨124001, by rfl⟩ : syracuseStep 2645365 = 248003) (by norm_num)
theorem B3527153 : Blo 2201435 3527153 := bstep (se 2 (by rfl) ⟨1322682, by rfl⟩ : syracuseStep 3527153 = 2645365) B2645365
theorem B2351435 : Blo 2201435 2351435 := bstep (se 1 (by rfl) ⟨1763576, by rfl⟩ : syracuseStep 2351435 = 3527153) B3527153
theorem B25081973 : Blo 2201435 25081973 := bstep (se 5 (by rfl) ⟨1175717, by rfl⟩ : syracuseStep 25081973 = 2351435) B2351435
theorem B16721315 : Blo 2201435 16721315 := bstep (se 1 (by rfl) ⟨12540986, by rfl⟩ : syracuseStep 16721315 = 25081973) B25081973
theorem B11147543 : Blo 2201435 11147543 := bstep (se 1 (by rfl) ⟨8360657, by rfl⟩ : syracuseStep 11147543 = 16721315) B16721315
theorem B7431695 : Blo 2201435 7431695 := bstep (se 1 (by rfl) ⟨5573771, by rfl⟩ : syracuseStep 7431695 = 11147543) B11147543
theorem B4954463 : Blo 2201435 4954463 := bstep (se 1 (by rfl) ⟨3715847, by rfl⟩ : syracuseStep 4954463 = 7431695) B7431695
theorem B3302975 : Blo 2201435 3302975 := bstep (se 1 (by rfl) ⟨2477231, by rfl⟩ : syracuseStep 3302975 = 4954463) B4954463
theorem B2201983 : Blo 2201435 2201983 := bstep (se 1 (by rfl) ⟨1651487, by rfl⟩ : syracuseStep 2201983 = 3302975) B3302975
theorem B3302981 : Blo 2201435 3302981 := bbase (se 4 (by rfl) ⟨309654, by rfl⟩ : syracuseStep 3302981 = 619309) (by norm_num)
theorem B2201987 : Blo 2201435 2201987 := bstep (se 1 (by rfl) ⟨1651490, by rfl⟩ : syracuseStep 2201987 = 3302981) B3302981
theorem B3715861 : Blo 2201435 3715861 := bbase (se 6 (by rfl) ⟨87090, by rfl⟩ : syracuseStep 3715861 = 174181) (by norm_num)
theorem B4954481 : Blo 2201435 4954481 := bstep (se 2 (by rfl) ⟨1857930, by rfl⟩ : syracuseStep 4954481 = 3715861) B3715861
theorem B3302987 : Blo 2201435 3302987 := bstep (se 1 (by rfl) ⟨2477240, by rfl⟩ : syracuseStep 3302987 = 4954481) B4954481
theorem B2201991 : Blo 2201435 2201991 := bstep (se 1 (by rfl) ⟨1651493, by rfl⟩ : syracuseStep 2201991 = 3302987) B3302987
theorem B2477245 : Blo 2201435 2477245 := bbase (se 3 (by rfl) ⟨464483, by rfl⟩ : syracuseStep 2477245 = 928967) (by norm_num)
theorem B3302993 : Blo 2201435 3302993 := bstep (se 2 (by rfl) ⟨1238622, by rfl⟩ : syracuseStep 3302993 = 2477245) B2477245
theorem B2201995 : Blo 2201435 2201995 := bstep (se 1 (by rfl) ⟨1651496, by rfl⟩ : syracuseStep 2201995 = 3302993) B3302993
theorem B7431749 : Blo 2201435 7431749 := bbase (se 4 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 7431749 = 1393453) (by norm_num)
theorem B4954499 : Blo 2201435 4954499 := bstep (se 1 (by rfl) ⟨3715874, by rfl⟩ : syracuseStep 4954499 = 7431749) B7431749
theorem B3302999 : Blo 2201435 3302999 := bstep (se 1 (by rfl) ⟨2477249, by rfl⟩ : syracuseStep 3302999 = 4954499) B4954499
theorem B2201999 : Blo 2201435 2201999 := bstep (se 1 (by rfl) ⟨1651499, by rfl⟩ : syracuseStep 2201999 = 3302999) B3302999
theorem B3303005 : Blo 2201435 3303005 := bbase (se 3 (by rfl) ⟨619313, by rfl⟩ : syracuseStep 3303005 = 1238627) (by norm_num)
theorem B2202003 : Blo 2201435 2202003 := bstep (se 1 (by rfl) ⟨1651502, by rfl⟩ : syracuseStep 2202003 = 3303005) B3303005
theorem B4954517 : Blo 2201435 4954517 := bbase (se 6 (by rfl) ⟨116121, by rfl⟩ : syracuseStep 4954517 = 232243) (by norm_num)
theorem B3303011 : Blo 2201435 3303011 := bstep (se 1 (by rfl) ⟨2477258, by rfl⟩ : syracuseStep 3303011 = 4954517) B4954517
theorem B2202007 : Blo 2201435 2202007 := bstep (se 1 (by rfl) ⟨1651505, by rfl⟩ : syracuseStep 2202007 = 3303011) B3303011
theorem B5952149 : Blo 2201435 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B3968099 : Blo 2201435 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2645399 : Blo 2201435 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B7054397 : Blo 2201435 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B4702931 : Blo 2201435 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B3135287 : Blo 2201435 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B8360765 : Blo 2201435 8360765 := bstep (se 3 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 8360765 = 3135287) B3135287
theorem B5573843 : Blo 2201435 5573843 := bstep (se 1 (by rfl) ⟨4180382, by rfl⟩ : syracuseStep 5573843 = 8360765) B8360765
theorem B3715895 : Blo 2201435 3715895 := bstep (se 1 (by rfl) ⟨2786921, by rfl⟩ : syracuseStep 3715895 = 5573843) B5573843
theorem B2477263 : Blo 2201435 2477263 := bstep (se 1 (by rfl) ⟨1857947, by rfl⟩ : syracuseStep 2477263 = 3715895) B3715895
theorem B3303017 : Blo 2201435 3303017 := bstep (se 2 (by rfl) ⟨1238631, by rfl⟩ : syracuseStep 3303017 = 2477263) B2477263
theorem B2202011 : Blo 2201435 2202011 := bstep (se 1 (by rfl) ⟨1651508, by rfl⟩ : syracuseStep 2202011 = 3303017) B3303017
theorem B9405877 : Blo 2201435 9405877 := bbase (se 5 (by rfl) ⟨440900, by rfl⟩ : syracuseStep 9405877 = 881801) (by norm_num)
theorem B12541169 : Blo 2201435 12541169 := bstep (se 2 (by rfl) ⟨4702938, by rfl⟩ : syracuseStep 12541169 = 9405877) B9405877
theorem B8360779 : Blo 2201435 8360779 := bstep (se 1 (by rfl) ⟨6270584, by rfl⟩ : syracuseStep 8360779 = 12541169) B12541169
theorem B11147705 : Blo 2201435 11147705 := bstep (se 2 (by rfl) ⟨4180389, by rfl⟩ : syracuseStep 11147705 = 8360779) B8360779
theorem B7431803 : Blo 2201435 7431803 := bstep (se 1 (by rfl) ⟨5573852, by rfl⟩ : syracuseStep 7431803 = 11147705) B11147705
theorem B4954535 : Blo 2201435 4954535 := bstep (se 1 (by rfl) ⟨3715901, by rfl⟩ : syracuseStep 4954535 = 7431803) B7431803
theorem B3303023 : Blo 2201435 3303023 := bstep (se 1 (by rfl) ⟨2477267, by rfl⟩ : syracuseStep 3303023 = 4954535) B4954535
theorem B2202015 : Blo 2201435 2202015 := bstep (se 1 (by rfl) ⟨1651511, by rfl⟩ : syracuseStep 2202015 = 3303023) B3303023
theorem B3303029 : Blo 2201435 3303029 := bbase (se 5 (by rfl) ⟨154829, by rfl⟩ : syracuseStep 3303029 = 309659) (by norm_num)
theorem B2202019 : Blo 2201435 2202019 := bstep (se 1 (by rfl) ⟨1651514, by rfl⟩ : syracuseStep 2202019 = 3303029) B3303029
theorem B4180405 : Blo 2201435 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B5573873 : Blo 2201435 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B3715915 : Blo 2201435 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B4954553 : Blo 2201435 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B3303035 : Blo 2201435 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B2202023 : Blo 2201435 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B2477281 : Blo 2201435 2477281 := bbase (se 2 (by rfl) ⟨928980, by rfl⟩ : syracuseStep 2477281 = 1857961) (by norm_num)
theorem B3303041 : Blo 2201435 3303041 := bstep (se 2 (by rfl) ⟨1238640, by rfl⟩ : syracuseStep 3303041 = 2477281) B2477281
theorem B2202027 : Blo 2201435 2202027 := bstep (se 1 (by rfl) ⟨1651520, by rfl⟩ : syracuseStep 2202027 = 3303041) B3303041
theorem B5573893 : Blo 2201435 5573893 := bbase (se 4 (by rfl) ⟨522552, by rfl⟩ : syracuseStep 5573893 = 1045105) (by norm_num)
theorem B7431857 : Blo 2201435 7431857 := bstep (se 2 (by rfl) ⟨2786946, by rfl⟩ : syracuseStep 7431857 = 5573893) B5573893
theorem B4954571 : Blo 2201435 4954571 := bstep (se 1 (by rfl) ⟨3715928, by rfl⟩ : syracuseStep 4954571 = 7431857) B7431857
theorem B3303047 : Blo 2201435 3303047 := bstep (se 1 (by rfl) ⟨2477285, by rfl⟩ : syracuseStep 3303047 = 4954571) B4954571
theorem B2202031 : Blo 2201435 2202031 := bstep (se 1 (by rfl) ⟨1651523, by rfl⟩ : syracuseStep 2202031 = 3303047) B3303047
theorem B3303053 : Blo 2201435 3303053 := bbase (se 3 (by rfl) ⟨619322, by rfl⟩ : syracuseStep 3303053 = 1238645) (by norm_num)
theorem B2202035 : Blo 2201435 2202035 := bstep (se 1 (by rfl) ⟨1651526, by rfl⟩ : syracuseStep 2202035 = 3303053) B3303053
theorem B4954589 : Blo 2201435 4954589 := bbase (se 3 (by rfl) ⟨928985, by rfl⟩ : syracuseStep 4954589 = 1857971) (by norm_num)
theorem B3303059 : Blo 2201435 3303059 := bstep (se 1 (by rfl) ⟨2477294, by rfl⟩ : syracuseStep 3303059 = 4954589) B4954589
theorem B2202039 : Blo 2201435 2202039 := bstep (se 1 (by rfl) ⟨1651529, by rfl⟩ : syracuseStep 2202039 = 3303059) B3303059
theorem B3715949 : Blo 2201435 3715949 := bbase (se 3 (by rfl) ⟨696740, by rfl⟩ : syracuseStep 3715949 = 1393481) (by norm_num)
theorem B2477299 : Blo 2201435 2477299 := bstep (se 1 (by rfl) ⟨1857974, by rfl⟩ : syracuseStep 2477299 = 3715949) B3715949
theorem B3303065 : Blo 2201435 3303065 := bstep (se 2 (by rfl) ⟨1238649, by rfl⟩ : syracuseStep 3303065 = 2477299) B2477299
theorem B2202043 : Blo 2201435 2202043 := bstep (se 1 (by rfl) ⟨1651532, by rfl⟩ : syracuseStep 2202043 = 3303065) B3303065
theorem B10872485 : Blo 2201435 10872485 := bbase (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) (by norm_num)
theorem B7248323 : Blo 2201435 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B19328861 : Blo 2201435 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B12885907 : Blo 2201435 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B17181209 : Blo 2201435 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B11454139 : Blo 2201435 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B15272185 : Blo 2201435 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B20362913 : Blo 2201435 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B13575275 : Blo 2201435 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B9050183 : Blo 2201435 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B6033455 : Blo 2201435 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B4022303 : Blo 2201435 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B42904565 : Blo 2201435 42904565 := bstep (se 5 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 42904565 = 4022303) B4022303
theorem B28603043 : Blo 2201435 28603043 := bstep (se 1 (by rfl) ⟨21452282, by rfl⟩ : syracuseStep 28603043 = 42904565) B42904565
theorem B19068695 : Blo 2201435 19068695 := bstep (se 1 (by rfl) ⟨14301521, by rfl⟩ : syracuseStep 19068695 = 28603043) B28603043
theorem B12712463 : Blo 2201435 12712463 := bstep (se 1 (by rfl) ⟨9534347, by rfl⟩ : syracuseStep 12712463 = 19068695) B19068695
theorem B8474975 : Blo 2201435 8474975 := bstep (se 1 (by rfl) ⟨6356231, by rfl⟩ : syracuseStep 8474975 = 12712463) B12712463
theorem B5649983 : Blo 2201435 5649983 := bstep (se 1 (by rfl) ⟨4237487, by rfl⟩ : syracuseStep 5649983 = 8474975) B8474975
theorem B3766655 : Blo 2201435 3766655 := bstep (se 1 (by rfl) ⟨2824991, by rfl⟩ : syracuseStep 3766655 = 5649983) B5649983
theorem B2511103 : Blo 2201435 2511103 := bstep (se 1 (by rfl) ⟨1883327, by rfl⟩ : syracuseStep 2511103 = 3766655) B3766655
theorem B3348137 : Blo 2201435 3348137 := bstep (se 2 (by rfl) ⟨1255551, by rfl⟩ : syracuseStep 3348137 = 2511103) B2511103
theorem B8928365 : Blo 2201435 8928365 := bstep (se 3 (by rfl) ⟨1674068, by rfl⟩ : syracuseStep 8928365 = 3348137) B3348137
theorem B23808973 : Blo 2201435 23808973 := bstep (se 3 (by rfl) ⟨4464182, by rfl⟩ : syracuseStep 23808973 = 8928365) B8928365
theorem B31745297 : Blo 2201435 31745297 := bstep (se 2 (by rfl) ⟨11904486, by rfl⟩ : syracuseStep 31745297 = 23808973) B23808973
theorem B21163531 : Blo 2201435 21163531 := bstep (se 1 (by rfl) ⟨15872648, by rfl⟩ : syracuseStep 21163531 = 31745297) B31745297
theorem B28218041 : Blo 2201435 28218041 := bstep (se 2 (by rfl) ⟨10581765, by rfl⟩ : syracuseStep 28218041 = 21163531) B21163531
theorem B18812027 : Blo 2201435 18812027 := bstep (se 1 (by rfl) ⟨14109020, by rfl⟩ : syracuseStep 18812027 = 28218041) B28218041
theorem B12541351 : Blo 2201435 12541351 := bstep (se 1 (by rfl) ⟨9406013, by rfl⟩ : syracuseStep 12541351 = 18812027) B18812027
theorem B16721801 : Blo 2201435 16721801 := bstep (se 2 (by rfl) ⟨6270675, by rfl⟩ : syracuseStep 16721801 = 12541351) B12541351
theorem B11147867 : Blo 2201435 11147867 := bstep (se 1 (by rfl) ⟨8360900, by rfl⟩ : syracuseStep 11147867 = 16721801) B16721801
theorem B7431911 : Blo 2201435 7431911 := bstep (se 1 (by rfl) ⟨5573933, by rfl⟩ : syracuseStep 7431911 = 11147867) B11147867
theorem B4954607 : Blo 2201435 4954607 := bstep (se 1 (by rfl) ⟨3715955, by rfl⟩ : syracuseStep 4954607 = 7431911) B7431911
theorem B3303071 : Blo 2201435 3303071 := bstep (se 1 (by rfl) ⟨2477303, by rfl⟩ : syracuseStep 3303071 = 4954607) B4954607
theorem B2202047 : Blo 2201435 2202047 := bstep (se 1 (by rfl) ⟨1651535, by rfl⟩ : syracuseStep 2202047 = 3303071) B3303071
theorem B3303077 : Blo 2201435 3303077 := bbase (se 4 (by rfl) ⟨309663, by rfl⟩ : syracuseStep 3303077 = 619327) (by norm_num)
theorem B2202051 : Blo 2201435 2202051 := bstep (se 1 (by rfl) ⟨1651538, by rfl⟩ : syracuseStep 2202051 = 3303077) B3303077
theorem B2786977 : Blo 2201435 2786977 := bbase (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) (by norm_num)
theorem B3715969 : Blo 2201435 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B4954625 : Blo 2201435 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B3303083 : Blo 2201435 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B2202055 : Blo 2201435 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B2477317 : Blo 2201435 2477317 := bbase (se 4 (by rfl) ⟨232248, by rfl⟩ : syracuseStep 2477317 = 464497) (by norm_num)
theorem B3303089 : Blo 2201435 3303089 := bstep (se 2 (by rfl) ⟨1238658, by rfl⟩ : syracuseStep 3303089 = 2477317) B2477317
theorem B2202059 : Blo 2201435 2202059 := bstep (se 1 (by rfl) ⟨1651544, by rfl⟩ : syracuseStep 2202059 = 3303089) B3303089
theorem B2351521 : Blo 2201435 2351521 := bbase (se 2 (by rfl) ⟨881820, by rfl⟩ : syracuseStep 2351521 = 1763641) (by norm_num)
theorem B3135361 : Blo 2201435 3135361 := bstep (se 2 (by rfl) ⟨1175760, by rfl⟩ : syracuseStep 3135361 = 2351521) B2351521
theorem B4180481 : Blo 2201435 4180481 := bstep (se 2 (by rfl) ⟨1567680, by rfl⟩ : syracuseStep 4180481 = 3135361) B3135361
theorem B2786987 : Blo 2201435 2786987 := bstep (se 1 (by rfl) ⟨2090240, by rfl⟩ : syracuseStep 2786987 = 4180481) B4180481
theorem B7431965 : Blo 2201435 7431965 := bstep (se 3 (by rfl) ⟨1393493, by rfl⟩ : syracuseStep 7431965 = 2786987) B2786987
theorem B4954643 : Blo 2201435 4954643 := bstep (se 1 (by rfl) ⟨3715982, by rfl⟩ : syracuseStep 4954643 = 7431965) B7431965
theorem B3303095 : Blo 2201435 3303095 := bstep (se 1 (by rfl) ⟨2477321, by rfl⟩ : syracuseStep 3303095 = 4954643) B4954643
theorem B2202063 : Blo 2201435 2202063 := bstep (se 1 (by rfl) ⟨1651547, by rfl⟩ : syracuseStep 2202063 = 3303095) B3303095
theorem B3303101 : Blo 2201435 3303101 := bbase (se 3 (by rfl) ⟨619331, by rfl⟩ : syracuseStep 3303101 = 1238663) (by norm_num)
theorem B2202067 : Blo 2201435 2202067 := bstep (se 1 (by rfl) ⟨1651550, by rfl⟩ : syracuseStep 2202067 = 3303101) B3303101
theorem B4954661 : Blo 2201435 4954661 := bbase (se 4 (by rfl) ⟨464499, by rfl⟩ : syracuseStep 4954661 = 928999) (by norm_num)
theorem B3303107 : Blo 2201435 3303107 := bstep (se 1 (by rfl) ⟨2477330, by rfl⟩ : syracuseStep 3303107 = 4954661) B4954661
theorem B2202071 : Blo 2201435 2202071 := bstep (se 1 (by rfl) ⟨1651553, by rfl⟩ : syracuseStep 2202071 = 3303107) B3303107
theorem B5574005 : Blo 2201435 5574005 := bbase (se 5 (by rfl) ⟨261281, by rfl⟩ : syracuseStep 5574005 = 522563) (by norm_num)
theorem B3716003 : Blo 2201435 3716003 := bstep (se 1 (by rfl) ⟨2787002, by rfl⟩ : syracuseStep 3716003 = 5574005) B5574005
theorem B2477335 : Blo 2201435 2477335 := bstep (se 1 (by rfl) ⟨1858001, by rfl⟩ : syracuseStep 2477335 = 3716003) B3716003
theorem B3303113 : Blo 2201435 3303113 := bstep (se 2 (by rfl) ⟨1238667, by rfl⟩ : syracuseStep 3303113 = 2477335) B2477335
theorem B2202075 : Blo 2201435 2202075 := bstep (se 1 (by rfl) ⟨1651556, by rfl⟩ : syracuseStep 2202075 = 3303113) B3303113
theorem B11904661 : Blo 2201435 11904661 := bbase (se 6 (by rfl) ⟨279015, by rfl⟩ : syracuseStep 11904661 = 558031) (by norm_num)
theorem B15872881 : Blo 2201435 15872881 := bstep (se 2 (by rfl) ⟨5952330, by rfl⟩ : syracuseStep 15872881 = 11904661) B11904661
theorem B21163841 : Blo 2201435 21163841 := bstep (se 2 (by rfl) ⟨7936440, by rfl⟩ : syracuseStep 21163841 = 15872881) B15872881
theorem B14109227 : Blo 2201435 14109227 := bstep (se 1 (by rfl) ⟨10581920, by rfl⟩ : syracuseStep 14109227 = 21163841) B21163841
theorem B9406151 : Blo 2201435 9406151 := bstep (se 1 (by rfl) ⟨7054613, by rfl⟩ : syracuseStep 9406151 = 14109227) B14109227
theorem B6270767 : Blo 2201435 6270767 := bstep (se 1 (by rfl) ⟨4703075, by rfl⟩ : syracuseStep 6270767 = 9406151) B9406151
theorem B4180511 : Blo 2201435 4180511 := bstep (se 1 (by rfl) ⟨3135383, by rfl⟩ : syracuseStep 4180511 = 6270767) B6270767
theorem B11148029 : Blo 2201435 11148029 := bstep (se 3 (by rfl) ⟨2090255, by rfl⟩ : syracuseStep 11148029 = 4180511) B4180511
theorem B7432019 : Blo 2201435 7432019 := bstep (se 1 (by rfl) ⟨5574014, by rfl⟩ : syracuseStep 7432019 = 11148029) B11148029
theorem B4954679 : Blo 2201435 4954679 := bstep (se 1 (by rfl) ⟨3716009, by rfl⟩ : syracuseStep 4954679 = 7432019) B7432019
theorem B3303119 : Blo 2201435 3303119 := bstep (se 1 (by rfl) ⟨2477339, by rfl⟩ : syracuseStep 3303119 = 4954679) B4954679
theorem B2202079 : Blo 2201435 2202079 := bstep (se 1 (by rfl) ⟨1651559, by rfl⟩ : syracuseStep 2202079 = 3303119) B3303119
theorem B3303125 : Blo 2201435 3303125 := bbase (se 7 (by rfl) ⟨38708, by rfl⟩ : syracuseStep 3303125 = 77417) (by norm_num)
theorem B2202083 : Blo 2201435 2202083 := bstep (se 1 (by rfl) ⟨1651562, by rfl⟩ : syracuseStep 2202083 = 3303125) B3303125
theorem B4703093 : Blo 2201435 4703093 := bbase (se 5 (by rfl) ⟨220457, by rfl⟩ : syracuseStep 4703093 = 440915) (by norm_num)
theorem B3135395 : Blo 2201435 3135395 := bstep (se 1 (by rfl) ⟨2351546, by rfl⟩ : syracuseStep 3135395 = 4703093) B4703093
theorem B8361053 : Blo 2201435 8361053 := bstep (se 3 (by rfl) ⟨1567697, by rfl⟩ : syracuseStep 8361053 = 3135395) B3135395
theorem B5574035 : Blo 2201435 5574035 := bstep (se 1 (by rfl) ⟨4180526, by rfl⟩ : syracuseStep 5574035 = 8361053) B8361053
theorem B3716023 : Blo 2201435 3716023 := bstep (se 1 (by rfl) ⟨2787017, by rfl⟩ : syracuseStep 3716023 = 5574035) B5574035
theorem B4954697 : Blo 2201435 4954697 := bstep (se 2 (by rfl) ⟨1858011, by rfl⟩ : syracuseStep 4954697 = 3716023) B3716023
theorem B3303131 : Blo 2201435 3303131 := bstep (se 1 (by rfl) ⟨2477348, by rfl⟩ : syracuseStep 3303131 = 4954697) B4954697
theorem B2202087 : Blo 2201435 2202087 := bstep (se 1 (by rfl) ⟨1651565, by rfl⟩ : syracuseStep 2202087 = 3303131) B3303131
theorem B2477353 : Blo 2201435 2477353 := bbase (se 2 (by rfl) ⟨929007, by rfl⟩ : syracuseStep 2477353 = 1858015) (by norm_num)
theorem B3303137 : Blo 2201435 3303137 := bstep (se 2 (by rfl) ⟨1238676, by rfl⟩ : syracuseStep 3303137 = 2477353) B2477353
theorem B2202091 : Blo 2201435 2202091 := bstep (se 1 (by rfl) ⟨1651568, by rfl⟩ : syracuseStep 2202091 = 3303137) B3303137
theorem B5022317 : Blo 2201435 5022317 := bbase (se 3 (by rfl) ⟨941684, by rfl⟩ : syracuseStep 5022317 = 1883369) (by norm_num)
theorem B3348211 : Blo 2201435 3348211 := bstep (se 1 (by rfl) ⟨2511158, by rfl⟩ : syracuseStep 3348211 = 5022317) B5022317
theorem B4464281 : Blo 2201435 4464281 := bstep (se 2 (by rfl) ⟨1674105, by rfl⟩ : syracuseStep 4464281 = 3348211) B3348211
theorem B2976187 : Blo 2201435 2976187 := bstep (se 1 (by rfl) ⟨2232140, by rfl⟩ : syracuseStep 2976187 = 4464281) B4464281
theorem B3968249 : Blo 2201435 3968249 := bstep (se 2 (by rfl) ⟨1488093, by rfl⟩ : syracuseStep 3968249 = 2976187) B2976187
theorem B10581997 : Blo 2201435 10581997 := bstep (se 3 (by rfl) ⟨1984124, by rfl⟩ : syracuseStep 10581997 = 3968249) B3968249
theorem B14109329 : Blo 2201435 14109329 := bstep (se 2 (by rfl) ⟨5290998, by rfl⟩ : syracuseStep 14109329 = 10581997) B10581997
theorem B9406219 : Blo 2201435 9406219 := bstep (se 1 (by rfl) ⟨7054664, by rfl⟩ : syracuseStep 9406219 = 14109329) B14109329
theorem B12541625 : Blo 2201435 12541625 := bstep (se 2 (by rfl) ⟨4703109, by rfl⟩ : syracuseStep 12541625 = 9406219) B9406219
theorem B8361083 : Blo 2201435 8361083 := bstep (se 1 (by rfl) ⟨6270812, by rfl⟩ : syracuseStep 8361083 = 12541625) B12541625
theorem B5574055 : Blo 2201435 5574055 := bstep (se 1 (by rfl) ⟨4180541, by rfl⟩ : syracuseStep 5574055 = 8361083) B8361083
theorem B7432073 : Blo 2201435 7432073 := bstep (se 2 (by rfl) ⟨2787027, by rfl⟩ : syracuseStep 7432073 = 5574055) B5574055
theorem B4954715 : Blo 2201435 4954715 := bstep (se 1 (by rfl) ⟨3716036, by rfl⟩ : syracuseStep 4954715 = 7432073) B7432073
theorem B3303143 : Blo 2201435 3303143 := bstep (se 1 (by rfl) ⟨2477357, by rfl⟩ : syracuseStep 3303143 = 4954715) B4954715
theorem B2202095 : Blo 2201435 2202095 := bstep (se 1 (by rfl) ⟨1651571, by rfl⟩ : syracuseStep 2202095 = 3303143) B3303143
theorem B3303149 : Blo 2201435 3303149 := bbase (se 3 (by rfl) ⟨619340, by rfl⟩ : syracuseStep 3303149 = 1238681) (by norm_num)
theorem B2202099 : Blo 2201435 2202099 := bstep (se 1 (by rfl) ⟨1651574, by rfl⟩ : syracuseStep 2202099 = 3303149) B3303149
theorem B4954733 : Blo 2201435 4954733 := bbase (se 3 (by rfl) ⟨929012, by rfl⟩ : syracuseStep 4954733 = 1858025) (by norm_num)
theorem B3303155 : Blo 2201435 3303155 := bstep (se 1 (by rfl) ⟨2477366, by rfl⟩ : syracuseStep 3303155 = 4954733) B4954733
theorem B2202103 : Blo 2201435 2202103 := bstep (se 1 (by rfl) ⟨1651577, by rfl⟩ : syracuseStep 2202103 = 3303155) B3303155
theorem B4180565 : Blo 2201435 4180565 := bbase (se 8 (by rfl) ⟨24495, by rfl⟩ : syracuseStep 4180565 = 48991) (by norm_num)
theorem B2787043 : Blo 2201435 2787043 := bstep (se 1 (by rfl) ⟨2090282, by rfl⟩ : syracuseStep 2787043 = 4180565) B4180565
theorem B3716057 : Blo 2201435 3716057 := bstep (se 2 (by rfl) ⟨1393521, by rfl⟩ : syracuseStep 3716057 = 2787043) B2787043
theorem B2477371 : Blo 2201435 2477371 := bstep (se 1 (by rfl) ⟨1858028, by rfl⟩ : syracuseStep 2477371 = 3716057) B3716057
theorem B3303161 : Blo 2201435 3303161 := bstep (se 2 (by rfl) ⟨1238685, by rfl⟩ : syracuseStep 3303161 = 2477371) B2477371
theorem B2202107 : Blo 2201435 2202107 := bstep (se 1 (by rfl) ⟨1651580, by rfl⟩ : syracuseStep 2202107 = 3303161) B3303161
theorem B63492437 : Blo 2201435 63492437 := bbase (se 10 (by rfl) ⟨93006, by rfl⟩ : syracuseStep 63492437 = 186013) (by norm_num)
theorem B42328291 : Blo 2201435 42328291 := bstep (se 1 (by rfl) ⟨31746218, by rfl⟩ : syracuseStep 42328291 = 63492437) B63492437
theorem B56437721 : Blo 2201435 56437721 := bstep (se 2 (by rfl) ⟨21164145, by rfl⟩ : syracuseStep 56437721 = 42328291) B42328291
theorem B37625147 : Blo 2201435 37625147 := bstep (se 1 (by rfl) ⟨28218860, by rfl⟩ : syracuseStep 37625147 = 56437721) B56437721
theorem B25083431 : Blo 2201435 25083431 := bstep (se 1 (by rfl) ⟨18812573, by rfl⟩ : syracuseStep 25083431 = 37625147) B37625147
theorem B16722287 : Blo 2201435 16722287 := bstep (se 1 (by rfl) ⟨12541715, by rfl⟩ : syracuseStep 16722287 = 25083431) B25083431
theorem B11148191 : Blo 2201435 11148191 := bstep (se 1 (by rfl) ⟨8361143, by rfl⟩ : syracuseStep 11148191 = 16722287) B16722287
theorem B7432127 : Blo 2201435 7432127 := bstep (se 1 (by rfl) ⟨5574095, by rfl⟩ : syracuseStep 7432127 = 11148191) B11148191
theorem B4954751 : Blo 2201435 4954751 := bstep (se 1 (by rfl) ⟨3716063, by rfl⟩ : syracuseStep 4954751 = 7432127) B7432127
theorem B3303167 : Blo 2201435 3303167 := bstep (se 1 (by rfl) ⟨2477375, by rfl⟩ : syracuseStep 3303167 = 4954751) B4954751
theorem B2202111 : Blo 2201435 2202111 := bstep (se 1 (by rfl) ⟨1651583, by rfl⟩ : syracuseStep 2202111 = 3303167) B3303167
theorem B3303173 : Blo 2201435 3303173 := bbase (se 4 (by rfl) ⟨309672, by rfl⟩ : syracuseStep 3303173 = 619345) (by norm_num)
theorem B2202115 : Blo 2201435 2202115 := bstep (se 1 (by rfl) ⟨1651586, by rfl⟩ : syracuseStep 2202115 = 3303173) B3303173
theorem B3716077 : Blo 2201435 3716077 := bbase (se 3 (by rfl) ⟨696764, by rfl⟩ : syracuseStep 3716077 = 1393529) (by norm_num)
theorem B4954769 : Blo 2201435 4954769 := bstep (se 2 (by rfl) ⟨1858038, by rfl⟩ : syracuseStep 4954769 = 3716077) B3716077
theorem B3303179 : Blo 2201435 3303179 := bstep (se 1 (by rfl) ⟨2477384, by rfl⟩ : syracuseStep 3303179 = 4954769) B4954769
theorem B2202119 : Blo 2201435 2202119 := bstep (se 1 (by rfl) ⟨1651589, by rfl⟩ : syracuseStep 2202119 = 3303179) B3303179
theorem B2477389 : Blo 2201435 2477389 := bbase (se 3 (by rfl) ⟨464510, by rfl⟩ : syracuseStep 2477389 = 929021) (by norm_num)
theorem B3303185 : Blo 2201435 3303185 := bstep (se 2 (by rfl) ⟨1238694, by rfl⟩ : syracuseStep 3303185 = 2477389) B2477389
theorem B2202123 : Blo 2201435 2202123 := bstep (se 1 (by rfl) ⟨1651592, by rfl⟩ : syracuseStep 2202123 = 3303185) B3303185
theorem B7432181 : Blo 2201435 7432181 := bbase (se 5 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 7432181 = 696767) (by norm_num)
theorem B4954787 : Blo 2201435 4954787 := bstep (se 1 (by rfl) ⟨3716090, by rfl⟩ : syracuseStep 4954787 = 7432181) B7432181
theorem B3303191 : Blo 2201435 3303191 := bstep (se 1 (by rfl) ⟨2477393, by rfl⟩ : syracuseStep 3303191 = 4954787) B4954787
theorem B2202127 : Blo 2201435 2202127 := bstep (se 1 (by rfl) ⟨1651595, by rfl⟩ : syracuseStep 2202127 = 3303191) B3303191
theorem B3303197 : Blo 2201435 3303197 := bbase (se 3 (by rfl) ⟨619349, by rfl⟩ : syracuseStep 3303197 = 1238699) (by norm_num)
theorem B2202131 : Blo 2201435 2202131 := bstep (se 1 (by rfl) ⟨1651598, by rfl⟩ : syracuseStep 2202131 = 3303197) B3303197
theorem B4954805 : Blo 2201435 4954805 := bbase (se 5 (by rfl) ⟨232256, by rfl⟩ : syracuseStep 4954805 = 464513) (by norm_num)
theorem B3303203 : Blo 2201435 3303203 := bstep (se 1 (by rfl) ⟨2477402, by rfl⟩ : syracuseStep 3303203 = 4954805) B4954805
theorem B2202135 : Blo 2201435 2202135 := bstep (se 1 (by rfl) ⟨1651601, by rfl⟩ : syracuseStep 2202135 = 3303203) B3303203
theorem B12541877 : Blo 2201435 12541877 := bbase (se 5 (by rfl) ⟨587900, by rfl⟩ : syracuseStep 12541877 = 1175801) (by norm_num)
theorem B8361251 : Blo 2201435 8361251 := bstep (se 1 (by rfl) ⟨6270938, by rfl⟩ : syracuseStep 8361251 = 12541877) B12541877
theorem B5574167 : Blo 2201435 5574167 := bstep (se 1 (by rfl) ⟨4180625, by rfl⟩ : syracuseStep 5574167 = 8361251) B8361251
theorem B3716111 : Blo 2201435 3716111 := bstep (se 1 (by rfl) ⟨2787083, by rfl⟩ : syracuseStep 3716111 = 5574167) B5574167
theorem B2477407 : Blo 2201435 2477407 := bstep (se 1 (by rfl) ⟨1858055, by rfl⟩ : syracuseStep 2477407 = 3716111) B3716111
theorem B3303209 : Blo 2201435 3303209 := bstep (se 2 (by rfl) ⟨1238703, by rfl⟩ : syracuseStep 3303209 = 2477407) B2477407
theorem B2202139 : Blo 2201435 2202139 := bstep (se 1 (by rfl) ⟨1651604, by rfl⟩ : syracuseStep 2202139 = 3303209) B3303209
theorem B6270949 : Blo 2201435 6270949 := bbase (se 4 (by rfl) ⟨587901, by rfl⟩ : syracuseStep 6270949 = 1175803) (by norm_num)
theorem B8361265 : Blo 2201435 8361265 := bstep (se 2 (by rfl) ⟨3135474, by rfl⟩ : syracuseStep 8361265 = 6270949) B6270949
theorem B11148353 : Blo 2201435 11148353 := bstep (se 2 (by rfl) ⟨4180632, by rfl⟩ : syracuseStep 11148353 = 8361265) B8361265
theorem B7432235 : Blo 2201435 7432235 := bstep (se 1 (by rfl) ⟨5574176, by rfl⟩ : syracuseStep 7432235 = 11148353) B11148353
theorem B4954823 : Blo 2201435 4954823 := bstep (se 1 (by rfl) ⟨3716117, by rfl⟩ : syracuseStep 4954823 = 7432235) B7432235
theorem B3303215 : Blo 2201435 3303215 := bstep (se 1 (by rfl) ⟨2477411, by rfl⟩ : syracuseStep 3303215 = 4954823) B4954823
theorem B2202143 : Blo 2201435 2202143 := bstep (se 1 (by rfl) ⟨1651607, by rfl⟩ : syracuseStep 2202143 = 3303215) B3303215
theorem B3303221 : Blo 2201435 3303221 := bbase (se 5 (by rfl) ⟨154838, by rfl⟩ : syracuseStep 3303221 = 309677) (by norm_num)
theorem B2202147 : Blo 2201435 2202147 := bstep (se 1 (by rfl) ⟨1651610, by rfl⟩ : syracuseStep 2202147 = 3303221) B3303221
theorem B5574197 : Blo 2201435 5574197 := bbase (se 5 (by rfl) ⟨261290, by rfl⟩ : syracuseStep 5574197 = 522581) (by norm_num)
theorem B3716131 : Blo 2201435 3716131 := bstep (se 1 (by rfl) ⟨2787098, by rfl⟩ : syracuseStep 3716131 = 5574197) B5574197
theorem B4954841 : Blo 2201435 4954841 := bstep (se 2 (by rfl) ⟨1858065, by rfl⟩ : syracuseStep 4954841 = 3716131) B3716131
theorem B3303227 : Blo 2201435 3303227 := bstep (se 1 (by rfl) ⟨2477420, by rfl⟩ : syracuseStep 3303227 = 4954841) B4954841
theorem B2202151 : Blo 2201435 2202151 := bstep (se 1 (by rfl) ⟨1651613, by rfl⟩ : syracuseStep 2202151 = 3303227) B3303227
theorem B2477425 : Blo 2201435 2477425 := bbase (se 2 (by rfl) ⟨929034, by rfl⟩ : syracuseStep 2477425 = 1858069) (by norm_num)
theorem B3303233 : Blo 2201435 3303233 := bstep (se 2 (by rfl) ⟨1238712, by rfl⟩ : syracuseStep 3303233 = 2477425) B2477425
theorem B2202155 : Blo 2201435 2202155 := bstep (se 1 (by rfl) ⟨1651616, by rfl⟩ : syracuseStep 2202155 = 3303233) B3303233
theorem B3968365 : Blo 2201435 3968365 := bbase (se 3 (by rfl) ⟨744068, by rfl⟩ : syracuseStep 3968365 = 1488137) (by norm_num)
theorem B5291153 : Blo 2201435 5291153 := bstep (se 2 (by rfl) ⟨1984182, by rfl⟩ : syracuseStep 5291153 = 3968365) B3968365
theorem B3527435 : Blo 2201435 3527435 := bstep (se 1 (by rfl) ⟨2645576, by rfl⟩ : syracuseStep 3527435 = 5291153) B5291153
theorem B9406493 : Blo 2201435 9406493 := bstep (se 3 (by rfl) ⟨1763717, by rfl⟩ : syracuseStep 9406493 = 3527435) B3527435
theorem B6270995 : Blo 2201435 6270995 := bstep (se 1 (by rfl) ⟨4703246, by rfl⟩ : syracuseStep 6270995 = 9406493) B9406493
theorem B4180663 : Blo 2201435 4180663 := bstep (se 1 (by rfl) ⟨3135497, by rfl⟩ : syracuseStep 4180663 = 6270995) B6270995
theorem B5574217 : Blo 2201435 5574217 := bstep (se 2 (by rfl) ⟨2090331, by rfl⟩ : syracuseStep 5574217 = 4180663) B4180663
theorem B7432289 : Blo 2201435 7432289 := bstep (se 2 (by rfl) ⟨2787108, by rfl⟩ : syracuseStep 7432289 = 5574217) B5574217
theorem B4954859 : Blo 2201435 4954859 := bstep (se 1 (by rfl) ⟨3716144, by rfl⟩ : syracuseStep 4954859 = 7432289) B7432289
theorem B3303239 : Blo 2201435 3303239 := bstep (se 1 (by rfl) ⟨2477429, by rfl⟩ : syracuseStep 3303239 = 4954859) B4954859
theorem B2202159 : Blo 2201435 2202159 := bstep (se 1 (by rfl) ⟨1651619, by rfl⟩ : syracuseStep 2202159 = 3303239) B3303239
theorem B3303245 : Blo 2201435 3303245 := bbase (se 3 (by rfl) ⟨619358, by rfl⟩ : syracuseStep 3303245 = 1238717) (by norm_num)
theorem B2202163 : Blo 2201435 2202163 := bstep (se 1 (by rfl) ⟨1651622, by rfl⟩ : syracuseStep 2202163 = 3303245) B3303245
theorem B4954877 : Blo 2201435 4954877 := bbase (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) (by norm_num)
theorem B3303251 : Blo 2201435 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B2202167 : Blo 2201435 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B3716165 : Blo 2201435 3716165 := bbase (se 4 (by rfl) ⟨348390, by rfl⟩ : syracuseStep 3716165 = 696781) (by norm_num)
theorem B2477443 : Blo 2201435 2477443 := bstep (se 1 (by rfl) ⟨1858082, by rfl⟩ : syracuseStep 2477443 = 3716165) B3716165
theorem B3303257 : Blo 2201435 3303257 := bstep (se 2 (by rfl) ⟨1238721, by rfl⟩ : syracuseStep 3303257 = 2477443) B2477443
theorem B2202171 : Blo 2201435 2202171 := bstep (se 1 (by rfl) ⟨1651628, by rfl⟩ : syracuseStep 2202171 = 3303257) B3303257
theorem B16722773 : Blo 2201435 16722773 := bbase (se 9 (by rfl) ⟨48992, by rfl⟩ : syracuseStep 16722773 = 97985) (by norm_num)
theorem B11148515 : Blo 2201435 11148515 := bstep (se 1 (by rfl) ⟨8361386, by rfl⟩ : syracuseStep 11148515 = 16722773) B16722773
theorem B7432343 : Blo 2201435 7432343 := bstep (se 1 (by rfl) ⟨5574257, by rfl⟩ : syracuseStep 7432343 = 11148515) B11148515
theorem B4954895 : Blo 2201435 4954895 := bstep (se 1 (by rfl) ⟨3716171, by rfl⟩ : syracuseStep 4954895 = 7432343) B7432343
theorem B3303263 : Blo 2201435 3303263 := bstep (se 1 (by rfl) ⟨2477447, by rfl⟩ : syracuseStep 3303263 = 4954895) B4954895
theorem B2202175 : Blo 2201435 2202175 := bstep (se 1 (by rfl) ⟨1651631, by rfl⟩ : syracuseStep 2202175 = 3303263) B3303263
theorem B3303269 : Blo 2201435 3303269 := bbase (se 4 (by rfl) ⟨309681, by rfl⟩ : syracuseStep 3303269 = 619363) (by norm_num)
theorem B2202179 : Blo 2201435 2202179 := bstep (se 1 (by rfl) ⟨1651634, by rfl⟩ : syracuseStep 2202179 = 3303269) B3303269
theorem B4180709 : Blo 2201435 4180709 := bbase (se 4 (by rfl) ⟨391941, by rfl⟩ : syracuseStep 4180709 = 783883) (by norm_num)
theorem B2787139 : Blo 2201435 2787139 := bstep (se 1 (by rfl) ⟨2090354, by rfl⟩ : syracuseStep 2787139 = 4180709) B4180709
theorem B3716185 : Blo 2201435 3716185 := bstep (se 2 (by rfl) ⟨1393569, by rfl⟩ : syracuseStep 3716185 = 2787139) B2787139
theorem B4954913 : Blo 2201435 4954913 := bstep (se 2 (by rfl) ⟨1858092, by rfl⟩ : syracuseStep 4954913 = 3716185) B3716185
theorem B3303275 : Blo 2201435 3303275 := bstep (se 1 (by rfl) ⟨2477456, by rfl⟩ : syracuseStep 3303275 = 4954913) B4954913
theorem B2202183 : Blo 2201435 2202183 := bstep (se 1 (by rfl) ⟨1651637, by rfl⟩ : syracuseStep 2202183 = 3303275) B3303275
theorem B2477461 : Blo 2201435 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B3303281 : Blo 2201435 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B2202187 : Blo 2201435 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B2787149 : Blo 2201435 2787149 := bbase (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) (by norm_num)
theorem B7432397 : Blo 2201435 7432397 := bstep (se 3 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 7432397 = 2787149) B2787149
theorem B4954931 : Blo 2201435 4954931 := bstep (se 1 (by rfl) ⟨3716198, by rfl⟩ : syracuseStep 4954931 = 7432397) B7432397
theorem B3303287 : Blo 2201435 3303287 := bstep (se 1 (by rfl) ⟨2477465, by rfl⟩ : syracuseStep 3303287 = 4954931) B4954931
theorem B2202191 : Blo 2201435 2202191 := bstep (se 1 (by rfl) ⟨1651643, by rfl⟩ : syracuseStep 2202191 = 3303287) B3303287
theorem B3303293 : Blo 2201435 3303293 := bbase (se 3 (by rfl) ⟨619367, by rfl⟩ : syracuseStep 3303293 = 1238735) (by norm_num)
theorem B2202195 : Blo 2201435 2202195 := bstep (se 1 (by rfl) ⟨1651646, by rfl⟩ : syracuseStep 2202195 = 3303293) B3303293
theorem B4954949 : Blo 2201435 4954949 := bbase (se 4 (by rfl) ⟨464526, by rfl⟩ : syracuseStep 4954949 = 929053) (by norm_num)
theorem B3303299 : Blo 2201435 3303299 := bstep (se 1 (by rfl) ⟨2477474, by rfl⟩ : syracuseStep 3303299 = 4954949) B4954949
theorem B2202199 : Blo 2201435 2202199 := bstep (se 1 (by rfl) ⟨1651649, by rfl⟩ : syracuseStep 2202199 = 3303299) B3303299
theorem B4703341 : Blo 2201435 4703341 := bbase (se 3 (by rfl) ⟨881876, by rfl⟩ : syracuseStep 4703341 = 1763753) (by norm_num)
theorem B6271121 : Blo 2201435 6271121 := bstep (se 2 (by rfl) ⟨2351670, by rfl⟩ : syracuseStep 6271121 = 4703341) B4703341
theorem B4180747 : Blo 2201435 4180747 := bstep (se 1 (by rfl) ⟨3135560, by rfl⟩ : syracuseStep 4180747 = 6271121) B6271121
theorem B5574329 : Blo 2201435 5574329 := bstep (se 2 (by rfl) ⟨2090373, by rfl⟩ : syracuseStep 5574329 = 4180747) B4180747
theorem B3716219 : Blo 2201435 3716219 := bstep (se 1 (by rfl) ⟨2787164, by rfl⟩ : syracuseStep 3716219 = 5574329) B5574329
theorem B2477479 : Blo 2201435 2477479 := bstep (se 1 (by rfl) ⟨1858109, by rfl⟩ : syracuseStep 2477479 = 3716219) B3716219
theorem B3303305 : Blo 2201435 3303305 := bstep (se 2 (by rfl) ⟨1238739, by rfl⟩ : syracuseStep 3303305 = 2477479) B2477479
theorem B2202203 : Blo 2201435 2202203 := bstep (se 1 (by rfl) ⟨1651652, by rfl⟩ : syracuseStep 2202203 = 3303305) B3303305
theorem B11148677 : Blo 2201435 11148677 := bbase (se 4 (by rfl) ⟨1045188, by rfl⟩ : syracuseStep 11148677 = 2090377) (by norm_num)
theorem B7432451 : Blo 2201435 7432451 := bstep (se 1 (by rfl) ⟨5574338, by rfl⟩ : syracuseStep 7432451 = 11148677) B11148677
theorem B4954967 : Blo 2201435 4954967 := bstep (se 1 (by rfl) ⟨3716225, by rfl⟩ : syracuseStep 4954967 = 7432451) B7432451
theorem B3303311 : Blo 2201435 3303311 := bstep (se 1 (by rfl) ⟨2477483, by rfl⟩ : syracuseStep 3303311 = 4954967) B4954967
theorem B2202207 : Blo 2201435 2202207 := bstep (se 1 (by rfl) ⟨1651655, by rfl⟩ : syracuseStep 2202207 = 3303311) B3303311
theorem B3303317 : Blo 2201435 3303317 := bbase (se 6 (by rfl) ⟨77421, by rfl⟩ : syracuseStep 3303317 = 154843) (by norm_num)
theorem B2202211 : Blo 2201435 2202211 := bstep (se 1 (by rfl) ⟨1651658, by rfl⟩ : syracuseStep 2202211 = 3303317) B3303317
theorem B3527525 : Blo 2201435 3527525 := bbase (se 4 (by rfl) ⟨330705, by rfl⟩ : syracuseStep 3527525 = 661411) (by norm_num)
theorem B2351683 : Blo 2201435 2351683 := bstep (se 1 (by rfl) ⟨1763762, by rfl⟩ : syracuseStep 2351683 = 3527525) B3527525
theorem B12542309 : Blo 2201435 12542309 := bstep (se 4 (by rfl) ⟨1175841, by rfl⟩ : syracuseStep 12542309 = 2351683) B2351683
theorem B8361539 : Blo 2201435 8361539 := bstep (se 1 (by rfl) ⟨6271154, by rfl⟩ : syracuseStep 8361539 = 12542309) B12542309
theorem B5574359 : Blo 2201435 5574359 := bstep (se 1 (by rfl) ⟨4180769, by rfl⟩ : syracuseStep 5574359 = 8361539) B8361539
theorem B3716239 : Blo 2201435 3716239 := bstep (se 1 (by rfl) ⟨2787179, by rfl⟩ : syracuseStep 3716239 = 5574359) B5574359
theorem B4954985 : Blo 2201435 4954985 := bstep (se 2 (by rfl) ⟨1858119, by rfl⟩ : syracuseStep 4954985 = 3716239) B3716239
theorem B3303323 : Blo 2201435 3303323 := bstep (se 1 (by rfl) ⟨2477492, by rfl⟩ : syracuseStep 3303323 = 4954985) B4954985
theorem B2202215 : Blo 2201435 2202215 := bstep (se 1 (by rfl) ⟨1651661, by rfl⟩ : syracuseStep 2202215 = 3303323) B3303323
theorem B2477497 : Blo 2201435 2477497 := bbase (se 2 (by rfl) ⟨929061, by rfl⟩ : syracuseStep 2477497 = 1858123) (by norm_num)
theorem B3303329 : Blo 2201435 3303329 := bstep (se 2 (by rfl) ⟨1238748, by rfl⟩ : syracuseStep 3303329 = 2477497) B2477497
theorem B2202219 : Blo 2201435 2202219 := bstep (se 1 (by rfl) ⟨1651664, by rfl⟩ : syracuseStep 2202219 = 3303329) B3303329
theorem B10582613 : Blo 2201435 10582613 := bbase (se 8 (by rfl) ⟨62007, by rfl⟩ : syracuseStep 10582613 = 124015) (by norm_num)
theorem B7055075 : Blo 2201435 7055075 := bstep (se 1 (by rfl) ⟨5291306, by rfl⟩ : syracuseStep 7055075 = 10582613) B10582613
theorem B4703383 : Blo 2201435 4703383 := bstep (se 1 (by rfl) ⟨3527537, by rfl⟩ : syracuseStep 4703383 = 7055075) B7055075
theorem B6271177 : Blo 2201435 6271177 := bstep (se 2 (by rfl) ⟨2351691, by rfl⟩ : syracuseStep 6271177 = 4703383) B4703383
theorem B8361569 : Blo 2201435 8361569 := bstep (se 2 (by rfl) ⟨3135588, by rfl⟩ : syracuseStep 8361569 = 6271177) B6271177
theorem B5574379 : Blo 2201435 5574379 := bstep (se 1 (by rfl) ⟨4180784, by rfl⟩ : syracuseStep 5574379 = 8361569) B8361569
theorem B7432505 : Blo 2201435 7432505 := bstep (se 2 (by rfl) ⟨2787189, by rfl⟩ : syracuseStep 7432505 = 5574379) B5574379
theorem B4955003 : Blo 2201435 4955003 := bstep (se 1 (by rfl) ⟨3716252, by rfl⟩ : syracuseStep 4955003 = 7432505) B7432505
theorem B3303335 : Blo 2201435 3303335 := bstep (se 1 (by rfl) ⟨2477501, by rfl⟩ : syracuseStep 3303335 = 4955003) B4955003
theorem B2202223 : Blo 2201435 2202223 := bstep (se 1 (by rfl) ⟨1651667, by rfl⟩ : syracuseStep 2202223 = 3303335) B3303335
theorem B3303341 : Blo 2201435 3303341 := bbase (se 3 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 3303341 = 1238753) (by norm_num)
theorem B2202227 : Blo 2201435 2202227 := bstep (se 1 (by rfl) ⟨1651670, by rfl⟩ : syracuseStep 2202227 = 3303341) B3303341
theorem B4955021 : Blo 2201435 4955021 := bbase (se 3 (by rfl) ⟨929066, by rfl⟩ : syracuseStep 4955021 = 1858133) (by norm_num)
theorem B3303347 : Blo 2201435 3303347 := bstep (se 1 (by rfl) ⟨2477510, by rfl⟩ : syracuseStep 3303347 = 4955021) B4955021
theorem B2202231 : Blo 2201435 2202231 := bstep (se 1 (by rfl) ⟨1651673, by rfl⟩ : syracuseStep 2202231 = 3303347) B3303347
theorem B2787205 : Blo 2201435 2787205 := bbase (se 4 (by rfl) ⟨261300, by rfl⟩ : syracuseStep 2787205 = 522601) (by norm_num)
theorem B3716273 : Blo 2201435 3716273 := bstep (se 2 (by rfl) ⟨1393602, by rfl⟩ : syracuseStep 3716273 = 2787205) B2787205
theorem B2477515 : Blo 2201435 2477515 := bstep (se 1 (by rfl) ⟨1858136, by rfl⟩ : syracuseStep 2477515 = 3716273) B3716273
theorem B3303353 : Blo 2201435 3303353 := bstep (se 2 (by rfl) ⟨1238757, by rfl⟩ : syracuseStep 3303353 = 2477515) B2477515
theorem B2202235 : Blo 2201435 2202235 := bstep (se 1 (by rfl) ⟨1651676, by rfl⟩ : syracuseStep 2202235 = 3303353) B3303353
theorem B28220501 : Blo 2201435 28220501 := bbase (se 8 (by rfl) ⟨165354, by rfl⟩ : syracuseStep 28220501 = 330709) (by norm_num)
theorem B18813667 : Blo 2201435 18813667 := bstep (se 1 (by rfl) ⟨14110250, by rfl⟩ : syracuseStep 18813667 = 28220501) B28220501
theorem B25084889 : Blo 2201435 25084889 := bstep (se 2 (by rfl) ⟨9406833, by rfl⟩ : syracuseStep 25084889 = 18813667) B18813667
theorem B16723259 : Blo 2201435 16723259 := bstep (se 1 (by rfl) ⟨12542444, by rfl⟩ : syracuseStep 16723259 = 25084889) B25084889
theorem B11148839 : Blo 2201435 11148839 := bstep (se 1 (by rfl) ⟨8361629, by rfl⟩ : syracuseStep 11148839 = 16723259) B16723259
theorem B7432559 : Blo 2201435 7432559 := bstep (se 1 (by rfl) ⟨5574419, by rfl⟩ : syracuseStep 7432559 = 11148839) B11148839
theorem B4955039 : Blo 2201435 4955039 := bstep (se 1 (by rfl) ⟨3716279, by rfl⟩ : syracuseStep 4955039 = 7432559) B7432559
theorem B3303359 : Blo 2201435 3303359 := bstep (se 1 (by rfl) ⟨2477519, by rfl⟩ : syracuseStep 3303359 = 4955039) B4955039
theorem B2202239 : Blo 2201435 2202239 := bstep (se 1 (by rfl) ⟨1651679, by rfl⟩ : syracuseStep 2202239 = 3303359) B3303359
theorem B3303365 : Blo 2201435 3303365 := bbase (se 4 (by rfl) ⟨309690, by rfl⟩ : syracuseStep 3303365 = 619381) (by norm_num)
theorem B2202243 : Blo 2201435 2202243 := bstep (se 1 (by rfl) ⟨1651682, by rfl⟩ : syracuseStep 2202243 = 3303365) B3303365
theorem B3716293 : Blo 2201435 3716293 := bbase (se 4 (by rfl) ⟨348402, by rfl⟩ : syracuseStep 3716293 = 696805) (by norm_num)
theorem B4955057 : Blo 2201435 4955057 := bstep (se 2 (by rfl) ⟨1858146, by rfl⟩ : syracuseStep 4955057 = 3716293) B3716293
theorem B3303371 : Blo 2201435 3303371 := bstep (se 1 (by rfl) ⟨2477528, by rfl⟩ : syracuseStep 3303371 = 4955057) B4955057
theorem B2202247 : Blo 2201435 2202247 := bstep (se 1 (by rfl) ⟨1651685, by rfl⟩ : syracuseStep 2202247 = 3303371) B3303371
theorem B2477533 : Blo 2201435 2477533 := bbase (se 3 (by rfl) ⟨464537, by rfl⟩ : syracuseStep 2477533 = 929075) (by norm_num)
theorem B3303377 : Blo 2201435 3303377 := bstep (se 2 (by rfl) ⟨1238766, by rfl⟩ : syracuseStep 3303377 = 2477533) B2477533
theorem B2202251 : Blo 2201435 2202251 := bstep (se 1 (by rfl) ⟨1651688, by rfl⟩ : syracuseStep 2202251 = 3303377) B3303377
theorem B7432613 : Blo 2201435 7432613 := bbase (se 4 (by rfl) ⟨696807, by rfl⟩ : syracuseStep 7432613 = 1393615) (by norm_num)
theorem B4955075 : Blo 2201435 4955075 := bstep (se 1 (by rfl) ⟨3716306, by rfl⟩ : syracuseStep 4955075 = 7432613) B7432613
theorem B3303383 : Blo 2201435 3303383 := bstep (se 1 (by rfl) ⟨2477537, by rfl⟩ : syracuseStep 3303383 = 4955075) B4955075
theorem B2202255 : Blo 2201435 2202255 := bstep (se 1 (by rfl) ⟨1651691, by rfl⟩ : syracuseStep 2202255 = 3303383) B3303383
theorem B3303389 : Blo 2201435 3303389 := bbase (se 3 (by rfl) ⟨619385, by rfl⟩ : syracuseStep 3303389 = 1238771) (by norm_num)
theorem B2202259 : Blo 2201435 2202259 := bstep (se 1 (by rfl) ⟨1651694, by rfl⟩ : syracuseStep 2202259 = 3303389) B3303389
theorem B4955093 : Blo 2201435 4955093 := bbase (se 7 (by rfl) ⟨58067, by rfl⟩ : syracuseStep 4955093 = 116135) (by norm_num)
theorem B3303395 : Blo 2201435 3303395 := bstep (se 1 (by rfl) ⟨2477546, by rfl⟩ : syracuseStep 3303395 = 4955093) B4955093
theorem B2202263 : Blo 2201435 2202263 := bstep (se 1 (by rfl) ⟨1651697, by rfl⟩ : syracuseStep 2202263 = 3303395) B3303395
theorem B2416349 : Blo 2201435 2416349 := bbase (se 3 (by rfl) ⟨453065, by rfl⟩ : syracuseStep 2416349 = 906131) (by norm_num)
theorem B6443597 : Blo 2201435 6443597 := bstep (se 3 (by rfl) ⟨1208174, by rfl⟩ : syracuseStep 6443597 = 2416349) B2416349
theorem B17182925 : Blo 2201435 17182925 := bstep (se 3 (by rfl) ⟨3221798, by rfl⟩ : syracuseStep 17182925 = 6443597) B6443597
theorem B11455283 : Blo 2201435 11455283 := bstep (se 1 (by rfl) ⟨8591462, by rfl⟩ : syracuseStep 11455283 = 17182925) B17182925
theorem B7636855 : Blo 2201435 7636855 := bstep (se 1 (by rfl) ⟨5727641, by rfl⟩ : syracuseStep 7636855 = 11455283) B11455283
theorem B10182473 : Blo 2201435 10182473 := bstep (se 2 (by rfl) ⟨3818427, by rfl⟩ : syracuseStep 10182473 = 7636855) B7636855
theorem B6788315 : Blo 2201435 6788315 := bstep (se 1 (by rfl) ⟨5091236, by rfl⟩ : syracuseStep 6788315 = 10182473) B10182473
theorem B4525543 : Blo 2201435 4525543 := bstep (se 1 (by rfl) ⟨3394157, by rfl⟩ : syracuseStep 4525543 = 6788315) B6788315
theorem B6034057 : Blo 2201435 6034057 := bstep (se 2 (by rfl) ⟨2262771, by rfl⟩ : syracuseStep 6034057 = 4525543) B4525543
theorem B32181637 : Blo 2201435 32181637 := bstep (se 4 (by rfl) ⟨3017028, by rfl⟩ : syracuseStep 32181637 = 6034057) B6034057
theorem B42908849 : Blo 2201435 42908849 := bstep (se 2 (by rfl) ⟨16090818, by rfl⟩ : syracuseStep 42908849 = 32181637) B32181637
theorem B28605899 : Blo 2201435 28605899 := bstep (se 1 (by rfl) ⟨21454424, by rfl⟩ : syracuseStep 28605899 = 42908849) B42908849
theorem B19070599 : Blo 2201435 19070599 := bstep (se 1 (by rfl) ⟨14302949, by rfl⟩ : syracuseStep 19070599 = 28605899) B28605899
theorem B25427465 : Blo 2201435 25427465 := bstep (se 2 (by rfl) ⟨9535299, by rfl⟩ : syracuseStep 25427465 = 19070599) B19070599
theorem B16951643 : Blo 2201435 16951643 := bstep (se 1 (by rfl) ⟨12713732, by rfl⟩ : syracuseStep 16951643 = 25427465) B25427465
theorem B11301095 : Blo 2201435 11301095 := bstep (se 1 (by rfl) ⟨8475821, by rfl⟩ : syracuseStep 11301095 = 16951643) B16951643
theorem B7534063 : Blo 2201435 7534063 := bstep (se 1 (by rfl) ⟨5650547, by rfl⟩ : syracuseStep 7534063 = 11301095) B11301095
theorem B40181669 : Blo 2201435 40181669 := bstep (se 4 (by rfl) ⟨3767031, by rfl⟩ : syracuseStep 40181669 = 7534063) B7534063
theorem B26787779 : Blo 2201435 26787779 := bstep (se 1 (by rfl) ⟨20090834, by rfl⟩ : syracuseStep 26787779 = 40181669) B40181669
theorem B17858519 : Blo 2201435 17858519 := bstep (se 1 (by rfl) ⟨13393889, by rfl⟩ : syracuseStep 17858519 = 26787779) B26787779
theorem B11905679 : Blo 2201435 11905679 := bstep (se 1 (by rfl) ⟨8929259, by rfl⟩ : syracuseStep 11905679 = 17858519) B17858519
theorem B7937119 : Blo 2201435 7937119 := bstep (se 1 (by rfl) ⟨5952839, by rfl⟩ : syracuseStep 7937119 = 11905679) B11905679
theorem B10582825 : Blo 2201435 10582825 := bstep (se 2 (by rfl) ⟨3968559, by rfl⟩ : syracuseStep 10582825 = 7937119) B7937119
theorem B14110433 : Blo 2201435 14110433 := bstep (se 2 (by rfl) ⟨5291412, by rfl⟩ : syracuseStep 14110433 = 10582825) B10582825
theorem B9406955 : Blo 2201435 9406955 := bstep (se 1 (by rfl) ⟨7055216, by rfl⟩ : syracuseStep 9406955 = 14110433) B14110433
theorem B6271303 : Blo 2201435 6271303 := bstep (se 1 (by rfl) ⟨4703477, by rfl⟩ : syracuseStep 6271303 = 9406955) B9406955
theorem B8361737 : Blo 2201435 8361737 := bstep (se 2 (by rfl) ⟨3135651, by rfl⟩ : syracuseStep 8361737 = 6271303) B6271303
theorem B5574491 : Blo 2201435 5574491 := bstep (se 1 (by rfl) ⟨4180868, by rfl⟩ : syracuseStep 5574491 = 8361737) B8361737
theorem B3716327 : Blo 2201435 3716327 := bstep (se 1 (by rfl) ⟨2787245, by rfl⟩ : syracuseStep 3716327 = 5574491) B5574491
theorem B2477551 : Blo 2201435 2477551 := bstep (se 1 (by rfl) ⟨1858163, by rfl⟩ : syracuseStep 2477551 = 3716327) B3716327
theorem B3303401 : Blo 2201435 3303401 := bstep (se 2 (by rfl) ⟨1238775, by rfl⟩ : syracuseStep 3303401 = 2477551) B2477551
theorem B2202267 : Blo 2201435 2202267 := bstep (se 1 (by rfl) ⟨1651700, by rfl⟩ : syracuseStep 2202267 = 3303401) B3303401
theorem B18813941 : Blo 2201435 18813941 := bbase (se 5 (by rfl) ⟨881903, by rfl⟩ : syracuseStep 18813941 = 1763807) (by norm_num)
theorem B12542627 : Blo 2201435 12542627 := bstep (se 1 (by rfl) ⟨9406970, by rfl⟩ : syracuseStep 12542627 = 18813941) B18813941
theorem B8361751 : Blo 2201435 8361751 := bstep (se 1 (by rfl) ⟨6271313, by rfl⟩ : syracuseStep 8361751 = 12542627) B12542627
theorem B11149001 : Blo 2201435 11149001 := bstep (se 2 (by rfl) ⟨4180875, by rfl⟩ : syracuseStep 11149001 = 8361751) B8361751
theorem B7432667 : Blo 2201435 7432667 := bstep (se 1 (by rfl) ⟨5574500, by rfl⟩ : syracuseStep 7432667 = 11149001) B11149001
theorem B4955111 : Blo 2201435 4955111 := bstep (se 1 (by rfl) ⟨3716333, by rfl⟩ : syracuseStep 4955111 = 7432667) B7432667
theorem B3303407 : Blo 2201435 3303407 := bstep (se 1 (by rfl) ⟨2477555, by rfl⟩ : syracuseStep 3303407 = 4955111) B4955111
theorem B2202271 : Blo 2201435 2202271 := bstep (se 1 (by rfl) ⟨1651703, by rfl⟩ : syracuseStep 2202271 = 3303407) B3303407
theorem B3303413 : Blo 2201435 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B2202275 : Blo 2201435 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B15874325 : Blo 2201435 15874325 := bbase (se 6 (by rfl) ⟨372054, by rfl⟩ : syracuseStep 15874325 = 744109) (by norm_num)
theorem B10582883 : Blo 2201435 10582883 := bstep (se 1 (by rfl) ⟨7937162, by rfl⟩ : syracuseStep 10582883 = 15874325) B15874325
theorem B7055255 : Blo 2201435 7055255 := bstep (se 1 (by rfl) ⟨5291441, by rfl⟩ : syracuseStep 7055255 = 10582883) B10582883
theorem B4703503 : Blo 2201435 4703503 := bstep (se 1 (by rfl) ⟨3527627, by rfl⟩ : syracuseStep 4703503 = 7055255) B7055255
theorem B6271337 : Blo 2201435 6271337 := bstep (se 2 (by rfl) ⟨2351751, by rfl⟩ : syracuseStep 6271337 = 4703503) B4703503
theorem B4180891 : Blo 2201435 4180891 := bstep (se 1 (by rfl) ⟨3135668, by rfl⟩ : syracuseStep 4180891 = 6271337) B6271337
theorem B5574521 : Blo 2201435 5574521 := bstep (se 2 (by rfl) ⟨2090445, by rfl⟩ : syracuseStep 5574521 = 4180891) B4180891
theorem B3716347 : Blo 2201435 3716347 := bstep (se 1 (by rfl) ⟨2787260, by rfl⟩ : syracuseStep 3716347 = 5574521) B5574521
theorem B4955129 : Blo 2201435 4955129 := bstep (se 2 (by rfl) ⟨1858173, by rfl⟩ : syracuseStep 4955129 = 3716347) B3716347
theorem B3303419 : Blo 2201435 3303419 := bstep (se 1 (by rfl) ⟨2477564, by rfl⟩ : syracuseStep 3303419 = 4955129) B4955129
theorem B2202279 : Blo 2201435 2202279 := bstep (se 1 (by rfl) ⟨1651709, by rfl⟩ : syracuseStep 2202279 = 3303419) B3303419
theorem B2477569 : Blo 2201435 2477569 := bbase (se 2 (by rfl) ⟨929088, by rfl⟩ : syracuseStep 2477569 = 1858177) (by norm_num)
theorem B3303425 : Blo 2201435 3303425 := bstep (se 2 (by rfl) ⟨1238784, by rfl⟩ : syracuseStep 3303425 = 2477569) B2477569
theorem B2202283 : Blo 2201435 2202283 := bstep (se 1 (by rfl) ⟨1651712, by rfl⟩ : syracuseStep 2202283 = 3303425) B3303425
theorem B5574541 : Blo 2201435 5574541 := bbase (se 3 (by rfl) ⟨1045226, by rfl⟩ : syracuseStep 5574541 = 2090453) (by norm_num)
theorem B7432721 : Blo 2201435 7432721 := bstep (se 2 (by rfl) ⟨2787270, by rfl⟩ : syracuseStep 7432721 = 5574541) B5574541
theorem B4955147 : Blo 2201435 4955147 := bstep (se 1 (by rfl) ⟨3716360, by rfl⟩ : syracuseStep 4955147 = 7432721) B7432721
theorem B3303431 : Blo 2201435 3303431 := bstep (se 1 (by rfl) ⟨2477573, by rfl⟩ : syracuseStep 3303431 = 4955147) B4955147
theorem B2202287 : Blo 2201435 2202287 := bstep (se 1 (by rfl) ⟨1651715, by rfl⟩ : syracuseStep 2202287 = 3303431) B3303431
theorem B3303437 : Blo 2201435 3303437 := bbase (se 3 (by rfl) ⟨619394, by rfl⟩ : syracuseStep 3303437 = 1238789) (by norm_num)
theorem B2202291 : Blo 2201435 2202291 := bstep (se 1 (by rfl) ⟨1651718, by rfl⟩ : syracuseStep 2202291 = 3303437) B3303437
theorem B4955165 : Blo 2201435 4955165 := bbase (se 3 (by rfl) ⟨929093, by rfl⟩ : syracuseStep 4955165 = 1858187) (by norm_num)
theorem B3303443 : Blo 2201435 3303443 := bstep (se 1 (by rfl) ⟨2477582, by rfl⟩ : syracuseStep 3303443 = 4955165) B4955165
theorem B2202295 : Blo 2201435 2202295 := bstep (se 1 (by rfl) ⟨1651721, by rfl⟩ : syracuseStep 2202295 = 3303443) B3303443
theorem B3716381 : Blo 2201435 3716381 := bbase (se 3 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 3716381 = 1393643) (by norm_num)
theorem B2477587 : Blo 2201435 2477587 := bstep (se 1 (by rfl) ⟨1858190, by rfl⟩ : syracuseStep 2477587 = 3716381) B3716381
theorem B3303449 : Blo 2201435 3303449 := bstep (se 2 (by rfl) ⟨1238793, by rfl⟩ : syracuseStep 3303449 = 2477587) B2477587
theorem B2202299 : Blo 2201435 2202299 := bstep (se 1 (by rfl) ⟨1651724, by rfl⟩ : syracuseStep 2202299 = 3303449) B3303449
theorem B2645749 : Blo 2201435 2645749 := bbase (se 5 (by rfl) ⟨124019, by rfl⟩ : syracuseStep 2645749 = 248039) (by norm_num)
theorem B14110661 : Blo 2201435 14110661 := bstep (se 4 (by rfl) ⟨1322874, by rfl⟩ : syracuseStep 14110661 = 2645749) B2645749
theorem B9407107 : Blo 2201435 9407107 := bstep (se 1 (by rfl) ⟨7055330, by rfl⟩ : syracuseStep 9407107 = 14110661) B14110661
theorem B12542809 : Blo 2201435 12542809 := bstep (se 2 (by rfl) ⟨4703553, by rfl⟩ : syracuseStep 12542809 = 9407107) B9407107
theorem B16723745 : Blo 2201435 16723745 := bstep (se 2 (by rfl) ⟨6271404, by rfl⟩ : syracuseStep 16723745 = 12542809) B12542809
theorem B11149163 : Blo 2201435 11149163 := bstep (se 1 (by rfl) ⟨8361872, by rfl⟩ : syracuseStep 11149163 = 16723745) B16723745
theorem B7432775 : Blo 2201435 7432775 := bstep (se 1 (by rfl) ⟨5574581, by rfl⟩ : syracuseStep 7432775 = 11149163) B11149163
theorem B4955183 : Blo 2201435 4955183 := bstep (se 1 (by rfl) ⟨3716387, by rfl⟩ : syracuseStep 4955183 = 7432775) B7432775
theorem B3303455 : Blo 2201435 3303455 := bstep (se 1 (by rfl) ⟨2477591, by rfl⟩ : syracuseStep 3303455 = 4955183) B4955183
theorem B2202303 : Blo 2201435 2202303 := bstep (se 1 (by rfl) ⟨1651727, by rfl⟩ : syracuseStep 2202303 = 3303455) B3303455
theorem B3303461 : Blo 2201435 3303461 := bbase (se 4 (by rfl) ⟨309699, by rfl⟩ : syracuseStep 3303461 = 619399) (by norm_num)
theorem B2202307 : Blo 2201435 2202307 := bstep (se 1 (by rfl) ⟨1651730, by rfl⟩ : syracuseStep 2202307 = 3303461) B3303461
theorem B2787301 : Blo 2201435 2787301 := bbase (se 4 (by rfl) ⟨261309, by rfl⟩ : syracuseStep 2787301 = 522619) (by norm_num)
theorem B3716401 : Blo 2201435 3716401 := bstep (se 2 (by rfl) ⟨1393650, by rfl⟩ : syracuseStep 3716401 = 2787301) B2787301
theorem B4955201 : Blo 2201435 4955201 := bstep (se 2 (by rfl) ⟨1858200, by rfl⟩ : syracuseStep 4955201 = 3716401) B3716401
theorem B3303467 : Blo 2201435 3303467 := bstep (se 1 (by rfl) ⟨2477600, by rfl⟩ : syracuseStep 3303467 = 4955201) B4955201
theorem B2202311 : Blo 2201435 2202311 := bstep (se 1 (by rfl) ⟨1651733, by rfl⟩ : syracuseStep 2202311 = 3303467) B3303467
theorem B2477605 : Blo 2201435 2477605 := bbase (se 4 (by rfl) ⟨232275, by rfl⟩ : syracuseStep 2477605 = 464551) (by norm_num)
theorem B3303473 : Blo 2201435 3303473 := bstep (se 2 (by rfl) ⟨1238802, by rfl⟩ : syracuseStep 3303473 = 2477605) B2477605
theorem B2202315 : Blo 2201435 2202315 := bstep (se 1 (by rfl) ⟨1651736, by rfl⟩ : syracuseStep 2202315 = 3303473) B3303473
theorem B15874613 : Blo 2201435 15874613 := bbase (se 5 (by rfl) ⟨744122, by rfl⟩ : syracuseStep 15874613 = 1488245) (by norm_num)
theorem B10583075 : Blo 2201435 10583075 := bstep (se 1 (by rfl) ⟨7937306, by rfl⟩ : syracuseStep 10583075 = 15874613) B15874613
theorem B7055383 : Blo 2201435 7055383 := bstep (se 1 (by rfl) ⟨5291537, by rfl⟩ : syracuseStep 7055383 = 10583075) B10583075
theorem B9407177 : Blo 2201435 9407177 := bstep (se 2 (by rfl) ⟨3527691, by rfl⟩ : syracuseStep 9407177 = 7055383) B7055383
theorem B6271451 : Blo 2201435 6271451 := bstep (se 1 (by rfl) ⟨4703588, by rfl⟩ : syracuseStep 6271451 = 9407177) B9407177
theorem B4180967 : Blo 2201435 4180967 := bstep (se 1 (by rfl) ⟨3135725, by rfl⟩ : syracuseStep 4180967 = 6271451) B6271451
theorem B2787311 : Blo 2201435 2787311 := bstep (se 1 (by rfl) ⟨2090483, by rfl⟩ : syracuseStep 2787311 = 4180967) B4180967
theorem B7432829 : Blo 2201435 7432829 := bstep (se 3 (by rfl) ⟨1393655, by rfl⟩ : syracuseStep 7432829 = 2787311) B2787311
theorem B4955219 : Blo 2201435 4955219 := bstep (se 1 (by rfl) ⟨3716414, by rfl⟩ : syracuseStep 4955219 = 7432829) B7432829
theorem B3303479 : Blo 2201435 3303479 := bstep (se 1 (by rfl) ⟨2477609, by rfl⟩ : syracuseStep 3303479 = 4955219) B4955219
theorem B2202319 : Blo 2201435 2202319 := bstep (se 1 (by rfl) ⟨1651739, by rfl⟩ : syracuseStep 2202319 = 3303479) B3303479
theorem B3303485 : Blo 2201435 3303485 := bbase (se 3 (by rfl) ⟨619403, by rfl⟩ : syracuseStep 3303485 = 1238807) (by norm_num)
theorem B2202323 : Blo 2201435 2202323 := bstep (se 1 (by rfl) ⟨1651742, by rfl⟩ : syracuseStep 2202323 = 3303485) B3303485
theorem B4955237 : Blo 2201435 4955237 := bbase (se 4 (by rfl) ⟨464553, by rfl⟩ : syracuseStep 4955237 = 929107) (by norm_num)
theorem B3303491 : Blo 2201435 3303491 := bstep (se 1 (by rfl) ⟨2477618, by rfl⟩ : syracuseStep 3303491 = 4955237) B4955237
theorem B2202327 : Blo 2201435 2202327 := bstep (se 1 (by rfl) ⟨1651745, by rfl⟩ : syracuseStep 2202327 = 3303491) B3303491
theorem B5574653 : Blo 2201435 5574653 := bbase (se 3 (by rfl) ⟨1045247, by rfl⟩ : syracuseStep 5574653 = 2090495) (by norm_num)
theorem B3716435 : Blo 2201435 3716435 := bstep (se 1 (by rfl) ⟨2787326, by rfl⟩ : syracuseStep 3716435 = 5574653) B5574653
theorem B2477623 : Blo 2201435 2477623 := bstep (se 1 (by rfl) ⟨1858217, by rfl⟩ : syracuseStep 2477623 = 3716435) B3716435
theorem B3303497 : Blo 2201435 3303497 := bstep (se 2 (by rfl) ⟨1238811, by rfl⟩ : syracuseStep 3303497 = 2477623) B2477623
theorem B2202331 : Blo 2201435 2202331 := bstep (se 1 (by rfl) ⟨1651748, by rfl⟩ : syracuseStep 2202331 = 3303497) B3303497
theorem B4180997 : Blo 2201435 4180997 := bbase (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) (by norm_num)
theorem B11149325 : Blo 2201435 11149325 := bstep (se 3 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 11149325 = 4180997) B4180997
theorem B7432883 : Blo 2201435 7432883 := bstep (se 1 (by rfl) ⟨5574662, by rfl⟩ : syracuseStep 7432883 = 11149325) B11149325
theorem B4955255 : Blo 2201435 4955255 := bstep (se 1 (by rfl) ⟨3716441, by rfl⟩ : syracuseStep 4955255 = 7432883) B7432883
theorem B3303503 : Blo 2201435 3303503 := bstep (se 1 (by rfl) ⟨2477627, by rfl⟩ : syracuseStep 3303503 = 4955255) B4955255
theorem B2202335 : Blo 2201435 2202335 := bstep (se 1 (by rfl) ⟨1651751, by rfl⟩ : syracuseStep 2202335 = 3303503) B3303503
theorem B3303509 : Blo 2201435 3303509 := bbase (se 8 (by rfl) ⟨19356, by rfl⟩ : syracuseStep 3303509 = 38713) (by norm_num)
theorem B2202339 : Blo 2201435 2202339 := bstep (se 1 (by rfl) ⟨1651754, by rfl⟩ : syracuseStep 2202339 = 3303509) B3303509
theorem B2416433 : Blo 2201435 2416433 := bbase (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) (by norm_num)
theorem B6443821 : Blo 2201435 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B8591761 : Blo 2201435 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B11455681 : Blo 2201435 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B15274241 : Blo 2201435 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B10182827 : Blo 2201435 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B6788551 : Blo 2201435 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B9051401 : Blo 2201435 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B6034267 : Blo 2201435 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B8045689 : Blo 2201435 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B10727585 : Blo 2201435 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B7151723 : Blo 2201435 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B4767815 : Blo 2201435 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B3178543 : Blo 2201435 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B4238057 : Blo 2201435 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B2825371 : Blo 2201435 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B15068645 : Blo 2201435 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B10045763 : Blo 2201435 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B6697175 : Blo 2201435 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B17859133 : Blo 2201435 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B23812177 : Blo 2201435 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B31749569 : Blo 2201435 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B21166379 : Blo 2201435 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B14110919 : Blo 2201435 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B9407279 : Blo 2201435 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B6271519 : Blo 2201435 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B8362025 : Blo 2201435 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B5574683 : Blo 2201435 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B3716455 : Blo 2201435 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B4955273 : Blo 2201435 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B3303515 : Blo 2201435 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B2202343 : Blo 2201435 2202343 := bstep (se 1 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 2202343 = 3303515) B3303515
theorem B2477641 : Blo 2201435 2477641 := bbase (se 2 (by rfl) ⟨929115, by rfl⟩ : syracuseStep 2477641 = 1858231) (by norm_num)
theorem B3303521 : Blo 2201435 3303521 := bstep (se 2 (by rfl) ⟨1238820, by rfl⟩ : syracuseStep 3303521 = 2477641) B2477641
theorem B2202347 : Blo 2201435 2202347 := bstep (se 1 (by rfl) ⟨1651760, by rfl⟩ : syracuseStep 2202347 = 3303521) B3303521
theorem B36205717 : Blo 2201435 36205717 := bbase (se 6 (by rfl) ⟨848571, by rfl⟩ : syracuseStep 36205717 = 1697143) (by norm_num)
theorem B48274289 : Blo 2201435 48274289 := bstep (se 2 (by rfl) ⟨18102858, by rfl⟩ : syracuseStep 48274289 = 36205717) B36205717
theorem B32182859 : Blo 2201435 32182859 := bstep (se 1 (by rfl) ⟨24137144, by rfl⟩ : syracuseStep 32182859 = 48274289) B48274289
theorem B85820957 : Blo 2201435 85820957 := bstep (se 3 (by rfl) ⟨16091429, by rfl⟩ : syracuseStep 85820957 = 32182859) B32182859
theorem B57213971 : Blo 2201435 57213971 := bstep (se 1 (by rfl) ⟨42910478, by rfl⟩ : syracuseStep 57213971 = 85820957) B85820957
theorem B38142647 : Blo 2201435 38142647 := bstep (se 1 (by rfl) ⟨28606985, by rfl⟩ : syracuseStep 38142647 = 57213971) B57213971
theorem B25428431 : Blo 2201435 25428431 := bstep (se 1 (by rfl) ⟨19071323, by rfl⟩ : syracuseStep 25428431 = 38142647) B38142647
theorem B16952287 : Blo 2201435 16952287 := bstep (se 1 (by rfl) ⟨12714215, by rfl⟩ : syracuseStep 16952287 = 25428431) B25428431
theorem B22603049 : Blo 2201435 22603049 := bstep (se 2 (by rfl) ⟨8476143, by rfl⟩ : syracuseStep 22603049 = 16952287) B16952287
theorem B15068699 : Blo 2201435 15068699 := bstep (se 1 (by rfl) ⟨11301524, by rfl⟩ : syracuseStep 15068699 = 22603049) B22603049
theorem B10045799 : Blo 2201435 10045799 := bstep (se 1 (by rfl) ⟨7534349, by rfl⟩ : syracuseStep 10045799 = 15068699) B15068699
theorem B6697199 : Blo 2201435 6697199 := bstep (se 1 (by rfl) ⟨5022899, by rfl⟩ : syracuseStep 6697199 = 10045799) B10045799
theorem B17859197 : Blo 2201435 17859197 := bstep (se 3 (by rfl) ⟨3348599, by rfl⟩ : syracuseStep 17859197 = 6697199) B6697199
theorem B11906131 : Blo 2201435 11906131 := bstep (se 1 (by rfl) ⟨8929598, by rfl⟩ : syracuseStep 11906131 = 17859197) B17859197
theorem B15874841 : Blo 2201435 15874841 := bstep (se 2 (by rfl) ⟨5953065, by rfl⟩ : syracuseStep 15874841 = 11906131) B11906131
theorem B10583227 : Blo 2201435 10583227 := bstep (se 1 (by rfl) ⟨7937420, by rfl⟩ : syracuseStep 10583227 = 15874841) B15874841
theorem B14110969 : Blo 2201435 14110969 := bstep (se 2 (by rfl) ⟨5291613, by rfl⟩ : syracuseStep 14110969 = 10583227) B10583227
theorem B18814625 : Blo 2201435 18814625 := bstep (se 2 (by rfl) ⟨7055484, by rfl⟩ : syracuseStep 18814625 = 14110969) B14110969
theorem B12543083 : Blo 2201435 12543083 := bstep (se 1 (by rfl) ⟨9407312, by rfl⟩ : syracuseStep 12543083 = 18814625) B18814625
theorem B8362055 : Blo 2201435 8362055 := bstep (se 1 (by rfl) ⟨6271541, by rfl⟩ : syracuseStep 8362055 = 12543083) B12543083
theorem B5574703 : Blo 2201435 5574703 := bstep (se 1 (by rfl) ⟨4181027, by rfl⟩ : syracuseStep 5574703 = 8362055) B8362055
theorem B7432937 : Blo 2201435 7432937 := bstep (se 2 (by rfl) ⟨2787351, by rfl⟩ : syracuseStep 7432937 = 5574703) B5574703
theorem B4955291 : Blo 2201435 4955291 := bstep (se 1 (by rfl) ⟨3716468, by rfl⟩ : syracuseStep 4955291 = 7432937) B7432937
theorem B3303527 : Blo 2201435 3303527 := bstep (se 1 (by rfl) ⟨2477645, by rfl⟩ : syracuseStep 3303527 = 4955291) B4955291
theorem B2202351 : Blo 2201435 2202351 := bstep (se 1 (by rfl) ⟨1651763, by rfl⟩ : syracuseStep 2202351 = 3303527) B3303527
theorem B3303533 : Blo 2201435 3303533 := bbase (se 3 (by rfl) ⟨619412, by rfl⟩ : syracuseStep 3303533 = 1238825) (by norm_num)
theorem B2202355 : Blo 2201435 2202355 := bstep (se 1 (by rfl) ⟨1651766, by rfl⟩ : syracuseStep 2202355 = 3303533) B3303533
theorem B4955309 : Blo 2201435 4955309 := bbase (se 3 (by rfl) ⟨929120, by rfl⟩ : syracuseStep 4955309 = 1858241) (by norm_num)
theorem B3303539 : Blo 2201435 3303539 := bstep (se 1 (by rfl) ⟨2477654, by rfl⟩ : syracuseStep 3303539 = 4955309) B4955309
theorem B2202359 : Blo 2201435 2202359 := bstep (se 1 (by rfl) ⟨1651769, by rfl⟩ : syracuseStep 2202359 = 3303539) B3303539
theorem B7055525 : Blo 2201435 7055525 := bbase (se 4 (by rfl) ⟨661455, by rfl⟩ : syracuseStep 7055525 = 1322911) (by norm_num)
theorem B4703683 : Blo 2201435 4703683 := bstep (se 1 (by rfl) ⟨3527762, by rfl⟩ : syracuseStep 4703683 = 7055525) B7055525
theorem B6271577 : Blo 2201435 6271577 := bstep (se 2 (by rfl) ⟨2351841, by rfl⟩ : syracuseStep 6271577 = 4703683) B4703683
theorem B4181051 : Blo 2201435 4181051 := bstep (se 1 (by rfl) ⟨3135788, by rfl⟩ : syracuseStep 4181051 = 6271577) B6271577
theorem B2787367 : Blo 2201435 2787367 := bstep (se 1 (by rfl) ⟨2090525, by rfl⟩ : syracuseStep 2787367 = 4181051) B4181051
theorem B3716489 : Blo 2201435 3716489 := bstep (se 2 (by rfl) ⟨1393683, by rfl⟩ : syracuseStep 3716489 = 2787367) B2787367
theorem B2477659 : Blo 2201435 2477659 := bstep (se 1 (by rfl) ⟨1858244, by rfl⟩ : syracuseStep 2477659 = 3716489) B3716489
theorem B3303545 : Blo 2201435 3303545 := bstep (se 2 (by rfl) ⟨1238829, by rfl⟩ : syracuseStep 3303545 = 2477659) B2477659
theorem B2202363 : Blo 2201435 2202363 := bstep (se 1 (by rfl) ⟨1651772, by rfl⟩ : syracuseStep 2202363 = 3303545) B3303545
theorem B22911605 : Blo 2201435 22911605 := bbase (se 5 (by rfl) ⟨1073981, by rfl⟩ : syracuseStep 22911605 = 2147963) (by norm_num)
theorem B15274403 : Blo 2201435 15274403 := bstep (se 1 (by rfl) ⟨11455802, by rfl⟩ : syracuseStep 15274403 = 22911605) B22911605
theorem B10182935 : Blo 2201435 10182935 := bstep (se 1 (by rfl) ⟨7637201, by rfl⟩ : syracuseStep 10182935 = 15274403) B15274403
theorem B6788623 : Blo 2201435 6788623 := bstep (se 1 (by rfl) ⟨5091467, by rfl⟩ : syracuseStep 6788623 = 10182935) B10182935
theorem B9051497 : Blo 2201435 9051497 := bstep (se 2 (by rfl) ⟨3394311, by rfl⟩ : syracuseStep 9051497 = 6788623) B6788623
theorem B6034331 : Blo 2201435 6034331 := bstep (se 1 (by rfl) ⟨4525748, by rfl⟩ : syracuseStep 6034331 = 9051497) B9051497
theorem B4022887 : Blo 2201435 4022887 := bstep (se 1 (by rfl) ⟨3017165, by rfl⟩ : syracuseStep 4022887 = 6034331) B6034331
theorem B5363849 : Blo 2201435 5363849 := bstep (se 2 (by rfl) ⟨2011443, by rfl⟩ : syracuseStep 5363849 = 4022887) B4022887
theorem B3575899 : Blo 2201435 3575899 := bstep (se 1 (by rfl) ⟨2681924, by rfl⟩ : syracuseStep 3575899 = 5363849) B5363849
theorem B4767865 : Blo 2201435 4767865 := bstep (se 2 (by rfl) ⟨1787949, by rfl⟩ : syracuseStep 4767865 = 3575899) B3575899
theorem B25428613 : Blo 2201435 25428613 := bstep (se 4 (by rfl) ⟨2383932, by rfl⟩ : syracuseStep 25428613 = 4767865) B4767865
theorem B33904817 : Blo 2201435 33904817 := bstep (se 2 (by rfl) ⟨12714306, by rfl⟩ : syracuseStep 33904817 = 25428613) B25428613
theorem B22603211 : Blo 2201435 22603211 := bstep (se 1 (by rfl) ⟨16952408, by rfl⟩ : syracuseStep 22603211 = 33904817) B33904817
theorem B15068807 : Blo 2201435 15068807 := bstep (se 1 (by rfl) ⟨11301605, by rfl⟩ : syracuseStep 15068807 = 22603211) B22603211
theorem B10045871 : Blo 2201435 10045871 := bstep (se 1 (by rfl) ⟨7534403, by rfl⟩ : syracuseStep 10045871 = 15068807) B15068807
theorem B6697247 : Blo 2201435 6697247 := bstep (se 1 (by rfl) ⟨5022935, by rfl⟩ : syracuseStep 6697247 = 10045871) B10045871
theorem B17859325 : Blo 2201435 17859325 := bstep (se 3 (by rfl) ⟨3348623, by rfl⟩ : syracuseStep 17859325 = 6697247) B6697247
theorem B23812433 : Blo 2201435 23812433 := bstep (se 2 (by rfl) ⟨8929662, by rfl⟩ : syracuseStep 23812433 = 17859325) B17859325
theorem B15874955 : Blo 2201435 15874955 := bstep (se 1 (by rfl) ⟨11906216, by rfl⟩ : syracuseStep 15874955 = 23812433) B23812433
theorem B10583303 : Blo 2201435 10583303 := bstep (se 1 (by rfl) ⟨7937477, by rfl⟩ : syracuseStep 10583303 = 15874955) B15874955
theorem B28222141 : Blo 2201435 28222141 := bstep (se 3 (by rfl) ⟨5291651, by rfl⟩ : syracuseStep 28222141 = 10583303) B10583303
theorem B37629521 : Blo 2201435 37629521 := bstep (se 2 (by rfl) ⟨14111070, by rfl⟩ : syracuseStep 37629521 = 28222141) B28222141
theorem B25086347 : Blo 2201435 25086347 := bstep (se 1 (by rfl) ⟨18814760, by rfl⟩ : syracuseStep 25086347 = 37629521) B37629521
theorem B16724231 : Blo 2201435 16724231 := bstep (se 1 (by rfl) ⟨12543173, by rfl⟩ : syracuseStep 16724231 = 25086347) B25086347
theorem B11149487 : Blo 2201435 11149487 := bstep (se 1 (by rfl) ⟨8362115, by rfl⟩ : syracuseStep 11149487 = 16724231) B16724231
theorem B7432991 : Blo 2201435 7432991 := bstep (se 1 (by rfl) ⟨5574743, by rfl⟩ : syracuseStep 7432991 = 11149487) B11149487
theorem B4955327 : Blo 2201435 4955327 := bstep (se 1 (by rfl) ⟨3716495, by rfl⟩ : syracuseStep 4955327 = 7432991) B7432991
theorem B3303551 : Blo 2201435 3303551 := bstep (se 1 (by rfl) ⟨2477663, by rfl⟩ : syracuseStep 3303551 = 4955327) B4955327
theorem B2202367 : Blo 2201435 2202367 := bstep (se 1 (by rfl) ⟨1651775, by rfl⟩ : syracuseStep 2202367 = 3303551) B3303551
theorem B3303557 : Blo 2201435 3303557 := bbase (se 4 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 3303557 = 619417) (by norm_num)
theorem B2202371 : Blo 2201435 2202371 := bstep (se 1 (by rfl) ⟨1651778, by rfl⟩ : syracuseStep 2202371 = 3303557) B3303557
theorem B3716509 : Blo 2201435 3716509 := bbase (se 3 (by rfl) ⟨696845, by rfl⟩ : syracuseStep 3716509 = 1393691) (by norm_num)
theorem B4955345 : Blo 2201435 4955345 := bstep (se 2 (by rfl) ⟨1858254, by rfl⟩ : syracuseStep 4955345 = 3716509) B3716509
theorem B3303563 : Blo 2201435 3303563 := bstep (se 1 (by rfl) ⟨2477672, by rfl⟩ : syracuseStep 3303563 = 4955345) B4955345
theorem B2202375 : Blo 2201435 2202375 := bstep (se 1 (by rfl) ⟨1651781, by rfl⟩ : syracuseStep 2202375 = 3303563) B3303563
theorem B2477677 : Blo 2201435 2477677 := bbase (se 3 (by rfl) ⟨464564, by rfl⟩ : syracuseStep 2477677 = 929129) (by norm_num)
theorem B3303569 : Blo 2201435 3303569 := bstep (se 2 (by rfl) ⟨1238838, by rfl⟩ : syracuseStep 3303569 = 2477677) B2477677
theorem B2202379 : Blo 2201435 2202379 := bstep (se 1 (by rfl) ⟨1651784, by rfl⟩ : syracuseStep 2202379 = 3303569) B3303569
theorem B7433045 : Blo 2201435 7433045 := bbase (se 9 (by rfl) ⟨21776, by rfl⟩ : syracuseStep 7433045 = 43553) (by norm_num)
theorem B4955363 : Blo 2201435 4955363 := bstep (se 1 (by rfl) ⟨3716522, by rfl⟩ : syracuseStep 4955363 = 7433045) B7433045
theorem B3303575 : Blo 2201435 3303575 := bstep (se 1 (by rfl) ⟨2477681, by rfl⟩ : syracuseStep 3303575 = 4955363) B4955363
theorem B2202383 : Blo 2201435 2202383 := bstep (se 1 (by rfl) ⟨1651787, by rfl⟩ : syracuseStep 2202383 = 3303575) B3303575
theorem B3303581 : Blo 2201435 3303581 := bbase (se 3 (by rfl) ⟨619421, by rfl⟩ : syracuseStep 3303581 = 1238843) (by norm_num)
theorem B2202387 : Blo 2201435 2202387 := bstep (se 1 (by rfl) ⟨1651790, by rfl⟩ : syracuseStep 2202387 = 3303581) B3303581
theorem B4955381 : Blo 2201435 4955381 := bbase (se 5 (by rfl) ⟨232283, by rfl⟩ : syracuseStep 4955381 = 464567) (by norm_num)
theorem B3303587 : Blo 2201435 3303587 := bstep (se 1 (by rfl) ⟨2477690, by rfl⟩ : syracuseStep 3303587 = 4955381) B4955381
theorem B2202391 : Blo 2201435 2202391 := bstep (se 1 (by rfl) ⟨1651793, by rfl⟩ : syracuseStep 2202391 = 3303587) B3303587
theorem B4525805 : Blo 2201435 4525805 := bbase (se 3 (by rfl) ⟨848588, by rfl⟩ : syracuseStep 4525805 = 1697177) (by norm_num)
theorem B12068813 : Blo 2201435 12068813 := bstep (se 3 (by rfl) ⟨2262902, by rfl⟩ : syracuseStep 12068813 = 4525805) B4525805
theorem B8045875 : Blo 2201435 8045875 := bstep (se 1 (by rfl) ⟨6034406, by rfl⟩ : syracuseStep 8045875 = 12068813) B12068813
theorem B42911333 : Blo 2201435 42911333 := bstep (se 4 (by rfl) ⟨4022937, by rfl⟩ : syracuseStep 42911333 = 8045875) B8045875
theorem B28607555 : Blo 2201435 28607555 := bstep (se 1 (by rfl) ⟨21455666, by rfl⟩ : syracuseStep 28607555 = 42911333) B42911333
theorem B19071703 : Blo 2201435 19071703 := bstep (se 1 (by rfl) ⟨14303777, by rfl⟩ : syracuseStep 19071703 = 28607555) B28607555
theorem B101715749 : Blo 2201435 101715749 := bstep (se 4 (by rfl) ⟨9535851, by rfl⟩ : syracuseStep 101715749 = 19071703) B19071703
theorem B67810499 : Blo 2201435 67810499 := bstep (se 1 (by rfl) ⟨50857874, by rfl⟩ : syracuseStep 67810499 = 101715749) B101715749
theorem B45206999 : Blo 2201435 45206999 := bstep (se 1 (by rfl) ⟨33905249, by rfl⟩ : syracuseStep 45206999 = 67810499) B67810499
theorem B30137999 : Blo 2201435 30137999 := bstep (se 1 (by rfl) ⟨22603499, by rfl⟩ : syracuseStep 30137999 = 45206999) B45206999
theorem B80367997 : Blo 2201435 80367997 := bstep (se 3 (by rfl) ⟨15068999, by rfl⟩ : syracuseStep 80367997 = 30137999) B30137999
theorem B107157329 : Blo 2201435 107157329 := bstep (se 2 (by rfl) ⟨40183998, by rfl⟩ : syracuseStep 107157329 = 80367997) B80367997
theorem B71438219 : Blo 2201435 71438219 := bstep (se 1 (by rfl) ⟨53578664, by rfl⟩ : syracuseStep 71438219 = 107157329) B107157329
theorem B47625479 : Blo 2201435 47625479 := bstep (se 1 (by rfl) ⟨35719109, by rfl⟩ : syracuseStep 47625479 = 71438219) B71438219
theorem B31750319 : Blo 2201435 31750319 := bstep (se 1 (by rfl) ⟨23812739, by rfl⟩ : syracuseStep 31750319 = 47625479) B47625479
theorem B21166879 : Blo 2201435 21166879 := bstep (se 1 (by rfl) ⟨15875159, by rfl⟩ : syracuseStep 21166879 = 31750319) B31750319
theorem B28222505 : Blo 2201435 28222505 := bstep (se 2 (by rfl) ⟨10583439, by rfl⟩ : syracuseStep 28222505 = 21166879) B21166879
theorem B18815003 : Blo 2201435 18815003 := bstep (se 1 (by rfl) ⟨14111252, by rfl⟩ : syracuseStep 18815003 = 28222505) B28222505
theorem B12543335 : Blo 2201435 12543335 := bstep (se 1 (by rfl) ⟨9407501, by rfl⟩ : syracuseStep 12543335 = 18815003) B18815003
theorem B8362223 : Blo 2201435 8362223 := bstep (se 1 (by rfl) ⟨6271667, by rfl⟩ : syracuseStep 8362223 = 12543335) B12543335
theorem B5574815 : Blo 2201435 5574815 := bstep (se 1 (by rfl) ⟨4181111, by rfl⟩ : syracuseStep 5574815 = 8362223) B8362223
theorem B3716543 : Blo 2201435 3716543 := bstep (se 1 (by rfl) ⟨2787407, by rfl⟩ : syracuseStep 3716543 = 5574815) B5574815
theorem B2477695 : Blo 2201435 2477695 := bstep (se 1 (by rfl) ⟨1858271, by rfl⟩ : syracuseStep 2477695 = 3716543) B3716543
theorem B3303593 : Blo 2201435 3303593 := bstep (se 2 (by rfl) ⟨1238847, by rfl⟩ : syracuseStep 3303593 = 2477695) B2477695
theorem B2202395 : Blo 2201435 2202395 := bstep (se 1 (by rfl) ⟨1651796, by rfl⟩ : syracuseStep 2202395 = 3303593) B3303593
theorem B15875189 : Blo 2201435 15875189 := bbase (se 5 (by rfl) ⟨744149, by rfl⟩ : syracuseStep 15875189 = 1488299) (by norm_num)
theorem B10583459 : Blo 2201435 10583459 := bstep (se 1 (by rfl) ⟨7937594, by rfl⟩ : syracuseStep 10583459 = 15875189) B15875189
theorem B7055639 : Blo 2201435 7055639 := bstep (se 1 (by rfl) ⟨5291729, by rfl⟩ : syracuseStep 7055639 = 10583459) B10583459
theorem B4703759 : Blo 2201435 4703759 := bstep (se 1 (by rfl) ⟨3527819, by rfl⟩ : syracuseStep 4703759 = 7055639) B7055639
theorem B3135839 : Blo 2201435 3135839 := bstep (se 1 (by rfl) ⟨2351879, by rfl⟩ : syracuseStep 3135839 = 4703759) B4703759
theorem B8362237 : Blo 2201435 8362237 := bstep (se 3 (by rfl) ⟨1567919, by rfl⟩ : syracuseStep 8362237 = 3135839) B3135839
theorem B11149649 : Blo 2201435 11149649 := bstep (se 2 (by rfl) ⟨4181118, by rfl⟩ : syracuseStep 11149649 = 8362237) B8362237
theorem B7433099 : Blo 2201435 7433099 := bstep (se 1 (by rfl) ⟨5574824, by rfl⟩ : syracuseStep 7433099 = 11149649) B11149649
theorem B4955399 : Blo 2201435 4955399 := bstep (se 1 (by rfl) ⟨3716549, by rfl⟩ : syracuseStep 4955399 = 7433099) B7433099
theorem B3303599 : Blo 2201435 3303599 := bstep (se 1 (by rfl) ⟨2477699, by rfl⟩ : syracuseStep 3303599 = 4955399) B4955399
theorem B2202399 : Blo 2201435 2202399 := bstep (se 1 (by rfl) ⟨1651799, by rfl⟩ : syracuseStep 2202399 = 3303599) B3303599
theorem B3303605 : Blo 2201435 3303605 := bbase (se 5 (by rfl) ⟨154856, by rfl⟩ : syracuseStep 3303605 = 309713) (by norm_num)
theorem B2202403 : Blo 2201435 2202403 := bstep (se 1 (by rfl) ⟨1651802, by rfl⟩ : syracuseStep 2202403 = 3303605) B3303605
theorem B5574845 : Blo 2201435 5574845 := bbase (se 3 (by rfl) ⟨1045283, by rfl⟩ : syracuseStep 5574845 = 2090567) (by norm_num)
theorem B3716563 : Blo 2201435 3716563 := bstep (se 1 (by rfl) ⟨2787422, by rfl⟩ : syracuseStep 3716563 = 5574845) B5574845
theorem B4955417 : Blo 2201435 4955417 := bstep (se 2 (by rfl) ⟨1858281, by rfl⟩ : syracuseStep 4955417 = 3716563) B3716563
theorem B3303611 : Blo 2201435 3303611 := bstep (se 1 (by rfl) ⟨2477708, by rfl⟩ : syracuseStep 3303611 = 4955417) B4955417
theorem B2202407 : Blo 2201435 2202407 := bstep (se 1 (by rfl) ⟨1651805, by rfl⟩ : syracuseStep 2202407 = 3303611) B3303611
theorem B2477713 : Blo 2201435 2477713 := bbase (se 2 (by rfl) ⟨929142, by rfl⟩ : syracuseStep 2477713 = 1858285) (by norm_num)
theorem B3303617 : Blo 2201435 3303617 := bstep (se 2 (by rfl) ⟨1238856, by rfl⟩ : syracuseStep 3303617 = 2477713) B2477713
theorem B2202411 : Blo 2201435 2202411 := bstep (se 1 (by rfl) ⟨1651808, by rfl⟩ : syracuseStep 2202411 = 3303617) B3303617
theorem B4181149 : Blo 2201435 4181149 := bbase (se 3 (by rfl) ⟨783965, by rfl⟩ : syracuseStep 4181149 = 1567931) (by norm_num)
theorem B5574865 : Blo 2201435 5574865 := bstep (se 2 (by rfl) ⟨2090574, by rfl⟩ : syracuseStep 5574865 = 4181149) B4181149
theorem B7433153 : Blo 2201435 7433153 := bstep (se 2 (by rfl) ⟨2787432, by rfl⟩ : syracuseStep 7433153 = 5574865) B5574865
theorem B4955435 : Blo 2201435 4955435 := bstep (se 1 (by rfl) ⟨3716576, by rfl⟩ : syracuseStep 4955435 = 7433153) B7433153
theorem B3303623 : Blo 2201435 3303623 := bstep (se 1 (by rfl) ⟨2477717, by rfl⟩ : syracuseStep 3303623 = 4955435) B4955435
theorem B2202415 : Blo 2201435 2202415 := bstep (se 1 (by rfl) ⟨1651811, by rfl⟩ : syracuseStep 2202415 = 3303623) B3303623
theorem B3303629 : Blo 2201435 3303629 := bbase (se 3 (by rfl) ⟨619430, by rfl⟩ : syracuseStep 3303629 = 1238861) (by norm_num)
theorem B2202419 : Blo 2201435 2202419 := bstep (se 1 (by rfl) ⟨1651814, by rfl⟩ : syracuseStep 2202419 = 3303629) B3303629
theorem B4955453 : Blo 2201435 4955453 := bbase (se 3 (by rfl) ⟨929147, by rfl⟩ : syracuseStep 4955453 = 1858295) (by norm_num)
theorem B3303635 : Blo 2201435 3303635 := bstep (se 1 (by rfl) ⟨2477726, by rfl⟩ : syracuseStep 3303635 = 4955453) B4955453
theorem B2202423 : Blo 2201435 2202423 := bstep (se 1 (by rfl) ⟨1651817, by rfl⟩ : syracuseStep 2202423 = 3303635) B3303635
theorem B3716597 : Blo 2201435 3716597 := bbase (se 5 (by rfl) ⟨174215, by rfl⟩ : syracuseStep 3716597 = 348431) (by norm_num)
theorem B2477731 : Blo 2201435 2477731 := bstep (se 1 (by rfl) ⟨1858298, by rfl⟩ : syracuseStep 2477731 = 3716597) B3716597
theorem B3303641 : Blo 2201435 3303641 := bstep (se 2 (by rfl) ⟨1238865, by rfl⟩ : syracuseStep 3303641 = 2477731) B2477731
theorem B2202427 : Blo 2201435 2202427 := bstep (se 1 (by rfl) ⟨1651820, by rfl⟩ : syracuseStep 2202427 = 3303641) B3303641
theorem B8929925 : Blo 2201435 8929925 := bbase (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) (by norm_num)
theorem B5953283 : Blo 2201435 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B3968855 : Blo 2201435 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B2645903 : Blo 2201435 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B7055741 : Blo 2201435 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B4703827 : Blo 2201435 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B6271769 : Blo 2201435 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B16724717 : Blo 2201435 16724717 := bstep (se 3 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 16724717 = 6271769) B6271769
theorem B11149811 : Blo 2201435 11149811 := bstep (se 1 (by rfl) ⟨8362358, by rfl⟩ : syracuseStep 11149811 = 16724717) B16724717
theorem B7433207 : Blo 2201435 7433207 := bstep (se 1 (by rfl) ⟨5574905, by rfl⟩ : syracuseStep 7433207 = 11149811) B11149811
theorem B4955471 : Blo 2201435 4955471 := bstep (se 1 (by rfl) ⟨3716603, by rfl⟩ : syracuseStep 4955471 = 7433207) B7433207
theorem B3303647 : Blo 2201435 3303647 := bstep (se 1 (by rfl) ⟨2477735, by rfl⟩ : syracuseStep 3303647 = 4955471) B4955471
theorem B2202431 : Blo 2201435 2202431 := bstep (se 1 (by rfl) ⟨1651823, by rfl⟩ : syracuseStep 2202431 = 3303647) B3303647
theorem B3303653 : Blo 2201435 3303653 := bbase (se 4 (by rfl) ⟨309717, by rfl⟩ : syracuseStep 3303653 = 619435) (by norm_num)
theorem B2202435 : Blo 2201435 2202435 := bstep (se 1 (by rfl) ⟨1651826, by rfl⟩ : syracuseStep 2202435 = 3303653) B3303653
theorem B4703845 : Blo 2201435 4703845 := bbase (se 4 (by rfl) ⟨440985, by rfl⟩ : syracuseStep 4703845 = 881971) (by norm_num)
theorem B6271793 : Blo 2201435 6271793 := bstep (se 2 (by rfl) ⟨2351922, by rfl⟩ : syracuseStep 6271793 = 4703845) B4703845
theorem B4181195 : Blo 2201435 4181195 := bstep (se 1 (by rfl) ⟨3135896, by rfl⟩ : syracuseStep 4181195 = 6271793) B6271793
theorem B2787463 : Blo 2201435 2787463 := bstep (se 1 (by rfl) ⟨2090597, by rfl⟩ : syracuseStep 2787463 = 4181195) B4181195
theorem B3716617 : Blo 2201435 3716617 := bstep (se 2 (by rfl) ⟨1393731, by rfl⟩ : syracuseStep 3716617 = 2787463) B2787463
theorem B4955489 : Blo 2201435 4955489 := bstep (se 2 (by rfl) ⟨1858308, by rfl⟩ : syracuseStep 4955489 = 3716617) B3716617
theorem B3303659 : Blo 2201435 3303659 := bstep (se 1 (by rfl) ⟨2477744, by rfl⟩ : syracuseStep 3303659 = 4955489) B4955489
theorem B2202439 : Blo 2201435 2202439 := bstep (se 1 (by rfl) ⟨1651829, by rfl⟩ : syracuseStep 2202439 = 3303659) B3303659
theorem B2477749 : Blo 2201435 2477749 := bbase (se 5 (by rfl) ⟨116144, by rfl⟩ : syracuseStep 2477749 = 232289) (by norm_num)
theorem B3303665 : Blo 2201435 3303665 := bstep (se 2 (by rfl) ⟨1238874, by rfl⟩ : syracuseStep 3303665 = 2477749) B2477749
theorem B2202443 : Blo 2201435 2202443 := bstep (se 1 (by rfl) ⟨1651832, by rfl⟩ : syracuseStep 2202443 = 3303665) B3303665
theorem B2787473 : Blo 2201435 2787473 := bbase (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) (by norm_num)
theorem B7433261 : Blo 2201435 7433261 := bstep (se 3 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 7433261 = 2787473) B2787473
theorem B4955507 : Blo 2201435 4955507 := bstep (se 1 (by rfl) ⟨3716630, by rfl⟩ : syracuseStep 4955507 = 7433261) B7433261
theorem B3303671 : Blo 2201435 3303671 := bstep (se 1 (by rfl) ⟨2477753, by rfl⟩ : syracuseStep 3303671 = 4955507) B4955507
theorem B2202447 : Blo 2201435 2202447 := bstep (se 1 (by rfl) ⟨1651835, by rfl⟩ : syracuseStep 2202447 = 3303671) B3303671
theorem B3303677 : Blo 2201435 3303677 := bbase (se 3 (by rfl) ⟨619439, by rfl⟩ : syracuseStep 3303677 = 1238879) (by norm_num)
theorem B2202451 : Blo 2201435 2202451 := bstep (se 1 (by rfl) ⟨1651838, by rfl⟩ : syracuseStep 2202451 = 3303677) B3303677
theorem B4955525 : Blo 2201435 4955525 := bbase (se 4 (by rfl) ⟨464580, by rfl⟩ : syracuseStep 4955525 = 929161) (by norm_num)
theorem B3303683 : Blo 2201435 3303683 := bstep (se 1 (by rfl) ⟨2477762, by rfl⟩ : syracuseStep 3303683 = 4955525) B4955525
theorem B2202455 : Blo 2201435 2202455 := bstep (se 1 (by rfl) ⟨1651841, by rfl⟩ : syracuseStep 2202455 = 3303683) B3303683
theorem B3135925 : Blo 2201435 3135925 := bbase (se 5 (by rfl) ⟨146996, by rfl⟩ : syracuseStep 3135925 = 293993) (by norm_num)
theorem B4181233 : Blo 2201435 4181233 := bstep (se 2 (by rfl) ⟨1567962, by rfl⟩ : syracuseStep 4181233 = 3135925) B3135925
theorem B5574977 : Blo 2201435 5574977 := bstep (se 2 (by rfl) ⟨2090616, by rfl⟩ : syracuseStep 5574977 = 4181233) B4181233
theorem B3716651 : Blo 2201435 3716651 := bstep (se 1 (by rfl) ⟨2787488, by rfl⟩ : syracuseStep 3716651 = 5574977) B5574977
theorem B2477767 : Blo 2201435 2477767 := bstep (se 1 (by rfl) ⟨1858325, by rfl⟩ : syracuseStep 2477767 = 3716651) B3716651
theorem B3303689 : Blo 2201435 3303689 := bstep (se 2 (by rfl) ⟨1238883, by rfl⟩ : syracuseStep 3303689 = 2477767) B2477767
theorem B2202459 : Blo 2201435 2202459 := bstep (se 1 (by rfl) ⟨1651844, by rfl⟩ : syracuseStep 2202459 = 3303689) B3303689
theorem B11149973 : Blo 2201435 11149973 := bbase (se 6 (by rfl) ⟨261327, by rfl⟩ : syracuseStep 11149973 = 522655) (by norm_num)
theorem B7433315 : Blo 2201435 7433315 := bstep (se 1 (by rfl) ⟨5574986, by rfl⟩ : syracuseStep 7433315 = 11149973) B11149973
theorem B4955543 : Blo 2201435 4955543 := bstep (se 1 (by rfl) ⟨3716657, by rfl⟩ : syracuseStep 4955543 = 7433315) B7433315
theorem B3303695 : Blo 2201435 3303695 := bstep (se 1 (by rfl) ⟨2477771, by rfl⟩ : syracuseStep 3303695 = 4955543) B4955543
theorem B2202463 : Blo 2201435 2202463 := bstep (se 1 (by rfl) ⟨1651847, by rfl⟩ : syracuseStep 2202463 = 3303695) B3303695
theorem B3303701 : Blo 2201435 3303701 := bbase (se 6 (by rfl) ⟨77430, by rfl⟩ : syracuseStep 3303701 = 154861) (by norm_num)
theorem B2202467 : Blo 2201435 2202467 := bstep (se 1 (by rfl) ⟨1651850, by rfl⟩ : syracuseStep 2202467 = 3303701) B3303701
theorem B6200405 : Blo 2201435 6200405 := bbase (se 8 (by rfl) ⟨36330, by rfl⟩ : syracuseStep 6200405 = 72661) (by norm_num)
theorem B4133603 : Blo 2201435 4133603 := bstep (se 1 (by rfl) ⟨3100202, by rfl⟩ : syracuseStep 4133603 = 6200405) B6200405
theorem B11022941 : Blo 2201435 11022941 := bstep (se 3 (by rfl) ⟨2066801, by rfl⟩ : syracuseStep 11022941 = 4133603) B4133603
theorem B29394509 : Blo 2201435 29394509 := bstep (se 3 (by rfl) ⟨5511470, by rfl⟩ : syracuseStep 29394509 = 11022941) B11022941
theorem B78385357 : Blo 2201435 78385357 := bstep (se 3 (by rfl) ⟨14697254, by rfl⟩ : syracuseStep 78385357 = 29394509) B29394509
theorem B104513809 : Blo 2201435 104513809 := bstep (se 2 (by rfl) ⟨39192678, by rfl⟩ : syracuseStep 104513809 = 78385357) B78385357
theorem B139351745 : Blo 2201435 139351745 := bstep (se 2 (by rfl) ⟨52256904, by rfl⟩ : syracuseStep 139351745 = 104513809) B104513809
theorem B92901163 : Blo 2201435 92901163 := bstep (se 1 (by rfl) ⟨69675872, by rfl⟩ : syracuseStep 92901163 = 139351745) B139351745
theorem B123868217 : Blo 2201435 123868217 := bstep (se 2 (by rfl) ⟨46450581, by rfl⟩ : syracuseStep 123868217 = 92901163) B92901163
theorem B82578811 : Blo 2201435 82578811 := bstep (se 1 (by rfl) ⟨61934108, by rfl⟩ : syracuseStep 82578811 = 123868217) B123868217
theorem B110105081 : Blo 2201435 110105081 := bstep (se 2 (by rfl) ⟨41289405, by rfl⟩ : syracuseStep 110105081 = 82578811) B82578811
theorem B73403387 : Blo 2201435 73403387 := bstep (se 1 (by rfl) ⟨55052540, by rfl⟩ : syracuseStep 73403387 = 110105081) B110105081
theorem B48935591 : Blo 2201435 48935591 := bstep (se 1 (by rfl) ⟨36701693, by rfl⟩ : syracuseStep 48935591 = 73403387) B73403387
theorem B32623727 : Blo 2201435 32623727 := bstep (se 1 (by rfl) ⟨24467795, by rfl⟩ : syracuseStep 32623727 = 48935591) B48935591
theorem B86996605 : Blo 2201435 86996605 := bstep (se 3 (by rfl) ⟨16311863, by rfl⟩ : syracuseStep 86996605 = 32623727) B32623727
theorem B115995473 : Blo 2201435 115995473 := bstep (se 2 (by rfl) ⟨43498302, by rfl⟩ : syracuseStep 115995473 = 86996605) B86996605
theorem B77330315 : Blo 2201435 77330315 := bstep (se 1 (by rfl) ⟨57997736, by rfl⟩ : syracuseStep 77330315 = 115995473) B115995473
theorem B51553543 : Blo 2201435 51553543 := bstep (se 1 (by rfl) ⟨38665157, by rfl⟩ : syracuseStep 51553543 = 77330315) B77330315
theorem B68738057 : Blo 2201435 68738057 := bstep (se 2 (by rfl) ⟨25776771, by rfl⟩ : syracuseStep 68738057 = 51553543) B51553543
theorem B45825371 : Blo 2201435 45825371 := bstep (se 1 (by rfl) ⟨34369028, by rfl⟩ : syracuseStep 45825371 = 68738057) B68738057
theorem B30550247 : Blo 2201435 30550247 := bstep (se 1 (by rfl) ⟨22912685, by rfl⟩ : syracuseStep 30550247 = 45825371) B45825371
theorem B20366831 : Blo 2201435 20366831 := bstep (se 1 (by rfl) ⟨15275123, by rfl⟩ : syracuseStep 20366831 = 30550247) B30550247
theorem B13577887 : Blo 2201435 13577887 := bstep (se 1 (by rfl) ⟨10183415, by rfl⟩ : syracuseStep 13577887 = 20366831) B20366831
theorem B72415397 : Blo 2201435 72415397 := bstep (se 4 (by rfl) ⟨6788943, by rfl⟩ : syracuseStep 72415397 = 13577887) B13577887
theorem B48276931 : Blo 2201435 48276931 := bstep (se 1 (by rfl) ⟨36207698, by rfl⟩ : syracuseStep 48276931 = 72415397) B72415397
theorem B64369241 : Blo 2201435 64369241 := bstep (se 2 (by rfl) ⟨24138465, by rfl⟩ : syracuseStep 64369241 = 48276931) B48276931
theorem B42912827 : Blo 2201435 42912827 := bstep (se 1 (by rfl) ⟨32184620, by rfl⟩ : syracuseStep 42912827 = 64369241) B64369241
theorem B28608551 : Blo 2201435 28608551 := bstep (se 1 (by rfl) ⟨21456413, by rfl⟩ : syracuseStep 28608551 = 42912827) B42912827
theorem B19072367 : Blo 2201435 19072367 := bstep (se 1 (by rfl) ⟨14304275, by rfl⟩ : syracuseStep 19072367 = 28608551) B28608551
theorem B12714911 : Blo 2201435 12714911 := bstep (se 1 (by rfl) ⟨9536183, by rfl⟩ : syracuseStep 12714911 = 19072367) B19072367
theorem B8476607 : Blo 2201435 8476607 := bstep (se 1 (by rfl) ⟨6357455, by rfl⟩ : syracuseStep 8476607 = 12714911) B12714911
theorem B22604285 : Blo 2201435 22604285 := bstep (se 3 (by rfl) ⟨4238303, by rfl⟩ : syracuseStep 22604285 = 8476607) B8476607
theorem B15069523 : Blo 2201435 15069523 := bstep (se 1 (by rfl) ⟨11302142, by rfl⟩ : syracuseStep 15069523 = 22604285) B22604285
theorem B20092697 : Blo 2201435 20092697 := bstep (se 2 (by rfl) ⟨7534761, by rfl⟩ : syracuseStep 20092697 = 15069523) B15069523
theorem B13395131 : Blo 2201435 13395131 := bstep (se 1 (by rfl) ⟨10046348, by rfl⟩ : syracuseStep 13395131 = 20092697) B20092697
theorem B8930087 : Blo 2201435 8930087 := bstep (se 1 (by rfl) ⟨6697565, by rfl⟩ : syracuseStep 8930087 = 13395131) B13395131
theorem B5953391 : Blo 2201435 5953391 := bstep (se 1 (by rfl) ⟨4465043, by rfl⟩ : syracuseStep 5953391 = 8930087) B8930087
theorem B3968927 : Blo 2201435 3968927 := bstep (se 1 (by rfl) ⟨2976695, by rfl⟩ : syracuseStep 3968927 = 5953391) B5953391
theorem B2645951 : Blo 2201435 2645951 := bstep (se 1 (by rfl) ⟨1984463, by rfl⟩ : syracuseStep 2645951 = 3968927) B3968927
theorem B28223477 : Blo 2201435 28223477 := bstep (se 5 (by rfl) ⟨1322975, by rfl⟩ : syracuseStep 28223477 = 2645951) B2645951
theorem B18815651 : Blo 2201435 18815651 := bstep (se 1 (by rfl) ⟨14111738, by rfl⟩ : syracuseStep 18815651 = 28223477) B28223477
theorem B12543767 : Blo 2201435 12543767 := bstep (se 1 (by rfl) ⟨9407825, by rfl⟩ : syracuseStep 12543767 = 18815651) B18815651
theorem B8362511 : Blo 2201435 8362511 := bstep (se 1 (by rfl) ⟨6271883, by rfl⟩ : syracuseStep 8362511 = 12543767) B12543767
theorem B5575007 : Blo 2201435 5575007 := bstep (se 1 (by rfl) ⟨4181255, by rfl⟩ : syracuseStep 5575007 = 8362511) B8362511
theorem B3716671 : Blo 2201435 3716671 := bstep (se 1 (by rfl) ⟨2787503, by rfl⟩ : syracuseStep 3716671 = 5575007) B5575007
theorem B4955561 : Blo 2201435 4955561 := bstep (se 2 (by rfl) ⟨1858335, by rfl⟩ : syracuseStep 4955561 = 3716671) B3716671
theorem B3303707 : Blo 2201435 3303707 := bstep (se 1 (by rfl) ⟨2477780, by rfl⟩ : syracuseStep 3303707 = 4955561) B4955561
theorem B2202471 : Blo 2201435 2202471 := bstep (se 1 (by rfl) ⟨1651853, by rfl⟩ : syracuseStep 2202471 = 3303707) B3303707
theorem B2477785 : Blo 2201435 2477785 := bbase (se 2 (by rfl) ⟨929169, by rfl⟩ : syracuseStep 2477785 = 1858339) (by norm_num)
theorem B3303713 : Blo 2201435 3303713 := bstep (se 2 (by rfl) ⟨1238892, by rfl⟩ : syracuseStep 3303713 = 2477785) B2477785
theorem B2202475 : Blo 2201435 2202475 := bstep (se 1 (by rfl) ⟨1651856, by rfl⟩ : syracuseStep 2202475 = 3303713) B3303713
theorem B2351965 : Blo 2201435 2351965 := bbase (se 3 (by rfl) ⟨440993, by rfl⟩ : syracuseStep 2351965 = 881987) (by norm_num)
theorem B3135953 : Blo 2201435 3135953 := bstep (se 2 (by rfl) ⟨1175982, by rfl⟩ : syracuseStep 3135953 = 2351965) B2351965
theorem B8362541 : Blo 2201435 8362541 := bstep (se 3 (by rfl) ⟨1567976, by rfl⟩ : syracuseStep 8362541 = 3135953) B3135953
theorem B5575027 : Blo 2201435 5575027 := bstep (se 1 (by rfl) ⟨4181270, by rfl⟩ : syracuseStep 5575027 = 8362541) B8362541
theorem B7433369 : Blo 2201435 7433369 := bstep (se 2 (by rfl) ⟨2787513, by rfl⟩ : syracuseStep 7433369 = 5575027) B5575027
theorem B4955579 : Blo 2201435 4955579 := bstep (se 1 (by rfl) ⟨3716684, by rfl⟩ : syracuseStep 4955579 = 7433369) B7433369
theorem B3303719 : Blo 2201435 3303719 := bstep (se 1 (by rfl) ⟨2477789, by rfl⟩ : syracuseStep 3303719 = 4955579) B4955579
theorem B2202479 : Blo 2201435 2202479 := bstep (se 1 (by rfl) ⟨1651859, by rfl⟩ : syracuseStep 2202479 = 3303719) B3303719
theorem B3303725 : Blo 2201435 3303725 := bbase (se 3 (by rfl) ⟨619448, by rfl⟩ : syracuseStep 3303725 = 1238897) (by norm_num)
theorem B2202483 : Blo 2201435 2202483 := bstep (se 1 (by rfl) ⟨1651862, by rfl⟩ : syracuseStep 2202483 = 3303725) B3303725
theorem B4955597 : Blo 2201435 4955597 := bbase (se 3 (by rfl) ⟨929174, by rfl⟩ : syracuseStep 4955597 = 1858349) (by norm_num)
theorem B3303731 : Blo 2201435 3303731 := bstep (se 1 (by rfl) ⟨2477798, by rfl⟩ : syracuseStep 3303731 = 4955597) B4955597
theorem B2202487 : Blo 2201435 2202487 := bstep (se 1 (by rfl) ⟨1651865, by rfl⟩ : syracuseStep 2202487 = 3303731) B3303731
theorem B2787529 : Blo 2201435 2787529 := bbase (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) (by norm_num)
theorem B3716705 : Blo 2201435 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B2477803 : Blo 2201435 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B3303737 : Blo 2201435 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B2202491 : Blo 2201435 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B6697637 : Blo 2201435 6697637 := bbase (se 4 (by rfl) ⟨627903, by rfl⟩ : syracuseStep 6697637 = 1255807) (by norm_num)
theorem B4465091 : Blo 2201435 4465091 := bstep (se 1 (by rfl) ⟨3348818, by rfl⟩ : syracuseStep 4465091 = 6697637) B6697637
theorem B11906909 : Blo 2201435 11906909 := bstep (se 3 (by rfl) ⟨2232545, by rfl⟩ : syracuseStep 11906909 = 4465091) B4465091
theorem B7937939 : Blo 2201435 7937939 := bstep (se 1 (by rfl) ⟨5953454, by rfl⟩ : syracuseStep 7937939 = 11906909) B11906909
theorem B21167837 : Blo 2201435 21167837 := bstep (se 3 (by rfl) ⟨3968969, by rfl⟩ : syracuseStep 21167837 = 7937939) B7937939
theorem B14111891 : Blo 2201435 14111891 := bstep (se 1 (by rfl) ⟨10583918, by rfl⟩ : syracuseStep 14111891 = 21167837) B21167837
theorem B9407927 : Blo 2201435 9407927 := bstep (se 1 (by rfl) ⟨7055945, by rfl⟩ : syracuseStep 9407927 = 14111891) B14111891
theorem B25087805 : Blo 2201435 25087805 := bstep (se 3 (by rfl) ⟨4703963, by rfl⟩ : syracuseStep 25087805 = 9407927) B9407927
theorem B16725203 : Blo 2201435 16725203 := bstep (se 1 (by rfl) ⟨12543902, by rfl⟩ : syracuseStep 16725203 = 25087805) B25087805
theorem B11150135 : Blo 2201435 11150135 := bstep (se 1 (by rfl) ⟨8362601, by rfl⟩ : syracuseStep 11150135 = 16725203) B16725203
theorem B7433423 : Blo 2201435 7433423 := bstep (se 1 (by rfl) ⟨5575067, by rfl⟩ : syracuseStep 7433423 = 11150135) B11150135
theorem B4955615 : Blo 2201435 4955615 := bstep (se 1 (by rfl) ⟨3716711, by rfl⟩ : syracuseStep 4955615 = 7433423) B7433423
theorem B3303743 : Blo 2201435 3303743 := bstep (se 1 (by rfl) ⟨2477807, by rfl⟩ : syracuseStep 3303743 = 4955615) B4955615
theorem B2202495 : Blo 2201435 2202495 := bstep (se 1 (by rfl) ⟨1651871, by rfl⟩ : syracuseStep 2202495 = 3303743) B3303743
theorem B3303749 : Blo 2201435 3303749 := bbase (se 4 (by rfl) ⟨309726, by rfl⟩ : syracuseStep 3303749 = 619453) (by norm_num)
theorem B2202499 : Blo 2201435 2202499 := bstep (se 1 (by rfl) ⟨1651874, by rfl⟩ : syracuseStep 2202499 = 3303749) B3303749
theorem B3716725 : Blo 2201435 3716725 := bbase (se 5 (by rfl) ⟨174221, by rfl⟩ : syracuseStep 3716725 = 348443) (by norm_num)
theorem B4955633 : Blo 2201435 4955633 := bstep (se 2 (by rfl) ⟨1858362, by rfl⟩ : syracuseStep 4955633 = 3716725) B3716725
theorem B3303755 : Blo 2201435 3303755 := bstep (se 1 (by rfl) ⟨2477816, by rfl⟩ : syracuseStep 3303755 = 4955633) B4955633
theorem B2202503 : Blo 2201435 2202503 := bstep (se 1 (by rfl) ⟨1651877, by rfl⟩ : syracuseStep 2202503 = 3303755) B3303755
theorem B2477821 : Blo 2201435 2477821 := bbase (se 3 (by rfl) ⟨464591, by rfl⟩ : syracuseStep 2477821 = 929183) (by norm_num)
theorem B3303761 : Blo 2201435 3303761 := bstep (se 2 (by rfl) ⟨1238910, by rfl⟩ : syracuseStep 3303761 = 2477821) B2477821
theorem B2202507 : Blo 2201435 2202507 := bstep (se 1 (by rfl) ⟨1651880, by rfl⟩ : syracuseStep 2202507 = 3303761) B3303761
theorem B7433477 : Blo 2201435 7433477 := bbase (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) (by norm_num)
theorem B4955651 : Blo 2201435 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B3303767 : Blo 2201435 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B2202511 : Blo 2201435 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B3303773 : Blo 2201435 3303773 := bbase (se 3 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 3303773 = 1238915) (by norm_num)
theorem B2202515 : Blo 2201435 2202515 := bstep (se 1 (by rfl) ⟨1651886, by rfl⟩ : syracuseStep 2202515 = 3303773) B3303773
theorem B4955669 : Blo 2201435 4955669 := bbase (se 6 (by rfl) ⟨116148, by rfl⟩ : syracuseStep 4955669 = 232297) (by norm_num)
theorem B3303779 : Blo 2201435 3303779 := bstep (se 1 (by rfl) ⟨2477834, by rfl⟩ : syracuseStep 3303779 = 4955669) B4955669
theorem B2202519 : Blo 2201435 2202519 := bstep (se 1 (by rfl) ⟨1651889, by rfl⟩ : syracuseStep 2202519 = 3303779) B3303779
theorem B8362709 : Blo 2201435 8362709 := bbase (se 7 (by rfl) ⟨98000, by rfl⟩ : syracuseStep 8362709 = 196001) (by norm_num)
theorem B5575139 : Blo 2201435 5575139 := bstep (se 1 (by rfl) ⟨4181354, by rfl⟩ : syracuseStep 5575139 = 8362709) B8362709
theorem B3716759 : Blo 2201435 3716759 := bstep (se 1 (by rfl) ⟨2787569, by rfl⟩ : syracuseStep 3716759 = 5575139) B5575139
theorem B2477839 : Blo 2201435 2477839 := bstep (se 1 (by rfl) ⟨1858379, by rfl⟩ : syracuseStep 2477839 = 3716759) B3716759
theorem B3303785 : Blo 2201435 3303785 := bstep (se 2 (by rfl) ⟨1238919, by rfl⟩ : syracuseStep 3303785 = 2477839) B2477839
theorem B2202523 : Blo 2201435 2202523 := bstep (se 1 (by rfl) ⟨1651892, by rfl⟩ : syracuseStep 2202523 = 3303785) B3303785
theorem B12544085 : Blo 2201435 12544085 := bbase (se 8 (by rfl) ⟨73500, by rfl⟩ : syracuseStep 12544085 = 147001) (by norm_num)
theorem B8362723 : Blo 2201435 8362723 := bstep (se 1 (by rfl) ⟨6272042, by rfl⟩ : syracuseStep 8362723 = 12544085) B12544085
theorem B11150297 : Blo 2201435 11150297 := bstep (se 2 (by rfl) ⟨4181361, by rfl⟩ : syracuseStep 11150297 = 8362723) B8362723
theorem B7433531 : Blo 2201435 7433531 := bstep (se 1 (by rfl) ⟨5575148, by rfl⟩ : syracuseStep 7433531 = 11150297) B11150297
theorem B4955687 : Blo 2201435 4955687 := bstep (se 1 (by rfl) ⟨3716765, by rfl⟩ : syracuseStep 4955687 = 7433531) B7433531
theorem B3303791 : Blo 2201435 3303791 := bstep (se 1 (by rfl) ⟨2477843, by rfl⟩ : syracuseStep 3303791 = 4955687) B4955687
theorem B2202527 : Blo 2201435 2202527 := bstep (se 1 (by rfl) ⟨1651895, by rfl⟩ : syracuseStep 2202527 = 3303791) B3303791
theorem B3303797 : Blo 2201435 3303797 := bbase (se 5 (by rfl) ⟨154865, by rfl⟩ : syracuseStep 3303797 = 309731) (by norm_num)
theorem B2202531 : Blo 2201435 2202531 := bstep (se 1 (by rfl) ⟨1651898, by rfl⟩ : syracuseStep 2202531 = 3303797) B3303797
theorem B2352025 : Blo 2201435 2352025 := bbase (se 2 (by rfl) ⟨882009, by rfl⟩ : syracuseStep 2352025 = 1764019) (by norm_num)
theorem B3136033 : Blo 2201435 3136033 := bstep (se 2 (by rfl) ⟨1176012, by rfl⟩ : syracuseStep 3136033 = 2352025) B2352025
theorem B4181377 : Blo 2201435 4181377 := bstep (se 2 (by rfl) ⟨1568016, by rfl⟩ : syracuseStep 4181377 = 3136033) B3136033
theorem B5575169 : Blo 2201435 5575169 := bstep (se 2 (by rfl) ⟨2090688, by rfl⟩ : syracuseStep 5575169 = 4181377) B4181377
theorem B3716779 : Blo 2201435 3716779 := bstep (se 1 (by rfl) ⟨2787584, by rfl⟩ : syracuseStep 3716779 = 5575169) B5575169
theorem B4955705 : Blo 2201435 4955705 := bstep (se 2 (by rfl) ⟨1858389, by rfl⟩ : syracuseStep 4955705 = 3716779) B3716779
theorem B3303803 : Blo 2201435 3303803 := bstep (se 1 (by rfl) ⟨2477852, by rfl⟩ : syracuseStep 3303803 = 4955705) B4955705
theorem B2202535 : Blo 2201435 2202535 := bstep (se 1 (by rfl) ⟨1651901, by rfl⟩ : syracuseStep 2202535 = 3303803) B3303803
theorem B2477857 : Blo 2201435 2477857 := bbase (se 2 (by rfl) ⟨929196, by rfl⟩ : syracuseStep 2477857 = 1858393) (by norm_num)
theorem B3303809 : Blo 2201435 3303809 := bstep (se 2 (by rfl) ⟨1238928, by rfl⟩ : syracuseStep 3303809 = 2477857) B2477857
theorem B2202539 : Blo 2201435 2202539 := bstep (se 1 (by rfl) ⟨1651904, by rfl⟩ : syracuseStep 2202539 = 3303809) B3303809
theorem B5575189 : Blo 2201435 5575189 := bbase (se 6 (by rfl) ⟨130668, by rfl⟩ : syracuseStep 5575189 = 261337) (by norm_num)
theorem B7433585 : Blo 2201435 7433585 := bstep (se 2 (by rfl) ⟨2787594, by rfl⟩ : syracuseStep 7433585 = 5575189) B5575189
theorem B4955723 : Blo 2201435 4955723 := bstep (se 1 (by rfl) ⟨3716792, by rfl⟩ : syracuseStep 4955723 = 7433585) B7433585
theorem B3303815 : Blo 2201435 3303815 := bstep (se 1 (by rfl) ⟨2477861, by rfl⟩ : syracuseStep 3303815 = 4955723) B4955723
theorem B2202543 : Blo 2201435 2202543 := bstep (se 1 (by rfl) ⟨1651907, by rfl⟩ : syracuseStep 2202543 = 3303815) B3303815
theorem B3303821 : Blo 2201435 3303821 := bbase (se 3 (by rfl) ⟨619466, by rfl⟩ : syracuseStep 3303821 = 1238933) (by norm_num)
theorem B2202547 : Blo 2201435 2202547 := bstep (se 1 (by rfl) ⟨1651910, by rfl⟩ : syracuseStep 2202547 = 3303821) B3303821
theorem B4955741 : Blo 2201435 4955741 := bbase (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) (by norm_num)
theorem B3303827 : Blo 2201435 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B2202551 : Blo 2201435 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B3716813 : Blo 2201435 3716813 := bbase (se 3 (by rfl) ⟨696902, by rfl⟩ : syracuseStep 3716813 = 1393805) (by norm_num)
theorem B2477875 : Blo 2201435 2477875 := bstep (se 1 (by rfl) ⟨1858406, by rfl⟩ : syracuseStep 2477875 = 3716813) B3716813
theorem B3303833 : Blo 2201435 3303833 := bstep (se 2 (by rfl) ⟨1238937, by rfl⟩ : syracuseStep 3303833 = 2477875) B2477875
theorem B2202555 : Blo 2201435 2202555 := bstep (se 1 (by rfl) ⟨1651916, by rfl⟩ : syracuseStep 2202555 = 3303833) B3303833
theorem B3969085 : Blo 2201435 3969085 := bbase (se 3 (by rfl) ⟨744203, by rfl⟩ : syracuseStep 3969085 = 1488407) (by norm_num)
theorem B5292113 : Blo 2201435 5292113 := bstep (se 2 (by rfl) ⟨1984542, by rfl⟩ : syracuseStep 5292113 = 3969085) B3969085
theorem B14112301 : Blo 2201435 14112301 := bstep (se 3 (by rfl) ⟨2646056, by rfl⟩ : syracuseStep 14112301 = 5292113) B5292113
theorem B18816401 : Blo 2201435 18816401 := bstep (se 2 (by rfl) ⟨7056150, by rfl⟩ : syracuseStep 18816401 = 14112301) B14112301
theorem B12544267 : Blo 2201435 12544267 := bstep (se 1 (by rfl) ⟨9408200, by rfl⟩ : syracuseStep 12544267 = 18816401) B18816401
theorem B16725689 : Blo 2201435 16725689 := bstep (se 2 (by rfl) ⟨6272133, by rfl⟩ : syracuseStep 16725689 = 12544267) B12544267
theorem B11150459 : Blo 2201435 11150459 := bstep (se 1 (by rfl) ⟨8362844, by rfl⟩ : syracuseStep 11150459 = 16725689) B16725689
theorem B7433639 : Blo 2201435 7433639 := bstep (se 1 (by rfl) ⟨5575229, by rfl⟩ : syracuseStep 7433639 = 11150459) B11150459
theorem B4955759 : Blo 2201435 4955759 := bstep (se 1 (by rfl) ⟨3716819, by rfl⟩ : syracuseStep 4955759 = 7433639) B7433639
theorem B3303839 : Blo 2201435 3303839 := bstep (se 1 (by rfl) ⟨2477879, by rfl⟩ : syracuseStep 3303839 = 4955759) B4955759
theorem B2202559 : Blo 2201435 2202559 := bstep (se 1 (by rfl) ⟨1651919, by rfl⟩ : syracuseStep 2202559 = 3303839) B3303839
theorem B3303845 : Blo 2201435 3303845 := bbase (se 4 (by rfl) ⟨309735, by rfl⟩ : syracuseStep 3303845 = 619471) (by norm_num)
theorem B2202563 : Blo 2201435 2202563 := bstep (se 1 (by rfl) ⟨1651922, by rfl⟩ : syracuseStep 2202563 = 3303845) B3303845
theorem B2787625 : Blo 2201435 2787625 := bbase (se 2 (by rfl) ⟨1045359, by rfl⟩ : syracuseStep 2787625 = 2090719) (by norm_num)
theorem B3716833 : Blo 2201435 3716833 := bstep (se 2 (by rfl) ⟨1393812, by rfl⟩ : syracuseStep 3716833 = 2787625) B2787625
theorem B4955777 : Blo 2201435 4955777 := bstep (se 2 (by rfl) ⟨1858416, by rfl⟩ : syracuseStep 4955777 = 3716833) B3716833
theorem B3303851 : Blo 2201435 3303851 := bstep (se 1 (by rfl) ⟨2477888, by rfl⟩ : syracuseStep 3303851 = 4955777) B4955777
theorem B2202567 : Blo 2201435 2202567 := bstep (se 1 (by rfl) ⟨1651925, by rfl⟩ : syracuseStep 2202567 = 3303851) B3303851
theorem B2477893 : Blo 2201435 2477893 := bbase (se 4 (by rfl) ⟨232302, by rfl⟩ : syracuseStep 2477893 = 464605) (by norm_num)
theorem B3303857 : Blo 2201435 3303857 := bstep (se 2 (by rfl) ⟨1238946, by rfl⟩ : syracuseStep 3303857 = 2477893) B2477893
theorem B2202571 : Blo 2201435 2202571 := bstep (se 1 (by rfl) ⟨1651928, by rfl⟩ : syracuseStep 2202571 = 3303857) B3303857
theorem B4181453 : Blo 2201435 4181453 := bbase (se 3 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 4181453 = 1568045) (by norm_num)
theorem B2787635 : Blo 2201435 2787635 := bstep (se 1 (by rfl) ⟨2090726, by rfl⟩ : syracuseStep 2787635 = 4181453) B4181453
theorem B7433693 : Blo 2201435 7433693 := bstep (se 3 (by rfl) ⟨1393817, by rfl⟩ : syracuseStep 7433693 = 2787635) B2787635
theorem B4955795 : Blo 2201435 4955795 := bstep (se 1 (by rfl) ⟨3716846, by rfl⟩ : syracuseStep 4955795 = 7433693) B7433693
theorem B3303863 : Blo 2201435 3303863 := bstep (se 1 (by rfl) ⟨2477897, by rfl⟩ : syracuseStep 3303863 = 4955795) B4955795
theorem B2202575 : Blo 2201435 2202575 := bstep (se 1 (by rfl) ⟨1651931, by rfl⟩ : syracuseStep 2202575 = 3303863) B3303863
theorem B3303869 : Blo 2201435 3303869 := bbase (se 3 (by rfl) ⟨619475, by rfl⟩ : syracuseStep 3303869 = 1238951) (by norm_num)
theorem B2202579 : Blo 2201435 2202579 := bstep (se 1 (by rfl) ⟨1651934, by rfl⟩ : syracuseStep 2202579 = 3303869) B3303869
theorem B4955813 : Blo 2201435 4955813 := bbase (se 4 (by rfl) ⟨464607, by rfl⟩ : syracuseStep 4955813 = 929215) (by norm_num)
theorem B3303875 : Blo 2201435 3303875 := bstep (se 1 (by rfl) ⟨2477906, by rfl⟩ : syracuseStep 3303875 = 4955813) B4955813
theorem B2202583 : Blo 2201435 2202583 := bstep (se 1 (by rfl) ⟨1651937, by rfl⟩ : syracuseStep 2202583 = 3303875) B3303875
theorem B5575301 : Blo 2201435 5575301 := bbase (se 4 (by rfl) ⟨522684, by rfl⟩ : syracuseStep 5575301 = 1045369) (by norm_num)
theorem B3716867 : Blo 2201435 3716867 := bstep (se 1 (by rfl) ⟨2787650, by rfl⟩ : syracuseStep 3716867 = 5575301) B5575301
theorem B2477911 : Blo 2201435 2477911 := bstep (se 1 (by rfl) ⟨1858433, by rfl⟩ : syracuseStep 2477911 = 3716867) B3716867
theorem B3303881 : Blo 2201435 3303881 := bstep (se 2 (by rfl) ⟨1238955, by rfl⟩ : syracuseStep 3303881 = 2477911) B2477911
theorem B2202587 : Blo 2201435 2202587 := bstep (se 1 (by rfl) ⟨1651940, by rfl⟩ : syracuseStep 2202587 = 3303881) B3303881
theorem B2545993 : Blo 2201435 2545993 := bbase (se 2 (by rfl) ⟨954747, by rfl⟩ : syracuseStep 2545993 = 1909495) (by norm_num)
theorem B3394657 : Blo 2201435 3394657 := bstep (se 2 (by rfl) ⟨1272996, by rfl⟩ : syracuseStep 3394657 = 2545993) B2545993
theorem B4526209 : Blo 2201435 4526209 := bstep (se 2 (by rfl) ⟨1697328, by rfl⟩ : syracuseStep 4526209 = 3394657) B3394657
theorem B24139781 : Blo 2201435 24139781 := bstep (se 4 (by rfl) ⟨2263104, by rfl⟩ : syracuseStep 24139781 = 4526209) B4526209
theorem B16093187 : Blo 2201435 16093187 := bstep (se 1 (by rfl) ⟨12069890, by rfl⟩ : syracuseStep 16093187 = 24139781) B24139781
theorem B10728791 : Blo 2201435 10728791 := bstep (se 1 (by rfl) ⟨8046593, by rfl⟩ : syracuseStep 10728791 = 16093187) B16093187
theorem B7152527 : Blo 2201435 7152527 := bstep (se 1 (by rfl) ⟨5364395, by rfl⟩ : syracuseStep 7152527 = 10728791) B10728791
theorem B4768351 : Blo 2201435 4768351 := bstep (se 1 (by rfl) ⟨3576263, by rfl⟩ : syracuseStep 4768351 = 7152527) B7152527
theorem B101724821 : Blo 2201435 101724821 := bstep (se 6 (by rfl) ⟨2384175, by rfl⟩ : syracuseStep 101724821 = 4768351) B4768351
theorem B67816547 : Blo 2201435 67816547 := bstep (se 1 (by rfl) ⟨50862410, by rfl⟩ : syracuseStep 67816547 = 101724821) B101724821
theorem B45211031 : Blo 2201435 45211031 := bstep (se 1 (by rfl) ⟨33908273, by rfl⟩ : syracuseStep 45211031 = 67816547) B67816547
theorem B30140687 : Blo 2201435 30140687 := bstep (se 1 (by rfl) ⟨22605515, by rfl⟩ : syracuseStep 30140687 = 45211031) B45211031
theorem B20093791 : Blo 2201435 20093791 := bstep (se 1 (by rfl) ⟨15070343, by rfl⟩ : syracuseStep 20093791 = 30140687) B30140687
theorem B26791721 : Blo 2201435 26791721 := bstep (se 2 (by rfl) ⟨10046895, by rfl⟩ : syracuseStep 26791721 = 20093791) B20093791
theorem B17861147 : Blo 2201435 17861147 := bstep (se 1 (by rfl) ⟨13395860, by rfl⟩ : syracuseStep 17861147 = 26791721) B26791721
theorem B11907431 : Blo 2201435 11907431 := bstep (se 1 (by rfl) ⟨8930573, by rfl⟩ : syracuseStep 11907431 = 17861147) B17861147
theorem B7938287 : Blo 2201435 7938287 := bstep (se 1 (by rfl) ⟨5953715, by rfl⟩ : syracuseStep 7938287 = 11907431) B11907431
theorem B5292191 : Blo 2201435 5292191 := bstep (se 1 (by rfl) ⟨3969143, by rfl⟩ : syracuseStep 5292191 = 7938287) B7938287
theorem B3528127 : Blo 2201435 3528127 := bstep (se 1 (by rfl) ⟨2646095, by rfl⟩ : syracuseStep 3528127 = 5292191) B5292191
theorem B4704169 : Blo 2201435 4704169 := bstep (se 2 (by rfl) ⟨1764063, by rfl⟩ : syracuseStep 4704169 = 3528127) B3528127
theorem B6272225 : Blo 2201435 6272225 := bstep (se 2 (by rfl) ⟨2352084, by rfl⟩ : syracuseStep 6272225 = 4704169) B4704169
theorem B4181483 : Blo 2201435 4181483 := bstep (se 1 (by rfl) ⟨3136112, by rfl⟩ : syracuseStep 4181483 = 6272225) B6272225
theorem B11150621 : Blo 2201435 11150621 := bstep (se 3 (by rfl) ⟨2090741, by rfl⟩ : syracuseStep 11150621 = 4181483) B4181483
theorem B7433747 : Blo 2201435 7433747 := bstep (se 1 (by rfl) ⟨5575310, by rfl⟩ : syracuseStep 7433747 = 11150621) B11150621
theorem B4955831 : Blo 2201435 4955831 := bstep (se 1 (by rfl) ⟨3716873, by rfl⟩ : syracuseStep 4955831 = 7433747) B7433747
theorem B3303887 : Blo 2201435 3303887 := bstep (se 1 (by rfl) ⟨2477915, by rfl⟩ : syracuseStep 3303887 = 4955831) B4955831
theorem B2202591 : Blo 2201435 2202591 := bstep (se 1 (by rfl) ⟨1651943, by rfl⟩ : syracuseStep 2202591 = 3303887) B3303887
theorem B3303893 : Blo 2201435 3303893 := bbase (se 7 (by rfl) ⟨38717, by rfl⟩ : syracuseStep 3303893 = 77435) (by norm_num)
theorem B2202595 : Blo 2201435 2202595 := bstep (se 1 (by rfl) ⟨1651946, by rfl⟩ : syracuseStep 2202595 = 3303893) B3303893
theorem B8362997 : Blo 2201435 8362997 := bbase (se 5 (by rfl) ⟨392015, by rfl⟩ : syracuseStep 8362997 = 784031) (by norm_num)
theorem B5575331 : Blo 2201435 5575331 := bstep (se 1 (by rfl) ⟨4181498, by rfl⟩ : syracuseStep 5575331 = 8362997) B8362997
theorem B3716887 : Blo 2201435 3716887 := bstep (se 1 (by rfl) ⟨2787665, by rfl⟩ : syracuseStep 3716887 = 5575331) B5575331
theorem B4955849 : Blo 2201435 4955849 := bstep (se 2 (by rfl) ⟨1858443, by rfl⟩ : syracuseStep 4955849 = 3716887) B3716887
theorem B3303899 : Blo 2201435 3303899 := bstep (se 1 (by rfl) ⟨2477924, by rfl⟩ : syracuseStep 3303899 = 4955849) B4955849
theorem B2202599 : Blo 2201435 2202599 := bstep (se 1 (by rfl) ⟨1651949, by rfl⟩ : syracuseStep 2202599 = 3303899) B3303899
theorem B2477929 : Blo 2201435 2477929 := bbase (se 2 (by rfl) ⟨929223, by rfl⟩ : syracuseStep 2477929 = 1858447) (by norm_num)
theorem B3303905 : Blo 2201435 3303905 := bstep (se 2 (by rfl) ⟨1238964, by rfl⟩ : syracuseStep 3303905 = 2477929) B2477929
theorem B2202603 : Blo 2201435 2202603 := bstep (se 1 (by rfl) ⟨1651952, by rfl⟩ : syracuseStep 2202603 = 3303905) B3303905
theorem B5292229 : Blo 2201435 5292229 := bbase (se 4 (by rfl) ⟨496146, by rfl⟩ : syracuseStep 5292229 = 992293) (by norm_num)
theorem B7056305 : Blo 2201435 7056305 := bstep (se 2 (by rfl) ⟨2646114, by rfl⟩ : syracuseStep 7056305 = 5292229) B5292229
theorem B4704203 : Blo 2201435 4704203 := bstep (se 1 (by rfl) ⟨3528152, by rfl⟩ : syracuseStep 4704203 = 7056305) B7056305
theorem B12544541 : Blo 2201435 12544541 := bstep (se 3 (by rfl) ⟨2352101, by rfl⟩ : syracuseStep 12544541 = 4704203) B4704203
theorem B8363027 : Blo 2201435 8363027 := bstep (se 1 (by rfl) ⟨6272270, by rfl⟩ : syracuseStep 8363027 = 12544541) B12544541
theorem B5575351 : Blo 2201435 5575351 := bstep (se 1 (by rfl) ⟨4181513, by rfl⟩ : syracuseStep 5575351 = 8363027) B8363027
theorem B7433801 : Blo 2201435 7433801 := bstep (se 2 (by rfl) ⟨2787675, by rfl⟩ : syracuseStep 7433801 = 5575351) B5575351
theorem B4955867 : Blo 2201435 4955867 := bstep (se 1 (by rfl) ⟨3716900, by rfl⟩ : syracuseStep 4955867 = 7433801) B7433801
theorem B3303911 : Blo 2201435 3303911 := bstep (se 1 (by rfl) ⟨2477933, by rfl⟩ : syracuseStep 3303911 = 4955867) B4955867
theorem B2202607 : Blo 2201435 2202607 := bstep (se 1 (by rfl) ⟨1651955, by rfl⟩ : syracuseStep 2202607 = 3303911) B3303911
theorem B3303917 : Blo 2201435 3303917 := bbase (se 3 (by rfl) ⟨619484, by rfl⟩ : syracuseStep 3303917 = 1238969) (by norm_num)
theorem B2202611 : Blo 2201435 2202611 := bstep (se 1 (by rfl) ⟨1651958, by rfl⟩ : syracuseStep 2202611 = 3303917) B3303917
theorem B4955885 : Blo 2201435 4955885 := bbase (se 3 (by rfl) ⟨929228, by rfl⟩ : syracuseStep 4955885 = 1858457) (by norm_num)
theorem B3303923 : Blo 2201435 3303923 := bstep (se 1 (by rfl) ⟨2477942, by rfl⟩ : syracuseStep 3303923 = 4955885) B4955885
theorem B2202615 : Blo 2201435 2202615 := bstep (se 1 (by rfl) ⟨1651961, by rfl⟩ : syracuseStep 2202615 = 3303923) B3303923
theorem B3528173 : Blo 2201435 3528173 := bbase (se 3 (by rfl) ⟨661532, by rfl⟩ : syracuseStep 3528173 = 1323065) (by norm_num)
theorem B2352115 : Blo 2201435 2352115 := bstep (se 1 (by rfl) ⟨1764086, by rfl⟩ : syracuseStep 2352115 = 3528173) B3528173
theorem B3136153 : Blo 2201435 3136153 := bstep (se 2 (by rfl) ⟨1176057, by rfl⟩ : syracuseStep 3136153 = 2352115) B2352115
theorem B4181537 : Blo 2201435 4181537 := bstep (se 2 (by rfl) ⟨1568076, by rfl⟩ : syracuseStep 4181537 = 3136153) B3136153
theorem B2787691 : Blo 2201435 2787691 := bstep (se 1 (by rfl) ⟨2090768, by rfl⟩ : syracuseStep 2787691 = 4181537) B4181537
theorem B3716921 : Blo 2201435 3716921 := bstep (se 2 (by rfl) ⟨1393845, by rfl⟩ : syracuseStep 3716921 = 2787691) B2787691
theorem B2477947 : Blo 2201435 2477947 := bstep (se 1 (by rfl) ⟨1858460, by rfl⟩ : syracuseStep 2477947 = 3716921) B3716921
theorem B3303929 : Blo 2201435 3303929 := bstep (se 2 (by rfl) ⟨1238973, by rfl⟩ : syracuseStep 3303929 = 2477947) B2477947
theorem B2202619 : Blo 2201435 2202619 := bstep (se 1 (by rfl) ⟨1651964, by rfl⟩ : syracuseStep 2202619 = 3303929) B3303929
theorem B2546029 : Blo 2201435 2546029 := bbase (se 3 (by rfl) ⟨477380, by rfl⟩ : syracuseStep 2546029 = 954761) (by norm_num)
theorem B3394705 : Blo 2201435 3394705 := bstep (se 2 (by rfl) ⟨1273014, by rfl⟩ : syracuseStep 3394705 = 2546029) B2546029
theorem B4526273 : Blo 2201435 4526273 := bstep (se 2 (by rfl) ⟨1697352, by rfl⟩ : syracuseStep 4526273 = 3394705) B3394705
theorem B3017515 : Blo 2201435 3017515 := bstep (se 1 (by rfl) ⟨2263136, by rfl⟩ : syracuseStep 3017515 = 4526273) B4526273
theorem B4023353 : Blo 2201435 4023353 := bstep (se 2 (by rfl) ⟨1508757, by rfl⟩ : syracuseStep 4023353 = 3017515) B3017515
theorem B10728941 : Blo 2201435 10728941 := bstep (se 3 (by rfl) ⟨2011676, by rfl⟩ : syracuseStep 10728941 = 4023353) B4023353
theorem B114442037 : Blo 2201435 114442037 := bstep (se 5 (by rfl) ⟨5364470, by rfl⟩ : syracuseStep 114442037 = 10728941) B10728941
theorem B76294691 : Blo 2201435 76294691 := bstep (se 1 (by rfl) ⟨57221018, by rfl⟩ : syracuseStep 76294691 = 114442037) B114442037
theorem B813810037 : Blo 2201435 813810037 := bstep (se 5 (by rfl) ⟨38147345, by rfl⟩ : syracuseStep 813810037 = 76294691) B76294691
theorem B1085080049 : Blo 2201435 1085080049 := bstep (se 2 (by rfl) ⟨406905018, by rfl⟩ : syracuseStep 1085080049 = 813810037) B813810037
theorem B723386699 : Blo 2201435 723386699 := bstep (se 1 (by rfl) ⟨542540024, by rfl⟩ : syracuseStep 723386699 = 1085080049) B1085080049
theorem B482257799 : Blo 2201435 482257799 := bstep (se 1 (by rfl) ⟨361693349, by rfl⟩ : syracuseStep 482257799 = 723386699) B723386699
theorem B321505199 : Blo 2201435 321505199 := bstep (se 1 (by rfl) ⟨241128899, by rfl⟩ : syracuseStep 321505199 = 482257799) B482257799
theorem B214336799 : Blo 2201435 214336799 := bstep (se 1 (by rfl) ⟨160752599, by rfl⟩ : syracuseStep 214336799 = 321505199) B321505199
theorem B142891199 : Blo 2201435 142891199 := bstep (se 1 (by rfl) ⟨107168399, by rfl⟩ : syracuseStep 142891199 = 214336799) B214336799
theorem B95260799 : Blo 2201435 95260799 := bstep (se 1 (by rfl) ⟨71445599, by rfl⟩ : syracuseStep 95260799 = 142891199) B142891199
theorem B63507199 : Blo 2201435 63507199 := bstep (se 1 (by rfl) ⟨47630399, by rfl⟩ : syracuseStep 63507199 = 95260799) B95260799
theorem B84676265 : Blo 2201435 84676265 := bstep (se 2 (by rfl) ⟨31753599, by rfl⟩ : syracuseStep 84676265 = 63507199) B63507199
theorem B56450843 : Blo 2201435 56450843 := bstep (se 1 (by rfl) ⟨42338132, by rfl⟩ : syracuseStep 56450843 = 84676265) B84676265
theorem B37633895 : Blo 2201435 37633895 := bstep (se 1 (by rfl) ⟨28225421, by rfl⟩ : syracuseStep 37633895 = 56450843) B56450843
theorem B25089263 : Blo 2201435 25089263 := bstep (se 1 (by rfl) ⟨18816947, by rfl⟩ : syracuseStep 25089263 = 37633895) B37633895
theorem B16726175 : Blo 2201435 16726175 := bstep (se 1 (by rfl) ⟨12544631, by rfl⟩ : syracuseStep 16726175 = 25089263) B25089263
theorem B11150783 : Blo 2201435 11150783 := bstep (se 1 (by rfl) ⟨8363087, by rfl⟩ : syracuseStep 11150783 = 16726175) B16726175
theorem B7433855 : Blo 2201435 7433855 := bstep (se 1 (by rfl) ⟨5575391, by rfl⟩ : syracuseStep 7433855 = 11150783) B11150783
theorem B4955903 : Blo 2201435 4955903 := bstep (se 1 (by rfl) ⟨3716927, by rfl⟩ : syracuseStep 4955903 = 7433855) B7433855
theorem B3303935 : Blo 2201435 3303935 := bstep (se 1 (by rfl) ⟨2477951, by rfl⟩ : syracuseStep 3303935 = 4955903) B4955903
theorem B2202623 : Blo 2201435 2202623 := bstep (se 1 (by rfl) ⟨1651967, by rfl⟩ : syracuseStep 2202623 = 3303935) B3303935
theorem B3303941 : Blo 2201435 3303941 := bbase (se 4 (by rfl) ⟨309744, by rfl⟩ : syracuseStep 3303941 = 619489) (by norm_num)
theorem B2202627 : Blo 2201435 2202627 := bstep (se 1 (by rfl) ⟨1651970, by rfl⟩ : syracuseStep 2202627 = 3303941) B3303941
theorem B3716941 : Blo 2201435 3716941 := bbase (se 3 (by rfl) ⟨696926, by rfl⟩ : syracuseStep 3716941 = 1393853) (by norm_num)
theorem B4955921 : Blo 2201435 4955921 := bstep (se 2 (by rfl) ⟨1858470, by rfl⟩ : syracuseStep 4955921 = 3716941) B3716941
theorem B3303947 : Blo 2201435 3303947 := bstep (se 1 (by rfl) ⟨2477960, by rfl⟩ : syracuseStep 3303947 = 4955921) B4955921
theorem B2202631 : Blo 2201435 2202631 := bstep (se 1 (by rfl) ⟨1651973, by rfl⟩ : syracuseStep 2202631 = 3303947) B3303947
theorem B2477965 : Blo 2201435 2477965 := bbase (se 3 (by rfl) ⟨464618, by rfl⟩ : syracuseStep 2477965 = 929237) (by norm_num)
theorem B3303953 : Blo 2201435 3303953 := bstep (se 2 (by rfl) ⟨1238982, by rfl⟩ : syracuseStep 3303953 = 2477965) B2477965
theorem B2202635 : Blo 2201435 2202635 := bstep (se 1 (by rfl) ⟨1651976, by rfl⟩ : syracuseStep 2202635 = 3303953) B3303953
theorem B7433909 : Blo 2201435 7433909 := bbase (se 5 (by rfl) ⟨348464, by rfl⟩ : syracuseStep 7433909 = 696929) (by norm_num)
theorem B4955939 : Blo 2201435 4955939 := bstep (se 1 (by rfl) ⟨3716954, by rfl⟩ : syracuseStep 4955939 = 7433909) B7433909
theorem B3303959 : Blo 2201435 3303959 := bstep (se 1 (by rfl) ⟨2477969, by rfl⟩ : syracuseStep 3303959 = 4955939) B4955939
theorem B2202639 : Blo 2201435 2202639 := bstep (se 1 (by rfl) ⟨1651979, by rfl⟩ : syracuseStep 2202639 = 3303959) B3303959
theorem B3303965 : Blo 2201435 3303965 := bbase (se 3 (by rfl) ⟨619493, by rfl⟩ : syracuseStep 3303965 = 1238987) (by norm_num)
theorem B2202643 : Blo 2201435 2202643 := bstep (se 1 (by rfl) ⟨1651982, by rfl⟩ : syracuseStep 2202643 = 3303965) B3303965
theorem B4955957 : Blo 2201435 4955957 := bbase (se 5 (by rfl) ⟨232310, by rfl⟩ : syracuseStep 4955957 = 464621) (by norm_num)
theorem B3303971 : Blo 2201435 3303971 := bstep (se 1 (by rfl) ⟨2477978, by rfl⟩ : syracuseStep 3303971 = 4955957) B4955957
theorem B2202647 : Blo 2201435 2202647 := bstep (se 1 (by rfl) ⟨1651985, by rfl⟩ : syracuseStep 2202647 = 3303971) B3303971
theorem B5651533 : Blo 2201435 5651533 := bbase (se 3 (by rfl) ⟨1059662, by rfl⟩ : syracuseStep 5651533 = 2119325) (by norm_num)
theorem B7535377 : Blo 2201435 7535377 := bstep (se 2 (by rfl) ⟨2825766, by rfl⟩ : syracuseStep 7535377 = 5651533) B5651533
theorem B10047169 : Blo 2201435 10047169 := bstep (se 2 (by rfl) ⟨3767688, by rfl⟩ : syracuseStep 10047169 = 7535377) B7535377
theorem B13396225 : Blo 2201435 13396225 := bstep (se 2 (by rfl) ⟨5023584, by rfl⟩ : syracuseStep 13396225 = 10047169) B10047169
theorem B17861633 : Blo 2201435 17861633 := bstep (se 2 (by rfl) ⟨6698112, by rfl⟩ : syracuseStep 17861633 = 13396225) B13396225
theorem B11907755 : Blo 2201435 11907755 := bstep (se 1 (by rfl) ⟨8930816, by rfl⟩ : syracuseStep 11907755 = 17861633) B17861633
theorem B7938503 : Blo 2201435 7938503 := bstep (se 1 (by rfl) ⟨5953877, by rfl⟩ : syracuseStep 7938503 = 11907755) B11907755
theorem B5292335 : Blo 2201435 5292335 := bstep (se 1 (by rfl) ⟨3969251, by rfl⟩ : syracuseStep 5292335 = 7938503) B7938503
theorem B14112893 : Blo 2201435 14112893 := bstep (se 3 (by rfl) ⟨2646167, by rfl⟩ : syracuseStep 14112893 = 5292335) B5292335
theorem B9408595 : Blo 2201435 9408595 := bstep (se 1 (by rfl) ⟨7056446, by rfl⟩ : syracuseStep 9408595 = 14112893) B14112893
theorem B12544793 : Blo 2201435 12544793 := bstep (se 2 (by rfl) ⟨4704297, by rfl⟩ : syracuseStep 12544793 = 9408595) B9408595
theorem B8363195 : Blo 2201435 8363195 := bstep (se 1 (by rfl) ⟨6272396, by rfl⟩ : syracuseStep 8363195 = 12544793) B12544793
theorem B5575463 : Blo 2201435 5575463 := bstep (se 1 (by rfl) ⟨4181597, by rfl⟩ : syracuseStep 5575463 = 8363195) B8363195
theorem B3716975 : Blo 2201435 3716975 := bstep (se 1 (by rfl) ⟨2787731, by rfl⟩ : syracuseStep 3716975 = 5575463) B5575463
theorem B2477983 : Blo 2201435 2477983 := bstep (se 1 (by rfl) ⟨1858487, by rfl⟩ : syracuseStep 2477983 = 3716975) B3716975
theorem B3303977 : Blo 2201435 3303977 := bstep (se 2 (by rfl) ⟨1238991, by rfl⟩ : syracuseStep 3303977 = 2477983) B2477983
theorem B2202651 : Blo 2201435 2202651 := bstep (se 1 (by rfl) ⟨1651988, by rfl⟩ : syracuseStep 2202651 = 3303977) B3303977
theorem B14112917 : Blo 2201435 14112917 := bbase (se 6 (by rfl) ⟨330771, by rfl⟩ : syracuseStep 14112917 = 661543) (by norm_num)
theorem B9408611 : Blo 2201435 9408611 := bstep (se 1 (by rfl) ⟨7056458, by rfl⟩ : syracuseStep 9408611 = 14112917) B14112917
theorem B6272407 : Blo 2201435 6272407 := bstep (se 1 (by rfl) ⟨4704305, by rfl⟩ : syracuseStep 6272407 = 9408611) B9408611
theorem B8363209 : Blo 2201435 8363209 := bstep (se 2 (by rfl) ⟨3136203, by rfl⟩ : syracuseStep 8363209 = 6272407) B6272407
theorem B11150945 : Blo 2201435 11150945 := bstep (se 2 (by rfl) ⟨4181604, by rfl⟩ : syracuseStep 11150945 = 8363209) B8363209
theorem B7433963 : Blo 2201435 7433963 := bstep (se 1 (by rfl) ⟨5575472, by rfl⟩ : syracuseStep 7433963 = 11150945) B11150945
theorem B4955975 : Blo 2201435 4955975 := bstep (se 1 (by rfl) ⟨3716981, by rfl⟩ : syracuseStep 4955975 = 7433963) B7433963
theorem B3303983 : Blo 2201435 3303983 := bstep (se 1 (by rfl) ⟨2477987, by rfl⟩ : syracuseStep 3303983 = 4955975) B4955975
theorem B2202655 : Blo 2201435 2202655 := bstep (se 1 (by rfl) ⟨1651991, by rfl⟩ : syracuseStep 2202655 = 3303983) B3303983
theorem B3303989 : Blo 2201435 3303989 := bbase (se 5 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 3303989 = 309749) (by norm_num)
theorem B2202659 : Blo 2201435 2202659 := bstep (se 1 (by rfl) ⟨1651994, by rfl⟩ : syracuseStep 2202659 = 3303989) B3303989
theorem B5575493 : Blo 2201435 5575493 := bbase (se 4 (by rfl) ⟨522702, by rfl⟩ : syracuseStep 5575493 = 1045405) (by norm_num)
theorem B3716995 : Blo 2201435 3716995 := bstep (se 1 (by rfl) ⟨2787746, by rfl⟩ : syracuseStep 3716995 = 5575493) B5575493
theorem B4955993 : Blo 2201435 4955993 := bstep (se 2 (by rfl) ⟨1858497, by rfl⟩ : syracuseStep 4955993 = 3716995) B3716995
theorem B3303995 : Blo 2201435 3303995 := bstep (se 1 (by rfl) ⟨2477996, by rfl⟩ : syracuseStep 3303995 = 4955993) B4955993
theorem B2202663 : Blo 2201435 2202663 := bstep (se 1 (by rfl) ⟨1651997, by rfl⟩ : syracuseStep 2202663 = 3303995) B3303995
theorem B2478001 : Blo 2201435 2478001 := bbase (se 2 (by rfl) ⟨929250, by rfl⟩ : syracuseStep 2478001 = 1858501) (by norm_num)
theorem B3304001 : Blo 2201435 3304001 := bstep (se 2 (by rfl) ⟨1239000, by rfl⟩ : syracuseStep 3304001 = 2478001) B2478001
theorem B2202667 : Blo 2201435 2202667 := bstep (se 1 (by rfl) ⟨1652000, by rfl⟩ : syracuseStep 2202667 = 3304001) B3304001
theorem B6272453 : Blo 2201435 6272453 := bbase (se 4 (by rfl) ⟨588042, by rfl⟩ : syracuseStep 6272453 = 1176085) (by norm_num)
theorem B4181635 : Blo 2201435 4181635 := bstep (se 1 (by rfl) ⟨3136226, by rfl⟩ : syracuseStep 4181635 = 6272453) B6272453
theorem B5575513 : Blo 2201435 5575513 := bstep (se 2 (by rfl) ⟨2090817, by rfl⟩ : syracuseStep 5575513 = 4181635) B4181635
theorem B7434017 : Blo 2201435 7434017 := bstep (se 2 (by rfl) ⟨2787756, by rfl⟩ : syracuseStep 7434017 = 5575513) B5575513
theorem B4956011 : Blo 2201435 4956011 := bstep (se 1 (by rfl) ⟨3717008, by rfl⟩ : syracuseStep 4956011 = 7434017) B7434017
theorem B3304007 : Blo 2201435 3304007 := bstep (se 1 (by rfl) ⟨2478005, by rfl⟩ : syracuseStep 3304007 = 4956011) B4956011
theorem B2202671 : Blo 2201435 2202671 := bstep (se 1 (by rfl) ⟨1652003, by rfl⟩ : syracuseStep 2202671 = 3304007) B3304007
theorem B3304013 : Blo 2201435 3304013 := bbase (se 3 (by rfl) ⟨619502, by rfl⟩ : syracuseStep 3304013 = 1239005) (by norm_num)
theorem B2202675 : Blo 2201435 2202675 := bstep (se 1 (by rfl) ⟨1652006, by rfl⟩ : syracuseStep 2202675 = 3304013) B3304013
theorem B4956029 : Blo 2201435 4956029 := bbase (se 3 (by rfl) ⟨929255, by rfl⟩ : syracuseStep 4956029 = 1858511) (by norm_num)
theorem B3304019 : Blo 2201435 3304019 := bstep (se 1 (by rfl) ⟨2478014, by rfl⟩ : syracuseStep 3304019 = 4956029) B4956029
theorem B2202679 : Blo 2201435 2202679 := bstep (se 1 (by rfl) ⟨1652009, by rfl⟩ : syracuseStep 2202679 = 3304019) B3304019
theorem B3717029 : Blo 2201435 3717029 := bbase (se 4 (by rfl) ⟨348471, by rfl⟩ : syracuseStep 3717029 = 696943) (by norm_num)
theorem B2478019 : Blo 2201435 2478019 := bstep (se 1 (by rfl) ⟨1858514, by rfl⟩ : syracuseStep 2478019 = 3717029) B3717029
theorem B3304025 : Blo 2201435 3304025 := bstep (se 2 (by rfl) ⟨1239009, by rfl⟩ : syracuseStep 3304025 = 2478019) B2478019
theorem B2202683 : Blo 2201435 2202683 := bstep (se 1 (by rfl) ⟨1652012, by rfl⟩ : syracuseStep 2202683 = 3304025) B3304025
theorem B3969317 : Blo 2201435 3969317 := bbase (se 4 (by rfl) ⟨372123, by rfl⟩ : syracuseStep 3969317 = 744247) (by norm_num)
theorem B2646211 : Blo 2201435 2646211 := bstep (se 1 (by rfl) ⟨1984658, by rfl⟩ : syracuseStep 2646211 = 3969317) B3969317
theorem B3528281 : Blo 2201435 3528281 := bstep (se 2 (by rfl) ⟨1323105, by rfl⟩ : syracuseStep 3528281 = 2646211) B2646211
theorem B2352187 : Blo 2201435 2352187 := bstep (se 1 (by rfl) ⟨1764140, by rfl⟩ : syracuseStep 2352187 = 3528281) B3528281
theorem B3136249 : Blo 2201435 3136249 := bstep (se 2 (by rfl) ⟨1176093, by rfl⟩ : syracuseStep 3136249 = 2352187) B2352187
theorem B16726661 : Blo 2201435 16726661 := bstep (se 4 (by rfl) ⟨1568124, by rfl⟩ : syracuseStep 16726661 = 3136249) B3136249
theorem B11151107 : Blo 2201435 11151107 := bstep (se 1 (by rfl) ⟨8363330, by rfl⟩ : syracuseStep 11151107 = 16726661) B16726661
theorem B7434071 : Blo 2201435 7434071 := bstep (se 1 (by rfl) ⟨5575553, by rfl⟩ : syracuseStep 7434071 = 11151107) B11151107
theorem B4956047 : Blo 2201435 4956047 := bstep (se 1 (by rfl) ⟨3717035, by rfl⟩ : syracuseStep 4956047 = 7434071) B7434071
theorem B3304031 : Blo 2201435 3304031 := bstep (se 1 (by rfl) ⟨2478023, by rfl⟩ : syracuseStep 3304031 = 4956047) B4956047
theorem B2202687 : Blo 2201435 2202687 := bstep (se 1 (by rfl) ⟨1652015, by rfl⟩ : syracuseStep 2202687 = 3304031) B3304031
theorem B3304037 : Blo 2201435 3304037 := bbase (se 4 (by rfl) ⟨309753, by rfl⟩ : syracuseStep 3304037 = 619507) (by norm_num)
theorem B2202691 : Blo 2201435 2202691 := bstep (se 1 (by rfl) ⟨1652018, by rfl⟩ : syracuseStep 2202691 = 3304037) B3304037
theorem B3136261 : Blo 2201435 3136261 := bbase (se 4 (by rfl) ⟨294024, by rfl⟩ : syracuseStep 3136261 = 588049) (by norm_num)
theorem B4181681 : Blo 2201435 4181681 := bstep (se 2 (by rfl) ⟨1568130, by rfl⟩ : syracuseStep 4181681 = 3136261) B3136261
theorem B2787787 : Blo 2201435 2787787 := bstep (se 1 (by rfl) ⟨2090840, by rfl⟩ : syracuseStep 2787787 = 4181681) B4181681
theorem B3717049 : Blo 2201435 3717049 := bstep (se 2 (by rfl) ⟨1393893, by rfl⟩ : syracuseStep 3717049 = 2787787) B2787787
theorem B4956065 : Blo 2201435 4956065 := bstep (se 2 (by rfl) ⟨1858524, by rfl⟩ : syracuseStep 4956065 = 3717049) B3717049
theorem B3304043 : Blo 2201435 3304043 := bstep (se 1 (by rfl) ⟨2478032, by rfl⟩ : syracuseStep 3304043 = 4956065) B4956065
theorem B2202695 : Blo 2201435 2202695 := bstep (se 1 (by rfl) ⟨1652021, by rfl⟩ : syracuseStep 2202695 = 3304043) B3304043
theorem B2478037 : Blo 2201435 2478037 := bbase (se 7 (by rfl) ⟨29039, by rfl⟩ : syracuseStep 2478037 = 58079) (by norm_num)
theorem B3304049 : Blo 2201435 3304049 := bstep (se 2 (by rfl) ⟨1239018, by rfl⟩ : syracuseStep 3304049 = 2478037) B2478037
theorem B2202699 : Blo 2201435 2202699 := bstep (se 1 (by rfl) ⟨1652024, by rfl⟩ : syracuseStep 2202699 = 3304049) B3304049
theorem B2787797 : Blo 2201435 2787797 := bbase (se 7 (by rfl) ⟨32669, by rfl⟩ : syracuseStep 2787797 = 65339) (by norm_num)
theorem B7434125 : Blo 2201435 7434125 := bstep (se 3 (by rfl) ⟨1393898, by rfl⟩ : syracuseStep 7434125 = 2787797) B2787797
theorem B4956083 : Blo 2201435 4956083 := bstep (se 1 (by rfl) ⟨3717062, by rfl⟩ : syracuseStep 4956083 = 7434125) B7434125
theorem B3304055 : Blo 2201435 3304055 := bstep (se 1 (by rfl) ⟨2478041, by rfl⟩ : syracuseStep 3304055 = 4956083) B4956083
theorem B2202703 : Blo 2201435 2202703 := bstep (se 1 (by rfl) ⟨1652027, by rfl⟩ : syracuseStep 2202703 = 3304055) B3304055
theorem B3304061 : Blo 2201435 3304061 := bbase (se 3 (by rfl) ⟨619511, by rfl⟩ : syracuseStep 3304061 = 1239023) (by norm_num)
theorem B2202707 : Blo 2201435 2202707 := bstep (se 1 (by rfl) ⟨1652030, by rfl⟩ : syracuseStep 2202707 = 3304061) B3304061
theorem B4956101 : Blo 2201435 4956101 := bbase (se 4 (by rfl) ⟨464634, by rfl⟩ : syracuseStep 4956101 = 929269) (by norm_num)
theorem B3304067 : Blo 2201435 3304067 := bstep (se 1 (by rfl) ⟨2478050, by rfl⟩ : syracuseStep 3304067 = 4956101) B4956101
theorem B2202711 : Blo 2201435 2202711 := bstep (se 1 (by rfl) ⟨1652033, by rfl⟩ : syracuseStep 2202711 = 3304067) B3304067
theorem B9408869 : Blo 2201435 9408869 := bbase (se 4 (by rfl) ⟨882081, by rfl⟩ : syracuseStep 9408869 = 1764163) (by norm_num)
theorem B6272579 : Blo 2201435 6272579 := bstep (se 1 (by rfl) ⟨4704434, by rfl⟩ : syracuseStep 6272579 = 9408869) B9408869
theorem B4181719 : Blo 2201435 4181719 := bstep (se 1 (by rfl) ⟨3136289, by rfl⟩ : syracuseStep 4181719 = 6272579) B6272579
theorem B5575625 : Blo 2201435 5575625 := bstep (se 2 (by rfl) ⟨2090859, by rfl⟩ : syracuseStep 5575625 = 4181719) B4181719
theorem B3717083 : Blo 2201435 3717083 := bstep (se 1 (by rfl) ⟨2787812, by rfl⟩ : syracuseStep 3717083 = 5575625) B5575625
theorem B2478055 : Blo 2201435 2478055 := bstep (se 1 (by rfl) ⟨1858541, by rfl⟩ : syracuseStep 2478055 = 3717083) B3717083
theorem B3304073 : Blo 2201435 3304073 := bstep (se 2 (by rfl) ⟨1239027, by rfl⟩ : syracuseStep 3304073 = 2478055) B2478055
theorem B2202715 : Blo 2201435 2202715 := bstep (se 1 (by rfl) ⟨1652036, by rfl⟩ : syracuseStep 2202715 = 3304073) B3304073
theorem B11151269 : Blo 2201435 11151269 := bbase (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) (by norm_num)
theorem B7434179 : Blo 2201435 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B4956119 : Blo 2201435 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B3304079 : Blo 2201435 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B2202719 : Blo 2201435 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B3304085 : Blo 2201435 3304085 := bbase (se 6 (by rfl) ⟨77439, by rfl⟩ : syracuseStep 3304085 = 154879) (by norm_num)
theorem B2202723 : Blo 2201435 2202723 := bstep (se 1 (by rfl) ⟨1652042, by rfl⟩ : syracuseStep 2202723 = 3304085) B3304085
theorem B21170069 : Blo 2201435 21170069 := bbase (se 6 (by rfl) ⟨496173, by rfl⟩ : syracuseStep 21170069 = 992347) (by norm_num)
theorem B14113379 : Blo 2201435 14113379 := bstep (se 1 (by rfl) ⟨10585034, by rfl⟩ : syracuseStep 14113379 = 21170069) B21170069
theorem B9408919 : Blo 2201435 9408919 := bstep (se 1 (by rfl) ⟨7056689, by rfl⟩ : syracuseStep 9408919 = 14113379) B14113379
theorem B12545225 : Blo 2201435 12545225 := bstep (se 2 (by rfl) ⟨4704459, by rfl⟩ : syracuseStep 12545225 = 9408919) B9408919
theorem B8363483 : Blo 2201435 8363483 := bstep (se 1 (by rfl) ⟨6272612, by rfl⟩ : syracuseStep 8363483 = 12545225) B12545225
theorem B5575655 : Blo 2201435 5575655 := bstep (se 1 (by rfl) ⟨4181741, by rfl⟩ : syracuseStep 5575655 = 8363483) B8363483
theorem B3717103 : Blo 2201435 3717103 := bstep (se 1 (by rfl) ⟨2787827, by rfl⟩ : syracuseStep 3717103 = 5575655) B5575655
theorem B4956137 : Blo 2201435 4956137 := bstep (se 2 (by rfl) ⟨1858551, by rfl⟩ : syracuseStep 4956137 = 3717103) B3717103
theorem B3304091 : Blo 2201435 3304091 := bstep (se 1 (by rfl) ⟨2478068, by rfl⟩ : syracuseStep 3304091 = 4956137) B4956137
theorem B2202727 : Blo 2201435 2202727 := bstep (se 1 (by rfl) ⟨1652045, by rfl⟩ : syracuseStep 2202727 = 3304091) B3304091
theorem B2478073 : Blo 2201435 2478073 := bbase (se 2 (by rfl) ⟨929277, by rfl⟩ : syracuseStep 2478073 = 1858555) (by norm_num)
theorem B3304097 : Blo 2201435 3304097 := bstep (se 2 (by rfl) ⟨1239036, by rfl⟩ : syracuseStep 3304097 = 2478073) B2478073
theorem B2202731 : Blo 2201435 2202731 := bstep (se 1 (by rfl) ⟨1652048, by rfl⟩ : syracuseStep 2202731 = 3304097) B3304097
theorem B7938805 : Blo 2201435 7938805 := bbase (se 5 (by rfl) ⟨372131, by rfl⟩ : syracuseStep 7938805 = 744263) (by norm_num)
theorem B10585073 : Blo 2201435 10585073 := bstep (se 2 (by rfl) ⟨3969402, by rfl⟩ : syracuseStep 10585073 = 7938805) B7938805
theorem B7056715 : Blo 2201435 7056715 := bstep (se 1 (by rfl) ⟨5292536, by rfl⟩ : syracuseStep 7056715 = 10585073) B10585073
theorem B9408953 : Blo 2201435 9408953 := bstep (se 2 (by rfl) ⟨3528357, by rfl⟩ : syracuseStep 9408953 = 7056715) B7056715
theorem B6272635 : Blo 2201435 6272635 := bstep (se 1 (by rfl) ⟨4704476, by rfl⟩ : syracuseStep 6272635 = 9408953) B9408953
theorem B8363513 : Blo 2201435 8363513 := bstep (se 2 (by rfl) ⟨3136317, by rfl⟩ : syracuseStep 8363513 = 6272635) B6272635
theorem B5575675 : Blo 2201435 5575675 := bstep (se 1 (by rfl) ⟨4181756, by rfl⟩ : syracuseStep 5575675 = 8363513) B8363513
theorem B7434233 : Blo 2201435 7434233 := bstep (se 2 (by rfl) ⟨2787837, by rfl⟩ : syracuseStep 7434233 = 5575675) B5575675
theorem B4956155 : Blo 2201435 4956155 := bstep (se 1 (by rfl) ⟨3717116, by rfl⟩ : syracuseStep 4956155 = 7434233) B7434233
theorem B3304103 : Blo 2201435 3304103 := bstep (se 1 (by rfl) ⟨2478077, by rfl⟩ : syracuseStep 3304103 = 4956155) B4956155
theorem B2202735 : Blo 2201435 2202735 := bstep (se 1 (by rfl) ⟨1652051, by rfl⟩ : syracuseStep 2202735 = 3304103) B3304103
theorem B3304109 : Blo 2201435 3304109 := bbase (se 3 (by rfl) ⟨619520, by rfl⟩ : syracuseStep 3304109 = 1239041) (by norm_num)
theorem B2202739 : Blo 2201435 2202739 := bstep (se 1 (by rfl) ⟨1652054, by rfl⟩ : syracuseStep 2202739 = 3304109) B3304109
theorem B4956173 : Blo 2201435 4956173 := bbase (se 3 (by rfl) ⟨929282, by rfl⟩ : syracuseStep 4956173 = 1858565) (by norm_num)
theorem B3304115 : Blo 2201435 3304115 := bstep (se 1 (by rfl) ⟨2478086, by rfl⟩ : syracuseStep 3304115 = 4956173) B4956173
theorem B2202743 : Blo 2201435 2202743 := bstep (se 1 (by rfl) ⟨1652057, by rfl⟩ : syracuseStep 2202743 = 3304115) B3304115
theorem B2787853 : Blo 2201435 2787853 := bbase (se 3 (by rfl) ⟨522722, by rfl⟩ : syracuseStep 2787853 = 1045445) (by norm_num)
theorem B3717137 : Blo 2201435 3717137 := bstep (se 2 (by rfl) ⟨1393926, by rfl⟩ : syracuseStep 3717137 = 2787853) B2787853
theorem B2478091 : Blo 2201435 2478091 := bstep (se 1 (by rfl) ⟨1858568, by rfl⟩ : syracuseStep 2478091 = 3717137) B3717137
theorem B3304121 : Blo 2201435 3304121 := bstep (se 2 (by rfl) ⟨1239045, by rfl⟩ : syracuseStep 3304121 = 2478091) B2478091
theorem B2202747 : Blo 2201435 2202747 := bstep (se 1 (by rfl) ⟨1652060, by rfl⟩ : syracuseStep 2202747 = 3304121) B3304121
theorem B25433045 : Blo 2201435 25433045 := bbase (se 7 (by rfl) ⟨298043, by rfl⟩ : syracuseStep 25433045 = 596087) (by norm_num)
theorem B16955363 : Blo 2201435 16955363 := bstep (se 1 (by rfl) ⟨12716522, by rfl⟩ : syracuseStep 16955363 = 25433045) B25433045
theorem B45214301 : Blo 2201435 45214301 := bstep (se 3 (by rfl) ⟨8477681, by rfl⟩ : syracuseStep 45214301 = 16955363) B16955363
theorem B30142867 : Blo 2201435 30142867 := bstep (se 1 (by rfl) ⟨22607150, by rfl⟩ : syracuseStep 30142867 = 45214301) B45214301
theorem B40190489 : Blo 2201435 40190489 := bstep (se 2 (by rfl) ⟨15071433, by rfl⟩ : syracuseStep 40190489 = 30142867) B30142867
theorem B26793659 : Blo 2201435 26793659 := bstep (se 1 (by rfl) ⟨20095244, by rfl⟩ : syracuseStep 26793659 = 40190489) B40190489
theorem B17862439 : Blo 2201435 17862439 := bstep (se 1 (by rfl) ⟨13396829, by rfl⟩ : syracuseStep 17862439 = 26793659) B26793659
theorem B23816585 : Blo 2201435 23816585 := bstep (se 2 (by rfl) ⟨8931219, by rfl⟩ : syracuseStep 23816585 = 17862439) B17862439
theorem B15877723 : Blo 2201435 15877723 := bstep (se 1 (by rfl) ⟨11908292, by rfl⟩ : syracuseStep 15877723 = 23816585) B23816585
theorem B21170297 : Blo 2201435 21170297 := bstep (se 2 (by rfl) ⟨7938861, by rfl⟩ : syracuseStep 21170297 = 15877723) B15877723
theorem B14113531 : Blo 2201435 14113531 := bstep (se 1 (by rfl) ⟨10585148, by rfl⟩ : syracuseStep 14113531 = 21170297) B21170297
theorem B18818041 : Blo 2201435 18818041 := bstep (se 2 (by rfl) ⟨7056765, by rfl⟩ : syracuseStep 18818041 = 14113531) B14113531
theorem B25090721 : Blo 2201435 25090721 := bstep (se 2 (by rfl) ⟨9409020, by rfl⟩ : syracuseStep 25090721 = 18818041) B18818041
theorem B16727147 : Blo 2201435 16727147 := bstep (se 1 (by rfl) ⟨12545360, by rfl⟩ : syracuseStep 16727147 = 25090721) B25090721
theorem B11151431 : Blo 2201435 11151431 := bstep (se 1 (by rfl) ⟨8363573, by rfl⟩ : syracuseStep 11151431 = 16727147) B16727147
theorem B7434287 : Blo 2201435 7434287 := bstep (se 1 (by rfl) ⟨5575715, by rfl⟩ : syracuseStep 7434287 = 11151431) B11151431
theorem B4956191 : Blo 2201435 4956191 := bstep (se 1 (by rfl) ⟨3717143, by rfl⟩ : syracuseStep 4956191 = 7434287) B7434287
theorem B3304127 : Blo 2201435 3304127 := bstep (se 1 (by rfl) ⟨2478095, by rfl⟩ : syracuseStep 3304127 = 4956191) B4956191
theorem B2202751 : Blo 2201435 2202751 := bstep (se 1 (by rfl) ⟨1652063, by rfl⟩ : syracuseStep 2202751 = 3304127) B3304127
theorem B3304133 : Blo 2201435 3304133 := bbase (se 4 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 3304133 = 619525) (by norm_num)
theorem B2202755 : Blo 2201435 2202755 := bstep (se 1 (by rfl) ⟨1652066, by rfl⟩ : syracuseStep 2202755 = 3304133) B3304133
theorem B3717157 : Blo 2201435 3717157 := bbase (se 4 (by rfl) ⟨348483, by rfl⟩ : syracuseStep 3717157 = 696967) (by norm_num)
theorem B4956209 : Blo 2201435 4956209 := bstep (se 2 (by rfl) ⟨1858578, by rfl⟩ : syracuseStep 4956209 = 3717157) B3717157
theorem B3304139 : Blo 2201435 3304139 := bstep (se 1 (by rfl) ⟨2478104, by rfl⟩ : syracuseStep 3304139 = 4956209) B4956209
theorem B2202759 : Blo 2201435 2202759 := bstep (se 1 (by rfl) ⟨1652069, by rfl⟩ : syracuseStep 2202759 = 3304139) B3304139
theorem B2478109 : Blo 2201435 2478109 := bbase (se 3 (by rfl) ⟨464645, by rfl⟩ : syracuseStep 2478109 = 929291) (by norm_num)
theorem B3304145 : Blo 2201435 3304145 := bstep (se 2 (by rfl) ⟨1239054, by rfl⟩ : syracuseStep 3304145 = 2478109) B2478109
theorem B2202763 : Blo 2201435 2202763 := bstep (se 1 (by rfl) ⟨1652072, by rfl⟩ : syracuseStep 2202763 = 3304145) B3304145
theorem B7434341 : Blo 2201435 7434341 := bbase (se 4 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 7434341 = 1393939) (by norm_num)
theorem B4956227 : Blo 2201435 4956227 := bstep (se 1 (by rfl) ⟨3717170, by rfl⟩ : syracuseStep 4956227 = 7434341) B7434341
theorem B3304151 : Blo 2201435 3304151 := bstep (se 1 (by rfl) ⟨2478113, by rfl⟩ : syracuseStep 3304151 = 4956227) B4956227
theorem B2202767 : Blo 2201435 2202767 := bstep (se 1 (by rfl) ⟨1652075, by rfl⟩ : syracuseStep 2202767 = 3304151) B3304151
theorem B3304157 : Blo 2201435 3304157 := bbase (se 3 (by rfl) ⟨619529, by rfl⟩ : syracuseStep 3304157 = 1239059) (by norm_num)
theorem B2202771 : Blo 2201435 2202771 := bstep (se 1 (by rfl) ⟨1652078, by rfl⟩ : syracuseStep 2202771 = 3304157) B3304157
theorem B4956245 : Blo 2201435 4956245 := bbase (se 8 (by rfl) ⟨29040, by rfl⟩ : syracuseStep 4956245 = 58081) (by norm_num)
theorem B3304163 : Blo 2201435 3304163 := bstep (se 1 (by rfl) ⟨2478122, by rfl⟩ : syracuseStep 3304163 = 4956245) B4956245
theorem B2202775 : Blo 2201435 2202775 := bstep (se 1 (by rfl) ⟨1652081, by rfl⟩ : syracuseStep 2202775 = 3304163) B3304163
theorem B7938965 : Blo 2201435 7938965 := bbase (se 6 (by rfl) ⟨186069, by rfl⟩ : syracuseStep 7938965 = 372139) (by norm_num)
theorem B5292643 : Blo 2201435 5292643 := bstep (se 1 (by rfl) ⟨3969482, by rfl⟩ : syracuseStep 5292643 = 7938965) B7938965
theorem B7056857 : Blo 2201435 7056857 := bstep (se 2 (by rfl) ⟨2646321, by rfl⟩ : syracuseStep 7056857 = 5292643) B5292643
theorem B4704571 : Blo 2201435 4704571 := bstep (se 1 (by rfl) ⟨3528428, by rfl⟩ : syracuseStep 4704571 = 7056857) B7056857
theorem B6272761 : Blo 2201435 6272761 := bstep (se 2 (by rfl) ⟨2352285, by rfl⟩ : syracuseStep 6272761 = 4704571) B4704571
theorem B8363681 : Blo 2201435 8363681 := bstep (se 2 (by rfl) ⟨3136380, by rfl⟩ : syracuseStep 8363681 = 6272761) B6272761
theorem B5575787 : Blo 2201435 5575787 := bstep (se 1 (by rfl) ⟨4181840, by rfl⟩ : syracuseStep 5575787 = 8363681) B8363681
theorem B3717191 : Blo 2201435 3717191 := bstep (se 1 (by rfl) ⟨2787893, by rfl⟩ : syracuseStep 3717191 = 5575787) B5575787
theorem B2478127 : Blo 2201435 2478127 := bstep (se 1 (by rfl) ⟨1858595, by rfl⟩ : syracuseStep 2478127 = 3717191) B3717191
theorem B3304169 : Blo 2201435 3304169 := bstep (se 2 (by rfl) ⟨1239063, by rfl⟩ : syracuseStep 3304169 = 2478127) B2478127
theorem B2202779 : Blo 2201435 2202779 := bstep (se 1 (by rfl) ⟨1652084, by rfl⟩ : syracuseStep 2202779 = 3304169) B3304169
theorem B5023885 : Blo 2201435 5023885 := bbase (se 3 (by rfl) ⟨941978, by rfl⟩ : syracuseStep 5023885 = 1883957) (by norm_num)
theorem B6698513 : Blo 2201435 6698513 := bstep (se 2 (by rfl) ⟨2511942, by rfl⟩ : syracuseStep 6698513 = 5023885) B5023885
theorem B4465675 : Blo 2201435 4465675 := bstep (se 1 (by rfl) ⟨3349256, by rfl⟩ : syracuseStep 4465675 = 6698513) B6698513
theorem B5954233 : Blo 2201435 5954233 := bstep (se 2 (by rfl) ⟨2232837, by rfl⟩ : syracuseStep 5954233 = 4465675) B4465675
theorem B7938977 : Blo 2201435 7938977 := bstep (se 2 (by rfl) ⟨2977116, by rfl⟩ : syracuseStep 7938977 = 5954233) B5954233
theorem B21170605 : Blo 2201435 21170605 := bstep (se 3 (by rfl) ⟨3969488, by rfl⟩ : syracuseStep 21170605 = 7938977) B7938977
theorem B28227473 : Blo 2201435 28227473 := bstep (se 2 (by rfl) ⟨10585302, by rfl⟩ : syracuseStep 28227473 = 21170605) B21170605
theorem B18818315 : Blo 2201435 18818315 := bstep (se 1 (by rfl) ⟨14113736, by rfl⟩ : syracuseStep 18818315 = 28227473) B28227473
theorem B12545543 : Blo 2201435 12545543 := bstep (se 1 (by rfl) ⟨9409157, by rfl⟩ : syracuseStep 12545543 = 18818315) B18818315
theorem B8363695 : Blo 2201435 8363695 := bstep (se 1 (by rfl) ⟨6272771, by rfl⟩ : syracuseStep 8363695 = 12545543) B12545543
theorem B11151593 : Blo 2201435 11151593 := bstep (se 2 (by rfl) ⟨4181847, by rfl⟩ : syracuseStep 11151593 = 8363695) B8363695
theorem B7434395 : Blo 2201435 7434395 := bstep (se 1 (by rfl) ⟨5575796, by rfl⟩ : syracuseStep 7434395 = 11151593) B11151593
theorem B4956263 : Blo 2201435 4956263 := bstep (se 1 (by rfl) ⟨3717197, by rfl⟩ : syracuseStep 4956263 = 7434395) B7434395
theorem B3304175 : Blo 2201435 3304175 := bstep (se 1 (by rfl) ⟨2478131, by rfl⟩ : syracuseStep 3304175 = 4956263) B4956263
theorem B2202783 : Blo 2201435 2202783 := bstep (se 1 (by rfl) ⟨1652087, by rfl⟩ : syracuseStep 2202783 = 3304175) B3304175
theorem B3304181 : Blo 2201435 3304181 := bbase (se 5 (by rfl) ⟨154883, by rfl⟩ : syracuseStep 3304181 = 309767) (by norm_num)
theorem B2202787 : Blo 2201435 2202787 := bstep (se 1 (by rfl) ⟨1652090, by rfl⟩ : syracuseStep 2202787 = 3304181) B3304181
theorem B5161925 : Blo 2201435 5161925 := bbase (se 4 (by rfl) ⟨483930, by rfl⟩ : syracuseStep 5161925 = 967861) (by norm_num)
theorem B3441283 : Blo 2201435 3441283 := bstep (se 1 (by rfl) ⟨2580962, by rfl⟩ : syracuseStep 3441283 = 5161925) B5161925
theorem B18353509 : Blo 2201435 18353509 := bstep (se 4 (by rfl) ⟨1720641, by rfl⟩ : syracuseStep 18353509 = 3441283) B3441283
theorem B97885381 : Blo 2201435 97885381 := bstep (se 4 (by rfl) ⟨9176754, by rfl⟩ : syracuseStep 97885381 = 18353509) B18353509
theorem B130513841 : Blo 2201435 130513841 := bstep (se 2 (by rfl) ⟨48942690, by rfl⟩ : syracuseStep 130513841 = 97885381) B97885381
theorem B87009227 : Blo 2201435 87009227 := bstep (se 1 (by rfl) ⟨65256920, by rfl⟩ : syracuseStep 87009227 = 130513841) B130513841
theorem B58006151 : Blo 2201435 58006151 := bstep (se 1 (by rfl) ⟨43504613, by rfl⟩ : syracuseStep 58006151 = 87009227) B87009227
theorem B38670767 : Blo 2201435 38670767 := bstep (se 1 (by rfl) ⟨29003075, by rfl⟩ : syracuseStep 38670767 = 58006151) B58006151
theorem B25780511 : Blo 2201435 25780511 := bstep (se 1 (by rfl) ⟨19335383, by rfl⟩ : syracuseStep 25780511 = 38670767) B38670767
theorem B17187007 : Blo 2201435 17187007 := bstep (se 1 (by rfl) ⟨12890255, by rfl⟩ : syracuseStep 17187007 = 25780511) B25780511
theorem B22916009 : Blo 2201435 22916009 := bstep (se 2 (by rfl) ⟨8593503, by rfl⟩ : syracuseStep 22916009 = 17187007) B17187007
theorem B15277339 : Blo 2201435 15277339 := bstep (se 1 (by rfl) ⟨11458004, by rfl⟩ : syracuseStep 15277339 = 22916009) B22916009
theorem B20369785 : Blo 2201435 20369785 := bstep (se 2 (by rfl) ⟨7638669, by rfl⟩ : syracuseStep 20369785 = 15277339) B15277339
theorem B27159713 : Blo 2201435 27159713 := bstep (se 2 (by rfl) ⟨10184892, by rfl⟩ : syracuseStep 27159713 = 20369785) B20369785
theorem B18106475 : Blo 2201435 18106475 := bstep (se 1 (by rfl) ⟨13579856, by rfl⟩ : syracuseStep 18106475 = 27159713) B27159713
theorem B48283933 : Blo 2201435 48283933 := bstep (se 3 (by rfl) ⟨9053237, by rfl⟩ : syracuseStep 48283933 = 18106475) B18106475
theorem B64378577 : Blo 2201435 64378577 := bstep (se 2 (by rfl) ⟨24141966, by rfl⟩ : syracuseStep 64378577 = 48283933) B48283933
theorem B171676205 : Blo 2201435 171676205 := bstep (se 3 (by rfl) ⟨32189288, by rfl⟩ : syracuseStep 171676205 = 64378577) B64378577
theorem B114450803 : Blo 2201435 114450803 := bstep (se 1 (by rfl) ⟨85838102, by rfl⟩ : syracuseStep 114450803 = 171676205) B171676205
theorem B76300535 : Blo 2201435 76300535 := bstep (se 1 (by rfl) ⟨57225401, by rfl⟩ : syracuseStep 76300535 = 114450803) B114450803
theorem B50867023 : Blo 2201435 50867023 := bstep (se 1 (by rfl) ⟨38150267, by rfl⟩ : syracuseStep 50867023 = 76300535) B76300535
theorem B67822697 : Blo 2201435 67822697 := bstep (se 2 (by rfl) ⟨25433511, by rfl⟩ : syracuseStep 67822697 = 50867023) B50867023
theorem B180860525 : Blo 2201435 180860525 := bstep (se 3 (by rfl) ⟨33911348, by rfl⟩ : syracuseStep 180860525 = 67822697) B67822697
theorem B120573683 : Blo 2201435 120573683 := bstep (se 1 (by rfl) ⟨90430262, by rfl⟩ : syracuseStep 120573683 = 180860525) B180860525
theorem B80382455 : Blo 2201435 80382455 := bstep (se 1 (by rfl) ⟨60286841, by rfl⟩ : syracuseStep 80382455 = 120573683) B120573683
theorem B53588303 : Blo 2201435 53588303 := bstep (se 1 (by rfl) ⟨40191227, by rfl⟩ : syracuseStep 53588303 = 80382455) B80382455
theorem B35725535 : Blo 2201435 35725535 := bstep (se 1 (by rfl) ⟨26794151, by rfl⟩ : syracuseStep 35725535 = 53588303) B53588303
theorem B23817023 : Blo 2201435 23817023 := bstep (se 1 (by rfl) ⟨17862767, by rfl⟩ : syracuseStep 23817023 = 35725535) B35725535
theorem B15878015 : Blo 2201435 15878015 := bstep (se 1 (by rfl) ⟨11908511, by rfl⟩ : syracuseStep 15878015 = 23817023) B23817023
theorem B10585343 : Blo 2201435 10585343 := bstep (se 1 (by rfl) ⟨7939007, by rfl⟩ : syracuseStep 10585343 = 15878015) B15878015
theorem B7056895 : Blo 2201435 7056895 := bstep (se 1 (by rfl) ⟨5292671, by rfl⟩ : syracuseStep 7056895 = 10585343) B10585343
theorem B9409193 : Blo 2201435 9409193 := bstep (se 2 (by rfl) ⟨3528447, by rfl⟩ : syracuseStep 9409193 = 7056895) B7056895
theorem B6272795 : Blo 2201435 6272795 := bstep (se 1 (by rfl) ⟨4704596, by rfl⟩ : syracuseStep 6272795 = 9409193) B9409193
theorem B4181863 : Blo 2201435 4181863 := bstep (se 1 (by rfl) ⟨3136397, by rfl⟩ : syracuseStep 4181863 = 6272795) B6272795
theorem B5575817 : Blo 2201435 5575817 := bstep (se 2 (by rfl) ⟨2090931, by rfl⟩ : syracuseStep 5575817 = 4181863) B4181863
theorem B3717211 : Blo 2201435 3717211 := bstep (se 1 (by rfl) ⟨2787908, by rfl⟩ : syracuseStep 3717211 = 5575817) B5575817
theorem B4956281 : Blo 2201435 4956281 := bstep (se 2 (by rfl) ⟨1858605, by rfl⟩ : syracuseStep 4956281 = 3717211) B3717211
theorem B3304187 : Blo 2201435 3304187 := bstep (se 1 (by rfl) ⟨2478140, by rfl⟩ : syracuseStep 3304187 = 4956281) B4956281
theorem B2202791 : Blo 2201435 2202791 := bstep (se 1 (by rfl) ⟨1652093, by rfl⟩ : syracuseStep 2202791 = 3304187) B3304187
theorem B2478145 : Blo 2201435 2478145 := bbase (se 2 (by rfl) ⟨929304, by rfl⟩ : syracuseStep 2478145 = 1858609) (by norm_num)
theorem B3304193 : Blo 2201435 3304193 := bstep (se 2 (by rfl) ⟨1239072, by rfl⟩ : syracuseStep 3304193 = 2478145) B2478145
theorem B2202795 : Blo 2201435 2202795 := bstep (se 1 (by rfl) ⟨1652096, by rfl⟩ : syracuseStep 2202795 = 3304193) B3304193
theorem B5575837 : Blo 2201435 5575837 := bbase (se 3 (by rfl) ⟨1045469, by rfl⟩ : syracuseStep 5575837 = 2090939) (by norm_num)
theorem B7434449 : Blo 2201435 7434449 := bstep (se 2 (by rfl) ⟨2787918, by rfl⟩ : syracuseStep 7434449 = 5575837) B5575837
theorem B4956299 : Blo 2201435 4956299 := bstep (se 1 (by rfl) ⟨3717224, by rfl⟩ : syracuseStep 4956299 = 7434449) B7434449
theorem B3304199 : Blo 2201435 3304199 := bstep (se 1 (by rfl) ⟨2478149, by rfl⟩ : syracuseStep 3304199 = 4956299) B4956299
theorem B2202799 : Blo 2201435 2202799 := bstep (se 1 (by rfl) ⟨1652099, by rfl⟩ : syracuseStep 2202799 = 3304199) B3304199
theorem B3304205 : Blo 2201435 3304205 := bbase (se 3 (by rfl) ⟨619538, by rfl⟩ : syracuseStep 3304205 = 1239077) (by norm_num)
theorem B2202803 : Blo 2201435 2202803 := bstep (se 1 (by rfl) ⟨1652102, by rfl⟩ : syracuseStep 2202803 = 3304205) B3304205
theorem B4956317 : Blo 2201435 4956317 := bbase (se 3 (by rfl) ⟨929309, by rfl⟩ : syracuseStep 4956317 = 1858619) (by norm_num)
theorem B3304211 : Blo 2201435 3304211 := bstep (se 1 (by rfl) ⟨2478158, by rfl⟩ : syracuseStep 3304211 = 4956317) B4956317
theorem B2202807 : Blo 2201435 2202807 := bstep (se 1 (by rfl) ⟨1652105, by rfl⟩ : syracuseStep 2202807 = 3304211) B3304211
theorem B3717245 : Blo 2201435 3717245 := bbase (se 3 (by rfl) ⟨696983, by rfl⟩ : syracuseStep 3717245 = 1393967) (by norm_num)
theorem B2478163 : Blo 2201435 2478163 := bstep (se 1 (by rfl) ⟨1858622, by rfl⟩ : syracuseStep 2478163 = 3717245) B3717245
theorem B3304217 : Blo 2201435 3304217 := bstep (se 2 (by rfl) ⟨1239081, by rfl⟩ : syracuseStep 3304217 = 2478163) B2478163
theorem B2202811 : Blo 2201435 2202811 := bstep (se 1 (by rfl) ⟨1652108, by rfl⟩ : syracuseStep 2202811 = 3304217) B3304217
theorem B7939093 : Blo 2201435 7939093 := bbase (se 6 (by rfl) ⟨186072, by rfl⟩ : syracuseStep 7939093 = 372145) (by norm_num)
theorem B10585457 : Blo 2201435 10585457 := bstep (se 2 (by rfl) ⟨3969546, by rfl⟩ : syracuseStep 10585457 = 7939093) B7939093
theorem B7056971 : Blo 2201435 7056971 := bstep (se 1 (by rfl) ⟨5292728, by rfl⟩ : syracuseStep 7056971 = 10585457) B10585457
theorem B4704647 : Blo 2201435 4704647 := bstep (se 1 (by rfl) ⟨3528485, by rfl⟩ : syracuseStep 4704647 = 7056971) B7056971
theorem B12545725 : Blo 2201435 12545725 := bstep (se 3 (by rfl) ⟨2352323, by rfl⟩ : syracuseStep 12545725 = 4704647) B4704647
theorem B16727633 : Blo 2201435 16727633 := bstep (se 2 (by rfl) ⟨6272862, by rfl⟩ : syracuseStep 16727633 = 12545725) B12545725
theorem B11151755 : Blo 2201435 11151755 := bstep (se 1 (by rfl) ⟨8363816, by rfl⟩ : syracuseStep 11151755 = 16727633) B16727633
theorem B7434503 : Blo 2201435 7434503 := bstep (se 1 (by rfl) ⟨5575877, by rfl⟩ : syracuseStep 7434503 = 11151755) B11151755
theorem B4956335 : Blo 2201435 4956335 := bstep (se 1 (by rfl) ⟨3717251, by rfl⟩ : syracuseStep 4956335 = 7434503) B7434503
theorem B3304223 : Blo 2201435 3304223 := bstep (se 1 (by rfl) ⟨2478167, by rfl⟩ : syracuseStep 3304223 = 4956335) B4956335
theorem B2202815 : Blo 2201435 2202815 := bstep (se 1 (by rfl) ⟨1652111, by rfl⟩ : syracuseStep 2202815 = 3304223) B3304223
theorem B3304229 : Blo 2201435 3304229 := bbase (se 4 (by rfl) ⟨309771, by rfl⟩ : syracuseStep 3304229 = 619543) (by norm_num)
theorem B2202819 : Blo 2201435 2202819 := bstep (se 1 (by rfl) ⟨1652114, by rfl⟩ : syracuseStep 2202819 = 3304229) B3304229
theorem B2787949 : Blo 2201435 2787949 := bbase (se 3 (by rfl) ⟨522740, by rfl⟩ : syracuseStep 2787949 = 1045481) (by norm_num)
theorem B3717265 : Blo 2201435 3717265 := bstep (se 2 (by rfl) ⟨1393974, by rfl⟩ : syracuseStep 3717265 = 2787949) B2787949
theorem B4956353 : Blo 2201435 4956353 := bstep (se 2 (by rfl) ⟨1858632, by rfl⟩ : syracuseStep 4956353 = 3717265) B3717265
theorem B3304235 : Blo 2201435 3304235 := bstep (se 1 (by rfl) ⟨2478176, by rfl⟩ : syracuseStep 3304235 = 4956353) B4956353
theorem B2202823 : Blo 2201435 2202823 := bstep (se 1 (by rfl) ⟨1652117, by rfl⟩ : syracuseStep 2202823 = 3304235) B3304235
theorem B2478181 : Blo 2201435 2478181 := bbase (se 4 (by rfl) ⟨232329, by rfl⟩ : syracuseStep 2478181 = 464659) (by norm_num)
theorem B3304241 : Blo 2201435 3304241 := bstep (se 2 (by rfl) ⟨1239090, by rfl⟩ : syracuseStep 3304241 = 2478181) B2478181
theorem B2202827 : Blo 2201435 2202827 := bstep (se 1 (by rfl) ⟨1652120, by rfl⟩ : syracuseStep 2202827 = 3304241) B3304241
theorem B2352341 : Blo 2201435 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B6272909 : Blo 2201435 6272909 := bstep (se 3 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 6272909 = 2352341) B2352341
theorem B4181939 : Blo 2201435 4181939 := bstep (se 1 (by rfl) ⟨3136454, by rfl⟩ : syracuseStep 4181939 = 6272909) B6272909
theorem B2787959 : Blo 2201435 2787959 := bstep (se 1 (by rfl) ⟨2090969, by rfl⟩ : syracuseStep 2787959 = 4181939) B4181939
theorem B7434557 : Blo 2201435 7434557 := bstep (se 3 (by rfl) ⟨1393979, by rfl⟩ : syracuseStep 7434557 = 2787959) B2787959
theorem B4956371 : Blo 2201435 4956371 := bstep (se 1 (by rfl) ⟨3717278, by rfl⟩ : syracuseStep 4956371 = 7434557) B7434557
theorem B3304247 : Blo 2201435 3304247 := bstep (se 1 (by rfl) ⟨2478185, by rfl⟩ : syracuseStep 3304247 = 4956371) B4956371
theorem B2202831 : Blo 2201435 2202831 := bstep (se 1 (by rfl) ⟨1652123, by rfl⟩ : syracuseStep 2202831 = 3304247) B3304247
theorem B3304253 : Blo 2201435 3304253 := bbase (se 3 (by rfl) ⟨619547, by rfl⟩ : syracuseStep 3304253 = 1239095) (by norm_num)
theorem B2202835 : Blo 2201435 2202835 := bstep (se 1 (by rfl) ⟨1652126, by rfl⟩ : syracuseStep 2202835 = 3304253) B3304253
theorem B4956389 : Blo 2201435 4956389 := bbase (se 4 (by rfl) ⟨464661, by rfl⟩ : syracuseStep 4956389 = 929323) (by norm_num)
theorem B3304259 : Blo 2201435 3304259 := bstep (se 1 (by rfl) ⟨2478194, by rfl⟩ : syracuseStep 3304259 = 4956389) B4956389
theorem B2202839 : Blo 2201435 2202839 := bstep (se 1 (by rfl) ⟨1652129, by rfl⟩ : syracuseStep 2202839 = 3304259) B3304259
theorem B5575949 : Blo 2201435 5575949 := bbase (se 3 (by rfl) ⟨1045490, by rfl⟩ : syracuseStep 5575949 = 2090981) (by norm_num)
theorem B3717299 : Blo 2201435 3717299 := bstep (se 1 (by rfl) ⟨2787974, by rfl⟩ : syracuseStep 3717299 = 5575949) B5575949
theorem B2478199 : Blo 2201435 2478199 := bstep (se 1 (by rfl) ⟨1858649, by rfl⟩ : syracuseStep 2478199 = 3717299) B3717299
theorem B3304265 : Blo 2201435 3304265 := bstep (se 2 (by rfl) ⟨1239099, by rfl⟩ : syracuseStep 3304265 = 2478199) B2478199
theorem B2202843 : Blo 2201435 2202843 := bstep (se 1 (by rfl) ⟨1652132, by rfl⟩ : syracuseStep 2202843 = 3304265) B3304265
theorem B3136477 : Blo 2201435 3136477 := bbase (se 3 (by rfl) ⟨588089, by rfl⟩ : syracuseStep 3136477 = 1176179) (by norm_num)
theorem B4181969 : Blo 2201435 4181969 := bstep (se 2 (by rfl) ⟨1568238, by rfl⟩ : syracuseStep 4181969 = 3136477) B3136477
theorem B11151917 : Blo 2201435 11151917 := bstep (se 3 (by rfl) ⟨2090984, by rfl⟩ : syracuseStep 11151917 = 4181969) B4181969
theorem B7434611 : Blo 2201435 7434611 := bstep (se 1 (by rfl) ⟨5575958, by rfl⟩ : syracuseStep 7434611 = 11151917) B11151917
theorem B4956407 : Blo 2201435 4956407 := bstep (se 1 (by rfl) ⟨3717305, by rfl⟩ : syracuseStep 4956407 = 7434611) B7434611
theorem B3304271 : Blo 2201435 3304271 := bstep (se 1 (by rfl) ⟨2478203, by rfl⟩ : syracuseStep 3304271 = 4956407) B4956407
theorem B2202847 : Blo 2201435 2202847 := bstep (se 1 (by rfl) ⟨1652135, by rfl⟩ : syracuseStep 2202847 = 3304271) B3304271
theorem B3304277 : Blo 2201435 3304277 := bbase (se 9 (by rfl) ⟨9680, by rfl⟩ : syracuseStep 3304277 = 19361) (by norm_num)
theorem B2202851 : Blo 2201435 2202851 := bstep (se 1 (by rfl) ⟨1652138, by rfl⟩ : syracuseStep 2202851 = 3304277) B3304277
theorem B4704733 : Blo 2201435 4704733 := bbase (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) (by norm_num)
theorem B6272977 : Blo 2201435 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B8363969 : Blo 2201435 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B5575979 : Blo 2201435 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B3717319 : Blo 2201435 3717319 := bstep (se 1 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 3717319 = 5575979) B5575979
theorem B4956425 : Blo 2201435 4956425 := bstep (se 2 (by rfl) ⟨1858659, by rfl⟩ : syracuseStep 4956425 = 3717319) B3717319
theorem B3304283 : Blo 2201435 3304283 := bstep (se 1 (by rfl) ⟨2478212, by rfl⟩ : syracuseStep 3304283 = 4956425) B4956425
theorem B2202855 : Blo 2201435 2202855 := bstep (se 1 (by rfl) ⟨1652141, by rfl⟩ : syracuseStep 2202855 = 3304283) B3304283
theorem B2478217 : Blo 2201435 2478217 := bbase (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) (by norm_num)
theorem B3304289 : Blo 2201435 3304289 := bstep (se 2 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 3304289 = 2478217) B2478217
theorem B2202859 : Blo 2201435 2202859 := bstep (se 1 (by rfl) ⟨1652144, by rfl⟩ : syracuseStep 2202859 = 3304289) B3304289
theorem B4465837 : Blo 2201435 4465837 := bbase (se 3 (by rfl) ⟨837344, by rfl⟩ : syracuseStep 4465837 = 1674689) (by norm_num)
theorem B23817797 : Blo 2201435 23817797 := bstep (se 4 (by rfl) ⟨2232918, by rfl⟩ : syracuseStep 23817797 = 4465837) B4465837
theorem B15878531 : Blo 2201435 15878531 := bstep (se 1 (by rfl) ⟨11908898, by rfl⟩ : syracuseStep 15878531 = 23817797) B23817797
theorem B42342749 : Blo 2201435 42342749 := bstep (se 3 (by rfl) ⟨7939265, by rfl⟩ : syracuseStep 42342749 = 15878531) B15878531
theorem B28228499 : Blo 2201435 28228499 := bstep (se 1 (by rfl) ⟨21171374, by rfl⟩ : syracuseStep 28228499 = 42342749) B42342749
theorem B18818999 : Blo 2201435 18818999 := bstep (se 1 (by rfl) ⟨14114249, by rfl⟩ : syracuseStep 18818999 = 28228499) B28228499
theorem B12545999 : Blo 2201435 12545999 := bstep (se 1 (by rfl) ⟨9409499, by rfl⟩ : syracuseStep 12545999 = 18818999) B18818999
theorem B8363999 : Blo 2201435 8363999 := bstep (se 1 (by rfl) ⟨6272999, by rfl⟩ : syracuseStep 8363999 = 12545999) B12545999
theorem B5575999 : Blo 2201435 5575999 := bstep (se 1 (by rfl) ⟨4181999, by rfl⟩ : syracuseStep 5575999 = 8363999) B8363999
theorem B7434665 : Blo 2201435 7434665 := bstep (se 2 (by rfl) ⟨2787999, by rfl⟩ : syracuseStep 7434665 = 5575999) B5575999
theorem B4956443 : Blo 2201435 4956443 := bstep (se 1 (by rfl) ⟨3717332, by rfl⟩ : syracuseStep 4956443 = 7434665) B7434665
theorem B3304295 : Blo 2201435 3304295 := bstep (se 1 (by rfl) ⟨2478221, by rfl⟩ : syracuseStep 3304295 = 4956443) B4956443
theorem B2202863 : Blo 2201435 2202863 := bstep (se 1 (by rfl) ⟨1652147, by rfl⟩ : syracuseStep 2202863 = 3304295) B3304295
theorem B3304301 : Blo 2201435 3304301 := bbase (se 3 (by rfl) ⟨619556, by rfl⟩ : syracuseStep 3304301 = 1239113) (by norm_num)
theorem B2202867 : Blo 2201435 2202867 := bstep (se 1 (by rfl) ⟨1652150, by rfl⟩ : syracuseStep 2202867 = 3304301) B3304301
theorem B4956461 : Blo 2201435 4956461 := bbase (se 3 (by rfl) ⟨929336, by rfl⟩ : syracuseStep 4956461 = 1858673) (by norm_num)
theorem B3304307 : Blo 2201435 3304307 := bstep (se 1 (by rfl) ⟨2478230, by rfl⟩ : syracuseStep 3304307 = 4956461) B4956461
theorem B2202871 : Blo 2201435 2202871 := bstep (se 1 (by rfl) ⟨1652153, by rfl⟩ : syracuseStep 2202871 = 3304307) B3304307
theorem B2646437 : Blo 2201435 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B7057165 : Blo 2201435 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B9409553 : Blo 2201435 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B6273035 : Blo 2201435 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B4182023 : Blo 2201435 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B2788015 : Blo 2201435 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B3717353 : Blo 2201435 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B2478235 : Blo 2201435 2478235 := bstep (se 1 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 2478235 = 3717353) B3717353
theorem B3304313 : Blo 2201435 3304313 := bstep (se 2 (by rfl) ⟨1239117, by rfl⟩ : syracuseStep 3304313 = 2478235) B2478235
theorem B2202875 : Blo 2201435 2202875 := bstep (se 1 (by rfl) ⟨1652156, by rfl⟩ : syracuseStep 2202875 = 3304313) B3304313
theorem B4023821 : Blo 2201435 4023821 := bbase (se 3 (by rfl) ⟨754466, by rfl⟩ : syracuseStep 4023821 = 1508933) (by norm_num)
theorem B10730189 : Blo 2201435 10730189 := bstep (se 3 (by rfl) ⟨2011910, by rfl⟩ : syracuseStep 10730189 = 4023821) B4023821
theorem B28613837 : Blo 2201435 28613837 := bstep (se 3 (by rfl) ⟨5365094, by rfl⟩ : syracuseStep 28613837 = 10730189) B10730189
theorem B76303565 : Blo 2201435 76303565 := bstep (se 3 (by rfl) ⟨14306918, by rfl⟩ : syracuseStep 76303565 = 28613837) B28613837
theorem B50869043 : Blo 2201435 50869043 := bstep (se 1 (by rfl) ⟨38151782, by rfl⟩ : syracuseStep 50869043 = 76303565) B76303565
theorem B33912695 : Blo 2201435 33912695 := bstep (se 1 (by rfl) ⟨25434521, by rfl⟩ : syracuseStep 33912695 = 50869043) B50869043
theorem B90433853 : Blo 2201435 90433853 := bstep (se 3 (by rfl) ⟨16956347, by rfl⟩ : syracuseStep 90433853 = 33912695) B33912695
theorem B60289235 : Blo 2201435 60289235 := bstep (se 1 (by rfl) ⟨45216926, by rfl⟩ : syracuseStep 60289235 = 90433853) B90433853
theorem B40192823 : Blo 2201435 40192823 := bstep (se 1 (by rfl) ⟨30144617, by rfl⟩ : syracuseStep 40192823 = 60289235) B60289235
theorem B26795215 : Blo 2201435 26795215 := bstep (se 1 (by rfl) ⟨20096411, by rfl⟩ : syracuseStep 26795215 = 40192823) B40192823
theorem B35726953 : Blo 2201435 35726953 := bstep (se 2 (by rfl) ⟨13397607, by rfl⟩ : syracuseStep 35726953 = 26795215) B26795215
theorem B47635937 : Blo 2201435 47635937 := bstep (se 2 (by rfl) ⟨17863476, by rfl⟩ : syracuseStep 47635937 = 35726953) B35726953
theorem B31757291 : Blo 2201435 31757291 := bstep (se 1 (by rfl) ⟨23817968, by rfl⟩ : syracuseStep 31757291 = 47635937) B47635937
theorem B21171527 : Blo 2201435 21171527 := bstep (se 1 (by rfl) ⟨15878645, by rfl⟩ : syracuseStep 21171527 = 31757291) B31757291
theorem B14114351 : Blo 2201435 14114351 := bstep (se 1 (by rfl) ⟨10585763, by rfl⟩ : syracuseStep 14114351 = 21171527) B21171527
theorem B37638269 : Blo 2201435 37638269 := bstep (se 3 (by rfl) ⟨7057175, by rfl⟩ : syracuseStep 37638269 = 14114351) B14114351
theorem B25092179 : Blo 2201435 25092179 := bstep (se 1 (by rfl) ⟨18819134, by rfl⟩ : syracuseStep 25092179 = 37638269) B37638269
theorem B16728119 : Blo 2201435 16728119 := bstep (se 1 (by rfl) ⟨12546089, by rfl⟩ : syracuseStep 16728119 = 25092179) B25092179
theorem B11152079 : Blo 2201435 11152079 := bstep (se 1 (by rfl) ⟨8364059, by rfl⟩ : syracuseStep 11152079 = 16728119) B16728119
theorem B7434719 : Blo 2201435 7434719 := bstep (se 1 (by rfl) ⟨5576039, by rfl⟩ : syracuseStep 7434719 = 11152079) B11152079
theorem B4956479 : Blo 2201435 4956479 := bstep (se 1 (by rfl) ⟨3717359, by rfl⟩ : syracuseStep 4956479 = 7434719) B7434719
theorem B3304319 : Blo 2201435 3304319 := bstep (se 1 (by rfl) ⟨2478239, by rfl⟩ : syracuseStep 3304319 = 4956479) B4956479
theorem B2202879 : Blo 2201435 2202879 := bstep (se 1 (by rfl) ⟨1652159, by rfl⟩ : syracuseStep 2202879 = 3304319) B3304319
theorem B3304325 : Blo 2201435 3304325 := bbase (se 4 (by rfl) ⟨309780, by rfl⟩ : syracuseStep 3304325 = 619561) (by norm_num)
theorem B2202883 : Blo 2201435 2202883 := bstep (se 1 (by rfl) ⟨1652162, by rfl⟩ : syracuseStep 2202883 = 3304325) B3304325
theorem B3717373 : Blo 2201435 3717373 := bbase (se 3 (by rfl) ⟨697007, by rfl⟩ : syracuseStep 3717373 = 1394015) (by norm_num)
theorem B4956497 : Blo 2201435 4956497 := bstep (se 2 (by rfl) ⟨1858686, by rfl⟩ : syracuseStep 4956497 = 3717373) B3717373
theorem B3304331 : Blo 2201435 3304331 := bstep (se 1 (by rfl) ⟨2478248, by rfl⟩ : syracuseStep 3304331 = 4956497) B4956497
theorem B2202887 : Blo 2201435 2202887 := bstep (se 1 (by rfl) ⟨1652165, by rfl⟩ : syracuseStep 2202887 = 3304331) B3304331
theorem B2478253 : Blo 2201435 2478253 := bbase (se 3 (by rfl) ⟨464672, by rfl⟩ : syracuseStep 2478253 = 929345) (by norm_num)
theorem B3304337 : Blo 2201435 3304337 := bstep (se 2 (by rfl) ⟨1239126, by rfl⟩ : syracuseStep 3304337 = 2478253) B2478253
theorem B2202891 : Blo 2201435 2202891 := bstep (se 1 (by rfl) ⟨1652168, by rfl⟩ : syracuseStep 2202891 = 3304337) B3304337
theorem B7434773 : Blo 2201435 7434773 := bbase (se 6 (by rfl) ⟨174252, by rfl⟩ : syracuseStep 7434773 = 348505) (by norm_num)
theorem B4956515 : Blo 2201435 4956515 := bstep (se 1 (by rfl) ⟨3717386, by rfl⟩ : syracuseStep 4956515 = 7434773) B7434773
theorem B3304343 : Blo 2201435 3304343 := bstep (se 1 (by rfl) ⟨2478257, by rfl⟩ : syracuseStep 3304343 = 4956515) B4956515
theorem B2202895 : Blo 2201435 2202895 := bstep (se 1 (by rfl) ⟨1652171, by rfl⟩ : syracuseStep 2202895 = 3304343) B3304343
theorem B3304349 : Blo 2201435 3304349 := bbase (se 3 (by rfl) ⟨619565, by rfl⟩ : syracuseStep 3304349 = 1239131) (by norm_num)
theorem B2202899 : Blo 2201435 2202899 := bstep (se 1 (by rfl) ⟨1652174, by rfl⟩ : syracuseStep 2202899 = 3304349) B3304349
theorem B4956533 : Blo 2201435 4956533 := bbase (se 5 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 4956533 = 464675) (by norm_num)
theorem B3304355 : Blo 2201435 3304355 := bstep (se 1 (by rfl) ⟨2478266, by rfl⟩ : syracuseStep 3304355 = 4956533) B4956533
theorem B2202903 : Blo 2201435 2202903 := bstep (se 1 (by rfl) ⟨1652177, by rfl⟩ : syracuseStep 2202903 = 3304355) B3304355
theorem B2977285 : Blo 2201435 2977285 := bbase (se 4 (by rfl) ⟨279120, by rfl⟩ : syracuseStep 2977285 = 558241) (by norm_num)
theorem B3969713 : Blo 2201435 3969713 := bstep (se 2 (by rfl) ⟨1488642, by rfl⟩ : syracuseStep 3969713 = 2977285) B2977285
theorem B2646475 : Blo 2201435 2646475 := bstep (se 1 (by rfl) ⟨1984856, by rfl⟩ : syracuseStep 2646475 = 3969713) B3969713
theorem B14114533 : Blo 2201435 14114533 := bstep (se 4 (by rfl) ⟨1323237, by rfl⟩ : syracuseStep 14114533 = 2646475) B2646475
theorem B18819377 : Blo 2201435 18819377 := bstep (se 2 (by rfl) ⟨7057266, by rfl⟩ : syracuseStep 18819377 = 14114533) B14114533
theorem B12546251 : Blo 2201435 12546251 := bstep (se 1 (by rfl) ⟨9409688, by rfl⟩ : syracuseStep 12546251 = 18819377) B18819377
theorem B8364167 : Blo 2201435 8364167 := bstep (se 1 (by rfl) ⟨6273125, by rfl⟩ : syracuseStep 8364167 = 12546251) B12546251
theorem B5576111 : Blo 2201435 5576111 := bstep (se 1 (by rfl) ⟨4182083, by rfl⟩ : syracuseStep 5576111 = 8364167) B8364167
theorem B3717407 : Blo 2201435 3717407 := bstep (se 1 (by rfl) ⟨2788055, by rfl⟩ : syracuseStep 3717407 = 5576111) B5576111
theorem B2478271 : Blo 2201435 2478271 := bstep (se 1 (by rfl) ⟨1858703, by rfl⟩ : syracuseStep 2478271 = 3717407) B3717407
theorem B3304361 : Blo 2201435 3304361 := bstep (se 2 (by rfl) ⟨1239135, by rfl⟩ : syracuseStep 3304361 = 2478271) B2478271
theorem B2202907 : Blo 2201435 2202907 := bstep (se 1 (by rfl) ⟨1652180, by rfl⟩ : syracuseStep 2202907 = 3304361) B3304361
theorem B8364181 : Blo 2201435 8364181 := bbase (se 6 (by rfl) ⟨196035, by rfl⟩ : syracuseStep 8364181 = 392071) (by norm_num)
theorem B11152241 : Blo 2201435 11152241 := bstep (se 2 (by rfl) ⟨4182090, by rfl⟩ : syracuseStep 11152241 = 8364181) B8364181
theorem B7434827 : Blo 2201435 7434827 := bstep (se 1 (by rfl) ⟨5576120, by rfl⟩ : syracuseStep 7434827 = 11152241) B11152241
theorem B4956551 : Blo 2201435 4956551 := bstep (se 1 (by rfl) ⟨3717413, by rfl⟩ : syracuseStep 4956551 = 7434827) B7434827
theorem B3304367 : Blo 2201435 3304367 := bstep (se 1 (by rfl) ⟨2478275, by rfl⟩ : syracuseStep 3304367 = 4956551) B4956551
theorem B2202911 : Blo 2201435 2202911 := bstep (se 1 (by rfl) ⟨1652183, by rfl⟩ : syracuseStep 2202911 = 3304367) B3304367
theorem B3304373 : Blo 2201435 3304373 := bbase (se 5 (by rfl) ⟨154892, by rfl⟩ : syracuseStep 3304373 = 309785) (by norm_num)
theorem B2202915 : Blo 2201435 2202915 := bstep (se 1 (by rfl) ⟨1652186, by rfl⟩ : syracuseStep 2202915 = 3304373) B3304373
theorem B5576141 : Blo 2201435 5576141 := bbase (se 3 (by rfl) ⟨1045526, by rfl⟩ : syracuseStep 5576141 = 2091053) (by norm_num)
theorem B3717427 : Blo 2201435 3717427 := bstep (se 1 (by rfl) ⟨2788070, by rfl⟩ : syracuseStep 3717427 = 5576141) B5576141
theorem B4956569 : Blo 2201435 4956569 := bstep (se 2 (by rfl) ⟨1858713, by rfl⟩ : syracuseStep 4956569 = 3717427) B3717427
theorem B3304379 : Blo 2201435 3304379 := bstep (se 1 (by rfl) ⟨2478284, by rfl⟩ : syracuseStep 3304379 = 4956569) B4956569
theorem B2202919 : Blo 2201435 2202919 := bstep (se 1 (by rfl) ⟨1652189, by rfl⟩ : syracuseStep 2202919 = 3304379) B3304379
theorem B2478289 : Blo 2201435 2478289 := bbase (se 2 (by rfl) ⟨929358, by rfl⟩ : syracuseStep 2478289 = 1858717) (by norm_num)
theorem B3304385 : Blo 2201435 3304385 := bstep (se 2 (by rfl) ⟨1239144, by rfl⟩ : syracuseStep 3304385 = 2478289) B2478289
theorem B2202923 : Blo 2201435 2202923 := bstep (se 1 (by rfl) ⟨1652192, by rfl⟩ : syracuseStep 2202923 = 3304385) B3304385
theorem B3969749 : Blo 2201435 3969749 := bbase (se 7 (by rfl) ⟨46520, by rfl⟩ : syracuseStep 3969749 = 93041) (by norm_num)
theorem B10585997 : Blo 2201435 10585997 := bstep (se 3 (by rfl) ⟨1984874, by rfl⟩ : syracuseStep 10585997 = 3969749) B3969749
theorem B7057331 : Blo 2201435 7057331 := bstep (se 1 (by rfl) ⟨5292998, by rfl⟩ : syracuseStep 7057331 = 10585997) B10585997
theorem B4704887 : Blo 2201435 4704887 := bstep (se 1 (by rfl) ⟨3528665, by rfl⟩ : syracuseStep 4704887 = 7057331) B7057331
theorem B3136591 : Blo 2201435 3136591 := bstep (se 1 (by rfl) ⟨2352443, by rfl⟩ : syracuseStep 3136591 = 4704887) B4704887
theorem B4182121 : Blo 2201435 4182121 := bstep (se 2 (by rfl) ⟨1568295, by rfl⟩ : syracuseStep 4182121 = 3136591) B3136591
theorem B5576161 : Blo 2201435 5576161 := bstep (se 2 (by rfl) ⟨2091060, by rfl⟩ : syracuseStep 5576161 = 4182121) B4182121
theorem B7434881 : Blo 2201435 7434881 := bstep (se 2 (by rfl) ⟨2788080, by rfl⟩ : syracuseStep 7434881 = 5576161) B5576161
theorem B4956587 : Blo 2201435 4956587 := bstep (se 1 (by rfl) ⟨3717440, by rfl⟩ : syracuseStep 4956587 = 7434881) B7434881
theorem B3304391 : Blo 2201435 3304391 := bstep (se 1 (by rfl) ⟨2478293, by rfl⟩ : syracuseStep 3304391 = 4956587) B4956587
theorem B2202927 : Blo 2201435 2202927 := bstep (se 1 (by rfl) ⟨1652195, by rfl⟩ : syracuseStep 2202927 = 3304391) B3304391
theorem B3304397 : Blo 2201435 3304397 := bbase (se 3 (by rfl) ⟨619574, by rfl⟩ : syracuseStep 3304397 = 1239149) (by norm_num)
theorem B2202931 : Blo 2201435 2202931 := bstep (se 1 (by rfl) ⟨1652198, by rfl⟩ : syracuseStep 2202931 = 3304397) B3304397
theorem B4956605 : Blo 2201435 4956605 := bbase (se 3 (by rfl) ⟨929363, by rfl⟩ : syracuseStep 4956605 = 1858727) (by norm_num)
theorem B3304403 : Blo 2201435 3304403 := bstep (se 1 (by rfl) ⟨2478302, by rfl⟩ : syracuseStep 3304403 = 4956605) B4956605
theorem B2202935 : Blo 2201435 2202935 := bstep (se 1 (by rfl) ⟨1652201, by rfl⟩ : syracuseStep 2202935 = 3304403) B3304403
theorem B3717461 : Blo 2201435 3717461 := bbase (se 10 (by rfl) ⟨5445, by rfl⟩ : syracuseStep 3717461 = 10891) (by norm_num)
theorem B2478307 : Blo 2201435 2478307 := bstep (se 1 (by rfl) ⟨1858730, by rfl⟩ : syracuseStep 2478307 = 3717461) B3717461
theorem B3304409 : Blo 2201435 3304409 := bstep (se 2 (by rfl) ⟨1239153, by rfl⟩ : syracuseStep 3304409 = 2478307) B2478307
theorem B2202939 : Blo 2201435 2202939 := bstep (se 1 (by rfl) ⟨1652204, by rfl⟩ : syracuseStep 2202939 = 3304409) B3304409
theorem B7057381 : Blo 2201435 7057381 := bbase (se 4 (by rfl) ⟨661629, by rfl⟩ : syracuseStep 7057381 = 1323259) (by norm_num)
theorem B9409841 : Blo 2201435 9409841 := bstep (se 2 (by rfl) ⟨3528690, by rfl⟩ : syracuseStep 9409841 = 7057381) B7057381
theorem B6273227 : Blo 2201435 6273227 := bstep (se 1 (by rfl) ⟨4704920, by rfl⟩ : syracuseStep 6273227 = 9409841) B9409841
theorem B16728605 : Blo 2201435 16728605 := bstep (se 3 (by rfl) ⟨3136613, by rfl⟩ : syracuseStep 16728605 = 6273227) B6273227
theorem B11152403 : Blo 2201435 11152403 := bstep (se 1 (by rfl) ⟨8364302, by rfl⟩ : syracuseStep 11152403 = 16728605) B16728605
theorem B7434935 : Blo 2201435 7434935 := bstep (se 1 (by rfl) ⟨5576201, by rfl⟩ : syracuseStep 7434935 = 11152403) B11152403
theorem B4956623 : Blo 2201435 4956623 := bstep (se 1 (by rfl) ⟨3717467, by rfl⟩ : syracuseStep 4956623 = 7434935) B7434935
theorem B3304415 : Blo 2201435 3304415 := bstep (se 1 (by rfl) ⟨2478311, by rfl⟩ : syracuseStep 3304415 = 4956623) B4956623
theorem B2202943 : Blo 2201435 2202943 := bstep (se 1 (by rfl) ⟨1652207, by rfl⟩ : syracuseStep 2202943 = 3304415) B3304415
theorem B3304421 : Blo 2201435 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B2202947 : Blo 2201435 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B9409877 : Blo 2201435 9409877 := bbase (se 14 (by rfl) ⟨861, by rfl⟩ : syracuseStep 9409877 = 1723) (by norm_num)
theorem B6273251 : Blo 2201435 6273251 := bstep (se 1 (by rfl) ⟨4704938, by rfl⟩ : syracuseStep 6273251 = 9409877) B9409877
theorem B4182167 : Blo 2201435 4182167 := bstep (se 1 (by rfl) ⟨3136625, by rfl⟩ : syracuseStep 4182167 = 6273251) B6273251
theorem B2788111 : Blo 2201435 2788111 := bstep (se 1 (by rfl) ⟨2091083, by rfl⟩ : syracuseStep 2788111 = 4182167) B4182167
theorem B3717481 : Blo 2201435 3717481 := bstep (se 2 (by rfl) ⟨1394055, by rfl⟩ : syracuseStep 3717481 = 2788111) B2788111
theorem B4956641 : Blo 2201435 4956641 := bstep (se 2 (by rfl) ⟨1858740, by rfl⟩ : syracuseStep 4956641 = 3717481) B3717481
theorem B3304427 : Blo 2201435 3304427 := bstep (se 1 (by rfl) ⟨2478320, by rfl⟩ : syracuseStep 3304427 = 4956641) B4956641
theorem B2202951 : Blo 2201435 2202951 := bstep (se 1 (by rfl) ⟨1652213, by rfl⟩ : syracuseStep 2202951 = 3304427) B3304427
theorem B2478325 : Blo 2201435 2478325 := bbase (se 5 (by rfl) ⟨116171, by rfl⟩ : syracuseStep 2478325 = 232343) (by norm_num)
theorem B3304433 : Blo 2201435 3304433 := bstep (se 2 (by rfl) ⟨1239162, by rfl⟩ : syracuseStep 3304433 = 2478325) B2478325
theorem B2202955 : Blo 2201435 2202955 := bstep (se 1 (by rfl) ⟨1652216, by rfl⟩ : syracuseStep 2202955 = 3304433) B3304433
theorem B2788121 : Blo 2201435 2788121 := bbase (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) (by norm_num)
theorem B7434989 : Blo 2201435 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B4956659 : Blo 2201435 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B3304439 : Blo 2201435 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B2202959 : Blo 2201435 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B3304445 : Blo 2201435 3304445 := bbase (se 3 (by rfl) ⟨619583, by rfl⟩ : syracuseStep 3304445 = 1239167) (by norm_num)
theorem B2202963 : Blo 2201435 2202963 := bstep (se 1 (by rfl) ⟨1652222, by rfl⟩ : syracuseStep 2202963 = 3304445) B3304445
theorem B4956677 : Blo 2201435 4956677 := bbase (se 4 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 4956677 = 929377) (by norm_num)
theorem B3304451 : Blo 2201435 3304451 := bstep (se 1 (by rfl) ⟨2478338, by rfl⟩ : syracuseStep 3304451 = 4956677) B4956677
theorem B2202967 : Blo 2201435 2202967 := bstep (se 1 (by rfl) ⟨1652225, by rfl⟩ : syracuseStep 2202967 = 3304451) B3304451
theorem B4182205 : Blo 2201435 4182205 := bbase (se 3 (by rfl) ⟨784163, by rfl⟩ : syracuseStep 4182205 = 1568327) (by norm_num)
theorem B5576273 : Blo 2201435 5576273 := bstep (se 2 (by rfl) ⟨2091102, by rfl⟩ : syracuseStep 5576273 = 4182205) B4182205
theorem B3717515 : Blo 2201435 3717515 := bstep (se 1 (by rfl) ⟨2788136, by rfl⟩ : syracuseStep 3717515 = 5576273) B5576273
theorem B2478343 : Blo 2201435 2478343 := bstep (se 1 (by rfl) ⟨1858757, by rfl⟩ : syracuseStep 2478343 = 3717515) B3717515
theorem B3304457 : Blo 2201435 3304457 := bstep (se 2 (by rfl) ⟨1239171, by rfl⟩ : syracuseStep 3304457 = 2478343) B2478343
theorem B2202971 : Blo 2201435 2202971 := bstep (se 1 (by rfl) ⟨1652228, by rfl⟩ : syracuseStep 2202971 = 3304457) B3304457
theorem B11152565 : Blo 2201435 11152565 := bbase (se 5 (by rfl) ⟨522776, by rfl⟩ : syracuseStep 11152565 = 1045553) (by norm_num)
theorem B7435043 : Blo 2201435 7435043 := bstep (se 1 (by rfl) ⟨5576282, by rfl⟩ : syracuseStep 7435043 = 11152565) B11152565
theorem B4956695 : Blo 2201435 4956695 := bstep (se 1 (by rfl) ⟨3717521, by rfl⟩ : syracuseStep 4956695 = 7435043) B7435043
theorem B3304463 : Blo 2201435 3304463 := bstep (se 1 (by rfl) ⟨2478347, by rfl⟩ : syracuseStep 3304463 = 4956695) B4956695
theorem B2202975 : Blo 2201435 2202975 := bstep (se 1 (by rfl) ⟨1652231, by rfl⟩ : syracuseStep 2202975 = 3304463) B3304463
theorem B3304469 : Blo 2201435 3304469 := bbase (se 6 (by rfl) ⟨77448, by rfl⟩ : syracuseStep 3304469 = 154897) (by norm_num)
theorem B2202979 : Blo 2201435 2202979 := bstep (se 1 (by rfl) ⟨1652234, by rfl⟩ : syracuseStep 2202979 = 3304469) B3304469
theorem B2826193 : Blo 2201435 2826193 := bbase (se 2 (by rfl) ⟨1059822, by rfl⟩ : syracuseStep 2826193 = 2119645) (by norm_num)
theorem B3768257 : Blo 2201435 3768257 := bstep (se 2 (by rfl) ⟨1413096, by rfl⟩ : syracuseStep 3768257 = 2826193) B2826193
theorem B2512171 : Blo 2201435 2512171 := bstep (se 1 (by rfl) ⟨1884128, by rfl⟩ : syracuseStep 2512171 = 3768257) B3768257
theorem B3349561 : Blo 2201435 3349561 := bstep (se 2 (by rfl) ⟨1256085, by rfl⟩ : syracuseStep 3349561 = 2512171) B2512171
theorem B4466081 : Blo 2201435 4466081 := bstep (se 2 (by rfl) ⟨1674780, by rfl⟩ : syracuseStep 4466081 = 3349561) B3349561
theorem B2977387 : Blo 2201435 2977387 := bstep (se 1 (by rfl) ⟨2233040, by rfl⟩ : syracuseStep 2977387 = 4466081) B4466081
theorem B15879397 : Blo 2201435 15879397 := bstep (se 4 (by rfl) ⟨1488693, by rfl⟩ : syracuseStep 15879397 = 2977387) B2977387
theorem B21172529 : Blo 2201435 21172529 := bstep (se 2 (by rfl) ⟨7939698, by rfl⟩ : syracuseStep 21172529 = 15879397) B15879397
theorem B14115019 : Blo 2201435 14115019 := bstep (se 1 (by rfl) ⟨10586264, by rfl⟩ : syracuseStep 14115019 = 21172529) B21172529
theorem B18820025 : Blo 2201435 18820025 := bstep (se 2 (by rfl) ⟨7057509, by rfl⟩ : syracuseStep 18820025 = 14115019) B14115019
theorem B12546683 : Blo 2201435 12546683 := bstep (se 1 (by rfl) ⟨9410012, by rfl⟩ : syracuseStep 12546683 = 18820025) B18820025
theorem B8364455 : Blo 2201435 8364455 := bstep (se 1 (by rfl) ⟨6273341, by rfl⟩ : syracuseStep 8364455 = 12546683) B12546683
theorem B5576303 : Blo 2201435 5576303 := bstep (se 1 (by rfl) ⟨4182227, by rfl⟩ : syracuseStep 5576303 = 8364455) B8364455
theorem B3717535 : Blo 2201435 3717535 := bstep (se 1 (by rfl) ⟨2788151, by rfl⟩ : syracuseStep 3717535 = 5576303) B5576303
theorem B4956713 : Blo 2201435 4956713 := bstep (se 2 (by rfl) ⟨1858767, by rfl⟩ : syracuseStep 4956713 = 3717535) B3717535
theorem B3304475 : Blo 2201435 3304475 := bstep (se 1 (by rfl) ⟨2478356, by rfl⟩ : syracuseStep 3304475 = 4956713) B4956713
theorem B2202983 : Blo 2201435 2202983 := bstep (se 1 (by rfl) ⟨1652237, by rfl⟩ : syracuseStep 2202983 = 3304475) B3304475
theorem B2478361 : Blo 2201435 2478361 := bbase (se 2 (by rfl) ⟨929385, by rfl⟩ : syracuseStep 2478361 = 1858771) (by norm_num)
theorem B3304481 : Blo 2201435 3304481 := bstep (se 2 (by rfl) ⟨1239180, by rfl⟩ : syracuseStep 3304481 = 2478361) B2478361
theorem B2202987 : Blo 2201435 2202987 := bstep (se 1 (by rfl) ⟨1652240, by rfl⟩ : syracuseStep 2202987 = 3304481) B3304481
theorem B8364485 : Blo 2201435 8364485 := bbase (se 4 (by rfl) ⟨784170, by rfl⟩ : syracuseStep 8364485 = 1568341) (by norm_num)
theorem B5576323 : Blo 2201435 5576323 := bstep (se 1 (by rfl) ⟨4182242, by rfl⟩ : syracuseStep 5576323 = 8364485) B8364485
theorem B7435097 : Blo 2201435 7435097 := bstep (se 2 (by rfl) ⟨2788161, by rfl⟩ : syracuseStep 7435097 = 5576323) B5576323
theorem B4956731 : Blo 2201435 4956731 := bstep (se 1 (by rfl) ⟨3717548, by rfl⟩ : syracuseStep 4956731 = 7435097) B7435097
theorem B3304487 : Blo 2201435 3304487 := bstep (se 1 (by rfl) ⟨2478365, by rfl⟩ : syracuseStep 3304487 = 4956731) B4956731
theorem B2202991 : Blo 2201435 2202991 := bstep (se 1 (by rfl) ⟨1652243, by rfl⟩ : syracuseStep 2202991 = 3304487) B3304487
theorem B3304493 : Blo 2201435 3304493 := bbase (se 3 (by rfl) ⟨619592, by rfl⟩ : syracuseStep 3304493 = 1239185) (by norm_num)
theorem B2202995 : Blo 2201435 2202995 := bstep (se 1 (by rfl) ⟨1652246, by rfl⟩ : syracuseStep 2202995 = 3304493) B3304493
theorem B4956749 : Blo 2201435 4956749 := bbase (se 3 (by rfl) ⟨929390, by rfl⟩ : syracuseStep 4956749 = 1858781) (by norm_num)
theorem B3304499 : Blo 2201435 3304499 := bstep (se 1 (by rfl) ⟨2478374, by rfl⟩ : syracuseStep 3304499 = 4956749) B4956749
theorem B2202999 : Blo 2201435 2202999 := bstep (se 1 (by rfl) ⟨1652249, by rfl⟩ : syracuseStep 2202999 = 3304499) B3304499
theorem B2788177 : Blo 2201435 2788177 := bbase (se 2 (by rfl) ⟨1045566, by rfl⟩ : syracuseStep 2788177 = 2091133) (by norm_num)
theorem B3717569 : Blo 2201435 3717569 := bstep (se 2 (by rfl) ⟨1394088, by rfl⟩ : syracuseStep 3717569 = 2788177) B2788177
theorem B2478379 : Blo 2201435 2478379 := bstep (se 1 (by rfl) ⟨1858784, by rfl⟩ : syracuseStep 2478379 = 3717569) B3717569
theorem B3304505 : Blo 2201435 3304505 := bstep (se 2 (by rfl) ⟨1239189, by rfl⟩ : syracuseStep 3304505 = 2478379) B2478379
theorem B2203003 : Blo 2201435 2203003 := bstep (se 1 (by rfl) ⟨1652252, by rfl⟩ : syracuseStep 2203003 = 3304505) B3304505
theorem B3969893 : Blo 2201435 3969893 := bbase (se 4 (by rfl) ⟨372177, by rfl⟩ : syracuseStep 3969893 = 744355) (by norm_num)
theorem B2646595 : Blo 2201435 2646595 := bstep (se 1 (by rfl) ⟨1984946, by rfl⟩ : syracuseStep 2646595 = 3969893) B3969893
theorem B3528793 : Blo 2201435 3528793 := bstep (se 2 (by rfl) ⟨1323297, by rfl⟩ : syracuseStep 3528793 = 2646595) B2646595
theorem B4705057 : Blo 2201435 4705057 := bstep (se 2 (by rfl) ⟨1764396, by rfl⟩ : syracuseStep 4705057 = 3528793) B3528793
theorem B25093637 : Blo 2201435 25093637 := bstep (se 4 (by rfl) ⟨2352528, by rfl⟩ : syracuseStep 25093637 = 4705057) B4705057
theorem B16729091 : Blo 2201435 16729091 := bstep (se 1 (by rfl) ⟨12546818, by rfl⟩ : syracuseStep 16729091 = 25093637) B25093637
theorem B11152727 : Blo 2201435 11152727 := bstep (se 1 (by rfl) ⟨8364545, by rfl⟩ : syracuseStep 11152727 = 16729091) B16729091
theorem B7435151 : Blo 2201435 7435151 := bstep (se 1 (by rfl) ⟨5576363, by rfl⟩ : syracuseStep 7435151 = 11152727) B11152727
theorem B4956767 : Blo 2201435 4956767 := bstep (se 1 (by rfl) ⟨3717575, by rfl⟩ : syracuseStep 4956767 = 7435151) B7435151
theorem B3304511 : Blo 2201435 3304511 := bstep (se 1 (by rfl) ⟨2478383, by rfl⟩ : syracuseStep 3304511 = 4956767) B4956767
theorem B2203007 : Blo 2201435 2203007 := bstep (se 1 (by rfl) ⟨1652255, by rfl⟩ : syracuseStep 2203007 = 3304511) B3304511
theorem B3304517 : Blo 2201435 3304517 := bbase (se 4 (by rfl) ⟨309798, by rfl⟩ : syracuseStep 3304517 = 619597) (by norm_num)
theorem B2203011 : Blo 2201435 2203011 := bstep (se 1 (by rfl) ⟨1652258, by rfl⟩ : syracuseStep 2203011 = 3304517) B3304517
theorem B3717589 : Blo 2201435 3717589 := bbase (se 7 (by rfl) ⟨43565, by rfl⟩ : syracuseStep 3717589 = 87131) (by norm_num)
theorem B4956785 : Blo 2201435 4956785 := bstep (se 2 (by rfl) ⟨1858794, by rfl⟩ : syracuseStep 4956785 = 3717589) B3717589
theorem B3304523 : Blo 2201435 3304523 := bstep (se 1 (by rfl) ⟨2478392, by rfl⟩ : syracuseStep 3304523 = 4956785) B4956785
theorem B2203015 : Blo 2201435 2203015 := bstep (se 1 (by rfl) ⟨1652261, by rfl⟩ : syracuseStep 2203015 = 3304523) B3304523
theorem B2478397 : Blo 2201435 2478397 := bbase (se 3 (by rfl) ⟨464699, by rfl⟩ : syracuseStep 2478397 = 929399) (by norm_num)
theorem B3304529 : Blo 2201435 3304529 := bstep (se 2 (by rfl) ⟨1239198, by rfl⟩ : syracuseStep 3304529 = 2478397) B2478397
theorem B2203019 : Blo 2201435 2203019 := bstep (se 1 (by rfl) ⟨1652264, by rfl⟩ : syracuseStep 2203019 = 3304529) B3304529
theorem B7435205 : Blo 2201435 7435205 := bbase (se 4 (by rfl) ⟨697050, by rfl⟩ : syracuseStep 7435205 = 1394101) (by norm_num)
theorem B4956803 : Blo 2201435 4956803 := bstep (se 1 (by rfl) ⟨3717602, by rfl⟩ : syracuseStep 4956803 = 7435205) B7435205
theorem B3304535 : Blo 2201435 3304535 := bstep (se 1 (by rfl) ⟨2478401, by rfl⟩ : syracuseStep 3304535 = 4956803) B4956803
theorem B2203023 : Blo 2201435 2203023 := bstep (se 1 (by rfl) ⟨1652267, by rfl⟩ : syracuseStep 2203023 = 3304535) B3304535
theorem B3304541 : Blo 2201435 3304541 := bbase (se 3 (by rfl) ⟨619601, by rfl⟩ : syracuseStep 3304541 = 1239203) (by norm_num)
theorem B2203027 : Blo 2201435 2203027 := bstep (se 1 (by rfl) ⟨1652270, by rfl⟩ : syracuseStep 2203027 = 3304541) B3304541
theorem B4956821 : Blo 2201435 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B3304547 : Blo 2201435 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B2203031 : Blo 2201435 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B5954917 : Blo 2201435 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B7939889 : Blo 2201435 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B5293259 : Blo 2201435 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B3528839 : Blo 2201435 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B2352559 : Blo 2201435 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B3136745 : Blo 2201435 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B8364653 : Blo 2201435 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B5576435 : Blo 2201435 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B3717623 : Blo 2201435 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B2478415 : Blo 2201435 2478415 := bstep (se 1 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 2478415 = 3717623) B3717623
theorem B3304553 : Blo 2201435 3304553 := bstep (se 2 (by rfl) ⟨1239207, by rfl⟩ : syracuseStep 3304553 = 2478415) B2478415
theorem B2203035 : Blo 2201435 2203035 := bstep (se 1 (by rfl) ⟨1652276, by rfl⟩ : syracuseStep 2203035 = 3304553) B3304553
theorem B10586533 : Blo 2201435 10586533 := bbase (se 4 (by rfl) ⟨992487, by rfl⟩ : syracuseStep 10586533 = 1984975) (by norm_num)
theorem B14115377 : Blo 2201435 14115377 := bstep (se 2 (by rfl) ⟨5293266, by rfl⟩ : syracuseStep 14115377 = 10586533) B10586533
theorem B9410251 : Blo 2201435 9410251 := bstep (se 1 (by rfl) ⟨7057688, by rfl⟩ : syracuseStep 9410251 = 14115377) B14115377
theorem B12547001 : Blo 2201435 12547001 := bstep (se 2 (by rfl) ⟨4705125, by rfl⟩ : syracuseStep 12547001 = 9410251) B9410251
theorem B8364667 : Blo 2201435 8364667 := bstep (se 1 (by rfl) ⟨6273500, by rfl⟩ : syracuseStep 8364667 = 12547001) B12547001
theorem B11152889 : Blo 2201435 11152889 := bstep (se 2 (by rfl) ⟨4182333, by rfl⟩ : syracuseStep 11152889 = 8364667) B8364667
theorem B7435259 : Blo 2201435 7435259 := bstep (se 1 (by rfl) ⟨5576444, by rfl⟩ : syracuseStep 7435259 = 11152889) B11152889
theorem B4956839 : Blo 2201435 4956839 := bstep (se 1 (by rfl) ⟨3717629, by rfl⟩ : syracuseStep 4956839 = 7435259) B7435259
theorem B3304559 : Blo 2201435 3304559 := bstep (se 1 (by rfl) ⟨2478419, by rfl⟩ : syracuseStep 3304559 = 4956839) B4956839
theorem B2203039 : Blo 2201435 2203039 := bstep (se 1 (by rfl) ⟨1652279, by rfl⟩ : syracuseStep 2203039 = 3304559) B3304559
theorem B3304565 : Blo 2201435 3304565 := bbase (se 5 (by rfl) ⟨154901, by rfl⟩ : syracuseStep 3304565 = 309803) (by norm_num)
theorem B2203043 : Blo 2201435 2203043 := bstep (se 1 (by rfl) ⟨1652282, by rfl⟩ : syracuseStep 2203043 = 3304565) B3304565
theorem B4182349 : Blo 2201435 4182349 := bbase (se 3 (by rfl) ⟨784190, by rfl⟩ : syracuseStep 4182349 = 1568381) (by norm_num)
theorem B5576465 : Blo 2201435 5576465 := bstep (se 2 (by rfl) ⟨2091174, by rfl⟩ : syracuseStep 5576465 = 4182349) B4182349
theorem B3717643 : Blo 2201435 3717643 := bstep (se 1 (by rfl) ⟨2788232, by rfl⟩ : syracuseStep 3717643 = 5576465) B5576465
theorem B4956857 : Blo 2201435 4956857 := bstep (se 2 (by rfl) ⟨1858821, by rfl⟩ : syracuseStep 4956857 = 3717643) B3717643
theorem B3304571 : Blo 2201435 3304571 := bstep (se 1 (by rfl) ⟨2478428, by rfl⟩ : syracuseStep 3304571 = 4956857) B4956857
theorem B2203047 : Blo 2201435 2203047 := bstep (se 1 (by rfl) ⟨1652285, by rfl⟩ : syracuseStep 2203047 = 3304571) B3304571
theorem B2478433 : Blo 2201435 2478433 := bbase (se 2 (by rfl) ⟨929412, by rfl⟩ : syracuseStep 2478433 = 1858825) (by norm_num)
theorem B3304577 : Blo 2201435 3304577 := bstep (se 2 (by rfl) ⟨1239216, by rfl⟩ : syracuseStep 3304577 = 2478433) B2478433
theorem B2203051 : Blo 2201435 2203051 := bstep (se 1 (by rfl) ⟨1652288, by rfl⟩ : syracuseStep 2203051 = 3304577) B3304577
theorem B5576485 : Blo 2201435 5576485 := bbase (se 4 (by rfl) ⟨522795, by rfl⟩ : syracuseStep 5576485 = 1045591) (by norm_num)
theorem B7435313 : Blo 2201435 7435313 := bstep (se 2 (by rfl) ⟨2788242, by rfl⟩ : syracuseStep 7435313 = 5576485) B5576485
theorem B4956875 : Blo 2201435 4956875 := bstep (se 1 (by rfl) ⟨3717656, by rfl⟩ : syracuseStep 4956875 = 7435313) B7435313
theorem B3304583 : Blo 2201435 3304583 := bstep (se 1 (by rfl) ⟨2478437, by rfl⟩ : syracuseStep 3304583 = 4956875) B4956875
theorem B2203055 : Blo 2201435 2203055 := bstep (se 1 (by rfl) ⟨1652291, by rfl⟩ : syracuseStep 2203055 = 3304583) B3304583
theorem B3304589 : Blo 2201435 3304589 := bbase (se 3 (by rfl) ⟨619610, by rfl⟩ : syracuseStep 3304589 = 1239221) (by norm_num)
theorem B2203059 : Blo 2201435 2203059 := bstep (se 1 (by rfl) ⟨1652294, by rfl⟩ : syracuseStep 2203059 = 3304589) B3304589
theorem B4956893 : Blo 2201435 4956893 := bbase (se 3 (by rfl) ⟨929417, by rfl⟩ : syracuseStep 4956893 = 1858835) (by norm_num)
theorem B3304595 : Blo 2201435 3304595 := bstep (se 1 (by rfl) ⟨2478446, by rfl⟩ : syracuseStep 3304595 = 4956893) B4956893
theorem B2203063 : Blo 2201435 2203063 := bstep (se 1 (by rfl) ⟨1652297, by rfl⟩ : syracuseStep 2203063 = 3304595) B3304595
theorem B3717677 : Blo 2201435 3717677 := bbase (se 3 (by rfl) ⟨697064, by rfl⟩ : syracuseStep 3717677 = 1394129) (by norm_num)
theorem B2478451 : Blo 2201435 2478451 := bstep (se 1 (by rfl) ⟨1858838, by rfl⟩ : syracuseStep 2478451 = 3717677) B3717677
theorem B3304601 : Blo 2201435 3304601 := bstep (se 2 (by rfl) ⟨1239225, by rfl⟩ : syracuseStep 3304601 = 2478451) B2478451
theorem B2203067 : Blo 2201435 2203067 := bstep (se 1 (by rfl) ⟨1652300, by rfl⟩ : syracuseStep 2203067 = 3304601) B3304601
theorem B4769389 : Blo 2201435 4769389 := bbase (se 3 (by rfl) ⟨894260, by rfl⟩ : syracuseStep 4769389 = 1788521) (by norm_num)
theorem B6359185 : Blo 2201435 6359185 := bstep (se 2 (by rfl) ⟨2384694, by rfl⟩ : syracuseStep 6359185 = 4769389) B4769389
theorem B8478913 : Blo 2201435 8478913 := bstep (se 2 (by rfl) ⟨3179592, by rfl⟩ : syracuseStep 8478913 = 6359185) B6359185
theorem B11305217 : Blo 2201435 11305217 := bstep (se 2 (by rfl) ⟨4239456, by rfl⟩ : syracuseStep 11305217 = 8478913) B8478913
theorem B30147245 : Blo 2201435 30147245 := bstep (se 3 (by rfl) ⟨5652608, by rfl⟩ : syracuseStep 30147245 = 11305217) B11305217
theorem B20098163 : Blo 2201435 20098163 := bstep (se 1 (by rfl) ⟨15073622, by rfl⟩ : syracuseStep 20098163 = 30147245) B30147245
theorem B53595101 : Blo 2201435 53595101 := bstep (se 3 (by rfl) ⟨10049081, by rfl⟩ : syracuseStep 53595101 = 20098163) B20098163
theorem B35730067 : Blo 2201435 35730067 := bstep (se 1 (by rfl) ⟨26797550, by rfl⟩ : syracuseStep 35730067 = 53595101) B53595101
theorem B47640089 : Blo 2201435 47640089 := bstep (se 2 (by rfl) ⟨17865033, by rfl⟩ : syracuseStep 47640089 = 35730067) B35730067
theorem B31760059 : Blo 2201435 31760059 := bstep (se 1 (by rfl) ⟨23820044, by rfl⟩ : syracuseStep 31760059 = 47640089) B47640089
theorem B42346745 : Blo 2201435 42346745 := bstep (se 2 (by rfl) ⟨15880029, by rfl⟩ : syracuseStep 42346745 = 31760059) B31760059
theorem B28231163 : Blo 2201435 28231163 := bstep (se 1 (by rfl) ⟨21173372, by rfl⟩ : syracuseStep 28231163 = 42346745) B42346745
theorem B18820775 : Blo 2201435 18820775 := bstep (se 1 (by rfl) ⟨14115581, by rfl⟩ : syracuseStep 18820775 = 28231163) B28231163
theorem B12547183 : Blo 2201435 12547183 := bstep (se 1 (by rfl) ⟨9410387, by rfl⟩ : syracuseStep 12547183 = 18820775) B18820775
theorem B16729577 : Blo 2201435 16729577 := bstep (se 2 (by rfl) ⟨6273591, by rfl⟩ : syracuseStep 16729577 = 12547183) B12547183
theorem B11153051 : Blo 2201435 11153051 := bstep (se 1 (by rfl) ⟨8364788, by rfl⟩ : syracuseStep 11153051 = 16729577) B16729577
theorem B7435367 : Blo 2201435 7435367 := bstep (se 1 (by rfl) ⟨5576525, by rfl⟩ : syracuseStep 7435367 = 11153051) B11153051
theorem B4956911 : Blo 2201435 4956911 := bstep (se 1 (by rfl) ⟨3717683, by rfl⟩ : syracuseStep 4956911 = 7435367) B7435367
theorem B3304607 : Blo 2201435 3304607 := bstep (se 1 (by rfl) ⟨2478455, by rfl⟩ : syracuseStep 3304607 = 4956911) B4956911
theorem B2203071 : Blo 2201435 2203071 := bstep (se 1 (by rfl) ⟨1652303, by rfl⟩ : syracuseStep 2203071 = 3304607) B3304607
theorem B3304613 : Blo 2201435 3304613 := bbase (se 4 (by rfl) ⟨309807, by rfl⟩ : syracuseStep 3304613 = 619615) (by norm_num)
theorem B2203075 : Blo 2201435 2203075 := bstep (se 1 (by rfl) ⟨1652306, by rfl⟩ : syracuseStep 2203075 = 3304613) B3304613
theorem B2788273 : Blo 2201435 2788273 := bbase (se 2 (by rfl) ⟨1045602, by rfl⟩ : syracuseStep 2788273 = 2091205) (by norm_num)
theorem B3717697 : Blo 2201435 3717697 := bstep (se 2 (by rfl) ⟨1394136, by rfl⟩ : syracuseStep 3717697 = 2788273) B2788273
theorem B4956929 : Blo 2201435 4956929 := bstep (se 2 (by rfl) ⟨1858848, by rfl⟩ : syracuseStep 4956929 = 3717697) B3717697
theorem B3304619 : Blo 2201435 3304619 := bstep (se 1 (by rfl) ⟨2478464, by rfl⟩ : syracuseStep 3304619 = 4956929) B4956929
theorem B2203079 : Blo 2201435 2203079 := bstep (se 1 (by rfl) ⟨1652309, by rfl⟩ : syracuseStep 2203079 = 3304619) B3304619
theorem B2478469 : Blo 2201435 2478469 := bbase (se 4 (by rfl) ⟨232356, by rfl⟩ : syracuseStep 2478469 = 464713) (by norm_num)
theorem B3304625 : Blo 2201435 3304625 := bstep (se 2 (by rfl) ⟨1239234, by rfl⟩ : syracuseStep 3304625 = 2478469) B2478469
theorem B2203083 : Blo 2201435 2203083 := bstep (se 1 (by rfl) ⟨1652312, by rfl⟩ : syracuseStep 2203083 = 3304625) B3304625
theorem B4705229 : Blo 2201435 4705229 := bbase (se 3 (by rfl) ⟨882230, by rfl⟩ : syracuseStep 4705229 = 1764461) (by norm_num)
theorem B3136819 : Blo 2201435 3136819 := bstep (se 1 (by rfl) ⟨2352614, by rfl⟩ : syracuseStep 3136819 = 4705229) B4705229
theorem B4182425 : Blo 2201435 4182425 := bstep (se 2 (by rfl) ⟨1568409, by rfl⟩ : syracuseStep 4182425 = 3136819) B3136819
theorem B2788283 : Blo 2201435 2788283 := bstep (se 1 (by rfl) ⟨2091212, by rfl⟩ : syracuseStep 2788283 = 4182425) B4182425
theorem B7435421 : Blo 2201435 7435421 := bstep (se 3 (by rfl) ⟨1394141, by rfl⟩ : syracuseStep 7435421 = 2788283) B2788283
theorem B4956947 : Blo 2201435 4956947 := bstep (se 1 (by rfl) ⟨3717710, by rfl⟩ : syracuseStep 4956947 = 7435421) B7435421
theorem B3304631 : Blo 2201435 3304631 := bstep (se 1 (by rfl) ⟨2478473, by rfl⟩ : syracuseStep 3304631 = 4956947) B4956947
theorem B2203087 : Blo 2201435 2203087 := bstep (se 1 (by rfl) ⟨1652315, by rfl⟩ : syracuseStep 2203087 = 3304631) B3304631
theorem B3304637 : Blo 2201435 3304637 := bbase (se 3 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 3304637 = 1239239) (by norm_num)
theorem B2203091 : Blo 2201435 2203091 := bstep (se 1 (by rfl) ⟨1652318, by rfl⟩ : syracuseStep 2203091 = 3304637) B3304637
theorem B4956965 : Blo 2201435 4956965 := bbase (se 4 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 4956965 = 929431) (by norm_num)
theorem B3304643 : Blo 2201435 3304643 := bstep (se 1 (by rfl) ⟨2478482, by rfl⟩ : syracuseStep 3304643 = 4956965) B4956965
theorem B2203095 : Blo 2201435 2203095 := bstep (se 1 (by rfl) ⟨1652321, by rfl⟩ : syracuseStep 2203095 = 3304643) B3304643
theorem B5576597 : Blo 2201435 5576597 := bbase (se 6 (by rfl) ⟨130701, by rfl⟩ : syracuseStep 5576597 = 261403) (by norm_num)
theorem B3717731 : Blo 2201435 3717731 := bstep (se 1 (by rfl) ⟨2788298, by rfl⟩ : syracuseStep 3717731 = 5576597) B5576597
theorem B2478487 : Blo 2201435 2478487 := bstep (se 1 (by rfl) ⟨1858865, by rfl⟩ : syracuseStep 2478487 = 3717731) B3717731
theorem B3304649 : Blo 2201435 3304649 := bstep (se 2 (by rfl) ⟨1239243, by rfl⟩ : syracuseStep 3304649 = 2478487) B2478487
theorem B2203099 : Blo 2201435 2203099 := bstep (se 1 (by rfl) ⟨1652324, by rfl⟩ : syracuseStep 2203099 = 3304649) B3304649
theorem B5293421 : Blo 2201435 5293421 := bbase (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) (by norm_num)
theorem B3528947 : Blo 2201435 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B9410525 : Blo 2201435 9410525 := bstep (se 3 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 9410525 = 3528947) B3528947
theorem B6273683 : Blo 2201435 6273683 := bstep (se 1 (by rfl) ⟨4705262, by rfl⟩ : syracuseStep 6273683 = 9410525) B9410525
theorem B4182455 : Blo 2201435 4182455 := bstep (se 1 (by rfl) ⟨3136841, by rfl⟩ : syracuseStep 4182455 = 6273683) B6273683
theorem B11153213 : Blo 2201435 11153213 := bstep (se 3 (by rfl) ⟨2091227, by rfl⟩ : syracuseStep 11153213 = 4182455) B4182455
theorem B7435475 : Blo 2201435 7435475 := bstep (se 1 (by rfl) ⟨5576606, by rfl⟩ : syracuseStep 7435475 = 11153213) B11153213
theorem B4956983 : Blo 2201435 4956983 := bstep (se 1 (by rfl) ⟨3717737, by rfl⟩ : syracuseStep 4956983 = 7435475) B7435475
theorem B3304655 : Blo 2201435 3304655 := bstep (se 1 (by rfl) ⟨2478491, by rfl⟩ : syracuseStep 3304655 = 4956983) B4956983
theorem B2203103 : Blo 2201435 2203103 := bstep (se 1 (by rfl) ⟨1652327, by rfl⟩ : syracuseStep 2203103 = 3304655) B3304655
theorem B3304661 : Blo 2201435 3304661 := bbase (se 7 (by rfl) ⟨38726, by rfl⟩ : syracuseStep 3304661 = 77453) (by norm_num)
theorem B2203107 : Blo 2201435 2203107 := bstep (se 1 (by rfl) ⟨1652330, by rfl⟩ : syracuseStep 2203107 = 3304661) B3304661
theorem B3136853 : Blo 2201435 3136853 := bbase (se 11 (by rfl) ⟨2297, by rfl⟩ : syracuseStep 3136853 = 4595) (by norm_num)
theorem B8364941 : Blo 2201435 8364941 := bstep (se 3 (by rfl) ⟨1568426, by rfl⟩ : syracuseStep 8364941 = 3136853) B3136853
theorem B5576627 : Blo 2201435 5576627 := bstep (se 1 (by rfl) ⟨4182470, by rfl⟩ : syracuseStep 5576627 = 8364941) B8364941
theorem B3717751 : Blo 2201435 3717751 := bstep (se 1 (by rfl) ⟨2788313, by rfl⟩ : syracuseStep 3717751 = 5576627) B5576627
theorem B4957001 : Blo 2201435 4957001 := bstep (se 2 (by rfl) ⟨1858875, by rfl⟩ : syracuseStep 4957001 = 3717751) B3717751
theorem B3304667 : Blo 2201435 3304667 := bstep (se 1 (by rfl) ⟨2478500, by rfl⟩ : syracuseStep 3304667 = 4957001) B4957001
theorem B2203111 : Blo 2201435 2203111 := bstep (se 1 (by rfl) ⟨1652333, by rfl⟩ : syracuseStep 2203111 = 3304667) B3304667
theorem B2478505 : Blo 2201435 2478505 := bbase (se 2 (by rfl) ⟨929439, by rfl⟩ : syracuseStep 2478505 = 1858879) (by norm_num)
theorem B3304673 : Blo 2201435 3304673 := bstep (se 2 (by rfl) ⟨1239252, by rfl⟩ : syracuseStep 3304673 = 2478505) B2478505
theorem B2203115 : Blo 2201435 2203115 := bstep (se 1 (by rfl) ⟨1652336, by rfl⟩ : syracuseStep 2203115 = 3304673) B3304673
theorem B4466357 : Blo 2201435 4466357 := bbase (se 5 (by rfl) ⟨209360, by rfl⟩ : syracuseStep 4466357 = 418721) (by norm_num)
theorem B2977571 : Blo 2201435 2977571 := bstep (se 1 (by rfl) ⟨2233178, by rfl⟩ : syracuseStep 2977571 = 4466357) B4466357
theorem B7940189 : Blo 2201435 7940189 := bstep (se 3 (by rfl) ⟨1488785, by rfl⟩ : syracuseStep 7940189 = 2977571) B2977571
theorem B5293459 : Blo 2201435 5293459 := bstep (se 1 (by rfl) ⟨3970094, by rfl⟩ : syracuseStep 5293459 = 7940189) B7940189
theorem B7057945 : Blo 2201435 7057945 := bstep (se 2 (by rfl) ⟨2646729, by rfl⟩ : syracuseStep 7057945 = 5293459) B5293459
theorem B9410593 : Blo 2201435 9410593 := bstep (se 2 (by rfl) ⟨3528972, by rfl⟩ : syracuseStep 9410593 = 7057945) B7057945
theorem B12547457 : Blo 2201435 12547457 := bstep (se 2 (by rfl) ⟨4705296, by rfl⟩ : syracuseStep 12547457 = 9410593) B9410593
theorem B8364971 : Blo 2201435 8364971 := bstep (se 1 (by rfl) ⟨6273728, by rfl⟩ : syracuseStep 8364971 = 12547457) B12547457
theorem B5576647 : Blo 2201435 5576647 := bstep (se 1 (by rfl) ⟨4182485, by rfl⟩ : syracuseStep 5576647 = 8364971) B8364971
theorem B7435529 : Blo 2201435 7435529 := bstep (se 2 (by rfl) ⟨2788323, by rfl⟩ : syracuseStep 7435529 = 5576647) B5576647
theorem B4957019 : Blo 2201435 4957019 := bstep (se 1 (by rfl) ⟨3717764, by rfl⟩ : syracuseStep 4957019 = 7435529) B7435529
theorem B3304679 : Blo 2201435 3304679 := bstep (se 1 (by rfl) ⟨2478509, by rfl⟩ : syracuseStep 3304679 = 4957019) B4957019
theorem B2203119 : Blo 2201435 2203119 := bstep (se 1 (by rfl) ⟨1652339, by rfl⟩ : syracuseStep 2203119 = 3304679) B3304679
theorem B3304685 : Blo 2201435 3304685 := bbase (se 3 (by rfl) ⟨619628, by rfl⟩ : syracuseStep 3304685 = 1239257) (by norm_num)
theorem B2203123 : Blo 2201435 2203123 := bstep (se 1 (by rfl) ⟨1652342, by rfl⟩ : syracuseStep 2203123 = 3304685) B3304685
theorem B4957037 : Blo 2201435 4957037 := bbase (se 3 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 4957037 = 1858889) (by norm_num)
theorem B3304691 : Blo 2201435 3304691 := bstep (se 1 (by rfl) ⟨2478518, by rfl⟩ : syracuseStep 3304691 = 4957037) B4957037
theorem B2203127 : Blo 2201435 2203127 := bstep (se 1 (by rfl) ⟨1652345, by rfl⟩ : syracuseStep 2203127 = 3304691) B3304691
theorem B4182509 : Blo 2201435 4182509 := bbase (se 3 (by rfl) ⟨784220, by rfl⟩ : syracuseStep 4182509 = 1568441) (by norm_num)
theorem B2788339 : Blo 2201435 2788339 := bstep (se 1 (by rfl) ⟨2091254, by rfl⟩ : syracuseStep 2788339 = 4182509) B4182509
theorem B3717785 : Blo 2201435 3717785 := bstep (se 2 (by rfl) ⟨1394169, by rfl⟩ : syracuseStep 3717785 = 2788339) B2788339
theorem B2478523 : Blo 2201435 2478523 := bstep (se 1 (by rfl) ⟨1858892, by rfl⟩ : syracuseStep 2478523 = 3717785) B3717785
theorem B3304697 : Blo 2201435 3304697 := bstep (se 2 (by rfl) ⟨1239261, by rfl⟩ : syracuseStep 3304697 = 2478523) B2478523
theorem B2203131 : Blo 2201435 2203131 := bstep (se 1 (by rfl) ⟨1652348, by rfl⟩ : syracuseStep 2203131 = 3304697) B3304697
theorem B31760981 : Blo 2201435 31760981 := bbase (se 8 (by rfl) ⟨186099, by rfl⟩ : syracuseStep 31760981 = 372199) (by norm_num)
theorem B21173987 : Blo 2201435 21173987 := bstep (se 1 (by rfl) ⟨15880490, by rfl⟩ : syracuseStep 21173987 = 31760981) B31760981
theorem B56463965 : Blo 2201435 56463965 := bstep (se 3 (by rfl) ⟨10586993, by rfl⟩ : syracuseStep 56463965 = 21173987) B21173987
theorem B37642643 : Blo 2201435 37642643 := bstep (se 1 (by rfl) ⟨28231982, by rfl⟩ : syracuseStep 37642643 = 56463965) B56463965
theorem B25095095 : Blo 2201435 25095095 := bstep (se 1 (by rfl) ⟨18821321, by rfl⟩ : syracuseStep 25095095 = 37642643) B37642643
theorem B16730063 : Blo 2201435 16730063 := bstep (se 1 (by rfl) ⟨12547547, by rfl⟩ : syracuseStep 16730063 = 25095095) B25095095
theorem B11153375 : Blo 2201435 11153375 := bstep (se 1 (by rfl) ⟨8365031, by rfl⟩ : syracuseStep 11153375 = 16730063) B16730063
theorem B7435583 : Blo 2201435 7435583 := bstep (se 1 (by rfl) ⟨5576687, by rfl⟩ : syracuseStep 7435583 = 11153375) B11153375
theorem B4957055 : Blo 2201435 4957055 := bstep (se 1 (by rfl) ⟨3717791, by rfl⟩ : syracuseStep 4957055 = 7435583) B7435583
theorem B3304703 : Blo 2201435 3304703 := bstep (se 1 (by rfl) ⟨2478527, by rfl⟩ : syracuseStep 3304703 = 4957055) B4957055
theorem B2203135 : Blo 2201435 2203135 := bstep (se 1 (by rfl) ⟨1652351, by rfl⟩ : syracuseStep 2203135 = 3304703) B3304703
theorem B3304709 : Blo 2201435 3304709 := bbase (se 4 (by rfl) ⟨309816, by rfl⟩ : syracuseStep 3304709 = 619633) (by norm_num)
theorem B2203139 : Blo 2201435 2203139 := bstep (se 1 (by rfl) ⟨1652354, by rfl⟩ : syracuseStep 2203139 = 3304709) B3304709
theorem B3717805 : Blo 2201435 3717805 := bbase (se 3 (by rfl) ⟨697088, by rfl⟩ : syracuseStep 3717805 = 1394177) (by norm_num)
theorem B4957073 : Blo 2201435 4957073 := bstep (se 2 (by rfl) ⟨1858902, by rfl⟩ : syracuseStep 4957073 = 3717805) B3717805
theorem B3304715 : Blo 2201435 3304715 := bstep (se 1 (by rfl) ⟨2478536, by rfl⟩ : syracuseStep 3304715 = 4957073) B4957073
theorem B2203143 : Blo 2201435 2203143 := bstep (se 1 (by rfl) ⟨1652357, by rfl⟩ : syracuseStep 2203143 = 3304715) B3304715
theorem B2478541 : Blo 2201435 2478541 := bbase (se 3 (by rfl) ⟨464726, by rfl⟩ : syracuseStep 2478541 = 929453) (by norm_num)
theorem B3304721 : Blo 2201435 3304721 := bstep (se 2 (by rfl) ⟨1239270, by rfl⟩ : syracuseStep 3304721 = 2478541) B2478541
theorem B2203147 : Blo 2201435 2203147 := bstep (se 1 (by rfl) ⟨1652360, by rfl⟩ : syracuseStep 2203147 = 3304721) B3304721
theorem B7435637 : Blo 2201435 7435637 := bbase (se 5 (by rfl) ⟨348545, by rfl⟩ : syracuseStep 7435637 = 697091) (by norm_num)
theorem B4957091 : Blo 2201435 4957091 := bstep (se 1 (by rfl) ⟨3717818, by rfl⟩ : syracuseStep 4957091 = 7435637) B7435637
theorem B3304727 : Blo 2201435 3304727 := bstep (se 1 (by rfl) ⟨2478545, by rfl⟩ : syracuseStep 3304727 = 4957091) B4957091
theorem B2203151 : Blo 2201435 2203151 := bstep (se 1 (by rfl) ⟨1652363, by rfl⟩ : syracuseStep 2203151 = 3304727) B3304727
theorem B3304733 : Blo 2201435 3304733 := bbase (se 3 (by rfl) ⟨619637, by rfl⟩ : syracuseStep 3304733 = 1239275) (by norm_num)
theorem B2203155 : Blo 2201435 2203155 := bstep (se 1 (by rfl) ⟨1652366, by rfl⟩ : syracuseStep 2203155 = 3304733) B3304733
theorem B4957109 : Blo 2201435 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B3304739 : Blo 2201435 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B2203159 : Blo 2201435 2203159 := bstep (se 1 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 2203159 = 3304739) B3304739
theorem B9054773 : Blo 2201435 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B6036515 : Blo 2201435 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B4024343 : Blo 2201435 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B2682895 : Blo 2201435 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B3577193 : Blo 2201435 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B2384795 : Blo 2201435 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B6359453 : Blo 2201435 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B4239635 : Blo 2201435 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B11305693 : Blo 2201435 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B15074257 : Blo 2201435 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B20099009 : Blo 2201435 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B13399339 : Blo 2201435 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B17865785 : Blo 2201435 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B11910523 : Blo 2201435 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B15880697 : Blo 2201435 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B10587131 : Blo 2201435 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B7058087 : Blo 2201435 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B4705391 : Blo 2201435 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B12547709 : Blo 2201435 12547709 := bstep (se 3 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 12547709 = 4705391) B4705391
theorem B8365139 : Blo 2201435 8365139 := bstep (se 1 (by rfl) ⟨6273854, by rfl⟩ : syracuseStep 8365139 = 12547709) B12547709
theorem B5576759 : Blo 2201435 5576759 := bstep (se 1 (by rfl) ⟨4182569, by rfl⟩ : syracuseStep 5576759 = 8365139) B8365139
theorem B3717839 : Blo 2201435 3717839 := bstep (se 1 (by rfl) ⟨2788379, by rfl⟩ : syracuseStep 3717839 = 5576759) B5576759
theorem B2478559 : Blo 2201435 2478559 := bstep (se 1 (by rfl) ⟨1858919, by rfl⟩ : syracuseStep 2478559 = 3717839) B3717839
theorem B3304745 : Blo 2201435 3304745 := bstep (se 2 (by rfl) ⟨1239279, by rfl⟩ : syracuseStep 3304745 = 2478559) B2478559
theorem B2203163 : Blo 2201435 2203163 := bstep (se 1 (by rfl) ⟨1652372, by rfl⟩ : syracuseStep 2203163 = 3304745) B3304745
theorem B3970181 : Blo 2201435 3970181 := bbase (se 4 (by rfl) ⟨372204, by rfl⟩ : syracuseStep 3970181 = 744409) (by norm_num)
theorem B10587149 : Blo 2201435 10587149 := bstep (se 3 (by rfl) ⟨1985090, by rfl⟩ : syracuseStep 10587149 = 3970181) B3970181
theorem B7058099 : Blo 2201435 7058099 := bstep (se 1 (by rfl) ⟨5293574, by rfl⟩ : syracuseStep 7058099 = 10587149) B10587149
theorem B4705399 : Blo 2201435 4705399 := bstep (se 1 (by rfl) ⟨3529049, by rfl⟩ : syracuseStep 4705399 = 7058099) B7058099
theorem B6273865 : Blo 2201435 6273865 := bstep (se 2 (by rfl) ⟨2352699, by rfl⟩ : syracuseStep 6273865 = 4705399) B4705399
theorem B8365153 : Blo 2201435 8365153 := bstep (se 2 (by rfl) ⟨3136932, by rfl⟩ : syracuseStep 8365153 = 6273865) B6273865
theorem B11153537 : Blo 2201435 11153537 := bstep (se 2 (by rfl) ⟨4182576, by rfl⟩ : syracuseStep 11153537 = 8365153) B8365153
theorem B7435691 : Blo 2201435 7435691 := bstep (se 1 (by rfl) ⟨5576768, by rfl⟩ : syracuseStep 7435691 = 11153537) B11153537
theorem B4957127 : Blo 2201435 4957127 := bstep (se 1 (by rfl) ⟨3717845, by rfl⟩ : syracuseStep 4957127 = 7435691) B7435691
theorem B3304751 : Blo 2201435 3304751 := bstep (se 1 (by rfl) ⟨2478563, by rfl⟩ : syracuseStep 3304751 = 4957127) B4957127
theorem B2203167 : Blo 2201435 2203167 := bstep (se 1 (by rfl) ⟨1652375, by rfl⟩ : syracuseStep 2203167 = 3304751) B3304751
theorem B3304757 : Blo 2201435 3304757 := bbase (se 5 (by rfl) ⟨154910, by rfl⟩ : syracuseStep 3304757 = 309821) (by norm_num)
theorem B2203171 : Blo 2201435 2203171 := bstep (se 1 (by rfl) ⟨1652378, by rfl⟩ : syracuseStep 2203171 = 3304757) B3304757
theorem B5576789 : Blo 2201435 5576789 := bbase (se 8 (by rfl) ⟨32676, by rfl⟩ : syracuseStep 5576789 = 65353) (by norm_num)
theorem B3717859 : Blo 2201435 3717859 := bstep (se 1 (by rfl) ⟨2788394, by rfl⟩ : syracuseStep 3717859 = 5576789) B5576789
theorem B4957145 : Blo 2201435 4957145 := bstep (se 2 (by rfl) ⟨1858929, by rfl⟩ : syracuseStep 4957145 = 3717859) B3717859
theorem B3304763 : Blo 2201435 3304763 := bstep (se 1 (by rfl) ⟨2478572, by rfl⟩ : syracuseStep 3304763 = 4957145) B4957145
theorem B2203175 : Blo 2201435 2203175 := bstep (se 1 (by rfl) ⟨1652381, by rfl⟩ : syracuseStep 2203175 = 3304763) B3304763
theorem B2478577 : Blo 2201435 2478577 := bbase (se 2 (by rfl) ⟨929466, by rfl⟩ : syracuseStep 2478577 = 1858933) (by norm_num)
theorem B3304769 : Blo 2201435 3304769 := bstep (se 2 (by rfl) ⟨1239288, by rfl⟩ : syracuseStep 3304769 = 2478577) B2478577
theorem B2203179 : Blo 2201435 2203179 := bstep (se 1 (by rfl) ⟨1652384, by rfl⟩ : syracuseStep 2203179 = 3304769) B3304769
theorem B5293613 : Blo 2201435 5293613 := bbase (se 3 (by rfl) ⟨992552, by rfl⟩ : syracuseStep 5293613 = 1985105) (by norm_num)
theorem B14116301 : Blo 2201435 14116301 := bstep (se 3 (by rfl) ⟨2646806, by rfl⟩ : syracuseStep 14116301 = 5293613) B5293613
theorem B9410867 : Blo 2201435 9410867 := bstep (se 1 (by rfl) ⟨7058150, by rfl⟩ : syracuseStep 9410867 = 14116301) B14116301
theorem B6273911 : Blo 2201435 6273911 := bstep (se 1 (by rfl) ⟨4705433, by rfl⟩ : syracuseStep 6273911 = 9410867) B9410867
theorem B4182607 : Blo 2201435 4182607 := bstep (se 1 (by rfl) ⟨3136955, by rfl⟩ : syracuseStep 4182607 = 6273911) B6273911
theorem B5576809 : Blo 2201435 5576809 := bstep (se 2 (by rfl) ⟨2091303, by rfl⟩ : syracuseStep 5576809 = 4182607) B4182607
theorem B7435745 : Blo 2201435 7435745 := bstep (se 2 (by rfl) ⟨2788404, by rfl⟩ : syracuseStep 7435745 = 5576809) B5576809
theorem B4957163 : Blo 2201435 4957163 := bstep (se 1 (by rfl) ⟨3717872, by rfl⟩ : syracuseStep 4957163 = 7435745) B7435745
theorem B3304775 : Blo 2201435 3304775 := bstep (se 1 (by rfl) ⟨2478581, by rfl⟩ : syracuseStep 3304775 = 4957163) B4957163
theorem B2203183 : Blo 2201435 2203183 := bstep (se 1 (by rfl) ⟨1652387, by rfl⟩ : syracuseStep 2203183 = 3304775) B3304775
theorem B3304781 : Blo 2201435 3304781 := bbase (se 3 (by rfl) ⟨619646, by rfl⟩ : syracuseStep 3304781 = 1239293) (by norm_num)
theorem B2203187 : Blo 2201435 2203187 := bstep (se 1 (by rfl) ⟨1652390, by rfl⟩ : syracuseStep 2203187 = 3304781) B3304781
theorem B4957181 : Blo 2201435 4957181 := bbase (se 3 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 4957181 = 1858943) (by norm_num)
theorem B3304787 : Blo 2201435 3304787 := bstep (se 1 (by rfl) ⟨2478590, by rfl⟩ : syracuseStep 3304787 = 4957181) B4957181
theorem B2203191 : Blo 2201435 2203191 := bstep (se 1 (by rfl) ⟨1652393, by rfl⟩ : syracuseStep 2203191 = 3304787) B3304787
theorem B3717893 : Blo 2201435 3717893 := bbase (se 4 (by rfl) ⟨348552, by rfl⟩ : syracuseStep 3717893 = 697105) (by norm_num)
theorem B2478595 : Blo 2201435 2478595 := bstep (se 1 (by rfl) ⟨1858946, by rfl⟩ : syracuseStep 2478595 = 3717893) B3717893
theorem B3304793 : Blo 2201435 3304793 := bstep (se 2 (by rfl) ⟨1239297, by rfl⟩ : syracuseStep 3304793 = 2478595) B2478595
theorem B2203195 : Blo 2201435 2203195 := bstep (se 1 (by rfl) ⟨1652396, by rfl⟩ : syracuseStep 2203195 = 3304793) B3304793
theorem B16730549 : Blo 2201435 16730549 := bbase (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) (by norm_num)
theorem B11153699 : Blo 2201435 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B7435799 : Blo 2201435 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B4957199 : Blo 2201435 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B3304799 : Blo 2201435 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B2203199 : Blo 2201435 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B3304805 : Blo 2201435 3304805 := bbase (se 4 (by rfl) ⟨309825, by rfl⟩ : syracuseStep 3304805 = 619651) (by norm_num)
theorem B2203203 : Blo 2201435 2203203 := bstep (se 1 (by rfl) ⟨1652402, by rfl⟩ : syracuseStep 2203203 = 3304805) B3304805
theorem B4182653 : Blo 2201435 4182653 := bbase (se 3 (by rfl) ⟨784247, by rfl⟩ : syracuseStep 4182653 = 1568495) (by norm_num)
theorem B2788435 : Blo 2201435 2788435 := bstep (se 1 (by rfl) ⟨2091326, by rfl⟩ : syracuseStep 2788435 = 4182653) B4182653
theorem B3717913 : Blo 2201435 3717913 := bstep (se 2 (by rfl) ⟨1394217, by rfl⟩ : syracuseStep 3717913 = 2788435) B2788435
theorem B4957217 : Blo 2201435 4957217 := bstep (se 2 (by rfl) ⟨1858956, by rfl⟩ : syracuseStep 4957217 = 3717913) B3717913
theorem B3304811 : Blo 2201435 3304811 := bstep (se 1 (by rfl) ⟨2478608, by rfl⟩ : syracuseStep 3304811 = 4957217) B4957217
theorem B2203207 : Blo 2201435 2203207 := bstep (se 1 (by rfl) ⟨1652405, by rfl⟩ : syracuseStep 2203207 = 3304811) B3304811
theorem B2478613 : Blo 2201435 2478613 := bbase (se 6 (by rfl) ⟨58092, by rfl⟩ : syracuseStep 2478613 = 116185) (by norm_num)
theorem B3304817 : Blo 2201435 3304817 := bstep (se 2 (by rfl) ⟨1239306, by rfl⟩ : syracuseStep 3304817 = 2478613) B2478613
theorem B2203211 : Blo 2201435 2203211 := bstep (se 1 (by rfl) ⟨1652408, by rfl⟩ : syracuseStep 2203211 = 3304817) B3304817
theorem B2788445 : Blo 2201435 2788445 := bbase (se 3 (by rfl) ⟨522833, by rfl⟩ : syracuseStep 2788445 = 1045667) (by norm_num)
theorem B7435853 : Blo 2201435 7435853 := bstep (se 3 (by rfl) ⟨1394222, by rfl⟩ : syracuseStep 7435853 = 2788445) B2788445
theorem B4957235 : Blo 2201435 4957235 := bstep (se 1 (by rfl) ⟨3717926, by rfl⟩ : syracuseStep 4957235 = 7435853) B7435853
theorem B3304823 : Blo 2201435 3304823 := bstep (se 1 (by rfl) ⟨2478617, by rfl⟩ : syracuseStep 3304823 = 4957235) B4957235
theorem B2203215 : Blo 2201435 2203215 := bstep (se 1 (by rfl) ⟨1652411, by rfl⟩ : syracuseStep 2203215 = 3304823) B3304823
theorem B3304829 : Blo 2201435 3304829 := bbase (se 3 (by rfl) ⟨619655, by rfl⟩ : syracuseStep 3304829 = 1239311) (by norm_num)
theorem B2203219 : Blo 2201435 2203219 := bstep (se 1 (by rfl) ⟨1652414, by rfl⟩ : syracuseStep 2203219 = 3304829) B3304829
theorem B4957253 : Blo 2201435 4957253 := bbase (se 4 (by rfl) ⟨464742, by rfl⟩ : syracuseStep 4957253 = 929485) (by norm_num)
theorem B3304835 : Blo 2201435 3304835 := bstep (se 1 (by rfl) ⟨2478626, by rfl⟩ : syracuseStep 3304835 = 4957253) B4957253
theorem B2203223 : Blo 2201435 2203223 := bstep (se 1 (by rfl) ⟨1652417, by rfl⟩ : syracuseStep 2203223 = 3304835) B3304835
theorem B6274037 : Blo 2201435 6274037 := bbase (se 5 (by rfl) ⟨294095, by rfl⟩ : syracuseStep 6274037 = 588191) (by norm_num)
theorem B4182691 : Blo 2201435 4182691 := bstep (se 1 (by rfl) ⟨3137018, by rfl⟩ : syracuseStep 4182691 = 6274037) B6274037
theorem B5576921 : Blo 2201435 5576921 := bstep (se 2 (by rfl) ⟨2091345, by rfl⟩ : syracuseStep 5576921 = 4182691) B4182691
theorem B3717947 : Blo 2201435 3717947 := bstep (se 1 (by rfl) ⟨2788460, by rfl⟩ : syracuseStep 3717947 = 5576921) B5576921
theorem B2478631 : Blo 2201435 2478631 := bstep (se 1 (by rfl) ⟨1858973, by rfl⟩ : syracuseStep 2478631 = 3717947) B3717947
theorem B3304841 : Blo 2201435 3304841 := bstep (se 2 (by rfl) ⟨1239315, by rfl⟩ : syracuseStep 3304841 = 2478631) B2478631
theorem B2203227 : Blo 2201435 2203227 := bstep (se 1 (by rfl) ⟨1652420, by rfl⟩ : syracuseStep 2203227 = 3304841) B3304841
theorem B11153861 : Blo 2201435 11153861 := bbase (se 4 (by rfl) ⟨1045674, by rfl⟩ : syracuseStep 11153861 = 2091349) (by norm_num)
theorem B7435907 : Blo 2201435 7435907 := bstep (se 1 (by rfl) ⟨5576930, by rfl⟩ : syracuseStep 7435907 = 11153861) B11153861
theorem B4957271 : Blo 2201435 4957271 := bstep (se 1 (by rfl) ⟨3717953, by rfl⟩ : syracuseStep 4957271 = 7435907) B7435907
theorem B3304847 : Blo 2201435 3304847 := bstep (se 1 (by rfl) ⟨2478635, by rfl⟩ : syracuseStep 3304847 = 4957271) B4957271
theorem B2203231 : Blo 2201435 2203231 := bstep (se 1 (by rfl) ⟨1652423, by rfl⟩ : syracuseStep 2203231 = 3304847) B3304847
theorem B3304853 : Blo 2201435 3304853 := bbase (se 6 (by rfl) ⟨77457, by rfl⟩ : syracuseStep 3304853 = 154915) (by norm_num)
theorem B2203235 : Blo 2201435 2203235 := bstep (se 1 (by rfl) ⟨1652426, by rfl⟩ : syracuseStep 2203235 = 3304853) B3304853
theorem B3529165 : Blo 2201435 3529165 := bbase (se 3 (by rfl) ⟨661718, by rfl⟩ : syracuseStep 3529165 = 1323437) (by norm_num)
theorem B4705553 : Blo 2201435 4705553 := bstep (se 2 (by rfl) ⟨1764582, by rfl⟩ : syracuseStep 4705553 = 3529165) B3529165
theorem B12548141 : Blo 2201435 12548141 := bstep (se 3 (by rfl) ⟨2352776, by rfl⟩ : syracuseStep 12548141 = 4705553) B4705553
theorem B8365427 : Blo 2201435 8365427 := bstep (se 1 (by rfl) ⟨6274070, by rfl⟩ : syracuseStep 8365427 = 12548141) B12548141
theorem B5576951 : Blo 2201435 5576951 := bstep (se 1 (by rfl) ⟨4182713, by rfl⟩ : syracuseStep 5576951 = 8365427) B8365427
theorem B3717967 : Blo 2201435 3717967 := bstep (se 1 (by rfl) ⟨2788475, by rfl⟩ : syracuseStep 3717967 = 5576951) B5576951
theorem B4957289 : Blo 2201435 4957289 := bstep (se 2 (by rfl) ⟨1858983, by rfl⟩ : syracuseStep 4957289 = 3717967) B3717967
theorem B3304859 : Blo 2201435 3304859 := bstep (se 1 (by rfl) ⟨2478644, by rfl⟩ : syracuseStep 3304859 = 4957289) B4957289
theorem B2203239 : Blo 2201435 2203239 := bstep (se 1 (by rfl) ⟨1652429, by rfl⟩ : syracuseStep 2203239 = 3304859) B3304859
theorem B2478649 : Blo 2201435 2478649 := bbase (se 2 (by rfl) ⟨929493, by rfl⟩ : syracuseStep 2478649 = 1858987) (by norm_num)
theorem B3304865 : Blo 2201435 3304865 := bstep (se 2 (by rfl) ⟨1239324, by rfl⟩ : syracuseStep 3304865 = 2478649) B2478649
theorem B2203243 : Blo 2201435 2203243 := bstep (se 1 (by rfl) ⟨1652432, by rfl⟩ : syracuseStep 2203243 = 3304865) B3304865
theorem B2352785 : Blo 2201435 2352785 := bbase (se 2 (by rfl) ⟨882294, by rfl⟩ : syracuseStep 2352785 = 1764589) (by norm_num)
theorem B6274093 : Blo 2201435 6274093 := bstep (se 3 (by rfl) ⟨1176392, by rfl⟩ : syracuseStep 6274093 = 2352785) B2352785
theorem B8365457 : Blo 2201435 8365457 := bstep (se 2 (by rfl) ⟨3137046, by rfl⟩ : syracuseStep 8365457 = 6274093) B6274093
theorem B5576971 : Blo 2201435 5576971 := bstep (se 1 (by rfl) ⟨4182728, by rfl⟩ : syracuseStep 5576971 = 8365457) B8365457
theorem B7435961 : Blo 2201435 7435961 := bstep (se 2 (by rfl) ⟨2788485, by rfl⟩ : syracuseStep 7435961 = 5576971) B5576971
theorem B4957307 : Blo 2201435 4957307 := bstep (se 1 (by rfl) ⟨3717980, by rfl⟩ : syracuseStep 4957307 = 7435961) B7435961
theorem B3304871 : Blo 2201435 3304871 := bstep (se 1 (by rfl) ⟨2478653, by rfl⟩ : syracuseStep 3304871 = 4957307) B4957307
theorem B2203247 : Blo 2201435 2203247 := bstep (se 1 (by rfl) ⟨1652435, by rfl⟩ : syracuseStep 2203247 = 3304871) B3304871
theorem B3304877 : Blo 2201435 3304877 := bbase (se 3 (by rfl) ⟨619664, by rfl⟩ : syracuseStep 3304877 = 1239329) (by norm_num)
theorem B2203251 : Blo 2201435 2203251 := bstep (se 1 (by rfl) ⟨1652438, by rfl⟩ : syracuseStep 2203251 = 3304877) B3304877
theorem B4957325 : Blo 2201435 4957325 := bbase (se 3 (by rfl) ⟨929498, by rfl⟩ : syracuseStep 4957325 = 1858997) (by norm_num)
theorem B3304883 : Blo 2201435 3304883 := bstep (se 1 (by rfl) ⟨2478662, by rfl⟩ : syracuseStep 3304883 = 4957325) B4957325
theorem B2203255 : Blo 2201435 2203255 := bstep (se 1 (by rfl) ⟨1652441, by rfl⟩ : syracuseStep 2203255 = 3304883) B3304883
theorem B2788501 : Blo 2201435 2788501 := bbase (se 6 (by rfl) ⟨65355, by rfl⟩ : syracuseStep 2788501 = 130711) (by norm_num)
theorem B3718001 : Blo 2201435 3718001 := bstep (se 2 (by rfl) ⟨1394250, by rfl⟩ : syracuseStep 3718001 = 2788501) B2788501
theorem B2478667 : Blo 2201435 2478667 := bstep (se 1 (by rfl) ⟨1859000, by rfl⟩ : syracuseStep 2478667 = 3718001) B3718001
theorem B3304889 : Blo 2201435 3304889 := bstep (se 2 (by rfl) ⟨1239333, by rfl⟩ : syracuseStep 3304889 = 2478667) B2478667
theorem B2203259 : Blo 2201435 2203259 := bstep (se 1 (by rfl) ⟨1652444, by rfl⟩ : syracuseStep 2203259 = 3304889) B3304889
theorem B2977765 : Blo 2201435 2977765 := bbase (se 4 (by rfl) ⟨279165, by rfl⟩ : syracuseStep 2977765 = 558331) (by norm_num)
theorem B63525653 : Blo 2201435 63525653 := bstep (se 6 (by rfl) ⟨1488882, by rfl⟩ : syracuseStep 63525653 = 2977765) B2977765
theorem B42350435 : Blo 2201435 42350435 := bstep (se 1 (by rfl) ⟨31762826, by rfl⟩ : syracuseStep 42350435 = 63525653) B63525653
theorem B28233623 : Blo 2201435 28233623 := bstep (se 1 (by rfl) ⟨21175217, by rfl⟩ : syracuseStep 28233623 = 42350435) B42350435
theorem B18822415 : Blo 2201435 18822415 := bstep (se 1 (by rfl) ⟨14116811, by rfl⟩ : syracuseStep 18822415 = 28233623) B28233623
theorem B25096553 : Blo 2201435 25096553 := bstep (se 2 (by rfl) ⟨9411207, by rfl⟩ : syracuseStep 25096553 = 18822415) B18822415
theorem B16731035 : Blo 2201435 16731035 := bstep (se 1 (by rfl) ⟨12548276, by rfl⟩ : syracuseStep 16731035 = 25096553) B25096553
theorem B11154023 : Blo 2201435 11154023 := bstep (se 1 (by rfl) ⟨8365517, by rfl⟩ : syracuseStep 11154023 = 16731035) B16731035
theorem B7436015 : Blo 2201435 7436015 := bstep (se 1 (by rfl) ⟨5577011, by rfl⟩ : syracuseStep 7436015 = 11154023) B11154023
theorem B4957343 : Blo 2201435 4957343 := bstep (se 1 (by rfl) ⟨3718007, by rfl⟩ : syracuseStep 4957343 = 7436015) B7436015
theorem B3304895 : Blo 2201435 3304895 := bstep (se 1 (by rfl) ⟨2478671, by rfl⟩ : syracuseStep 3304895 = 4957343) B4957343
theorem B2203263 : Blo 2201435 2203263 := bstep (se 1 (by rfl) ⟨1652447, by rfl⟩ : syracuseStep 2203263 = 3304895) B3304895
theorem B3304901 : Blo 2201435 3304901 := bbase (se 4 (by rfl) ⟨309834, by rfl⟩ : syracuseStep 3304901 = 619669) (by norm_num)
theorem B2203267 : Blo 2201435 2203267 := bstep (se 1 (by rfl) ⟨1652450, by rfl⟩ : syracuseStep 2203267 = 3304901) B3304901
theorem B3718021 : Blo 2201435 3718021 := bbase (se 4 (by rfl) ⟨348564, by rfl⟩ : syracuseStep 3718021 = 697129) (by norm_num)
theorem B4957361 : Blo 2201435 4957361 := bstep (se 2 (by rfl) ⟨1859010, by rfl⟩ : syracuseStep 4957361 = 3718021) B3718021
theorem B3304907 : Blo 2201435 3304907 := bstep (se 1 (by rfl) ⟨2478680, by rfl⟩ : syracuseStep 3304907 = 4957361) B4957361
theorem B2203271 : Blo 2201435 2203271 := bstep (se 1 (by rfl) ⟨1652453, by rfl⟩ : syracuseStep 2203271 = 3304907) B3304907
theorem B2478685 : Blo 2201435 2478685 := bbase (se 3 (by rfl) ⟨464753, by rfl⟩ : syracuseStep 2478685 = 929507) (by norm_num)
theorem B3304913 : Blo 2201435 3304913 := bstep (se 2 (by rfl) ⟨1239342, by rfl⟩ : syracuseStep 3304913 = 2478685) B2478685
theorem B2203275 : Blo 2201435 2203275 := bstep (se 1 (by rfl) ⟨1652456, by rfl⟩ : syracuseStep 2203275 = 3304913) B3304913
theorem B7436069 : Blo 2201435 7436069 := bbase (se 4 (by rfl) ⟨697131, by rfl⟩ : syracuseStep 7436069 = 1394263) (by norm_num)
theorem B4957379 : Blo 2201435 4957379 := bstep (se 1 (by rfl) ⟨3718034, by rfl⟩ : syracuseStep 4957379 = 7436069) B7436069
theorem B3304919 : Blo 2201435 3304919 := bstep (se 1 (by rfl) ⟨2478689, by rfl⟩ : syracuseStep 3304919 = 4957379) B4957379
theorem B2203279 : Blo 2201435 2203279 := bstep (se 1 (by rfl) ⟨1652459, by rfl⟩ : syracuseStep 2203279 = 3304919) B3304919
theorem B3304925 : Blo 2201435 3304925 := bbase (se 3 (by rfl) ⟨619673, by rfl⟩ : syracuseStep 3304925 = 1239347) (by norm_num)
theorem B2203283 : Blo 2201435 2203283 := bstep (se 1 (by rfl) ⟨1652462, by rfl⟩ : syracuseStep 2203283 = 3304925) B3304925
theorem B4957397 : Blo 2201435 4957397 := bbase (se 7 (by rfl) ⟨58094, by rfl⟩ : syracuseStep 4957397 = 116189) (by norm_num)
theorem B3304931 : Blo 2201435 3304931 := bstep (se 1 (by rfl) ⟨2478698, by rfl⟩ : syracuseStep 3304931 = 4957397) B4957397
theorem B2203287 : Blo 2201435 2203287 := bstep (se 1 (by rfl) ⟨1652465, by rfl⟩ : syracuseStep 2203287 = 3304931) B3304931
theorem B3970405 : Blo 2201435 3970405 := bbase (se 4 (by rfl) ⟨372225, by rfl⟩ : syracuseStep 3970405 = 744451) (by norm_num)
theorem B5293873 : Blo 2201435 5293873 := bstep (se 2 (by rfl) ⟨1985202, by rfl⟩ : syracuseStep 5293873 = 3970405) B3970405
theorem B7058497 : Blo 2201435 7058497 := bstep (se 2 (by rfl) ⟨2646936, by rfl⟩ : syracuseStep 7058497 = 5293873) B5293873
theorem B9411329 : Blo 2201435 9411329 := bstep (se 2 (by rfl) ⟨3529248, by rfl⟩ : syracuseStep 9411329 = 7058497) B7058497
theorem B6274219 : Blo 2201435 6274219 := bstep (se 1 (by rfl) ⟨4705664, by rfl⟩ : syracuseStep 6274219 = 9411329) B9411329
theorem B8365625 : Blo 2201435 8365625 := bstep (se 2 (by rfl) ⟨3137109, by rfl⟩ : syracuseStep 8365625 = 6274219) B6274219
theorem B5577083 : Blo 2201435 5577083 := bstep (se 1 (by rfl) ⟨4182812, by rfl⟩ : syracuseStep 5577083 = 8365625) B8365625
theorem B3718055 : Blo 2201435 3718055 := bstep (se 1 (by rfl) ⟨2788541, by rfl⟩ : syracuseStep 3718055 = 5577083) B5577083
theorem B2478703 : Blo 2201435 2478703 := bstep (se 1 (by rfl) ⟨1859027, by rfl⟩ : syracuseStep 2478703 = 3718055) B3718055
theorem B3304937 : Blo 2201435 3304937 := bstep (se 2 (by rfl) ⟨1239351, by rfl⟩ : syracuseStep 3304937 = 2478703) B2478703
theorem B2203291 : Blo 2201435 2203291 := bstep (se 1 (by rfl) ⟨1652468, by rfl⟩ : syracuseStep 2203291 = 3304937) B3304937
theorem B5025053 : Blo 2201435 5025053 := bbase (se 3 (by rfl) ⟨942197, by rfl⟩ : syracuseStep 5025053 = 1884395) (by norm_num)
theorem B3350035 : Blo 2201435 3350035 := bstep (se 1 (by rfl) ⟨2512526, by rfl⟩ : syracuseStep 3350035 = 5025053) B5025053
theorem B4466713 : Blo 2201435 4466713 := bstep (se 2 (by rfl) ⟨1675017, by rfl⟩ : syracuseStep 4466713 = 3350035) B3350035
theorem B5955617 : Blo 2201435 5955617 := bstep (se 2 (by rfl) ⟨2233356, by rfl⟩ : syracuseStep 5955617 = 4466713) B4466713
theorem B15881645 : Blo 2201435 15881645 := bstep (se 3 (by rfl) ⟨2977808, by rfl⟩ : syracuseStep 15881645 = 5955617) B5955617
theorem B10587763 : Blo 2201435 10587763 := bstep (se 1 (by rfl) ⟨7940822, by rfl⟩ : syracuseStep 10587763 = 15881645) B15881645
theorem B14117017 : Blo 2201435 14117017 := bstep (se 2 (by rfl) ⟨5293881, by rfl⟩ : syracuseStep 14117017 = 10587763) B10587763
theorem B18822689 : Blo 2201435 18822689 := bstep (se 2 (by rfl) ⟨7058508, by rfl⟩ : syracuseStep 18822689 = 14117017) B14117017
theorem B12548459 : Blo 2201435 12548459 := bstep (se 1 (by rfl) ⟨9411344, by rfl⟩ : syracuseStep 12548459 = 18822689) B18822689
theorem B8365639 : Blo 2201435 8365639 := bstep (se 1 (by rfl) ⟨6274229, by rfl⟩ : syracuseStep 8365639 = 12548459) B12548459
theorem B11154185 : Blo 2201435 11154185 := bstep (se 2 (by rfl) ⟨4182819, by rfl⟩ : syracuseStep 11154185 = 8365639) B8365639
theorem B7436123 : Blo 2201435 7436123 := bstep (se 1 (by rfl) ⟨5577092, by rfl⟩ : syracuseStep 7436123 = 11154185) B11154185
theorem B4957415 : Blo 2201435 4957415 := bstep (se 1 (by rfl) ⟨3718061, by rfl⟩ : syracuseStep 4957415 = 7436123) B7436123
theorem B3304943 : Blo 2201435 3304943 := bstep (se 1 (by rfl) ⟨2478707, by rfl⟩ : syracuseStep 3304943 = 4957415) B4957415
theorem B2203295 : Blo 2201435 2203295 := bstep (se 1 (by rfl) ⟨1652471, by rfl⟩ : syracuseStep 2203295 = 3304943) B3304943
theorem B3304949 : Blo 2201435 3304949 := bbase (se 5 (by rfl) ⟨154919, by rfl⟩ : syracuseStep 3304949 = 309839) (by norm_num)
theorem B2203299 : Blo 2201435 2203299 := bstep (se 1 (by rfl) ⟨1652474, by rfl⟩ : syracuseStep 2203299 = 3304949) B3304949
theorem B2352845 : Blo 2201435 2352845 := bbase (se 3 (by rfl) ⟨441158, by rfl⟩ : syracuseStep 2352845 = 882317) (by norm_num)
theorem B6274253 : Blo 2201435 6274253 := bstep (se 3 (by rfl) ⟨1176422, by rfl⟩ : syracuseStep 6274253 = 2352845) B2352845
theorem B4182835 : Blo 2201435 4182835 := bstep (se 1 (by rfl) ⟨3137126, by rfl⟩ : syracuseStep 4182835 = 6274253) B6274253
theorem B5577113 : Blo 2201435 5577113 := bstep (se 2 (by rfl) ⟨2091417, by rfl⟩ : syracuseStep 5577113 = 4182835) B4182835
theorem B3718075 : Blo 2201435 3718075 := bstep (se 1 (by rfl) ⟨2788556, by rfl⟩ : syracuseStep 3718075 = 5577113) B5577113
theorem B4957433 : Blo 2201435 4957433 := bstep (se 2 (by rfl) ⟨1859037, by rfl⟩ : syracuseStep 4957433 = 3718075) B3718075
theorem B3304955 : Blo 2201435 3304955 := bstep (se 1 (by rfl) ⟨2478716, by rfl⟩ : syracuseStep 3304955 = 4957433) B4957433
theorem B2203303 : Blo 2201435 2203303 := bstep (se 1 (by rfl) ⟨1652477, by rfl⟩ : syracuseStep 2203303 = 3304955) B3304955
theorem B2478721 : Blo 2201435 2478721 := bbase (se 2 (by rfl) ⟨929520, by rfl⟩ : syracuseStep 2478721 = 1859041) (by norm_num)
theorem B3304961 : Blo 2201435 3304961 := bstep (se 2 (by rfl) ⟨1239360, by rfl⟩ : syracuseStep 3304961 = 2478721) B2478721
theorem B2203307 : Blo 2201435 2203307 := bstep (se 1 (by rfl) ⟨1652480, by rfl⟩ : syracuseStep 2203307 = 3304961) B3304961
theorem B5577133 : Blo 2201435 5577133 := bbase (se 3 (by rfl) ⟨1045712, by rfl⟩ : syracuseStep 5577133 = 2091425) (by norm_num)
theorem B7436177 : Blo 2201435 7436177 := bstep (se 2 (by rfl) ⟨2788566, by rfl⟩ : syracuseStep 7436177 = 5577133) B5577133
theorem B4957451 : Blo 2201435 4957451 := bstep (se 1 (by rfl) ⟨3718088, by rfl⟩ : syracuseStep 4957451 = 7436177) B7436177
theorem B3304967 : Blo 2201435 3304967 := bstep (se 1 (by rfl) ⟨2478725, by rfl⟩ : syracuseStep 3304967 = 4957451) B4957451
theorem B2203311 : Blo 2201435 2203311 := bstep (se 1 (by rfl) ⟨1652483, by rfl⟩ : syracuseStep 2203311 = 3304967) B3304967
theorem B3304973 : Blo 2201435 3304973 := bbase (se 3 (by rfl) ⟨619682, by rfl⟩ : syracuseStep 3304973 = 1239365) (by norm_num)
theorem B2203315 : Blo 2201435 2203315 := bstep (se 1 (by rfl) ⟨1652486, by rfl⟩ : syracuseStep 2203315 = 3304973) B3304973
theorem B4957469 : Blo 2201435 4957469 := bbase (se 3 (by rfl) ⟨929525, by rfl⟩ : syracuseStep 4957469 = 1859051) (by norm_num)
theorem B3304979 : Blo 2201435 3304979 := bstep (se 1 (by rfl) ⟨2478734, by rfl⟩ : syracuseStep 3304979 = 4957469) B4957469
theorem B2203319 : Blo 2201435 2203319 := bstep (se 1 (by rfl) ⟨1652489, by rfl⟩ : syracuseStep 2203319 = 3304979) B3304979
theorem B3718109 : Blo 2201435 3718109 := bbase (se 3 (by rfl) ⟨697145, by rfl⟩ : syracuseStep 3718109 = 1394291) (by norm_num)
theorem B2478739 : Blo 2201435 2478739 := bstep (se 1 (by rfl) ⟨1859054, by rfl⟩ : syracuseStep 2478739 = 3718109) B3718109
theorem B3304985 : Blo 2201435 3304985 := bstep (se 2 (by rfl) ⟨1239369, by rfl⟩ : syracuseStep 3304985 = 2478739) B2478739
theorem B2203323 : Blo 2201435 2203323 := bstep (se 1 (by rfl) ⟨1652492, by rfl⟩ : syracuseStep 2203323 = 3304985) B3304985
theorem B3970469 : Blo 2201435 3970469 := bbase (se 4 (by rfl) ⟨372231, by rfl⟩ : syracuseStep 3970469 = 744463) (by norm_num)
theorem B10587917 : Blo 2201435 10587917 := bstep (se 3 (by rfl) ⟨1985234, by rfl⟩ : syracuseStep 10587917 = 3970469) B3970469
theorem B7058611 : Blo 2201435 7058611 := bstep (se 1 (by rfl) ⟨5293958, by rfl⟩ : syracuseStep 7058611 = 10587917) B10587917
theorem B9411481 : Blo 2201435 9411481 := bstep (se 2 (by rfl) ⟨3529305, by rfl⟩ : syracuseStep 9411481 = 7058611) B7058611
theorem B12548641 : Blo 2201435 12548641 := bstep (se 2 (by rfl) ⟨4705740, by rfl⟩ : syracuseStep 12548641 = 9411481) B9411481
theorem B16731521 : Blo 2201435 16731521 := bstep (se 2 (by rfl) ⟨6274320, by rfl⟩ : syracuseStep 16731521 = 12548641) B12548641
theorem B11154347 : Blo 2201435 11154347 := bstep (se 1 (by rfl) ⟨8365760, by rfl⟩ : syracuseStep 11154347 = 16731521) B16731521
theorem B7436231 : Blo 2201435 7436231 := bstep (se 1 (by rfl) ⟨5577173, by rfl⟩ : syracuseStep 7436231 = 11154347) B11154347
theorem B4957487 : Blo 2201435 4957487 := bstep (se 1 (by rfl) ⟨3718115, by rfl⟩ : syracuseStep 4957487 = 7436231) B7436231
theorem B3304991 : Blo 2201435 3304991 := bstep (se 1 (by rfl) ⟨2478743, by rfl⟩ : syracuseStep 3304991 = 4957487) B4957487
theorem B2203327 : Blo 2201435 2203327 := bstep (se 1 (by rfl) ⟨1652495, by rfl⟩ : syracuseStep 2203327 = 3304991) B3304991
theorem B3304997 : Blo 2201435 3304997 := bbase (se 4 (by rfl) ⟨309843, by rfl⟩ : syracuseStep 3304997 = 619687) (by norm_num)
theorem B2203331 : Blo 2201435 2203331 := bstep (se 1 (by rfl) ⟨1652498, by rfl⟩ : syracuseStep 2203331 = 3304997) B3304997
theorem B2788597 : Blo 2201435 2788597 := bbase (se 5 (by rfl) ⟨130715, by rfl⟩ : syracuseStep 2788597 = 261431) (by norm_num)
theorem B3718129 : Blo 2201435 3718129 := bstep (se 2 (by rfl) ⟨1394298, by rfl⟩ : syracuseStep 3718129 = 2788597) B2788597
theorem B4957505 : Blo 2201435 4957505 := bstep (se 2 (by rfl) ⟨1859064, by rfl⟩ : syracuseStep 4957505 = 3718129) B3718129
theorem B3305003 : Blo 2201435 3305003 := bstep (se 1 (by rfl) ⟨2478752, by rfl⟩ : syracuseStep 3305003 = 4957505) B4957505
theorem B2203335 : Blo 2201435 2203335 := bstep (se 1 (by rfl) ⟨1652501, by rfl⟩ : syracuseStep 2203335 = 3305003) B3305003
theorem B2478757 : Blo 2201435 2478757 := bbase (se 4 (by rfl) ⟨232383, by rfl⟩ : syracuseStep 2478757 = 464767) (by norm_num)
theorem B3305009 : Blo 2201435 3305009 := bstep (se 2 (by rfl) ⟨1239378, by rfl⟩ : syracuseStep 3305009 = 2478757) B2478757
theorem B2203339 : Blo 2201435 2203339 := bstep (se 1 (by rfl) ⟨1652504, by rfl⟩ : syracuseStep 2203339 = 3305009) B3305009
theorem B3626293 : Blo 2201435 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B4835057 : Blo 2201435 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B51573941 : Blo 2201435 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B34382627 : Blo 2201435 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B22921751 : Blo 2201435 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B15281167 : Blo 2201435 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B325998229 : Blo 2201435 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B434664305 : Blo 2201435 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B289776203 : Blo 2201435 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B193184135 : Blo 2201435 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B128789423 : Blo 2201435 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B85859615 : Blo 2201435 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B57239743 : Blo 2201435 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B76319657 : Blo 2201435 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B50879771 : Blo 2201435 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B33919847 : Blo 2201435 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B22613231 : Blo 2201435 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B15075487 : Blo 2201435 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B20100649 : Blo 2201435 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B26800865 : Blo 2201435 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B17867243 : Blo 2201435 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B47645981 : Blo 2201435 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B31763987 : Blo 2201435 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B21175991 : Blo 2201435 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B14117327 : Blo 2201435 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B9411551 : Blo 2201435 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B6274367 : Blo 2201435 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B4182911 : Blo 2201435 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B2788607 : Blo 2201435 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B7436285 : Blo 2201435 7436285 := bstep (se 3 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 7436285 = 2788607) B2788607
theorem B4957523 : Blo 2201435 4957523 := bstep (se 1 (by rfl) ⟨3718142, by rfl⟩ : syracuseStep 4957523 = 7436285) B7436285
theorem B3305015 : Blo 2201435 3305015 := bstep (se 1 (by rfl) ⟨2478761, by rfl⟩ : syracuseStep 3305015 = 4957523) B4957523
theorem B2203343 : Blo 2201435 2203343 := bstep (se 1 (by rfl) ⟨1652507, by rfl⟩ : syracuseStep 2203343 = 3305015) B3305015
theorem B3305021 : Blo 2201435 3305021 := bbase (se 3 (by rfl) ⟨619691, by rfl⟩ : syracuseStep 3305021 = 1239383) (by norm_num)
theorem B2203347 : Blo 2201435 2203347 := bstep (se 1 (by rfl) ⟨1652510, by rfl⟩ : syracuseStep 2203347 = 3305021) B3305021
theorem B4957541 : Blo 2201435 4957541 := bbase (se 4 (by rfl) ⟨464769, by rfl⟩ : syracuseStep 4957541 = 929539) (by norm_num)
theorem B3305027 : Blo 2201435 3305027 := bstep (se 1 (by rfl) ⟨2478770, by rfl⟩ : syracuseStep 3305027 = 4957541) B4957541
theorem B2203351 : Blo 2201435 2203351 := bstep (se 1 (by rfl) ⟨1652513, by rfl⟩ : syracuseStep 2203351 = 3305027) B3305027
theorem B5577245 : Blo 2201435 5577245 := bbase (se 3 (by rfl) ⟨1045733, by rfl⟩ : syracuseStep 5577245 = 2091467) (by norm_num)
theorem B3718163 : Blo 2201435 3718163 := bstep (se 1 (by rfl) ⟨2788622, by rfl⟩ : syracuseStep 3718163 = 5577245) B5577245
theorem B2478775 : Blo 2201435 2478775 := bstep (se 1 (by rfl) ⟨1859081, by rfl⟩ : syracuseStep 2478775 = 3718163) B3718163
theorem B3305033 : Blo 2201435 3305033 := bstep (se 2 (by rfl) ⟨1239387, by rfl⟩ : syracuseStep 3305033 = 2478775) B2478775
theorem B2203355 : Blo 2201435 2203355 := bstep (se 1 (by rfl) ⟨1652516, by rfl⟩ : syracuseStep 2203355 = 3305033) B3305033
theorem B4182941 : Blo 2201435 4182941 := bbase (se 3 (by rfl) ⟨784301, by rfl⟩ : syracuseStep 4182941 = 1568603) (by norm_num)
theorem B11154509 : Blo 2201435 11154509 := bstep (se 3 (by rfl) ⟨2091470, by rfl⟩ : syracuseStep 11154509 = 4182941) B4182941
theorem B7436339 : Blo 2201435 7436339 := bstep (se 1 (by rfl) ⟨5577254, by rfl⟩ : syracuseStep 7436339 = 11154509) B11154509
theorem B4957559 : Blo 2201435 4957559 := bstep (se 1 (by rfl) ⟨3718169, by rfl⟩ : syracuseStep 4957559 = 7436339) B7436339
theorem B3305039 : Blo 2201435 3305039 := bstep (se 1 (by rfl) ⟨2478779, by rfl⟩ : syracuseStep 3305039 = 4957559) B4957559
theorem B2203359 : Blo 2201435 2203359 := bstep (se 1 (by rfl) ⟨1652519, by rfl⟩ : syracuseStep 2203359 = 3305039) B3305039
theorem B3305045 : Blo 2201435 3305045 := bbase (se 8 (by rfl) ⟨19365, by rfl⟩ : syracuseStep 3305045 = 38731) (by norm_num)
theorem B2203363 : Blo 2201435 2203363 := bstep (se 1 (by rfl) ⟨1652522, by rfl⟩ : syracuseStep 2203363 = 3305045) B3305045
theorem B9411653 : Blo 2201435 9411653 := bbase (se 4 (by rfl) ⟨882342, by rfl⟩ : syracuseStep 9411653 = 1764685) (by norm_num)
theorem B6274435 : Blo 2201435 6274435 := bstep (se 1 (by rfl) ⟨4705826, by rfl⟩ : syracuseStep 6274435 = 9411653) B9411653
theorem B8365913 : Blo 2201435 8365913 := bstep (se 2 (by rfl) ⟨3137217, by rfl⟩ : syracuseStep 8365913 = 6274435) B6274435
theorem B5577275 : Blo 2201435 5577275 := bstep (se 1 (by rfl) ⟨4182956, by rfl⟩ : syracuseStep 5577275 = 8365913) B8365913
theorem B3718183 : Blo 2201435 3718183 := bstep (se 1 (by rfl) ⟨2788637, by rfl⟩ : syracuseStep 3718183 = 5577275) B5577275
theorem B4957577 : Blo 2201435 4957577 := bstep (se 2 (by rfl) ⟨1859091, by rfl⟩ : syracuseStep 4957577 = 3718183) B3718183
theorem B3305051 : Blo 2201435 3305051 := bstep (se 1 (by rfl) ⟨2478788, by rfl⟩ : syracuseStep 3305051 = 4957577) B4957577
theorem B2203367 : Blo 2201435 2203367 := bstep (se 1 (by rfl) ⟨1652525, by rfl⟩ : syracuseStep 2203367 = 3305051) B3305051
theorem B2478793 : Blo 2201435 2478793 := bbase (se 2 (by rfl) ⟨929547, by rfl⟩ : syracuseStep 2478793 = 1859095) (by norm_num)
theorem B3305057 : Blo 2201435 3305057 := bstep (se 2 (by rfl) ⟨1239396, by rfl⟩ : syracuseStep 3305057 = 2478793) B2478793
theorem B2203371 : Blo 2201435 2203371 := bstep (se 1 (by rfl) ⟨1652528, by rfl⟩ : syracuseStep 2203371 = 3305057) B3305057
theorem B2647037 : Blo 2201435 2647037 := bbase (se 3 (by rfl) ⟨496319, by rfl⟩ : syracuseStep 2647037 = 992639) (by norm_num)
theorem B7058765 : Blo 2201435 7058765 := bstep (se 3 (by rfl) ⟨1323518, by rfl⟩ : syracuseStep 7058765 = 2647037) B2647037
theorem B18823373 : Blo 2201435 18823373 := bstep (se 3 (by rfl) ⟨3529382, by rfl⟩ : syracuseStep 18823373 = 7058765) B7058765
theorem B12548915 : Blo 2201435 12548915 := bstep (se 1 (by rfl) ⟨9411686, by rfl⟩ : syracuseStep 12548915 = 18823373) B18823373
theorem B8365943 : Blo 2201435 8365943 := bstep (se 1 (by rfl) ⟨6274457, by rfl⟩ : syracuseStep 8365943 = 12548915) B12548915
theorem B5577295 : Blo 2201435 5577295 := bstep (se 1 (by rfl) ⟨4182971, by rfl⟩ : syracuseStep 5577295 = 8365943) B8365943
theorem B7436393 : Blo 2201435 7436393 := bstep (se 2 (by rfl) ⟨2788647, by rfl⟩ : syracuseStep 7436393 = 5577295) B5577295
theorem B4957595 : Blo 2201435 4957595 := bstep (se 1 (by rfl) ⟨3718196, by rfl⟩ : syracuseStep 4957595 = 7436393) B7436393
theorem B3305063 : Blo 2201435 3305063 := bstep (se 1 (by rfl) ⟨2478797, by rfl⟩ : syracuseStep 3305063 = 4957595) B4957595
theorem B2203375 : Blo 2201435 2203375 := bstep (se 1 (by rfl) ⟨1652531, by rfl⟩ : syracuseStep 2203375 = 3305063) B3305063
theorem B3305069 : Blo 2201435 3305069 := bbase (se 3 (by rfl) ⟨619700, by rfl⟩ : syracuseStep 3305069 = 1239401) (by norm_num)
theorem B2203379 : Blo 2201435 2203379 := bstep (se 1 (by rfl) ⟨1652534, by rfl⟩ : syracuseStep 2203379 = 3305069) B3305069
theorem B4957613 : Blo 2201435 4957613 := bbase (se 3 (by rfl) ⟨929552, by rfl⟩ : syracuseStep 4957613 = 1859105) (by norm_num)
theorem B3305075 : Blo 2201435 3305075 := bstep (se 1 (by rfl) ⟨2478806, by rfl⟩ : syracuseStep 3305075 = 4957613) B4957613
theorem B2203383 : Blo 2201435 2203383 := bstep (se 1 (by rfl) ⟨1652537, by rfl⟩ : syracuseStep 2203383 = 3305075) B3305075
theorem B2512633 : Blo 2201435 2512633 := bbase (se 2 (by rfl) ⟨942237, by rfl⟩ : syracuseStep 2512633 = 1884475) (by norm_num)
theorem B3350177 : Blo 2201435 3350177 := bstep (se 2 (by rfl) ⟨1256316, by rfl⟩ : syracuseStep 3350177 = 2512633) B2512633
theorem B2233451 : Blo 2201435 2233451 := bstep (se 1 (by rfl) ⟨1675088, by rfl⟩ : syracuseStep 2233451 = 3350177) B3350177
theorem B5955869 : Blo 2201435 5955869 := bstep (se 3 (by rfl) ⟨1116725, by rfl⟩ : syracuseStep 5955869 = 2233451) B2233451
theorem B3970579 : Blo 2201435 3970579 := bstep (se 1 (by rfl) ⟨2977934, by rfl⟩ : syracuseStep 3970579 = 5955869) B5955869
theorem B5294105 : Blo 2201435 5294105 := bstep (se 2 (by rfl) ⟨1985289, by rfl⟩ : syracuseStep 5294105 = 3970579) B3970579
theorem B3529403 : Blo 2201435 3529403 := bstep (se 1 (by rfl) ⟨2647052, by rfl⟩ : syracuseStep 3529403 = 5294105) B5294105
theorem B2352935 : Blo 2201435 2352935 := bstep (se 1 (by rfl) ⟨1764701, by rfl⟩ : syracuseStep 2352935 = 3529403) B3529403
theorem B6274493 : Blo 2201435 6274493 := bstep (se 3 (by rfl) ⟨1176467, by rfl⟩ : syracuseStep 6274493 = 2352935) B2352935
theorem B4182995 : Blo 2201435 4182995 := bstep (se 1 (by rfl) ⟨3137246, by rfl⟩ : syracuseStep 4182995 = 6274493) B6274493
theorem B2788663 : Blo 2201435 2788663 := bstep (se 1 (by rfl) ⟨2091497, by rfl⟩ : syracuseStep 2788663 = 4182995) B4182995
theorem B3718217 : Blo 2201435 3718217 := bstep (se 2 (by rfl) ⟨1394331, by rfl⟩ : syracuseStep 3718217 = 2788663) B2788663
theorem B2478811 : Blo 2201435 2478811 := bstep (se 1 (by rfl) ⟨1859108, by rfl⟩ : syracuseStep 2478811 = 3718217) B3718217
theorem B3305081 : Blo 2201435 3305081 := bstep (se 2 (by rfl) ⟨1239405, by rfl⟩ : syracuseStep 3305081 = 2478811) B2478811
theorem B2203387 : Blo 2201435 2203387 := bstep (se 1 (by rfl) ⟨1652540, by rfl⟩ : syracuseStep 2203387 = 3305081) B3305081
theorem B29010965 : Blo 2201435 29010965 := bbase (se 6 (by rfl) ⟨679944, by rfl⟩ : syracuseStep 29010965 = 1359889) (by norm_num)
theorem B77362573 : Blo 2201435 77362573 := bstep (se 3 (by rfl) ⟨14505482, by rfl⟩ : syracuseStep 77362573 = 29010965) B29010965
theorem B103150097 : Blo 2201435 103150097 := bstep (se 2 (by rfl) ⟨38681286, by rfl⟩ : syracuseStep 103150097 = 77362573) B77362573
theorem B68766731 : Blo 2201435 68766731 := bstep (se 1 (by rfl) ⟨51575048, by rfl⟩ : syracuseStep 68766731 = 103150097) B103150097
theorem B45844487 : Blo 2201435 45844487 := bstep (se 1 (by rfl) ⟨34383365, by rfl⟩ : syracuseStep 45844487 = 68766731) B68766731
theorem B30562991 : Blo 2201435 30562991 := bstep (se 1 (by rfl) ⟨22922243, by rfl⟩ : syracuseStep 30562991 = 45844487) B45844487
theorem B20375327 : Blo 2201435 20375327 := bstep (se 1 (by rfl) ⟨15281495, by rfl⟩ : syracuseStep 20375327 = 30562991) B30562991
theorem B54334205 : Blo 2201435 54334205 := bstep (se 3 (by rfl) ⟨10187663, by rfl⟩ : syracuseStep 54334205 = 20375327) B20375327
theorem B36222803 : Blo 2201435 36222803 := bstep (se 1 (by rfl) ⟨27167102, by rfl⟩ : syracuseStep 36222803 = 54334205) B54334205
theorem B24148535 : Blo 2201435 24148535 := bstep (se 1 (by rfl) ⟨18111401, by rfl⟩ : syracuseStep 24148535 = 36222803) B36222803
theorem B257584373 : Blo 2201435 257584373 := bstep (se 5 (by rfl) ⟨12074267, by rfl⟩ : syracuseStep 257584373 = 24148535) B24148535
theorem B171722915 : Blo 2201435 171722915 := bstep (se 1 (by rfl) ⟨128792186, by rfl⟩ : syracuseStep 171722915 = 257584373) B257584373
theorem B114481943 : Blo 2201435 114481943 := bstep (se 1 (by rfl) ⟨85861457, by rfl⟩ : syracuseStep 114481943 = 171722915) B171722915
theorem B76321295 : Blo 2201435 76321295 := bstep (se 1 (by rfl) ⟨57240971, by rfl⟩ : syracuseStep 76321295 = 114481943) B114481943
theorem B50880863 : Blo 2201435 50880863 := bstep (se 1 (by rfl) ⟨38160647, by rfl⟩ : syracuseStep 50880863 = 76321295) B76321295
theorem B33920575 : Blo 2201435 33920575 := bstep (se 1 (by rfl) ⟨25440431, by rfl⟩ : syracuseStep 33920575 = 50880863) B50880863
theorem B723638933 : Blo 2201435 723638933 := bstep (se 6 (by rfl) ⟨16960287, by rfl⟩ : syracuseStep 723638933 = 33920575) B33920575
theorem B482425955 : Blo 2201435 482425955 := bstep (se 1 (by rfl) ⟨361819466, by rfl⟩ : syracuseStep 482425955 = 723638933) B723638933
theorem B321617303 : Blo 2201435 321617303 := bstep (se 1 (by rfl) ⟨241212977, by rfl⟩ : syracuseStep 321617303 = 482425955) B482425955
theorem B214411535 : Blo 2201435 214411535 := bstep (se 1 (by rfl) ⟨160808651, by rfl⟩ : syracuseStep 214411535 = 321617303) B321617303
theorem B142941023 : Blo 2201435 142941023 := bstep (se 1 (by rfl) ⟨107205767, by rfl⟩ : syracuseStep 142941023 = 214411535) B214411535
theorem B95294015 : Blo 2201435 95294015 := bstep (se 1 (by rfl) ⟨71470511, by rfl⟩ : syracuseStep 95294015 = 142941023) B142941023
theorem B63529343 : Blo 2201435 63529343 := bstep (se 1 (by rfl) ⟨47647007, by rfl⟩ : syracuseStep 63529343 = 95294015) B95294015
theorem B42352895 : Blo 2201435 42352895 := bstep (se 1 (by rfl) ⟨31764671, by rfl⟩ : syracuseStep 42352895 = 63529343) B63529343
theorem B28235263 : Blo 2201435 28235263 := bstep (se 1 (by rfl) ⟨21176447, by rfl⟩ : syracuseStep 28235263 = 42352895) B42352895
theorem B37647017 : Blo 2201435 37647017 := bstep (se 2 (by rfl) ⟨14117631, by rfl⟩ : syracuseStep 37647017 = 28235263) B28235263
theorem B25098011 : Blo 2201435 25098011 := bstep (se 1 (by rfl) ⟨18823508, by rfl⟩ : syracuseStep 25098011 = 37647017) B37647017
theorem B16732007 : Blo 2201435 16732007 := bstep (se 1 (by rfl) ⟨12549005, by rfl⟩ : syracuseStep 16732007 = 25098011) B25098011
theorem B11154671 : Blo 2201435 11154671 := bstep (se 1 (by rfl) ⟨8366003, by rfl⟩ : syracuseStep 11154671 = 16732007) B16732007
theorem B7436447 : Blo 2201435 7436447 := bstep (se 1 (by rfl) ⟨5577335, by rfl⟩ : syracuseStep 7436447 = 11154671) B11154671
theorem B4957631 : Blo 2201435 4957631 := bstep (se 1 (by rfl) ⟨3718223, by rfl⟩ : syracuseStep 4957631 = 7436447) B7436447
theorem B3305087 : Blo 2201435 3305087 := bstep (se 1 (by rfl) ⟨2478815, by rfl⟩ : syracuseStep 3305087 = 4957631) B4957631
theorem B2203391 : Blo 2201435 2203391 := bstep (se 1 (by rfl) ⟨1652543, by rfl⟩ : syracuseStep 2203391 = 3305087) B3305087
theorem B3305093 : Blo 2201435 3305093 := bbase (se 4 (by rfl) ⟨309852, by rfl⟩ : syracuseStep 3305093 = 619705) (by norm_num)
theorem B2203395 : Blo 2201435 2203395 := bstep (se 1 (by rfl) ⟨1652546, by rfl⟩ : syracuseStep 2203395 = 3305093) B3305093
theorem B3718237 : Blo 2201435 3718237 := bbase (se 3 (by rfl) ⟨697169, by rfl⟩ : syracuseStep 3718237 = 1394339) (by norm_num)
theorem B4957649 : Blo 2201435 4957649 := bstep (se 2 (by rfl) ⟨1859118, by rfl⟩ : syracuseStep 4957649 = 3718237) B3718237
theorem B3305099 : Blo 2201435 3305099 := bstep (se 1 (by rfl) ⟨2478824, by rfl⟩ : syracuseStep 3305099 = 4957649) B4957649
theorem B2203399 : Blo 2201435 2203399 := bstep (se 1 (by rfl) ⟨1652549, by rfl⟩ : syracuseStep 2203399 = 3305099) B3305099
theorem B2478829 : Blo 2201435 2478829 := bbase (se 3 (by rfl) ⟨464780, by rfl⟩ : syracuseStep 2478829 = 929561) (by norm_num)
theorem B3305105 : Blo 2201435 3305105 := bstep (se 2 (by rfl) ⟨1239414, by rfl⟩ : syracuseStep 3305105 = 2478829) B2478829
theorem B2203403 : Blo 2201435 2203403 := bstep (se 1 (by rfl) ⟨1652552, by rfl⟩ : syracuseStep 2203403 = 3305105) B3305105
theorem B7436501 : Blo 2201435 7436501 := bbase (se 7 (by rfl) ⟨87146, by rfl⟩ : syracuseStep 7436501 = 174293) (by norm_num)
theorem B4957667 : Blo 2201435 4957667 := bstep (se 1 (by rfl) ⟨3718250, by rfl⟩ : syracuseStep 4957667 = 7436501) B7436501
theorem B3305111 : Blo 2201435 3305111 := bstep (se 1 (by rfl) ⟨2478833, by rfl⟩ : syracuseStep 3305111 = 4957667) B4957667
theorem B2203407 : Blo 2201435 2203407 := bstep (se 1 (by rfl) ⟨1652555, by rfl⟩ : syracuseStep 2203407 = 3305111) B3305111
theorem B3305117 : Blo 2201435 3305117 := bbase (se 3 (by rfl) ⟨619709, by rfl⟩ : syracuseStep 3305117 = 1239419) (by norm_num)
theorem B2203411 : Blo 2201435 2203411 := bstep (se 1 (by rfl) ⟨1652558, by rfl⟩ : syracuseStep 2203411 = 3305117) B3305117
theorem B4957685 : Blo 2201435 4957685 := bbase (se 5 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 4957685 = 464783) (by norm_num)
theorem B3305123 : Blo 2201435 3305123 := bstep (se 1 (by rfl) ⟨2478842, by rfl⟩ : syracuseStep 3305123 = 4957685) B4957685
theorem B2203415 : Blo 2201435 2203415 := bstep (se 1 (by rfl) ⟨1652561, by rfl⟩ : syracuseStep 2203415 = 3305123) B3305123
theorem B10187797 : Blo 2201435 10187797 := bbase (se 6 (by rfl) ⟨238776, by rfl⟩ : syracuseStep 10187797 = 477553) (by norm_num)
theorem B13583729 : Blo 2201435 13583729 := bstep (se 2 (by rfl) ⟨5093898, by rfl⟩ : syracuseStep 13583729 = 10187797) B10187797
theorem B9055819 : Blo 2201435 9055819 := bstep (se 1 (by rfl) ⟨6791864, by rfl⟩ : syracuseStep 9055819 = 13583729) B13583729
theorem B48297701 : Blo 2201435 48297701 := bstep (se 4 (by rfl) ⟨4527909, by rfl⟩ : syracuseStep 48297701 = 9055819) B9055819
theorem B32198467 : Blo 2201435 32198467 := bstep (se 1 (by rfl) ⟨24148850, by rfl⟩ : syracuseStep 32198467 = 48297701) B48297701
theorem B42931289 : Blo 2201435 42931289 := bstep (se 2 (by rfl) ⟨16099233, by rfl⟩ : syracuseStep 42931289 = 32198467) B32198467
theorem B28620859 : Blo 2201435 28620859 := bstep (se 1 (by rfl) ⟨21465644, by rfl⟩ : syracuseStep 28620859 = 42931289) B42931289
theorem B38161145 : Blo 2201435 38161145 := bstep (se 2 (by rfl) ⟨14310429, by rfl⟩ : syracuseStep 38161145 = 28620859) B28620859
theorem B25440763 : Blo 2201435 25440763 := bstep (se 1 (by rfl) ⟨19080572, by rfl⟩ : syracuseStep 25440763 = 38161145) B38161145
theorem B33921017 : Blo 2201435 33921017 := bstep (se 2 (by rfl) ⟨12720381, by rfl⟩ : syracuseStep 33921017 = 25440763) B25440763
theorem B22614011 : Blo 2201435 22614011 := bstep (se 1 (by rfl) ⟨16960508, by rfl⟩ : syracuseStep 22614011 = 33921017) B33921017
theorem B15076007 : Blo 2201435 15076007 := bstep (se 1 (by rfl) ⟨11307005, by rfl⟩ : syracuseStep 15076007 = 22614011) B22614011
theorem B10050671 : Blo 2201435 10050671 := bstep (se 1 (by rfl) ⟨7538003, by rfl⟩ : syracuseStep 10050671 = 15076007) B15076007
theorem B6700447 : Blo 2201435 6700447 := bstep (se 1 (by rfl) ⟨5025335, by rfl⟩ : syracuseStep 6700447 = 10050671) B10050671
theorem B35735717 : Blo 2201435 35735717 := bstep (se 4 (by rfl) ⟨3350223, by rfl⟩ : syracuseStep 35735717 = 6700447) B6700447
theorem B23823811 : Blo 2201435 23823811 := bstep (se 1 (by rfl) ⟨17867858, by rfl⟩ : syracuseStep 23823811 = 35735717) B35735717
theorem B31765081 : Blo 2201435 31765081 := bstep (se 2 (by rfl) ⟨11911905, by rfl⟩ : syracuseStep 31765081 = 23823811) B23823811
theorem B42353441 : Blo 2201435 42353441 := bstep (se 2 (by rfl) ⟨15882540, by rfl⟩ : syracuseStep 42353441 = 31765081) B31765081
theorem B28235627 : Blo 2201435 28235627 := bstep (se 1 (by rfl) ⟨21176720, by rfl⟩ : syracuseStep 28235627 = 42353441) B42353441
theorem B18823751 : Blo 2201435 18823751 := bstep (se 1 (by rfl) ⟨14117813, by rfl⟩ : syracuseStep 18823751 = 28235627) B28235627
theorem B12549167 : Blo 2201435 12549167 := bstep (se 1 (by rfl) ⟨9411875, by rfl⟩ : syracuseStep 12549167 = 18823751) B18823751
theorem B8366111 : Blo 2201435 8366111 := bstep (se 1 (by rfl) ⟨6274583, by rfl⟩ : syracuseStep 8366111 = 12549167) B12549167
theorem B5577407 : Blo 2201435 5577407 := bstep (se 1 (by rfl) ⟨4183055, by rfl⟩ : syracuseStep 5577407 = 8366111) B8366111
theorem B3718271 : Blo 2201435 3718271 := bstep (se 1 (by rfl) ⟨2788703, by rfl⟩ : syracuseStep 3718271 = 5577407) B5577407
theorem B2478847 : Blo 2201435 2478847 := bstep (se 1 (by rfl) ⟨1859135, by rfl⟩ : syracuseStep 2478847 = 3718271) B3718271
theorem B3305129 : Blo 2201435 3305129 := bstep (se 2 (by rfl) ⟨1239423, by rfl⟩ : syracuseStep 3305129 = 2478847) B2478847
theorem B2203419 : Blo 2201435 2203419 := bstep (se 1 (by rfl) ⟨1652564, by rfl⟩ : syracuseStep 2203419 = 3305129) B3305129
theorem B2352973 : Blo 2201435 2352973 := bbase (se 3 (by rfl) ⟨441182, by rfl⟩ : syracuseStep 2352973 = 882365) (by norm_num)
theorem B3137297 : Blo 2201435 3137297 := bstep (se 2 (by rfl) ⟨1176486, by rfl⟩ : syracuseStep 3137297 = 2352973) B2352973
theorem B8366125 : Blo 2201435 8366125 := bstep (se 3 (by rfl) ⟨1568648, by rfl⟩ : syracuseStep 8366125 = 3137297) B3137297
theorem B11154833 : Blo 2201435 11154833 := bstep (se 2 (by rfl) ⟨4183062, by rfl⟩ : syracuseStep 11154833 = 8366125) B8366125
theorem B7436555 : Blo 2201435 7436555 := bstep (se 1 (by rfl) ⟨5577416, by rfl⟩ : syracuseStep 7436555 = 11154833) B11154833
theorem B4957703 : Blo 2201435 4957703 := bstep (se 1 (by rfl) ⟨3718277, by rfl⟩ : syracuseStep 4957703 = 7436555) B7436555
theorem B3305135 : Blo 2201435 3305135 := bstep (se 1 (by rfl) ⟨2478851, by rfl⟩ : syracuseStep 3305135 = 4957703) B4957703
theorem B2203423 : Blo 2201435 2203423 := bstep (se 1 (by rfl) ⟨1652567, by rfl⟩ : syracuseStep 2203423 = 3305135) B3305135
theorem B3305141 : Blo 2201435 3305141 := bbase (se 5 (by rfl) ⟨154928, by rfl⟩ : syracuseStep 3305141 = 309857) (by norm_num)
theorem B2203427 : Blo 2201435 2203427 := bstep (se 1 (by rfl) ⟨1652570, by rfl⟩ : syracuseStep 2203427 = 3305141) B3305141
theorem B5577437 : Blo 2201435 5577437 := bbase (se 3 (by rfl) ⟨1045769, by rfl⟩ : syracuseStep 5577437 = 2091539) (by norm_num)
theorem B3718291 : Blo 2201435 3718291 := bstep (se 1 (by rfl) ⟨2788718, by rfl⟩ : syracuseStep 3718291 = 5577437) B5577437
theorem B4957721 : Blo 2201435 4957721 := bstep (se 2 (by rfl) ⟨1859145, by rfl⟩ : syracuseStep 4957721 = 3718291) B3718291
theorem B3305147 : Blo 2201435 3305147 := bstep (se 1 (by rfl) ⟨2478860, by rfl⟩ : syracuseStep 3305147 = 4957721) B4957721
theorem B2203431 : Blo 2201435 2203431 := bstep (se 1 (by rfl) ⟨1652573, by rfl⟩ : syracuseStep 2203431 = 3305147) B3305147
theorem B2478865 : Blo 2201435 2478865 := bbase (se 2 (by rfl) ⟨929574, by rfl⟩ : syracuseStep 2478865 = 1859149) (by norm_num)
theorem B3305153 : Blo 2201435 3305153 := bstep (se 2 (by rfl) ⟨1239432, by rfl⟩ : syracuseStep 3305153 = 2478865) B2478865
theorem B2203435 : Blo 2201435 2203435 := bstep (se 1 (by rfl) ⟨1652576, by rfl⟩ : syracuseStep 2203435 = 3305153) B3305153
theorem C0 (j : ℕ) (h1 : 550358 ≤ j) (h2 : j ≤ 550858) : Blo 2201435 (4 * j + 3) := by
  interval_cases j
  · exact B2201435
  · exact B2201439
  · exact B2201443
  · exact B2201447
  · exact B2201451
  · exact B2201455
  · exact B2201459
  · exact B2201463
  · exact B2201467
  · exact B2201471
  · exact B2201475
  · exact B2201479
  · exact B2201483
  · exact B2201487
  · exact B2201491
  · exact B2201495
  · exact B2201499
  · exact B2201503
  · exact B2201507
  · exact B2201511
  · exact B2201515
  · exact B2201519
  · exact B2201523
  · exact B2201527
  · exact B2201531
  · exact B2201535
  · exact B2201539
  · exact B2201543
  · exact B2201547
  · exact B2201551
  · exact B2201555
  · exact B2201559
  · exact B2201563
  · exact B2201567
  · exact B2201571
  · exact B2201575
  · exact B2201579
  · exact B2201583
  · exact B2201587
  · exact B2201591
  · exact B2201595
  · exact B2201599
  · exact B2201603
  · exact B2201607
  · exact B2201611
  · exact B2201615
  · exact B2201619
  · exact B2201623
  · exact B2201627
  · exact B2201631
  · exact B2201635
  · exact B2201639
  · exact B2201643
  · exact B2201647
  · exact B2201651
  · exact B2201655
  · exact B2201659
  · exact B2201663
  · exact B2201667
  · exact B2201671
  · exact B2201675
  · exact B2201679
  · exact B2201683
  · exact B2201687
  · exact B2201691
  · exact B2201695
  · exact B2201699
  · exact B2201703
  · exact B2201707
  · exact B2201711
  · exact B2201715
  · exact B2201719
  · exact B2201723
  · exact B2201727
  · exact B2201731
  · exact B2201735
  · exact B2201739
  · exact B2201743
  · exact B2201747
  · exact B2201751
  · exact B2201755
  · exact B2201759
  · exact B2201763
  · exact B2201767
  · exact B2201771
  · exact B2201775
  · exact B2201779
  · exact B2201783
  · exact B2201787
  · exact B2201791
  · exact B2201795
  · exact B2201799
  · exact B2201803
  · exact B2201807
  · exact B2201811
  · exact B2201815
  · exact B2201819
  · exact B2201823
  · exact B2201827
  · exact B2201831
  · exact B2201835
  · exact B2201839
  · exact B2201843
  · exact B2201847
  · exact B2201851
  · exact B2201855
  · exact B2201859
  · exact B2201863
  · exact B2201867
  · exact B2201871
  · exact B2201875
  · exact B2201879
  · exact B2201883
  · exact B2201887
  · exact B2201891
  · exact B2201895
  · exact B2201899
  · exact B2201903
  · exact B2201907
  · exact B2201911
  · exact B2201915
  · exact B2201919
  · exact B2201923
  · exact B2201927
  · exact B2201931
  · exact B2201935
  · exact B2201939
  · exact B2201943
  · exact B2201947
  · exact B2201951
  · exact B2201955
  · exact B2201959
  · exact B2201963
  · exact B2201967
  · exact B2201971
  · exact B2201975
  · exact B2201979
  · exact B2201983
  · exact B2201987
  · exact B2201991
  · exact B2201995
  · exact B2201999
  · exact B2202003
  · exact B2202007
  · exact B2202011
  · exact B2202015
  · exact B2202019
  · exact B2202023
  · exact B2202027
  · exact B2202031
  · exact B2202035
  · exact B2202039
  · exact B2202043
  · exact B2202047
  · exact B2202051
  · exact B2202055
  · exact B2202059
  · exact B2202063
  · exact B2202067
  · exact B2202071
  · exact B2202075
  · exact B2202079
  · exact B2202083
  · exact B2202087
  · exact B2202091
  · exact B2202095
  · exact B2202099
  · exact B2202103
  · exact B2202107
  · exact B2202111
  · exact B2202115
  · exact B2202119
  · exact B2202123
  · exact B2202127
  · exact B2202131
  · exact B2202135
  · exact B2202139
  · exact B2202143
  · exact B2202147
  · exact B2202151
  · exact B2202155
  · exact B2202159
  · exact B2202163
  · exact B2202167
  · exact B2202171
  · exact B2202175
  · exact B2202179
  · exact B2202183
  · exact B2202187
  · exact B2202191
  · exact B2202195
  · exact B2202199
  · exact B2202203
  · exact B2202207
  · exact B2202211
  · exact B2202215
  · exact B2202219
  · exact B2202223
  · exact B2202227
  · exact B2202231
  · exact B2202235
  · exact B2202239
  · exact B2202243
  · exact B2202247
  · exact B2202251
  · exact B2202255
  · exact B2202259
  · exact B2202263
  · exact B2202267
  · exact B2202271
  · exact B2202275
  · exact B2202279
  · exact B2202283
  · exact B2202287
  · exact B2202291
  · exact B2202295
  · exact B2202299
  · exact B2202303
  · exact B2202307
  · exact B2202311
  · exact B2202315
  · exact B2202319
  · exact B2202323
  · exact B2202327
  · exact B2202331
  · exact B2202335
  · exact B2202339
  · exact B2202343
  · exact B2202347
  · exact B2202351
  · exact B2202355
  · exact B2202359
  · exact B2202363
  · exact B2202367
  · exact B2202371
  · exact B2202375
  · exact B2202379
  · exact B2202383
  · exact B2202387
  · exact B2202391
  · exact B2202395
  · exact B2202399
  · exact B2202403
  · exact B2202407
  · exact B2202411
  · exact B2202415
  · exact B2202419
  · exact B2202423
  · exact B2202427
  · exact B2202431
  · exact B2202435
  · exact B2202439
  · exact B2202443
  · exact B2202447
  · exact B2202451
  · exact B2202455
  · exact B2202459
  · exact B2202463
  · exact B2202467
  · exact B2202471
  · exact B2202475
  · exact B2202479
  · exact B2202483
  · exact B2202487
  · exact B2202491
  · exact B2202495
  · exact B2202499
  · exact B2202503
  · exact B2202507
  · exact B2202511
  · exact B2202515
  · exact B2202519
  · exact B2202523
  · exact B2202527
  · exact B2202531
  · exact B2202535
  · exact B2202539
  · exact B2202543
  · exact B2202547
  · exact B2202551
  · exact B2202555
  · exact B2202559
  · exact B2202563
  · exact B2202567
  · exact B2202571
  · exact B2202575
  · exact B2202579
  · exact B2202583
  · exact B2202587
  · exact B2202591
  · exact B2202595
  · exact B2202599
  · exact B2202603
  · exact B2202607
  · exact B2202611
  · exact B2202615
  · exact B2202619
  · exact B2202623
  · exact B2202627
  · exact B2202631
  · exact B2202635
  · exact B2202639
  · exact B2202643
  · exact B2202647
  · exact B2202651
  · exact B2202655
  · exact B2202659
  · exact B2202663
  · exact B2202667
  · exact B2202671
  · exact B2202675
  · exact B2202679
  · exact B2202683
  · exact B2202687
  · exact B2202691
  · exact B2202695
  · exact B2202699
  · exact B2202703
  · exact B2202707
  · exact B2202711
  · exact B2202715
  · exact B2202719
  · exact B2202723
  · exact B2202727
  · exact B2202731
  · exact B2202735
  · exact B2202739
  · exact B2202743
  · exact B2202747
  · exact B2202751
  · exact B2202755
  · exact B2202759
  · exact B2202763
  · exact B2202767
  · exact B2202771
  · exact B2202775
  · exact B2202779
  · exact B2202783
  · exact B2202787
  · exact B2202791
  · exact B2202795
  · exact B2202799
  · exact B2202803
  · exact B2202807
  · exact B2202811
  · exact B2202815
  · exact B2202819
  · exact B2202823
  · exact B2202827
  · exact B2202831
  · exact B2202835
  · exact B2202839
  · exact B2202843
  · exact B2202847
  · exact B2202851
  · exact B2202855
  · exact B2202859
  · exact B2202863
  · exact B2202867
  · exact B2202871
  · exact B2202875
  · exact B2202879
  · exact B2202883
  · exact B2202887
  · exact B2202891
  · exact B2202895
  · exact B2202899
  · exact B2202903
  · exact B2202907
  · exact B2202911
  · exact B2202915
  · exact B2202919
  · exact B2202923
  · exact B2202927
  · exact B2202931
  · exact B2202935
  · exact B2202939
  · exact B2202943
  · exact B2202947
  · exact B2202951
  · exact B2202955
  · exact B2202959
  · exact B2202963
  · exact B2202967
  · exact B2202971
  · exact B2202975
  · exact B2202979
  · exact B2202983
  · exact B2202987
  · exact B2202991
  · exact B2202995
  · exact B2202999
  · exact B2203003
  · exact B2203007
  · exact B2203011
  · exact B2203015
  · exact B2203019
  · exact B2203023
  · exact B2203027
  · exact B2203031
  · exact B2203035
  · exact B2203039
  · exact B2203043
  · exact B2203047
  · exact B2203051
  · exact B2203055
  · exact B2203059
  · exact B2203063
  · exact B2203067
  · exact B2203071
  · exact B2203075
  · exact B2203079
  · exact B2203083
  · exact B2203087
  · exact B2203091
  · exact B2203095
  · exact B2203099
  · exact B2203103
  · exact B2203107
  · exact B2203111
  · exact B2203115
  · exact B2203119
  · exact B2203123
  · exact B2203127
  · exact B2203131
  · exact B2203135
  · exact B2203139
  · exact B2203143
  · exact B2203147
  · exact B2203151
  · exact B2203155
  · exact B2203159
  · exact B2203163
  · exact B2203167
  · exact B2203171
  · exact B2203175
  · exact B2203179
  · exact B2203183
  · exact B2203187
  · exact B2203191
  · exact B2203195
  · exact B2203199
  · exact B2203203
  · exact B2203207
  · exact B2203211
  · exact B2203215
  · exact B2203219
  · exact B2203223
  · exact B2203227
  · exact B2203231
  · exact B2203235
  · exact B2203239
  · exact B2203243
  · exact B2203247
  · exact B2203251
  · exact B2203255
  · exact B2203259
  · exact B2203263
  · exact B2203267
  · exact B2203271
  · exact B2203275
  · exact B2203279
  · exact B2203283
  · exact B2203287
  · exact B2203291
  · exact B2203295
  · exact B2203299
  · exact B2203303
  · exact B2203307
  · exact B2203311
  · exact B2203315
  · exact B2203319
  · exact B2203323
  · exact B2203327
  · exact B2203331
  · exact B2203335
  · exact B2203339
  · exact B2203343
  · exact B2203347
  · exact B2203351
  · exact B2203355
  · exact B2203359
  · exact B2203363
  · exact B2203367
  · exact B2203371
  · exact B2203375
  · exact B2203379
  · exact B2203383
  · exact B2203387
  · exact B2203391
  · exact B2203395
  · exact B2203399
  · exact B2203403
  · exact B2203407
  · exact B2203411
  · exact B2203415
  · exact B2203419
  · exact B2203423
  · exact B2203427
  · exact B2203431
  · exact B2203435
theorem solution (m : ℕ) (hlo : 2201435 ≤ m) (hhi : m ≤ 2203435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 550358 ≤ j := by omega
    have hj2 : j ≤ 550858 := by omega
    have hb : Blo 2201435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
