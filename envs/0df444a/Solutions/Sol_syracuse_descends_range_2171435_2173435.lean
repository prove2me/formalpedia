-- Prove2me | solution 1 for syracuse_descends_range_2171435_2173435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:47.739126+00:00
-- url     : https://prove2.me/submissions/5464d61d-5e32-4eba-bfd7-24cd82be600a

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

theorem B2442865 : Blo 2171435 2442865 := bbase (se 2 (by rfl) ⟨916074, by rfl⟩ : syracuseStep 2442865 = 1832149) (by norm_num)
theorem B3257153 : Blo 2171435 3257153 := bstep (se 2 (by rfl) ⟨1221432, by rfl⟩ : syracuseStep 3257153 = 2442865) B2442865
theorem B2171435 : Blo 2171435 2171435 := bstep (se 1 (by rfl) ⟨1628576, by rfl⟩ : syracuseStep 2171435 = 3257153) B3257153
theorem B2544229 : Blo 2171435 2544229 := bbase (se 4 (by rfl) ⟨238521, by rfl⟩ : syracuseStep 2544229 = 477043) (by norm_num)
theorem B13569221 : Blo 2171435 13569221 := bstep (se 4 (by rfl) ⟨1272114, by rfl⟩ : syracuseStep 13569221 = 2544229) B2544229
theorem B36184589 : Blo 2171435 36184589 := bstep (se 3 (by rfl) ⟨6784610, by rfl⟩ : syracuseStep 36184589 = 13569221) B13569221
theorem B24123059 : Blo 2171435 24123059 := bstep (se 1 (by rfl) ⟨18092294, by rfl⟩ : syracuseStep 24123059 = 36184589) B36184589
theorem B16082039 : Blo 2171435 16082039 := bstep (se 1 (by rfl) ⟨12061529, by rfl⟩ : syracuseStep 16082039 = 24123059) B24123059
theorem B10721359 : Blo 2171435 10721359 := bstep (se 1 (by rfl) ⟨8041019, by rfl⟩ : syracuseStep 10721359 = 16082039) B16082039
theorem B14295145 : Blo 2171435 14295145 := bstep (se 2 (by rfl) ⟨5360679, by rfl⟩ : syracuseStep 14295145 = 10721359) B10721359
theorem B19060193 : Blo 2171435 19060193 := bstep (se 2 (by rfl) ⟨7147572, by rfl⟩ : syracuseStep 19060193 = 14295145) B14295145
theorem B12706795 : Blo 2171435 12706795 := bstep (se 1 (by rfl) ⟨9530096, by rfl⟩ : syracuseStep 12706795 = 19060193) B19060193
theorem B16942393 : Blo 2171435 16942393 := bstep (se 2 (by rfl) ⟨6353397, by rfl⟩ : syracuseStep 16942393 = 12706795) B12706795
theorem B22589857 : Blo 2171435 22589857 := bstep (se 2 (by rfl) ⟨8471196, by rfl⟩ : syracuseStep 22589857 = 16942393) B16942393
theorem B30119809 : Blo 2171435 30119809 := bstep (se 2 (by rfl) ⟨11294928, by rfl⟩ : syracuseStep 30119809 = 22589857) B22589857
theorem B40159745 : Blo 2171435 40159745 := bstep (se 2 (by rfl) ⟨15059904, by rfl⟩ : syracuseStep 40159745 = 30119809) B30119809
theorem B26773163 : Blo 2171435 26773163 := bstep (se 1 (by rfl) ⟨20079872, by rfl⟩ : syracuseStep 26773163 = 40159745) B40159745
theorem B17848775 : Blo 2171435 17848775 := bstep (se 1 (by rfl) ⟨13386581, by rfl⟩ : syracuseStep 17848775 = 26773163) B26773163
theorem B11899183 : Blo 2171435 11899183 := bstep (se 1 (by rfl) ⟨8924387, by rfl⟩ : syracuseStep 11899183 = 17848775) B17848775
theorem B15865577 : Blo 2171435 15865577 := bstep (se 2 (by rfl) ⟨5949591, by rfl⟩ : syracuseStep 15865577 = 11899183) B11899183
theorem B10577051 : Blo 2171435 10577051 := bstep (se 1 (by rfl) ⟨7932788, by rfl⟩ : syracuseStep 10577051 = 15865577) B15865577
theorem B7051367 : Blo 2171435 7051367 := bstep (se 1 (by rfl) ⟨5288525, by rfl⟩ : syracuseStep 7051367 = 10577051) B10577051
theorem B4700911 : Blo 2171435 4700911 := bstep (se 1 (by rfl) ⟨3525683, by rfl⟩ : syracuseStep 4700911 = 7051367) B7051367
theorem B6267881 : Blo 2171435 6267881 := bstep (se 2 (by rfl) ⟨2350455, by rfl⟩ : syracuseStep 6267881 = 4700911) B4700911
theorem B16714349 : Blo 2171435 16714349 := bstep (se 3 (by rfl) ⟨3133940, by rfl⟩ : syracuseStep 16714349 = 6267881) B6267881
theorem B11142899 : Blo 2171435 11142899 := bstep (se 1 (by rfl) ⟨8357174, by rfl⟩ : syracuseStep 11142899 = 16714349) B16714349
theorem B7428599 : Blo 2171435 7428599 := bstep (se 1 (by rfl) ⟨5571449, by rfl⟩ : syracuseStep 7428599 = 11142899) B11142899
theorem B4952399 : Blo 2171435 4952399 := bstep (se 1 (by rfl) ⟨3714299, by rfl⟩ : syracuseStep 4952399 = 7428599) B7428599
theorem B13206397 : Blo 2171435 13206397 := bstep (se 3 (by rfl) ⟨2476199, by rfl⟩ : syracuseStep 13206397 = 4952399) B4952399
theorem B17608529 : Blo 2171435 17608529 := bstep (se 2 (by rfl) ⟨6603198, by rfl⟩ : syracuseStep 17608529 = 13206397) B13206397
theorem B11739019 : Blo 2171435 11739019 := bstep (se 1 (by rfl) ⟨8804264, by rfl⟩ : syracuseStep 11739019 = 17608529) B17608529
theorem B15652025 : Blo 2171435 15652025 := bstep (se 2 (by rfl) ⟨5869509, by rfl⟩ : syracuseStep 15652025 = 11739019) B11739019
theorem B10434683 : Blo 2171435 10434683 := bstep (se 1 (by rfl) ⟨7826012, by rfl⟩ : syracuseStep 10434683 = 15652025) B15652025
theorem B6956455 : Blo 2171435 6956455 := bstep (se 1 (by rfl) ⟨5217341, by rfl⟩ : syracuseStep 6956455 = 10434683) B10434683
theorem B9275273 : Blo 2171435 9275273 := bstep (se 2 (by rfl) ⟨3478227, by rfl⟩ : syracuseStep 9275273 = 6956455) B6956455
theorem B6183515 : Blo 2171435 6183515 := bstep (se 1 (by rfl) ⟨4637636, by rfl⟩ : syracuseStep 6183515 = 9275273) B9275273
theorem B4122343 : Blo 2171435 4122343 := bstep (se 1 (by rfl) ⟨3091757, by rfl⟩ : syracuseStep 4122343 = 6183515) B6183515
theorem B5496457 : Blo 2171435 5496457 := bstep (se 2 (by rfl) ⟨2061171, by rfl⟩ : syracuseStep 5496457 = 4122343) B4122343
theorem B7328609 : Blo 2171435 7328609 := bstep (se 2 (by rfl) ⟨2748228, by rfl⟩ : syracuseStep 7328609 = 5496457) B5496457
theorem B4885739 : Blo 2171435 4885739 := bstep (se 1 (by rfl) ⟨3664304, by rfl⟩ : syracuseStep 4885739 = 7328609) B7328609
theorem B3257159 : Blo 2171435 3257159 := bstep (se 1 (by rfl) ⟨2442869, by rfl⟩ : syracuseStep 3257159 = 4885739) B4885739
theorem B2171439 : Blo 2171435 2171439 := bstep (se 1 (by rfl) ⟨1628579, by rfl⟩ : syracuseStep 2171439 = 3257159) B3257159
theorem B3257165 : Blo 2171435 3257165 := bbase (se 3 (by rfl) ⟨610718, by rfl⟩ : syracuseStep 3257165 = 1221437) (by norm_num)
theorem B2171443 : Blo 2171435 2171443 := bstep (se 1 (by rfl) ⟨1628582, by rfl⟩ : syracuseStep 2171443 = 3257165) B3257165
theorem B4885757 : Blo 2171435 4885757 := bbase (se 3 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 4885757 = 1832159) (by norm_num)
theorem B3257171 : Blo 2171435 3257171 := bstep (se 1 (by rfl) ⟨2442878, by rfl⟩ : syracuseStep 3257171 = 4885757) B4885757
theorem B2171447 : Blo 2171435 2171447 := bstep (se 1 (by rfl) ⟨1628585, by rfl⟩ : syracuseStep 2171447 = 3257171) B3257171
theorem B3664325 : Blo 2171435 3664325 := bbase (se 4 (by rfl) ⟨343530, by rfl⟩ : syracuseStep 3664325 = 687061) (by norm_num)
theorem B2442883 : Blo 2171435 2442883 := bstep (se 1 (by rfl) ⟨1832162, by rfl⟩ : syracuseStep 2442883 = 3664325) B3664325
theorem B3257177 : Blo 2171435 3257177 := bstep (se 2 (by rfl) ⟨1221441, by rfl⟩ : syracuseStep 3257177 = 2442883) B2442883
theorem B2171451 : Blo 2171435 2171451 := bstep (se 1 (by rfl) ⟨1628588, by rfl⟩ : syracuseStep 2171451 = 3257177) B3257177
theorem B16489493 : Blo 2171435 16489493 := bbase (se 6 (by rfl) ⟨386472, by rfl⟩ : syracuseStep 16489493 = 772945) (by norm_num)
theorem B10992995 : Blo 2171435 10992995 := bstep (se 1 (by rfl) ⟨8244746, by rfl⟩ : syracuseStep 10992995 = 16489493) B16489493
theorem B7328663 : Blo 2171435 7328663 := bstep (se 1 (by rfl) ⟨5496497, by rfl⟩ : syracuseStep 7328663 = 10992995) B10992995
theorem B4885775 : Blo 2171435 4885775 := bstep (se 1 (by rfl) ⟨3664331, by rfl⟩ : syracuseStep 4885775 = 7328663) B7328663
theorem B3257183 : Blo 2171435 3257183 := bstep (se 1 (by rfl) ⟨2442887, by rfl⟩ : syracuseStep 3257183 = 4885775) B4885775
theorem B2171455 : Blo 2171435 2171455 := bstep (se 1 (by rfl) ⟨1628591, by rfl⟩ : syracuseStep 2171455 = 3257183) B3257183
theorem B3257189 : Blo 2171435 3257189 := bbase (se 4 (by rfl) ⟨305361, by rfl⟩ : syracuseStep 3257189 = 610723) (by norm_num)
theorem B2171459 : Blo 2171435 2171459 := bstep (se 1 (by rfl) ⟨1628594, by rfl⟩ : syracuseStep 2171459 = 3257189) B3257189
theorem B4122389 : Blo 2171435 4122389 := bbase (se 6 (by rfl) ⟨96618, by rfl⟩ : syracuseStep 4122389 = 193237) (by norm_num)
theorem B2748259 : Blo 2171435 2748259 := bstep (se 1 (by rfl) ⟨2061194, by rfl⟩ : syracuseStep 2748259 = 4122389) B4122389
theorem B3664345 : Blo 2171435 3664345 := bstep (se 2 (by rfl) ⟨1374129, by rfl⟩ : syracuseStep 3664345 = 2748259) B2748259
theorem B4885793 : Blo 2171435 4885793 := bstep (se 2 (by rfl) ⟨1832172, by rfl⟩ : syracuseStep 4885793 = 3664345) B3664345
theorem B3257195 : Blo 2171435 3257195 := bstep (se 1 (by rfl) ⟨2442896, by rfl⟩ : syracuseStep 3257195 = 4885793) B4885793
theorem B2171463 : Blo 2171435 2171463 := bstep (se 1 (by rfl) ⟨1628597, by rfl⟩ : syracuseStep 2171463 = 3257195) B3257195
theorem B2442901 : Blo 2171435 2442901 := bbase (se 6 (by rfl) ⟨57255, by rfl⟩ : syracuseStep 2442901 = 114511) (by norm_num)
theorem B3257201 : Blo 2171435 3257201 := bstep (se 2 (by rfl) ⟨1221450, by rfl⟩ : syracuseStep 3257201 = 2442901) B2442901
theorem B2171467 : Blo 2171435 2171467 := bstep (se 1 (by rfl) ⟨1628600, by rfl⟩ : syracuseStep 2171467 = 3257201) B3257201
theorem B2748269 : Blo 2171435 2748269 := bbase (se 3 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 2748269 = 1030601) (by norm_num)
theorem B7328717 : Blo 2171435 7328717 := bstep (se 3 (by rfl) ⟨1374134, by rfl⟩ : syracuseStep 7328717 = 2748269) B2748269
theorem B4885811 : Blo 2171435 4885811 := bstep (se 1 (by rfl) ⟨3664358, by rfl⟩ : syracuseStep 4885811 = 7328717) B7328717
theorem B3257207 : Blo 2171435 3257207 := bstep (se 1 (by rfl) ⟨2442905, by rfl⟩ : syracuseStep 3257207 = 4885811) B4885811
theorem B2171471 : Blo 2171435 2171471 := bstep (se 1 (by rfl) ⟨1628603, by rfl⟩ : syracuseStep 2171471 = 3257207) B3257207
theorem B3257213 : Blo 2171435 3257213 := bbase (se 3 (by rfl) ⟨610727, by rfl⟩ : syracuseStep 3257213 = 1221455) (by norm_num)
theorem B2171475 : Blo 2171435 2171475 := bstep (se 1 (by rfl) ⟨1628606, by rfl⟩ : syracuseStep 2171475 = 3257213) B3257213
theorem B4885829 : Blo 2171435 4885829 := bbase (se 4 (by rfl) ⟨458046, by rfl⟩ : syracuseStep 4885829 = 916093) (by norm_num)
theorem B3257219 : Blo 2171435 3257219 := bstep (se 1 (by rfl) ⟨2442914, by rfl⟩ : syracuseStep 3257219 = 4885829) B4885829
theorem B2171479 : Blo 2171435 2171479 := bstep (se 1 (by rfl) ⟨1628609, by rfl⟩ : syracuseStep 2171479 = 3257219) B3257219
theorem B6956597 : Blo 2171435 6956597 := bbase (se 5 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 6956597 = 652181) (by norm_num)
theorem B4637731 : Blo 2171435 4637731 := bstep (se 1 (by rfl) ⟨3478298, by rfl⟩ : syracuseStep 4637731 = 6956597) B6956597
theorem B6183641 : Blo 2171435 6183641 := bstep (se 2 (by rfl) ⟨2318865, by rfl⟩ : syracuseStep 6183641 = 4637731) B4637731
theorem B4122427 : Blo 2171435 4122427 := bstep (se 1 (by rfl) ⟨3091820, by rfl⟩ : syracuseStep 4122427 = 6183641) B6183641
theorem B5496569 : Blo 2171435 5496569 := bstep (se 2 (by rfl) ⟨2061213, by rfl⟩ : syracuseStep 5496569 = 4122427) B4122427
theorem B3664379 : Blo 2171435 3664379 := bstep (se 1 (by rfl) ⟨2748284, by rfl⟩ : syracuseStep 3664379 = 5496569) B5496569
theorem B2442919 : Blo 2171435 2442919 := bstep (se 1 (by rfl) ⟨1832189, by rfl⟩ : syracuseStep 2442919 = 3664379) B3664379
theorem B3257225 : Blo 2171435 3257225 := bstep (se 2 (by rfl) ⟨1221459, by rfl⟩ : syracuseStep 3257225 = 2442919) B2442919
theorem B2171483 : Blo 2171435 2171483 := bstep (se 1 (by rfl) ⟨1628612, by rfl⟩ : syracuseStep 2171483 = 3257225) B3257225
theorem B10993157 : Blo 2171435 10993157 := bbase (se 4 (by rfl) ⟨1030608, by rfl⟩ : syracuseStep 10993157 = 2061217) (by norm_num)
theorem B7328771 : Blo 2171435 7328771 := bstep (se 1 (by rfl) ⟨5496578, by rfl⟩ : syracuseStep 7328771 = 10993157) B10993157
theorem B4885847 : Blo 2171435 4885847 := bstep (se 1 (by rfl) ⟨3664385, by rfl⟩ : syracuseStep 4885847 = 7328771) B7328771
theorem B3257231 : Blo 2171435 3257231 := bstep (se 1 (by rfl) ⟨2442923, by rfl⟩ : syracuseStep 3257231 = 4885847) B4885847
theorem B2171487 : Blo 2171435 2171487 := bstep (se 1 (by rfl) ⟨1628615, by rfl⟩ : syracuseStep 2171487 = 3257231) B3257231
theorem B3257237 : Blo 2171435 3257237 := bbase (se 6 (by rfl) ⟨76341, by rfl⟩ : syracuseStep 3257237 = 152683) (by norm_num)
theorem B2171491 : Blo 2171435 2171491 := bstep (se 1 (by rfl) ⟨1628618, by rfl⟩ : syracuseStep 2171491 = 3257237) B3257237
theorem B12367349 : Blo 2171435 12367349 := bbase (se 5 (by rfl) ⟨579719, by rfl⟩ : syracuseStep 12367349 = 1159439) (by norm_num)
theorem B8244899 : Blo 2171435 8244899 := bstep (se 1 (by rfl) ⟨6183674, by rfl⟩ : syracuseStep 8244899 = 12367349) B12367349
theorem B5496599 : Blo 2171435 5496599 := bstep (se 1 (by rfl) ⟨4122449, by rfl⟩ : syracuseStep 5496599 = 8244899) B8244899
theorem B3664399 : Blo 2171435 3664399 := bstep (se 1 (by rfl) ⟨2748299, by rfl⟩ : syracuseStep 3664399 = 5496599) B5496599
theorem B4885865 : Blo 2171435 4885865 := bstep (se 2 (by rfl) ⟨1832199, by rfl⟩ : syracuseStep 4885865 = 3664399) B3664399
theorem B3257243 : Blo 2171435 3257243 := bstep (se 1 (by rfl) ⟨2442932, by rfl⟩ : syracuseStep 3257243 = 4885865) B4885865
theorem B2171495 : Blo 2171435 2171495 := bstep (se 1 (by rfl) ⟨1628621, by rfl⟩ : syracuseStep 2171495 = 3257243) B3257243
theorem B2442937 : Blo 2171435 2442937 := bbase (se 2 (by rfl) ⟨916101, by rfl⟩ : syracuseStep 2442937 = 1832203) (by norm_num)
theorem B3257249 : Blo 2171435 3257249 := bstep (se 2 (by rfl) ⟨1221468, by rfl⟩ : syracuseStep 3257249 = 2442937) B2442937
theorem B2171499 : Blo 2171435 2171499 := bstep (se 1 (by rfl) ⟨1628624, by rfl⟩ : syracuseStep 2171499 = 3257249) B3257249
theorem B4637773 : Blo 2171435 4637773 := bbase (se 3 (by rfl) ⟨869582, by rfl⟩ : syracuseStep 4637773 = 1739165) (by norm_num)
theorem B6183697 : Blo 2171435 6183697 := bstep (se 2 (by rfl) ⟨2318886, by rfl⟩ : syracuseStep 6183697 = 4637773) B4637773
theorem B8244929 : Blo 2171435 8244929 := bstep (se 2 (by rfl) ⟨3091848, by rfl⟩ : syracuseStep 8244929 = 6183697) B6183697
theorem B5496619 : Blo 2171435 5496619 := bstep (se 1 (by rfl) ⟨4122464, by rfl⟩ : syracuseStep 5496619 = 8244929) B8244929
theorem B7328825 : Blo 2171435 7328825 := bstep (se 2 (by rfl) ⟨2748309, by rfl⟩ : syracuseStep 7328825 = 5496619) B5496619
theorem B4885883 : Blo 2171435 4885883 := bstep (se 1 (by rfl) ⟨3664412, by rfl⟩ : syracuseStep 4885883 = 7328825) B7328825
theorem B3257255 : Blo 2171435 3257255 := bstep (se 1 (by rfl) ⟨2442941, by rfl⟩ : syracuseStep 3257255 = 4885883) B4885883
theorem B2171503 : Blo 2171435 2171503 := bstep (se 1 (by rfl) ⟨1628627, by rfl⟩ : syracuseStep 2171503 = 3257255) B3257255
theorem B3257261 : Blo 2171435 3257261 := bbase (se 3 (by rfl) ⟨610736, by rfl⟩ : syracuseStep 3257261 = 1221473) (by norm_num)
theorem B2171507 : Blo 2171435 2171507 := bstep (se 1 (by rfl) ⟨1628630, by rfl⟩ : syracuseStep 2171507 = 3257261) B3257261
theorem B4885901 : Blo 2171435 4885901 := bbase (se 3 (by rfl) ⟨916106, by rfl⟩ : syracuseStep 4885901 = 1832213) (by norm_num)
theorem B3257267 : Blo 2171435 3257267 := bstep (se 1 (by rfl) ⟨2442950, by rfl⟩ : syracuseStep 3257267 = 4885901) B4885901
theorem B2171511 : Blo 2171435 2171511 := bstep (se 1 (by rfl) ⟨1628633, by rfl⟩ : syracuseStep 2171511 = 3257267) B3257267
theorem B2748325 : Blo 2171435 2748325 := bbase (se 4 (by rfl) ⟨257655, by rfl⟩ : syracuseStep 2748325 = 515311) (by norm_num)
theorem B3664433 : Blo 2171435 3664433 := bstep (se 2 (by rfl) ⟨1374162, by rfl⟩ : syracuseStep 3664433 = 2748325) B2748325
theorem B2442955 : Blo 2171435 2442955 := bstep (se 1 (by rfl) ⟨1832216, by rfl⟩ : syracuseStep 2442955 = 3664433) B3664433
theorem B3257273 : Blo 2171435 3257273 := bstep (se 2 (by rfl) ⟨1221477, by rfl⟩ : syracuseStep 3257273 = 2442955) B2442955
theorem B2171515 : Blo 2171435 2171515 := bstep (se 1 (by rfl) ⟨1628636, by rfl⟩ : syracuseStep 2171515 = 3257273) B3257273
theorem B17849429 : Blo 2171435 17849429 := bbase (se 8 (by rfl) ⟨104586, by rfl⟩ : syracuseStep 17849429 = 209173) (by norm_num)
theorem B11899619 : Blo 2171435 11899619 := bstep (se 1 (by rfl) ⟨8924714, by rfl⟩ : syracuseStep 11899619 = 17849429) B17849429
theorem B7933079 : Blo 2171435 7933079 := bstep (se 1 (by rfl) ⟨5949809, by rfl⟩ : syracuseStep 7933079 = 11899619) B11899619
theorem B5288719 : Blo 2171435 5288719 := bstep (se 1 (by rfl) ⟨3966539, by rfl⟩ : syracuseStep 5288719 = 7933079) B7933079
theorem B7051625 : Blo 2171435 7051625 := bstep (se 2 (by rfl) ⟨2644359, by rfl⟩ : syracuseStep 7051625 = 5288719) B5288719
theorem B4701083 : Blo 2171435 4701083 := bstep (se 1 (by rfl) ⟨3525812, by rfl⟩ : syracuseStep 4701083 = 7051625) B7051625
theorem B12536221 : Blo 2171435 12536221 := bstep (se 3 (by rfl) ⟨2350541, by rfl⟩ : syracuseStep 12536221 = 4701083) B4701083
theorem B16714961 : Blo 2171435 16714961 := bstep (se 2 (by rfl) ⟨6268110, by rfl⟩ : syracuseStep 16714961 = 12536221) B12536221
theorem B11143307 : Blo 2171435 11143307 := bstep (se 1 (by rfl) ⟨8357480, by rfl⟩ : syracuseStep 11143307 = 16714961) B16714961
theorem B7428871 : Blo 2171435 7428871 := bstep (se 1 (by rfl) ⟨5571653, by rfl⟩ : syracuseStep 7428871 = 11143307) B11143307
theorem B9905161 : Blo 2171435 9905161 := bstep (se 2 (by rfl) ⟨3714435, by rfl⟩ : syracuseStep 9905161 = 7428871) B7428871
theorem B13206881 : Blo 2171435 13206881 := bstep (se 2 (by rfl) ⟨4952580, by rfl⟩ : syracuseStep 13206881 = 9905161) B9905161
theorem B8804587 : Blo 2171435 8804587 := bstep (se 1 (by rfl) ⟨6603440, by rfl⟩ : syracuseStep 8804587 = 13206881) B13206881
theorem B11739449 : Blo 2171435 11739449 := bstep (se 2 (by rfl) ⟨4402293, by rfl⟩ : syracuseStep 11739449 = 8804587) B8804587
theorem B31305197 : Blo 2171435 31305197 := bstep (se 3 (by rfl) ⟨5869724, by rfl⟩ : syracuseStep 31305197 = 11739449) B11739449
theorem B20870131 : Blo 2171435 20870131 := bstep (se 1 (by rfl) ⟨15652598, by rfl⟩ : syracuseStep 20870131 = 31305197) B31305197
theorem B27826841 : Blo 2171435 27826841 := bstep (se 2 (by rfl) ⟨10435065, by rfl⟩ : syracuseStep 27826841 = 20870131) B20870131
theorem B18551227 : Blo 2171435 18551227 := bstep (se 1 (by rfl) ⟨13913420, by rfl⟩ : syracuseStep 18551227 = 27826841) B27826841
theorem B24734969 : Blo 2171435 24734969 := bstep (se 2 (by rfl) ⟨9275613, by rfl⟩ : syracuseStep 24734969 = 18551227) B18551227
theorem B16489979 : Blo 2171435 16489979 := bstep (se 1 (by rfl) ⟨12367484, by rfl⟩ : syracuseStep 16489979 = 24734969) B24734969
theorem B10993319 : Blo 2171435 10993319 := bstep (se 1 (by rfl) ⟨8244989, by rfl⟩ : syracuseStep 10993319 = 16489979) B16489979
theorem B7328879 : Blo 2171435 7328879 := bstep (se 1 (by rfl) ⟨5496659, by rfl⟩ : syracuseStep 7328879 = 10993319) B10993319
theorem B4885919 : Blo 2171435 4885919 := bstep (se 1 (by rfl) ⟨3664439, by rfl⟩ : syracuseStep 4885919 = 7328879) B7328879
theorem B3257279 : Blo 2171435 3257279 := bstep (se 1 (by rfl) ⟨2442959, by rfl⟩ : syracuseStep 3257279 = 4885919) B4885919
theorem B2171519 : Blo 2171435 2171519 := bstep (se 1 (by rfl) ⟨1628639, by rfl⟩ : syracuseStep 2171519 = 3257279) B3257279
theorem B3257285 : Blo 2171435 3257285 := bbase (se 4 (by rfl) ⟨305370, by rfl⟩ : syracuseStep 3257285 = 610741) (by norm_num)
theorem B2171523 : Blo 2171435 2171523 := bstep (se 1 (by rfl) ⟨1628642, by rfl⟩ : syracuseStep 2171523 = 3257285) B3257285
theorem B3664453 : Blo 2171435 3664453 := bbase (se 4 (by rfl) ⟨343542, by rfl⟩ : syracuseStep 3664453 = 687085) (by norm_num)
theorem B4885937 : Blo 2171435 4885937 := bstep (se 2 (by rfl) ⟨1832226, by rfl⟩ : syracuseStep 4885937 = 3664453) B3664453
theorem B3257291 : Blo 2171435 3257291 := bstep (se 1 (by rfl) ⟨2442968, by rfl⟩ : syracuseStep 3257291 = 4885937) B4885937
theorem B2171527 : Blo 2171435 2171527 := bstep (se 1 (by rfl) ⟨1628645, by rfl⟩ : syracuseStep 2171527 = 3257291) B3257291
theorem B2442973 : Blo 2171435 2442973 := bbase (se 3 (by rfl) ⟨458057, by rfl⟩ : syracuseStep 2442973 = 916115) (by norm_num)
theorem B3257297 : Blo 2171435 3257297 := bstep (se 2 (by rfl) ⟨1221486, by rfl⟩ : syracuseStep 3257297 = 2442973) B2442973
theorem B2171531 : Blo 2171435 2171531 := bstep (se 1 (by rfl) ⟨1628648, by rfl⟩ : syracuseStep 2171531 = 3257297) B3257297
theorem B7328933 : Blo 2171435 7328933 := bbase (se 4 (by rfl) ⟨687087, by rfl⟩ : syracuseStep 7328933 = 1374175) (by norm_num)
theorem B4885955 : Blo 2171435 4885955 := bstep (se 1 (by rfl) ⟨3664466, by rfl⟩ : syracuseStep 4885955 = 7328933) B7328933
theorem B3257303 : Blo 2171435 3257303 := bstep (se 1 (by rfl) ⟨2442977, by rfl⟩ : syracuseStep 3257303 = 4885955) B4885955
theorem B2171535 : Blo 2171435 2171535 := bstep (se 1 (by rfl) ⟨1628651, by rfl⟩ : syracuseStep 2171535 = 3257303) B3257303
theorem B3257309 : Blo 2171435 3257309 := bbase (se 3 (by rfl) ⟨610745, by rfl⟩ : syracuseStep 3257309 = 1221491) (by norm_num)
theorem B2171539 : Blo 2171435 2171539 := bstep (se 1 (by rfl) ⟨1628654, by rfl⟩ : syracuseStep 2171539 = 3257309) B3257309
theorem B4885973 : Blo 2171435 4885973 := bbase (se 7 (by rfl) ⟨57257, by rfl⟩ : syracuseStep 4885973 = 114515) (by norm_num)
theorem B3257315 : Blo 2171435 3257315 := bstep (se 1 (by rfl) ⟨2442986, by rfl⟩ : syracuseStep 3257315 = 4885973) B4885973
theorem B2171543 : Blo 2171435 2171543 := bstep (se 1 (by rfl) ⟨1628657, by rfl⟩ : syracuseStep 2171543 = 3257315) B3257315
theorem B2934901 : Blo 2171435 2934901 := bbase (se 5 (by rfl) ⟨137573, by rfl⟩ : syracuseStep 2934901 = 275147) (by norm_num)
theorem B3913201 : Blo 2171435 3913201 := bstep (se 2 (by rfl) ⟨1467450, by rfl⟩ : syracuseStep 3913201 = 2934901) B2934901
theorem B20870405 : Blo 2171435 20870405 := bstep (se 4 (by rfl) ⟨1956600, by rfl⟩ : syracuseStep 20870405 = 3913201) B3913201
theorem B13913603 : Blo 2171435 13913603 := bstep (se 1 (by rfl) ⟨10435202, by rfl⟩ : syracuseStep 13913603 = 20870405) B20870405
theorem B9275735 : Blo 2171435 9275735 := bstep (se 1 (by rfl) ⟨6956801, by rfl⟩ : syracuseStep 9275735 = 13913603) B13913603
theorem B6183823 : Blo 2171435 6183823 := bstep (se 1 (by rfl) ⟨4637867, by rfl⟩ : syracuseStep 6183823 = 9275735) B9275735
theorem B8245097 : Blo 2171435 8245097 := bstep (se 2 (by rfl) ⟨3091911, by rfl⟩ : syracuseStep 8245097 = 6183823) B6183823
theorem B5496731 : Blo 2171435 5496731 := bstep (se 1 (by rfl) ⟨4122548, by rfl⟩ : syracuseStep 5496731 = 8245097) B8245097
theorem B3664487 : Blo 2171435 3664487 := bstep (se 1 (by rfl) ⟨2748365, by rfl⟩ : syracuseStep 3664487 = 5496731) B5496731
theorem B2442991 : Blo 2171435 2442991 := bstep (se 1 (by rfl) ⟨1832243, by rfl⟩ : syracuseStep 2442991 = 3664487) B3664487
theorem B3257321 : Blo 2171435 3257321 := bstep (se 2 (by rfl) ⟨1221495, by rfl⟩ : syracuseStep 3257321 = 2442991) B2442991
theorem B2171547 : Blo 2171435 2171547 := bstep (se 1 (by rfl) ⟨1628660, by rfl⟩ : syracuseStep 2171547 = 3257321) B3257321
theorem B2608805 : Blo 2171435 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B6956813 : Blo 2171435 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B18551501 : Blo 2171435 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B12367667 : Blo 2171435 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B8245111 : Blo 2171435 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B10993481 : Blo 2171435 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B7328987 : Blo 2171435 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B4885991 : Blo 2171435 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B3257327 : Blo 2171435 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B2171551 : Blo 2171435 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B3257333 : Blo 2171435 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B2171555 : Blo 2171435 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B4637893 : Blo 2171435 4637893 := bbase (se 4 (by rfl) ⟨434802, by rfl⟩ : syracuseStep 4637893 = 869605) (by norm_num)
theorem B6183857 : Blo 2171435 6183857 := bstep (se 2 (by rfl) ⟨2318946, by rfl⟩ : syracuseStep 6183857 = 4637893) B4637893
theorem B4122571 : Blo 2171435 4122571 := bstep (se 1 (by rfl) ⟨3091928, by rfl⟩ : syracuseStep 4122571 = 6183857) B6183857
theorem B5496761 : Blo 2171435 5496761 := bstep (se 2 (by rfl) ⟨2061285, by rfl⟩ : syracuseStep 5496761 = 4122571) B4122571
theorem B3664507 : Blo 2171435 3664507 := bstep (se 1 (by rfl) ⟨2748380, by rfl⟩ : syracuseStep 3664507 = 5496761) B5496761
theorem B4886009 : Blo 2171435 4886009 := bstep (se 2 (by rfl) ⟨1832253, by rfl⟩ : syracuseStep 4886009 = 3664507) B3664507
theorem B3257339 : Blo 2171435 3257339 := bstep (se 1 (by rfl) ⟨2443004, by rfl⟩ : syracuseStep 3257339 = 4886009) B4886009
theorem B2171559 : Blo 2171435 2171559 := bstep (se 1 (by rfl) ⟨1628669, by rfl⟩ : syracuseStep 2171559 = 3257339) B3257339
theorem B2443009 : Blo 2171435 2443009 := bbase (se 2 (by rfl) ⟨916128, by rfl⟩ : syracuseStep 2443009 = 1832257) (by norm_num)
theorem B3257345 : Blo 2171435 3257345 := bstep (se 2 (by rfl) ⟨1221504, by rfl⟩ : syracuseStep 3257345 = 2443009) B2443009
theorem B2171563 : Blo 2171435 2171563 := bstep (se 1 (by rfl) ⟨1628672, by rfl⟩ : syracuseStep 2171563 = 3257345) B3257345
theorem B5496781 : Blo 2171435 5496781 := bbase (se 3 (by rfl) ⟨1030646, by rfl⟩ : syracuseStep 5496781 = 2061293) (by norm_num)
theorem B7329041 : Blo 2171435 7329041 := bstep (se 2 (by rfl) ⟨2748390, by rfl⟩ : syracuseStep 7329041 = 5496781) B5496781
theorem B4886027 : Blo 2171435 4886027 := bstep (se 1 (by rfl) ⟨3664520, by rfl⟩ : syracuseStep 4886027 = 7329041) B7329041
theorem B3257351 : Blo 2171435 3257351 := bstep (se 1 (by rfl) ⟨2443013, by rfl⟩ : syracuseStep 3257351 = 4886027) B4886027
theorem B2171567 : Blo 2171435 2171567 := bstep (se 1 (by rfl) ⟨1628675, by rfl⟩ : syracuseStep 2171567 = 3257351) B3257351
theorem B3257357 : Blo 2171435 3257357 := bbase (se 3 (by rfl) ⟨610754, by rfl⟩ : syracuseStep 3257357 = 1221509) (by norm_num)
theorem B2171571 : Blo 2171435 2171571 := bstep (se 1 (by rfl) ⟨1628678, by rfl⟩ : syracuseStep 2171571 = 3257357) B3257357
theorem B4886045 : Blo 2171435 4886045 := bbase (se 3 (by rfl) ⟨916133, by rfl⟩ : syracuseStep 4886045 = 1832267) (by norm_num)
theorem B3257363 : Blo 2171435 3257363 := bstep (se 1 (by rfl) ⟨2443022, by rfl⟩ : syracuseStep 3257363 = 4886045) B4886045
theorem B2171575 : Blo 2171435 2171575 := bstep (se 1 (by rfl) ⟨1628681, by rfl⟩ : syracuseStep 2171575 = 3257363) B3257363
theorem B3664541 : Blo 2171435 3664541 := bbase (se 3 (by rfl) ⟨687101, by rfl⟩ : syracuseStep 3664541 = 1374203) (by norm_num)
theorem B2443027 : Blo 2171435 2443027 := bstep (se 1 (by rfl) ⟨1832270, by rfl⟩ : syracuseStep 2443027 = 3664541) B3664541
theorem B3257369 : Blo 2171435 3257369 := bstep (se 2 (by rfl) ⟨1221513, by rfl⟩ : syracuseStep 3257369 = 2443027) B2443027
theorem B2171579 : Blo 2171435 2171579 := bstep (se 1 (by rfl) ⟨1628684, by rfl⟩ : syracuseStep 2171579 = 3257369) B3257369
theorem B10577749 : Blo 2171435 10577749 := bbase (se 9 (by rfl) ⟨30989, by rfl⟩ : syracuseStep 10577749 = 61979) (by norm_num)
theorem B14103665 : Blo 2171435 14103665 := bstep (se 2 (by rfl) ⟨5288874, by rfl⟩ : syracuseStep 14103665 = 10577749) B10577749
theorem B9402443 : Blo 2171435 9402443 := bstep (se 1 (by rfl) ⟨7051832, by rfl⟩ : syracuseStep 9402443 = 14103665) B14103665
theorem B6268295 : Blo 2171435 6268295 := bstep (se 1 (by rfl) ⟨4701221, by rfl⟩ : syracuseStep 6268295 = 9402443) B9402443
theorem B4178863 : Blo 2171435 4178863 := bstep (se 1 (by rfl) ⟨3134147, by rfl⟩ : syracuseStep 4178863 = 6268295) B6268295
theorem B22287269 : Blo 2171435 22287269 := bstep (se 4 (by rfl) ⟨2089431, by rfl⟩ : syracuseStep 22287269 = 4178863) B4178863
theorem B59432717 : Blo 2171435 59432717 := bstep (se 3 (by rfl) ⟨11143634, by rfl⟩ : syracuseStep 59432717 = 22287269) B22287269
theorem B39621811 : Blo 2171435 39621811 := bstep (se 1 (by rfl) ⟨29716358, by rfl⟩ : syracuseStep 39621811 = 59432717) B59432717
theorem B52829081 : Blo 2171435 52829081 := bstep (se 2 (by rfl) ⟨19810905, by rfl⟩ : syracuseStep 52829081 = 39621811) B39621811
theorem B35219387 : Blo 2171435 35219387 := bstep (se 1 (by rfl) ⟨26414540, by rfl⟩ : syracuseStep 35219387 = 52829081) B52829081
theorem B23479591 : Blo 2171435 23479591 := bstep (se 1 (by rfl) ⟨17609693, by rfl⟩ : syracuseStep 23479591 = 35219387) B35219387
theorem B31306121 : Blo 2171435 31306121 := bstep (se 2 (by rfl) ⟨11739795, by rfl⟩ : syracuseStep 31306121 = 23479591) B23479591
theorem B20870747 : Blo 2171435 20870747 := bstep (se 1 (by rfl) ⟨15653060, by rfl⟩ : syracuseStep 20870747 = 31306121) B31306121
theorem B13913831 : Blo 2171435 13913831 := bstep (se 1 (by rfl) ⟨10435373, by rfl⟩ : syracuseStep 13913831 = 20870747) B20870747
theorem B9275887 : Blo 2171435 9275887 := bstep (se 1 (by rfl) ⟨6956915, by rfl⟩ : syracuseStep 9275887 = 13913831) B13913831
theorem B12367849 : Blo 2171435 12367849 := bstep (se 2 (by rfl) ⟨4637943, by rfl⟩ : syracuseStep 12367849 = 9275887) B9275887
theorem B16490465 : Blo 2171435 16490465 := bstep (se 2 (by rfl) ⟨6183924, by rfl⟩ : syracuseStep 16490465 = 12367849) B12367849
theorem B10993643 : Blo 2171435 10993643 := bstep (se 1 (by rfl) ⟨8245232, by rfl⟩ : syracuseStep 10993643 = 16490465) B16490465
theorem B7329095 : Blo 2171435 7329095 := bstep (se 1 (by rfl) ⟨5496821, by rfl⟩ : syracuseStep 7329095 = 10993643) B10993643
theorem B4886063 : Blo 2171435 4886063 := bstep (se 1 (by rfl) ⟨3664547, by rfl⟩ : syracuseStep 4886063 = 7329095) B7329095
theorem B3257375 : Blo 2171435 3257375 := bstep (se 1 (by rfl) ⟨2443031, by rfl⟩ : syracuseStep 3257375 = 4886063) B4886063
theorem B2171583 : Blo 2171435 2171583 := bstep (se 1 (by rfl) ⟨1628687, by rfl⟩ : syracuseStep 2171583 = 3257375) B3257375
theorem B3257381 : Blo 2171435 3257381 := bbase (se 4 (by rfl) ⟨305379, by rfl⟩ : syracuseStep 3257381 = 610759) (by norm_num)
theorem B2171587 : Blo 2171435 2171587 := bstep (se 1 (by rfl) ⟨1628690, by rfl⟩ : syracuseStep 2171587 = 3257381) B3257381
theorem B2748421 : Blo 2171435 2748421 := bbase (se 4 (by rfl) ⟨257664, by rfl⟩ : syracuseStep 2748421 = 515329) (by norm_num)
theorem B3664561 : Blo 2171435 3664561 := bstep (se 2 (by rfl) ⟨1374210, by rfl⟩ : syracuseStep 3664561 = 2748421) B2748421
theorem B4886081 : Blo 2171435 4886081 := bstep (se 2 (by rfl) ⟨1832280, by rfl⟩ : syracuseStep 4886081 = 3664561) B3664561
theorem B3257387 : Blo 2171435 3257387 := bstep (se 1 (by rfl) ⟨2443040, by rfl⟩ : syracuseStep 3257387 = 4886081) B4886081
theorem B2171591 : Blo 2171435 2171591 := bstep (se 1 (by rfl) ⟨1628693, by rfl⟩ : syracuseStep 2171591 = 3257387) B3257387
theorem B2443045 : Blo 2171435 2443045 := bbase (se 4 (by rfl) ⟨229035, by rfl⟩ : syracuseStep 2443045 = 458071) (by norm_num)
theorem B3257393 : Blo 2171435 3257393 := bstep (se 2 (by rfl) ⟨1221522, by rfl⟩ : syracuseStep 3257393 = 2443045) B2443045
theorem B2171595 : Blo 2171435 2171595 := bstep (se 1 (by rfl) ⟨1628696, by rfl⟩ : syracuseStep 2171595 = 3257393) B3257393
theorem B9275957 : Blo 2171435 9275957 := bbase (se 5 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 9275957 = 869621) (by norm_num)
theorem B6183971 : Blo 2171435 6183971 := bstep (se 1 (by rfl) ⟨4637978, by rfl⟩ : syracuseStep 6183971 = 9275957) B9275957
theorem B4122647 : Blo 2171435 4122647 := bstep (se 1 (by rfl) ⟨3091985, by rfl⟩ : syracuseStep 4122647 = 6183971) B6183971
theorem B2748431 : Blo 2171435 2748431 := bstep (se 1 (by rfl) ⟨2061323, by rfl⟩ : syracuseStep 2748431 = 4122647) B4122647
theorem B7329149 : Blo 2171435 7329149 := bstep (se 3 (by rfl) ⟨1374215, by rfl⟩ : syracuseStep 7329149 = 2748431) B2748431
theorem B4886099 : Blo 2171435 4886099 := bstep (se 1 (by rfl) ⟨3664574, by rfl⟩ : syracuseStep 4886099 = 7329149) B7329149
theorem B3257399 : Blo 2171435 3257399 := bstep (se 1 (by rfl) ⟨2443049, by rfl⟩ : syracuseStep 3257399 = 4886099) B4886099
theorem B2171599 : Blo 2171435 2171599 := bstep (se 1 (by rfl) ⟨1628699, by rfl⟩ : syracuseStep 2171599 = 3257399) B3257399
theorem B3257405 : Blo 2171435 3257405 := bbase (se 3 (by rfl) ⟨610763, by rfl⟩ : syracuseStep 3257405 = 1221527) (by norm_num)
theorem B2171603 : Blo 2171435 2171603 := bstep (se 1 (by rfl) ⟨1628702, by rfl⟩ : syracuseStep 2171603 = 3257405) B3257405
theorem B4886117 : Blo 2171435 4886117 := bbase (se 4 (by rfl) ⟨458073, by rfl⟩ : syracuseStep 4886117 = 916147) (by norm_num)
theorem B3257411 : Blo 2171435 3257411 := bstep (se 1 (by rfl) ⟨2443058, by rfl⟩ : syracuseStep 3257411 = 4886117) B4886117
theorem B2171607 : Blo 2171435 2171607 := bstep (se 1 (by rfl) ⟨1628705, by rfl⟩ : syracuseStep 2171607 = 3257411) B3257411
theorem B5496893 : Blo 2171435 5496893 := bbase (se 3 (by rfl) ⟨1030667, by rfl⟩ : syracuseStep 5496893 = 2061335) (by norm_num)
theorem B3664595 : Blo 2171435 3664595 := bstep (se 1 (by rfl) ⟨2748446, by rfl⟩ : syracuseStep 3664595 = 5496893) B5496893
theorem B2443063 : Blo 2171435 2443063 := bstep (se 1 (by rfl) ⟨1832297, by rfl⟩ : syracuseStep 2443063 = 3664595) B3664595
theorem B3257417 : Blo 2171435 3257417 := bstep (se 2 (by rfl) ⟨1221531, by rfl⟩ : syracuseStep 3257417 = 2443063) B2443063
theorem B2171611 : Blo 2171435 2171611 := bstep (se 1 (by rfl) ⟨1628708, by rfl⟩ : syracuseStep 2171611 = 3257417) B3257417
theorem B4122677 : Blo 2171435 4122677 := bbase (se 5 (by rfl) ⟨193250, by rfl⟩ : syracuseStep 4122677 = 386501) (by norm_num)
theorem B10993805 : Blo 2171435 10993805 := bstep (se 3 (by rfl) ⟨2061338, by rfl⟩ : syracuseStep 10993805 = 4122677) B4122677
theorem B7329203 : Blo 2171435 7329203 := bstep (se 1 (by rfl) ⟨5496902, by rfl⟩ : syracuseStep 7329203 = 10993805) B10993805
theorem B4886135 : Blo 2171435 4886135 := bstep (se 1 (by rfl) ⟨3664601, by rfl⟩ : syracuseStep 4886135 = 7329203) B7329203
theorem B3257423 : Blo 2171435 3257423 := bstep (se 1 (by rfl) ⟨2443067, by rfl⟩ : syracuseStep 3257423 = 4886135) B4886135
theorem B2171615 : Blo 2171435 2171615 := bstep (se 1 (by rfl) ⟨1628711, by rfl⟩ : syracuseStep 2171615 = 3257423) B3257423
theorem B3257429 : Blo 2171435 3257429 := bbase (se 8 (by rfl) ⟨19086, by rfl⟩ : syracuseStep 3257429 = 38173) (by norm_num)
theorem B2171619 : Blo 2171435 2171619 := bstep (se 1 (by rfl) ⟨1628714, by rfl⟩ : syracuseStep 2171619 = 3257429) B3257429
theorem B2261729 : Blo 2171435 2261729 := bbase (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) (by norm_num)
theorem B6031277 : Blo 2171435 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B4020851 : Blo 2171435 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B10722269 : Blo 2171435 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B7148179 : Blo 2171435 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B9530905 : Blo 2171435 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B12707873 : Blo 2171435 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B8471915 : Blo 2171435 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B5647943 : Blo 2171435 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B3765295 : Blo 2171435 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B5020393 : Blo 2171435 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B6693857 : Blo 2171435 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B4462571 : Blo 2171435 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B11900189 : Blo 2171435 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B7933459 : Blo 2171435 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B10577945 : Blo 2171435 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B7051963 : Blo 2171435 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B9402617 : Blo 2171435 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B6268411 : Blo 2171435 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B33431525 : Blo 2171435 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B22287683 : Blo 2171435 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B59433821 : Blo 2171435 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B39622547 : Blo 2171435 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B26415031 : Blo 2171435 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B35220041 : Blo 2171435 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B23480027 : Blo 2171435 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B15653351 : Blo 2171435 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B10435567 : Blo 2171435 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B13914089 : Blo 2171435 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B9276059 : Blo 2171435 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B6184039 : Blo 2171435 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B8245385 : Blo 2171435 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B5496923 : Blo 2171435 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B3664615 : Blo 2171435 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B4886153 : Blo 2171435 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B3257435 : Blo 2171435 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B2171623 : Blo 2171435 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B2443081 : Blo 2171435 2443081 := bbase (se 2 (by rfl) ⟨916155, by rfl⟩ : syracuseStep 2443081 = 1832311) (by norm_num)
theorem B3257441 : Blo 2171435 3257441 := bstep (se 2 (by rfl) ⟨1221540, by rfl⟩ : syracuseStep 3257441 = 2443081) B2443081
theorem B2171627 : Blo 2171435 2171627 := bstep (se 1 (by rfl) ⟨1628720, by rfl⟩ : syracuseStep 2171627 = 3257441) B3257441
theorem B18805301 : Blo 2171435 18805301 := bbase (se 5 (by rfl) ⟨881498, by rfl⟩ : syracuseStep 18805301 = 1762997) (by norm_num)
theorem B12536867 : Blo 2171435 12536867 := bstep (se 1 (by rfl) ⟨9402650, by rfl⟩ : syracuseStep 12536867 = 18805301) B18805301
theorem B8357911 : Blo 2171435 8357911 := bstep (se 1 (by rfl) ⟨6268433, by rfl⟩ : syracuseStep 8357911 = 12536867) B12536867
theorem B44575525 : Blo 2171435 44575525 := bstep (se 4 (by rfl) ⟨4178955, by rfl⟩ : syracuseStep 44575525 = 8357911) B8357911
theorem B59434033 : Blo 2171435 59434033 := bstep (se 2 (by rfl) ⟨22287762, by rfl⟩ : syracuseStep 59434033 = 44575525) B44575525
theorem B79245377 : Blo 2171435 79245377 := bstep (se 2 (by rfl) ⟨29717016, by rfl⟩ : syracuseStep 79245377 = 59434033) B59434033
theorem B52830251 : Blo 2171435 52830251 := bstep (se 1 (by rfl) ⟨39622688, by rfl⟩ : syracuseStep 52830251 = 79245377) B79245377
theorem B35220167 : Blo 2171435 35220167 := bstep (se 1 (by rfl) ⟨26415125, by rfl⟩ : syracuseStep 35220167 = 52830251) B52830251
theorem B23480111 : Blo 2171435 23480111 := bstep (se 1 (by rfl) ⟨17610083, by rfl⟩ : syracuseStep 23480111 = 35220167) B35220167
theorem B15653407 : Blo 2171435 15653407 := bstep (se 1 (by rfl) ⟨11740055, by rfl⟩ : syracuseStep 15653407 = 23480111) B23480111
theorem B20871209 : Blo 2171435 20871209 := bstep (se 2 (by rfl) ⟨7826703, by rfl⟩ : syracuseStep 20871209 = 15653407) B15653407
theorem B13914139 : Blo 2171435 13914139 := bstep (se 1 (by rfl) ⟨10435604, by rfl⟩ : syracuseStep 13914139 = 20871209) B20871209
theorem B18552185 : Blo 2171435 18552185 := bstep (se 2 (by rfl) ⟨6957069, by rfl⟩ : syracuseStep 18552185 = 13914139) B13914139
theorem B12368123 : Blo 2171435 12368123 := bstep (se 1 (by rfl) ⟨9276092, by rfl⟩ : syracuseStep 12368123 = 18552185) B18552185
theorem B8245415 : Blo 2171435 8245415 := bstep (se 1 (by rfl) ⟨6184061, by rfl⟩ : syracuseStep 8245415 = 12368123) B12368123
theorem B5496943 : Blo 2171435 5496943 := bstep (se 1 (by rfl) ⟨4122707, by rfl⟩ : syracuseStep 5496943 = 8245415) B8245415
theorem B7329257 : Blo 2171435 7329257 := bstep (se 2 (by rfl) ⟨2748471, by rfl⟩ : syracuseStep 7329257 = 5496943) B5496943
theorem B4886171 : Blo 2171435 4886171 := bstep (se 1 (by rfl) ⟨3664628, by rfl⟩ : syracuseStep 4886171 = 7329257) B7329257
theorem B3257447 : Blo 2171435 3257447 := bstep (se 1 (by rfl) ⟨2443085, by rfl⟩ : syracuseStep 3257447 = 4886171) B4886171
theorem B2171631 : Blo 2171435 2171631 := bstep (se 1 (by rfl) ⟨1628723, by rfl⟩ : syracuseStep 2171631 = 3257447) B3257447
theorem B3257453 : Blo 2171435 3257453 := bbase (se 3 (by rfl) ⟨610772, by rfl⟩ : syracuseStep 3257453 = 1221545) (by norm_num)
theorem B2171635 : Blo 2171435 2171635 := bstep (se 1 (by rfl) ⟨1628726, by rfl⟩ : syracuseStep 2171635 = 3257453) B3257453
theorem B4886189 : Blo 2171435 4886189 := bbase (se 3 (by rfl) ⟨916160, by rfl⟩ : syracuseStep 4886189 = 1832321) (by norm_num)
theorem B3257459 : Blo 2171435 3257459 := bstep (se 1 (by rfl) ⟨2443094, by rfl⟩ : syracuseStep 3257459 = 4886189) B4886189
theorem B2171639 : Blo 2171435 2171639 := bstep (se 1 (by rfl) ⟨1628729, by rfl⟩ : syracuseStep 2171639 = 3257459) B3257459
theorem B7148245 : Blo 2171435 7148245 := bbase (se 7 (by rfl) ⟨83768, by rfl⟩ : syracuseStep 7148245 = 167537) (by norm_num)
theorem B9530993 : Blo 2171435 9530993 := bstep (se 2 (by rfl) ⟨3574122, by rfl⟩ : syracuseStep 9530993 = 7148245) B7148245
theorem B6353995 : Blo 2171435 6353995 := bstep (se 1 (by rfl) ⟨4765496, by rfl⟩ : syracuseStep 6353995 = 9530993) B9530993
theorem B8471993 : Blo 2171435 8471993 := bstep (se 2 (by rfl) ⟨3176997, by rfl⟩ : syracuseStep 8471993 = 6353995) B6353995
theorem B22591981 : Blo 2171435 22591981 := bstep (se 3 (by rfl) ⟨4235996, by rfl⟩ : syracuseStep 22591981 = 8471993) B8471993
theorem B30122641 : Blo 2171435 30122641 := bstep (se 2 (by rfl) ⟨11295990, by rfl⟩ : syracuseStep 30122641 = 22591981) B22591981
theorem B40163521 : Blo 2171435 40163521 := bstep (se 2 (by rfl) ⟨15061320, by rfl⟩ : syracuseStep 40163521 = 30122641) B30122641
theorem B53551361 : Blo 2171435 53551361 := bstep (se 2 (by rfl) ⟨20081760, by rfl⟩ : syracuseStep 53551361 = 40163521) B40163521
theorem B35700907 : Blo 2171435 35700907 := bstep (se 1 (by rfl) ⟨26775680, by rfl⟩ : syracuseStep 35700907 = 53551361) B53551361
theorem B47601209 : Blo 2171435 47601209 := bstep (se 2 (by rfl) ⟨17850453, by rfl⟩ : syracuseStep 47601209 = 35700907) B35700907
theorem B126936557 : Blo 2171435 126936557 := bstep (se 3 (by rfl) ⟨23800604, by rfl⟩ : syracuseStep 126936557 = 47601209) B47601209
theorem B84624371 : Blo 2171435 84624371 := bstep (se 1 (by rfl) ⟨63468278, by rfl⟩ : syracuseStep 84624371 = 126936557) B126936557
theorem B56416247 : Blo 2171435 56416247 := bstep (se 1 (by rfl) ⟨42312185, by rfl⟩ : syracuseStep 56416247 = 84624371) B84624371
theorem B37610831 : Blo 2171435 37610831 := bstep (se 1 (by rfl) ⟨28208123, by rfl⟩ : syracuseStep 37610831 = 56416247) B56416247
theorem B25073887 : Blo 2171435 25073887 := bstep (se 1 (by rfl) ⟨18805415, by rfl⟩ : syracuseStep 25073887 = 37610831) B37610831
theorem B33431849 : Blo 2171435 33431849 := bstep (se 2 (by rfl) ⟨12536943, by rfl⟩ : syracuseStep 33431849 = 25073887) B25073887
theorem B22287899 : Blo 2171435 22287899 := bstep (se 1 (by rfl) ⟨16715924, by rfl⟩ : syracuseStep 22287899 = 33431849) B33431849
theorem B14858599 : Blo 2171435 14858599 := bstep (se 1 (by rfl) ⟨11143949, by rfl⟩ : syracuseStep 14858599 = 22287899) B22287899
theorem B19811465 : Blo 2171435 19811465 := bstep (se 2 (by rfl) ⟨7429299, by rfl⟩ : syracuseStep 19811465 = 14858599) B14858599
theorem B13207643 : Blo 2171435 13207643 := bstep (se 1 (by rfl) ⟨9905732, by rfl⟩ : syracuseStep 13207643 = 19811465) B19811465
theorem B8805095 : Blo 2171435 8805095 := bstep (se 1 (by rfl) ⟨6603821, by rfl⟩ : syracuseStep 8805095 = 13207643) B13207643
theorem B5870063 : Blo 2171435 5870063 := bstep (se 1 (by rfl) ⟨4402547, by rfl⟩ : syracuseStep 5870063 = 8805095) B8805095
theorem B3913375 : Blo 2171435 3913375 := bstep (se 1 (by rfl) ⟨2935031, by rfl⟩ : syracuseStep 3913375 = 5870063) B5870063
theorem B5217833 : Blo 2171435 5217833 := bstep (se 2 (by rfl) ⟨1956687, by rfl⟩ : syracuseStep 5217833 = 3913375) B3913375
theorem B3478555 : Blo 2171435 3478555 := bstep (se 1 (by rfl) ⟨2608916, by rfl⟩ : syracuseStep 3478555 = 5217833) B5217833
theorem B4638073 : Blo 2171435 4638073 := bstep (se 2 (by rfl) ⟨1739277, by rfl⟩ : syracuseStep 4638073 = 3478555) B3478555
theorem B6184097 : Blo 2171435 6184097 := bstep (se 2 (by rfl) ⟨2319036, by rfl⟩ : syracuseStep 6184097 = 4638073) B4638073
theorem B4122731 : Blo 2171435 4122731 := bstep (se 1 (by rfl) ⟨3092048, by rfl⟩ : syracuseStep 4122731 = 6184097) B6184097
theorem B2748487 : Blo 2171435 2748487 := bstep (se 1 (by rfl) ⟨2061365, by rfl⟩ : syracuseStep 2748487 = 4122731) B4122731
theorem B3664649 : Blo 2171435 3664649 := bstep (se 2 (by rfl) ⟨1374243, by rfl⟩ : syracuseStep 3664649 = 2748487) B2748487
theorem B2443099 : Blo 2171435 2443099 := bstep (se 1 (by rfl) ⟨1832324, by rfl⟩ : syracuseStep 2443099 = 3664649) B3664649
theorem B3257465 : Blo 2171435 3257465 := bstep (se 2 (by rfl) ⟨1221549, by rfl⟩ : syracuseStep 3257465 = 2443099) B2443099
theorem B2171643 : Blo 2171435 2171643 := bstep (se 1 (by rfl) ⟨1628732, by rfl⟩ : syracuseStep 2171643 = 3257465) B3257465
theorem B3526021 : Blo 2171435 3526021 := bbase (se 4 (by rfl) ⟨330564, by rfl⟩ : syracuseStep 3526021 = 661129) (by norm_num)
theorem B18805445 : Blo 2171435 18805445 := bstep (se 4 (by rfl) ⟨1763010, by rfl⟩ : syracuseStep 18805445 = 3526021) B3526021
theorem B12536963 : Blo 2171435 12536963 := bstep (se 1 (by rfl) ⟨9402722, by rfl⟩ : syracuseStep 12536963 = 18805445) B18805445
theorem B8357975 : Blo 2171435 8357975 := bstep (se 1 (by rfl) ⟨6268481, by rfl⟩ : syracuseStep 8357975 = 12536963) B12536963
theorem B5571983 : Blo 2171435 5571983 := bstep (se 1 (by rfl) ⟨4178987, by rfl⟩ : syracuseStep 5571983 = 8357975) B8357975
theorem B3714655 : Blo 2171435 3714655 := bstep (se 1 (by rfl) ⟨2785991, by rfl⟩ : syracuseStep 3714655 = 5571983) B5571983
theorem B4952873 : Blo 2171435 4952873 := bstep (se 2 (by rfl) ⟨1857327, by rfl⟩ : syracuseStep 4952873 = 3714655) B3714655
theorem B3301915 : Blo 2171435 3301915 := bstep (se 1 (by rfl) ⟨2476436, by rfl⟩ : syracuseStep 3301915 = 4952873) B4952873
theorem B4402553 : Blo 2171435 4402553 := bstep (se 2 (by rfl) ⟨1650957, by rfl⟩ : syracuseStep 4402553 = 3301915) B3301915
theorem B11740141 : Blo 2171435 11740141 := bstep (se 3 (by rfl) ⟨2201276, by rfl⟩ : syracuseStep 11740141 = 4402553) B4402553
theorem B15653521 : Blo 2171435 15653521 := bstep (se 2 (by rfl) ⟨5870070, by rfl⟩ : syracuseStep 15653521 = 11740141) B11740141
theorem B20871361 : Blo 2171435 20871361 := bstep (se 2 (by rfl) ⟨7826760, by rfl⟩ : syracuseStep 20871361 = 15653521) B15653521
theorem B27828481 : Blo 2171435 27828481 := bstep (se 2 (by rfl) ⟨10435680, by rfl⟩ : syracuseStep 27828481 = 20871361) B20871361
theorem B37104641 : Blo 2171435 37104641 := bstep (se 2 (by rfl) ⟨13914240, by rfl⟩ : syracuseStep 37104641 = 27828481) B27828481
theorem B24736427 : Blo 2171435 24736427 := bstep (se 1 (by rfl) ⟨18552320, by rfl⟩ : syracuseStep 24736427 = 37104641) B37104641
theorem B16490951 : Blo 2171435 16490951 := bstep (se 1 (by rfl) ⟨12368213, by rfl⟩ : syracuseStep 16490951 = 24736427) B24736427
theorem B10993967 : Blo 2171435 10993967 := bstep (se 1 (by rfl) ⟨8245475, by rfl⟩ : syracuseStep 10993967 = 16490951) B16490951
theorem B7329311 : Blo 2171435 7329311 := bstep (se 1 (by rfl) ⟨5496983, by rfl⟩ : syracuseStep 7329311 = 10993967) B10993967
theorem B4886207 : Blo 2171435 4886207 := bstep (se 1 (by rfl) ⟨3664655, by rfl⟩ : syracuseStep 4886207 = 7329311) B7329311
theorem B3257471 : Blo 2171435 3257471 := bstep (se 1 (by rfl) ⟨2443103, by rfl⟩ : syracuseStep 3257471 = 4886207) B4886207
theorem B2171647 : Blo 2171435 2171647 := bstep (se 1 (by rfl) ⟨1628735, by rfl⟩ : syracuseStep 2171647 = 3257471) B3257471
theorem B3257477 : Blo 2171435 3257477 := bbase (se 4 (by rfl) ⟨305388, by rfl⟩ : syracuseStep 3257477 = 610777) (by norm_num)
theorem B2171651 : Blo 2171435 2171651 := bstep (se 1 (by rfl) ⟨1628738, by rfl⟩ : syracuseStep 2171651 = 3257477) B3257477
theorem B3664669 : Blo 2171435 3664669 := bbase (se 3 (by rfl) ⟨687125, by rfl⟩ : syracuseStep 3664669 = 1374251) (by norm_num)
theorem B4886225 : Blo 2171435 4886225 := bstep (se 2 (by rfl) ⟨1832334, by rfl⟩ : syracuseStep 4886225 = 3664669) B3664669
theorem B3257483 : Blo 2171435 3257483 := bstep (se 1 (by rfl) ⟨2443112, by rfl⟩ : syracuseStep 3257483 = 4886225) B4886225
theorem B2171655 : Blo 2171435 2171655 := bstep (se 1 (by rfl) ⟨1628741, by rfl⟩ : syracuseStep 2171655 = 3257483) B3257483
theorem B2443117 : Blo 2171435 2443117 := bbase (se 3 (by rfl) ⟨458084, by rfl⟩ : syracuseStep 2443117 = 916169) (by norm_num)
theorem B3257489 : Blo 2171435 3257489 := bstep (se 2 (by rfl) ⟨1221558, by rfl⟩ : syracuseStep 3257489 = 2443117) B2443117
theorem B2171659 : Blo 2171435 2171659 := bstep (se 1 (by rfl) ⟨1628744, by rfl⟩ : syracuseStep 2171659 = 3257489) B3257489
theorem B7329365 : Blo 2171435 7329365 := bbase (se 8 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 7329365 = 85891) (by norm_num)
theorem B4886243 : Blo 2171435 4886243 := bstep (se 1 (by rfl) ⟨3664682, by rfl⟩ : syracuseStep 4886243 = 7329365) B7329365
theorem B3257495 : Blo 2171435 3257495 := bstep (se 1 (by rfl) ⟨2443121, by rfl⟩ : syracuseStep 3257495 = 4886243) B4886243
theorem B2171663 : Blo 2171435 2171663 := bstep (se 1 (by rfl) ⟨1628747, by rfl⟩ : syracuseStep 2171663 = 3257495) B3257495
theorem B3257501 : Blo 2171435 3257501 := bbase (se 3 (by rfl) ⟨610781, by rfl⟩ : syracuseStep 3257501 = 1221563) (by norm_num)
theorem B2171667 : Blo 2171435 2171667 := bstep (se 1 (by rfl) ⟨1628750, by rfl⟩ : syracuseStep 2171667 = 3257501) B3257501
theorem B4886261 : Blo 2171435 4886261 := bbase (se 5 (by rfl) ⟨229043, by rfl⟩ : syracuseStep 4886261 = 458087) (by norm_num)
theorem B3257507 : Blo 2171435 3257507 := bstep (se 1 (by rfl) ⟨2443130, by rfl⟩ : syracuseStep 3257507 = 4886261) B4886261
theorem B2171671 : Blo 2171435 2171671 := bstep (se 1 (by rfl) ⟨1628753, by rfl⟩ : syracuseStep 2171671 = 3257507) B3257507
theorem B5289101 : Blo 2171435 5289101 := bbase (se 3 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 5289101 = 1983413) (by norm_num)
theorem B3526067 : Blo 2171435 3526067 := bstep (se 1 (by rfl) ⟨2644550, by rfl⟩ : syracuseStep 3526067 = 5289101) B5289101
theorem B2350711 : Blo 2171435 2350711 := bstep (se 1 (by rfl) ⟨1763033, by rfl⟩ : syracuseStep 2350711 = 3526067) B3526067
theorem B12537125 : Blo 2171435 12537125 := bstep (se 4 (by rfl) ⟨1175355, by rfl⟩ : syracuseStep 12537125 = 2350711) B2350711
theorem B8358083 : Blo 2171435 8358083 := bstep (se 1 (by rfl) ⟨6268562, by rfl⟩ : syracuseStep 8358083 = 12537125) B12537125
theorem B5572055 : Blo 2171435 5572055 := bstep (se 1 (by rfl) ⟨4179041, by rfl⟩ : syracuseStep 5572055 = 8358083) B8358083
theorem B3714703 : Blo 2171435 3714703 := bstep (se 1 (by rfl) ⟨2786027, by rfl⟩ : syracuseStep 3714703 = 5572055) B5572055
theorem B19811749 : Blo 2171435 19811749 := bstep (se 4 (by rfl) ⟨1857351, by rfl⟩ : syracuseStep 19811749 = 3714703) B3714703
theorem B26415665 : Blo 2171435 26415665 := bstep (se 2 (by rfl) ⟨9905874, by rfl⟩ : syracuseStep 26415665 = 19811749) B19811749
theorem B17610443 : Blo 2171435 17610443 := bstep (se 1 (by rfl) ⟨13207832, by rfl⟩ : syracuseStep 17610443 = 26415665) B26415665
theorem B11740295 : Blo 2171435 11740295 := bstep (se 1 (by rfl) ⟨8805221, by rfl⟩ : syracuseStep 11740295 = 17610443) B17610443
theorem B7826863 : Blo 2171435 7826863 := bstep (se 1 (by rfl) ⟨5870147, by rfl⟩ : syracuseStep 7826863 = 11740295) B11740295
theorem B10435817 : Blo 2171435 10435817 := bstep (se 2 (by rfl) ⟨3913431, by rfl⟩ : syracuseStep 10435817 = 7826863) B7826863
theorem B27828845 : Blo 2171435 27828845 := bstep (se 3 (by rfl) ⟨5217908, by rfl⟩ : syracuseStep 27828845 = 10435817) B10435817
theorem B18552563 : Blo 2171435 18552563 := bstep (se 1 (by rfl) ⟨13914422, by rfl⟩ : syracuseStep 18552563 = 27828845) B27828845
theorem B12368375 : Blo 2171435 12368375 := bstep (se 1 (by rfl) ⟨9276281, by rfl⟩ : syracuseStep 12368375 = 18552563) B18552563
theorem B8245583 : Blo 2171435 8245583 := bstep (se 1 (by rfl) ⟨6184187, by rfl⟩ : syracuseStep 8245583 = 12368375) B12368375
theorem B5497055 : Blo 2171435 5497055 := bstep (se 1 (by rfl) ⟨4122791, by rfl⟩ : syracuseStep 5497055 = 8245583) B8245583
theorem B3664703 : Blo 2171435 3664703 := bstep (se 1 (by rfl) ⟨2748527, by rfl⟩ : syracuseStep 3664703 = 5497055) B5497055
theorem B2443135 : Blo 2171435 2443135 := bstep (se 1 (by rfl) ⟨1832351, by rfl⟩ : syracuseStep 2443135 = 3664703) B3664703
theorem B3257513 : Blo 2171435 3257513 := bstep (se 2 (by rfl) ⟨1221567, by rfl⟩ : syracuseStep 3257513 = 2443135) B2443135
theorem B2171675 : Blo 2171435 2171675 := bstep (se 1 (by rfl) ⟨1628756, by rfl⟩ : syracuseStep 2171675 = 3257513) B3257513
theorem B4638149 : Blo 2171435 4638149 := bbase (se 4 (by rfl) ⟨434826, by rfl⟩ : syracuseStep 4638149 = 869653) (by norm_num)
theorem B3092099 : Blo 2171435 3092099 := bstep (se 1 (by rfl) ⟨2319074, by rfl⟩ : syracuseStep 3092099 = 4638149) B4638149
theorem B8245597 : Blo 2171435 8245597 := bstep (se 3 (by rfl) ⟨1546049, by rfl⟩ : syracuseStep 8245597 = 3092099) B3092099
theorem B10994129 : Blo 2171435 10994129 := bstep (se 2 (by rfl) ⟨4122798, by rfl⟩ : syracuseStep 10994129 = 8245597) B8245597
theorem B7329419 : Blo 2171435 7329419 := bstep (se 1 (by rfl) ⟨5497064, by rfl⟩ : syracuseStep 7329419 = 10994129) B10994129
theorem B4886279 : Blo 2171435 4886279 := bstep (se 1 (by rfl) ⟨3664709, by rfl⟩ : syracuseStep 4886279 = 7329419) B7329419
theorem B3257519 : Blo 2171435 3257519 := bstep (se 1 (by rfl) ⟨2443139, by rfl⟩ : syracuseStep 3257519 = 4886279) B4886279
theorem B2171679 : Blo 2171435 2171679 := bstep (se 1 (by rfl) ⟨1628759, by rfl⟩ : syracuseStep 2171679 = 3257519) B3257519
theorem B3257525 : Blo 2171435 3257525 := bbase (se 5 (by rfl) ⟨152696, by rfl⟩ : syracuseStep 3257525 = 305393) (by norm_num)
theorem B2171683 : Blo 2171435 2171683 := bstep (se 1 (by rfl) ⟨1628762, by rfl⟩ : syracuseStep 2171683 = 3257525) B3257525
theorem B5497085 : Blo 2171435 5497085 := bbase (se 3 (by rfl) ⟨1030703, by rfl⟩ : syracuseStep 5497085 = 2061407) (by norm_num)
theorem B3664723 : Blo 2171435 3664723 := bstep (se 1 (by rfl) ⟨2748542, by rfl⟩ : syracuseStep 3664723 = 5497085) B5497085
theorem B4886297 : Blo 2171435 4886297 := bstep (se 2 (by rfl) ⟨1832361, by rfl⟩ : syracuseStep 4886297 = 3664723) B3664723
theorem B3257531 : Blo 2171435 3257531 := bstep (se 1 (by rfl) ⟨2443148, by rfl⟩ : syracuseStep 3257531 = 4886297) B4886297
theorem B2171687 : Blo 2171435 2171687 := bstep (se 1 (by rfl) ⟨1628765, by rfl⟩ : syracuseStep 2171687 = 3257531) B3257531
theorem B2443153 : Blo 2171435 2443153 := bbase (se 2 (by rfl) ⟨916182, by rfl⟩ : syracuseStep 2443153 = 1832365) (by norm_num)
theorem B3257537 : Blo 2171435 3257537 := bstep (se 2 (by rfl) ⟨1221576, by rfl⟩ : syracuseStep 3257537 = 2443153) B2443153
theorem B2171691 : Blo 2171435 2171691 := bstep (se 1 (by rfl) ⟨1628768, by rfl⟩ : syracuseStep 2171691 = 3257537) B3257537
theorem B4122829 : Blo 2171435 4122829 := bbase (se 3 (by rfl) ⟨773030, by rfl⟩ : syracuseStep 4122829 = 1546061) (by norm_num)
theorem B5497105 : Blo 2171435 5497105 := bstep (se 2 (by rfl) ⟨2061414, by rfl⟩ : syracuseStep 5497105 = 4122829) B4122829
theorem B7329473 : Blo 2171435 7329473 := bstep (se 2 (by rfl) ⟨2748552, by rfl⟩ : syracuseStep 7329473 = 5497105) B5497105
theorem B4886315 : Blo 2171435 4886315 := bstep (se 1 (by rfl) ⟨3664736, by rfl⟩ : syracuseStep 4886315 = 7329473) B7329473
theorem B3257543 : Blo 2171435 3257543 := bstep (se 1 (by rfl) ⟨2443157, by rfl⟩ : syracuseStep 3257543 = 4886315) B4886315
theorem B2171695 : Blo 2171435 2171695 := bstep (se 1 (by rfl) ⟨1628771, by rfl⟩ : syracuseStep 2171695 = 3257543) B3257543
theorem B3257549 : Blo 2171435 3257549 := bbase (se 3 (by rfl) ⟨610790, by rfl⟩ : syracuseStep 3257549 = 1221581) (by norm_num)
theorem B2171699 : Blo 2171435 2171699 := bstep (se 1 (by rfl) ⟨1628774, by rfl⟩ : syracuseStep 2171699 = 3257549) B3257549
theorem B4886333 : Blo 2171435 4886333 := bbase (se 3 (by rfl) ⟨916187, by rfl⟩ : syracuseStep 4886333 = 1832375) (by norm_num)
theorem B3257555 : Blo 2171435 3257555 := bstep (se 1 (by rfl) ⟨2443166, by rfl⟩ : syracuseStep 3257555 = 4886333) B4886333
theorem B2171703 : Blo 2171435 2171703 := bstep (se 1 (by rfl) ⟨1628777, by rfl⟩ : syracuseStep 2171703 = 3257555) B3257555
theorem B3664757 : Blo 2171435 3664757 := bbase (se 5 (by rfl) ⟨171785, by rfl⟩ : syracuseStep 3664757 = 343571) (by norm_num)
theorem B2443171 : Blo 2171435 2443171 := bstep (se 1 (by rfl) ⟨1832378, by rfl⟩ : syracuseStep 2443171 = 3664757) B3664757
theorem B3257561 : Blo 2171435 3257561 := bstep (se 2 (by rfl) ⟨1221585, by rfl⟩ : syracuseStep 3257561 = 2443171) B2443171
theorem B2171707 : Blo 2171435 2171707 := bstep (se 1 (by rfl) ⟨1628780, by rfl⟩ : syracuseStep 2171707 = 3257561) B3257561
theorem B5870245 : Blo 2171435 5870245 := bbase (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) (by norm_num)
theorem B7826993 : Blo 2171435 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B5217995 : Blo 2171435 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B3478663 : Blo 2171435 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B4638217 : Blo 2171435 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B6184289 : Blo 2171435 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B16491437 : Blo 2171435 16491437 := bstep (se 3 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 16491437 = 6184289) B6184289
theorem B10994291 : Blo 2171435 10994291 := bstep (se 1 (by rfl) ⟨8245718, by rfl⟩ : syracuseStep 10994291 = 16491437) B16491437
theorem B7329527 : Blo 2171435 7329527 := bstep (se 1 (by rfl) ⟨5497145, by rfl⟩ : syracuseStep 7329527 = 10994291) B10994291
theorem B4886351 : Blo 2171435 4886351 := bstep (se 1 (by rfl) ⟨3664763, by rfl⟩ : syracuseStep 4886351 = 7329527) B7329527
theorem B3257567 : Blo 2171435 3257567 := bstep (se 1 (by rfl) ⟨2443175, by rfl⟩ : syracuseStep 3257567 = 4886351) B4886351
theorem B2171711 : Blo 2171435 2171711 := bstep (se 1 (by rfl) ⟨1628783, by rfl⟩ : syracuseStep 2171711 = 3257567) B3257567
theorem B3257573 : Blo 2171435 3257573 := bbase (se 4 (by rfl) ⟨305397, by rfl⟩ : syracuseStep 3257573 = 610795) (by norm_num)
theorem B2171715 : Blo 2171435 2171715 := bstep (se 1 (by rfl) ⟨1628786, by rfl⟩ : syracuseStep 2171715 = 3257573) B3257573
theorem B2510309 : Blo 2171435 2510309 := bbase (se 4 (by rfl) ⟨235341, by rfl⟩ : syracuseStep 2510309 = 470683) (by norm_num)
theorem B6694157 : Blo 2171435 6694157 := bstep (se 3 (by rfl) ⟨1255154, by rfl⟩ : syracuseStep 6694157 = 2510309) B2510309
theorem B4462771 : Blo 2171435 4462771 := bstep (se 1 (by rfl) ⟨3347078, by rfl⟩ : syracuseStep 4462771 = 6694157) B6694157
theorem B5950361 : Blo 2171435 5950361 := bstep (se 2 (by rfl) ⟨2231385, by rfl⟩ : syracuseStep 5950361 = 4462771) B4462771
theorem B3966907 : Blo 2171435 3966907 := bstep (se 1 (by rfl) ⟨2975180, by rfl⟩ : syracuseStep 3966907 = 5950361) B5950361
theorem B5289209 : Blo 2171435 5289209 := bstep (se 2 (by rfl) ⟨1983453, by rfl⟩ : syracuseStep 5289209 = 3966907) B3966907
theorem B3526139 : Blo 2171435 3526139 := bstep (se 1 (by rfl) ⟨2644604, by rfl⟩ : syracuseStep 3526139 = 5289209) B5289209
theorem B9403037 : Blo 2171435 9403037 := bstep (se 3 (by rfl) ⟨1763069, by rfl⟩ : syracuseStep 9403037 = 3526139) B3526139
theorem B6268691 : Blo 2171435 6268691 := bstep (se 1 (by rfl) ⟨4701518, by rfl⟩ : syracuseStep 6268691 = 9403037) B9403037
theorem B4179127 : Blo 2171435 4179127 := bstep (se 1 (by rfl) ⟨3134345, by rfl⟩ : syracuseStep 4179127 = 6268691) B6268691
theorem B5572169 : Blo 2171435 5572169 := bstep (se 2 (by rfl) ⟨2089563, by rfl⟩ : syracuseStep 5572169 = 4179127) B4179127
theorem B3714779 : Blo 2171435 3714779 := bstep (se 1 (by rfl) ⟨2786084, by rfl⟩ : syracuseStep 3714779 = 5572169) B5572169
theorem B9906077 : Blo 2171435 9906077 := bstep (se 3 (by rfl) ⟨1857389, by rfl⟩ : syracuseStep 9906077 = 3714779) B3714779
theorem B26416205 : Blo 2171435 26416205 := bstep (se 3 (by rfl) ⟨4953038, by rfl⟩ : syracuseStep 26416205 = 9906077) B9906077
theorem B17610803 : Blo 2171435 17610803 := bstep (se 1 (by rfl) ⟨13208102, by rfl⟩ : syracuseStep 17610803 = 26416205) B26416205
theorem B11740535 : Blo 2171435 11740535 := bstep (se 1 (by rfl) ⟨8805401, by rfl⟩ : syracuseStep 11740535 = 17610803) B17610803
theorem B7827023 : Blo 2171435 7827023 := bstep (se 1 (by rfl) ⟨5870267, by rfl⟩ : syracuseStep 7827023 = 11740535) B11740535
theorem B5218015 : Blo 2171435 5218015 := bstep (se 1 (by rfl) ⟨3913511, by rfl⟩ : syracuseStep 5218015 = 7827023) B7827023
theorem B6957353 : Blo 2171435 6957353 := bstep (se 2 (by rfl) ⟨2609007, by rfl⟩ : syracuseStep 6957353 = 5218015) B5218015
theorem B4638235 : Blo 2171435 4638235 := bstep (se 1 (by rfl) ⟨3478676, by rfl⟩ : syracuseStep 4638235 = 6957353) B6957353
theorem B6184313 : Blo 2171435 6184313 := bstep (se 2 (by rfl) ⟨2319117, by rfl⟩ : syracuseStep 6184313 = 4638235) B4638235
theorem B4122875 : Blo 2171435 4122875 := bstep (se 1 (by rfl) ⟨3092156, by rfl⟩ : syracuseStep 4122875 = 6184313) B6184313
theorem B2748583 : Blo 2171435 2748583 := bstep (se 1 (by rfl) ⟨2061437, by rfl⟩ : syracuseStep 2748583 = 4122875) B4122875
theorem B3664777 : Blo 2171435 3664777 := bstep (se 2 (by rfl) ⟨1374291, by rfl⟩ : syracuseStep 3664777 = 2748583) B2748583
theorem B4886369 : Blo 2171435 4886369 := bstep (se 2 (by rfl) ⟨1832388, by rfl⟩ : syracuseStep 4886369 = 3664777) B3664777
theorem B3257579 : Blo 2171435 3257579 := bstep (se 1 (by rfl) ⟨2443184, by rfl⟩ : syracuseStep 3257579 = 4886369) B4886369
theorem B2171719 : Blo 2171435 2171719 := bstep (se 1 (by rfl) ⟨1628789, by rfl⟩ : syracuseStep 2171719 = 3257579) B3257579
theorem B2443189 : Blo 2171435 2443189 := bbase (se 5 (by rfl) ⟨114524, by rfl⟩ : syracuseStep 2443189 = 229049) (by norm_num)
theorem B3257585 : Blo 2171435 3257585 := bstep (se 2 (by rfl) ⟨1221594, by rfl⟩ : syracuseStep 3257585 = 2443189) B2443189
theorem B2171723 : Blo 2171435 2171723 := bstep (se 1 (by rfl) ⟨1628792, by rfl⟩ : syracuseStep 2171723 = 3257585) B3257585
theorem B2748593 : Blo 2171435 2748593 := bbase (se 2 (by rfl) ⟨1030722, by rfl⟩ : syracuseStep 2748593 = 2061445) (by norm_num)
theorem B7329581 : Blo 2171435 7329581 := bstep (se 3 (by rfl) ⟨1374296, by rfl⟩ : syracuseStep 7329581 = 2748593) B2748593
theorem B4886387 : Blo 2171435 4886387 := bstep (se 1 (by rfl) ⟨3664790, by rfl⟩ : syracuseStep 4886387 = 7329581) B7329581
theorem B3257591 : Blo 2171435 3257591 := bstep (se 1 (by rfl) ⟨2443193, by rfl⟩ : syracuseStep 3257591 = 4886387) B4886387
theorem B2171727 : Blo 2171435 2171727 := bstep (se 1 (by rfl) ⟨1628795, by rfl⟩ : syracuseStep 2171727 = 3257591) B3257591
theorem B3257597 : Blo 2171435 3257597 := bbase (se 3 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 3257597 = 1221599) (by norm_num)
theorem B2171731 : Blo 2171435 2171731 := bstep (se 1 (by rfl) ⟨1628798, by rfl⟩ : syracuseStep 2171731 = 3257597) B3257597
theorem B4886405 : Blo 2171435 4886405 := bbase (se 4 (by rfl) ⟨458100, by rfl⟩ : syracuseStep 4886405 = 916201) (by norm_num)
theorem B3257603 : Blo 2171435 3257603 := bstep (se 1 (by rfl) ⟨2443202, by rfl⟩ : syracuseStep 3257603 = 4886405) B4886405
theorem B2171735 : Blo 2171435 2171735 := bstep (se 1 (by rfl) ⟨1628801, by rfl⟩ : syracuseStep 2171735 = 3257603) B3257603
theorem B3478709 : Blo 2171435 3478709 := bbase (se 5 (by rfl) ⟨163064, by rfl⟩ : syracuseStep 3478709 = 326129) (by norm_num)
theorem B2319139 : Blo 2171435 2319139 := bstep (se 1 (by rfl) ⟨1739354, by rfl⟩ : syracuseStep 2319139 = 3478709) B3478709
theorem B3092185 : Blo 2171435 3092185 := bstep (se 2 (by rfl) ⟨1159569, by rfl⟩ : syracuseStep 3092185 = 2319139) B2319139
theorem B4122913 : Blo 2171435 4122913 := bstep (se 2 (by rfl) ⟨1546092, by rfl⟩ : syracuseStep 4122913 = 3092185) B3092185
theorem B5497217 : Blo 2171435 5497217 := bstep (se 2 (by rfl) ⟨2061456, by rfl⟩ : syracuseStep 5497217 = 4122913) B4122913
theorem B3664811 : Blo 2171435 3664811 := bstep (se 1 (by rfl) ⟨2748608, by rfl⟩ : syracuseStep 3664811 = 5497217) B5497217
theorem B2443207 : Blo 2171435 2443207 := bstep (se 1 (by rfl) ⟨1832405, by rfl⟩ : syracuseStep 2443207 = 3664811) B3664811
theorem B3257609 : Blo 2171435 3257609 := bstep (se 2 (by rfl) ⟨1221603, by rfl⟩ : syracuseStep 3257609 = 2443207) B2443207
theorem B2171739 : Blo 2171435 2171739 := bstep (se 1 (by rfl) ⟨1628804, by rfl⟩ : syracuseStep 2171739 = 3257609) B3257609
theorem B10994453 : Blo 2171435 10994453 := bbase (se 6 (by rfl) ⟨257682, by rfl⟩ : syracuseStep 10994453 = 515365) (by norm_num)
theorem B7329635 : Blo 2171435 7329635 := bstep (se 1 (by rfl) ⟨5497226, by rfl⟩ : syracuseStep 7329635 = 10994453) B10994453
theorem B4886423 : Blo 2171435 4886423 := bstep (se 1 (by rfl) ⟨3664817, by rfl⟩ : syracuseStep 4886423 = 7329635) B7329635
theorem B3257615 : Blo 2171435 3257615 := bstep (se 1 (by rfl) ⟨2443211, by rfl⟩ : syracuseStep 3257615 = 4886423) B4886423
theorem B2171743 : Blo 2171435 2171743 := bstep (se 1 (by rfl) ⟨1628807, by rfl⟩ : syracuseStep 2171743 = 3257615) B3257615
theorem B3257621 : Blo 2171435 3257621 := bbase (se 6 (by rfl) ⟨76350, by rfl⟩ : syracuseStep 3257621 = 152701) (by norm_num)
theorem B2171747 : Blo 2171435 2171747 := bstep (se 1 (by rfl) ⟨1628810, by rfl⟩ : syracuseStep 2171747 = 3257621) B3257621
theorem B2786125 : Blo 2171435 2786125 := bbase (se 3 (by rfl) ⟨522398, by rfl⟩ : syracuseStep 2786125 = 1044797) (by norm_num)
theorem B3714833 : Blo 2171435 3714833 := bstep (se 2 (by rfl) ⟨1393062, by rfl⟩ : syracuseStep 3714833 = 2786125) B2786125
theorem B2476555 : Blo 2171435 2476555 := bstep (se 1 (by rfl) ⟨1857416, by rfl⟩ : syracuseStep 2476555 = 3714833) B3714833
theorem B13208293 : Blo 2171435 13208293 := bstep (se 4 (by rfl) ⟨1238277, by rfl⟩ : syracuseStep 13208293 = 2476555) B2476555
theorem B17611057 : Blo 2171435 17611057 := bstep (se 2 (by rfl) ⟨6604146, by rfl⟩ : syracuseStep 17611057 = 13208293) B13208293
theorem B23481409 : Blo 2171435 23481409 := bstep (se 2 (by rfl) ⟨8805528, by rfl⟩ : syracuseStep 23481409 = 17611057) B17611057
theorem B31308545 : Blo 2171435 31308545 := bstep (se 2 (by rfl) ⟨11740704, by rfl⟩ : syracuseStep 31308545 = 23481409) B23481409
theorem B20872363 : Blo 2171435 20872363 := bstep (se 1 (by rfl) ⟨15654272, by rfl⟩ : syracuseStep 20872363 = 31308545) B31308545
theorem B27829817 : Blo 2171435 27829817 := bstep (se 2 (by rfl) ⟨10436181, by rfl⟩ : syracuseStep 27829817 = 20872363) B20872363
theorem B18553211 : Blo 2171435 18553211 := bstep (se 1 (by rfl) ⟨13914908, by rfl⟩ : syracuseStep 18553211 = 27829817) B27829817
theorem B12368807 : Blo 2171435 12368807 := bstep (se 1 (by rfl) ⟨9276605, by rfl⟩ : syracuseStep 12368807 = 18553211) B18553211
theorem B8245871 : Blo 2171435 8245871 := bstep (se 1 (by rfl) ⟨6184403, by rfl⟩ : syracuseStep 8245871 = 12368807) B12368807
theorem B5497247 : Blo 2171435 5497247 := bstep (se 1 (by rfl) ⟨4122935, by rfl⟩ : syracuseStep 5497247 = 8245871) B8245871
theorem B3664831 : Blo 2171435 3664831 := bstep (se 1 (by rfl) ⟨2748623, by rfl⟩ : syracuseStep 3664831 = 5497247) B5497247
theorem B4886441 : Blo 2171435 4886441 := bstep (se 2 (by rfl) ⟨1832415, by rfl⟩ : syracuseStep 4886441 = 3664831) B3664831
theorem B3257627 : Blo 2171435 3257627 := bstep (se 1 (by rfl) ⟨2443220, by rfl⟩ : syracuseStep 3257627 = 4886441) B4886441
theorem B2171751 : Blo 2171435 2171751 := bstep (se 1 (by rfl) ⟨1628813, by rfl⟩ : syracuseStep 2171751 = 3257627) B3257627
theorem B2443225 : Blo 2171435 2443225 := bbase (se 2 (by rfl) ⟨916209, by rfl⟩ : syracuseStep 2443225 = 1832419) (by norm_num)
theorem B3257633 : Blo 2171435 3257633 := bstep (se 2 (by rfl) ⟨1221612, by rfl⟩ : syracuseStep 3257633 = 2443225) B2443225
theorem B2171755 : Blo 2171435 2171755 := bstep (se 1 (by rfl) ⟨1628816, by rfl⟩ : syracuseStep 2171755 = 3257633) B3257633
theorem B3092213 : Blo 2171435 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B8245901 : Blo 2171435 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B5497267 : Blo 2171435 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B7329689 : Blo 2171435 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B4886459 : Blo 2171435 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B3257639 : Blo 2171435 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B2171759 : Blo 2171435 2171759 := bstep (se 1 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 2171759 = 3257639) B3257639
theorem B3257645 : Blo 2171435 3257645 := bbase (se 3 (by rfl) ⟨610808, by rfl⟩ : syracuseStep 3257645 = 1221617) (by norm_num)
theorem B2171763 : Blo 2171435 2171763 := bstep (se 1 (by rfl) ⟨1628822, by rfl⟩ : syracuseStep 2171763 = 3257645) B3257645
theorem B4886477 : Blo 2171435 4886477 := bbase (se 3 (by rfl) ⟨916214, by rfl⟩ : syracuseStep 4886477 = 1832429) (by norm_num)
theorem B3257651 : Blo 2171435 3257651 := bstep (se 1 (by rfl) ⟨2443238, by rfl⟩ : syracuseStep 3257651 = 4886477) B4886477
theorem B2171767 : Blo 2171435 2171767 := bstep (se 1 (by rfl) ⟨1628825, by rfl⟩ : syracuseStep 2171767 = 3257651) B3257651
theorem B2748649 : Blo 2171435 2748649 := bbase (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) (by norm_num)
theorem B3664865 : Blo 2171435 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B2443243 : Blo 2171435 2443243 := bstep (se 1 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 2443243 = 3664865) B3664865
theorem B3257657 : Blo 2171435 3257657 := bstep (se 2 (by rfl) ⟨1221621, by rfl⟩ : syracuseStep 3257657 = 2443243) B2443243
theorem B2171771 : Blo 2171435 2171771 := bstep (se 1 (by rfl) ⟨1628828, by rfl⟩ : syracuseStep 2171771 = 3257657) B3257657
theorem B13915061 : Blo 2171435 13915061 := bbase (se 5 (by rfl) ⟨652268, by rfl⟩ : syracuseStep 13915061 = 1304537) (by norm_num)
theorem B9276707 : Blo 2171435 9276707 := bstep (se 1 (by rfl) ⟨6957530, by rfl⟩ : syracuseStep 9276707 = 13915061) B13915061
theorem B24737885 : Blo 2171435 24737885 := bstep (se 3 (by rfl) ⟨4638353, by rfl⟩ : syracuseStep 24737885 = 9276707) B9276707
theorem B16491923 : Blo 2171435 16491923 := bstep (se 1 (by rfl) ⟨12368942, by rfl⟩ : syracuseStep 16491923 = 24737885) B24737885
theorem B10994615 : Blo 2171435 10994615 := bstep (se 1 (by rfl) ⟨8245961, by rfl⟩ : syracuseStep 10994615 = 16491923) B16491923
theorem B7329743 : Blo 2171435 7329743 := bstep (se 1 (by rfl) ⟨5497307, by rfl⟩ : syracuseStep 7329743 = 10994615) B10994615
theorem B4886495 : Blo 2171435 4886495 := bstep (se 1 (by rfl) ⟨3664871, by rfl⟩ : syracuseStep 4886495 = 7329743) B7329743
theorem B3257663 : Blo 2171435 3257663 := bstep (se 1 (by rfl) ⟨2443247, by rfl⟩ : syracuseStep 3257663 = 4886495) B4886495
theorem B2171775 : Blo 2171435 2171775 := bstep (se 1 (by rfl) ⟨1628831, by rfl⟩ : syracuseStep 2171775 = 3257663) B3257663
theorem B3257669 : Blo 2171435 3257669 := bbase (se 4 (by rfl) ⟨305406, by rfl⟩ : syracuseStep 3257669 = 610813) (by norm_num)
theorem B2171779 : Blo 2171435 2171779 := bstep (se 1 (by rfl) ⟨1628834, by rfl⟩ : syracuseStep 2171779 = 3257669) B3257669
theorem B3664885 : Blo 2171435 3664885 := bbase (se 5 (by rfl) ⟨171791, by rfl⟩ : syracuseStep 3664885 = 343583) (by norm_num)
theorem B4886513 : Blo 2171435 4886513 := bstep (se 2 (by rfl) ⟨1832442, by rfl⟩ : syracuseStep 4886513 = 3664885) B3664885
theorem B3257675 : Blo 2171435 3257675 := bstep (se 1 (by rfl) ⟨2443256, by rfl⟩ : syracuseStep 3257675 = 4886513) B4886513
theorem B2171783 : Blo 2171435 2171783 := bstep (se 1 (by rfl) ⟨1628837, by rfl⟩ : syracuseStep 2171783 = 3257675) B3257675
theorem B2443261 : Blo 2171435 2443261 := bbase (se 3 (by rfl) ⟨458111, by rfl⟩ : syracuseStep 2443261 = 916223) (by norm_num)
theorem B3257681 : Blo 2171435 3257681 := bstep (se 2 (by rfl) ⟨1221630, by rfl⟩ : syracuseStep 3257681 = 2443261) B2443261
theorem B2171787 : Blo 2171435 2171787 := bstep (se 1 (by rfl) ⟨1628840, by rfl⟩ : syracuseStep 2171787 = 3257681) B3257681
theorem B7329797 : Blo 2171435 7329797 := bbase (se 4 (by rfl) ⟨687168, by rfl⟩ : syracuseStep 7329797 = 1374337) (by norm_num)
theorem B4886531 : Blo 2171435 4886531 := bstep (se 1 (by rfl) ⟨3664898, by rfl⟩ : syracuseStep 4886531 = 7329797) B7329797
theorem B3257687 : Blo 2171435 3257687 := bstep (se 1 (by rfl) ⟨2443265, by rfl⟩ : syracuseStep 3257687 = 4886531) B4886531
theorem B2171791 : Blo 2171435 2171791 := bstep (se 1 (by rfl) ⟨1628843, by rfl⟩ : syracuseStep 2171791 = 3257687) B3257687
theorem B3257693 : Blo 2171435 3257693 := bbase (se 3 (by rfl) ⟨610817, by rfl⟩ : syracuseStep 3257693 = 1221635) (by norm_num)
theorem B2171795 : Blo 2171435 2171795 := bstep (se 1 (by rfl) ⟨1628846, by rfl⟩ : syracuseStep 2171795 = 3257693) B3257693
theorem B4886549 : Blo 2171435 4886549 := bbase (se 6 (by rfl) ⟨114528, by rfl⟩ : syracuseStep 4886549 = 229057) (by norm_num)
theorem B3257699 : Blo 2171435 3257699 := bstep (se 1 (by rfl) ⟨2443274, by rfl⟩ : syracuseStep 3257699 = 4886549) B4886549
theorem B2171799 : Blo 2171435 2171799 := bstep (se 1 (by rfl) ⟨1628849, by rfl⟩ : syracuseStep 2171799 = 3257699) B3257699
theorem B8246069 : Blo 2171435 8246069 := bbase (se 5 (by rfl) ⟨386534, by rfl⟩ : syracuseStep 8246069 = 773069) (by norm_num)
theorem B5497379 : Blo 2171435 5497379 := bstep (se 1 (by rfl) ⟨4123034, by rfl⟩ : syracuseStep 5497379 = 8246069) B8246069
theorem B3664919 : Blo 2171435 3664919 := bstep (se 1 (by rfl) ⟨2748689, by rfl⟩ : syracuseStep 3664919 = 5497379) B5497379
theorem B2443279 : Blo 2171435 2443279 := bstep (se 1 (by rfl) ⟨1832459, by rfl⟩ : syracuseStep 2443279 = 3664919) B3664919
theorem B3257705 : Blo 2171435 3257705 := bstep (se 2 (by rfl) ⟨1221639, by rfl⟩ : syracuseStep 3257705 = 2443279) B2443279
theorem B2171803 : Blo 2171435 2171803 := bstep (se 1 (by rfl) ⟨1628852, by rfl⟩ : syracuseStep 2171803 = 3257705) B3257705
theorem B2609113 : Blo 2171435 2609113 := bbase (se 2 (by rfl) ⟨978417, by rfl⟩ : syracuseStep 2609113 = 1956835) (by norm_num)
theorem B3478817 : Blo 2171435 3478817 := bstep (se 2 (by rfl) ⟨1304556, by rfl⟩ : syracuseStep 3478817 = 2609113) B2609113
theorem B2319211 : Blo 2171435 2319211 := bstep (se 1 (by rfl) ⟨1739408, by rfl⟩ : syracuseStep 2319211 = 3478817) B3478817
theorem B12369125 : Blo 2171435 12369125 := bstep (se 4 (by rfl) ⟨1159605, by rfl⟩ : syracuseStep 12369125 = 2319211) B2319211
theorem B8246083 : Blo 2171435 8246083 := bstep (se 1 (by rfl) ⟨6184562, by rfl⟩ : syracuseStep 8246083 = 12369125) B12369125
theorem B10994777 : Blo 2171435 10994777 := bstep (se 2 (by rfl) ⟨4123041, by rfl⟩ : syracuseStep 10994777 = 8246083) B8246083
theorem B7329851 : Blo 2171435 7329851 := bstep (se 1 (by rfl) ⟨5497388, by rfl⟩ : syracuseStep 7329851 = 10994777) B10994777
theorem B4886567 : Blo 2171435 4886567 := bstep (se 1 (by rfl) ⟨3664925, by rfl⟩ : syracuseStep 4886567 = 7329851) B7329851
theorem B3257711 : Blo 2171435 3257711 := bstep (se 1 (by rfl) ⟨2443283, by rfl⟩ : syracuseStep 3257711 = 4886567) B4886567
theorem B2171807 : Blo 2171435 2171807 := bstep (se 1 (by rfl) ⟨1628855, by rfl⟩ : syracuseStep 2171807 = 3257711) B3257711
theorem B3257717 : Blo 2171435 3257717 := bbase (se 5 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 3257717 = 305411) (by norm_num)
theorem B2171811 : Blo 2171435 2171811 := bstep (se 1 (by rfl) ⟨1628858, by rfl⟩ : syracuseStep 2171811 = 3257717) B3257717
theorem B3092293 : Blo 2171435 3092293 := bbase (se 4 (by rfl) ⟨289902, by rfl⟩ : syracuseStep 3092293 = 579805) (by norm_num)
theorem B4123057 : Blo 2171435 4123057 := bstep (se 2 (by rfl) ⟨1546146, by rfl⟩ : syracuseStep 4123057 = 3092293) B3092293
theorem B5497409 : Blo 2171435 5497409 := bstep (se 2 (by rfl) ⟨2061528, by rfl⟩ : syracuseStep 5497409 = 4123057) B4123057
theorem B3664939 : Blo 2171435 3664939 := bstep (se 1 (by rfl) ⟨2748704, by rfl⟩ : syracuseStep 3664939 = 5497409) B5497409
theorem B4886585 : Blo 2171435 4886585 := bstep (se 2 (by rfl) ⟨1832469, by rfl⟩ : syracuseStep 4886585 = 3664939) B3664939
theorem B3257723 : Blo 2171435 3257723 := bstep (se 1 (by rfl) ⟨2443292, by rfl⟩ : syracuseStep 3257723 = 4886585) B4886585
theorem B2171815 : Blo 2171435 2171815 := bstep (se 1 (by rfl) ⟨1628861, by rfl⟩ : syracuseStep 2171815 = 3257723) B3257723
theorem B2443297 : Blo 2171435 2443297 := bbase (se 2 (by rfl) ⟨916236, by rfl⟩ : syracuseStep 2443297 = 1832473) (by norm_num)
theorem B3257729 : Blo 2171435 3257729 := bstep (se 2 (by rfl) ⟨1221648, by rfl⟩ : syracuseStep 3257729 = 2443297) B2443297
theorem B2171819 : Blo 2171435 2171819 := bstep (se 1 (by rfl) ⟨1628864, by rfl⟩ : syracuseStep 2171819 = 3257729) B3257729
theorem B5497429 : Blo 2171435 5497429 := bbase (se 8 (by rfl) ⟨32211, by rfl⟩ : syracuseStep 5497429 = 64423) (by norm_num)
theorem B7329905 : Blo 2171435 7329905 := bstep (se 2 (by rfl) ⟨2748714, by rfl⟩ : syracuseStep 7329905 = 5497429) B5497429
theorem B4886603 : Blo 2171435 4886603 := bstep (se 1 (by rfl) ⟨3664952, by rfl⟩ : syracuseStep 4886603 = 7329905) B7329905
theorem B3257735 : Blo 2171435 3257735 := bstep (se 1 (by rfl) ⟨2443301, by rfl⟩ : syracuseStep 3257735 = 4886603) B4886603
theorem B2171823 : Blo 2171435 2171823 := bstep (se 1 (by rfl) ⟨1628867, by rfl⟩ : syracuseStep 2171823 = 3257735) B3257735
theorem B3257741 : Blo 2171435 3257741 := bbase (se 3 (by rfl) ⟨610826, by rfl⟩ : syracuseStep 3257741 = 1221653) (by norm_num)
theorem B2171827 : Blo 2171435 2171827 := bstep (se 1 (by rfl) ⟨1628870, by rfl⟩ : syracuseStep 2171827 = 3257741) B3257741
theorem B4886621 : Blo 2171435 4886621 := bbase (se 3 (by rfl) ⟨916241, by rfl⟩ : syracuseStep 4886621 = 1832483) (by norm_num)
theorem B3257747 : Blo 2171435 3257747 := bstep (se 1 (by rfl) ⟨2443310, by rfl⟩ : syracuseStep 3257747 = 4886621) B4886621
theorem B2171831 : Blo 2171435 2171831 := bstep (se 1 (by rfl) ⟨1628873, by rfl⟩ : syracuseStep 2171831 = 3257747) B3257747
theorem B3664973 : Blo 2171435 3664973 := bbase (se 3 (by rfl) ⟨687182, by rfl⟩ : syracuseStep 3664973 = 1374365) (by norm_num)
theorem B2443315 : Blo 2171435 2443315 := bstep (se 1 (by rfl) ⟨1832486, by rfl⟩ : syracuseStep 2443315 = 3664973) B3664973
theorem B3257753 : Blo 2171435 3257753 := bstep (se 2 (by rfl) ⟨1221657, by rfl⟩ : syracuseStep 3257753 = 2443315) B2443315
theorem B2171835 : Blo 2171435 2171835 := bstep (se 1 (by rfl) ⟨1628876, by rfl⟩ : syracuseStep 2171835 = 3257753) B3257753
theorem B10041781 : Blo 2171435 10041781 := bbase (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) (by norm_num)
theorem B13389041 : Blo 2171435 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B8926027 : Blo 2171435 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B47605477 : Blo 2171435 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B63473969 : Blo 2171435 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B42315979 : Blo 2171435 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B56421305 : Blo 2171435 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B37614203 : Blo 2171435 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B25076135 : Blo 2171435 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B16717423 : Blo 2171435 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B22289897 : Blo 2171435 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B14859931 : Blo 2171435 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B19813241 : Blo 2171435 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B13208827 : Blo 2171435 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B17611769 : Blo 2171435 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B46964717 : Blo 2171435 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B31309811 : Blo 2171435 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B20873207 : Blo 2171435 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B13915471 : Blo 2171435 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B18553961 : Blo 2171435 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B12369307 : Blo 2171435 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B16492409 : Blo 2171435 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B10994939 : Blo 2171435 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B7329959 : Blo 2171435 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B4886639 : Blo 2171435 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B3257759 : Blo 2171435 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B2171839 : Blo 2171435 2171839 := bstep (se 1 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 2171839 = 3257759) B3257759
theorem B3257765 : Blo 2171435 3257765 := bbase (se 4 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 3257765 = 610831) (by norm_num)
theorem B2171843 : Blo 2171435 2171843 := bstep (se 1 (by rfl) ⟨1628882, by rfl⟩ : syracuseStep 2171843 = 3257765) B3257765
theorem B2748745 : Blo 2171435 2748745 := bbase (se 2 (by rfl) ⟨1030779, by rfl⟩ : syracuseStep 2748745 = 2061559) (by norm_num)
theorem B3664993 : Blo 2171435 3664993 := bstep (se 2 (by rfl) ⟨1374372, by rfl⟩ : syracuseStep 3664993 = 2748745) B2748745
theorem B4886657 : Blo 2171435 4886657 := bstep (se 2 (by rfl) ⟨1832496, by rfl⟩ : syracuseStep 4886657 = 3664993) B3664993
theorem B3257771 : Blo 2171435 3257771 := bstep (se 1 (by rfl) ⟨2443328, by rfl⟩ : syracuseStep 3257771 = 4886657) B4886657
theorem B2171847 : Blo 2171435 2171847 := bstep (se 1 (by rfl) ⟨1628885, by rfl⟩ : syracuseStep 2171847 = 3257771) B3257771
theorem B2443333 : Blo 2171435 2443333 := bbase (se 4 (by rfl) ⟨229062, by rfl⟩ : syracuseStep 2443333 = 458125) (by norm_num)
theorem B3257777 : Blo 2171435 3257777 := bstep (se 2 (by rfl) ⟨1221666, by rfl⟩ : syracuseStep 3257777 = 2443333) B2443333
theorem B2171851 : Blo 2171435 2171851 := bstep (se 1 (by rfl) ⟨1628888, by rfl⟩ : syracuseStep 2171851 = 3257777) B3257777
theorem B4123133 : Blo 2171435 4123133 := bbase (se 3 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 4123133 = 1546175) (by norm_num)
theorem B2748755 : Blo 2171435 2748755 := bstep (se 1 (by rfl) ⟨2061566, by rfl⟩ : syracuseStep 2748755 = 4123133) B4123133
theorem B7330013 : Blo 2171435 7330013 := bstep (se 3 (by rfl) ⟨1374377, by rfl⟩ : syracuseStep 7330013 = 2748755) B2748755
theorem B4886675 : Blo 2171435 4886675 := bstep (se 1 (by rfl) ⟨3665006, by rfl⟩ : syracuseStep 4886675 = 7330013) B7330013
theorem B3257783 : Blo 2171435 3257783 := bstep (se 1 (by rfl) ⟨2443337, by rfl⟩ : syracuseStep 3257783 = 4886675) B4886675
theorem B2171855 : Blo 2171435 2171855 := bstep (se 1 (by rfl) ⟨1628891, by rfl⟩ : syracuseStep 2171855 = 3257783) B3257783
theorem B3257789 : Blo 2171435 3257789 := bbase (se 3 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 3257789 = 1221671) (by norm_num)
theorem B2171859 : Blo 2171435 2171859 := bstep (se 1 (by rfl) ⟨1628894, by rfl⟩ : syracuseStep 2171859 = 3257789) B3257789
theorem B4886693 : Blo 2171435 4886693 := bbase (se 4 (by rfl) ⟨458127, by rfl⟩ : syracuseStep 4886693 = 916255) (by norm_num)
theorem B3257795 : Blo 2171435 3257795 := bstep (se 1 (by rfl) ⟨2443346, by rfl⟩ : syracuseStep 3257795 = 4886693) B4886693
theorem B2171863 : Blo 2171435 2171863 := bstep (se 1 (by rfl) ⟨1628897, by rfl⟩ : syracuseStep 2171863 = 3257795) B3257795
theorem B5497541 : Blo 2171435 5497541 := bbase (se 4 (by rfl) ⟨515394, by rfl⟩ : syracuseStep 5497541 = 1030789) (by norm_num)
theorem B3665027 : Blo 2171435 3665027 := bstep (se 1 (by rfl) ⟨2748770, by rfl⟩ : syracuseStep 3665027 = 5497541) B5497541
theorem B2443351 : Blo 2171435 2443351 := bstep (se 1 (by rfl) ⟨1832513, by rfl⟩ : syracuseStep 2443351 = 3665027) B3665027
theorem B3257801 : Blo 2171435 3257801 := bstep (se 2 (by rfl) ⟨1221675, by rfl⟩ : syracuseStep 3257801 = 2443351) B2443351
theorem B2171867 : Blo 2171435 2171867 := bstep (se 1 (by rfl) ⟨1628900, by rfl⟩ : syracuseStep 2171867 = 3257801) B3257801
theorem B23482709 : Blo 2171435 23482709 := bbase (se 10 (by rfl) ⟨34398, by rfl⟩ : syracuseStep 23482709 = 68797) (by norm_num)
theorem B15655139 : Blo 2171435 15655139 := bstep (se 1 (by rfl) ⟨11741354, by rfl⟩ : syracuseStep 15655139 = 23482709) B23482709
theorem B10436759 : Blo 2171435 10436759 := bstep (se 1 (by rfl) ⟨7827569, by rfl⟩ : syracuseStep 10436759 = 15655139) B15655139
theorem B6957839 : Blo 2171435 6957839 := bstep (se 1 (by rfl) ⟨5218379, by rfl⟩ : syracuseStep 6957839 = 10436759) B10436759
theorem B4638559 : Blo 2171435 4638559 := bstep (se 1 (by rfl) ⟨3478919, by rfl⟩ : syracuseStep 4638559 = 6957839) B6957839
theorem B6184745 : Blo 2171435 6184745 := bstep (se 2 (by rfl) ⟨2319279, by rfl⟩ : syracuseStep 6184745 = 4638559) B4638559
theorem B4123163 : Blo 2171435 4123163 := bstep (se 1 (by rfl) ⟨3092372, by rfl⟩ : syracuseStep 4123163 = 6184745) B6184745
theorem B10995101 : Blo 2171435 10995101 := bstep (se 3 (by rfl) ⟨2061581, by rfl⟩ : syracuseStep 10995101 = 4123163) B4123163
theorem B7330067 : Blo 2171435 7330067 := bstep (se 1 (by rfl) ⟨5497550, by rfl⟩ : syracuseStep 7330067 = 10995101) B10995101
theorem B4886711 : Blo 2171435 4886711 := bstep (se 1 (by rfl) ⟨3665033, by rfl⟩ : syracuseStep 4886711 = 7330067) B7330067
theorem B3257807 : Blo 2171435 3257807 := bstep (se 1 (by rfl) ⟨2443355, by rfl⟩ : syracuseStep 3257807 = 4886711) B4886711
theorem B2171871 : Blo 2171435 2171871 := bstep (se 1 (by rfl) ⟨1628903, by rfl⟩ : syracuseStep 2171871 = 3257807) B3257807
theorem B3257813 : Blo 2171435 3257813 := bbase (se 7 (by rfl) ⟨38177, by rfl⟩ : syracuseStep 3257813 = 76355) (by norm_num)
theorem B2171875 : Blo 2171435 2171875 := bstep (se 1 (by rfl) ⟨1628906, by rfl⟩ : syracuseStep 2171875 = 3257813) B3257813
theorem B8246357 : Blo 2171435 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B5497571 : Blo 2171435 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B3665047 : Blo 2171435 3665047 := bstep (se 1 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 3665047 = 5497571) B5497571
theorem B4886729 : Blo 2171435 4886729 := bstep (se 2 (by rfl) ⟨1832523, by rfl⟩ : syracuseStep 4886729 = 3665047) B3665047
theorem B3257819 : Blo 2171435 3257819 := bstep (se 1 (by rfl) ⟨2443364, by rfl⟩ : syracuseStep 3257819 = 4886729) B4886729
theorem B2171879 : Blo 2171435 2171879 := bstep (se 1 (by rfl) ⟨1628909, by rfl⟩ : syracuseStep 2171879 = 3257819) B3257819
theorem B2443369 : Blo 2171435 2443369 := bbase (se 2 (by rfl) ⟨916263, by rfl⟩ : syracuseStep 2443369 = 1832527) (by norm_num)
theorem B3257825 : Blo 2171435 3257825 := bstep (se 2 (by rfl) ⟨1221684, by rfl⟩ : syracuseStep 3257825 = 2443369) B2443369
theorem B2171883 : Blo 2171435 2171883 := bstep (se 1 (by rfl) ⟨1628912, by rfl⟩ : syracuseStep 2171883 = 3257825) B3257825
theorem B2609209 : Blo 2171435 2609209 := bbase (se 2 (by rfl) ⟨978453, by rfl⟩ : syracuseStep 2609209 = 1956907) (by norm_num)
theorem B3478945 : Blo 2171435 3478945 := bstep (se 2 (by rfl) ⟨1304604, by rfl⟩ : syracuseStep 3478945 = 2609209) B2609209
theorem B4638593 : Blo 2171435 4638593 := bstep (se 2 (by rfl) ⟨1739472, by rfl⟩ : syracuseStep 4638593 = 3478945) B3478945
theorem B12369581 : Blo 2171435 12369581 := bstep (se 3 (by rfl) ⟨2319296, by rfl⟩ : syracuseStep 12369581 = 4638593) B4638593
theorem B8246387 : Blo 2171435 8246387 := bstep (se 1 (by rfl) ⟨6184790, by rfl⟩ : syracuseStep 8246387 = 12369581) B12369581
theorem B5497591 : Blo 2171435 5497591 := bstep (se 1 (by rfl) ⟨4123193, by rfl⟩ : syracuseStep 5497591 = 8246387) B8246387
theorem B7330121 : Blo 2171435 7330121 := bstep (se 2 (by rfl) ⟨2748795, by rfl⟩ : syracuseStep 7330121 = 5497591) B5497591
theorem B4886747 : Blo 2171435 4886747 := bstep (se 1 (by rfl) ⟨3665060, by rfl⟩ : syracuseStep 4886747 = 7330121) B7330121
theorem B3257831 : Blo 2171435 3257831 := bstep (se 1 (by rfl) ⟨2443373, by rfl⟩ : syracuseStep 3257831 = 4886747) B4886747
theorem B2171887 : Blo 2171435 2171887 := bstep (se 1 (by rfl) ⟨1628915, by rfl⟩ : syracuseStep 2171887 = 3257831) B3257831
theorem B3257837 : Blo 2171435 3257837 := bbase (se 3 (by rfl) ⟨610844, by rfl⟩ : syracuseStep 3257837 = 1221689) (by norm_num)
theorem B2171891 : Blo 2171435 2171891 := bstep (se 1 (by rfl) ⟨1628918, by rfl⟩ : syracuseStep 2171891 = 3257837) B3257837
theorem B4886765 : Blo 2171435 4886765 := bbase (se 3 (by rfl) ⟨916268, by rfl⟩ : syracuseStep 4886765 = 1832537) (by norm_num)
theorem B3257843 : Blo 2171435 3257843 := bstep (se 1 (by rfl) ⟨2443382, by rfl⟩ : syracuseStep 3257843 = 4886765) B4886765
theorem B2171895 : Blo 2171435 2171895 := bstep (se 1 (by rfl) ⟨1628921, by rfl⟩ : syracuseStep 2171895 = 3257843) B3257843
theorem B3092413 : Blo 2171435 3092413 := bbase (se 3 (by rfl) ⟨579827, by rfl⟩ : syracuseStep 3092413 = 1159655) (by norm_num)
theorem B4123217 : Blo 2171435 4123217 := bstep (se 2 (by rfl) ⟨1546206, by rfl⟩ : syracuseStep 4123217 = 3092413) B3092413
theorem B2748811 : Blo 2171435 2748811 := bstep (se 1 (by rfl) ⟨2061608, by rfl⟩ : syracuseStep 2748811 = 4123217) B4123217
theorem B3665081 : Blo 2171435 3665081 := bstep (se 2 (by rfl) ⟨1374405, by rfl⟩ : syracuseStep 3665081 = 2748811) B2748811
theorem B2443387 : Blo 2171435 2443387 := bstep (se 1 (by rfl) ⟨1832540, by rfl⟩ : syracuseStep 2443387 = 3665081) B3665081
theorem B3257849 : Blo 2171435 3257849 := bstep (se 2 (by rfl) ⟨1221693, by rfl⟩ : syracuseStep 3257849 = 2443387) B2443387
theorem B2171899 : Blo 2171435 2171899 := bstep (se 1 (by rfl) ⟨1628924, by rfl⟩ : syracuseStep 2171899 = 3257849) B3257849
theorem B11741525 : Blo 2171435 11741525 := bbase (se 10 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 11741525 = 34399) (by norm_num)
theorem B7827683 : Blo 2171435 7827683 := bstep (se 1 (by rfl) ⟨5870762, by rfl⟩ : syracuseStep 7827683 = 11741525) B11741525
theorem B83495285 : Blo 2171435 83495285 := bstep (se 5 (by rfl) ⟨3913841, by rfl⟩ : syracuseStep 83495285 = 7827683) B7827683
theorem B55663523 : Blo 2171435 55663523 := bstep (se 1 (by rfl) ⟨41747642, by rfl⟩ : syracuseStep 55663523 = 83495285) B83495285
theorem B37109015 : Blo 2171435 37109015 := bstep (se 1 (by rfl) ⟨27831761, by rfl⟩ : syracuseStep 37109015 = 55663523) B55663523
theorem B24739343 : Blo 2171435 24739343 := bstep (se 1 (by rfl) ⟨18554507, by rfl⟩ : syracuseStep 24739343 = 37109015) B37109015
theorem B16492895 : Blo 2171435 16492895 := bstep (se 1 (by rfl) ⟨12369671, by rfl⟩ : syracuseStep 16492895 = 24739343) B24739343
theorem B10995263 : Blo 2171435 10995263 := bstep (se 1 (by rfl) ⟨8246447, by rfl⟩ : syracuseStep 10995263 = 16492895) B16492895
theorem B7330175 : Blo 2171435 7330175 := bstep (se 1 (by rfl) ⟨5497631, by rfl⟩ : syracuseStep 7330175 = 10995263) B10995263
theorem B4886783 : Blo 2171435 4886783 := bstep (se 1 (by rfl) ⟨3665087, by rfl⟩ : syracuseStep 4886783 = 7330175) B7330175
theorem B3257855 : Blo 2171435 3257855 := bstep (se 1 (by rfl) ⟨2443391, by rfl⟩ : syracuseStep 3257855 = 4886783) B4886783
theorem B2171903 : Blo 2171435 2171903 := bstep (se 1 (by rfl) ⟨1628927, by rfl⟩ : syracuseStep 2171903 = 3257855) B3257855
theorem B3257861 : Blo 2171435 3257861 := bbase (se 4 (by rfl) ⟨305424, by rfl⟩ : syracuseStep 3257861 = 610849) (by norm_num)
theorem B2171907 : Blo 2171435 2171907 := bstep (se 1 (by rfl) ⟨1628930, by rfl⟩ : syracuseStep 2171907 = 3257861) B3257861
theorem B3665101 : Blo 2171435 3665101 := bbase (se 3 (by rfl) ⟨687206, by rfl⟩ : syracuseStep 3665101 = 1374413) (by norm_num)
theorem B4886801 : Blo 2171435 4886801 := bstep (se 2 (by rfl) ⟨1832550, by rfl⟩ : syracuseStep 4886801 = 3665101) B3665101
theorem B3257867 : Blo 2171435 3257867 := bstep (se 1 (by rfl) ⟨2443400, by rfl⟩ : syracuseStep 3257867 = 4886801) B4886801
theorem B2171911 : Blo 2171435 2171911 := bstep (se 1 (by rfl) ⟨1628933, by rfl⟩ : syracuseStep 2171911 = 3257867) B3257867
theorem B2443405 : Blo 2171435 2443405 := bbase (se 3 (by rfl) ⟨458138, by rfl⟩ : syracuseStep 2443405 = 916277) (by norm_num)
theorem B3257873 : Blo 2171435 3257873 := bstep (se 2 (by rfl) ⟨1221702, by rfl⟩ : syracuseStep 3257873 = 2443405) B2443405
theorem B2171915 : Blo 2171435 2171915 := bstep (se 1 (by rfl) ⟨1628936, by rfl⟩ : syracuseStep 2171915 = 3257873) B3257873
theorem B7330229 : Blo 2171435 7330229 := bbase (se 5 (by rfl) ⟨343604, by rfl⟩ : syracuseStep 7330229 = 687209) (by norm_num)
theorem B4886819 : Blo 2171435 4886819 := bstep (se 1 (by rfl) ⟨3665114, by rfl⟩ : syracuseStep 4886819 = 7330229) B7330229
theorem B3257879 : Blo 2171435 3257879 := bstep (se 1 (by rfl) ⟨2443409, by rfl⟩ : syracuseStep 3257879 = 4886819) B4886819
theorem B2171919 : Blo 2171435 2171919 := bstep (se 1 (by rfl) ⟨1628939, by rfl⟩ : syracuseStep 2171919 = 3257879) B3257879
theorem B3257885 : Blo 2171435 3257885 := bbase (se 3 (by rfl) ⟨610853, by rfl⟩ : syracuseStep 3257885 = 1221707) (by norm_num)
theorem B2171923 : Blo 2171435 2171923 := bstep (se 1 (by rfl) ⟨1628942, by rfl⟩ : syracuseStep 2171923 = 3257885) B3257885
theorem B4886837 : Blo 2171435 4886837 := bbase (se 5 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 4886837 = 458141) (by norm_num)
theorem B3257891 : Blo 2171435 3257891 := bstep (se 1 (by rfl) ⟨2443418, by rfl⟩ : syracuseStep 3257891 = 4886837) B4886837
theorem B2171927 : Blo 2171435 2171927 := bstep (se 1 (by rfl) ⟨1628945, by rfl⟩ : syracuseStep 2171927 = 3257891) B3257891
theorem B4236557 : Blo 2171435 4236557 := bbase (se 3 (by rfl) ⟨794354, by rfl⟩ : syracuseStep 4236557 = 1588709) (by norm_num)
theorem B11297485 : Blo 2171435 11297485 := bstep (se 3 (by rfl) ⟨2118278, by rfl⟩ : syracuseStep 11297485 = 4236557) B4236557
theorem B60253253 : Blo 2171435 60253253 := bstep (se 4 (by rfl) ⟨5648742, by rfl⟩ : syracuseStep 60253253 = 11297485) B11297485
theorem B40168835 : Blo 2171435 40168835 := bstep (se 1 (by rfl) ⟨30126626, by rfl⟩ : syracuseStep 40168835 = 60253253) B60253253
theorem B26779223 : Blo 2171435 26779223 := bstep (se 1 (by rfl) ⟨20084417, by rfl⟩ : syracuseStep 26779223 = 40168835) B40168835
theorem B17852815 : Blo 2171435 17852815 := bstep (se 1 (by rfl) ⟨13389611, by rfl⟩ : syracuseStep 17852815 = 26779223) B26779223
theorem B23803753 : Blo 2171435 23803753 := bstep (se 2 (by rfl) ⟨8926407, by rfl⟩ : syracuseStep 23803753 = 17852815) B17852815
theorem B31738337 : Blo 2171435 31738337 := bstep (se 2 (by rfl) ⟨11901876, by rfl⟩ : syracuseStep 31738337 = 23803753) B23803753
theorem B21158891 : Blo 2171435 21158891 := bstep (se 1 (by rfl) ⟨15869168, by rfl⟩ : syracuseStep 21158891 = 31738337) B31738337
theorem B14105927 : Blo 2171435 14105927 := bstep (se 1 (by rfl) ⟨10579445, by rfl⟩ : syracuseStep 14105927 = 21158891) B21158891
theorem B9403951 : Blo 2171435 9403951 := bstep (se 1 (by rfl) ⟨7052963, by rfl⟩ : syracuseStep 9403951 = 14105927) B14105927
theorem B12538601 : Blo 2171435 12538601 := bstep (se 2 (by rfl) ⟨4701975, by rfl⟩ : syracuseStep 12538601 = 9403951) B9403951
theorem B8359067 : Blo 2171435 8359067 := bstep (se 1 (by rfl) ⟨6269300, by rfl⟩ : syracuseStep 8359067 = 12538601) B12538601
theorem B5572711 : Blo 2171435 5572711 := bstep (se 1 (by rfl) ⟨4179533, by rfl⟩ : syracuseStep 5572711 = 8359067) B8359067
theorem B29721125 : Blo 2171435 29721125 := bstep (se 4 (by rfl) ⟨2786355, by rfl⟩ : syracuseStep 29721125 = 5572711) B5572711
theorem B79256333 : Blo 2171435 79256333 := bstep (se 3 (by rfl) ⟨14860562, by rfl⟩ : syracuseStep 79256333 = 29721125) B29721125
theorem B52837555 : Blo 2171435 52837555 := bstep (se 1 (by rfl) ⟨39628166, by rfl⟩ : syracuseStep 52837555 = 79256333) B79256333
theorem B70450073 : Blo 2171435 70450073 := bstep (se 2 (by rfl) ⟨26418777, by rfl⟩ : syracuseStep 70450073 = 52837555) B52837555
theorem B46966715 : Blo 2171435 46966715 := bstep (se 1 (by rfl) ⟨35225036, by rfl⟩ : syracuseStep 46966715 = 70450073) B70450073
theorem B31311143 : Blo 2171435 31311143 := bstep (se 1 (by rfl) ⟨23483357, by rfl⟩ : syracuseStep 31311143 = 46966715) B46966715
theorem B20874095 : Blo 2171435 20874095 := bstep (se 1 (by rfl) ⟨15655571, by rfl⟩ : syracuseStep 20874095 = 31311143) B31311143
theorem B13916063 : Blo 2171435 13916063 := bstep (se 1 (by rfl) ⟨10437047, by rfl⟩ : syracuseStep 13916063 = 20874095) B20874095
theorem B9277375 : Blo 2171435 9277375 := bstep (se 1 (by rfl) ⟨6958031, by rfl⟩ : syracuseStep 9277375 = 13916063) B13916063
theorem B12369833 : Blo 2171435 12369833 := bstep (se 2 (by rfl) ⟨4638687, by rfl⟩ : syracuseStep 12369833 = 9277375) B9277375
theorem B8246555 : Blo 2171435 8246555 := bstep (se 1 (by rfl) ⟨6184916, by rfl⟩ : syracuseStep 8246555 = 12369833) B12369833
theorem B5497703 : Blo 2171435 5497703 := bstep (se 1 (by rfl) ⟨4123277, by rfl⟩ : syracuseStep 5497703 = 8246555) B8246555
theorem B3665135 : Blo 2171435 3665135 := bstep (se 1 (by rfl) ⟨2748851, by rfl⟩ : syracuseStep 3665135 = 5497703) B5497703
theorem B2443423 : Blo 2171435 2443423 := bstep (se 1 (by rfl) ⟨1832567, by rfl⟩ : syracuseStep 2443423 = 3665135) B3665135
theorem B3257897 : Blo 2171435 3257897 := bstep (se 2 (by rfl) ⟨1221711, by rfl⟩ : syracuseStep 3257897 = 2443423) B2443423
theorem B2171931 : Blo 2171435 2171931 := bstep (se 1 (by rfl) ⟨1628948, by rfl⟩ : syracuseStep 2171931 = 3257897) B3257897
theorem B2476765 : Blo 2171435 2476765 := bbase (se 3 (by rfl) ⟨464393, by rfl⟩ : syracuseStep 2476765 = 928787) (by norm_num)
theorem B3302353 : Blo 2171435 3302353 := bstep (se 2 (by rfl) ⟨1238382, by rfl⟩ : syracuseStep 3302353 = 2476765) B2476765
theorem B17612549 : Blo 2171435 17612549 := bstep (se 4 (by rfl) ⟨1651176, by rfl⟩ : syracuseStep 17612549 = 3302353) B3302353
theorem B11741699 : Blo 2171435 11741699 := bstep (se 1 (by rfl) ⟨8806274, by rfl⟩ : syracuseStep 11741699 = 17612549) B17612549
theorem B31311197 : Blo 2171435 31311197 := bstep (se 3 (by rfl) ⟨5870849, by rfl⟩ : syracuseStep 31311197 = 11741699) B11741699
theorem B20874131 : Blo 2171435 20874131 := bstep (se 1 (by rfl) ⟨15655598, by rfl⟩ : syracuseStep 20874131 = 31311197) B31311197
theorem B13916087 : Blo 2171435 13916087 := bstep (se 1 (by rfl) ⟨10437065, by rfl⟩ : syracuseStep 13916087 = 20874131) B20874131
theorem B9277391 : Blo 2171435 9277391 := bstep (se 1 (by rfl) ⟨6958043, by rfl⟩ : syracuseStep 9277391 = 13916087) B13916087
theorem B6184927 : Blo 2171435 6184927 := bstep (se 1 (by rfl) ⟨4638695, by rfl⟩ : syracuseStep 6184927 = 9277391) B9277391
theorem B8246569 : Blo 2171435 8246569 := bstep (se 2 (by rfl) ⟨3092463, by rfl⟩ : syracuseStep 8246569 = 6184927) B6184927
theorem B10995425 : Blo 2171435 10995425 := bstep (se 2 (by rfl) ⟨4123284, by rfl⟩ : syracuseStep 10995425 = 8246569) B8246569
theorem B7330283 : Blo 2171435 7330283 := bstep (se 1 (by rfl) ⟨5497712, by rfl⟩ : syracuseStep 7330283 = 10995425) B10995425
theorem B4886855 : Blo 2171435 4886855 := bstep (se 1 (by rfl) ⟨3665141, by rfl⟩ : syracuseStep 4886855 = 7330283) B7330283
theorem B3257903 : Blo 2171435 3257903 := bstep (se 1 (by rfl) ⟨2443427, by rfl⟩ : syracuseStep 3257903 = 4886855) B4886855
theorem B2171935 : Blo 2171435 2171935 := bstep (se 1 (by rfl) ⟨1628951, by rfl⟩ : syracuseStep 2171935 = 3257903) B3257903
theorem B3257909 : Blo 2171435 3257909 := bbase (se 5 (by rfl) ⟨152714, by rfl⟩ : syracuseStep 3257909 = 305429) (by norm_num)
theorem B2171939 : Blo 2171435 2171939 := bstep (se 1 (by rfl) ⟨1628954, by rfl⟩ : syracuseStep 2171939 = 3257909) B3257909
theorem B5497733 : Blo 2171435 5497733 := bbase (se 4 (by rfl) ⟨515412, by rfl⟩ : syracuseStep 5497733 = 1030825) (by norm_num)
theorem B3665155 : Blo 2171435 3665155 := bstep (se 1 (by rfl) ⟨2748866, by rfl⟩ : syracuseStep 3665155 = 5497733) B5497733
theorem B4886873 : Blo 2171435 4886873 := bstep (se 2 (by rfl) ⟨1832577, by rfl⟩ : syracuseStep 4886873 = 3665155) B3665155
theorem B3257915 : Blo 2171435 3257915 := bstep (se 1 (by rfl) ⟨2443436, by rfl⟩ : syracuseStep 3257915 = 4886873) B4886873
theorem B2171943 : Blo 2171435 2171943 := bstep (se 1 (by rfl) ⟨1628957, by rfl⟩ : syracuseStep 2171943 = 3257915) B3257915
theorem B2443441 : Blo 2171435 2443441 := bbase (se 2 (by rfl) ⟨916290, by rfl⟩ : syracuseStep 2443441 = 1832581) (by norm_num)
theorem B3257921 : Blo 2171435 3257921 := bstep (se 2 (by rfl) ⟨1221720, by rfl⟩ : syracuseStep 3257921 = 2443441) B2443441
theorem B2171947 : Blo 2171435 2171947 := bstep (se 1 (by rfl) ⟨1628960, by rfl⟩ : syracuseStep 2171947 = 3257921) B3257921
theorem B2319365 : Blo 2171435 2319365 := bbase (se 4 (by rfl) ⟨217440, by rfl⟩ : syracuseStep 2319365 = 434881) (by norm_num)
theorem B6184973 : Blo 2171435 6184973 := bstep (se 3 (by rfl) ⟨1159682, by rfl⟩ : syracuseStep 6184973 = 2319365) B2319365
theorem B4123315 : Blo 2171435 4123315 := bstep (se 1 (by rfl) ⟨3092486, by rfl⟩ : syracuseStep 4123315 = 6184973) B6184973
theorem B5497753 : Blo 2171435 5497753 := bstep (se 2 (by rfl) ⟨2061657, by rfl⟩ : syracuseStep 5497753 = 4123315) B4123315
theorem B7330337 : Blo 2171435 7330337 := bstep (se 2 (by rfl) ⟨2748876, by rfl⟩ : syracuseStep 7330337 = 5497753) B5497753
theorem B4886891 : Blo 2171435 4886891 := bstep (se 1 (by rfl) ⟨3665168, by rfl⟩ : syracuseStep 4886891 = 7330337) B7330337
theorem B3257927 : Blo 2171435 3257927 := bstep (se 1 (by rfl) ⟨2443445, by rfl⟩ : syracuseStep 3257927 = 4886891) B4886891
theorem B2171951 : Blo 2171435 2171951 := bstep (se 1 (by rfl) ⟨1628963, by rfl⟩ : syracuseStep 2171951 = 3257927) B3257927
theorem B3257933 : Blo 2171435 3257933 := bbase (se 3 (by rfl) ⟨610862, by rfl⟩ : syracuseStep 3257933 = 1221725) (by norm_num)
theorem B2171955 : Blo 2171435 2171955 := bstep (se 1 (by rfl) ⟨1628966, by rfl⟩ : syracuseStep 2171955 = 3257933) B3257933
theorem B4886909 : Blo 2171435 4886909 := bbase (se 3 (by rfl) ⟨916295, by rfl⟩ : syracuseStep 4886909 = 1832591) (by norm_num)
theorem B3257939 : Blo 2171435 3257939 := bstep (se 1 (by rfl) ⟨2443454, by rfl⟩ : syracuseStep 3257939 = 4886909) B4886909
theorem B2171959 : Blo 2171435 2171959 := bstep (se 1 (by rfl) ⟨1628969, by rfl⟩ : syracuseStep 2171959 = 3257939) B3257939
theorem B3665189 : Blo 2171435 3665189 := bbase (se 4 (by rfl) ⟨343611, by rfl⟩ : syracuseStep 3665189 = 687223) (by norm_num)
theorem B2443459 : Blo 2171435 2443459 := bstep (se 1 (by rfl) ⟨1832594, by rfl⟩ : syracuseStep 2443459 = 3665189) B3665189
theorem B3257945 : Blo 2171435 3257945 := bstep (se 2 (by rfl) ⟨1221729, by rfl⟩ : syracuseStep 3257945 = 2443459) B2443459
theorem B2171963 : Blo 2171435 2171963 := bstep (se 1 (by rfl) ⟨1628972, by rfl⟩ : syracuseStep 2171963 = 3257945) B3257945
theorem B3092509 : Blo 2171435 3092509 := bbase (se 3 (by rfl) ⟨579845, by rfl⟩ : syracuseStep 3092509 = 1159691) (by norm_num)
theorem B16493381 : Blo 2171435 16493381 := bstep (se 4 (by rfl) ⟨1546254, by rfl⟩ : syracuseStep 16493381 = 3092509) B3092509
theorem B10995587 : Blo 2171435 10995587 := bstep (se 1 (by rfl) ⟨8246690, by rfl⟩ : syracuseStep 10995587 = 16493381) B16493381
theorem B7330391 : Blo 2171435 7330391 := bstep (se 1 (by rfl) ⟨5497793, by rfl⟩ : syracuseStep 7330391 = 10995587) B10995587
theorem B4886927 : Blo 2171435 4886927 := bstep (se 1 (by rfl) ⟨3665195, by rfl⟩ : syracuseStep 4886927 = 7330391) B7330391
theorem B3257951 : Blo 2171435 3257951 := bstep (se 1 (by rfl) ⟨2443463, by rfl⟩ : syracuseStep 3257951 = 4886927) B4886927
theorem B2171967 : Blo 2171435 2171967 := bstep (se 1 (by rfl) ⟨1628975, by rfl⟩ : syracuseStep 2171967 = 3257951) B3257951
theorem B3257957 : Blo 2171435 3257957 := bbase (se 4 (by rfl) ⟨305433, by rfl⟩ : syracuseStep 3257957 = 610867) (by norm_num)
theorem B2171971 : Blo 2171435 2171971 := bstep (se 1 (by rfl) ⟨1628978, by rfl⟩ : syracuseStep 2171971 = 3257957) B3257957
theorem B28212437 : Blo 2171435 28212437 := bbase (se 7 (by rfl) ⟨330614, by rfl⟩ : syracuseStep 28212437 = 661229) (by norm_num)
theorem B18808291 : Blo 2171435 18808291 := bstep (se 1 (by rfl) ⟨14106218, by rfl⟩ : syracuseStep 18808291 = 28212437) B28212437
theorem B25077721 : Blo 2171435 25077721 := bstep (se 2 (by rfl) ⟨9404145, by rfl⟩ : syracuseStep 25077721 = 18808291) B18808291
theorem B33436961 : Blo 2171435 33436961 := bstep (se 2 (by rfl) ⟨12538860, by rfl⟩ : syracuseStep 33436961 = 25077721) B25077721
theorem B22291307 : Blo 2171435 22291307 := bstep (se 1 (by rfl) ⟨16718480, by rfl⟩ : syracuseStep 22291307 = 33436961) B33436961
theorem B14860871 : Blo 2171435 14860871 := bstep (se 1 (by rfl) ⟨11145653, by rfl⟩ : syracuseStep 14860871 = 22291307) B22291307
theorem B9907247 : Blo 2171435 9907247 := bstep (se 1 (by rfl) ⟨7430435, by rfl⟩ : syracuseStep 9907247 = 14860871) B14860871
theorem B6604831 : Blo 2171435 6604831 := bstep (se 1 (by rfl) ⟨4953623, by rfl⟩ : syracuseStep 6604831 = 9907247) B9907247
theorem B8806441 : Blo 2171435 8806441 := bstep (se 2 (by rfl) ⟨3302415, by rfl⟩ : syracuseStep 8806441 = 6604831) B6604831
theorem B11741921 : Blo 2171435 11741921 := bstep (se 2 (by rfl) ⟨4403220, by rfl⟩ : syracuseStep 11741921 = 8806441) B8806441
theorem B7827947 : Blo 2171435 7827947 := bstep (se 1 (by rfl) ⟨5870960, by rfl⟩ : syracuseStep 7827947 = 11741921) B11741921
theorem B5218631 : Blo 2171435 5218631 := bstep (se 1 (by rfl) ⟨3913973, by rfl⟩ : syracuseStep 5218631 = 7827947) B7827947
theorem B3479087 : Blo 2171435 3479087 := bstep (se 1 (by rfl) ⟨2609315, by rfl⟩ : syracuseStep 3479087 = 5218631) B5218631
theorem B2319391 : Blo 2171435 2319391 := bstep (se 1 (by rfl) ⟨1739543, by rfl⟩ : syracuseStep 2319391 = 3479087) B3479087
theorem B3092521 : Blo 2171435 3092521 := bstep (se 2 (by rfl) ⟨1159695, by rfl⟩ : syracuseStep 3092521 = 2319391) B2319391
theorem B4123361 : Blo 2171435 4123361 := bstep (se 2 (by rfl) ⟨1546260, by rfl⟩ : syracuseStep 4123361 = 3092521) B3092521
theorem B2748907 : Blo 2171435 2748907 := bstep (se 1 (by rfl) ⟨2061680, by rfl⟩ : syracuseStep 2748907 = 4123361) B4123361
theorem B3665209 : Blo 2171435 3665209 := bstep (se 2 (by rfl) ⟨1374453, by rfl⟩ : syracuseStep 3665209 = 2748907) B2748907
theorem B4886945 : Blo 2171435 4886945 := bstep (se 2 (by rfl) ⟨1832604, by rfl⟩ : syracuseStep 4886945 = 3665209) B3665209
theorem B3257963 : Blo 2171435 3257963 := bstep (se 1 (by rfl) ⟨2443472, by rfl⟩ : syracuseStep 3257963 = 4886945) B4886945
theorem B2171975 : Blo 2171435 2171975 := bstep (se 1 (by rfl) ⟨1628981, by rfl⟩ : syracuseStep 2171975 = 3257963) B3257963
theorem B2443477 : Blo 2171435 2443477 := bbase (se 7 (by rfl) ⟨28634, by rfl⟩ : syracuseStep 2443477 = 57269) (by norm_num)
theorem B3257969 : Blo 2171435 3257969 := bstep (se 2 (by rfl) ⟨1221738, by rfl⟩ : syracuseStep 3257969 = 2443477) B2443477
theorem B2171979 : Blo 2171435 2171979 := bstep (se 1 (by rfl) ⟨1628984, by rfl⟩ : syracuseStep 2171979 = 3257969) B3257969
theorem B2748917 : Blo 2171435 2748917 := bbase (se 5 (by rfl) ⟨128855, by rfl⟩ : syracuseStep 2748917 = 257711) (by norm_num)
theorem B7330445 : Blo 2171435 7330445 := bstep (se 3 (by rfl) ⟨1374458, by rfl⟩ : syracuseStep 7330445 = 2748917) B2748917
theorem B4886963 : Blo 2171435 4886963 := bstep (se 1 (by rfl) ⟨3665222, by rfl⟩ : syracuseStep 4886963 = 7330445) B7330445
theorem B3257975 : Blo 2171435 3257975 := bstep (se 1 (by rfl) ⟨2443481, by rfl⟩ : syracuseStep 3257975 = 4886963) B4886963
theorem B2171983 : Blo 2171435 2171983 := bstep (se 1 (by rfl) ⟨1628987, by rfl⟩ : syracuseStep 2171983 = 3257975) B3257975
theorem B3257981 : Blo 2171435 3257981 := bbase (se 3 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 3257981 = 1221743) (by norm_num)
theorem B2171987 : Blo 2171435 2171987 := bstep (se 1 (by rfl) ⟨1628990, by rfl⟩ : syracuseStep 2171987 = 3257981) B3257981
theorem B4886981 : Blo 2171435 4886981 := bbase (se 4 (by rfl) ⟨458154, by rfl⟩ : syracuseStep 4886981 = 916309) (by norm_num)
theorem B3257987 : Blo 2171435 3257987 := bstep (se 1 (by rfl) ⟨2443490, by rfl⟩ : syracuseStep 3257987 = 4886981) B4886981
theorem B2171991 : Blo 2171435 2171991 := bstep (se 1 (by rfl) ⟨1628993, by rfl⟩ : syracuseStep 2171991 = 3257987) B3257987
theorem B4403261 : Blo 2171435 4403261 := bbase (se 3 (by rfl) ⟨825611, by rfl⟩ : syracuseStep 4403261 = 1651223) (by norm_num)
theorem B2935507 : Blo 2171435 2935507 := bstep (se 1 (by rfl) ⟨2201630, by rfl⟩ : syracuseStep 2935507 = 4403261) B4403261
theorem B3914009 : Blo 2171435 3914009 := bstep (se 2 (by rfl) ⟨1467753, by rfl⟩ : syracuseStep 3914009 = 2935507) B2935507
theorem B2609339 : Blo 2171435 2609339 := bstep (se 1 (by rfl) ⟨1957004, by rfl⟩ : syracuseStep 2609339 = 3914009) B3914009
theorem B6958237 : Blo 2171435 6958237 := bstep (se 3 (by rfl) ⟨1304669, by rfl⟩ : syracuseStep 6958237 = 2609339) B2609339
theorem B9277649 : Blo 2171435 9277649 := bstep (se 2 (by rfl) ⟨3479118, by rfl⟩ : syracuseStep 9277649 = 6958237) B6958237
theorem B6185099 : Blo 2171435 6185099 := bstep (se 1 (by rfl) ⟨4638824, by rfl⟩ : syracuseStep 6185099 = 9277649) B9277649
theorem B4123399 : Blo 2171435 4123399 := bstep (se 1 (by rfl) ⟨3092549, by rfl⟩ : syracuseStep 4123399 = 6185099) B6185099
theorem B5497865 : Blo 2171435 5497865 := bstep (se 2 (by rfl) ⟨2061699, by rfl⟩ : syracuseStep 5497865 = 4123399) B4123399
theorem B3665243 : Blo 2171435 3665243 := bstep (se 1 (by rfl) ⟨2748932, by rfl⟩ : syracuseStep 3665243 = 5497865) B5497865
theorem B2443495 : Blo 2171435 2443495 := bstep (se 1 (by rfl) ⟨1832621, by rfl⟩ : syracuseStep 2443495 = 3665243) B3665243
theorem B3257993 : Blo 2171435 3257993 := bstep (se 2 (by rfl) ⟨1221747, by rfl⟩ : syracuseStep 3257993 = 2443495) B2443495
theorem B2171995 : Blo 2171435 2171995 := bstep (se 1 (by rfl) ⟨1628996, by rfl⟩ : syracuseStep 2171995 = 3257993) B3257993
theorem B10995749 : Blo 2171435 10995749 := bbase (se 4 (by rfl) ⟨1030851, by rfl⟩ : syracuseStep 10995749 = 2061703) (by norm_num)
theorem B7330499 : Blo 2171435 7330499 := bstep (se 1 (by rfl) ⟨5497874, by rfl⟩ : syracuseStep 7330499 = 10995749) B10995749
theorem B4886999 : Blo 2171435 4886999 := bstep (se 1 (by rfl) ⟨3665249, by rfl⟩ : syracuseStep 4886999 = 7330499) B7330499
theorem B3257999 : Blo 2171435 3257999 := bstep (se 1 (by rfl) ⟨2443499, by rfl⟩ : syracuseStep 3257999 = 4886999) B4886999
theorem B2171999 : Blo 2171435 2171999 := bstep (se 1 (by rfl) ⟨1628999, by rfl⟩ : syracuseStep 2171999 = 3257999) B3257999
theorem B3258005 : Blo 2171435 3258005 := bbase (se 6 (by rfl) ⟨76359, by rfl⟩ : syracuseStep 3258005 = 152719) (by norm_num)
theorem B2172003 : Blo 2171435 2172003 := bstep (se 1 (by rfl) ⟨1629002, by rfl⟩ : syracuseStep 2172003 = 3258005) B3258005
theorem B2609353 : Blo 2171435 2609353 := bbase (se 2 (by rfl) ⟨978507, by rfl⟩ : syracuseStep 2609353 = 1957015) (by norm_num)
theorem B13916549 : Blo 2171435 13916549 := bstep (se 4 (by rfl) ⟨1304676, by rfl⟩ : syracuseStep 13916549 = 2609353) B2609353
theorem B9277699 : Blo 2171435 9277699 := bstep (se 1 (by rfl) ⟨6958274, by rfl⟩ : syracuseStep 9277699 = 13916549) B13916549
theorem B12370265 : Blo 2171435 12370265 := bstep (se 2 (by rfl) ⟨4638849, by rfl⟩ : syracuseStep 12370265 = 9277699) B9277699
theorem B8246843 : Blo 2171435 8246843 := bstep (se 1 (by rfl) ⟨6185132, by rfl⟩ : syracuseStep 8246843 = 12370265) B12370265
theorem B5497895 : Blo 2171435 5497895 := bstep (se 1 (by rfl) ⟨4123421, by rfl⟩ : syracuseStep 5497895 = 8246843) B8246843
theorem B3665263 : Blo 2171435 3665263 := bstep (se 1 (by rfl) ⟨2748947, by rfl⟩ : syracuseStep 3665263 = 5497895) B5497895
theorem B4887017 : Blo 2171435 4887017 := bstep (se 2 (by rfl) ⟨1832631, by rfl⟩ : syracuseStep 4887017 = 3665263) B3665263
theorem B3258011 : Blo 2171435 3258011 := bstep (se 1 (by rfl) ⟨2443508, by rfl⟩ : syracuseStep 3258011 = 4887017) B4887017
theorem B2172007 : Blo 2171435 2172007 := bstep (se 1 (by rfl) ⟨1629005, by rfl⟩ : syracuseStep 2172007 = 3258011) B3258011
theorem B2443513 : Blo 2171435 2443513 := bbase (se 2 (by rfl) ⟨916317, by rfl⟩ : syracuseStep 2443513 = 1832635) (by norm_num)
theorem B3258017 : Blo 2171435 3258017 := bstep (se 2 (by rfl) ⟨1221756, by rfl⟩ : syracuseStep 3258017 = 2443513) B2443513
theorem B2172011 : Blo 2171435 2172011 := bstep (se 1 (by rfl) ⟨1629008, by rfl⟩ : syracuseStep 2172011 = 3258017) B3258017
theorem B9277733 : Blo 2171435 9277733 := bbase (se 4 (by rfl) ⟨869787, by rfl⟩ : syracuseStep 9277733 = 1739575) (by norm_num)
theorem B6185155 : Blo 2171435 6185155 := bstep (se 1 (by rfl) ⟨4638866, by rfl⟩ : syracuseStep 6185155 = 9277733) B9277733
theorem B8246873 : Blo 2171435 8246873 := bstep (se 2 (by rfl) ⟨3092577, by rfl⟩ : syracuseStep 8246873 = 6185155) B6185155
theorem B5497915 : Blo 2171435 5497915 := bstep (se 1 (by rfl) ⟨4123436, by rfl⟩ : syracuseStep 5497915 = 8246873) B8246873
theorem B7330553 : Blo 2171435 7330553 := bstep (se 2 (by rfl) ⟨2748957, by rfl⟩ : syracuseStep 7330553 = 5497915) B5497915
theorem B4887035 : Blo 2171435 4887035 := bstep (se 1 (by rfl) ⟨3665276, by rfl⟩ : syracuseStep 4887035 = 7330553) B7330553
theorem B3258023 : Blo 2171435 3258023 := bstep (se 1 (by rfl) ⟨2443517, by rfl⟩ : syracuseStep 3258023 = 4887035) B4887035
theorem B2172015 : Blo 2171435 2172015 := bstep (se 1 (by rfl) ⟨1629011, by rfl⟩ : syracuseStep 2172015 = 3258023) B3258023
theorem B3258029 : Blo 2171435 3258029 := bbase (se 3 (by rfl) ⟨610880, by rfl⟩ : syracuseStep 3258029 = 1221761) (by norm_num)
theorem B2172019 : Blo 2171435 2172019 := bstep (se 1 (by rfl) ⟨1629014, by rfl⟩ : syracuseStep 2172019 = 3258029) B3258029
theorem B4887053 : Blo 2171435 4887053 := bbase (se 3 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 4887053 = 1832645) (by norm_num)
theorem B3258035 : Blo 2171435 3258035 := bstep (se 1 (by rfl) ⟨2443526, by rfl⟩ : syracuseStep 3258035 = 4887053) B4887053
theorem B2172023 : Blo 2171435 2172023 := bstep (se 1 (by rfl) ⟨1629017, by rfl⟩ : syracuseStep 2172023 = 3258035) B3258035
theorem B2748973 : Blo 2171435 2748973 := bbase (se 3 (by rfl) ⟨515432, by rfl⟩ : syracuseStep 2748973 = 1030865) (by norm_num)
theorem B3665297 : Blo 2171435 3665297 := bstep (se 2 (by rfl) ⟨1374486, by rfl⟩ : syracuseStep 3665297 = 2748973) B2748973
theorem B2443531 : Blo 2171435 2443531 := bstep (se 1 (by rfl) ⟨1832648, by rfl⟩ : syracuseStep 2443531 = 3665297) B3665297
theorem B3258041 : Blo 2171435 3258041 := bstep (se 2 (by rfl) ⟨1221765, by rfl⟩ : syracuseStep 3258041 = 2443531) B2443531
theorem B2172027 : Blo 2171435 2172027 := bstep (se 1 (by rfl) ⟨1629020, by rfl⟩ : syracuseStep 2172027 = 3258041) B3258041
theorem B5871109 : Blo 2171435 5871109 := bbase (se 4 (by rfl) ⟨550416, by rfl⟩ : syracuseStep 5871109 = 1100833) (by norm_num)
theorem B7828145 : Blo 2171435 7828145 := bstep (se 2 (by rfl) ⟨2935554, by rfl⟩ : syracuseStep 7828145 = 5871109) B5871109
theorem B5218763 : Blo 2171435 5218763 := bstep (se 1 (by rfl) ⟨3914072, by rfl⟩ : syracuseStep 5218763 = 7828145) B7828145
theorem B13916701 : Blo 2171435 13916701 := bstep (se 3 (by rfl) ⟨2609381, by rfl⟩ : syracuseStep 13916701 = 5218763) B5218763
theorem B18555601 : Blo 2171435 18555601 := bstep (se 2 (by rfl) ⟨6958350, by rfl⟩ : syracuseStep 18555601 = 13916701) B13916701
theorem B24740801 : Blo 2171435 24740801 := bstep (se 2 (by rfl) ⟨9277800, by rfl⟩ : syracuseStep 24740801 = 18555601) B18555601
theorem B16493867 : Blo 2171435 16493867 := bstep (se 1 (by rfl) ⟨12370400, by rfl⟩ : syracuseStep 16493867 = 24740801) B24740801
theorem B10995911 : Blo 2171435 10995911 := bstep (se 1 (by rfl) ⟨8246933, by rfl⟩ : syracuseStep 10995911 = 16493867) B16493867
theorem B7330607 : Blo 2171435 7330607 := bstep (se 1 (by rfl) ⟨5497955, by rfl⟩ : syracuseStep 7330607 = 10995911) B10995911
theorem B4887071 : Blo 2171435 4887071 := bstep (se 1 (by rfl) ⟨3665303, by rfl⟩ : syracuseStep 4887071 = 7330607) B7330607
theorem B3258047 : Blo 2171435 3258047 := bstep (se 1 (by rfl) ⟨2443535, by rfl⟩ : syracuseStep 3258047 = 4887071) B4887071
theorem B2172031 : Blo 2171435 2172031 := bstep (se 1 (by rfl) ⟨1629023, by rfl⟩ : syracuseStep 2172031 = 3258047) B3258047
theorem B3258053 : Blo 2171435 3258053 := bbase (se 4 (by rfl) ⟨305442, by rfl⟩ : syracuseStep 3258053 = 610885) (by norm_num)
theorem B2172035 : Blo 2171435 2172035 := bstep (se 1 (by rfl) ⟨1629026, by rfl⟩ : syracuseStep 2172035 = 3258053) B3258053
theorem B3665317 : Blo 2171435 3665317 := bbase (se 4 (by rfl) ⟨343623, by rfl⟩ : syracuseStep 3665317 = 687247) (by norm_num)
theorem B4887089 : Blo 2171435 4887089 := bstep (se 2 (by rfl) ⟨1832658, by rfl⟩ : syracuseStep 4887089 = 3665317) B3665317
theorem B3258059 : Blo 2171435 3258059 := bstep (se 1 (by rfl) ⟨2443544, by rfl⟩ : syracuseStep 3258059 = 4887089) B4887089
theorem B2172039 : Blo 2171435 2172039 := bstep (se 1 (by rfl) ⟨1629029, by rfl⟩ : syracuseStep 2172039 = 3258059) B3258059
theorem B2443549 : Blo 2171435 2443549 := bbase (se 3 (by rfl) ⟨458165, by rfl⟩ : syracuseStep 2443549 = 916331) (by norm_num)
theorem B3258065 : Blo 2171435 3258065 := bstep (se 2 (by rfl) ⟨1221774, by rfl⟩ : syracuseStep 3258065 = 2443549) B2443549
theorem B2172043 : Blo 2171435 2172043 := bstep (se 1 (by rfl) ⟨1629032, by rfl⟩ : syracuseStep 2172043 = 3258065) B3258065
theorem B7330661 : Blo 2171435 7330661 := bbase (se 4 (by rfl) ⟨687249, by rfl⟩ : syracuseStep 7330661 = 1374499) (by norm_num)
theorem B4887107 : Blo 2171435 4887107 := bstep (se 1 (by rfl) ⟨3665330, by rfl⟩ : syracuseStep 4887107 = 7330661) B7330661
theorem B3258071 : Blo 2171435 3258071 := bstep (se 1 (by rfl) ⟨2443553, by rfl⟩ : syracuseStep 3258071 = 4887107) B4887107
theorem B2172047 : Blo 2171435 2172047 := bstep (se 1 (by rfl) ⟨1629035, by rfl⟩ : syracuseStep 2172047 = 3258071) B3258071
theorem B3258077 : Blo 2171435 3258077 := bbase (se 3 (by rfl) ⟨610889, by rfl⟩ : syracuseStep 3258077 = 1221779) (by norm_num)
theorem B2172051 : Blo 2171435 2172051 := bstep (se 1 (by rfl) ⟨1629038, by rfl⟩ : syracuseStep 2172051 = 3258077) B3258077
theorem B4887125 : Blo 2171435 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B3258083 : Blo 2171435 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B2172055 : Blo 2171435 2172055 := bstep (se 1 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 2172055 = 3258083) B3258083
theorem B3479221 : Blo 2171435 3479221 := bbase (se 5 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 3479221 = 326177) (by norm_num)
theorem B4638961 : Blo 2171435 4638961 := bstep (se 2 (by rfl) ⟨1739610, by rfl⟩ : syracuseStep 4638961 = 3479221) B3479221
theorem B6185281 : Blo 2171435 6185281 := bstep (se 2 (by rfl) ⟨2319480, by rfl⟩ : syracuseStep 6185281 = 4638961) B4638961
theorem B8247041 : Blo 2171435 8247041 := bstep (se 2 (by rfl) ⟨3092640, by rfl⟩ : syracuseStep 8247041 = 6185281) B6185281
theorem B5498027 : Blo 2171435 5498027 := bstep (se 1 (by rfl) ⟨4123520, by rfl⟩ : syracuseStep 5498027 = 8247041) B8247041
theorem B3665351 : Blo 2171435 3665351 := bstep (se 1 (by rfl) ⟨2749013, by rfl⟩ : syracuseStep 3665351 = 5498027) B5498027
theorem B2443567 : Blo 2171435 2443567 := bstep (se 1 (by rfl) ⟨1832675, by rfl⟩ : syracuseStep 2443567 = 3665351) B3665351
theorem B3258089 : Blo 2171435 3258089 := bstep (se 2 (by rfl) ⟨1221783, by rfl⟩ : syracuseStep 3258089 = 2443567) B2443567
theorem B2172059 : Blo 2171435 2172059 := bstep (se 1 (by rfl) ⟨1629044, by rfl⟩ : syracuseStep 2172059 = 3258089) B3258089
theorem B27833813 : Blo 2171435 27833813 := bbase (se 7 (by rfl) ⟨326177, by rfl⟩ : syracuseStep 27833813 = 652355) (by norm_num)
theorem B18555875 : Blo 2171435 18555875 := bstep (se 1 (by rfl) ⟨13916906, by rfl⟩ : syracuseStep 18555875 = 27833813) B27833813
theorem B12370583 : Blo 2171435 12370583 := bstep (se 1 (by rfl) ⟨9277937, by rfl⟩ : syracuseStep 12370583 = 18555875) B18555875
theorem B8247055 : Blo 2171435 8247055 := bstep (se 1 (by rfl) ⟨6185291, by rfl⟩ : syracuseStep 8247055 = 12370583) B12370583
theorem B10996073 : Blo 2171435 10996073 := bstep (se 2 (by rfl) ⟨4123527, by rfl⟩ : syracuseStep 10996073 = 8247055) B8247055
theorem B7330715 : Blo 2171435 7330715 := bstep (se 1 (by rfl) ⟨5498036, by rfl⟩ : syracuseStep 7330715 = 10996073) B10996073
theorem B4887143 : Blo 2171435 4887143 := bstep (se 1 (by rfl) ⟨3665357, by rfl⟩ : syracuseStep 4887143 = 7330715) B7330715
theorem B3258095 : Blo 2171435 3258095 := bstep (se 1 (by rfl) ⟨2443571, by rfl⟩ : syracuseStep 3258095 = 4887143) B4887143
theorem B2172063 : Blo 2171435 2172063 := bstep (se 1 (by rfl) ⟨1629047, by rfl⟩ : syracuseStep 2172063 = 3258095) B3258095
theorem B3258101 : Blo 2171435 3258101 := bbase (se 5 (by rfl) ⟨152723, by rfl⟩ : syracuseStep 3258101 = 305447) (by norm_num)
theorem B2172067 : Blo 2171435 2172067 := bstep (se 1 (by rfl) ⟨1629050, by rfl⟩ : syracuseStep 2172067 = 3258101) B3258101
theorem B9277973 : Blo 2171435 9277973 := bbase (se 6 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 9277973 = 434905) (by norm_num)
theorem B6185315 : Blo 2171435 6185315 := bstep (se 1 (by rfl) ⟨4638986, by rfl⟩ : syracuseStep 6185315 = 9277973) B9277973
theorem B4123543 : Blo 2171435 4123543 := bstep (se 1 (by rfl) ⟨3092657, by rfl⟩ : syracuseStep 4123543 = 6185315) B6185315
theorem B5498057 : Blo 2171435 5498057 := bstep (se 2 (by rfl) ⟨2061771, by rfl⟩ : syracuseStep 5498057 = 4123543) B4123543
theorem B3665371 : Blo 2171435 3665371 := bstep (se 1 (by rfl) ⟨2749028, by rfl⟩ : syracuseStep 3665371 = 5498057) B5498057
theorem B4887161 : Blo 2171435 4887161 := bstep (se 2 (by rfl) ⟨1832685, by rfl⟩ : syracuseStep 4887161 = 3665371) B3665371
theorem B3258107 : Blo 2171435 3258107 := bstep (se 1 (by rfl) ⟨2443580, by rfl⟩ : syracuseStep 3258107 = 4887161) B4887161
theorem B2172071 : Blo 2171435 2172071 := bstep (se 1 (by rfl) ⟨1629053, by rfl⟩ : syracuseStep 2172071 = 3258107) B3258107
theorem B2443585 : Blo 2171435 2443585 := bbase (se 2 (by rfl) ⟨916344, by rfl⟩ : syracuseStep 2443585 = 1832689) (by norm_num)
theorem B3258113 : Blo 2171435 3258113 := bstep (se 2 (by rfl) ⟨1221792, by rfl⟩ : syracuseStep 3258113 = 2443585) B2443585
theorem B2172075 : Blo 2171435 2172075 := bstep (se 1 (by rfl) ⟨1629056, by rfl⟩ : syracuseStep 2172075 = 3258113) B3258113
theorem B5498077 : Blo 2171435 5498077 := bbase (se 3 (by rfl) ⟨1030889, by rfl⟩ : syracuseStep 5498077 = 2061779) (by norm_num)
theorem B7330769 : Blo 2171435 7330769 := bstep (se 2 (by rfl) ⟨2749038, by rfl⟩ : syracuseStep 7330769 = 5498077) B5498077
theorem B4887179 : Blo 2171435 4887179 := bstep (se 1 (by rfl) ⟨3665384, by rfl⟩ : syracuseStep 4887179 = 7330769) B7330769
theorem B3258119 : Blo 2171435 3258119 := bstep (se 1 (by rfl) ⟨2443589, by rfl⟩ : syracuseStep 3258119 = 4887179) B4887179
theorem B2172079 : Blo 2171435 2172079 := bstep (se 1 (by rfl) ⟨1629059, by rfl⟩ : syracuseStep 2172079 = 3258119) B3258119
theorem B3258125 : Blo 2171435 3258125 := bbase (se 3 (by rfl) ⟨610898, by rfl⟩ : syracuseStep 3258125 = 1221797) (by norm_num)
theorem B2172083 : Blo 2171435 2172083 := bstep (se 1 (by rfl) ⟨1629062, by rfl⟩ : syracuseStep 2172083 = 3258125) B3258125
theorem B4887197 : Blo 2171435 4887197 := bbase (se 3 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 4887197 = 1832699) (by norm_num)
theorem B3258131 : Blo 2171435 3258131 := bstep (se 1 (by rfl) ⟨2443598, by rfl⟩ : syracuseStep 3258131 = 4887197) B4887197
theorem B2172087 : Blo 2171435 2172087 := bstep (se 1 (by rfl) ⟨1629065, by rfl⟩ : syracuseStep 2172087 = 3258131) B3258131
theorem B3665405 : Blo 2171435 3665405 := bbase (se 3 (by rfl) ⟨687263, by rfl⟩ : syracuseStep 3665405 = 1374527) (by norm_num)
theorem B2443603 : Blo 2171435 2443603 := bstep (se 1 (by rfl) ⟨1832702, by rfl⟩ : syracuseStep 2443603 = 3665405) B3665405
theorem B3258137 : Blo 2171435 3258137 := bstep (se 2 (by rfl) ⟨1221801, by rfl⟩ : syracuseStep 3258137 = 2443603) B2443603
theorem B2172091 : Blo 2171435 2172091 := bstep (se 1 (by rfl) ⟨1629068, by rfl⟩ : syracuseStep 2172091 = 3258137) B3258137
theorem B4639037 : Blo 2171435 4639037 := bbase (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) (by norm_num)
theorem B12370765 : Blo 2171435 12370765 := bstep (se 3 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 12370765 = 4639037) B4639037
theorem B16494353 : Blo 2171435 16494353 := bstep (se 2 (by rfl) ⟨6185382, by rfl⟩ : syracuseStep 16494353 = 12370765) B12370765
theorem B10996235 : Blo 2171435 10996235 := bstep (se 1 (by rfl) ⟨8247176, by rfl⟩ : syracuseStep 10996235 = 16494353) B16494353
theorem B7330823 : Blo 2171435 7330823 := bstep (se 1 (by rfl) ⟨5498117, by rfl⟩ : syracuseStep 7330823 = 10996235) B10996235
theorem B4887215 : Blo 2171435 4887215 := bstep (se 1 (by rfl) ⟨3665411, by rfl⟩ : syracuseStep 4887215 = 7330823) B7330823
theorem B3258143 : Blo 2171435 3258143 := bstep (se 1 (by rfl) ⟨2443607, by rfl⟩ : syracuseStep 3258143 = 4887215) B4887215
theorem B2172095 : Blo 2171435 2172095 := bstep (se 1 (by rfl) ⟨1629071, by rfl⟩ : syracuseStep 2172095 = 3258143) B3258143
theorem B3258149 : Blo 2171435 3258149 := bbase (se 4 (by rfl) ⟨305451, by rfl⟩ : syracuseStep 3258149 = 610903) (by norm_num)
theorem B2172099 : Blo 2171435 2172099 := bstep (se 1 (by rfl) ⟨1629074, by rfl⟩ : syracuseStep 2172099 = 3258149) B3258149
theorem B2749069 : Blo 2171435 2749069 := bbase (se 3 (by rfl) ⟨515450, by rfl⟩ : syracuseStep 2749069 = 1030901) (by norm_num)
theorem B3665425 : Blo 2171435 3665425 := bstep (se 2 (by rfl) ⟨1374534, by rfl⟩ : syracuseStep 3665425 = 2749069) B2749069
theorem B4887233 : Blo 2171435 4887233 := bstep (se 2 (by rfl) ⟨1832712, by rfl⟩ : syracuseStep 4887233 = 3665425) B3665425
theorem B3258155 : Blo 2171435 3258155 := bstep (se 1 (by rfl) ⟨2443616, by rfl⟩ : syracuseStep 3258155 = 4887233) B4887233
theorem B2172103 : Blo 2171435 2172103 := bstep (se 1 (by rfl) ⟨1629077, by rfl⟩ : syracuseStep 2172103 = 3258155) B3258155
theorem B2443621 : Blo 2171435 2443621 := bbase (se 4 (by rfl) ⟨229089, by rfl⟩ : syracuseStep 2443621 = 458179) (by norm_num)
theorem B3258161 : Blo 2171435 3258161 := bstep (se 2 (by rfl) ⟨1221810, by rfl⟩ : syracuseStep 3258161 = 2443621) B2443621
theorem B2172107 : Blo 2171435 2172107 := bstep (se 1 (by rfl) ⟨1629080, by rfl⟩ : syracuseStep 2172107 = 3258161) B3258161
theorem B6185429 : Blo 2171435 6185429 := bbase (se 7 (by rfl) ⟨72485, by rfl⟩ : syracuseStep 6185429 = 144971) (by norm_num)
theorem B4123619 : Blo 2171435 4123619 := bstep (se 1 (by rfl) ⟨3092714, by rfl⟩ : syracuseStep 4123619 = 6185429) B6185429
theorem B2749079 : Blo 2171435 2749079 := bstep (se 1 (by rfl) ⟨2061809, by rfl⟩ : syracuseStep 2749079 = 4123619) B4123619
theorem B7330877 : Blo 2171435 7330877 := bstep (se 3 (by rfl) ⟨1374539, by rfl⟩ : syracuseStep 7330877 = 2749079) B2749079
theorem B4887251 : Blo 2171435 4887251 := bstep (se 1 (by rfl) ⟨3665438, by rfl⟩ : syracuseStep 4887251 = 7330877) B7330877
theorem B3258167 : Blo 2171435 3258167 := bstep (se 1 (by rfl) ⟨2443625, by rfl⟩ : syracuseStep 3258167 = 4887251) B4887251
theorem B2172111 : Blo 2171435 2172111 := bstep (se 1 (by rfl) ⟨1629083, by rfl⟩ : syracuseStep 2172111 = 3258167) B3258167
theorem B3258173 : Blo 2171435 3258173 := bbase (se 3 (by rfl) ⟨610907, by rfl⟩ : syracuseStep 3258173 = 1221815) (by norm_num)
theorem B2172115 : Blo 2171435 2172115 := bstep (se 1 (by rfl) ⟨1629086, by rfl⟩ : syracuseStep 2172115 = 3258173) B3258173
theorem B4887269 : Blo 2171435 4887269 := bbase (se 4 (by rfl) ⟨458181, by rfl⟩ : syracuseStep 4887269 = 916363) (by norm_num)
theorem B3258179 : Blo 2171435 3258179 := bstep (se 1 (by rfl) ⟨2443634, by rfl⟩ : syracuseStep 3258179 = 4887269) B4887269
theorem B2172119 : Blo 2171435 2172119 := bstep (se 1 (by rfl) ⟨1629089, by rfl⟩ : syracuseStep 2172119 = 3258179) B3258179
theorem B5498189 : Blo 2171435 5498189 := bbase (se 3 (by rfl) ⟨1030910, by rfl⟩ : syracuseStep 5498189 = 2061821) (by norm_num)
theorem B3665459 : Blo 2171435 3665459 := bstep (se 1 (by rfl) ⟨2749094, by rfl⟩ : syracuseStep 3665459 = 5498189) B5498189
theorem B2443639 : Blo 2171435 2443639 := bstep (se 1 (by rfl) ⟨1832729, by rfl⟩ : syracuseStep 2443639 = 3665459) B3665459
theorem B3258185 : Blo 2171435 3258185 := bstep (se 2 (by rfl) ⟨1221819, by rfl⟩ : syracuseStep 3258185 = 2443639) B2443639
theorem B2172123 : Blo 2171435 2172123 := bstep (se 1 (by rfl) ⟨1629092, by rfl⟩ : syracuseStep 2172123 = 3258185) B3258185
theorem B2319553 : Blo 2171435 2319553 := bbase (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) (by norm_num)
theorem B3092737 : Blo 2171435 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B4123649 : Blo 2171435 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B10996397 : Blo 2171435 10996397 := bstep (se 3 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 10996397 = 4123649) B4123649
theorem B7330931 : Blo 2171435 7330931 := bstep (se 1 (by rfl) ⟨5498198, by rfl⟩ : syracuseStep 7330931 = 10996397) B10996397
theorem B4887287 : Blo 2171435 4887287 := bstep (se 1 (by rfl) ⟨3665465, by rfl⟩ : syracuseStep 4887287 = 7330931) B7330931
theorem B3258191 : Blo 2171435 3258191 := bstep (se 1 (by rfl) ⟨2443643, by rfl⟩ : syracuseStep 3258191 = 4887287) B4887287
theorem B2172127 : Blo 2171435 2172127 := bstep (se 1 (by rfl) ⟨1629095, by rfl⟩ : syracuseStep 2172127 = 3258191) B3258191
theorem B3258197 : Blo 2171435 3258197 := bbase (se 9 (by rfl) ⟨9545, by rfl⟩ : syracuseStep 3258197 = 19091) (by norm_num)
theorem B2172131 : Blo 2171435 2172131 := bstep (se 1 (by rfl) ⟨1629098, by rfl⟩ : syracuseStep 2172131 = 3258197) B3258197
theorem B3914261 : Blo 2171435 3914261 := bbase (se 6 (by rfl) ⟨91740, by rfl⟩ : syracuseStep 3914261 = 183481) (by norm_num)
theorem B2609507 : Blo 2171435 2609507 := bstep (se 1 (by rfl) ⟨1957130, by rfl⟩ : syracuseStep 2609507 = 3914261) B3914261
theorem B6958685 : Blo 2171435 6958685 := bstep (se 3 (by rfl) ⟨1304753, by rfl⟩ : syracuseStep 6958685 = 2609507) B2609507
theorem B4639123 : Blo 2171435 4639123 := bstep (se 1 (by rfl) ⟨3479342, by rfl⟩ : syracuseStep 4639123 = 6958685) B6958685
theorem B6185497 : Blo 2171435 6185497 := bstep (se 2 (by rfl) ⟨2319561, by rfl⟩ : syracuseStep 6185497 = 4639123) B4639123
theorem B8247329 : Blo 2171435 8247329 := bstep (se 2 (by rfl) ⟨3092748, by rfl⟩ : syracuseStep 8247329 = 6185497) B6185497
theorem B5498219 : Blo 2171435 5498219 := bstep (se 1 (by rfl) ⟨4123664, by rfl⟩ : syracuseStep 5498219 = 8247329) B8247329
theorem B3665479 : Blo 2171435 3665479 := bstep (se 1 (by rfl) ⟨2749109, by rfl⟩ : syracuseStep 3665479 = 5498219) B5498219
theorem B4887305 : Blo 2171435 4887305 := bstep (se 2 (by rfl) ⟨1832739, by rfl⟩ : syracuseStep 4887305 = 3665479) B3665479
theorem B3258203 : Blo 2171435 3258203 := bstep (se 1 (by rfl) ⟨2443652, by rfl⟩ : syracuseStep 3258203 = 4887305) B4887305
theorem B2172135 : Blo 2171435 2172135 := bstep (se 1 (by rfl) ⟨1629101, by rfl⟩ : syracuseStep 2172135 = 3258203) B3258203
theorem B2443657 : Blo 2171435 2443657 := bbase (se 2 (by rfl) ⟨916371, by rfl⟩ : syracuseStep 2443657 = 1832743) (by norm_num)
theorem B3258209 : Blo 2171435 3258209 := bstep (se 2 (by rfl) ⟨1221828, by rfl⟩ : syracuseStep 3258209 = 2443657) B2443657
theorem B2172139 : Blo 2171435 2172139 := bstep (se 1 (by rfl) ⟨1629104, by rfl⟩ : syracuseStep 2172139 = 3258209) B3258209
theorem B8589557 : Blo 2171435 8589557 := bbase (se 5 (by rfl) ⟨402635, by rfl⟩ : syracuseStep 8589557 = 805271) (by norm_num)
theorem B5726371 : Blo 2171435 5726371 := bstep (se 1 (by rfl) ⟨4294778, by rfl⟩ : syracuseStep 5726371 = 8589557) B8589557
theorem B7635161 : Blo 2171435 7635161 := bstep (se 2 (by rfl) ⟨2863185, by rfl⟩ : syracuseStep 7635161 = 5726371) B5726371
theorem B20360429 : Blo 2171435 20360429 := bstep (se 3 (by rfl) ⟨3817580, by rfl⟩ : syracuseStep 20360429 = 7635161) B7635161
theorem B13573619 : Blo 2171435 13573619 := bstep (se 1 (by rfl) ⟨10180214, by rfl⟩ : syracuseStep 13573619 = 20360429) B20360429
theorem B9049079 : Blo 2171435 9049079 := bstep (se 1 (by rfl) ⟨6786809, by rfl⟩ : syracuseStep 9049079 = 13573619) B13573619
theorem B6032719 : Blo 2171435 6032719 := bstep (se 1 (by rfl) ⟨4524539, by rfl⟩ : syracuseStep 6032719 = 9049079) B9049079
theorem B8043625 : Blo 2171435 8043625 := bstep (se 2 (by rfl) ⟨3016359, by rfl⟩ : syracuseStep 8043625 = 6032719) B6032719
theorem B10724833 : Blo 2171435 10724833 := bstep (se 2 (by rfl) ⟨4021812, by rfl⟩ : syracuseStep 10724833 = 8043625) B8043625
theorem B14299777 : Blo 2171435 14299777 := bstep (se 2 (by rfl) ⟨5362416, by rfl⟩ : syracuseStep 14299777 = 10724833) B10724833
theorem B19066369 : Blo 2171435 19066369 := bstep (se 2 (by rfl) ⟨7149888, by rfl⟩ : syracuseStep 19066369 = 14299777) B14299777
theorem B25421825 : Blo 2171435 25421825 := bstep (se 2 (by rfl) ⟨9533184, by rfl⟩ : syracuseStep 25421825 = 19066369) B19066369
theorem B16947883 : Blo 2171435 16947883 := bstep (se 1 (by rfl) ⟨12710912, by rfl⟩ : syracuseStep 16947883 = 25421825) B25421825
theorem B22597177 : Blo 2171435 22597177 := bstep (se 2 (by rfl) ⟨8473941, by rfl⟩ : syracuseStep 22597177 = 16947883) B16947883
theorem B30129569 : Blo 2171435 30129569 := bstep (se 2 (by rfl) ⟨11298588, by rfl⟩ : syracuseStep 30129569 = 22597177) B22597177
theorem B20086379 : Blo 2171435 20086379 := bstep (se 1 (by rfl) ⟨15064784, by rfl⟩ : syracuseStep 20086379 = 30129569) B30129569
theorem B13390919 : Blo 2171435 13390919 := bstep (se 1 (by rfl) ⟨10043189, by rfl⟩ : syracuseStep 13390919 = 20086379) B20086379
theorem B8927279 : Blo 2171435 8927279 := bstep (se 1 (by rfl) ⟨6695459, by rfl⟩ : syracuseStep 8927279 = 13390919) B13390919
theorem B5951519 : Blo 2171435 5951519 := bstep (se 1 (by rfl) ⟨4463639, by rfl⟩ : syracuseStep 5951519 = 8927279) B8927279
theorem B3967679 : Blo 2171435 3967679 := bstep (se 1 (by rfl) ⟨2975759, by rfl⟩ : syracuseStep 3967679 = 5951519) B5951519
theorem B2645119 : Blo 2171435 2645119 := bstep (se 1 (by rfl) ⟨1983839, by rfl⟩ : syracuseStep 2645119 = 3967679) B3967679
theorem B14107301 : Blo 2171435 14107301 := bstep (se 4 (by rfl) ⟨1322559, by rfl⟩ : syracuseStep 14107301 = 2645119) B2645119
theorem B9404867 : Blo 2171435 9404867 := bstep (se 1 (by rfl) ⟨7053650, by rfl⟩ : syracuseStep 9404867 = 14107301) B14107301
theorem B25079645 : Blo 2171435 25079645 := bstep (se 3 (by rfl) ⟨4702433, by rfl⟩ : syracuseStep 25079645 = 9404867) B9404867
theorem B66879053 : Blo 2171435 66879053 := bstep (se 3 (by rfl) ⟨12539822, by rfl⟩ : syracuseStep 66879053 = 25079645) B25079645
theorem B44586035 : Blo 2171435 44586035 := bstep (se 1 (by rfl) ⟨33439526, by rfl⟩ : syracuseStep 44586035 = 66879053) B66879053
theorem B29724023 : Blo 2171435 29724023 := bstep (se 1 (by rfl) ⟨22293017, by rfl⟩ : syracuseStep 29724023 = 44586035) B44586035
theorem B19816015 : Blo 2171435 19816015 := bstep (se 1 (by rfl) ⟨14862011, by rfl⟩ : syracuseStep 19816015 = 29724023) B29724023
theorem B26421353 : Blo 2171435 26421353 := bstep (se 2 (by rfl) ⟨9908007, by rfl⟩ : syracuseStep 26421353 = 19816015) B19816015
theorem B17614235 : Blo 2171435 17614235 := bstep (se 1 (by rfl) ⟨13210676, by rfl⟩ : syracuseStep 17614235 = 26421353) B26421353
theorem B11742823 : Blo 2171435 11742823 := bstep (se 1 (by rfl) ⟨8807117, by rfl⟩ : syracuseStep 11742823 = 17614235) B17614235
theorem B62628389 : Blo 2171435 62628389 := bstep (se 4 (by rfl) ⟨5871411, by rfl⟩ : syracuseStep 62628389 = 11742823) B11742823
theorem B41752259 : Blo 2171435 41752259 := bstep (se 1 (by rfl) ⟨31314194, by rfl⟩ : syracuseStep 41752259 = 62628389) B62628389
theorem B27834839 : Blo 2171435 27834839 := bstep (se 1 (by rfl) ⟨20876129, by rfl⟩ : syracuseStep 27834839 = 41752259) B41752259
theorem B18556559 : Blo 2171435 18556559 := bstep (se 1 (by rfl) ⟨13917419, by rfl⟩ : syracuseStep 18556559 = 27834839) B27834839
theorem B12371039 : Blo 2171435 12371039 := bstep (se 1 (by rfl) ⟨9278279, by rfl⟩ : syracuseStep 12371039 = 18556559) B18556559
theorem B8247359 : Blo 2171435 8247359 := bstep (se 1 (by rfl) ⟨6185519, by rfl⟩ : syracuseStep 8247359 = 12371039) B12371039
theorem B5498239 : Blo 2171435 5498239 := bstep (se 1 (by rfl) ⟨4123679, by rfl⟩ : syracuseStep 5498239 = 8247359) B8247359
theorem B7330985 : Blo 2171435 7330985 := bstep (se 2 (by rfl) ⟨2749119, by rfl⟩ : syracuseStep 7330985 = 5498239) B5498239
theorem B4887323 : Blo 2171435 4887323 := bstep (se 1 (by rfl) ⟨3665492, by rfl⟩ : syracuseStep 4887323 = 7330985) B7330985
theorem B3258215 : Blo 2171435 3258215 := bstep (se 1 (by rfl) ⟨2443661, by rfl⟩ : syracuseStep 3258215 = 4887323) B4887323
theorem B2172143 : Blo 2171435 2172143 := bstep (se 1 (by rfl) ⟨1629107, by rfl⟩ : syracuseStep 2172143 = 3258215) B3258215
theorem B3258221 : Blo 2171435 3258221 := bbase (se 3 (by rfl) ⟨610916, by rfl⟩ : syracuseStep 3258221 = 1221833) (by norm_num)
theorem B2172147 : Blo 2171435 2172147 := bstep (se 1 (by rfl) ⟨1629110, by rfl⟩ : syracuseStep 2172147 = 3258221) B3258221
theorem B4887341 : Blo 2171435 4887341 := bbase (se 3 (by rfl) ⟨916376, by rfl⟩ : syracuseStep 4887341 = 1832753) (by norm_num)
theorem B3258227 : Blo 2171435 3258227 := bstep (se 1 (by rfl) ⟨2443670, by rfl⟩ : syracuseStep 3258227 = 4887341) B4887341
theorem B2172151 : Blo 2171435 2172151 := bstep (se 1 (by rfl) ⟨1629113, by rfl⟩ : syracuseStep 2172151 = 3258227) B3258227
theorem B2477017 : Blo 2171435 2477017 := bbase (se 2 (by rfl) ⟨928881, by rfl⟩ : syracuseStep 2477017 = 1857763) (by norm_num)
theorem B3302689 : Blo 2171435 3302689 := bstep (se 2 (by rfl) ⟨1238508, by rfl⟩ : syracuseStep 3302689 = 2477017) B2477017
theorem B4403585 : Blo 2171435 4403585 := bstep (se 2 (by rfl) ⟨1651344, by rfl⟩ : syracuseStep 4403585 = 3302689) B3302689
theorem B11742893 : Blo 2171435 11742893 := bstep (se 3 (by rfl) ⟨2201792, by rfl⟩ : syracuseStep 11742893 = 4403585) B4403585
theorem B7828595 : Blo 2171435 7828595 := bstep (se 1 (by rfl) ⟨5871446, by rfl⟩ : syracuseStep 7828595 = 11742893) B11742893
theorem B5219063 : Blo 2171435 5219063 := bstep (se 1 (by rfl) ⟨3914297, by rfl⟩ : syracuseStep 5219063 = 7828595) B7828595
theorem B3479375 : Blo 2171435 3479375 := bstep (se 1 (by rfl) ⟨2609531, by rfl⟩ : syracuseStep 3479375 = 5219063) B5219063
theorem B9278333 : Blo 2171435 9278333 := bstep (se 3 (by rfl) ⟨1739687, by rfl⟩ : syracuseStep 9278333 = 3479375) B3479375
theorem B6185555 : Blo 2171435 6185555 := bstep (se 1 (by rfl) ⟨4639166, by rfl⟩ : syracuseStep 6185555 = 9278333) B9278333
theorem B4123703 : Blo 2171435 4123703 := bstep (se 1 (by rfl) ⟨3092777, by rfl⟩ : syracuseStep 4123703 = 6185555) B6185555
theorem B2749135 : Blo 2171435 2749135 := bstep (se 1 (by rfl) ⟨2061851, by rfl⟩ : syracuseStep 2749135 = 4123703) B4123703
theorem B3665513 : Blo 2171435 3665513 := bstep (se 2 (by rfl) ⟨1374567, by rfl⟩ : syracuseStep 3665513 = 2749135) B2749135
theorem B2443675 : Blo 2171435 2443675 := bstep (se 1 (by rfl) ⟨1832756, by rfl⟩ : syracuseStep 2443675 = 3665513) B3665513
theorem B3258233 : Blo 2171435 3258233 := bstep (se 2 (by rfl) ⟨1221837, by rfl⟩ : syracuseStep 3258233 = 2443675) B2443675
theorem B2172155 : Blo 2171435 2172155 := bstep (se 1 (by rfl) ⟨1629116, by rfl⟩ : syracuseStep 2172155 = 3258233) B3258233
theorem B29724245 : Blo 2171435 29724245 := bbase (se 8 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 29724245 = 348331) (by norm_num)
theorem B19816163 : Blo 2171435 19816163 := bstep (se 1 (by rfl) ⟨14862122, by rfl⟩ : syracuseStep 19816163 = 29724245) B29724245
theorem B13210775 : Blo 2171435 13210775 := bstep (se 1 (by rfl) ⟨9908081, by rfl⟩ : syracuseStep 13210775 = 19816163) B19816163
theorem B8807183 : Blo 2171435 8807183 := bstep (se 1 (by rfl) ⟨6605387, by rfl⟩ : syracuseStep 8807183 = 13210775) B13210775
theorem B5871455 : Blo 2171435 5871455 := bstep (se 1 (by rfl) ⟨4403591, by rfl⟩ : syracuseStep 5871455 = 8807183) B8807183
theorem B3914303 : Blo 2171435 3914303 := bstep (se 1 (by rfl) ⟨2935727, by rfl⟩ : syracuseStep 3914303 = 5871455) B5871455
theorem B10438141 : Blo 2171435 10438141 := bstep (se 3 (by rfl) ⟨1957151, by rfl⟩ : syracuseStep 10438141 = 3914303) B3914303
theorem B13917521 : Blo 2171435 13917521 := bstep (se 2 (by rfl) ⟨5219070, by rfl⟩ : syracuseStep 13917521 = 10438141) B10438141
theorem B37113389 : Blo 2171435 37113389 := bstep (se 3 (by rfl) ⟨6958760, by rfl⟩ : syracuseStep 37113389 = 13917521) B13917521
theorem B24742259 : Blo 2171435 24742259 := bstep (se 1 (by rfl) ⟨18556694, by rfl⟩ : syracuseStep 24742259 = 37113389) B37113389
theorem B16494839 : Blo 2171435 16494839 := bstep (se 1 (by rfl) ⟨12371129, by rfl⟩ : syracuseStep 16494839 = 24742259) B24742259
theorem B10996559 : Blo 2171435 10996559 := bstep (se 1 (by rfl) ⟨8247419, by rfl⟩ : syracuseStep 10996559 = 16494839) B16494839
theorem B7331039 : Blo 2171435 7331039 := bstep (se 1 (by rfl) ⟨5498279, by rfl⟩ : syracuseStep 7331039 = 10996559) B10996559
theorem B4887359 : Blo 2171435 4887359 := bstep (se 1 (by rfl) ⟨3665519, by rfl⟩ : syracuseStep 4887359 = 7331039) B7331039
theorem B3258239 : Blo 2171435 3258239 := bstep (se 1 (by rfl) ⟨2443679, by rfl⟩ : syracuseStep 3258239 = 4887359) B4887359
theorem B2172159 : Blo 2171435 2172159 := bstep (se 1 (by rfl) ⟨1629119, by rfl⟩ : syracuseStep 2172159 = 3258239) B3258239
theorem B3258245 : Blo 2171435 3258245 := bbase (se 4 (by rfl) ⟨305460, by rfl⟩ : syracuseStep 3258245 = 610921) (by norm_num)
theorem B2172163 : Blo 2171435 2172163 := bstep (se 1 (by rfl) ⟨1629122, by rfl⟩ : syracuseStep 2172163 = 3258245) B3258245
theorem B3665533 : Blo 2171435 3665533 := bbase (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) (by norm_num)
theorem B4887377 : Blo 2171435 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B3258251 : Blo 2171435 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B2172167 : Blo 2171435 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B2443693 : Blo 2171435 2443693 := bbase (se 3 (by rfl) ⟨458192, by rfl⟩ : syracuseStep 2443693 = 916385) (by norm_num)
theorem B3258257 : Blo 2171435 3258257 := bstep (se 2 (by rfl) ⟨1221846, by rfl⟩ : syracuseStep 3258257 = 2443693) B2443693
theorem B2172171 : Blo 2171435 2172171 := bstep (se 1 (by rfl) ⟨1629128, by rfl⟩ : syracuseStep 2172171 = 3258257) B3258257
theorem B7331093 : Blo 2171435 7331093 := bbase (se 6 (by rfl) ⟨171822, by rfl⟩ : syracuseStep 7331093 = 343645) (by norm_num)
theorem B4887395 : Blo 2171435 4887395 := bstep (se 1 (by rfl) ⟨3665546, by rfl⟩ : syracuseStep 4887395 = 7331093) B7331093
theorem B3258263 : Blo 2171435 3258263 := bstep (se 1 (by rfl) ⟨2443697, by rfl⟩ : syracuseStep 3258263 = 4887395) B4887395
theorem B2172175 : Blo 2171435 2172175 := bstep (se 1 (by rfl) ⟨1629131, by rfl⟩ : syracuseStep 2172175 = 3258263) B3258263
theorem B3258269 : Blo 2171435 3258269 := bbase (se 3 (by rfl) ⟨610925, by rfl⟩ : syracuseStep 3258269 = 1221851) (by norm_num)
theorem B2172179 : Blo 2171435 2172179 := bstep (se 1 (by rfl) ⟨1629134, by rfl⟩ : syracuseStep 2172179 = 3258269) B3258269
theorem B4887413 : Blo 2171435 4887413 := bbase (se 5 (by rfl) ⟨229097, by rfl⟩ : syracuseStep 4887413 = 458195) (by norm_num)
theorem B3258275 : Blo 2171435 3258275 := bstep (se 1 (by rfl) ⟨2443706, by rfl⟩ : syracuseStep 3258275 = 4887413) B4887413
theorem B2172183 : Blo 2171435 2172183 := bstep (se 1 (by rfl) ⟨1629137, by rfl⟩ : syracuseStep 2172183 = 3258275) B3258275
theorem B7053797 : Blo 2171435 7053797 := bbase (se 4 (by rfl) ⟨661293, by rfl⟩ : syracuseStep 7053797 = 1322587) (by norm_num)
theorem B4702531 : Blo 2171435 4702531 := bstep (se 1 (by rfl) ⟨3526898, by rfl⟩ : syracuseStep 4702531 = 7053797) B7053797
theorem B6270041 : Blo 2171435 6270041 := bstep (se 2 (by rfl) ⟨2351265, by rfl⟩ : syracuseStep 6270041 = 4702531) B4702531
theorem B4180027 : Blo 2171435 4180027 := bstep (se 1 (by rfl) ⟨3135020, by rfl⟩ : syracuseStep 4180027 = 6270041) B6270041
theorem B5573369 : Blo 2171435 5573369 := bstep (se 2 (by rfl) ⟨2090013, by rfl⟩ : syracuseStep 5573369 = 4180027) B4180027
theorem B3715579 : Blo 2171435 3715579 := bstep (se 1 (by rfl) ⟨2786684, by rfl⟩ : syracuseStep 3715579 = 5573369) B5573369
theorem B4954105 : Blo 2171435 4954105 := bstep (se 2 (by rfl) ⟨1857789, by rfl⟩ : syracuseStep 4954105 = 3715579) B3715579
theorem B6605473 : Blo 2171435 6605473 := bstep (se 2 (by rfl) ⟨2477052, by rfl⟩ : syracuseStep 6605473 = 4954105) B4954105
theorem B8807297 : Blo 2171435 8807297 := bstep (se 2 (by rfl) ⟨3302736, by rfl⟩ : syracuseStep 8807297 = 6605473) B6605473
theorem B23486125 : Blo 2171435 23486125 := bstep (se 3 (by rfl) ⟨4403648, by rfl⟩ : syracuseStep 23486125 = 8807297) B8807297
theorem B31314833 : Blo 2171435 31314833 := bstep (se 2 (by rfl) ⟨11743062, by rfl⟩ : syracuseStep 31314833 = 23486125) B23486125
theorem B20876555 : Blo 2171435 20876555 := bstep (se 1 (by rfl) ⟨15657416, by rfl⟩ : syracuseStep 20876555 = 31314833) B31314833
theorem B13917703 : Blo 2171435 13917703 := bstep (se 1 (by rfl) ⟨10438277, by rfl⟩ : syracuseStep 13917703 = 20876555) B20876555
theorem B18556937 : Blo 2171435 18556937 := bstep (se 2 (by rfl) ⟨6958851, by rfl⟩ : syracuseStep 18556937 = 13917703) B13917703
theorem B12371291 : Blo 2171435 12371291 := bstep (se 1 (by rfl) ⟨9278468, by rfl⟩ : syracuseStep 12371291 = 18556937) B18556937
theorem B8247527 : Blo 2171435 8247527 := bstep (se 1 (by rfl) ⟨6185645, by rfl⟩ : syracuseStep 8247527 = 12371291) B12371291
theorem B5498351 : Blo 2171435 5498351 := bstep (se 1 (by rfl) ⟨4123763, by rfl⟩ : syracuseStep 5498351 = 8247527) B8247527
theorem B3665567 : Blo 2171435 3665567 := bstep (se 1 (by rfl) ⟨2749175, by rfl⟩ : syracuseStep 3665567 = 5498351) B5498351
theorem B2443711 : Blo 2171435 2443711 := bstep (se 1 (by rfl) ⟨1832783, by rfl⟩ : syracuseStep 2443711 = 3665567) B3665567
theorem B3258281 : Blo 2171435 3258281 := bstep (se 2 (by rfl) ⟨1221855, by rfl⟩ : syracuseStep 3258281 = 2443711) B2443711
theorem B2172187 : Blo 2171435 2172187 := bstep (se 1 (by rfl) ⟨1629140, by rfl⟩ : syracuseStep 2172187 = 3258281) B3258281
theorem B8247541 : Blo 2171435 8247541 := bbase (se 5 (by rfl) ⟨386603, by rfl⟩ : syracuseStep 8247541 = 773207) (by norm_num)
theorem B10996721 : Blo 2171435 10996721 := bstep (se 2 (by rfl) ⟨4123770, by rfl⟩ : syracuseStep 10996721 = 8247541) B8247541
theorem B7331147 : Blo 2171435 7331147 := bstep (se 1 (by rfl) ⟨5498360, by rfl⟩ : syracuseStep 7331147 = 10996721) B10996721
theorem B4887431 : Blo 2171435 4887431 := bstep (se 1 (by rfl) ⟨3665573, by rfl⟩ : syracuseStep 4887431 = 7331147) B7331147
theorem B3258287 : Blo 2171435 3258287 := bstep (se 1 (by rfl) ⟨2443715, by rfl⟩ : syracuseStep 3258287 = 4887431) B4887431
theorem B2172191 : Blo 2171435 2172191 := bstep (se 1 (by rfl) ⟨1629143, by rfl⟩ : syracuseStep 2172191 = 3258287) B3258287
theorem B3258293 : Blo 2171435 3258293 := bbase (se 5 (by rfl) ⟨152732, by rfl⟩ : syracuseStep 3258293 = 305465) (by norm_num)
theorem B2172195 : Blo 2171435 2172195 := bstep (se 1 (by rfl) ⟨1629146, by rfl⟩ : syracuseStep 2172195 = 3258293) B3258293
theorem B5498381 : Blo 2171435 5498381 := bbase (se 3 (by rfl) ⟨1030946, by rfl⟩ : syracuseStep 5498381 = 2061893) (by norm_num)
theorem B3665587 : Blo 2171435 3665587 := bstep (se 1 (by rfl) ⟨2749190, by rfl⟩ : syracuseStep 3665587 = 5498381) B5498381
theorem B4887449 : Blo 2171435 4887449 := bstep (se 2 (by rfl) ⟨1832793, by rfl⟩ : syracuseStep 4887449 = 3665587) B3665587
theorem B3258299 : Blo 2171435 3258299 := bstep (se 1 (by rfl) ⟨2443724, by rfl⟩ : syracuseStep 3258299 = 4887449) B4887449
theorem B2172199 : Blo 2171435 2172199 := bstep (se 1 (by rfl) ⟨1629149, by rfl⟩ : syracuseStep 2172199 = 3258299) B3258299
theorem B2443729 : Blo 2171435 2443729 := bbase (se 2 (by rfl) ⟨916398, by rfl⟩ : syracuseStep 2443729 = 1832797) (by norm_num)
theorem B3258305 : Blo 2171435 3258305 := bstep (se 2 (by rfl) ⟨1221864, by rfl⟩ : syracuseStep 3258305 = 2443729) B2443729
theorem B2172203 : Blo 2171435 2172203 := bstep (se 1 (by rfl) ⟨1629152, by rfl⟩ : syracuseStep 2172203 = 3258305) B3258305
theorem B4639277 : Blo 2171435 4639277 := bbase (se 3 (by rfl) ⟨869864, by rfl⟩ : syracuseStep 4639277 = 1739729) (by norm_num)
theorem B3092851 : Blo 2171435 3092851 := bstep (se 1 (by rfl) ⟨2319638, by rfl⟩ : syracuseStep 3092851 = 4639277) B4639277
theorem B4123801 : Blo 2171435 4123801 := bstep (se 2 (by rfl) ⟨1546425, by rfl⟩ : syracuseStep 4123801 = 3092851) B3092851
theorem B5498401 : Blo 2171435 5498401 := bstep (se 2 (by rfl) ⟨2061900, by rfl⟩ : syracuseStep 5498401 = 4123801) B4123801
theorem B7331201 : Blo 2171435 7331201 := bstep (se 2 (by rfl) ⟨2749200, by rfl⟩ : syracuseStep 7331201 = 5498401) B5498401
theorem B4887467 : Blo 2171435 4887467 := bstep (se 1 (by rfl) ⟨3665600, by rfl⟩ : syracuseStep 4887467 = 7331201) B7331201
theorem B3258311 : Blo 2171435 3258311 := bstep (se 1 (by rfl) ⟨2443733, by rfl⟩ : syracuseStep 3258311 = 4887467) B4887467
theorem B2172207 : Blo 2171435 2172207 := bstep (se 1 (by rfl) ⟨1629155, by rfl⟩ : syracuseStep 2172207 = 3258311) B3258311
theorem B3258317 : Blo 2171435 3258317 := bbase (se 3 (by rfl) ⟨610934, by rfl⟩ : syracuseStep 3258317 = 1221869) (by norm_num)
theorem B2172211 : Blo 2171435 2172211 := bstep (se 1 (by rfl) ⟨1629158, by rfl⟩ : syracuseStep 2172211 = 3258317) B3258317
theorem B4887485 : Blo 2171435 4887485 := bbase (se 3 (by rfl) ⟨916403, by rfl⟩ : syracuseStep 4887485 = 1832807) (by norm_num)
theorem B3258323 : Blo 2171435 3258323 := bstep (se 1 (by rfl) ⟨2443742, by rfl⟩ : syracuseStep 3258323 = 4887485) B4887485
theorem B2172215 : Blo 2171435 2172215 := bstep (se 1 (by rfl) ⟨1629161, by rfl⟩ : syracuseStep 2172215 = 3258323) B3258323
theorem B3665621 : Blo 2171435 3665621 := bbase (se 7 (by rfl) ⟨42956, by rfl⟩ : syracuseStep 3665621 = 85913) (by norm_num)
theorem B2443747 : Blo 2171435 2443747 := bstep (se 1 (by rfl) ⟨1832810, by rfl⟩ : syracuseStep 2443747 = 3665621) B3665621
theorem B3258329 : Blo 2171435 3258329 := bstep (se 2 (by rfl) ⟨1221873, by rfl⟩ : syracuseStep 3258329 = 2443747) B2443747
theorem B2172219 : Blo 2171435 2172219 := bstep (se 1 (by rfl) ⟨1629164, by rfl⟩ : syracuseStep 2172219 = 3258329) B3258329
theorem B2201861 : Blo 2171435 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B5871629 : Blo 2171435 5871629 := bstep (se 3 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 5871629 = 2201861) B2201861
theorem B3914419 : Blo 2171435 3914419 := bstep (se 1 (by rfl) ⟨2935814, by rfl⟩ : syracuseStep 3914419 = 5871629) B5871629
theorem B5219225 : Blo 2171435 5219225 := bstep (se 2 (by rfl) ⟨1957209, by rfl⟩ : syracuseStep 5219225 = 3914419) B3914419
theorem B3479483 : Blo 2171435 3479483 := bstep (se 1 (by rfl) ⟨2609612, by rfl⟩ : syracuseStep 3479483 = 5219225) B5219225
theorem B9278621 : Blo 2171435 9278621 := bstep (se 3 (by rfl) ⟨1739741, by rfl⟩ : syracuseStep 9278621 = 3479483) B3479483
theorem B6185747 : Blo 2171435 6185747 := bstep (se 1 (by rfl) ⟨4639310, by rfl⟩ : syracuseStep 6185747 = 9278621) B9278621
theorem B16495325 : Blo 2171435 16495325 := bstep (se 3 (by rfl) ⟨3092873, by rfl⟩ : syracuseStep 16495325 = 6185747) B6185747
theorem B10996883 : Blo 2171435 10996883 := bstep (se 1 (by rfl) ⟨8247662, by rfl⟩ : syracuseStep 10996883 = 16495325) B16495325
theorem B7331255 : Blo 2171435 7331255 := bstep (se 1 (by rfl) ⟨5498441, by rfl⟩ : syracuseStep 7331255 = 10996883) B10996883
theorem B4887503 : Blo 2171435 4887503 := bstep (se 1 (by rfl) ⟨3665627, by rfl⟩ : syracuseStep 4887503 = 7331255) B7331255
theorem B3258335 : Blo 2171435 3258335 := bstep (se 1 (by rfl) ⟨2443751, by rfl⟩ : syracuseStep 3258335 = 4887503) B4887503
theorem B2172223 : Blo 2171435 2172223 := bstep (se 1 (by rfl) ⟨1629167, by rfl⟩ : syracuseStep 2172223 = 3258335) B3258335
theorem B3258341 : Blo 2171435 3258341 := bbase (se 4 (by rfl) ⟨305469, by rfl⟩ : syracuseStep 3258341 = 610939) (by norm_num)
theorem B2172227 : Blo 2171435 2172227 := bstep (se 1 (by rfl) ⟨1629170, by rfl⟩ : syracuseStep 2172227 = 3258341) B3258341
theorem B5219245 : Blo 2171435 5219245 := bbase (se 3 (by rfl) ⟨978608, by rfl⟩ : syracuseStep 5219245 = 1957217) (by norm_num)
theorem B6958993 : Blo 2171435 6958993 := bstep (se 2 (by rfl) ⟨2609622, by rfl⟩ : syracuseStep 6958993 = 5219245) B5219245
theorem B9278657 : Blo 2171435 9278657 := bstep (se 2 (by rfl) ⟨3479496, by rfl⟩ : syracuseStep 9278657 = 6958993) B6958993
theorem B6185771 : Blo 2171435 6185771 := bstep (se 1 (by rfl) ⟨4639328, by rfl⟩ : syracuseStep 6185771 = 9278657) B9278657
theorem B4123847 : Blo 2171435 4123847 := bstep (se 1 (by rfl) ⟨3092885, by rfl⟩ : syracuseStep 4123847 = 6185771) B6185771
theorem B2749231 : Blo 2171435 2749231 := bstep (se 1 (by rfl) ⟨2061923, by rfl⟩ : syracuseStep 2749231 = 4123847) B4123847
theorem B3665641 : Blo 2171435 3665641 := bstep (se 2 (by rfl) ⟨1374615, by rfl⟩ : syracuseStep 3665641 = 2749231) B2749231
theorem B4887521 : Blo 2171435 4887521 := bstep (se 2 (by rfl) ⟨1832820, by rfl⟩ : syracuseStep 4887521 = 3665641) B3665641
theorem B3258347 : Blo 2171435 3258347 := bstep (se 1 (by rfl) ⟨2443760, by rfl⟩ : syracuseStep 3258347 = 4887521) B4887521
theorem B2172231 : Blo 2171435 2172231 := bstep (se 1 (by rfl) ⟨1629173, by rfl⟩ : syracuseStep 2172231 = 3258347) B3258347
theorem B2443765 : Blo 2171435 2443765 := bbase (se 5 (by rfl) ⟨114551, by rfl⟩ : syracuseStep 2443765 = 229103) (by norm_num)
theorem B3258353 : Blo 2171435 3258353 := bstep (se 2 (by rfl) ⟨1221882, by rfl⟩ : syracuseStep 3258353 = 2443765) B2443765
theorem B2172235 : Blo 2171435 2172235 := bstep (se 1 (by rfl) ⟨1629176, by rfl⟩ : syracuseStep 2172235 = 3258353) B3258353
theorem B2749241 : Blo 2171435 2749241 := bbase (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) (by norm_num)
theorem B7331309 : Blo 2171435 7331309 := bstep (se 3 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 7331309 = 2749241) B2749241
theorem B4887539 : Blo 2171435 4887539 := bstep (se 1 (by rfl) ⟨3665654, by rfl⟩ : syracuseStep 4887539 = 7331309) B7331309
theorem B3258359 : Blo 2171435 3258359 := bstep (se 1 (by rfl) ⟨2443769, by rfl⟩ : syracuseStep 3258359 = 4887539) B4887539
theorem B2172239 : Blo 2171435 2172239 := bstep (se 1 (by rfl) ⟨1629179, by rfl⟩ : syracuseStep 2172239 = 3258359) B3258359
theorem B3258365 : Blo 2171435 3258365 := bbase (se 3 (by rfl) ⟨610943, by rfl⟩ : syracuseStep 3258365 = 1221887) (by norm_num)
theorem B2172243 : Blo 2171435 2172243 := bstep (se 1 (by rfl) ⟨1629182, by rfl⟩ : syracuseStep 2172243 = 3258365) B3258365
theorem B4887557 : Blo 2171435 4887557 := bbase (se 4 (by rfl) ⟨458208, by rfl⟩ : syracuseStep 4887557 = 916417) (by norm_num)
theorem B3258371 : Blo 2171435 3258371 := bstep (se 1 (by rfl) ⟨2443778, by rfl⟩ : syracuseStep 3258371 = 4887557) B4887557
theorem B2172247 : Blo 2171435 2172247 := bstep (se 1 (by rfl) ⟨1629185, by rfl⟩ : syracuseStep 2172247 = 3258371) B3258371
theorem B4123885 : Blo 2171435 4123885 := bbase (se 3 (by rfl) ⟨773228, by rfl⟩ : syracuseStep 4123885 = 1546457) (by norm_num)
theorem B5498513 : Blo 2171435 5498513 := bstep (se 2 (by rfl) ⟨2061942, by rfl⟩ : syracuseStep 5498513 = 4123885) B4123885
theorem B3665675 : Blo 2171435 3665675 := bstep (se 1 (by rfl) ⟨2749256, by rfl⟩ : syracuseStep 3665675 = 5498513) B5498513
theorem B2443783 : Blo 2171435 2443783 := bstep (se 1 (by rfl) ⟨1832837, by rfl⟩ : syracuseStep 2443783 = 3665675) B3665675
theorem B3258377 : Blo 2171435 3258377 := bstep (se 2 (by rfl) ⟨1221891, by rfl⟩ : syracuseStep 3258377 = 2443783) B2443783
theorem B2172251 : Blo 2171435 2172251 := bstep (se 1 (by rfl) ⟨1629188, by rfl⟩ : syracuseStep 2172251 = 3258377) B3258377
theorem B10997045 : Blo 2171435 10997045 := bbase (se 5 (by rfl) ⟨515486, by rfl⟩ : syracuseStep 10997045 = 1030973) (by norm_num)
theorem B7331363 : Blo 2171435 7331363 := bstep (se 1 (by rfl) ⟨5498522, by rfl⟩ : syracuseStep 7331363 = 10997045) B10997045
theorem B4887575 : Blo 2171435 4887575 := bstep (se 1 (by rfl) ⟨3665681, by rfl⟩ : syracuseStep 4887575 = 7331363) B7331363
theorem B3258383 : Blo 2171435 3258383 := bstep (se 1 (by rfl) ⟨2443787, by rfl⟩ : syracuseStep 3258383 = 4887575) B4887575
theorem B2172255 : Blo 2171435 2172255 := bstep (se 1 (by rfl) ⟨1629191, by rfl⟩ : syracuseStep 2172255 = 3258383) B3258383
theorem B3258389 : Blo 2171435 3258389 := bbase (se 6 (by rfl) ⟨76368, by rfl⟩ : syracuseStep 3258389 = 152737) (by norm_num)
theorem B2172259 : Blo 2171435 2172259 := bstep (se 1 (by rfl) ⟨1629194, by rfl⟩ : syracuseStep 2172259 = 3258389) B3258389
theorem B15065621 : Blo 2171435 15065621 := bbase (se 6 (by rfl) ⟨353100, by rfl⟩ : syracuseStep 15065621 = 706201) (by norm_num)
theorem B10043747 : Blo 2171435 10043747 := bstep (se 1 (by rfl) ⟨7532810, by rfl⟩ : syracuseStep 10043747 = 15065621) B15065621
theorem B6695831 : Blo 2171435 6695831 := bstep (se 1 (by rfl) ⟨5021873, by rfl⟩ : syracuseStep 6695831 = 10043747) B10043747
theorem B17855549 : Blo 2171435 17855549 := bstep (se 3 (by rfl) ⟨3347915, by rfl⟩ : syracuseStep 17855549 = 6695831) B6695831
theorem B11903699 : Blo 2171435 11903699 := bstep (se 1 (by rfl) ⟨8927774, by rfl⟩ : syracuseStep 11903699 = 17855549) B17855549
theorem B31743197 : Blo 2171435 31743197 := bstep (se 3 (by rfl) ⟨5951849, by rfl⟩ : syracuseStep 31743197 = 11903699) B11903699
theorem B21162131 : Blo 2171435 21162131 := bstep (se 1 (by rfl) ⟨15871598, by rfl⟩ : syracuseStep 21162131 = 31743197) B31743197
theorem B14108087 : Blo 2171435 14108087 := bstep (se 1 (by rfl) ⟨10581065, by rfl⟩ : syracuseStep 14108087 = 21162131) B21162131
theorem B9405391 : Blo 2171435 9405391 := bstep (se 1 (by rfl) ⟨7054043, by rfl⟩ : syracuseStep 9405391 = 14108087) B14108087
theorem B12540521 : Blo 2171435 12540521 := bstep (se 2 (by rfl) ⟨4702695, by rfl⟩ : syracuseStep 12540521 = 9405391) B9405391
theorem B8360347 : Blo 2171435 8360347 := bstep (se 1 (by rfl) ⟨6270260, by rfl⟩ : syracuseStep 8360347 = 12540521) B12540521
theorem B11147129 : Blo 2171435 11147129 := bstep (se 2 (by rfl) ⟨4180173, by rfl⟩ : syracuseStep 11147129 = 8360347) B8360347
theorem B7431419 : Blo 2171435 7431419 := bstep (se 1 (by rfl) ⟨5573564, by rfl⟩ : syracuseStep 7431419 = 11147129) B11147129
theorem B4954279 : Blo 2171435 4954279 := bstep (se 1 (by rfl) ⟨3715709, by rfl⟩ : syracuseStep 4954279 = 7431419) B7431419
theorem B6605705 : Blo 2171435 6605705 := bstep (se 2 (by rfl) ⟨2477139, by rfl⟩ : syracuseStep 6605705 = 4954279) B4954279
theorem B4403803 : Blo 2171435 4403803 := bstep (se 1 (by rfl) ⟨3302852, by rfl⟩ : syracuseStep 4403803 = 6605705) B6605705
theorem B5871737 : Blo 2171435 5871737 := bstep (se 2 (by rfl) ⟨2201901, by rfl⟩ : syracuseStep 5871737 = 4403803) B4403803
theorem B3914491 : Blo 2171435 3914491 := bstep (se 1 (by rfl) ⟨2935868, by rfl⟩ : syracuseStep 3914491 = 5871737) B5871737
theorem B5219321 : Blo 2171435 5219321 := bstep (se 2 (by rfl) ⟨1957245, by rfl⟩ : syracuseStep 5219321 = 3914491) B3914491
theorem B13918189 : Blo 2171435 13918189 := bstep (se 3 (by rfl) ⟨2609660, by rfl⟩ : syracuseStep 13918189 = 5219321) B5219321
theorem B18557585 : Blo 2171435 18557585 := bstep (se 2 (by rfl) ⟨6959094, by rfl⟩ : syracuseStep 18557585 = 13918189) B13918189
theorem B12371723 : Blo 2171435 12371723 := bstep (se 1 (by rfl) ⟨9278792, by rfl⟩ : syracuseStep 12371723 = 18557585) B18557585
theorem B8247815 : Blo 2171435 8247815 := bstep (se 1 (by rfl) ⟨6185861, by rfl⟩ : syracuseStep 8247815 = 12371723) B12371723
theorem B5498543 : Blo 2171435 5498543 := bstep (se 1 (by rfl) ⟨4123907, by rfl⟩ : syracuseStep 5498543 = 8247815) B8247815
theorem B3665695 : Blo 2171435 3665695 := bstep (se 1 (by rfl) ⟨2749271, by rfl⟩ : syracuseStep 3665695 = 5498543) B5498543
theorem B4887593 : Blo 2171435 4887593 := bstep (se 2 (by rfl) ⟨1832847, by rfl⟩ : syracuseStep 4887593 = 3665695) B3665695
theorem B3258395 : Blo 2171435 3258395 := bstep (se 1 (by rfl) ⟨2443796, by rfl⟩ : syracuseStep 3258395 = 4887593) B4887593
theorem B2172263 : Blo 2171435 2172263 := bstep (se 1 (by rfl) ⟨1629197, by rfl⟩ : syracuseStep 2172263 = 3258395) B3258395
theorem B2443801 : Blo 2171435 2443801 := bbase (se 2 (by rfl) ⟨916425, by rfl⟩ : syracuseStep 2443801 = 1832851) (by norm_num)
theorem B3258401 : Blo 2171435 3258401 := bstep (se 2 (by rfl) ⟨1221900, by rfl⟩ : syracuseStep 3258401 = 2443801) B2443801
theorem B2172267 : Blo 2171435 2172267 := bstep (se 1 (by rfl) ⟨1629200, by rfl⟩ : syracuseStep 2172267 = 3258401) B3258401
theorem B8247845 : Blo 2171435 8247845 := bbase (se 4 (by rfl) ⟨773235, by rfl⟩ : syracuseStep 8247845 = 1546471) (by norm_num)
theorem B5498563 : Blo 2171435 5498563 := bstep (se 1 (by rfl) ⟨4123922, by rfl⟩ : syracuseStep 5498563 = 8247845) B8247845
theorem B7331417 : Blo 2171435 7331417 := bstep (se 2 (by rfl) ⟨2749281, by rfl⟩ : syracuseStep 7331417 = 5498563) B5498563
theorem B4887611 : Blo 2171435 4887611 := bstep (se 1 (by rfl) ⟨3665708, by rfl⟩ : syracuseStep 4887611 = 7331417) B7331417
theorem B3258407 : Blo 2171435 3258407 := bstep (se 1 (by rfl) ⟨2443805, by rfl⟩ : syracuseStep 3258407 = 4887611) B4887611
theorem B2172271 : Blo 2171435 2172271 := bstep (se 1 (by rfl) ⟨1629203, by rfl⟩ : syracuseStep 2172271 = 3258407) B3258407
theorem B3258413 : Blo 2171435 3258413 := bbase (se 3 (by rfl) ⟨610952, by rfl⟩ : syracuseStep 3258413 = 1221905) (by norm_num)
theorem B2172275 : Blo 2171435 2172275 := bstep (se 1 (by rfl) ⟨1629206, by rfl⟩ : syracuseStep 2172275 = 3258413) B3258413
theorem B4887629 : Blo 2171435 4887629 := bbase (se 3 (by rfl) ⟨916430, by rfl⟩ : syracuseStep 4887629 = 1832861) (by norm_num)
theorem B3258419 : Blo 2171435 3258419 := bstep (se 1 (by rfl) ⟨2443814, by rfl⟩ : syracuseStep 3258419 = 4887629) B4887629
theorem B2172279 : Blo 2171435 2172279 := bstep (se 1 (by rfl) ⟨1629209, by rfl⟩ : syracuseStep 2172279 = 3258419) B3258419
theorem B2749297 : Blo 2171435 2749297 := bbase (se 2 (by rfl) ⟨1030986, by rfl⟩ : syracuseStep 2749297 = 2061973) (by norm_num)
theorem B3665729 : Blo 2171435 3665729 := bstep (se 2 (by rfl) ⟨1374648, by rfl⟩ : syracuseStep 3665729 = 2749297) B2749297
theorem B2443819 : Blo 2171435 2443819 := bstep (se 1 (by rfl) ⟨1832864, by rfl⟩ : syracuseStep 2443819 = 3665729) B3665729
theorem B3258425 : Blo 2171435 3258425 := bstep (se 2 (by rfl) ⟨1221909, by rfl⟩ : syracuseStep 3258425 = 2443819) B2443819
theorem B2172283 : Blo 2171435 2172283 := bstep (se 1 (by rfl) ⟨1629212, by rfl⟩ : syracuseStep 2172283 = 3258425) B3258425
theorem B10438757 : Blo 2171435 10438757 := bbase (se 4 (by rfl) ⟨978633, by rfl⟩ : syracuseStep 10438757 = 1957267) (by norm_num)
theorem B6959171 : Blo 2171435 6959171 := bstep (se 1 (by rfl) ⟨5219378, by rfl⟩ : syracuseStep 6959171 = 10438757) B10438757
theorem B4639447 : Blo 2171435 4639447 := bstep (se 1 (by rfl) ⟨3479585, by rfl⟩ : syracuseStep 4639447 = 6959171) B6959171
theorem B24743717 : Blo 2171435 24743717 := bstep (se 4 (by rfl) ⟨2319723, by rfl⟩ : syracuseStep 24743717 = 4639447) B4639447
theorem B16495811 : Blo 2171435 16495811 := bstep (se 1 (by rfl) ⟨12371858, by rfl⟩ : syracuseStep 16495811 = 24743717) B24743717
theorem B10997207 : Blo 2171435 10997207 := bstep (se 1 (by rfl) ⟨8247905, by rfl⟩ : syracuseStep 10997207 = 16495811) B16495811
theorem B7331471 : Blo 2171435 7331471 := bstep (se 1 (by rfl) ⟨5498603, by rfl⟩ : syracuseStep 7331471 = 10997207) B10997207
theorem B4887647 : Blo 2171435 4887647 := bstep (se 1 (by rfl) ⟨3665735, by rfl⟩ : syracuseStep 4887647 = 7331471) B7331471
theorem B3258431 : Blo 2171435 3258431 := bstep (se 1 (by rfl) ⟨2443823, by rfl⟩ : syracuseStep 3258431 = 4887647) B4887647
theorem B2172287 : Blo 2171435 2172287 := bstep (se 1 (by rfl) ⟨1629215, by rfl⟩ : syracuseStep 2172287 = 3258431) B3258431
theorem B3258437 : Blo 2171435 3258437 := bbase (se 4 (by rfl) ⟨305478, by rfl⟩ : syracuseStep 3258437 = 610957) (by norm_num)
theorem B2172291 : Blo 2171435 2172291 := bstep (se 1 (by rfl) ⟨1629218, by rfl⟩ : syracuseStep 2172291 = 3258437) B3258437
theorem B3665749 : Blo 2171435 3665749 := bbase (se 9 (by rfl) ⟨10739, by rfl⟩ : syracuseStep 3665749 = 21479) (by norm_num)
theorem B4887665 : Blo 2171435 4887665 := bstep (se 2 (by rfl) ⟨1832874, by rfl⟩ : syracuseStep 4887665 = 3665749) B3665749
theorem B3258443 : Blo 2171435 3258443 := bstep (se 1 (by rfl) ⟨2443832, by rfl⟩ : syracuseStep 3258443 = 4887665) B4887665
theorem B2172295 : Blo 2171435 2172295 := bstep (se 1 (by rfl) ⟨1629221, by rfl⟩ : syracuseStep 2172295 = 3258443) B3258443
theorem B2443837 : Blo 2171435 2443837 := bbase (se 3 (by rfl) ⟨458219, by rfl⟩ : syracuseStep 2443837 = 916439) (by norm_num)
theorem B3258449 : Blo 2171435 3258449 := bstep (se 2 (by rfl) ⟨1221918, by rfl⟩ : syracuseStep 3258449 = 2443837) B2443837
theorem B2172299 : Blo 2171435 2172299 := bstep (se 1 (by rfl) ⟨1629224, by rfl⟩ : syracuseStep 2172299 = 3258449) B3258449
theorem B7331525 : Blo 2171435 7331525 := bbase (se 4 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 7331525 = 1374661) (by norm_num)
theorem B4887683 : Blo 2171435 4887683 := bstep (se 1 (by rfl) ⟨3665762, by rfl⟩ : syracuseStep 4887683 = 7331525) B7331525
theorem B3258455 : Blo 2171435 3258455 := bstep (se 1 (by rfl) ⟨2443841, by rfl⟩ : syracuseStep 3258455 = 4887683) B4887683
theorem B2172303 : Blo 2171435 2172303 := bstep (se 1 (by rfl) ⟨1629227, by rfl⟩ : syracuseStep 2172303 = 3258455) B3258455
theorem B3258461 : Blo 2171435 3258461 := bbase (se 3 (by rfl) ⟨610961, by rfl⟩ : syracuseStep 3258461 = 1221923) (by norm_num)
theorem B2172307 : Blo 2171435 2172307 := bstep (se 1 (by rfl) ⟨1629230, by rfl⟩ : syracuseStep 2172307 = 3258461) B3258461
theorem B4887701 : Blo 2171435 4887701 := bbase (se 6 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 4887701 = 229111) (by norm_num)
theorem B3258467 : Blo 2171435 3258467 := bstep (se 1 (by rfl) ⟨2443850, by rfl⟩ : syracuseStep 3258467 = 4887701) B4887701
theorem B2172311 : Blo 2171435 2172311 := bstep (se 1 (by rfl) ⟨1629233, by rfl⟩ : syracuseStep 2172311 = 3258467) B3258467
theorem B3093005 : Blo 2171435 3093005 := bbase (se 3 (by rfl) ⟨579938, by rfl⟩ : syracuseStep 3093005 = 1159877) (by norm_num)
theorem B8248013 : Blo 2171435 8248013 := bstep (se 3 (by rfl) ⟨1546502, by rfl⟩ : syracuseStep 8248013 = 3093005) B3093005
theorem B5498675 : Blo 2171435 5498675 := bstep (se 1 (by rfl) ⟨4124006, by rfl⟩ : syracuseStep 5498675 = 8248013) B8248013
theorem B3665783 : Blo 2171435 3665783 := bstep (se 1 (by rfl) ⟨2749337, by rfl⟩ : syracuseStep 3665783 = 5498675) B5498675
theorem B2443855 : Blo 2171435 2443855 := bstep (se 1 (by rfl) ⟨1832891, by rfl⟩ : syracuseStep 2443855 = 3665783) B3665783
theorem B3258473 : Blo 2171435 3258473 := bstep (se 2 (by rfl) ⟨1221927, by rfl⟩ : syracuseStep 3258473 = 2443855) B2443855
theorem B2172315 : Blo 2171435 2172315 := bstep (se 1 (by rfl) ⟨1629236, by rfl⟩ : syracuseStep 2172315 = 3258473) B3258473
theorem B2383489 : Blo 2171435 2383489 := bbase (se 2 (by rfl) ⟨893808, by rfl⟩ : syracuseStep 2383489 = 1787617) (by norm_num)
theorem B12711941 : Blo 2171435 12711941 := bstep (se 4 (by rfl) ⟨1191744, by rfl⟩ : syracuseStep 12711941 = 2383489) B2383489
theorem B8474627 : Blo 2171435 8474627 := bstep (se 1 (by rfl) ⟨6355970, by rfl⟩ : syracuseStep 8474627 = 12711941) B12711941
theorem B5649751 : Blo 2171435 5649751 := bstep (se 1 (by rfl) ⟨4237313, by rfl⟩ : syracuseStep 5649751 = 8474627) B8474627
theorem B7533001 : Blo 2171435 7533001 := bstep (se 2 (by rfl) ⟨2824875, by rfl⟩ : syracuseStep 7533001 = 5649751) B5649751
theorem B10044001 : Blo 2171435 10044001 := bstep (se 2 (by rfl) ⟨3766500, by rfl⟩ : syracuseStep 10044001 = 7533001) B7533001
theorem B13392001 : Blo 2171435 13392001 := bstep (se 2 (by rfl) ⟨5022000, by rfl⟩ : syracuseStep 13392001 = 10044001) B10044001
theorem B17856001 : Blo 2171435 17856001 := bstep (se 2 (by rfl) ⟨6696000, by rfl⟩ : syracuseStep 17856001 = 13392001) B13392001
theorem B23808001 : Blo 2171435 23808001 := bstep (se 2 (by rfl) ⟨8928000, by rfl⟩ : syracuseStep 23808001 = 17856001) B17856001
theorem B31744001 : Blo 2171435 31744001 := bstep (se 2 (by rfl) ⟨11904000, by rfl⟩ : syracuseStep 31744001 = 23808001) B23808001
theorem B21162667 : Blo 2171435 21162667 := bstep (se 1 (by rfl) ⟨15872000, by rfl⟩ : syracuseStep 21162667 = 31744001) B31744001
theorem B28216889 : Blo 2171435 28216889 := bstep (se 2 (by rfl) ⟨10581333, by rfl⟩ : syracuseStep 28216889 = 21162667) B21162667
theorem B18811259 : Blo 2171435 18811259 := bstep (se 1 (by rfl) ⟨14108444, by rfl⟩ : syracuseStep 18811259 = 28216889) B28216889
theorem B12540839 : Blo 2171435 12540839 := bstep (se 1 (by rfl) ⟨9405629, by rfl⟩ : syracuseStep 12540839 = 18811259) B18811259
theorem B33442237 : Blo 2171435 33442237 := bstep (se 3 (by rfl) ⟨6270419, by rfl⟩ : syracuseStep 33442237 = 12540839) B12540839
theorem B44589649 : Blo 2171435 44589649 := bstep (se 2 (by rfl) ⟨16721118, by rfl⟩ : syracuseStep 44589649 = 33442237) B33442237
theorem B59452865 : Blo 2171435 59452865 := bstep (se 2 (by rfl) ⟨22294824, by rfl⟩ : syracuseStep 59452865 = 44589649) B44589649
theorem B39635243 : Blo 2171435 39635243 := bstep (se 1 (by rfl) ⟨29726432, by rfl⟩ : syracuseStep 39635243 = 59452865) B59452865
theorem B26423495 : Blo 2171435 26423495 := bstep (se 1 (by rfl) ⟨19817621, by rfl⟩ : syracuseStep 26423495 = 39635243) B39635243
theorem B17615663 : Blo 2171435 17615663 := bstep (se 1 (by rfl) ⟨13211747, by rfl⟩ : syracuseStep 17615663 = 26423495) B26423495
theorem B11743775 : Blo 2171435 11743775 := bstep (se 1 (by rfl) ⟨8807831, by rfl⟩ : syracuseStep 11743775 = 17615663) B17615663
theorem B7829183 : Blo 2171435 7829183 := bstep (se 1 (by rfl) ⟨5871887, by rfl⟩ : syracuseStep 7829183 = 11743775) B11743775
theorem B20877821 : Blo 2171435 20877821 := bstep (se 3 (by rfl) ⟨3914591, by rfl⟩ : syracuseStep 20877821 = 7829183) B7829183
theorem B13918547 : Blo 2171435 13918547 := bstep (se 1 (by rfl) ⟨10438910, by rfl⟩ : syracuseStep 13918547 = 20877821) B20877821
theorem B9279031 : Blo 2171435 9279031 := bstep (se 1 (by rfl) ⟨6959273, by rfl⟩ : syracuseStep 9279031 = 13918547) B13918547
theorem B12372041 : Blo 2171435 12372041 := bstep (se 2 (by rfl) ⟨4639515, by rfl⟩ : syracuseStep 12372041 = 9279031) B9279031
theorem B8248027 : Blo 2171435 8248027 := bstep (se 1 (by rfl) ⟨6186020, by rfl⟩ : syracuseStep 8248027 = 12372041) B12372041
theorem B10997369 : Blo 2171435 10997369 := bstep (se 2 (by rfl) ⟨4124013, by rfl⟩ : syracuseStep 10997369 = 8248027) B8248027
theorem B7331579 : Blo 2171435 7331579 := bstep (se 1 (by rfl) ⟨5498684, by rfl⟩ : syracuseStep 7331579 = 10997369) B10997369
theorem B4887719 : Blo 2171435 4887719 := bstep (se 1 (by rfl) ⟨3665789, by rfl⟩ : syracuseStep 4887719 = 7331579) B7331579
theorem B3258479 : Blo 2171435 3258479 := bstep (se 1 (by rfl) ⟨2443859, by rfl⟩ : syracuseStep 3258479 = 4887719) B4887719
theorem B2172319 : Blo 2171435 2172319 := bstep (se 1 (by rfl) ⟨1629239, by rfl⟩ : syracuseStep 2172319 = 3258479) B3258479
theorem B3258485 : Blo 2171435 3258485 := bbase (se 5 (by rfl) ⟨152741, by rfl⟩ : syracuseStep 3258485 = 305483) (by norm_num)
theorem B2172323 : Blo 2171435 2172323 := bstep (se 1 (by rfl) ⟨1629242, by rfl⟩ : syracuseStep 2172323 = 3258485) B3258485
theorem B4124029 : Blo 2171435 4124029 := bbase (se 3 (by rfl) ⟨773255, by rfl⟩ : syracuseStep 4124029 = 1546511) (by norm_num)
theorem B5498705 : Blo 2171435 5498705 := bstep (se 2 (by rfl) ⟨2062014, by rfl⟩ : syracuseStep 5498705 = 4124029) B4124029
theorem B3665803 : Blo 2171435 3665803 := bstep (se 1 (by rfl) ⟨2749352, by rfl⟩ : syracuseStep 3665803 = 5498705) B5498705
theorem B4887737 : Blo 2171435 4887737 := bstep (se 2 (by rfl) ⟨1832901, by rfl⟩ : syracuseStep 4887737 = 3665803) B3665803
theorem B3258491 : Blo 2171435 3258491 := bstep (se 1 (by rfl) ⟨2443868, by rfl⟩ : syracuseStep 3258491 = 4887737) B4887737
theorem B2172327 : Blo 2171435 2172327 := bstep (se 1 (by rfl) ⟨1629245, by rfl⟩ : syracuseStep 2172327 = 3258491) B3258491
theorem B2443873 : Blo 2171435 2443873 := bbase (se 2 (by rfl) ⟨916452, by rfl⟩ : syracuseStep 2443873 = 1832905) (by norm_num)
theorem B3258497 : Blo 2171435 3258497 := bstep (se 2 (by rfl) ⟨1221936, by rfl⟩ : syracuseStep 3258497 = 2443873) B2443873
theorem B2172331 : Blo 2171435 2172331 := bstep (se 1 (by rfl) ⟨1629248, by rfl⟩ : syracuseStep 2172331 = 3258497) B3258497
theorem B5498725 : Blo 2171435 5498725 := bbase (se 4 (by rfl) ⟨515505, by rfl⟩ : syracuseStep 5498725 = 1031011) (by norm_num)
theorem B7331633 : Blo 2171435 7331633 := bstep (se 2 (by rfl) ⟨2749362, by rfl⟩ : syracuseStep 7331633 = 5498725) B5498725
theorem B4887755 : Blo 2171435 4887755 := bstep (se 1 (by rfl) ⟨3665816, by rfl⟩ : syracuseStep 4887755 = 7331633) B7331633
theorem B3258503 : Blo 2171435 3258503 := bstep (se 1 (by rfl) ⟨2443877, by rfl⟩ : syracuseStep 3258503 = 4887755) B4887755
theorem B2172335 : Blo 2171435 2172335 := bstep (se 1 (by rfl) ⟨1629251, by rfl⟩ : syracuseStep 2172335 = 3258503) B3258503
theorem B3258509 : Blo 2171435 3258509 := bbase (se 3 (by rfl) ⟨610970, by rfl⟩ : syracuseStep 3258509 = 1221941) (by norm_num)
theorem B2172339 : Blo 2171435 2172339 := bstep (se 1 (by rfl) ⟨1629254, by rfl⟩ : syracuseStep 2172339 = 3258509) B3258509
theorem B4887773 : Blo 2171435 4887773 := bbase (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) (by norm_num)
theorem B3258515 : Blo 2171435 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B2172343 : Blo 2171435 2172343 := bstep (se 1 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 2172343 = 3258515) B3258515
theorem B3665837 : Blo 2171435 3665837 := bbase (se 3 (by rfl) ⟨687344, by rfl⟩ : syracuseStep 3665837 = 1374689) (by norm_num)
theorem B2443891 : Blo 2171435 2443891 := bstep (se 1 (by rfl) ⟨1832918, by rfl⟩ : syracuseStep 2443891 = 3665837) B3665837
theorem B3258521 : Blo 2171435 3258521 := bstep (se 2 (by rfl) ⟨1221945, by rfl⟩ : syracuseStep 3258521 = 2443891) B2443891
theorem B2172347 : Blo 2171435 2172347 := bstep (se 1 (by rfl) ⟨1629260, by rfl⟩ : syracuseStep 2172347 = 3258521) B3258521
theorem B4295189 : Blo 2171435 4295189 := bbase (se 6 (by rfl) ⟨100668, by rfl⟩ : syracuseStep 4295189 = 201337) (by norm_num)
theorem B2863459 : Blo 2171435 2863459 := bstep (se 1 (by rfl) ⟨2147594, by rfl⟩ : syracuseStep 2863459 = 4295189) B4295189
theorem B3817945 : Blo 2171435 3817945 := bstep (se 2 (by rfl) ⟨1431729, by rfl⟩ : syracuseStep 3817945 = 2863459) B2863459
theorem B20362373 : Blo 2171435 20362373 := bstep (se 4 (by rfl) ⟨1908972, by rfl⟩ : syracuseStep 20362373 = 3817945) B3817945
theorem B13574915 : Blo 2171435 13574915 := bstep (se 1 (by rfl) ⟨10181186, by rfl⟩ : syracuseStep 13574915 = 20362373) B20362373
theorem B9049943 : Blo 2171435 9049943 := bstep (se 1 (by rfl) ⟨6787457, by rfl⟩ : syracuseStep 9049943 = 13574915) B13574915
theorem B6033295 : Blo 2171435 6033295 := bstep (se 1 (by rfl) ⟨4524971, by rfl⟩ : syracuseStep 6033295 = 9049943) B9049943
theorem B32177573 : Blo 2171435 32177573 := bstep (se 4 (by rfl) ⟨3016647, by rfl⟩ : syracuseStep 32177573 = 6033295) B6033295
theorem B21451715 : Blo 2171435 21451715 := bstep (se 1 (by rfl) ⟨16088786, by rfl⟩ : syracuseStep 21451715 = 32177573) B32177573
theorem B14301143 : Blo 2171435 14301143 := bstep (se 1 (by rfl) ⟨10725857, by rfl⟩ : syracuseStep 14301143 = 21451715) B21451715
theorem B9534095 : Blo 2171435 9534095 := bstep (se 1 (by rfl) ⟨7150571, by rfl⟩ : syracuseStep 9534095 = 14301143) B14301143
theorem B6356063 : Blo 2171435 6356063 := bstep (se 1 (by rfl) ⟨4767047, by rfl⟩ : syracuseStep 6356063 = 9534095) B9534095
theorem B16949501 : Blo 2171435 16949501 := bstep (se 3 (by rfl) ⟨3178031, by rfl⟩ : syracuseStep 16949501 = 6356063) B6356063
theorem B11299667 : Blo 2171435 11299667 := bstep (se 1 (by rfl) ⟨8474750, by rfl⟩ : syracuseStep 11299667 = 16949501) B16949501
theorem B30132445 : Blo 2171435 30132445 := bstep (se 3 (by rfl) ⟨5649833, by rfl⟩ : syracuseStep 30132445 = 11299667) B11299667
theorem B40176593 : Blo 2171435 40176593 := bstep (se 2 (by rfl) ⟨15066222, by rfl⟩ : syracuseStep 40176593 = 30132445) B30132445
theorem B26784395 : Blo 2171435 26784395 := bstep (se 1 (by rfl) ⟨20088296, by rfl⟩ : syracuseStep 26784395 = 40176593) B40176593
theorem B17856263 : Blo 2171435 17856263 := bstep (se 1 (by rfl) ⟨13392197, by rfl⟩ : syracuseStep 17856263 = 26784395) B26784395
theorem B11904175 : Blo 2171435 11904175 := bstep (se 1 (by rfl) ⟨8928131, by rfl⟩ : syracuseStep 11904175 = 17856263) B17856263
theorem B15872233 : Blo 2171435 15872233 := bstep (se 2 (by rfl) ⟨5952087, by rfl⟩ : syracuseStep 15872233 = 11904175) B11904175
theorem B21162977 : Blo 2171435 21162977 := bstep (se 2 (by rfl) ⟨7936116, by rfl⟩ : syracuseStep 21162977 = 15872233) B15872233
theorem B14108651 : Blo 2171435 14108651 := bstep (se 1 (by rfl) ⟨10581488, by rfl⟩ : syracuseStep 14108651 = 21162977) B21162977
theorem B9405767 : Blo 2171435 9405767 := bstep (se 1 (by rfl) ⟨7054325, by rfl⟩ : syracuseStep 9405767 = 14108651) B14108651
theorem B25082045 : Blo 2171435 25082045 := bstep (se 3 (by rfl) ⟨4702883, by rfl⟩ : syracuseStep 25082045 = 9405767) B9405767
theorem B16721363 : Blo 2171435 16721363 := bstep (se 1 (by rfl) ⟨12541022, by rfl⟩ : syracuseStep 16721363 = 25082045) B25082045
theorem B11147575 : Blo 2171435 11147575 := bstep (se 1 (by rfl) ⟨8360681, by rfl⟩ : syracuseStep 11147575 = 16721363) B16721363
theorem B14863433 : Blo 2171435 14863433 := bstep (se 2 (by rfl) ⟨5573787, by rfl⟩ : syracuseStep 14863433 = 11147575) B11147575
theorem B39635821 : Blo 2171435 39635821 := bstep (se 3 (by rfl) ⟨7431716, by rfl⟩ : syracuseStep 39635821 = 14863433) B14863433
theorem B211391045 : Blo 2171435 211391045 := bstep (se 4 (by rfl) ⟨19817910, by rfl⟩ : syracuseStep 211391045 = 39635821) B39635821
theorem B140927363 : Blo 2171435 140927363 := bstep (se 1 (by rfl) ⟨105695522, by rfl⟩ : syracuseStep 140927363 = 211391045) B211391045
theorem B93951575 : Blo 2171435 93951575 := bstep (se 1 (by rfl) ⟨70463681, by rfl⟩ : syracuseStep 93951575 = 140927363) B140927363
theorem B62634383 : Blo 2171435 62634383 := bstep (se 1 (by rfl) ⟨46975787, by rfl⟩ : syracuseStep 62634383 = 93951575) B93951575
theorem B41756255 : Blo 2171435 41756255 := bstep (se 1 (by rfl) ⟨31317191, by rfl⟩ : syracuseStep 41756255 = 62634383) B62634383
theorem B27837503 : Blo 2171435 27837503 := bstep (se 1 (by rfl) ⟨20878127, by rfl⟩ : syracuseStep 27837503 = 41756255) B41756255
theorem B18558335 : Blo 2171435 18558335 := bstep (se 1 (by rfl) ⟨13918751, by rfl⟩ : syracuseStep 18558335 = 27837503) B27837503
theorem B12372223 : Blo 2171435 12372223 := bstep (se 1 (by rfl) ⟨9279167, by rfl⟩ : syracuseStep 12372223 = 18558335) B18558335
theorem B16496297 : Blo 2171435 16496297 := bstep (se 2 (by rfl) ⟨6186111, by rfl⟩ : syracuseStep 16496297 = 12372223) B12372223
theorem B10997531 : Blo 2171435 10997531 := bstep (se 1 (by rfl) ⟨8248148, by rfl⟩ : syracuseStep 10997531 = 16496297) B16496297
theorem B7331687 : Blo 2171435 7331687 := bstep (se 1 (by rfl) ⟨5498765, by rfl⟩ : syracuseStep 7331687 = 10997531) B10997531
theorem B4887791 : Blo 2171435 4887791 := bstep (se 1 (by rfl) ⟨3665843, by rfl⟩ : syracuseStep 4887791 = 7331687) B7331687
theorem B3258527 : Blo 2171435 3258527 := bstep (se 1 (by rfl) ⟨2443895, by rfl⟩ : syracuseStep 3258527 = 4887791) B4887791
theorem B2172351 : Blo 2171435 2172351 := bstep (se 1 (by rfl) ⟨1629263, by rfl⟩ : syracuseStep 2172351 = 3258527) B3258527
theorem B3258533 : Blo 2171435 3258533 := bbase (se 4 (by rfl) ⟨305487, by rfl⟩ : syracuseStep 3258533 = 610975) (by norm_num)
theorem B2172355 : Blo 2171435 2172355 := bstep (se 1 (by rfl) ⟨1629266, by rfl⟩ : syracuseStep 2172355 = 3258533) B3258533
theorem B2749393 : Blo 2171435 2749393 := bbase (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) (by norm_num)
theorem B3665857 : Blo 2171435 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B4887809 : Blo 2171435 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B3258539 : Blo 2171435 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B2172359 : Blo 2171435 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B2443909 : Blo 2171435 2443909 := bbase (se 4 (by rfl) ⟨229116, by rfl⟩ : syracuseStep 2443909 = 458233) (by norm_num)
theorem B3258545 : Blo 2171435 3258545 := bstep (se 2 (by rfl) ⟨1221954, by rfl⟩ : syracuseStep 3258545 = 2443909) B2443909
theorem B2172363 : Blo 2171435 2172363 := bstep (se 1 (by rfl) ⟨1629272, by rfl⟩ : syracuseStep 2172363 = 3258545) B3258545
theorem B6959429 : Blo 2171435 6959429 := bbase (se 4 (by rfl) ⟨652446, by rfl⟩ : syracuseStep 6959429 = 1304893) (by norm_num)
theorem B4639619 : Blo 2171435 4639619 := bstep (se 1 (by rfl) ⟨3479714, by rfl⟩ : syracuseStep 4639619 = 6959429) B6959429
theorem B3093079 : Blo 2171435 3093079 := bstep (se 1 (by rfl) ⟨2319809, by rfl⟩ : syracuseStep 3093079 = 4639619) B4639619
theorem B4124105 : Blo 2171435 4124105 := bstep (se 2 (by rfl) ⟨1546539, by rfl⟩ : syracuseStep 4124105 = 3093079) B3093079
theorem B2749403 : Blo 2171435 2749403 := bstep (se 1 (by rfl) ⟨2062052, by rfl⟩ : syracuseStep 2749403 = 4124105) B4124105
theorem B7331741 : Blo 2171435 7331741 := bstep (se 3 (by rfl) ⟨1374701, by rfl⟩ : syracuseStep 7331741 = 2749403) B2749403
theorem B4887827 : Blo 2171435 4887827 := bstep (se 1 (by rfl) ⟨3665870, by rfl⟩ : syracuseStep 4887827 = 7331741) B7331741
theorem B3258551 : Blo 2171435 3258551 := bstep (se 1 (by rfl) ⟨2443913, by rfl⟩ : syracuseStep 3258551 = 4887827) B4887827
theorem B2172367 : Blo 2171435 2172367 := bstep (se 1 (by rfl) ⟨1629275, by rfl⟩ : syracuseStep 2172367 = 3258551) B3258551
theorem B3258557 : Blo 2171435 3258557 := bbase (se 3 (by rfl) ⟨610979, by rfl⟩ : syracuseStep 3258557 = 1221959) (by norm_num)
theorem B2172371 : Blo 2171435 2172371 := bstep (se 1 (by rfl) ⟨1629278, by rfl⟩ : syracuseStep 2172371 = 3258557) B3258557
theorem B4887845 : Blo 2171435 4887845 := bbase (se 4 (by rfl) ⟨458235, by rfl⟩ : syracuseStep 4887845 = 916471) (by norm_num)
theorem B3258563 : Blo 2171435 3258563 := bstep (se 1 (by rfl) ⟨2443922, by rfl⟩ : syracuseStep 3258563 = 4887845) B4887845
theorem B2172375 : Blo 2171435 2172375 := bstep (se 1 (by rfl) ⟨1629281, by rfl⟩ : syracuseStep 2172375 = 3258563) B3258563
theorem B5498837 : Blo 2171435 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B3665891 : Blo 2171435 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B2443927 : Blo 2171435 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B3258569 : Blo 2171435 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B2172379 : Blo 2171435 2172379 := bstep (se 1 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 2172379 = 3258569) B3258569
theorem B4180405 : Blo 2171435 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B5573873 : Blo 2171435 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B3715915 : Blo 2171435 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B4954553 : Blo 2171435 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B3303035 : Blo 2171435 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B2202023 : Blo 2171435 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B5872061 : Blo 2171435 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B15658829 : Blo 2171435 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B10439219 : Blo 2171435 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B6959479 : Blo 2171435 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B9279305 : Blo 2171435 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B6186203 : Blo 2171435 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B4124135 : Blo 2171435 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B10997693 : Blo 2171435 10997693 := bstep (se 3 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 10997693 = 4124135) B4124135
theorem B7331795 : Blo 2171435 7331795 := bstep (se 1 (by rfl) ⟨5498846, by rfl⟩ : syracuseStep 7331795 = 10997693) B10997693
theorem B4887863 : Blo 2171435 4887863 := bstep (se 1 (by rfl) ⟨3665897, by rfl⟩ : syracuseStep 4887863 = 7331795) B7331795
theorem B3258575 : Blo 2171435 3258575 := bstep (se 1 (by rfl) ⟨2443931, by rfl⟩ : syracuseStep 3258575 = 4887863) B4887863
theorem B2172383 : Blo 2171435 2172383 := bstep (se 1 (by rfl) ⟨1629287, by rfl⟩ : syracuseStep 2172383 = 3258575) B3258575
theorem B3258581 : Blo 2171435 3258581 := bbase (se 7 (by rfl) ⟨38186, by rfl⟩ : syracuseStep 3258581 = 76373) (by norm_num)
theorem B2172387 : Blo 2171435 2172387 := bstep (se 1 (by rfl) ⟨1629290, by rfl⟩ : syracuseStep 2172387 = 3258581) B3258581
theorem B5872085 : Blo 2171435 5872085 := bbase (se 7 (by rfl) ⟨68813, by rfl⟩ : syracuseStep 5872085 = 137627) (by norm_num)
theorem B3914723 : Blo 2171435 3914723 := bstep (se 1 (by rfl) ⟨2936042, by rfl⟩ : syracuseStep 3914723 = 5872085) B5872085
theorem B2609815 : Blo 2171435 2609815 := bstep (se 1 (by rfl) ⟨1957361, by rfl⟩ : syracuseStep 2609815 = 3914723) B3914723
theorem B3479753 : Blo 2171435 3479753 := bstep (se 2 (by rfl) ⟨1304907, by rfl⟩ : syracuseStep 3479753 = 2609815) B2609815
theorem B2319835 : Blo 2171435 2319835 := bstep (se 1 (by rfl) ⟨1739876, by rfl⟩ : syracuseStep 2319835 = 3479753) B3479753
theorem B3093113 : Blo 2171435 3093113 := bstep (se 2 (by rfl) ⟨1159917, by rfl⟩ : syracuseStep 3093113 = 2319835) B2319835
theorem B8248301 : Blo 2171435 8248301 := bstep (se 3 (by rfl) ⟨1546556, by rfl⟩ : syracuseStep 8248301 = 3093113) B3093113
theorem B5498867 : Blo 2171435 5498867 := bstep (se 1 (by rfl) ⟨4124150, by rfl⟩ : syracuseStep 5498867 = 8248301) B8248301
theorem B3665911 : Blo 2171435 3665911 := bstep (se 1 (by rfl) ⟨2749433, by rfl⟩ : syracuseStep 3665911 = 5498867) B5498867
theorem B4887881 : Blo 2171435 4887881 := bstep (se 2 (by rfl) ⟨1832955, by rfl⟩ : syracuseStep 4887881 = 3665911) B3665911
theorem B3258587 : Blo 2171435 3258587 := bstep (se 1 (by rfl) ⟨2443940, by rfl⟩ : syracuseStep 3258587 = 4887881) B4887881
theorem B2172391 : Blo 2171435 2172391 := bstep (se 1 (by rfl) ⟨1629293, by rfl⟩ : syracuseStep 2172391 = 3258587) B3258587
theorem B2443945 : Blo 2171435 2443945 := bbase (se 2 (by rfl) ⟨916479, by rfl⟩ : syracuseStep 2443945 = 1832959) (by norm_num)
theorem B3258593 : Blo 2171435 3258593 := bstep (se 2 (by rfl) ⟨1221972, by rfl⟩ : syracuseStep 3258593 = 2443945) B2443945
theorem B2172395 : Blo 2171435 2172395 := bstep (se 1 (by rfl) ⟨1629296, by rfl⟩ : syracuseStep 2172395 = 3258593) B3258593
theorem B3479765 : Blo 2171435 3479765 := bbase (se 7 (by rfl) ⟨40778, by rfl⟩ : syracuseStep 3479765 = 81557) (by norm_num)
theorem B9279373 : Blo 2171435 9279373 := bstep (se 3 (by rfl) ⟨1739882, by rfl⟩ : syracuseStep 9279373 = 3479765) B3479765
theorem B12372497 : Blo 2171435 12372497 := bstep (se 2 (by rfl) ⟨4639686, by rfl⟩ : syracuseStep 12372497 = 9279373) B9279373
theorem B8248331 : Blo 2171435 8248331 := bstep (se 1 (by rfl) ⟨6186248, by rfl⟩ : syracuseStep 8248331 = 12372497) B12372497
theorem B5498887 : Blo 2171435 5498887 := bstep (se 1 (by rfl) ⟨4124165, by rfl⟩ : syracuseStep 5498887 = 8248331) B8248331
theorem B7331849 : Blo 2171435 7331849 := bstep (se 2 (by rfl) ⟨2749443, by rfl⟩ : syracuseStep 7331849 = 5498887) B5498887
theorem B4887899 : Blo 2171435 4887899 := bstep (se 1 (by rfl) ⟨3665924, by rfl⟩ : syracuseStep 4887899 = 7331849) B7331849
theorem B3258599 : Blo 2171435 3258599 := bstep (se 1 (by rfl) ⟨2443949, by rfl⟩ : syracuseStep 3258599 = 4887899) B4887899
theorem B2172399 : Blo 2171435 2172399 := bstep (se 1 (by rfl) ⟨1629299, by rfl⟩ : syracuseStep 2172399 = 3258599) B3258599
theorem B3258605 : Blo 2171435 3258605 := bbase (se 3 (by rfl) ⟨610988, by rfl⟩ : syracuseStep 3258605 = 1221977) (by norm_num)
theorem B2172403 : Blo 2171435 2172403 := bstep (se 1 (by rfl) ⟨1629302, by rfl⟩ : syracuseStep 2172403 = 3258605) B3258605
theorem B4887917 : Blo 2171435 4887917 := bbase (se 3 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 4887917 = 1832969) (by norm_num)
theorem B3258611 : Blo 2171435 3258611 := bstep (se 1 (by rfl) ⟨2443958, by rfl⟩ : syracuseStep 3258611 = 4887917) B4887917
theorem B2172407 : Blo 2171435 2172407 := bstep (se 1 (by rfl) ⟨1629305, by rfl⟩ : syracuseStep 2172407 = 3258611) B3258611
theorem B4124189 : Blo 2171435 4124189 := bbase (se 3 (by rfl) ⟨773285, by rfl⟩ : syracuseStep 4124189 = 1546571) (by norm_num)
theorem B2749459 : Blo 2171435 2749459 := bstep (se 1 (by rfl) ⟨2062094, by rfl⟩ : syracuseStep 2749459 = 4124189) B4124189
theorem B3665945 : Blo 2171435 3665945 := bstep (se 2 (by rfl) ⟨1374729, by rfl⟩ : syracuseStep 3665945 = 2749459) B2749459
theorem B2443963 : Blo 2171435 2443963 := bstep (se 1 (by rfl) ⟨1832972, by rfl⟩ : syracuseStep 2443963 = 3665945) B3665945
theorem B3258617 : Blo 2171435 3258617 := bstep (se 2 (by rfl) ⟨1221981, by rfl⟩ : syracuseStep 3258617 = 2443963) B2443963
theorem B2172411 : Blo 2171435 2172411 := bstep (se 1 (by rfl) ⟨1629308, by rfl⟩ : syracuseStep 2172411 = 3258617) B3258617
theorem B2786977 : Blo 2171435 2786977 := bbase (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) (by norm_num)
theorem B3715969 : Blo 2171435 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B4954625 : Blo 2171435 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B3303083 : Blo 2171435 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B2202055 : Blo 2171435 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B11744293 : Blo 2171435 11744293 := bstep (se 4 (by rfl) ⟨1101027, by rfl⟩ : syracuseStep 11744293 = 2202055) B2202055
theorem B15659057 : Blo 2171435 15659057 := bstep (se 2 (by rfl) ⟨5872146, by rfl⟩ : syracuseStep 15659057 = 11744293) B11744293
theorem B10439371 : Blo 2171435 10439371 := bstep (se 1 (by rfl) ⟨7829528, by rfl⟩ : syracuseStep 10439371 = 15659057) B15659057
theorem B55676645 : Blo 2171435 55676645 := bstep (se 4 (by rfl) ⟨5219685, by rfl⟩ : syracuseStep 55676645 = 10439371) B10439371
theorem B37117763 : Blo 2171435 37117763 := bstep (se 1 (by rfl) ⟨27838322, by rfl⟩ : syracuseStep 37117763 = 55676645) B55676645
theorem B24745175 : Blo 2171435 24745175 := bstep (se 1 (by rfl) ⟨18558881, by rfl⟩ : syracuseStep 24745175 = 37117763) B37117763
theorem B16496783 : Blo 2171435 16496783 := bstep (se 1 (by rfl) ⟨12372587, by rfl⟩ : syracuseStep 16496783 = 24745175) B24745175
theorem B10997855 : Blo 2171435 10997855 := bstep (se 1 (by rfl) ⟨8248391, by rfl⟩ : syracuseStep 10997855 = 16496783) B16496783
theorem B7331903 : Blo 2171435 7331903 := bstep (se 1 (by rfl) ⟨5498927, by rfl⟩ : syracuseStep 7331903 = 10997855) B10997855
theorem B4887935 : Blo 2171435 4887935 := bstep (se 1 (by rfl) ⟨3665951, by rfl⟩ : syracuseStep 4887935 = 7331903) B7331903
theorem B3258623 : Blo 2171435 3258623 := bstep (se 1 (by rfl) ⟨2443967, by rfl⟩ : syracuseStep 3258623 = 4887935) B4887935
theorem B2172415 : Blo 2171435 2172415 := bstep (se 1 (by rfl) ⟨1629311, by rfl⟩ : syracuseStep 2172415 = 3258623) B3258623
theorem B3258629 : Blo 2171435 3258629 := bbase (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) (by norm_num)
theorem B2172419 : Blo 2171435 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B3665965 : Blo 2171435 3665965 := bbase (se 3 (by rfl) ⟨687368, by rfl⟩ : syracuseStep 3665965 = 1374737) (by norm_num)
theorem B4887953 : Blo 2171435 4887953 := bstep (se 2 (by rfl) ⟨1832982, by rfl⟩ : syracuseStep 4887953 = 3665965) B3665965
theorem B3258635 : Blo 2171435 3258635 := bstep (se 1 (by rfl) ⟨2443976, by rfl⟩ : syracuseStep 3258635 = 4887953) B4887953
theorem B2172423 : Blo 2171435 2172423 := bstep (se 1 (by rfl) ⟨1629317, by rfl⟩ : syracuseStep 2172423 = 3258635) B3258635
theorem B2443981 : Blo 2171435 2443981 := bbase (se 3 (by rfl) ⟨458246, by rfl⟩ : syracuseStep 2443981 = 916493) (by norm_num)
theorem B3258641 : Blo 2171435 3258641 := bstep (se 2 (by rfl) ⟨1221990, by rfl⟩ : syracuseStep 3258641 = 2443981) B2443981
theorem B2172427 : Blo 2171435 2172427 := bstep (se 1 (by rfl) ⟨1629320, by rfl⟩ : syracuseStep 2172427 = 3258641) B3258641
theorem B7331957 : Blo 2171435 7331957 := bbase (se 5 (by rfl) ⟨343685, by rfl⟩ : syracuseStep 7331957 = 687371) (by norm_num)
theorem B4887971 : Blo 2171435 4887971 := bstep (se 1 (by rfl) ⟨3665978, by rfl⟩ : syracuseStep 4887971 = 7331957) B7331957
theorem B3258647 : Blo 2171435 3258647 := bstep (se 1 (by rfl) ⟨2443985, by rfl⟩ : syracuseStep 3258647 = 4887971) B4887971
theorem B2172431 : Blo 2171435 2172431 := bstep (se 1 (by rfl) ⟨1629323, by rfl⟩ : syracuseStep 2172431 = 3258647) B3258647
theorem B3258653 : Blo 2171435 3258653 := bbase (se 3 (by rfl) ⟨610997, by rfl⟩ : syracuseStep 3258653 = 1221995) (by norm_num)
theorem B2172435 : Blo 2171435 2172435 := bstep (se 1 (by rfl) ⟨1629326, by rfl⟩ : syracuseStep 2172435 = 3258653) B3258653
theorem B4887989 : Blo 2171435 4887989 := bbase (se 5 (by rfl) ⟨229124, by rfl⟩ : syracuseStep 4887989 = 458249) (by norm_num)
theorem B3258659 : Blo 2171435 3258659 := bstep (se 1 (by rfl) ⟨2443994, by rfl⟩ : syracuseStep 3258659 = 4887989) B4887989
theorem B2172439 : Blo 2171435 2172439 := bstep (se 1 (by rfl) ⟨1629329, by rfl⟩ : syracuseStep 2172439 = 3258659) B3258659
theorem B4639781 : Blo 2171435 4639781 := bbase (se 4 (by rfl) ⟨434979, by rfl⟩ : syracuseStep 4639781 = 869959) (by norm_num)
theorem B12372749 : Blo 2171435 12372749 := bstep (se 3 (by rfl) ⟨2319890, by rfl⟩ : syracuseStep 12372749 = 4639781) B4639781
theorem B8248499 : Blo 2171435 8248499 := bstep (se 1 (by rfl) ⟨6186374, by rfl⟩ : syracuseStep 8248499 = 12372749) B12372749
theorem B5498999 : Blo 2171435 5498999 := bstep (se 1 (by rfl) ⟨4124249, by rfl⟩ : syracuseStep 5498999 = 8248499) B8248499
theorem B3665999 : Blo 2171435 3665999 := bstep (se 1 (by rfl) ⟨2749499, by rfl⟩ : syracuseStep 3665999 = 5498999) B5498999
theorem B2443999 : Blo 2171435 2443999 := bstep (se 1 (by rfl) ⟨1832999, by rfl⟩ : syracuseStep 2443999 = 3665999) B3665999
theorem B3258665 : Blo 2171435 3258665 := bstep (se 2 (by rfl) ⟨1221999, by rfl⟩ : syracuseStep 3258665 = 2443999) B2443999
theorem B2172443 : Blo 2171435 2172443 := bstep (se 1 (by rfl) ⟨1629332, by rfl⟩ : syracuseStep 2172443 = 3258665) B3258665
theorem B4639789 : Blo 2171435 4639789 := bbase (se 3 (by rfl) ⟨869960, by rfl⟩ : syracuseStep 4639789 = 1739921) (by norm_num)
theorem B6186385 : Blo 2171435 6186385 := bstep (se 2 (by rfl) ⟨2319894, by rfl⟩ : syracuseStep 6186385 = 4639789) B4639789
theorem B8248513 : Blo 2171435 8248513 := bstep (se 2 (by rfl) ⟨3093192, by rfl⟩ : syracuseStep 8248513 = 6186385) B6186385
theorem B10998017 : Blo 2171435 10998017 := bstep (se 2 (by rfl) ⟨4124256, by rfl⟩ : syracuseStep 10998017 = 8248513) B8248513
theorem B7332011 : Blo 2171435 7332011 := bstep (se 1 (by rfl) ⟨5499008, by rfl⟩ : syracuseStep 7332011 = 10998017) B10998017
theorem B4888007 : Blo 2171435 4888007 := bstep (se 1 (by rfl) ⟨3666005, by rfl⟩ : syracuseStep 4888007 = 7332011) B7332011
theorem B3258671 : Blo 2171435 3258671 := bstep (se 1 (by rfl) ⟨2444003, by rfl⟩ : syracuseStep 3258671 = 4888007) B4888007
theorem B2172447 : Blo 2171435 2172447 := bstep (se 1 (by rfl) ⟨1629335, by rfl⟩ : syracuseStep 2172447 = 3258671) B3258671
theorem B3258677 : Blo 2171435 3258677 := bbase (se 5 (by rfl) ⟨152750, by rfl⟩ : syracuseStep 3258677 = 305501) (by norm_num)
theorem B2172451 : Blo 2171435 2172451 := bstep (se 1 (by rfl) ⟨1629338, by rfl⟩ : syracuseStep 2172451 = 3258677) B3258677
theorem B5499029 : Blo 2171435 5499029 := bbase (se 6 (by rfl) ⟨128883, by rfl⟩ : syracuseStep 5499029 = 257767) (by norm_num)
theorem B3666019 : Blo 2171435 3666019 := bstep (se 1 (by rfl) ⟨2749514, by rfl⟩ : syracuseStep 3666019 = 5499029) B5499029
theorem B4888025 : Blo 2171435 4888025 := bstep (se 2 (by rfl) ⟨1833009, by rfl⟩ : syracuseStep 4888025 = 3666019) B3666019
theorem B3258683 : Blo 2171435 3258683 := bstep (se 1 (by rfl) ⟨2444012, by rfl⟩ : syracuseStep 3258683 = 4888025) B4888025
theorem B2172455 : Blo 2171435 2172455 := bstep (se 1 (by rfl) ⟨1629341, by rfl⟩ : syracuseStep 2172455 = 3258683) B3258683
theorem B2444017 : Blo 2171435 2444017 := bbase (se 2 (by rfl) ⟨916506, by rfl⟩ : syracuseStep 2444017 = 1833013) (by norm_num)
theorem B3258689 : Blo 2171435 3258689 := bstep (se 2 (by rfl) ⟨1222008, by rfl⟩ : syracuseStep 3258689 = 2444017) B2444017
theorem B2172459 : Blo 2171435 2172459 := bstep (se 1 (by rfl) ⟨1629344, by rfl⟩ : syracuseStep 2172459 = 3258689) B3258689
theorem B2545429 : Blo 2171435 2545429 := bbase (se 6 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 2545429 = 119317) (by norm_num)
theorem B3393905 : Blo 2171435 3393905 := bstep (se 2 (by rfl) ⟨1272714, by rfl⟩ : syracuseStep 3393905 = 2545429) B2545429
theorem B36201653 : Blo 2171435 36201653 := bstep (se 5 (by rfl) ⟨1696952, by rfl⟩ : syracuseStep 36201653 = 3393905) B3393905
theorem B24134435 : Blo 2171435 24134435 := bstep (se 1 (by rfl) ⟨18100826, by rfl⟩ : syracuseStep 24134435 = 36201653) B36201653
theorem B16089623 : Blo 2171435 16089623 := bstep (se 1 (by rfl) ⟨12067217, by rfl⟩ : syracuseStep 16089623 = 24134435) B24134435
theorem B10726415 : Blo 2171435 10726415 := bstep (se 1 (by rfl) ⟨8044811, by rfl⟩ : syracuseStep 10726415 = 16089623) B16089623
theorem B7150943 : Blo 2171435 7150943 := bstep (se 1 (by rfl) ⟨5363207, by rfl⟩ : syracuseStep 7150943 = 10726415) B10726415
theorem B19069181 : Blo 2171435 19069181 := bstep (se 3 (by rfl) ⟨3575471, by rfl⟩ : syracuseStep 19069181 = 7150943) B7150943
theorem B12712787 : Blo 2171435 12712787 := bstep (se 1 (by rfl) ⟨9534590, by rfl⟩ : syracuseStep 12712787 = 19069181) B19069181
theorem B8475191 : Blo 2171435 8475191 := bstep (se 1 (by rfl) ⟨6356393, by rfl⟩ : syracuseStep 8475191 = 12712787) B12712787
theorem B5650127 : Blo 2171435 5650127 := bstep (se 1 (by rfl) ⟨4237595, by rfl⟩ : syracuseStep 5650127 = 8475191) B8475191
theorem B3766751 : Blo 2171435 3766751 := bstep (se 1 (by rfl) ⟨2825063, by rfl⟩ : syracuseStep 3766751 = 5650127) B5650127
theorem B2511167 : Blo 2171435 2511167 := bstep (se 1 (by rfl) ⟨1883375, by rfl⟩ : syracuseStep 2511167 = 3766751) B3766751
theorem B6696445 : Blo 2171435 6696445 := bstep (se 3 (by rfl) ⟨1255583, by rfl⟩ : syracuseStep 6696445 = 2511167) B2511167
theorem B8928593 : Blo 2171435 8928593 := bstep (se 2 (by rfl) ⟨3348222, by rfl⟩ : syracuseStep 8928593 = 6696445) B6696445
theorem B5952395 : Blo 2171435 5952395 := bstep (se 1 (by rfl) ⟨4464296, by rfl⟩ : syracuseStep 5952395 = 8928593) B8928593
theorem B3968263 : Blo 2171435 3968263 := bstep (se 1 (by rfl) ⟨2976197, by rfl⟩ : syracuseStep 3968263 = 5952395) B5952395
theorem B21164069 : Blo 2171435 21164069 := bstep (se 4 (by rfl) ⟨1984131, by rfl⟩ : syracuseStep 21164069 = 3968263) B3968263
theorem B56437517 : Blo 2171435 56437517 := bstep (se 3 (by rfl) ⟨10582034, by rfl⟩ : syracuseStep 56437517 = 21164069) B21164069
theorem B150500045 : Blo 2171435 150500045 := bstep (se 3 (by rfl) ⟨28218758, by rfl⟩ : syracuseStep 150500045 = 56437517) B56437517
theorem B401333453 : Blo 2171435 401333453 := bstep (se 3 (by rfl) ⟨75250022, by rfl⟩ : syracuseStep 401333453 = 150500045) B150500045
theorem B267555635 : Blo 2171435 267555635 := bstep (se 1 (by rfl) ⟨200666726, by rfl⟩ : syracuseStep 267555635 = 401333453) B401333453
theorem B178370423 : Blo 2171435 178370423 := bstep (se 1 (by rfl) ⟨133777817, by rfl⟩ : syracuseStep 178370423 = 267555635) B267555635
theorem B118913615 : Blo 2171435 118913615 := bstep (se 1 (by rfl) ⟨89185211, by rfl⟩ : syracuseStep 118913615 = 178370423) B178370423
theorem B79275743 : Blo 2171435 79275743 := bstep (se 1 (by rfl) ⟨59456807, by rfl⟩ : syracuseStep 79275743 = 118913615) B118913615
theorem B52850495 : Blo 2171435 52850495 := bstep (se 1 (by rfl) ⟨39637871, by rfl⟩ : syracuseStep 52850495 = 79275743) B79275743
theorem B35233663 : Blo 2171435 35233663 := bstep (se 1 (by rfl) ⟨26425247, by rfl⟩ : syracuseStep 35233663 = 52850495) B52850495
theorem B46978217 : Blo 2171435 46978217 := bstep (se 2 (by rfl) ⟨17616831, by rfl⟩ : syracuseStep 46978217 = 35233663) B35233663
theorem B31318811 : Blo 2171435 31318811 := bstep (se 1 (by rfl) ⟨23489108, by rfl⟩ : syracuseStep 31318811 = 46978217) B46978217
theorem B20879207 : Blo 2171435 20879207 := bstep (se 1 (by rfl) ⟨15659405, by rfl⟩ : syracuseStep 20879207 = 31318811) B31318811
theorem B13919471 : Blo 2171435 13919471 := bstep (se 1 (by rfl) ⟨10439603, by rfl⟩ : syracuseStep 13919471 = 20879207) B20879207
theorem B9279647 : Blo 2171435 9279647 := bstep (se 1 (by rfl) ⟨6959735, by rfl⟩ : syracuseStep 9279647 = 13919471) B13919471
theorem B6186431 : Blo 2171435 6186431 := bstep (se 1 (by rfl) ⟨4639823, by rfl⟩ : syracuseStep 6186431 = 9279647) B9279647
theorem B4124287 : Blo 2171435 4124287 := bstep (se 1 (by rfl) ⟨3093215, by rfl⟩ : syracuseStep 4124287 = 6186431) B6186431
theorem B5499049 : Blo 2171435 5499049 := bstep (se 2 (by rfl) ⟨2062143, by rfl⟩ : syracuseStep 5499049 = 4124287) B4124287
theorem B7332065 : Blo 2171435 7332065 := bstep (se 2 (by rfl) ⟨2749524, by rfl⟩ : syracuseStep 7332065 = 5499049) B5499049
theorem B4888043 : Blo 2171435 4888043 := bstep (se 1 (by rfl) ⟨3666032, by rfl⟩ : syracuseStep 4888043 = 7332065) B7332065
theorem B3258695 : Blo 2171435 3258695 := bstep (se 1 (by rfl) ⟨2444021, by rfl⟩ : syracuseStep 3258695 = 4888043) B4888043
theorem B2172463 : Blo 2171435 2172463 := bstep (se 1 (by rfl) ⟨1629347, by rfl⟩ : syracuseStep 2172463 = 3258695) B3258695
theorem B3258701 : Blo 2171435 3258701 := bbase (se 3 (by rfl) ⟨611006, by rfl⟩ : syracuseStep 3258701 = 1222013) (by norm_num)
theorem B2172467 : Blo 2171435 2172467 := bstep (se 1 (by rfl) ⟨1629350, by rfl⟩ : syracuseStep 2172467 = 3258701) B3258701
theorem B4888061 : Blo 2171435 4888061 := bbase (se 3 (by rfl) ⟨916511, by rfl⟩ : syracuseStep 4888061 = 1833023) (by norm_num)
theorem B3258707 : Blo 2171435 3258707 := bstep (se 1 (by rfl) ⟨2444030, by rfl⟩ : syracuseStep 3258707 = 4888061) B4888061
theorem B2172471 : Blo 2171435 2172471 := bstep (se 1 (by rfl) ⟨1629353, by rfl⟩ : syracuseStep 2172471 = 3258707) B3258707
theorem B3666053 : Blo 2171435 3666053 := bbase (se 4 (by rfl) ⟨343692, by rfl⟩ : syracuseStep 3666053 = 687385) (by norm_num)
theorem B2444035 : Blo 2171435 2444035 := bstep (se 1 (by rfl) ⟨1833026, by rfl⟩ : syracuseStep 2444035 = 3666053) B3666053
theorem B3258713 : Blo 2171435 3258713 := bstep (se 2 (by rfl) ⟨1222017, by rfl⟩ : syracuseStep 3258713 = 2444035) B2444035
theorem B2172475 : Blo 2171435 2172475 := bstep (se 1 (by rfl) ⟨1629356, by rfl⟩ : syracuseStep 2172475 = 3258713) B3258713
theorem B16497269 : Blo 2171435 16497269 := bbase (se 5 (by rfl) ⟨773309, by rfl⟩ : syracuseStep 16497269 = 1546619) (by norm_num)
theorem B10998179 : Blo 2171435 10998179 := bstep (se 1 (by rfl) ⟨8248634, by rfl⟩ : syracuseStep 10998179 = 16497269) B16497269
theorem B7332119 : Blo 2171435 7332119 := bstep (se 1 (by rfl) ⟨5499089, by rfl⟩ : syracuseStep 7332119 = 10998179) B10998179
theorem B4888079 : Blo 2171435 4888079 := bstep (se 1 (by rfl) ⟨3666059, by rfl⟩ : syracuseStep 4888079 = 7332119) B7332119
theorem B3258719 : Blo 2171435 3258719 := bstep (se 1 (by rfl) ⟨2444039, by rfl⟩ : syracuseStep 3258719 = 4888079) B4888079
theorem B2172479 : Blo 2171435 2172479 := bstep (se 1 (by rfl) ⟨1629359, by rfl⟩ : syracuseStep 2172479 = 3258719) B3258719
theorem B3258725 : Blo 2171435 3258725 := bbase (se 4 (by rfl) ⟨305505, by rfl⟩ : syracuseStep 3258725 = 611011) (by norm_num)
theorem B2172483 : Blo 2171435 2172483 := bstep (se 1 (by rfl) ⟨1629362, by rfl⟩ : syracuseStep 2172483 = 3258725) B3258725
theorem B4124333 : Blo 2171435 4124333 := bbase (se 3 (by rfl) ⟨773312, by rfl⟩ : syracuseStep 4124333 = 1546625) (by norm_num)
theorem B2749555 : Blo 2171435 2749555 := bstep (se 1 (by rfl) ⟨2062166, by rfl⟩ : syracuseStep 2749555 = 4124333) B4124333
theorem B3666073 : Blo 2171435 3666073 := bstep (se 2 (by rfl) ⟨1374777, by rfl⟩ : syracuseStep 3666073 = 2749555) B2749555
theorem B4888097 : Blo 2171435 4888097 := bstep (se 2 (by rfl) ⟨1833036, by rfl⟩ : syracuseStep 4888097 = 3666073) B3666073
theorem B3258731 : Blo 2171435 3258731 := bstep (se 1 (by rfl) ⟨2444048, by rfl⟩ : syracuseStep 3258731 = 4888097) B4888097
theorem B2172487 : Blo 2171435 2172487 := bstep (se 1 (by rfl) ⟨1629365, by rfl⟩ : syracuseStep 2172487 = 3258731) B3258731
theorem B2444053 : Blo 2171435 2444053 := bbase (se 6 (by rfl) ⟨57282, by rfl⟩ : syracuseStep 2444053 = 114565) (by norm_num)
theorem B3258737 : Blo 2171435 3258737 := bstep (se 2 (by rfl) ⟨1222026, by rfl⟩ : syracuseStep 3258737 = 2444053) B2444053
theorem B2172491 : Blo 2171435 2172491 := bstep (se 1 (by rfl) ⟨1629368, by rfl⟩ : syracuseStep 2172491 = 3258737) B3258737
theorem B2749565 : Blo 2171435 2749565 := bbase (se 3 (by rfl) ⟨515543, by rfl⟩ : syracuseStep 2749565 = 1031087) (by norm_num)
theorem B7332173 : Blo 2171435 7332173 := bstep (se 3 (by rfl) ⟨1374782, by rfl⟩ : syracuseStep 7332173 = 2749565) B2749565
theorem B4888115 : Blo 2171435 4888115 := bstep (se 1 (by rfl) ⟨3666086, by rfl⟩ : syracuseStep 4888115 = 7332173) B7332173
theorem B3258743 : Blo 2171435 3258743 := bstep (se 1 (by rfl) ⟨2444057, by rfl⟩ : syracuseStep 3258743 = 4888115) B4888115
theorem B2172495 : Blo 2171435 2172495 := bstep (se 1 (by rfl) ⟨1629371, by rfl⟩ : syracuseStep 2172495 = 3258743) B3258743
theorem B3258749 : Blo 2171435 3258749 := bbase (se 3 (by rfl) ⟨611015, by rfl⟩ : syracuseStep 3258749 = 1222031) (by norm_num)
theorem B2172499 : Blo 2171435 2172499 := bstep (se 1 (by rfl) ⟨1629374, by rfl⟩ : syracuseStep 2172499 = 3258749) B3258749
theorem B4888133 : Blo 2171435 4888133 := bbase (se 4 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 4888133 = 916525) (by norm_num)
theorem B3258755 : Blo 2171435 3258755 := bstep (se 1 (by rfl) ⟨2444066, by rfl⟩ : syracuseStep 3258755 = 4888133) B4888133
theorem B2172503 : Blo 2171435 2172503 := bstep (se 1 (by rfl) ⟨1629377, by rfl⟩ : syracuseStep 2172503 = 3258755) B3258755
theorem B5219909 : Blo 2171435 5219909 := bbase (se 4 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 5219909 = 978733) (by norm_num)
theorem B3479939 : Blo 2171435 3479939 := bstep (se 1 (by rfl) ⟨2609954, by rfl⟩ : syracuseStep 3479939 = 5219909) B5219909
theorem B2319959 : Blo 2171435 2319959 := bstep (se 1 (by rfl) ⟨1739969, by rfl⟩ : syracuseStep 2319959 = 3479939) B3479939
theorem B6186557 : Blo 2171435 6186557 := bstep (se 3 (by rfl) ⟨1159979, by rfl⟩ : syracuseStep 6186557 = 2319959) B2319959
theorem B4124371 : Blo 2171435 4124371 := bstep (se 1 (by rfl) ⟨3093278, by rfl⟩ : syracuseStep 4124371 = 6186557) B6186557
theorem B5499161 : Blo 2171435 5499161 := bstep (se 2 (by rfl) ⟨2062185, by rfl⟩ : syracuseStep 5499161 = 4124371) B4124371
theorem B3666107 : Blo 2171435 3666107 := bstep (se 1 (by rfl) ⟨2749580, by rfl⟩ : syracuseStep 3666107 = 5499161) B5499161
theorem B2444071 : Blo 2171435 2444071 := bstep (se 1 (by rfl) ⟨1833053, by rfl⟩ : syracuseStep 2444071 = 3666107) B3666107
theorem B3258761 : Blo 2171435 3258761 := bstep (se 2 (by rfl) ⟨1222035, by rfl⟩ : syracuseStep 3258761 = 2444071) B2444071
theorem B2172507 : Blo 2171435 2172507 := bstep (se 1 (by rfl) ⟨1629380, by rfl⟩ : syracuseStep 2172507 = 3258761) B3258761
theorem B10998341 : Blo 2171435 10998341 := bbase (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) (by norm_num)
theorem B7332227 : Blo 2171435 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B4888151 : Blo 2171435 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B3258767 : Blo 2171435 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B2172511 : Blo 2171435 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B3258773 : Blo 2171435 3258773 := bbase (se 6 (by rfl) ⟨76377, by rfl⟩ : syracuseStep 3258773 = 152755) (by norm_num)
theorem B2172515 : Blo 2171435 2172515 := bstep (se 1 (by rfl) ⟨1629386, by rfl⟩ : syracuseStep 2172515 = 3258773) B3258773
theorem B2202161 : Blo 2171435 2202161 := bbase (se 2 (by rfl) ⟨825810, by rfl⟩ : syracuseStep 2202161 = 1651621) (by norm_num)
theorem B5872429 : Blo 2171435 5872429 := bstep (se 3 (by rfl) ⟨1101080, by rfl⟩ : syracuseStep 5872429 = 2202161) B2202161
theorem B7829905 : Blo 2171435 7829905 := bstep (se 2 (by rfl) ⟨2936214, by rfl⟩ : syracuseStep 7829905 = 5872429) B5872429
theorem B10439873 : Blo 2171435 10439873 := bstep (se 2 (by rfl) ⟨3914952, by rfl⟩ : syracuseStep 10439873 = 7829905) B7829905
theorem B6959915 : Blo 2171435 6959915 := bstep (se 1 (by rfl) ⟨5219936, by rfl⟩ : syracuseStep 6959915 = 10439873) B10439873
theorem B4639943 : Blo 2171435 4639943 := bstep (se 1 (by rfl) ⟨3479957, by rfl⟩ : syracuseStep 4639943 = 6959915) B6959915
theorem B12373181 : Blo 2171435 12373181 := bstep (se 3 (by rfl) ⟨2319971, by rfl⟩ : syracuseStep 12373181 = 4639943) B4639943
theorem B8248787 : Blo 2171435 8248787 := bstep (se 1 (by rfl) ⟨6186590, by rfl⟩ : syracuseStep 8248787 = 12373181) B12373181
theorem B5499191 : Blo 2171435 5499191 := bstep (se 1 (by rfl) ⟨4124393, by rfl⟩ : syracuseStep 5499191 = 8248787) B8248787
theorem B3666127 : Blo 2171435 3666127 := bstep (se 1 (by rfl) ⟨2749595, by rfl⟩ : syracuseStep 3666127 = 5499191) B5499191
theorem B4888169 : Blo 2171435 4888169 := bstep (se 2 (by rfl) ⟨1833063, by rfl⟩ : syracuseStep 4888169 = 3666127) B3666127
theorem B3258779 : Blo 2171435 3258779 := bstep (se 1 (by rfl) ⟨2444084, by rfl⟩ : syracuseStep 3258779 = 4888169) B4888169
theorem B2172519 : Blo 2171435 2172519 := bstep (se 1 (by rfl) ⟨1629389, by rfl⟩ : syracuseStep 2172519 = 3258779) B3258779
theorem B2444089 : Blo 2171435 2444089 := bbase (se 2 (by rfl) ⟨916533, by rfl⟩ : syracuseStep 2444089 = 1833067) (by norm_num)
theorem B3258785 : Blo 2171435 3258785 := bstep (se 2 (by rfl) ⟨1222044, by rfl⟩ : syracuseStep 3258785 = 2444089) B2444089
theorem B2172523 : Blo 2171435 2172523 := bstep (se 1 (by rfl) ⟨1629392, by rfl⟩ : syracuseStep 2172523 = 3258785) B3258785
theorem B6186613 : Blo 2171435 6186613 := bbase (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) (by norm_num)
theorem B8248817 : Blo 2171435 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B5499211 : Blo 2171435 5499211 := bstep (se 1 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 5499211 = 8248817) B8248817
theorem B7332281 : Blo 2171435 7332281 := bstep (se 2 (by rfl) ⟨2749605, by rfl⟩ : syracuseStep 7332281 = 5499211) B5499211
theorem B4888187 : Blo 2171435 4888187 := bstep (se 1 (by rfl) ⟨3666140, by rfl⟩ : syracuseStep 4888187 = 7332281) B7332281
theorem B3258791 : Blo 2171435 3258791 := bstep (se 1 (by rfl) ⟨2444093, by rfl⟩ : syracuseStep 3258791 = 4888187) B4888187
theorem B2172527 : Blo 2171435 2172527 := bstep (se 1 (by rfl) ⟨1629395, by rfl⟩ : syracuseStep 2172527 = 3258791) B3258791
theorem B3258797 : Blo 2171435 3258797 := bbase (se 3 (by rfl) ⟨611024, by rfl⟩ : syracuseStep 3258797 = 1222049) (by norm_num)
theorem B2172531 : Blo 2171435 2172531 := bstep (se 1 (by rfl) ⟨1629398, by rfl⟩ : syracuseStep 2172531 = 3258797) B3258797
theorem B4888205 : Blo 2171435 4888205 := bbase (se 3 (by rfl) ⟨916538, by rfl⟩ : syracuseStep 4888205 = 1833077) (by norm_num)
theorem B3258803 : Blo 2171435 3258803 := bstep (se 1 (by rfl) ⟨2444102, by rfl⟩ : syracuseStep 3258803 = 4888205) B4888205
theorem B2172535 : Blo 2171435 2172535 := bstep (se 1 (by rfl) ⟨1629401, by rfl⟩ : syracuseStep 2172535 = 3258803) B3258803
theorem B2749621 : Blo 2171435 2749621 := bbase (se 5 (by rfl) ⟨128888, by rfl⟩ : syracuseStep 2749621 = 257777) (by norm_num)
theorem B3666161 : Blo 2171435 3666161 := bstep (se 2 (by rfl) ⟨1374810, by rfl⟩ : syracuseStep 3666161 = 2749621) B2749621
theorem B2444107 : Blo 2171435 2444107 := bstep (se 1 (by rfl) ⟨1833080, by rfl⟩ : syracuseStep 2444107 = 3666161) B3666161
theorem B3258809 : Blo 2171435 3258809 := bstep (se 2 (by rfl) ⟨1222053, by rfl⟩ : syracuseStep 3258809 = 2444107) B2444107
theorem B2172539 : Blo 2171435 2172539 := bstep (se 1 (by rfl) ⟨1629404, by rfl⟩ : syracuseStep 2172539 = 3258809) B3258809
theorem B3303277 : Blo 2171435 3303277 := bbase (se 3 (by rfl) ⟨619364, by rfl⟩ : syracuseStep 3303277 = 1238729) (by norm_num)
theorem B70469909 : Blo 2171435 70469909 := bstep (se 6 (by rfl) ⟨1651638, by rfl⟩ : syracuseStep 70469909 = 3303277) B3303277
theorem B46979939 : Blo 2171435 46979939 := bstep (se 1 (by rfl) ⟨35234954, by rfl⟩ : syracuseStep 46979939 = 70469909) B70469909
theorem B31319959 : Blo 2171435 31319959 := bstep (se 1 (by rfl) ⟨23489969, by rfl⟩ : syracuseStep 31319959 = 46979939) B46979939
theorem B41759945 : Blo 2171435 41759945 := bstep (se 2 (by rfl) ⟨15659979, by rfl⟩ : syracuseStep 41759945 = 31319959) B31319959
theorem B27839963 : Blo 2171435 27839963 := bstep (se 1 (by rfl) ⟨20879972, by rfl⟩ : syracuseStep 27839963 = 41759945) B41759945
theorem B18559975 : Blo 2171435 18559975 := bstep (se 1 (by rfl) ⟨13919981, by rfl⟩ : syracuseStep 18559975 = 27839963) B27839963
theorem B24746633 : Blo 2171435 24746633 := bstep (se 2 (by rfl) ⟨9279987, by rfl⟩ : syracuseStep 24746633 = 18559975) B18559975
theorem B16497755 : Blo 2171435 16497755 := bstep (se 1 (by rfl) ⟨12373316, by rfl⟩ : syracuseStep 16497755 = 24746633) B24746633
theorem B10998503 : Blo 2171435 10998503 := bstep (se 1 (by rfl) ⟨8248877, by rfl⟩ : syracuseStep 10998503 = 16497755) B16497755
theorem B7332335 : Blo 2171435 7332335 := bstep (se 1 (by rfl) ⟨5499251, by rfl⟩ : syracuseStep 7332335 = 10998503) B10998503
theorem B4888223 : Blo 2171435 4888223 := bstep (se 1 (by rfl) ⟨3666167, by rfl⟩ : syracuseStep 4888223 = 7332335) B7332335
theorem B3258815 : Blo 2171435 3258815 := bstep (se 1 (by rfl) ⟨2444111, by rfl⟩ : syracuseStep 3258815 = 4888223) B4888223
theorem B2172543 : Blo 2171435 2172543 := bstep (se 1 (by rfl) ⟨1629407, by rfl⟩ : syracuseStep 2172543 = 3258815) B3258815
theorem B3258821 : Blo 2171435 3258821 := bbase (se 4 (by rfl) ⟨305514, by rfl⟩ : syracuseStep 3258821 = 611029) (by norm_num)
theorem B2172547 : Blo 2171435 2172547 := bstep (se 1 (by rfl) ⟨1629410, by rfl⟩ : syracuseStep 2172547 = 3258821) B3258821
theorem B3666181 : Blo 2171435 3666181 := bbase (se 4 (by rfl) ⟨343704, by rfl⟩ : syracuseStep 3666181 = 687409) (by norm_num)
theorem B4888241 : Blo 2171435 4888241 := bstep (se 2 (by rfl) ⟨1833090, by rfl⟩ : syracuseStep 4888241 = 3666181) B3666181
theorem B3258827 : Blo 2171435 3258827 := bstep (se 1 (by rfl) ⟨2444120, by rfl⟩ : syracuseStep 3258827 = 4888241) B4888241
theorem B2172551 : Blo 2171435 2172551 := bstep (se 1 (by rfl) ⟨1629413, by rfl⟩ : syracuseStep 2172551 = 3258827) B3258827
theorem B2444125 : Blo 2171435 2444125 := bbase (se 3 (by rfl) ⟨458273, by rfl⟩ : syracuseStep 2444125 = 916547) (by norm_num)
theorem B3258833 : Blo 2171435 3258833 := bstep (se 2 (by rfl) ⟨1222062, by rfl⟩ : syracuseStep 3258833 = 2444125) B2444125
theorem B2172555 : Blo 2171435 2172555 := bstep (se 1 (by rfl) ⟨1629416, by rfl⟩ : syracuseStep 2172555 = 3258833) B3258833
theorem B7332389 : Blo 2171435 7332389 := bbase (se 4 (by rfl) ⟨687411, by rfl⟩ : syracuseStep 7332389 = 1374823) (by norm_num)
theorem B4888259 : Blo 2171435 4888259 := bstep (se 1 (by rfl) ⟨3666194, by rfl⟩ : syracuseStep 4888259 = 7332389) B7332389
theorem B3258839 : Blo 2171435 3258839 := bstep (se 1 (by rfl) ⟨2444129, by rfl⟩ : syracuseStep 3258839 = 4888259) B4888259
theorem B2172559 : Blo 2171435 2172559 := bstep (se 1 (by rfl) ⟨1629419, by rfl⟩ : syracuseStep 2172559 = 3258839) B3258839
theorem B3258845 : Blo 2171435 3258845 := bbase (se 3 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 3258845 = 1222067) (by norm_num)
theorem B2172563 : Blo 2171435 2172563 := bstep (se 1 (by rfl) ⟨1629422, by rfl⟩ : syracuseStep 2172563 = 3258845) B3258845
theorem B4888277 : Blo 2171435 4888277 := bbase (se 7 (by rfl) ⟨57284, by rfl⟩ : syracuseStep 4888277 = 114569) (by norm_num)
theorem B3258851 : Blo 2171435 3258851 := bstep (se 1 (by rfl) ⟨2444138, by rfl⟩ : syracuseStep 3258851 = 4888277) B4888277
theorem B2172567 : Blo 2171435 2172567 := bstep (se 1 (by rfl) ⟨1629425, by rfl⟩ : syracuseStep 2172567 = 3258851) B3258851
theorem B3716237 : Blo 2171435 3716237 := bbase (se 3 (by rfl) ⟨696794, by rfl⟩ : syracuseStep 3716237 = 1393589) (by norm_num)
theorem B9909965 : Blo 2171435 9909965 := bstep (se 3 (by rfl) ⟨1858118, by rfl⟩ : syracuseStep 9909965 = 3716237) B3716237
theorem B6606643 : Blo 2171435 6606643 := bstep (se 1 (by rfl) ⟨4954982, by rfl⟩ : syracuseStep 6606643 = 9909965) B9909965
theorem B8808857 : Blo 2171435 8808857 := bstep (se 2 (by rfl) ⟨3303321, by rfl⟩ : syracuseStep 8808857 = 6606643) B6606643
theorem B5872571 : Blo 2171435 5872571 := bstep (se 1 (by rfl) ⟨4404428, by rfl⟩ : syracuseStep 5872571 = 8808857) B8808857
theorem B3915047 : Blo 2171435 3915047 := bstep (se 1 (by rfl) ⟨2936285, by rfl⟩ : syracuseStep 3915047 = 5872571) B5872571
theorem B2610031 : Blo 2171435 2610031 := bstep (se 1 (by rfl) ⟨1957523, by rfl⟩ : syracuseStep 2610031 = 3915047) B3915047
theorem B3480041 : Blo 2171435 3480041 := bstep (se 2 (by rfl) ⟨1305015, by rfl⟩ : syracuseStep 3480041 = 2610031) B2610031
theorem B9280109 : Blo 2171435 9280109 := bstep (se 3 (by rfl) ⟨1740020, by rfl⟩ : syracuseStep 9280109 = 3480041) B3480041
theorem B6186739 : Blo 2171435 6186739 := bstep (se 1 (by rfl) ⟨4640054, by rfl⟩ : syracuseStep 6186739 = 9280109) B9280109
theorem B8248985 : Blo 2171435 8248985 := bstep (se 2 (by rfl) ⟨3093369, by rfl⟩ : syracuseStep 8248985 = 6186739) B6186739
theorem B5499323 : Blo 2171435 5499323 := bstep (se 1 (by rfl) ⟨4124492, by rfl⟩ : syracuseStep 5499323 = 8248985) B8248985
theorem B3666215 : Blo 2171435 3666215 := bstep (se 1 (by rfl) ⟨2749661, by rfl⟩ : syracuseStep 3666215 = 5499323) B5499323
theorem B2444143 : Blo 2171435 2444143 := bstep (se 1 (by rfl) ⟨1833107, by rfl⟩ : syracuseStep 2444143 = 3666215) B3666215
theorem B3258857 : Blo 2171435 3258857 := bstep (se 2 (by rfl) ⟨1222071, by rfl⟩ : syracuseStep 3258857 = 2444143) B2444143
theorem B2172571 : Blo 2171435 2172571 := bstep (se 1 (by rfl) ⟨1629428, by rfl⟩ : syracuseStep 2172571 = 3258857) B3258857
theorem B8808869 : Blo 2171435 8808869 := bbase (se 4 (by rfl) ⟨825831, by rfl⟩ : syracuseStep 8808869 = 1651663) (by norm_num)
theorem B23490317 : Blo 2171435 23490317 := bstep (se 3 (by rfl) ⟨4404434, by rfl⟩ : syracuseStep 23490317 = 8808869) B8808869
theorem B15660211 : Blo 2171435 15660211 := bstep (se 1 (by rfl) ⟨11745158, by rfl⟩ : syracuseStep 15660211 = 23490317) B23490317
theorem B20880281 : Blo 2171435 20880281 := bstep (se 2 (by rfl) ⟨7830105, by rfl⟩ : syracuseStep 20880281 = 15660211) B15660211
theorem B13920187 : Blo 2171435 13920187 := bstep (se 1 (by rfl) ⟨10440140, by rfl⟩ : syracuseStep 13920187 = 20880281) B20880281
theorem B18560249 : Blo 2171435 18560249 := bstep (se 2 (by rfl) ⟨6960093, by rfl⟩ : syracuseStep 18560249 = 13920187) B13920187
theorem B12373499 : Blo 2171435 12373499 := bstep (se 1 (by rfl) ⟨9280124, by rfl⟩ : syracuseStep 12373499 = 18560249) B18560249
theorem B8248999 : Blo 2171435 8248999 := bstep (se 1 (by rfl) ⟨6186749, by rfl⟩ : syracuseStep 8248999 = 12373499) B12373499
theorem B10998665 : Blo 2171435 10998665 := bstep (se 2 (by rfl) ⟨4124499, by rfl⟩ : syracuseStep 10998665 = 8248999) B8248999
theorem B7332443 : Blo 2171435 7332443 := bstep (se 1 (by rfl) ⟨5499332, by rfl⟩ : syracuseStep 7332443 = 10998665) B10998665
theorem B4888295 : Blo 2171435 4888295 := bstep (se 1 (by rfl) ⟨3666221, by rfl⟩ : syracuseStep 4888295 = 7332443) B7332443
theorem B3258863 : Blo 2171435 3258863 := bstep (se 1 (by rfl) ⟨2444147, by rfl⟩ : syracuseStep 3258863 = 4888295) B4888295
theorem B2172575 : Blo 2171435 2172575 := bstep (se 1 (by rfl) ⟨1629431, by rfl⟩ : syracuseStep 2172575 = 3258863) B3258863
theorem B3258869 : Blo 2171435 3258869 := bbase (se 5 (by rfl) ⟨152759, by rfl⟩ : syracuseStep 3258869 = 305519) (by norm_num)
theorem B2172579 : Blo 2171435 2172579 := bstep (se 1 (by rfl) ⟨1629434, by rfl⟩ : syracuseStep 2172579 = 3258869) B3258869
theorem B6186773 : Blo 2171435 6186773 := bbase (se 6 (by rfl) ⟨145002, by rfl⟩ : syracuseStep 6186773 = 290005) (by norm_num)
theorem B4124515 : Blo 2171435 4124515 := bstep (se 1 (by rfl) ⟨3093386, by rfl⟩ : syracuseStep 4124515 = 6186773) B6186773
theorem B5499353 : Blo 2171435 5499353 := bstep (se 2 (by rfl) ⟨2062257, by rfl⟩ : syracuseStep 5499353 = 4124515) B4124515
theorem B3666235 : Blo 2171435 3666235 := bstep (se 1 (by rfl) ⟨2749676, by rfl⟩ : syracuseStep 3666235 = 5499353) B5499353
theorem B4888313 : Blo 2171435 4888313 := bstep (se 2 (by rfl) ⟨1833117, by rfl⟩ : syracuseStep 4888313 = 3666235) B3666235
theorem B3258875 : Blo 2171435 3258875 := bstep (se 1 (by rfl) ⟨2444156, by rfl⟩ : syracuseStep 3258875 = 4888313) B4888313
theorem B2172583 : Blo 2171435 2172583 := bstep (se 1 (by rfl) ⟨1629437, by rfl⟩ : syracuseStep 2172583 = 3258875) B3258875
theorem B2444161 : Blo 2171435 2444161 := bbase (se 2 (by rfl) ⟨916560, by rfl⟩ : syracuseStep 2444161 = 1833121) (by norm_num)
theorem B3258881 : Blo 2171435 3258881 := bstep (se 2 (by rfl) ⟨1222080, by rfl⟩ : syracuseStep 3258881 = 2444161) B2444161
theorem B2172587 : Blo 2171435 2172587 := bstep (se 1 (by rfl) ⟨1629440, by rfl⟩ : syracuseStep 2172587 = 3258881) B3258881
theorem B5499373 : Blo 2171435 5499373 := bbase (se 3 (by rfl) ⟨1031132, by rfl⟩ : syracuseStep 5499373 = 2062265) (by norm_num)
theorem B7332497 : Blo 2171435 7332497 := bstep (se 2 (by rfl) ⟨2749686, by rfl⟩ : syracuseStep 7332497 = 5499373) B5499373
theorem B4888331 : Blo 2171435 4888331 := bstep (se 1 (by rfl) ⟨3666248, by rfl⟩ : syracuseStep 4888331 = 7332497) B7332497
theorem B3258887 : Blo 2171435 3258887 := bstep (se 1 (by rfl) ⟨2444165, by rfl⟩ : syracuseStep 3258887 = 4888331) B4888331
theorem B2172591 : Blo 2171435 2172591 := bstep (se 1 (by rfl) ⟨1629443, by rfl⟩ : syracuseStep 2172591 = 3258887) B3258887
theorem B3258893 : Blo 2171435 3258893 := bbase (se 3 (by rfl) ⟨611042, by rfl⟩ : syracuseStep 3258893 = 1222085) (by norm_num)
theorem B2172595 : Blo 2171435 2172595 := bstep (se 1 (by rfl) ⟨1629446, by rfl⟩ : syracuseStep 2172595 = 3258893) B3258893
theorem B4888349 : Blo 2171435 4888349 := bbase (se 3 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 4888349 = 1833131) (by norm_num)
theorem B3258899 : Blo 2171435 3258899 := bstep (se 1 (by rfl) ⟨2444174, by rfl⟩ : syracuseStep 3258899 = 4888349) B4888349
theorem B2172599 : Blo 2171435 2172599 := bstep (se 1 (by rfl) ⟨1629449, by rfl⟩ : syracuseStep 2172599 = 3258899) B3258899
theorem B3666269 : Blo 2171435 3666269 := bbase (se 3 (by rfl) ⟨687425, by rfl⟩ : syracuseStep 3666269 = 1374851) (by norm_num)
theorem B2444179 : Blo 2171435 2444179 := bstep (se 1 (by rfl) ⟨1833134, by rfl⟩ : syracuseStep 2444179 = 3666269) B3666269
theorem B3258905 : Blo 2171435 3258905 := bstep (se 2 (by rfl) ⟨1222089, by rfl⟩ : syracuseStep 3258905 = 2444179) B2444179
theorem B2172603 : Blo 2171435 2172603 := bstep (se 1 (by rfl) ⟨1629452, by rfl⟩ : syracuseStep 2172603 = 3258905) B3258905
theorem B9280261 : Blo 2171435 9280261 := bbase (se 4 (by rfl) ⟨870024, by rfl⟩ : syracuseStep 9280261 = 1740049) (by norm_num)
theorem B12373681 : Blo 2171435 12373681 := bstep (se 2 (by rfl) ⟨4640130, by rfl⟩ : syracuseStep 12373681 = 9280261) B9280261
theorem B16498241 : Blo 2171435 16498241 := bstep (se 2 (by rfl) ⟨6186840, by rfl⟩ : syracuseStep 16498241 = 12373681) B12373681
theorem B10998827 : Blo 2171435 10998827 := bstep (se 1 (by rfl) ⟨8249120, by rfl⟩ : syracuseStep 10998827 = 16498241) B16498241
theorem B7332551 : Blo 2171435 7332551 := bstep (se 1 (by rfl) ⟨5499413, by rfl⟩ : syracuseStep 7332551 = 10998827) B10998827
theorem B4888367 : Blo 2171435 4888367 := bstep (se 1 (by rfl) ⟨3666275, by rfl⟩ : syracuseStep 4888367 = 7332551) B7332551
theorem B3258911 : Blo 2171435 3258911 := bstep (se 1 (by rfl) ⟨2444183, by rfl⟩ : syracuseStep 3258911 = 4888367) B4888367
theorem B2172607 : Blo 2171435 2172607 := bstep (se 1 (by rfl) ⟨1629455, by rfl⟩ : syracuseStep 2172607 = 3258911) B3258911
theorem B3258917 : Blo 2171435 3258917 := bbase (se 4 (by rfl) ⟨305523, by rfl⟩ : syracuseStep 3258917 = 611047) (by norm_num)
theorem B2172611 : Blo 2171435 2172611 := bstep (se 1 (by rfl) ⟨1629458, by rfl⟩ : syracuseStep 2172611 = 3258917) B3258917
theorem B2749717 : Blo 2171435 2749717 := bbase (se 6 (by rfl) ⟨64446, by rfl⟩ : syracuseStep 2749717 = 128893) (by norm_num)
theorem B3666289 : Blo 2171435 3666289 := bstep (se 2 (by rfl) ⟨1374858, by rfl⟩ : syracuseStep 3666289 = 2749717) B2749717
theorem B4888385 : Blo 2171435 4888385 := bstep (se 2 (by rfl) ⟨1833144, by rfl⟩ : syracuseStep 4888385 = 3666289) B3666289
theorem B3258923 : Blo 2171435 3258923 := bstep (se 1 (by rfl) ⟨2444192, by rfl⟩ : syracuseStep 3258923 = 4888385) B4888385
theorem B2172615 : Blo 2171435 2172615 := bstep (se 1 (by rfl) ⟨1629461, by rfl⟩ : syracuseStep 2172615 = 3258923) B3258923
theorem B2444197 : Blo 2171435 2444197 := bbase (se 4 (by rfl) ⟨229143, by rfl⟩ : syracuseStep 2444197 = 458287) (by norm_num)
theorem B3258929 : Blo 2171435 3258929 := bstep (se 2 (by rfl) ⟨1222098, by rfl⟩ : syracuseStep 3258929 = 2444197) B2444197
theorem B2172619 : Blo 2171435 2172619 := bstep (se 1 (by rfl) ⟨1629464, by rfl⟩ : syracuseStep 2172619 = 3258929) B3258929
theorem B10440373 : Blo 2171435 10440373 := bbase (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) (by norm_num)
theorem B13920497 : Blo 2171435 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B9280331 : Blo 2171435 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B6186887 : Blo 2171435 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B4124591 : Blo 2171435 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B2749727 : Blo 2171435 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B7332605 : Blo 2171435 7332605 := bstep (se 3 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 7332605 = 2749727) B2749727
theorem B4888403 : Blo 2171435 4888403 := bstep (se 1 (by rfl) ⟨3666302, by rfl⟩ : syracuseStep 4888403 = 7332605) B7332605
theorem B3258935 : Blo 2171435 3258935 := bstep (se 1 (by rfl) ⟨2444201, by rfl⟩ : syracuseStep 3258935 = 4888403) B4888403
theorem B2172623 : Blo 2171435 2172623 := bstep (se 1 (by rfl) ⟨1629467, by rfl⟩ : syracuseStep 2172623 = 3258935) B3258935
theorem B3258941 : Blo 2171435 3258941 := bbase (se 3 (by rfl) ⟨611051, by rfl⟩ : syracuseStep 3258941 = 1222103) (by norm_num)
theorem B2172627 : Blo 2171435 2172627 := bstep (se 1 (by rfl) ⟨1629470, by rfl⟩ : syracuseStep 2172627 = 3258941) B3258941
theorem B4888421 : Blo 2171435 4888421 := bbase (se 4 (by rfl) ⟨458289, by rfl⟩ : syracuseStep 4888421 = 916579) (by norm_num)
theorem B3258947 : Blo 2171435 3258947 := bstep (se 1 (by rfl) ⟨2444210, by rfl⟩ : syracuseStep 3258947 = 4888421) B4888421
theorem B2172631 : Blo 2171435 2172631 := bstep (se 1 (by rfl) ⟨1629473, by rfl⟩ : syracuseStep 2172631 = 3258947) B3258947
theorem B5499485 : Blo 2171435 5499485 := bbase (se 3 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 5499485 = 2062307) (by norm_num)
theorem B3666323 : Blo 2171435 3666323 := bstep (se 1 (by rfl) ⟨2749742, by rfl⟩ : syracuseStep 3666323 = 5499485) B5499485
theorem B2444215 : Blo 2171435 2444215 := bstep (se 1 (by rfl) ⟨1833161, by rfl⟩ : syracuseStep 2444215 = 3666323) B3666323
theorem B3258953 : Blo 2171435 3258953 := bstep (se 2 (by rfl) ⟨1222107, by rfl⟩ : syracuseStep 3258953 = 2444215) B2444215
theorem B2172635 : Blo 2171435 2172635 := bstep (se 1 (by rfl) ⟨1629476, by rfl⟩ : syracuseStep 2172635 = 3258953) B3258953
theorem B4124621 : Blo 2171435 4124621 := bbase (se 3 (by rfl) ⟨773366, by rfl⟩ : syracuseStep 4124621 = 1546733) (by norm_num)
theorem B10998989 : Blo 2171435 10998989 := bstep (se 3 (by rfl) ⟨2062310, by rfl⟩ : syracuseStep 10998989 = 4124621) B4124621
theorem B7332659 : Blo 2171435 7332659 := bstep (se 1 (by rfl) ⟨5499494, by rfl⟩ : syracuseStep 7332659 = 10998989) B10998989
theorem B4888439 : Blo 2171435 4888439 := bstep (se 1 (by rfl) ⟨3666329, by rfl⟩ : syracuseStep 4888439 = 7332659) B7332659
theorem B3258959 : Blo 2171435 3258959 := bstep (se 1 (by rfl) ⟨2444219, by rfl⟩ : syracuseStep 3258959 = 4888439) B4888439
theorem B2172639 : Blo 2171435 2172639 := bstep (se 1 (by rfl) ⟨1629479, by rfl⟩ : syracuseStep 2172639 = 3258959) B3258959
theorem B3258965 : Blo 2171435 3258965 := bbase (se 8 (by rfl) ⟨19095, by rfl⟩ : syracuseStep 3258965 = 38191) (by norm_num)
theorem B2172643 : Blo 2171435 2172643 := bstep (se 1 (by rfl) ⟨1629482, by rfl⟩ : syracuseStep 2172643 = 3258965) B3258965
theorem B6960325 : Blo 2171435 6960325 := bbase (se 4 (by rfl) ⟨652530, by rfl⟩ : syracuseStep 6960325 = 1305061) (by norm_num)
theorem B9280433 : Blo 2171435 9280433 := bstep (se 2 (by rfl) ⟨3480162, by rfl⟩ : syracuseStep 9280433 = 6960325) B6960325
theorem B6186955 : Blo 2171435 6186955 := bstep (se 1 (by rfl) ⟨4640216, by rfl⟩ : syracuseStep 6186955 = 9280433) B9280433
theorem B8249273 : Blo 2171435 8249273 := bstep (se 2 (by rfl) ⟨3093477, by rfl⟩ : syracuseStep 8249273 = 6186955) B6186955
theorem B5499515 : Blo 2171435 5499515 := bstep (se 1 (by rfl) ⟨4124636, by rfl⟩ : syracuseStep 5499515 = 8249273) B8249273
theorem B3666343 : Blo 2171435 3666343 := bstep (se 1 (by rfl) ⟨2749757, by rfl⟩ : syracuseStep 3666343 = 5499515) B5499515
theorem B4888457 : Blo 2171435 4888457 := bstep (se 2 (by rfl) ⟨1833171, by rfl⟩ : syracuseStep 4888457 = 3666343) B3666343
theorem B3258971 : Blo 2171435 3258971 := bstep (se 1 (by rfl) ⟨2444228, by rfl⟩ : syracuseStep 3258971 = 4888457) B4888457
theorem B2172647 : Blo 2171435 2172647 := bstep (se 1 (by rfl) ⟨1629485, by rfl⟩ : syracuseStep 2172647 = 3258971) B3258971
theorem B2444233 : Blo 2171435 2444233 := bbase (se 2 (by rfl) ⟨916587, by rfl⟩ : syracuseStep 2444233 = 1833175) (by norm_num)
theorem B3258977 : Blo 2171435 3258977 := bstep (se 2 (by rfl) ⟨1222116, by rfl⟩ : syracuseStep 3258977 = 2444233) B2444233
theorem B2172651 : Blo 2171435 2172651 := bstep (se 1 (by rfl) ⟨1629488, by rfl⟩ : syracuseStep 2172651 = 3258977) B3258977
theorem B3394205 : Blo 2171435 3394205 := bbase (se 3 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 3394205 = 1272827) (by norm_num)
theorem B2262803 : Blo 2171435 2262803 := bstep (se 1 (by rfl) ⟨1697102, by rfl⟩ : syracuseStep 2262803 = 3394205) B3394205
theorem B6034141 : Blo 2171435 6034141 := bstep (se 3 (by rfl) ⟨1131401, by rfl⟩ : syracuseStep 6034141 = 2262803) B2262803
theorem B32182085 : Blo 2171435 32182085 := bstep (se 4 (by rfl) ⟨3017070, by rfl⟩ : syracuseStep 32182085 = 6034141) B6034141
theorem B21454723 : Blo 2171435 21454723 := bstep (se 1 (by rfl) ⟨16091042, by rfl⟩ : syracuseStep 21454723 = 32182085) B32182085
theorem B28606297 : Blo 2171435 28606297 := bstep (se 2 (by rfl) ⟨10727361, by rfl⟩ : syracuseStep 28606297 = 21454723) B21454723
theorem B38141729 : Blo 2171435 38141729 := bstep (se 2 (by rfl) ⟨14303148, by rfl⟩ : syracuseStep 38141729 = 28606297) B28606297
theorem B25427819 : Blo 2171435 25427819 := bstep (se 1 (by rfl) ⟨19070864, by rfl⟩ : syracuseStep 25427819 = 38141729) B38141729
theorem B16951879 : Blo 2171435 16951879 := bstep (se 1 (by rfl) ⟨12713909, by rfl⟩ : syracuseStep 16951879 = 25427819) B25427819
theorem B22602505 : Blo 2171435 22602505 := bstep (se 2 (by rfl) ⟨8475939, by rfl⟩ : syracuseStep 22602505 = 16951879) B16951879
theorem B30136673 : Blo 2171435 30136673 := bstep (se 2 (by rfl) ⟨11301252, by rfl⟩ : syracuseStep 30136673 = 22602505) B22602505
theorem B20091115 : Blo 2171435 20091115 := bstep (se 1 (by rfl) ⟨15068336, by rfl⟩ : syracuseStep 20091115 = 30136673) B30136673
theorem B26788153 : Blo 2171435 26788153 := bstep (se 2 (by rfl) ⟨10045557, by rfl⟩ : syracuseStep 26788153 = 20091115) B20091115
theorem B35717537 : Blo 2171435 35717537 := bstep (se 2 (by rfl) ⟨13394076, by rfl⟩ : syracuseStep 35717537 = 26788153) B26788153
theorem B23811691 : Blo 2171435 23811691 := bstep (se 1 (by rfl) ⟨17858768, by rfl⟩ : syracuseStep 23811691 = 35717537) B35717537
theorem B31748921 : Blo 2171435 31748921 := bstep (se 2 (by rfl) ⟨11905845, by rfl⟩ : syracuseStep 31748921 = 23811691) B23811691
theorem B21165947 : Blo 2171435 21165947 := bstep (se 1 (by rfl) ⟨15874460, by rfl⟩ : syracuseStep 21165947 = 31748921) B31748921
theorem B14110631 : Blo 2171435 14110631 := bstep (se 1 (by rfl) ⟨10582973, by rfl⟩ : syracuseStep 14110631 = 21165947) B21165947
theorem B9407087 : Blo 2171435 9407087 := bstep (se 1 (by rfl) ⟨7055315, by rfl⟩ : syracuseStep 9407087 = 14110631) B14110631
theorem B6271391 : Blo 2171435 6271391 := bstep (se 1 (by rfl) ⟨4703543, by rfl⟩ : syracuseStep 6271391 = 9407087) B9407087
theorem B16723709 : Blo 2171435 16723709 := bstep (se 3 (by rfl) ⟨3135695, by rfl⟩ : syracuseStep 16723709 = 6271391) B6271391
theorem B11149139 : Blo 2171435 11149139 := bstep (se 1 (by rfl) ⟨8361854, by rfl⟩ : syracuseStep 11149139 = 16723709) B16723709
theorem B7432759 : Blo 2171435 7432759 := bstep (se 1 (by rfl) ⟨5574569, by rfl⟩ : syracuseStep 7432759 = 11149139) B11149139
theorem B9910345 : Blo 2171435 9910345 := bstep (se 2 (by rfl) ⟨3716379, by rfl⟩ : syracuseStep 9910345 = 7432759) B7432759
theorem B13213793 : Blo 2171435 13213793 := bstep (se 2 (by rfl) ⟨4955172, by rfl⟩ : syracuseStep 13213793 = 9910345) B9910345
theorem B8809195 : Blo 2171435 8809195 := bstep (se 1 (by rfl) ⟨6606896, by rfl⟩ : syracuseStep 8809195 = 13213793) B13213793
theorem B11745593 : Blo 2171435 11745593 := bstep (se 2 (by rfl) ⟨4404597, by rfl⟩ : syracuseStep 11745593 = 8809195) B8809195
theorem B7830395 : Blo 2171435 7830395 := bstep (se 1 (by rfl) ⟨5872796, by rfl⟩ : syracuseStep 7830395 = 11745593) B11745593
theorem B5220263 : Blo 2171435 5220263 := bstep (se 1 (by rfl) ⟨3915197, by rfl⟩ : syracuseStep 5220263 = 7830395) B7830395
theorem B3480175 : Blo 2171435 3480175 := bstep (se 1 (by rfl) ⟨2610131, by rfl⟩ : syracuseStep 3480175 = 5220263) B5220263
theorem B18560933 : Blo 2171435 18560933 := bstep (se 4 (by rfl) ⟨1740087, by rfl⟩ : syracuseStep 18560933 = 3480175) B3480175
theorem B12373955 : Blo 2171435 12373955 := bstep (se 1 (by rfl) ⟨9280466, by rfl⟩ : syracuseStep 12373955 = 18560933) B18560933
theorem B8249303 : Blo 2171435 8249303 := bstep (se 1 (by rfl) ⟨6186977, by rfl⟩ : syracuseStep 8249303 = 12373955) B12373955
theorem B5499535 : Blo 2171435 5499535 := bstep (se 1 (by rfl) ⟨4124651, by rfl⟩ : syracuseStep 5499535 = 8249303) B8249303
theorem B7332713 : Blo 2171435 7332713 := bstep (se 2 (by rfl) ⟨2749767, by rfl⟩ : syracuseStep 7332713 = 5499535) B5499535
theorem B4888475 : Blo 2171435 4888475 := bstep (se 1 (by rfl) ⟨3666356, by rfl⟩ : syracuseStep 4888475 = 7332713) B7332713
theorem B3258983 : Blo 2171435 3258983 := bstep (se 1 (by rfl) ⟨2444237, by rfl⟩ : syracuseStep 3258983 = 4888475) B4888475
theorem B2172655 : Blo 2171435 2172655 := bstep (se 1 (by rfl) ⟨1629491, by rfl⟩ : syracuseStep 2172655 = 3258983) B3258983
theorem B3258989 : Blo 2171435 3258989 := bbase (se 3 (by rfl) ⟨611060, by rfl⟩ : syracuseStep 3258989 = 1222121) (by norm_num)
theorem B2172659 : Blo 2171435 2172659 := bstep (se 1 (by rfl) ⟨1629494, by rfl⟩ : syracuseStep 2172659 = 3258989) B3258989
theorem B4888493 : Blo 2171435 4888493 := bbase (se 3 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 4888493 = 1833185) (by norm_num)
theorem B3258995 : Blo 2171435 3258995 := bstep (se 1 (by rfl) ⟨2444246, by rfl⟩ : syracuseStep 3258995 = 4888493) B4888493
theorem B2172663 : Blo 2171435 2172663 := bstep (se 1 (by rfl) ⟨1629497, by rfl⟩ : syracuseStep 2172663 = 3258995) B3258995
theorem B6187013 : Blo 2171435 6187013 := bbase (se 4 (by rfl) ⟨580032, by rfl⟩ : syracuseStep 6187013 = 1160065) (by norm_num)
theorem B4124675 : Blo 2171435 4124675 := bstep (se 1 (by rfl) ⟨3093506, by rfl⟩ : syracuseStep 4124675 = 6187013) B6187013
theorem B2749783 : Blo 2171435 2749783 := bstep (se 1 (by rfl) ⟨2062337, by rfl⟩ : syracuseStep 2749783 = 4124675) B4124675
theorem B3666377 : Blo 2171435 3666377 := bstep (se 2 (by rfl) ⟨1374891, by rfl⟩ : syracuseStep 3666377 = 2749783) B2749783
theorem B2444251 : Blo 2171435 2444251 := bstep (se 1 (by rfl) ⟨1833188, by rfl⟩ : syracuseStep 2444251 = 3666377) B3666377
theorem B3259001 : Blo 2171435 3259001 := bstep (se 2 (by rfl) ⟨1222125, by rfl⟩ : syracuseStep 3259001 = 2444251) B2444251
theorem B2172667 : Blo 2171435 2172667 := bstep (se 1 (by rfl) ⟨1629500, by rfl⟩ : syracuseStep 2172667 = 3259001) B3259001
theorem B4404629 : Blo 2171435 4404629 := bbase (se 6 (by rfl) ⟨103233, by rfl⟩ : syracuseStep 4404629 = 206467) (by norm_num)
theorem B11745677 : Blo 2171435 11745677 := bstep (se 3 (by rfl) ⟨2202314, by rfl⟩ : syracuseStep 11745677 = 4404629) B4404629
theorem B7830451 : Blo 2171435 7830451 := bstep (se 1 (by rfl) ⟨5872838, by rfl⟩ : syracuseStep 7830451 = 11745677) B11745677
theorem B41762405 : Blo 2171435 41762405 := bstep (se 4 (by rfl) ⟨3915225, by rfl⟩ : syracuseStep 41762405 = 7830451) B7830451
theorem B27841603 : Blo 2171435 27841603 := bstep (se 1 (by rfl) ⟨20881202, by rfl⟩ : syracuseStep 27841603 = 41762405) B41762405
theorem B37122137 : Blo 2171435 37122137 := bstep (se 2 (by rfl) ⟨13920801, by rfl⟩ : syracuseStep 37122137 = 27841603) B27841603
theorem B24748091 : Blo 2171435 24748091 := bstep (se 1 (by rfl) ⟨18561068, by rfl⟩ : syracuseStep 24748091 = 37122137) B37122137
theorem B16498727 : Blo 2171435 16498727 := bstep (se 1 (by rfl) ⟨12374045, by rfl⟩ : syracuseStep 16498727 = 24748091) B24748091
theorem B10999151 : Blo 2171435 10999151 := bstep (se 1 (by rfl) ⟨8249363, by rfl⟩ : syracuseStep 10999151 = 16498727) B16498727
theorem B7332767 : Blo 2171435 7332767 := bstep (se 1 (by rfl) ⟨5499575, by rfl⟩ : syracuseStep 7332767 = 10999151) B10999151
theorem B4888511 : Blo 2171435 4888511 := bstep (se 1 (by rfl) ⟨3666383, by rfl⟩ : syracuseStep 4888511 = 7332767) B7332767
theorem B3259007 : Blo 2171435 3259007 := bstep (se 1 (by rfl) ⟨2444255, by rfl⟩ : syracuseStep 3259007 = 4888511) B4888511
theorem B2172671 : Blo 2171435 2172671 := bstep (se 1 (by rfl) ⟨1629503, by rfl⟩ : syracuseStep 2172671 = 3259007) B3259007
theorem B3259013 : Blo 2171435 3259013 := bbase (se 4 (by rfl) ⟨305532, by rfl⟩ : syracuseStep 3259013 = 611065) (by norm_num)
theorem B2172675 : Blo 2171435 2172675 := bstep (se 1 (by rfl) ⟨1629506, by rfl⟩ : syracuseStep 2172675 = 3259013) B3259013
theorem B3666397 : Blo 2171435 3666397 := bbase (se 3 (by rfl) ⟨687449, by rfl⟩ : syracuseStep 3666397 = 1374899) (by norm_num)
theorem B4888529 : Blo 2171435 4888529 := bstep (se 2 (by rfl) ⟨1833198, by rfl⟩ : syracuseStep 4888529 = 3666397) B3666397
theorem B3259019 : Blo 2171435 3259019 := bstep (se 1 (by rfl) ⟨2444264, by rfl⟩ : syracuseStep 3259019 = 4888529) B4888529
theorem B2172679 : Blo 2171435 2172679 := bstep (se 1 (by rfl) ⟨1629509, by rfl⟩ : syracuseStep 2172679 = 3259019) B3259019
theorem B2444269 : Blo 2171435 2444269 := bbase (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) (by norm_num)
theorem B3259025 : Blo 2171435 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B2172683 : Blo 2171435 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B7332821 : Blo 2171435 7332821 := bbase (se 7 (by rfl) ⟨85931, by rfl⟩ : syracuseStep 7332821 = 171863) (by norm_num)
theorem B4888547 : Blo 2171435 4888547 := bstep (se 1 (by rfl) ⟨3666410, by rfl⟩ : syracuseStep 4888547 = 7332821) B7332821
theorem B3259031 : Blo 2171435 3259031 := bstep (se 1 (by rfl) ⟨2444273, by rfl⟩ : syracuseStep 3259031 = 4888547) B4888547
theorem B2172687 : Blo 2171435 2172687 := bstep (se 1 (by rfl) ⟨1629515, by rfl⟩ : syracuseStep 2172687 = 3259031) B3259031
theorem B3259037 : Blo 2171435 3259037 := bbase (se 3 (by rfl) ⟨611069, by rfl⟩ : syracuseStep 3259037 = 1222139) (by norm_num)
theorem B2172691 : Blo 2171435 2172691 := bstep (se 1 (by rfl) ⟨1629518, by rfl⟩ : syracuseStep 2172691 = 3259037) B3259037
theorem B4888565 : Blo 2171435 4888565 := bbase (se 5 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 4888565 = 458303) (by norm_num)
theorem B3259043 : Blo 2171435 3259043 := bstep (se 1 (by rfl) ⟨2444282, by rfl⟩ : syracuseStep 3259043 = 4888565) B4888565
theorem B2172695 : Blo 2171435 2172695 := bstep (se 1 (by rfl) ⟨1629521, by rfl⟩ : syracuseStep 2172695 = 3259043) B3259043
theorem B2645797 : Blo 2171435 2645797 := bbase (se 4 (by rfl) ⟨248043, by rfl⟩ : syracuseStep 2645797 = 496087) (by norm_num)
theorem B3527729 : Blo 2171435 3527729 := bstep (se 2 (by rfl) ⟨1322898, by rfl⟩ : syracuseStep 3527729 = 2645797) B2645797
theorem B2351819 : Blo 2171435 2351819 := bstep (se 1 (by rfl) ⟨1763864, by rfl⟩ : syracuseStep 2351819 = 3527729) B3527729
theorem B6271517 : Blo 2171435 6271517 := bstep (se 3 (by rfl) ⟨1175909, by rfl⟩ : syracuseStep 6271517 = 2351819) B2351819
theorem B16724045 : Blo 2171435 16724045 := bstep (se 3 (by rfl) ⟨3135758, by rfl⟩ : syracuseStep 16724045 = 6271517) B6271517
theorem B11149363 : Blo 2171435 11149363 := bstep (se 1 (by rfl) ⟨8362022, by rfl⟩ : syracuseStep 11149363 = 16724045) B16724045
theorem B14865817 : Blo 2171435 14865817 := bstep (se 2 (by rfl) ⟨5574681, by rfl⟩ : syracuseStep 14865817 = 11149363) B11149363
theorem B19821089 : Blo 2171435 19821089 := bstep (se 2 (by rfl) ⟨7432908, by rfl⟩ : syracuseStep 19821089 = 14865817) B14865817
theorem B13214059 : Blo 2171435 13214059 := bstep (se 1 (by rfl) ⟨9910544, by rfl⟩ : syracuseStep 13214059 = 19821089) B19821089
theorem B70474981 : Blo 2171435 70474981 := bstep (se 4 (by rfl) ⟨6607029, by rfl⟩ : syracuseStep 70474981 = 13214059) B13214059
theorem B93966641 : Blo 2171435 93966641 := bstep (se 2 (by rfl) ⟨35237490, by rfl⟩ : syracuseStep 93966641 = 70474981) B70474981
theorem B62644427 : Blo 2171435 62644427 := bstep (se 1 (by rfl) ⟨46983320, by rfl⟩ : syracuseStep 62644427 = 93966641) B93966641
theorem B41762951 : Blo 2171435 41762951 := bstep (se 1 (by rfl) ⟨31322213, by rfl⟩ : syracuseStep 41762951 = 62644427) B62644427
theorem B27841967 : Blo 2171435 27841967 := bstep (se 1 (by rfl) ⟨20881475, by rfl⟩ : syracuseStep 27841967 = 41762951) B41762951
theorem B18561311 : Blo 2171435 18561311 := bstep (se 1 (by rfl) ⟨13920983, by rfl⟩ : syracuseStep 18561311 = 27841967) B27841967
theorem B12374207 : Blo 2171435 12374207 := bstep (se 1 (by rfl) ⟨9280655, by rfl⟩ : syracuseStep 12374207 = 18561311) B18561311
theorem B8249471 : Blo 2171435 8249471 := bstep (se 1 (by rfl) ⟨6187103, by rfl⟩ : syracuseStep 8249471 = 12374207) B12374207
theorem B5499647 : Blo 2171435 5499647 := bstep (se 1 (by rfl) ⟨4124735, by rfl⟩ : syracuseStep 5499647 = 8249471) B8249471
theorem B3666431 : Blo 2171435 3666431 := bstep (se 1 (by rfl) ⟨2749823, by rfl⟩ : syracuseStep 3666431 = 5499647) B5499647
theorem B2444287 : Blo 2171435 2444287 := bstep (se 1 (by rfl) ⟨1833215, by rfl⟩ : syracuseStep 2444287 = 3666431) B3666431
theorem B3259049 : Blo 2171435 3259049 := bstep (se 2 (by rfl) ⟨1222143, by rfl⟩ : syracuseStep 3259049 = 2444287) B2444287
theorem B2172699 : Blo 2171435 2172699 := bstep (se 1 (by rfl) ⟨1629524, by rfl⟩ : syracuseStep 2172699 = 3259049) B3259049
theorem B3093557 : Blo 2171435 3093557 := bbase (se 5 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 3093557 = 290021) (by norm_num)
theorem B8249485 : Blo 2171435 8249485 := bstep (se 3 (by rfl) ⟨1546778, by rfl⟩ : syracuseStep 8249485 = 3093557) B3093557
theorem B10999313 : Blo 2171435 10999313 := bstep (se 2 (by rfl) ⟨4124742, by rfl⟩ : syracuseStep 10999313 = 8249485) B8249485
theorem B7332875 : Blo 2171435 7332875 := bstep (se 1 (by rfl) ⟨5499656, by rfl⟩ : syracuseStep 7332875 = 10999313) B10999313
theorem B4888583 : Blo 2171435 4888583 := bstep (se 1 (by rfl) ⟨3666437, by rfl⟩ : syracuseStep 4888583 = 7332875) B7332875
theorem B3259055 : Blo 2171435 3259055 := bstep (se 1 (by rfl) ⟨2444291, by rfl⟩ : syracuseStep 3259055 = 4888583) B4888583
theorem B2172703 : Blo 2171435 2172703 := bstep (se 1 (by rfl) ⟨1629527, by rfl⟩ : syracuseStep 2172703 = 3259055) B3259055
theorem B3259061 : Blo 2171435 3259061 := bbase (se 5 (by rfl) ⟨152768, by rfl⟩ : syracuseStep 3259061 = 305537) (by norm_num)
theorem B2172707 : Blo 2171435 2172707 := bstep (se 1 (by rfl) ⟨1629530, by rfl⟩ : syracuseStep 2172707 = 3259061) B3259061
theorem B5499677 : Blo 2171435 5499677 := bbase (se 3 (by rfl) ⟨1031189, by rfl⟩ : syracuseStep 5499677 = 2062379) (by norm_num)
theorem B3666451 : Blo 2171435 3666451 := bstep (se 1 (by rfl) ⟨2749838, by rfl⟩ : syracuseStep 3666451 = 5499677) B5499677
theorem B4888601 : Blo 2171435 4888601 := bstep (se 2 (by rfl) ⟨1833225, by rfl⟩ : syracuseStep 4888601 = 3666451) B3666451
theorem B3259067 : Blo 2171435 3259067 := bstep (se 1 (by rfl) ⟨2444300, by rfl⟩ : syracuseStep 3259067 = 4888601) B4888601
theorem B2172711 : Blo 2171435 2172711 := bstep (se 1 (by rfl) ⟨1629533, by rfl⟩ : syracuseStep 2172711 = 3259067) B3259067
theorem B2444305 : Blo 2171435 2444305 := bbase (se 2 (by rfl) ⟨916614, by rfl⟩ : syracuseStep 2444305 = 1833229) (by norm_num)
theorem B3259073 : Blo 2171435 3259073 := bstep (se 2 (by rfl) ⟨1222152, by rfl⟩ : syracuseStep 3259073 = 2444305) B2444305
theorem B2172715 : Blo 2171435 2172715 := bstep (se 1 (by rfl) ⟨1629536, by rfl⟩ : syracuseStep 2172715 = 3259073) B3259073
theorem B4124773 : Blo 2171435 4124773 := bbase (se 4 (by rfl) ⟨386697, by rfl⟩ : syracuseStep 4124773 = 773395) (by norm_num)
theorem B5499697 : Blo 2171435 5499697 := bstep (se 2 (by rfl) ⟨2062386, by rfl⟩ : syracuseStep 5499697 = 4124773) B4124773
theorem B7332929 : Blo 2171435 7332929 := bstep (se 2 (by rfl) ⟨2749848, by rfl⟩ : syracuseStep 7332929 = 5499697) B5499697
theorem B4888619 : Blo 2171435 4888619 := bstep (se 1 (by rfl) ⟨3666464, by rfl⟩ : syracuseStep 4888619 = 7332929) B7332929
theorem B3259079 : Blo 2171435 3259079 := bstep (se 1 (by rfl) ⟨2444309, by rfl⟩ : syracuseStep 3259079 = 4888619) B4888619
theorem B2172719 : Blo 2171435 2172719 := bstep (se 1 (by rfl) ⟨1629539, by rfl⟩ : syracuseStep 2172719 = 3259079) B3259079
theorem B3259085 : Blo 2171435 3259085 := bbase (se 3 (by rfl) ⟨611078, by rfl⟩ : syracuseStep 3259085 = 1222157) (by norm_num)
theorem B2172723 : Blo 2171435 2172723 := bstep (se 1 (by rfl) ⟨1629542, by rfl⟩ : syracuseStep 2172723 = 3259085) B3259085
theorem B4888637 : Blo 2171435 4888637 := bbase (se 3 (by rfl) ⟨916619, by rfl⟩ : syracuseStep 4888637 = 1833239) (by norm_num)
theorem B3259091 : Blo 2171435 3259091 := bstep (se 1 (by rfl) ⟨2444318, by rfl⟩ : syracuseStep 3259091 = 4888637) B4888637
theorem B2172727 : Blo 2171435 2172727 := bstep (se 1 (by rfl) ⟨1629545, by rfl⟩ : syracuseStep 2172727 = 3259091) B3259091
theorem B3666485 : Blo 2171435 3666485 := bbase (se 5 (by rfl) ⟨171866, by rfl⟩ : syracuseStep 3666485 = 343733) (by norm_num)
theorem B2444323 : Blo 2171435 2444323 := bstep (se 1 (by rfl) ⟨1833242, by rfl⟩ : syracuseStep 2444323 = 3666485) B3666485
theorem B3259097 : Blo 2171435 3259097 := bstep (se 2 (by rfl) ⟨1222161, by rfl⟩ : syracuseStep 3259097 = 2444323) B2444323
theorem B2172731 : Blo 2171435 2172731 := bstep (se 1 (by rfl) ⟨1629548, by rfl⟩ : syracuseStep 2172731 = 3259097) B3259097
theorem B6187205 : Blo 2171435 6187205 := bbase (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) (by norm_num)
theorem B16499213 : Blo 2171435 16499213 := bstep (se 3 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 16499213 = 6187205) B6187205
theorem B10999475 : Blo 2171435 10999475 := bstep (se 1 (by rfl) ⟨8249606, by rfl⟩ : syracuseStep 10999475 = 16499213) B16499213
theorem B7332983 : Blo 2171435 7332983 := bstep (se 1 (by rfl) ⟨5499737, by rfl⟩ : syracuseStep 7332983 = 10999475) B10999475
theorem B4888655 : Blo 2171435 4888655 := bstep (se 1 (by rfl) ⟨3666491, by rfl⟩ : syracuseStep 4888655 = 7332983) B7332983
theorem B3259103 : Blo 2171435 3259103 := bstep (se 1 (by rfl) ⟨2444327, by rfl⟩ : syracuseStep 3259103 = 4888655) B4888655
theorem B2172735 : Blo 2171435 2172735 := bstep (se 1 (by rfl) ⟨1629551, by rfl⟩ : syracuseStep 2172735 = 3259103) B3259103
theorem B3259109 : Blo 2171435 3259109 := bbase (se 4 (by rfl) ⟨305541, by rfl⟩ : syracuseStep 3259109 = 611083) (by norm_num)
theorem B2172739 : Blo 2171435 2172739 := bstep (se 1 (by rfl) ⟨1629554, by rfl⟩ : syracuseStep 2172739 = 3259109) B3259109
theorem B3480317 : Blo 2171435 3480317 := bbase (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) (by norm_num)
theorem B2320211 : Blo 2171435 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B6187229 : Blo 2171435 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B4124819 : Blo 2171435 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B2749879 : Blo 2171435 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B3666505 : Blo 2171435 3666505 := bstep (se 2 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 3666505 = 2749879) B2749879
theorem B4888673 : Blo 2171435 4888673 := bstep (se 2 (by rfl) ⟨1833252, by rfl⟩ : syracuseStep 4888673 = 3666505) B3666505
theorem B3259115 : Blo 2171435 3259115 := bstep (se 1 (by rfl) ⟨2444336, by rfl⟩ : syracuseStep 3259115 = 4888673) B4888673
theorem B2172743 : Blo 2171435 2172743 := bstep (se 1 (by rfl) ⟨1629557, by rfl⟩ : syracuseStep 2172743 = 3259115) B3259115
theorem B2444341 : Blo 2171435 2444341 := bbase (se 5 (by rfl) ⟨114578, by rfl⟩ : syracuseStep 2444341 = 229157) (by norm_num)
theorem B3259121 : Blo 2171435 3259121 := bstep (se 2 (by rfl) ⟨1222170, by rfl⟩ : syracuseStep 3259121 = 2444341) B2444341
theorem B2172747 : Blo 2171435 2172747 := bstep (se 1 (by rfl) ⟨1629560, by rfl⟩ : syracuseStep 2172747 = 3259121) B3259121
theorem B2749889 : Blo 2171435 2749889 := bbase (se 2 (by rfl) ⟨1031208, by rfl⟩ : syracuseStep 2749889 = 2062417) (by norm_num)
theorem B7333037 : Blo 2171435 7333037 := bstep (se 3 (by rfl) ⟨1374944, by rfl⟩ : syracuseStep 7333037 = 2749889) B2749889
theorem B4888691 : Blo 2171435 4888691 := bstep (se 1 (by rfl) ⟨3666518, by rfl⟩ : syracuseStep 4888691 = 7333037) B7333037
theorem B3259127 : Blo 2171435 3259127 := bstep (se 1 (by rfl) ⟨2444345, by rfl⟩ : syracuseStep 3259127 = 4888691) B4888691
theorem B2172751 : Blo 2171435 2172751 := bstep (se 1 (by rfl) ⟨1629563, by rfl⟩ : syracuseStep 2172751 = 3259127) B3259127
theorem B3259133 : Blo 2171435 3259133 := bbase (se 3 (by rfl) ⟨611087, by rfl⟩ : syracuseStep 3259133 = 1222175) (by norm_num)
theorem B2172755 : Blo 2171435 2172755 := bstep (se 1 (by rfl) ⟨1629566, by rfl⟩ : syracuseStep 2172755 = 3259133) B3259133
theorem B4888709 : Blo 2171435 4888709 := bbase (se 4 (by rfl) ⟨458316, by rfl⟩ : syracuseStep 4888709 = 916633) (by norm_num)
theorem B3259139 : Blo 2171435 3259139 := bstep (se 1 (by rfl) ⟨2444354, by rfl⟩ : syracuseStep 3259139 = 4888709) B4888709
theorem B2172759 : Blo 2171435 2172759 := bstep (se 1 (by rfl) ⟨1629569, by rfl⟩ : syracuseStep 2172759 = 3259139) B3259139
theorem B3480349 : Blo 2171435 3480349 := bbase (se 3 (by rfl) ⟨652565, by rfl⟩ : syracuseStep 3480349 = 1305131) (by norm_num)
theorem B4640465 : Blo 2171435 4640465 := bstep (se 2 (by rfl) ⟨1740174, by rfl⟩ : syracuseStep 4640465 = 3480349) B3480349
theorem B3093643 : Blo 2171435 3093643 := bstep (se 1 (by rfl) ⟨2320232, by rfl⟩ : syracuseStep 3093643 = 4640465) B4640465
theorem B4124857 : Blo 2171435 4124857 := bstep (se 2 (by rfl) ⟨1546821, by rfl⟩ : syracuseStep 4124857 = 3093643) B3093643
theorem B5499809 : Blo 2171435 5499809 := bstep (se 2 (by rfl) ⟨2062428, by rfl⟩ : syracuseStep 5499809 = 4124857) B4124857
theorem B3666539 : Blo 2171435 3666539 := bstep (se 1 (by rfl) ⟨2749904, by rfl⟩ : syracuseStep 3666539 = 5499809) B5499809
theorem B2444359 : Blo 2171435 2444359 := bstep (se 1 (by rfl) ⟨1833269, by rfl⟩ : syracuseStep 2444359 = 3666539) B3666539
theorem B3259145 : Blo 2171435 3259145 := bstep (se 2 (by rfl) ⟨1222179, by rfl⟩ : syracuseStep 3259145 = 2444359) B2444359
theorem B2172763 : Blo 2171435 2172763 := bstep (se 1 (by rfl) ⟨1629572, by rfl⟩ : syracuseStep 2172763 = 3259145) B3259145
theorem B10999637 : Blo 2171435 10999637 := bbase (se 9 (by rfl) ⟨32225, by rfl⟩ : syracuseStep 10999637 = 64451) (by norm_num)
theorem B7333091 : Blo 2171435 7333091 := bstep (se 1 (by rfl) ⟨5499818, by rfl⟩ : syracuseStep 7333091 = 10999637) B10999637
theorem B4888727 : Blo 2171435 4888727 := bstep (se 1 (by rfl) ⟨3666545, by rfl⟩ : syracuseStep 4888727 = 7333091) B7333091
theorem B3259151 : Blo 2171435 3259151 := bstep (se 1 (by rfl) ⟨2444363, by rfl⟩ : syracuseStep 3259151 = 4888727) B4888727
theorem B2172767 : Blo 2171435 2172767 := bstep (se 1 (by rfl) ⟨1629575, by rfl⟩ : syracuseStep 2172767 = 3259151) B3259151
theorem B3259157 : Blo 2171435 3259157 := bbase (se 6 (by rfl) ⟨76386, by rfl⟩ : syracuseStep 3259157 = 152773) (by norm_num)
theorem B2172771 : Blo 2171435 2172771 := bstep (se 1 (by rfl) ⟨1629578, by rfl⟩ : syracuseStep 2172771 = 3259157) B3259157
theorem B19821781 : Blo 2171435 19821781 := bbase (se 7 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 19821781 = 464573) (by norm_num)
theorem B26429041 : Blo 2171435 26429041 := bstep (se 2 (by rfl) ⟨9910890, by rfl⟩ : syracuseStep 26429041 = 19821781) B19821781
theorem B35238721 : Blo 2171435 35238721 := bstep (se 2 (by rfl) ⟨13214520, by rfl⟩ : syracuseStep 35238721 = 26429041) B26429041
theorem B46984961 : Blo 2171435 46984961 := bstep (se 2 (by rfl) ⟨17619360, by rfl⟩ : syracuseStep 46984961 = 35238721) B35238721
theorem B31323307 : Blo 2171435 31323307 := bstep (se 1 (by rfl) ⟨23492480, by rfl⟩ : syracuseStep 31323307 = 46984961) B46984961
theorem B41764409 : Blo 2171435 41764409 := bstep (se 2 (by rfl) ⟨15661653, by rfl⟩ : syracuseStep 41764409 = 31323307) B31323307
theorem B27842939 : Blo 2171435 27842939 := bstep (se 1 (by rfl) ⟨20882204, by rfl⟩ : syracuseStep 27842939 = 41764409) B41764409
theorem B18561959 : Blo 2171435 18561959 := bstep (se 1 (by rfl) ⟨13921469, by rfl⟩ : syracuseStep 18561959 = 27842939) B27842939
theorem B12374639 : Blo 2171435 12374639 := bstep (se 1 (by rfl) ⟨9280979, by rfl⟩ : syracuseStep 12374639 = 18561959) B18561959
theorem B8249759 : Blo 2171435 8249759 := bstep (se 1 (by rfl) ⟨6187319, by rfl⟩ : syracuseStep 8249759 = 12374639) B12374639
theorem B5499839 : Blo 2171435 5499839 := bstep (se 1 (by rfl) ⟨4124879, by rfl⟩ : syracuseStep 5499839 = 8249759) B8249759
theorem B3666559 : Blo 2171435 3666559 := bstep (se 1 (by rfl) ⟨2749919, by rfl⟩ : syracuseStep 3666559 = 5499839) B5499839
theorem B4888745 : Blo 2171435 4888745 := bstep (se 2 (by rfl) ⟨1833279, by rfl⟩ : syracuseStep 4888745 = 3666559) B3666559
theorem B3259163 : Blo 2171435 3259163 := bstep (se 1 (by rfl) ⟨2444372, by rfl⟩ : syracuseStep 3259163 = 4888745) B4888745
theorem B2172775 : Blo 2171435 2172775 := bstep (se 1 (by rfl) ⟨1629581, by rfl⟩ : syracuseStep 2172775 = 3259163) B3259163
theorem B2444377 : Blo 2171435 2444377 := bbase (se 2 (by rfl) ⟨916641, by rfl⟩ : syracuseStep 2444377 = 1833283) (by norm_num)
theorem B3259169 : Blo 2171435 3259169 := bstep (se 2 (by rfl) ⟨1222188, by rfl⟩ : syracuseStep 3259169 = 2444377) B2444377
theorem B2172779 : Blo 2171435 2172779 := bstep (se 1 (by rfl) ⟨1629584, by rfl⟩ : syracuseStep 2172779 = 3259169) B3259169
theorem B4525877 : Blo 2171435 4525877 := bbase (se 5 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 4525877 = 424301) (by norm_num)
theorem B12069005 : Blo 2171435 12069005 := bstep (se 3 (by rfl) ⟨2262938, by rfl⟩ : syracuseStep 12069005 = 4525877) B4525877
theorem B32184013 : Blo 2171435 32184013 := bstep (se 3 (by rfl) ⟨6034502, by rfl⟩ : syracuseStep 32184013 = 12069005) B12069005
theorem B42912017 : Blo 2171435 42912017 := bstep (se 2 (by rfl) ⟨16092006, by rfl⟩ : syracuseStep 42912017 = 32184013) B32184013
theorem B28608011 : Blo 2171435 28608011 := bstep (se 1 (by rfl) ⟨21456008, by rfl⟩ : syracuseStep 28608011 = 42912017) B42912017
theorem B19072007 : Blo 2171435 19072007 := bstep (se 1 (by rfl) ⟨14304005, by rfl⟩ : syracuseStep 19072007 = 28608011) B28608011
theorem B12714671 : Blo 2171435 12714671 := bstep (se 1 (by rfl) ⟨9536003, by rfl⟩ : syracuseStep 12714671 = 19072007) B19072007
theorem B8476447 : Blo 2171435 8476447 := bstep (se 1 (by rfl) ⟨6357335, by rfl⟩ : syracuseStep 8476447 = 12714671) B12714671
theorem B11301929 : Blo 2171435 11301929 := bstep (se 2 (by rfl) ⟨4238223, by rfl⟩ : syracuseStep 11301929 = 8476447) B8476447
theorem B7534619 : Blo 2171435 7534619 := bstep (se 1 (by rfl) ⟨5650964, by rfl⟩ : syracuseStep 7534619 = 11301929) B11301929
theorem B5023079 : Blo 2171435 5023079 := bstep (se 1 (by rfl) ⟨3767309, by rfl⟩ : syracuseStep 5023079 = 7534619) B7534619
theorem B3348719 : Blo 2171435 3348719 := bstep (se 1 (by rfl) ⟨2511539, by rfl⟩ : syracuseStep 3348719 = 5023079) B5023079
theorem B2232479 : Blo 2171435 2232479 := bstep (se 1 (by rfl) ⟨1674359, by rfl⟩ : syracuseStep 2232479 = 3348719) B3348719
theorem B5953277 : Blo 2171435 5953277 := bstep (se 3 (by rfl) ⟨1116239, by rfl⟩ : syracuseStep 5953277 = 2232479) B2232479
theorem B3968851 : Blo 2171435 3968851 := bstep (se 1 (by rfl) ⟨2976638, by rfl⟩ : syracuseStep 3968851 = 5953277) B5953277
theorem B5291801 : Blo 2171435 5291801 := bstep (se 2 (by rfl) ⟨1984425, by rfl⟩ : syracuseStep 5291801 = 3968851) B3968851
theorem B3527867 : Blo 2171435 3527867 := bstep (se 1 (by rfl) ⟨2645900, by rfl⟩ : syracuseStep 3527867 = 5291801) B5291801
theorem B2351911 : Blo 2171435 2351911 := bstep (se 1 (by rfl) ⟨1763933, by rfl⟩ : syracuseStep 2351911 = 3527867) B3527867
theorem B3135881 : Blo 2171435 3135881 := bstep (se 2 (by rfl) ⟨1175955, by rfl⟩ : syracuseStep 3135881 = 2351911) B2351911
theorem B8362349 : Blo 2171435 8362349 := bstep (se 3 (by rfl) ⟨1567940, by rfl⟩ : syracuseStep 8362349 = 3135881) B3135881
theorem B5574899 : Blo 2171435 5574899 := bstep (se 1 (by rfl) ⟨4181174, by rfl⟩ : syracuseStep 5574899 = 8362349) B8362349
theorem B3716599 : Blo 2171435 3716599 := bstep (se 1 (by rfl) ⟨2787449, by rfl⟩ : syracuseStep 3716599 = 5574899) B5574899
theorem B4955465 : Blo 2171435 4955465 := bstep (se 2 (by rfl) ⟨1858299, by rfl⟩ : syracuseStep 4955465 = 3716599) B3716599
theorem B13214573 : Blo 2171435 13214573 := bstep (se 3 (by rfl) ⟨2477732, by rfl⟩ : syracuseStep 13214573 = 4955465) B4955465
theorem B8809715 : Blo 2171435 8809715 := bstep (se 1 (by rfl) ⟨6607286, by rfl⟩ : syracuseStep 8809715 = 13214573) B13214573
theorem B5873143 : Blo 2171435 5873143 := bstep (se 1 (by rfl) ⟨4404857, by rfl⟩ : syracuseStep 5873143 = 8809715) B8809715
theorem B7830857 : Blo 2171435 7830857 := bstep (se 2 (by rfl) ⟨2936571, by rfl⟩ : syracuseStep 7830857 = 5873143) B5873143
theorem B5220571 : Blo 2171435 5220571 := bstep (se 1 (by rfl) ⟨3915428, by rfl⟩ : syracuseStep 5220571 = 7830857) B7830857
theorem B6960761 : Blo 2171435 6960761 := bstep (se 2 (by rfl) ⟨2610285, by rfl⟩ : syracuseStep 6960761 = 5220571) B5220571
theorem B4640507 : Blo 2171435 4640507 := bstep (se 1 (by rfl) ⟨3480380, by rfl⟩ : syracuseStep 4640507 = 6960761) B6960761
theorem B3093671 : Blo 2171435 3093671 := bstep (se 1 (by rfl) ⟨2320253, by rfl⟩ : syracuseStep 3093671 = 4640507) B4640507
theorem B8249789 : Blo 2171435 8249789 := bstep (se 3 (by rfl) ⟨1546835, by rfl⟩ : syracuseStep 8249789 = 3093671) B3093671
theorem B5499859 : Blo 2171435 5499859 := bstep (se 1 (by rfl) ⟨4124894, by rfl⟩ : syracuseStep 5499859 = 8249789) B8249789
theorem B7333145 : Blo 2171435 7333145 := bstep (se 2 (by rfl) ⟨2749929, by rfl⟩ : syracuseStep 7333145 = 5499859) B5499859
theorem B4888763 : Blo 2171435 4888763 := bstep (se 1 (by rfl) ⟨3666572, by rfl⟩ : syracuseStep 4888763 = 7333145) B7333145
theorem B3259175 : Blo 2171435 3259175 := bstep (se 1 (by rfl) ⟨2444381, by rfl⟩ : syracuseStep 3259175 = 4888763) B4888763
theorem B2172783 : Blo 2171435 2172783 := bstep (se 1 (by rfl) ⟨1629587, by rfl⟩ : syracuseStep 2172783 = 3259175) B3259175
theorem B3259181 : Blo 2171435 3259181 := bbase (se 3 (by rfl) ⟨611096, by rfl⟩ : syracuseStep 3259181 = 1222193) (by norm_num)
theorem B2172787 : Blo 2171435 2172787 := bstep (se 1 (by rfl) ⟨1629590, by rfl⟩ : syracuseStep 2172787 = 3259181) B3259181
theorem B4888781 : Blo 2171435 4888781 := bbase (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) (by norm_num)
theorem B3259187 : Blo 2171435 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B2172791 : Blo 2171435 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B2749945 : Blo 2171435 2749945 := bbase (se 2 (by rfl) ⟨1031229, by rfl⟩ : syracuseStep 2749945 = 2062459) (by norm_num)
theorem B3666593 : Blo 2171435 3666593 := bstep (se 2 (by rfl) ⟨1374972, by rfl⟩ : syracuseStep 3666593 = 2749945) B2749945
theorem B2444395 : Blo 2171435 2444395 := bstep (se 1 (by rfl) ⟨1833296, by rfl⟩ : syracuseStep 2444395 = 3666593) B3666593
theorem B3259193 : Blo 2171435 3259193 := bstep (se 2 (by rfl) ⟨1222197, by rfl⟩ : syracuseStep 3259193 = 2444395) B2444395
theorem B2172795 : Blo 2171435 2172795 := bstep (se 1 (by rfl) ⟨1629596, by rfl⟩ : syracuseStep 2172795 = 3259193) B3259193
theorem B4955501 : Blo 2171435 4955501 := bbase (se 3 (by rfl) ⟨929156, by rfl⟩ : syracuseStep 4955501 = 1858313) (by norm_num)
theorem B3303667 : Blo 2171435 3303667 := bstep (se 1 (by rfl) ⟨2477750, by rfl⟩ : syracuseStep 3303667 = 4955501) B4955501
theorem B4404889 : Blo 2171435 4404889 := bstep (se 2 (by rfl) ⟨1651833, by rfl⟩ : syracuseStep 4404889 = 3303667) B3303667
theorem B5873185 : Blo 2171435 5873185 := bstep (se 2 (by rfl) ⟨2202444, by rfl⟩ : syracuseStep 5873185 = 4404889) B4404889
theorem B7830913 : Blo 2171435 7830913 := bstep (se 2 (by rfl) ⟨2936592, by rfl⟩ : syracuseStep 7830913 = 5873185) B5873185
theorem B10441217 : Blo 2171435 10441217 := bstep (se 2 (by rfl) ⟨3915456, by rfl⟩ : syracuseStep 10441217 = 7830913) B7830913
theorem B6960811 : Blo 2171435 6960811 := bstep (se 1 (by rfl) ⟨5220608, by rfl⟩ : syracuseStep 6960811 = 10441217) B10441217
theorem B9281081 : Blo 2171435 9281081 := bstep (se 2 (by rfl) ⟨3480405, by rfl⟩ : syracuseStep 9281081 = 6960811) B6960811
theorem B24749549 : Blo 2171435 24749549 := bstep (se 3 (by rfl) ⟨4640540, by rfl⟩ : syracuseStep 24749549 = 9281081) B9281081
theorem B16499699 : Blo 2171435 16499699 := bstep (se 1 (by rfl) ⟨12374774, by rfl⟩ : syracuseStep 16499699 = 24749549) B24749549
theorem B10999799 : Blo 2171435 10999799 := bstep (se 1 (by rfl) ⟨8249849, by rfl⟩ : syracuseStep 10999799 = 16499699) B16499699
theorem B7333199 : Blo 2171435 7333199 := bstep (se 1 (by rfl) ⟨5499899, by rfl⟩ : syracuseStep 7333199 = 10999799) B10999799
theorem B4888799 : Blo 2171435 4888799 := bstep (se 1 (by rfl) ⟨3666599, by rfl⟩ : syracuseStep 4888799 = 7333199) B7333199
theorem B3259199 : Blo 2171435 3259199 := bstep (se 1 (by rfl) ⟨2444399, by rfl⟩ : syracuseStep 3259199 = 4888799) B4888799
theorem B2172799 : Blo 2171435 2172799 := bstep (se 1 (by rfl) ⟨1629599, by rfl⟩ : syracuseStep 2172799 = 3259199) B3259199
theorem B3259205 : Blo 2171435 3259205 := bbase (se 4 (by rfl) ⟨305550, by rfl⟩ : syracuseStep 3259205 = 611101) (by norm_num)
theorem B2172803 : Blo 2171435 2172803 := bstep (se 1 (by rfl) ⟨1629602, by rfl⟩ : syracuseStep 2172803 = 3259205) B3259205
theorem B3666613 : Blo 2171435 3666613 := bbase (se 5 (by rfl) ⟨171872, by rfl⟩ : syracuseStep 3666613 = 343745) (by norm_num)
theorem B4888817 : Blo 2171435 4888817 := bstep (se 2 (by rfl) ⟨1833306, by rfl⟩ : syracuseStep 4888817 = 3666613) B3666613
theorem B3259211 : Blo 2171435 3259211 := bstep (se 1 (by rfl) ⟨2444408, by rfl⟩ : syracuseStep 3259211 = 4888817) B4888817
theorem B2172807 : Blo 2171435 2172807 := bstep (se 1 (by rfl) ⟨1629605, by rfl⟩ : syracuseStep 2172807 = 3259211) B3259211
theorem B2444413 : Blo 2171435 2444413 := bbase (se 3 (by rfl) ⟨458327, by rfl⟩ : syracuseStep 2444413 = 916655) (by norm_num)
theorem B3259217 : Blo 2171435 3259217 := bstep (se 2 (by rfl) ⟨1222206, by rfl⟩ : syracuseStep 3259217 = 2444413) B2444413
theorem B2172811 : Blo 2171435 2172811 := bstep (se 1 (by rfl) ⟨1629608, by rfl⟩ : syracuseStep 2172811 = 3259217) B3259217
theorem B7333253 : Blo 2171435 7333253 := bbase (se 4 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 7333253 = 1374985) (by norm_num)
theorem B4888835 : Blo 2171435 4888835 := bstep (se 1 (by rfl) ⟨3666626, by rfl⟩ : syracuseStep 4888835 = 7333253) B7333253
theorem B3259223 : Blo 2171435 3259223 := bstep (se 1 (by rfl) ⟨2444417, by rfl⟩ : syracuseStep 3259223 = 4888835) B4888835
theorem B2172815 : Blo 2171435 2172815 := bstep (se 1 (by rfl) ⟨1629611, by rfl⟩ : syracuseStep 2172815 = 3259223) B3259223
theorem B3259229 : Blo 2171435 3259229 := bbase (se 3 (by rfl) ⟨611105, by rfl⟩ : syracuseStep 3259229 = 1222211) (by norm_num)
theorem B2172819 : Blo 2171435 2172819 := bstep (se 1 (by rfl) ⟨1629614, by rfl⟩ : syracuseStep 2172819 = 3259229) B3259229
theorem B4888853 : Blo 2171435 4888853 := bbase (se 6 (by rfl) ⟨114582, by rfl⟩ : syracuseStep 4888853 = 229165) (by norm_num)
theorem B3259235 : Blo 2171435 3259235 := bstep (se 1 (by rfl) ⟨2444426, by rfl⟩ : syracuseStep 3259235 = 4888853) B4888853
theorem B2172823 : Blo 2171435 2172823 := bstep (se 1 (by rfl) ⟨1629617, by rfl⟩ : syracuseStep 2172823 = 3259235) B3259235
theorem B8249957 : Blo 2171435 8249957 := bbase (se 4 (by rfl) ⟨773433, by rfl⟩ : syracuseStep 8249957 = 1546867) (by norm_num)
theorem B5499971 : Blo 2171435 5499971 := bstep (se 1 (by rfl) ⟨4124978, by rfl⟩ : syracuseStep 5499971 = 8249957) B8249957
theorem B3666647 : Blo 2171435 3666647 := bstep (se 1 (by rfl) ⟨2749985, by rfl⟩ : syracuseStep 3666647 = 5499971) B5499971
theorem B2444431 : Blo 2171435 2444431 := bstep (se 1 (by rfl) ⟨1833323, by rfl⟩ : syracuseStep 2444431 = 3666647) B3666647
theorem B3259241 : Blo 2171435 3259241 := bstep (se 2 (by rfl) ⟨1222215, by rfl⟩ : syracuseStep 3259241 = 2444431) B2444431
theorem B2172827 : Blo 2171435 2172827 := bstep (se 1 (by rfl) ⟨1629620, by rfl⟩ : syracuseStep 2172827 = 3259241) B3259241
theorem B2825545 : Blo 2171435 2825545 := bbase (se 2 (by rfl) ⟨1059579, by rfl⟩ : syracuseStep 2825545 = 2119159) (by norm_num)
theorem B3767393 : Blo 2171435 3767393 := bstep (se 2 (by rfl) ⟨1412772, by rfl⟩ : syracuseStep 3767393 = 2825545) B2825545
theorem B2511595 : Blo 2171435 2511595 := bstep (se 1 (by rfl) ⟨1883696, by rfl⟩ : syracuseStep 2511595 = 3767393) B3767393
theorem B3348793 : Blo 2171435 3348793 := bstep (se 2 (by rfl) ⟨1255797, by rfl⟩ : syracuseStep 3348793 = 2511595) B2511595
theorem B4465057 : Blo 2171435 4465057 := bstep (se 2 (by rfl) ⟨1674396, by rfl⟩ : syracuseStep 4465057 = 3348793) B3348793
theorem B5953409 : Blo 2171435 5953409 := bstep (se 2 (by rfl) ⟨2232528, by rfl⟩ : syracuseStep 5953409 = 4465057) B4465057
theorem B3968939 : Blo 2171435 3968939 := bstep (se 1 (by rfl) ⟨2976704, by rfl⟩ : syracuseStep 3968939 = 5953409) B5953409
theorem B2645959 : Blo 2171435 2645959 := bstep (se 1 (by rfl) ⟨1984469, by rfl⟩ : syracuseStep 2645959 = 3968939) B3968939
theorem B3527945 : Blo 2171435 3527945 := bstep (se 2 (by rfl) ⟨1322979, by rfl⟩ : syracuseStep 3527945 = 2645959) B2645959
theorem B2351963 : Blo 2171435 2351963 := bstep (se 1 (by rfl) ⟨1763972, by rfl⟩ : syracuseStep 2351963 = 3527945) B3527945
theorem B6271901 : Blo 2171435 6271901 := bstep (se 3 (by rfl) ⟨1175981, by rfl⟩ : syracuseStep 6271901 = 2351963) B2351963
theorem B4181267 : Blo 2171435 4181267 := bstep (se 1 (by rfl) ⟨3135950, by rfl⟩ : syracuseStep 4181267 = 6271901) B6271901
theorem B11150045 : Blo 2171435 11150045 := bstep (se 3 (by rfl) ⟨2090633, by rfl⟩ : syracuseStep 11150045 = 4181267) B4181267
theorem B7433363 : Blo 2171435 7433363 := bstep (se 1 (by rfl) ⟨5575022, by rfl⟩ : syracuseStep 7433363 = 11150045) B11150045
theorem B4955575 : Blo 2171435 4955575 := bstep (se 1 (by rfl) ⟨3716681, by rfl⟩ : syracuseStep 4955575 = 7433363) B7433363
theorem B6607433 : Blo 2171435 6607433 := bstep (se 2 (by rfl) ⟨2477787, by rfl⟩ : syracuseStep 6607433 = 4955575) B4955575
theorem B4404955 : Blo 2171435 4404955 := bstep (se 1 (by rfl) ⟨3303716, by rfl⟩ : syracuseStep 4404955 = 6607433) B6607433
theorem B5873273 : Blo 2171435 5873273 := bstep (se 2 (by rfl) ⟨2202477, by rfl⟩ : syracuseStep 5873273 = 4404955) B4404955
theorem B3915515 : Blo 2171435 3915515 := bstep (se 1 (by rfl) ⟨2936636, by rfl⟩ : syracuseStep 3915515 = 5873273) B5873273
theorem B2610343 : Blo 2171435 2610343 := bstep (se 1 (by rfl) ⟨1957757, by rfl⟩ : syracuseStep 2610343 = 3915515) B3915515
theorem B3480457 : Blo 2171435 3480457 := bstep (se 2 (by rfl) ⟨1305171, by rfl⟩ : syracuseStep 3480457 = 2610343) B2610343
theorem B4640609 : Blo 2171435 4640609 := bstep (se 2 (by rfl) ⟨1740228, by rfl⟩ : syracuseStep 4640609 = 3480457) B3480457
theorem B12374957 : Blo 2171435 12374957 := bstep (se 3 (by rfl) ⟨2320304, by rfl⟩ : syracuseStep 12374957 = 4640609) B4640609
theorem B8249971 : Blo 2171435 8249971 := bstep (se 1 (by rfl) ⟨6187478, by rfl⟩ : syracuseStep 8249971 = 12374957) B12374957
theorem B10999961 : Blo 2171435 10999961 := bstep (se 2 (by rfl) ⟨4124985, by rfl⟩ : syracuseStep 10999961 = 8249971) B8249971
theorem B7333307 : Blo 2171435 7333307 := bstep (se 1 (by rfl) ⟨5499980, by rfl⟩ : syracuseStep 7333307 = 10999961) B10999961
theorem B4888871 : Blo 2171435 4888871 := bstep (se 1 (by rfl) ⟨3666653, by rfl⟩ : syracuseStep 4888871 = 7333307) B7333307
theorem B3259247 : Blo 2171435 3259247 := bstep (se 1 (by rfl) ⟨2444435, by rfl⟩ : syracuseStep 3259247 = 4888871) B4888871
theorem B2172831 : Blo 2171435 2172831 := bstep (se 1 (by rfl) ⟨1629623, by rfl⟩ : syracuseStep 2172831 = 3259247) B3259247
theorem B3259253 : Blo 2171435 3259253 := bbase (se 5 (by rfl) ⟨152777, by rfl⟩ : syracuseStep 3259253 = 305555) (by norm_num)
theorem B2172835 : Blo 2171435 2172835 := bstep (se 1 (by rfl) ⟨1629626, by rfl⟩ : syracuseStep 2172835 = 3259253) B3259253
theorem B2610353 : Blo 2171435 2610353 := bbase (se 2 (by rfl) ⟨978882, by rfl⟩ : syracuseStep 2610353 = 1957765) (by norm_num)
theorem B6960941 : Blo 2171435 6960941 := bstep (se 3 (by rfl) ⟨1305176, by rfl⟩ : syracuseStep 6960941 = 2610353) B2610353
theorem B4640627 : Blo 2171435 4640627 := bstep (se 1 (by rfl) ⟨3480470, by rfl⟩ : syracuseStep 4640627 = 6960941) B6960941
theorem B3093751 : Blo 2171435 3093751 := bstep (se 1 (by rfl) ⟨2320313, by rfl⟩ : syracuseStep 3093751 = 4640627) B4640627
theorem B4125001 : Blo 2171435 4125001 := bstep (se 2 (by rfl) ⟨1546875, by rfl⟩ : syracuseStep 4125001 = 3093751) B3093751
theorem B5500001 : Blo 2171435 5500001 := bstep (se 2 (by rfl) ⟨2062500, by rfl⟩ : syracuseStep 5500001 = 4125001) B4125001
theorem B3666667 : Blo 2171435 3666667 := bstep (se 1 (by rfl) ⟨2750000, by rfl⟩ : syracuseStep 3666667 = 5500001) B5500001
theorem B4888889 : Blo 2171435 4888889 := bstep (se 2 (by rfl) ⟨1833333, by rfl⟩ : syracuseStep 4888889 = 3666667) B3666667
theorem B3259259 : Blo 2171435 3259259 := bstep (se 1 (by rfl) ⟨2444444, by rfl⟩ : syracuseStep 3259259 = 4888889) B4888889
theorem B2172839 : Blo 2171435 2172839 := bstep (se 1 (by rfl) ⟨1629629, by rfl⟩ : syracuseStep 2172839 = 3259259) B3259259
theorem B2444449 : Blo 2171435 2444449 := bbase (se 2 (by rfl) ⟨916668, by rfl⟩ : syracuseStep 2444449 = 1833337) (by norm_num)
theorem B3259265 : Blo 2171435 3259265 := bstep (se 2 (by rfl) ⟨1222224, by rfl⟩ : syracuseStep 3259265 = 2444449) B2444449
theorem B2172843 : Blo 2171435 2172843 := bstep (se 1 (by rfl) ⟨1629632, by rfl⟩ : syracuseStep 2172843 = 3259265) B3259265
theorem B5500021 : Blo 2171435 5500021 := bbase (se 5 (by rfl) ⟨257813, by rfl⟩ : syracuseStep 5500021 = 515627) (by norm_num)
theorem B7333361 : Blo 2171435 7333361 := bstep (se 2 (by rfl) ⟨2750010, by rfl⟩ : syracuseStep 7333361 = 5500021) B5500021
theorem B4888907 : Blo 2171435 4888907 := bstep (se 1 (by rfl) ⟨3666680, by rfl⟩ : syracuseStep 4888907 = 7333361) B7333361
theorem B3259271 : Blo 2171435 3259271 := bstep (se 1 (by rfl) ⟨2444453, by rfl⟩ : syracuseStep 3259271 = 4888907) B4888907
theorem B2172847 : Blo 2171435 2172847 := bstep (se 1 (by rfl) ⟨1629635, by rfl⟩ : syracuseStep 2172847 = 3259271) B3259271
theorem B3259277 : Blo 2171435 3259277 := bbase (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) (by norm_num)
theorem B2172851 : Blo 2171435 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B4888925 : Blo 2171435 4888925 := bbase (se 3 (by rfl) ⟨916673, by rfl⟩ : syracuseStep 4888925 = 1833347) (by norm_num)
theorem B3259283 : Blo 2171435 3259283 := bstep (se 1 (by rfl) ⟨2444462, by rfl⟩ : syracuseStep 3259283 = 4888925) B4888925
theorem B2172855 : Blo 2171435 2172855 := bstep (se 1 (by rfl) ⟨1629641, by rfl⟩ : syracuseStep 2172855 = 3259283) B3259283
theorem B3666701 : Blo 2171435 3666701 := bbase (se 3 (by rfl) ⟨687506, by rfl⟩ : syracuseStep 3666701 = 1375013) (by norm_num)
theorem B2444467 : Blo 2171435 2444467 := bstep (se 1 (by rfl) ⟨1833350, by rfl⟩ : syracuseStep 2444467 = 3666701) B3666701
theorem B3259289 : Blo 2171435 3259289 := bstep (se 2 (by rfl) ⟨1222233, by rfl⟩ : syracuseStep 3259289 = 2444467) B2444467
theorem B2172859 : Blo 2171435 2172859 := bstep (se 1 (by rfl) ⟨1629644, by rfl⟩ : syracuseStep 2172859 = 3259289) B3259289
theorem B18562709 : Blo 2171435 18562709 := bbase (se 6 (by rfl) ⟨435063, by rfl⟩ : syracuseStep 18562709 = 870127) (by norm_num)
theorem B12375139 : Blo 2171435 12375139 := bstep (se 1 (by rfl) ⟨9281354, by rfl⟩ : syracuseStep 12375139 = 18562709) B18562709
theorem B16500185 : Blo 2171435 16500185 := bstep (se 2 (by rfl) ⟨6187569, by rfl⟩ : syracuseStep 16500185 = 12375139) B12375139
theorem B11000123 : Blo 2171435 11000123 := bstep (se 1 (by rfl) ⟨8250092, by rfl⟩ : syracuseStep 11000123 = 16500185) B16500185
theorem B7333415 : Blo 2171435 7333415 := bstep (se 1 (by rfl) ⟨5500061, by rfl⟩ : syracuseStep 7333415 = 11000123) B11000123
theorem B4888943 : Blo 2171435 4888943 := bstep (se 1 (by rfl) ⟨3666707, by rfl⟩ : syracuseStep 4888943 = 7333415) B7333415
theorem B3259295 : Blo 2171435 3259295 := bstep (se 1 (by rfl) ⟨2444471, by rfl⟩ : syracuseStep 3259295 = 4888943) B4888943
theorem B2172863 : Blo 2171435 2172863 := bstep (se 1 (by rfl) ⟨1629647, by rfl⟩ : syracuseStep 2172863 = 3259295) B3259295
theorem B3259301 : Blo 2171435 3259301 := bbase (se 4 (by rfl) ⟨305559, by rfl⟩ : syracuseStep 3259301 = 611119) (by norm_num)
theorem B2172867 : Blo 2171435 2172867 := bstep (se 1 (by rfl) ⟨1629650, by rfl⟩ : syracuseStep 2172867 = 3259301) B3259301
theorem B2750041 : Blo 2171435 2750041 := bbase (se 2 (by rfl) ⟨1031265, by rfl⟩ : syracuseStep 2750041 = 2062531) (by norm_num)
theorem B3666721 : Blo 2171435 3666721 := bstep (se 2 (by rfl) ⟨1375020, by rfl⟩ : syracuseStep 3666721 = 2750041) B2750041
theorem B4888961 : Blo 2171435 4888961 := bstep (se 2 (by rfl) ⟨1833360, by rfl⟩ : syracuseStep 4888961 = 3666721) B3666721
theorem B3259307 : Blo 2171435 3259307 := bstep (se 1 (by rfl) ⟨2444480, by rfl⟩ : syracuseStep 3259307 = 4888961) B4888961
theorem B2172871 : Blo 2171435 2172871 := bstep (se 1 (by rfl) ⟨1629653, by rfl⟩ : syracuseStep 2172871 = 3259307) B3259307
theorem B2444485 : Blo 2171435 2444485 := bbase (se 4 (by rfl) ⟨229170, by rfl⟩ : syracuseStep 2444485 = 458341) (by norm_num)
theorem B3259313 : Blo 2171435 3259313 := bstep (se 2 (by rfl) ⟨1222242, by rfl⟩ : syracuseStep 3259313 = 2444485) B2444485
theorem B2172875 : Blo 2171435 2172875 := bstep (se 1 (by rfl) ⟨1629656, by rfl⟩ : syracuseStep 2172875 = 3259313) B3259313
theorem B4125077 : Blo 2171435 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B2750051 : Blo 2171435 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B7333469 : Blo 2171435 7333469 := bstep (se 3 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 7333469 = 2750051) B2750051
theorem B4888979 : Blo 2171435 4888979 := bstep (se 1 (by rfl) ⟨3666734, by rfl⟩ : syracuseStep 4888979 = 7333469) B7333469
theorem B3259319 : Blo 2171435 3259319 := bstep (se 1 (by rfl) ⟨2444489, by rfl⟩ : syracuseStep 3259319 = 4888979) B4888979
theorem B2172879 : Blo 2171435 2172879 := bstep (se 1 (by rfl) ⟨1629659, by rfl⟩ : syracuseStep 2172879 = 3259319) B3259319
theorem B3259325 : Blo 2171435 3259325 := bbase (se 3 (by rfl) ⟨611123, by rfl⟩ : syracuseStep 3259325 = 1222247) (by norm_num)
theorem B2172883 : Blo 2171435 2172883 := bstep (se 1 (by rfl) ⟨1629662, by rfl⟩ : syracuseStep 2172883 = 3259325) B3259325
theorem B4888997 : Blo 2171435 4888997 := bbase (se 4 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 4888997 = 916687) (by norm_num)
theorem B3259331 : Blo 2171435 3259331 := bstep (se 1 (by rfl) ⟨2444498, by rfl⟩ : syracuseStep 3259331 = 4888997) B4888997
theorem B2172887 : Blo 2171435 2172887 := bstep (se 1 (by rfl) ⟨1629665, by rfl⟩ : syracuseStep 2172887 = 3259331) B3259331
theorem B5500133 : Blo 2171435 5500133 := bbase (se 4 (by rfl) ⟨515637, by rfl⟩ : syracuseStep 5500133 = 1031275) (by norm_num)
theorem B3666755 : Blo 2171435 3666755 := bstep (se 1 (by rfl) ⟨2750066, by rfl⟩ : syracuseStep 3666755 = 5500133) B5500133
theorem B2444503 : Blo 2171435 2444503 := bstep (se 1 (by rfl) ⟨1833377, by rfl⟩ : syracuseStep 2444503 = 3666755) B3666755
theorem B3259337 : Blo 2171435 3259337 := bstep (se 2 (by rfl) ⟨1222251, by rfl⟩ : syracuseStep 3259337 = 2444503) B2444503
theorem B2172891 : Blo 2171435 2172891 := bstep (se 1 (by rfl) ⟨1629668, by rfl⟩ : syracuseStep 2172891 = 3259337) B3259337
theorem B2320373 : Blo 2171435 2320373 := bbase (se 5 (by rfl) ⟨108767, by rfl⟩ : syracuseStep 2320373 = 217535) (by norm_num)
theorem B6187661 : Blo 2171435 6187661 := bstep (se 3 (by rfl) ⟨1160186, by rfl⟩ : syracuseStep 6187661 = 2320373) B2320373
theorem B4125107 : Blo 2171435 4125107 := bstep (se 1 (by rfl) ⟨3093830, by rfl⟩ : syracuseStep 4125107 = 6187661) B6187661
theorem B11000285 : Blo 2171435 11000285 := bstep (se 3 (by rfl) ⟨2062553, by rfl⟩ : syracuseStep 11000285 = 4125107) B4125107
theorem B7333523 : Blo 2171435 7333523 := bstep (se 1 (by rfl) ⟨5500142, by rfl⟩ : syracuseStep 7333523 = 11000285) B11000285
theorem B4889015 : Blo 2171435 4889015 := bstep (se 1 (by rfl) ⟨3666761, by rfl⟩ : syracuseStep 4889015 = 7333523) B7333523
theorem B3259343 : Blo 2171435 3259343 := bstep (se 1 (by rfl) ⟨2444507, by rfl⟩ : syracuseStep 3259343 = 4889015) B4889015
theorem B2172895 : Blo 2171435 2172895 := bstep (se 1 (by rfl) ⟨1629671, by rfl⟩ : syracuseStep 2172895 = 3259343) B3259343
theorem B3259349 : Blo 2171435 3259349 := bbase (se 7 (by rfl) ⟨38195, by rfl⟩ : syracuseStep 3259349 = 76391) (by norm_num)
theorem B2172899 : Blo 2171435 2172899 := bstep (se 1 (by rfl) ⟨1629674, by rfl⟩ : syracuseStep 2172899 = 3259349) B3259349
theorem B8250245 : Blo 2171435 8250245 := bbase (se 4 (by rfl) ⟨773460, by rfl⟩ : syracuseStep 8250245 = 1546921) (by norm_num)
theorem B5500163 : Blo 2171435 5500163 := bstep (se 1 (by rfl) ⟨4125122, by rfl⟩ : syracuseStep 5500163 = 8250245) B8250245
theorem B3666775 : Blo 2171435 3666775 := bstep (se 1 (by rfl) ⟨2750081, by rfl⟩ : syracuseStep 3666775 = 5500163) B5500163
theorem B4889033 : Blo 2171435 4889033 := bstep (se 2 (by rfl) ⟨1833387, by rfl⟩ : syracuseStep 4889033 = 3666775) B3666775
theorem B3259355 : Blo 2171435 3259355 := bstep (se 1 (by rfl) ⟨2444516, by rfl⟩ : syracuseStep 3259355 = 4889033) B4889033
theorem B2172903 : Blo 2171435 2172903 := bstep (se 1 (by rfl) ⟨1629677, by rfl⟩ : syracuseStep 2172903 = 3259355) B3259355
theorem B2444521 : Blo 2171435 2444521 := bbase (se 2 (by rfl) ⟨916695, by rfl⟩ : syracuseStep 2444521 = 1833391) (by norm_num)
theorem B3259361 : Blo 2171435 3259361 := bstep (se 2 (by rfl) ⟨1222260, by rfl⟩ : syracuseStep 3259361 = 2444521) B2444521
theorem B2172907 : Blo 2171435 2172907 := bstep (se 1 (by rfl) ⟨1629680, by rfl⟩ : syracuseStep 2172907 = 3259361) B3259361
theorem B12375413 : Blo 2171435 12375413 := bbase (se 5 (by rfl) ⟨580097, by rfl⟩ : syracuseStep 12375413 = 1160195) (by norm_num)
theorem B8250275 : Blo 2171435 8250275 := bstep (se 1 (by rfl) ⟨6187706, by rfl⟩ : syracuseStep 8250275 = 12375413) B12375413
theorem B5500183 : Blo 2171435 5500183 := bstep (se 1 (by rfl) ⟨4125137, by rfl⟩ : syracuseStep 5500183 = 8250275) B8250275
theorem B7333577 : Blo 2171435 7333577 := bstep (se 2 (by rfl) ⟨2750091, by rfl⟩ : syracuseStep 7333577 = 5500183) B5500183
theorem B4889051 : Blo 2171435 4889051 := bstep (se 1 (by rfl) ⟨3666788, by rfl⟩ : syracuseStep 4889051 = 7333577) B7333577
theorem B3259367 : Blo 2171435 3259367 := bstep (se 1 (by rfl) ⟨2444525, by rfl⟩ : syracuseStep 3259367 = 4889051) B4889051
theorem B2172911 : Blo 2171435 2172911 := bstep (se 1 (by rfl) ⟨1629683, by rfl⟩ : syracuseStep 2172911 = 3259367) B3259367
theorem B3259373 : Blo 2171435 3259373 := bbase (se 3 (by rfl) ⟨611132, by rfl⟩ : syracuseStep 3259373 = 1222265) (by norm_num)
theorem B2172915 : Blo 2171435 2172915 := bstep (se 1 (by rfl) ⟨1629686, by rfl⟩ : syracuseStep 2172915 = 3259373) B3259373
theorem B4889069 : Blo 2171435 4889069 := bbase (se 3 (by rfl) ⟨916700, by rfl⟩ : syracuseStep 4889069 = 1833401) (by norm_num)
theorem B3259379 : Blo 2171435 3259379 := bstep (se 1 (by rfl) ⟨2444534, by rfl⟩ : syracuseStep 3259379 = 4889069) B4889069
theorem B2172919 : Blo 2171435 2172919 := bstep (se 1 (by rfl) ⟨1629689, by rfl⟩ : syracuseStep 2172919 = 3259379) B3259379
theorem B2477893 : Blo 2171435 2477893 := bbase (se 4 (by rfl) ⟨232302, by rfl⟩ : syracuseStep 2477893 = 464605) (by norm_num)
theorem B3303857 : Blo 2171435 3303857 := bstep (se 2 (by rfl) ⟨1238946, by rfl⟩ : syracuseStep 3303857 = 2477893) B2477893
theorem B2202571 : Blo 2171435 2202571 := bstep (se 1 (by rfl) ⟨1651928, by rfl⟩ : syracuseStep 2202571 = 3303857) B3303857
theorem B11747045 : Blo 2171435 11747045 := bstep (se 4 (by rfl) ⟨1101285, by rfl⟩ : syracuseStep 11747045 = 2202571) B2202571
theorem B7831363 : Blo 2171435 7831363 := bstep (se 1 (by rfl) ⟨5873522, by rfl⟩ : syracuseStep 7831363 = 11747045) B11747045
theorem B10441817 : Blo 2171435 10441817 := bstep (se 2 (by rfl) ⟨3915681, by rfl⟩ : syracuseStep 10441817 = 7831363) B7831363
theorem B6961211 : Blo 2171435 6961211 := bstep (se 1 (by rfl) ⟨5220908, by rfl⟩ : syracuseStep 6961211 = 10441817) B10441817
theorem B4640807 : Blo 2171435 4640807 := bstep (se 1 (by rfl) ⟨3480605, by rfl⟩ : syracuseStep 4640807 = 6961211) B6961211
theorem B3093871 : Blo 2171435 3093871 := bstep (se 1 (by rfl) ⟨2320403, by rfl⟩ : syracuseStep 3093871 = 4640807) B4640807
theorem B4125161 : Blo 2171435 4125161 := bstep (se 2 (by rfl) ⟨1546935, by rfl⟩ : syracuseStep 4125161 = 3093871) B3093871
theorem B2750107 : Blo 2171435 2750107 := bstep (se 1 (by rfl) ⟨2062580, by rfl⟩ : syracuseStep 2750107 = 4125161) B4125161
theorem B3666809 : Blo 2171435 3666809 := bstep (se 2 (by rfl) ⟨1375053, by rfl⟩ : syracuseStep 3666809 = 2750107) B2750107
theorem B2444539 : Blo 2171435 2444539 := bstep (se 1 (by rfl) ⟨1833404, by rfl⟩ : syracuseStep 2444539 = 3666809) B3666809
theorem B3259385 : Blo 2171435 3259385 := bstep (se 2 (by rfl) ⟨1222269, by rfl⟩ : syracuseStep 3259385 = 2444539) B2444539
theorem B2172923 : Blo 2171435 2172923 := bstep (se 1 (by rfl) ⟨1629692, by rfl⟩ : syracuseStep 2172923 = 3259385) B3259385
theorem B7056197 : Blo 2171435 7056197 := bbase (se 4 (by rfl) ⟨661518, by rfl⟩ : syracuseStep 7056197 = 1323037) (by norm_num)
theorem B4704131 : Blo 2171435 4704131 := bstep (se 1 (by rfl) ⟨3528098, by rfl⟩ : syracuseStep 4704131 = 7056197) B7056197
theorem B3136087 : Blo 2171435 3136087 := bstep (se 1 (by rfl) ⟨2352065, by rfl⟩ : syracuseStep 3136087 = 4704131) B4704131
theorem B16725797 : Blo 2171435 16725797 := bstep (se 4 (by rfl) ⟨1568043, by rfl⟩ : syracuseStep 16725797 = 3136087) B3136087
theorem B11150531 : Blo 2171435 11150531 := bstep (se 1 (by rfl) ⟨8362898, by rfl⟩ : syracuseStep 11150531 = 16725797) B16725797
theorem B7433687 : Blo 2171435 7433687 := bstep (se 1 (by rfl) ⟨5575265, by rfl⟩ : syracuseStep 7433687 = 11150531) B11150531
theorem B19823165 : Blo 2171435 19823165 := bstep (se 3 (by rfl) ⟨3716843, by rfl⟩ : syracuseStep 19823165 = 7433687) B7433687
theorem B13215443 : Blo 2171435 13215443 := bstep (se 1 (by rfl) ⟨9911582, by rfl⟩ : syracuseStep 13215443 = 19823165) B19823165
theorem B140964725 : Blo 2171435 140964725 := bstep (se 5 (by rfl) ⟨6607721, by rfl⟩ : syracuseStep 140964725 = 13215443) B13215443
theorem B93976483 : Blo 2171435 93976483 := bstep (se 1 (by rfl) ⟨70482362, by rfl⟩ : syracuseStep 93976483 = 140964725) B140964725
theorem B125301977 : Blo 2171435 125301977 := bstep (se 2 (by rfl) ⟨46988241, by rfl⟩ : syracuseStep 125301977 = 93976483) B93976483
theorem B83534651 : Blo 2171435 83534651 := bstep (se 1 (by rfl) ⟨62650988, by rfl⟩ : syracuseStep 83534651 = 125301977) B125301977
theorem B55689767 : Blo 2171435 55689767 := bstep (se 1 (by rfl) ⟨41767325, by rfl⟩ : syracuseStep 55689767 = 83534651) B83534651
theorem B37126511 : Blo 2171435 37126511 := bstep (se 1 (by rfl) ⟨27844883, by rfl⟩ : syracuseStep 37126511 = 55689767) B55689767
theorem B24751007 : Blo 2171435 24751007 := bstep (se 1 (by rfl) ⟨18563255, by rfl⟩ : syracuseStep 24751007 = 37126511) B37126511
theorem B16500671 : Blo 2171435 16500671 := bstep (se 1 (by rfl) ⟨12375503, by rfl⟩ : syracuseStep 16500671 = 24751007) B24751007
theorem B11000447 : Blo 2171435 11000447 := bstep (se 1 (by rfl) ⟨8250335, by rfl⟩ : syracuseStep 11000447 = 16500671) B16500671
theorem B7333631 : Blo 2171435 7333631 := bstep (se 1 (by rfl) ⟨5500223, by rfl⟩ : syracuseStep 7333631 = 11000447) B11000447
theorem B4889087 : Blo 2171435 4889087 := bstep (se 1 (by rfl) ⟨3666815, by rfl⟩ : syracuseStep 4889087 = 7333631) B7333631
theorem B3259391 : Blo 2171435 3259391 := bstep (se 1 (by rfl) ⟨2444543, by rfl⟩ : syracuseStep 3259391 = 4889087) B4889087
theorem B2172927 : Blo 2171435 2172927 := bstep (se 1 (by rfl) ⟨1629695, by rfl⟩ : syracuseStep 2172927 = 3259391) B3259391
theorem B3259397 : Blo 2171435 3259397 := bbase (se 4 (by rfl) ⟨305568, by rfl⟩ : syracuseStep 3259397 = 611137) (by norm_num)
theorem B2172931 : Blo 2171435 2172931 := bstep (se 1 (by rfl) ⟨1629698, by rfl⟩ : syracuseStep 2172931 = 3259397) B3259397
theorem B3666829 : Blo 2171435 3666829 := bbase (se 3 (by rfl) ⟨687530, by rfl⟩ : syracuseStep 3666829 = 1375061) (by norm_num)
theorem B4889105 : Blo 2171435 4889105 := bstep (se 2 (by rfl) ⟨1833414, by rfl⟩ : syracuseStep 4889105 = 3666829) B3666829
theorem B3259403 : Blo 2171435 3259403 := bstep (se 1 (by rfl) ⟨2444552, by rfl⟩ : syracuseStep 3259403 = 4889105) B4889105
theorem B2172935 : Blo 2171435 2172935 := bstep (se 1 (by rfl) ⟨1629701, by rfl⟩ : syracuseStep 2172935 = 3259403) B3259403
theorem B2444557 : Blo 2171435 2444557 := bbase (se 3 (by rfl) ⟨458354, by rfl⟩ : syracuseStep 2444557 = 916709) (by norm_num)
theorem B3259409 : Blo 2171435 3259409 := bstep (se 2 (by rfl) ⟨1222278, by rfl⟩ : syracuseStep 3259409 = 2444557) B2444557
theorem B2172939 : Blo 2171435 2172939 := bstep (se 1 (by rfl) ⟨1629704, by rfl⟩ : syracuseStep 2172939 = 3259409) B3259409
theorem B7333685 : Blo 2171435 7333685 := bbase (se 5 (by rfl) ⟨343766, by rfl⟩ : syracuseStep 7333685 = 687533) (by norm_num)
theorem B4889123 : Blo 2171435 4889123 := bstep (se 1 (by rfl) ⟨3666842, by rfl⟩ : syracuseStep 4889123 = 7333685) B7333685
theorem B3259415 : Blo 2171435 3259415 := bstep (se 1 (by rfl) ⟨2444561, by rfl⟩ : syracuseStep 3259415 = 4889123) B4889123
theorem B2172943 : Blo 2171435 2172943 := bstep (se 1 (by rfl) ⟨1629707, by rfl⟩ : syracuseStep 2172943 = 3259415) B3259415
theorem B3259421 : Blo 2171435 3259421 := bbase (se 3 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 3259421 = 1222283) (by norm_num)
theorem B2172947 : Blo 2171435 2172947 := bstep (se 1 (by rfl) ⟨1629710, by rfl⟩ : syracuseStep 2172947 = 3259421) B3259421
theorem B4889141 : Blo 2171435 4889141 := bbase (se 5 (by rfl) ⟨229178, by rfl⟩ : syracuseStep 4889141 = 458357) (by norm_num)
theorem B3259427 : Blo 2171435 3259427 := bstep (se 1 (by rfl) ⟨2444570, by rfl⟩ : syracuseStep 3259427 = 4889141) B4889141
theorem B2172951 : Blo 2171435 2172951 := bstep (se 1 (by rfl) ⟨1629713, by rfl⟩ : syracuseStep 2172951 = 3259427) B3259427
theorem B9281749 : Blo 2171435 9281749 := bbase (se 7 (by rfl) ⟨108770, by rfl⟩ : syracuseStep 9281749 = 217541) (by norm_num)
theorem B12375665 : Blo 2171435 12375665 := bstep (se 2 (by rfl) ⟨4640874, by rfl⟩ : syracuseStep 12375665 = 9281749) B9281749
theorem B8250443 : Blo 2171435 8250443 := bstep (se 1 (by rfl) ⟨6187832, by rfl⟩ : syracuseStep 8250443 = 12375665) B12375665
theorem B5500295 : Blo 2171435 5500295 := bstep (se 1 (by rfl) ⟨4125221, by rfl⟩ : syracuseStep 5500295 = 8250443) B8250443
theorem B3666863 : Blo 2171435 3666863 := bstep (se 1 (by rfl) ⟨2750147, by rfl⟩ : syracuseStep 3666863 = 5500295) B5500295
theorem B2444575 : Blo 2171435 2444575 := bstep (se 1 (by rfl) ⟨1833431, by rfl⟩ : syracuseStep 2444575 = 3666863) B3666863
theorem B3259433 : Blo 2171435 3259433 := bstep (se 2 (by rfl) ⟨1222287, by rfl⟩ : syracuseStep 3259433 = 2444575) B2444575
theorem B2172955 : Blo 2171435 2172955 := bstep (se 1 (by rfl) ⟨1629716, by rfl⟩ : syracuseStep 2172955 = 3259433) B3259433
theorem B9281765 : Blo 2171435 9281765 := bbase (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) (by norm_num)
theorem B6187843 : Blo 2171435 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B8250457 : Blo 2171435 8250457 := bstep (se 2 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 8250457 = 6187843) B6187843
theorem B11000609 : Blo 2171435 11000609 := bstep (se 2 (by rfl) ⟨4125228, by rfl⟩ : syracuseStep 11000609 = 8250457) B8250457
theorem B7333739 : Blo 2171435 7333739 := bstep (se 1 (by rfl) ⟨5500304, by rfl⟩ : syracuseStep 7333739 = 11000609) B11000609
theorem B4889159 : Blo 2171435 4889159 := bstep (se 1 (by rfl) ⟨3666869, by rfl⟩ : syracuseStep 4889159 = 7333739) B7333739
theorem B3259439 : Blo 2171435 3259439 := bstep (se 1 (by rfl) ⟨2444579, by rfl⟩ : syracuseStep 3259439 = 4889159) B4889159
theorem B2172959 : Blo 2171435 2172959 := bstep (se 1 (by rfl) ⟨1629719, by rfl⟩ : syracuseStep 2172959 = 3259439) B3259439
theorem B3259445 : Blo 2171435 3259445 := bbase (se 5 (by rfl) ⟨152786, by rfl⟩ : syracuseStep 3259445 = 305573) (by norm_num)
theorem B2172963 : Blo 2171435 2172963 := bstep (se 1 (by rfl) ⟨1629722, by rfl⟩ : syracuseStep 2172963 = 3259445) B3259445
theorem B5500325 : Blo 2171435 5500325 := bbase (se 4 (by rfl) ⟨515655, by rfl⟩ : syracuseStep 5500325 = 1031311) (by norm_num)
theorem B3666883 : Blo 2171435 3666883 := bstep (se 1 (by rfl) ⟨2750162, by rfl⟩ : syracuseStep 3666883 = 5500325) B5500325
theorem B4889177 : Blo 2171435 4889177 := bstep (se 2 (by rfl) ⟨1833441, by rfl⟩ : syracuseStep 4889177 = 3666883) B3666883
theorem B3259451 : Blo 2171435 3259451 := bstep (se 1 (by rfl) ⟨2444588, by rfl⟩ : syracuseStep 3259451 = 4889177) B4889177
theorem B2172967 : Blo 2171435 2172967 := bstep (se 1 (by rfl) ⟨1629725, by rfl⟩ : syracuseStep 2172967 = 3259451) B3259451
theorem B2444593 : Blo 2171435 2444593 := bbase (se 2 (by rfl) ⟨916722, by rfl⟩ : syracuseStep 2444593 = 1833445) (by norm_num)
theorem B3259457 : Blo 2171435 3259457 := bstep (se 2 (by rfl) ⟨1222296, by rfl⟩ : syracuseStep 3259457 = 2444593) B2444593
theorem B2172971 : Blo 2171435 2172971 := bstep (se 1 (by rfl) ⟨1629728, by rfl⟩ : syracuseStep 2172971 = 3259457) B3259457
theorem B4640917 : Blo 2171435 4640917 := bbase (se 6 (by rfl) ⟨108771, by rfl⟩ : syracuseStep 4640917 = 217543) (by norm_num)
theorem B6187889 : Blo 2171435 6187889 := bstep (se 2 (by rfl) ⟨2320458, by rfl⟩ : syracuseStep 6187889 = 4640917) B4640917
theorem B4125259 : Blo 2171435 4125259 := bstep (se 1 (by rfl) ⟨3093944, by rfl⟩ : syracuseStep 4125259 = 6187889) B6187889
theorem B5500345 : Blo 2171435 5500345 := bstep (se 2 (by rfl) ⟨2062629, by rfl⟩ : syracuseStep 5500345 = 4125259) B4125259
theorem B7333793 : Blo 2171435 7333793 := bstep (se 2 (by rfl) ⟨2750172, by rfl⟩ : syracuseStep 7333793 = 5500345) B5500345
theorem B4889195 : Blo 2171435 4889195 := bstep (se 1 (by rfl) ⟨3666896, by rfl⟩ : syracuseStep 4889195 = 7333793) B7333793
theorem B3259463 : Blo 2171435 3259463 := bstep (se 1 (by rfl) ⟨2444597, by rfl⟩ : syracuseStep 3259463 = 4889195) B4889195
theorem B2172975 : Blo 2171435 2172975 := bstep (se 1 (by rfl) ⟨1629731, by rfl⟩ : syracuseStep 2172975 = 3259463) B3259463
theorem B3259469 : Blo 2171435 3259469 := bbase (se 3 (by rfl) ⟨611150, by rfl⟩ : syracuseStep 3259469 = 1222301) (by norm_num)
theorem B2172979 : Blo 2171435 2172979 := bstep (se 1 (by rfl) ⟨1629734, by rfl⟩ : syracuseStep 2172979 = 3259469) B3259469
theorem B4889213 : Blo 2171435 4889213 := bbase (se 3 (by rfl) ⟨916727, by rfl⟩ : syracuseStep 4889213 = 1833455) (by norm_num)
theorem B3259475 : Blo 2171435 3259475 := bstep (se 1 (by rfl) ⟨2444606, by rfl⟩ : syracuseStep 3259475 = 4889213) B4889213
theorem B2172983 : Blo 2171435 2172983 := bstep (se 1 (by rfl) ⟨1629737, by rfl⟩ : syracuseStep 2172983 = 3259475) B3259475
theorem B3666917 : Blo 2171435 3666917 := bbase (se 4 (by rfl) ⟨343773, by rfl⟩ : syracuseStep 3666917 = 687547) (by norm_num)
theorem B2444611 : Blo 2171435 2444611 := bstep (se 1 (by rfl) ⟨1833458, by rfl⟩ : syracuseStep 2444611 = 3666917) B3666917
theorem B3259481 : Blo 2171435 3259481 := bstep (se 2 (by rfl) ⟨1222305, by rfl⟩ : syracuseStep 3259481 = 2444611) B2444611
theorem B2172987 : Blo 2171435 2172987 := bstep (se 1 (by rfl) ⟨1629740, by rfl⟩ : syracuseStep 2172987 = 3259481) B3259481
theorem B15876917 : Blo 2171435 15876917 := bbase (se 5 (by rfl) ⟨744230, by rfl⟩ : syracuseStep 15876917 = 1488461) (by norm_num)
theorem B10584611 : Blo 2171435 10584611 := bstep (se 1 (by rfl) ⟨7938458, by rfl⟩ : syracuseStep 10584611 = 15876917) B15876917
theorem B7056407 : Blo 2171435 7056407 := bstep (se 1 (by rfl) ⟨5292305, by rfl⟩ : syracuseStep 7056407 = 10584611) B10584611
theorem B18817085 : Blo 2171435 18817085 := bstep (se 3 (by rfl) ⟨3528203, by rfl⟩ : syracuseStep 18817085 = 7056407) B7056407
theorem B12544723 : Blo 2171435 12544723 := bstep (se 1 (by rfl) ⟨9408542, by rfl⟩ : syracuseStep 12544723 = 18817085) B18817085
theorem B16726297 : Blo 2171435 16726297 := bstep (se 2 (by rfl) ⟨6272361, by rfl⟩ : syracuseStep 16726297 = 12544723) B12544723
theorem B22301729 : Blo 2171435 22301729 := bstep (se 2 (by rfl) ⟨8363148, by rfl⟩ : syracuseStep 22301729 = 16726297) B16726297
theorem B14867819 : Blo 2171435 14867819 := bstep (se 1 (by rfl) ⟨11150864, by rfl⟩ : syracuseStep 14867819 = 22301729) B22301729
theorem B9911879 : Blo 2171435 9911879 := bstep (se 1 (by rfl) ⟨7433909, by rfl⟩ : syracuseStep 9911879 = 14867819) B14867819
theorem B6607919 : Blo 2171435 6607919 := bstep (se 1 (by rfl) ⟨4955939, by rfl⟩ : syracuseStep 6607919 = 9911879) B9911879
theorem B4405279 : Blo 2171435 4405279 := bstep (se 1 (by rfl) ⟨3303959, by rfl⟩ : syracuseStep 4405279 = 6607919) B6607919
theorem B5873705 : Blo 2171435 5873705 := bstep (se 2 (by rfl) ⟨2202639, by rfl⟩ : syracuseStep 5873705 = 4405279) B4405279
theorem B3915803 : Blo 2171435 3915803 := bstep (se 1 (by rfl) ⟨2936852, by rfl⟩ : syracuseStep 3915803 = 5873705) B5873705
theorem B10442141 : Blo 2171435 10442141 := bstep (se 3 (by rfl) ⟨1957901, by rfl⟩ : syracuseStep 10442141 = 3915803) B3915803
theorem B6961427 : Blo 2171435 6961427 := bstep (se 1 (by rfl) ⟨5221070, by rfl⟩ : syracuseStep 6961427 = 10442141) B10442141
theorem B4640951 : Blo 2171435 4640951 := bstep (se 1 (by rfl) ⟨3480713, by rfl⟩ : syracuseStep 4640951 = 6961427) B6961427
theorem B3093967 : Blo 2171435 3093967 := bstep (se 1 (by rfl) ⟨2320475, by rfl⟩ : syracuseStep 3093967 = 4640951) B4640951
theorem B16501157 : Blo 2171435 16501157 := bstep (se 4 (by rfl) ⟨1546983, by rfl⟩ : syracuseStep 16501157 = 3093967) B3093967
theorem B11000771 : Blo 2171435 11000771 := bstep (se 1 (by rfl) ⟨8250578, by rfl⟩ : syracuseStep 11000771 = 16501157) B16501157
theorem B7333847 : Blo 2171435 7333847 := bstep (se 1 (by rfl) ⟨5500385, by rfl⟩ : syracuseStep 7333847 = 11000771) B11000771
theorem B4889231 : Blo 2171435 4889231 := bstep (se 1 (by rfl) ⟨3666923, by rfl⟩ : syracuseStep 4889231 = 7333847) B7333847
theorem B3259487 : Blo 2171435 3259487 := bstep (se 1 (by rfl) ⟨2444615, by rfl⟩ : syracuseStep 3259487 = 4889231) B4889231
theorem B2172991 : Blo 2171435 2172991 := bstep (se 1 (by rfl) ⟨1629743, by rfl⟩ : syracuseStep 2172991 = 3259487) B3259487
theorem B3259493 : Blo 2171435 3259493 := bbase (se 4 (by rfl) ⟨305577, by rfl⟩ : syracuseStep 3259493 = 611155) (by norm_num)
theorem B2172995 : Blo 2171435 2172995 := bstep (se 1 (by rfl) ⟨1629746, by rfl⟩ : syracuseStep 2172995 = 3259493) B3259493
theorem B7831637 : Blo 2171435 7831637 := bbase (se 8 (by rfl) ⟨45888, by rfl⟩ : syracuseStep 7831637 = 91777) (by norm_num)
theorem B5221091 : Blo 2171435 5221091 := bstep (se 1 (by rfl) ⟨3915818, by rfl⟩ : syracuseStep 5221091 = 7831637) B7831637
theorem B3480727 : Blo 2171435 3480727 := bstep (se 1 (by rfl) ⟨2610545, by rfl⟩ : syracuseStep 3480727 = 5221091) B5221091
theorem B4640969 : Blo 2171435 4640969 := bstep (se 2 (by rfl) ⟨1740363, by rfl⟩ : syracuseStep 4640969 = 3480727) B3480727
theorem B3093979 : Blo 2171435 3093979 := bstep (se 1 (by rfl) ⟨2320484, by rfl⟩ : syracuseStep 3093979 = 4640969) B4640969
theorem B4125305 : Blo 2171435 4125305 := bstep (se 2 (by rfl) ⟨1546989, by rfl⟩ : syracuseStep 4125305 = 3093979) B3093979
theorem B2750203 : Blo 2171435 2750203 := bstep (se 1 (by rfl) ⟨2062652, by rfl⟩ : syracuseStep 2750203 = 4125305) B4125305
theorem B3666937 : Blo 2171435 3666937 := bstep (se 2 (by rfl) ⟨1375101, by rfl⟩ : syracuseStep 3666937 = 2750203) B2750203
theorem B4889249 : Blo 2171435 4889249 := bstep (se 2 (by rfl) ⟨1833468, by rfl⟩ : syracuseStep 4889249 = 3666937) B3666937
theorem B3259499 : Blo 2171435 3259499 := bstep (se 1 (by rfl) ⟨2444624, by rfl⟩ : syracuseStep 3259499 = 4889249) B4889249
theorem B2172999 : Blo 2171435 2172999 := bstep (se 1 (by rfl) ⟨1629749, by rfl⟩ : syracuseStep 2172999 = 3259499) B3259499
theorem B2444629 : Blo 2171435 2444629 := bbase (se 11 (by rfl) ⟨1790, by rfl⟩ : syracuseStep 2444629 = 3581) (by norm_num)
theorem B3259505 : Blo 2171435 3259505 := bstep (se 2 (by rfl) ⟨1222314, by rfl⟩ : syracuseStep 3259505 = 2444629) B2444629
theorem B2173003 : Blo 2171435 2173003 := bstep (se 1 (by rfl) ⟨1629752, by rfl⟩ : syracuseStep 2173003 = 3259505) B3259505
theorem B2750213 : Blo 2171435 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B7333901 : Blo 2171435 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B4889267 : Blo 2171435 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B3259511 : Blo 2171435 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B2173007 : Blo 2171435 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B3259517 : Blo 2171435 3259517 := bbase (se 3 (by rfl) ⟨611159, by rfl⟩ : syracuseStep 3259517 = 1222319) (by norm_num)
theorem B2173011 : Blo 2171435 2173011 := bstep (se 1 (by rfl) ⟨1629758, by rfl⟩ : syracuseStep 2173011 = 3259517) B3259517
theorem B4889285 : Blo 2171435 4889285 := bbase (se 4 (by rfl) ⟨458370, by rfl⟩ : syracuseStep 4889285 = 916741) (by norm_num)
theorem B3259523 : Blo 2171435 3259523 := bstep (se 1 (by rfl) ⟨2444642, by rfl⟩ : syracuseStep 3259523 = 4889285) B4889285
theorem B2173015 : Blo 2171435 2173015 := bstep (se 1 (by rfl) ⟨1629761, by rfl⟩ : syracuseStep 2173015 = 3259523) B3259523
theorem B5292373 : Blo 2171435 5292373 := bbase (se 10 (by rfl) ⟨7752, by rfl⟩ : syracuseStep 5292373 = 15505) (by norm_num)
theorem B7056497 : Blo 2171435 7056497 := bstep (se 2 (by rfl) ⟨2646186, by rfl⟩ : syracuseStep 7056497 = 5292373) B5292373
theorem B18817325 : Blo 2171435 18817325 := bstep (se 3 (by rfl) ⟨3528248, by rfl⟩ : syracuseStep 18817325 = 7056497) B7056497
theorem B12544883 : Blo 2171435 12544883 := bstep (se 1 (by rfl) ⟨9408662, by rfl⟩ : syracuseStep 12544883 = 18817325) B18817325
theorem B8363255 : Blo 2171435 8363255 := bstep (se 1 (by rfl) ⟨6272441, by rfl⟩ : syracuseStep 8363255 = 12544883) B12544883
theorem B22302013 : Blo 2171435 22302013 := bstep (se 3 (by rfl) ⟨4181627, by rfl⟩ : syracuseStep 22302013 = 8363255) B8363255
theorem B29736017 : Blo 2171435 29736017 := bstep (se 2 (by rfl) ⟨11151006, by rfl⟩ : syracuseStep 29736017 = 22302013) B22302013
theorem B19824011 : Blo 2171435 19824011 := bstep (se 1 (by rfl) ⟨14868008, by rfl⟩ : syracuseStep 19824011 = 29736017) B29736017
theorem B13216007 : Blo 2171435 13216007 := bstep (se 1 (by rfl) ⟨9912005, by rfl⟩ : syracuseStep 13216007 = 19824011) B19824011
theorem B35242685 : Blo 2171435 35242685 := bstep (se 3 (by rfl) ⟨6608003, by rfl⟩ : syracuseStep 35242685 = 13216007) B13216007
theorem B23495123 : Blo 2171435 23495123 := bstep (se 1 (by rfl) ⟨17621342, by rfl⟩ : syracuseStep 23495123 = 35242685) B35242685
theorem B15663415 : Blo 2171435 15663415 := bstep (se 1 (by rfl) ⟨11747561, by rfl⟩ : syracuseStep 15663415 = 23495123) B23495123
theorem B20884553 : Blo 2171435 20884553 := bstep (se 2 (by rfl) ⟨7831707, by rfl⟩ : syracuseStep 20884553 = 15663415) B15663415
theorem B13923035 : Blo 2171435 13923035 := bstep (se 1 (by rfl) ⟨10442276, by rfl⟩ : syracuseStep 13923035 = 20884553) B20884553
theorem B9282023 : Blo 2171435 9282023 := bstep (se 1 (by rfl) ⟨6961517, by rfl⟩ : syracuseStep 9282023 = 13923035) B13923035
theorem B6188015 : Blo 2171435 6188015 := bstep (se 1 (by rfl) ⟨4641011, by rfl⟩ : syracuseStep 6188015 = 9282023) B9282023
theorem B4125343 : Blo 2171435 4125343 := bstep (se 1 (by rfl) ⟨3094007, by rfl⟩ : syracuseStep 4125343 = 6188015) B6188015
theorem B5500457 : Blo 2171435 5500457 := bstep (se 2 (by rfl) ⟨2062671, by rfl⟩ : syracuseStep 5500457 = 4125343) B4125343
theorem B3666971 : Blo 2171435 3666971 := bstep (se 1 (by rfl) ⟨2750228, by rfl⟩ : syracuseStep 3666971 = 5500457) B5500457
theorem B2444647 : Blo 2171435 2444647 := bstep (se 1 (by rfl) ⟨1833485, by rfl⟩ : syracuseStep 2444647 = 3666971) B3666971
theorem B3259529 : Blo 2171435 3259529 := bstep (se 2 (by rfl) ⟨1222323, by rfl⟩ : syracuseStep 3259529 = 2444647) B2444647
theorem B2173019 : Blo 2171435 2173019 := bstep (se 1 (by rfl) ⟨1629764, by rfl⟩ : syracuseStep 2173019 = 3259529) B3259529
theorem B11000933 : Blo 2171435 11000933 := bbase (se 4 (by rfl) ⟨1031337, by rfl⟩ : syracuseStep 11000933 = 2062675) (by norm_num)
theorem B7333955 : Blo 2171435 7333955 := bstep (se 1 (by rfl) ⟨5500466, by rfl⟩ : syracuseStep 7333955 = 11000933) B11000933
theorem B4889303 : Blo 2171435 4889303 := bstep (se 1 (by rfl) ⟨3666977, by rfl⟩ : syracuseStep 4889303 = 7333955) B7333955
theorem B3259535 : Blo 2171435 3259535 := bstep (se 1 (by rfl) ⟨2444651, by rfl⟩ : syracuseStep 3259535 = 4889303) B4889303
theorem B2173023 : Blo 2171435 2173023 := bstep (se 1 (by rfl) ⟨1629767, by rfl⟩ : syracuseStep 2173023 = 3259535) B3259535
theorem B3259541 : Blo 2171435 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B2173027 : Blo 2171435 2173027 := bstep (se 1 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 2173027 = 3259541) B3259541
theorem B5873813 : Blo 2171435 5873813 := bbase (se 6 (by rfl) ⟨137667, by rfl⟩ : syracuseStep 5873813 = 275335) (by norm_num)
theorem B3915875 : Blo 2171435 3915875 := bstep (se 1 (by rfl) ⟨2936906, by rfl⟩ : syracuseStep 3915875 = 5873813) B5873813
theorem B10442333 : Blo 2171435 10442333 := bstep (se 3 (by rfl) ⟨1957937, by rfl⟩ : syracuseStep 10442333 = 3915875) B3915875
theorem B6961555 : Blo 2171435 6961555 := bstep (se 1 (by rfl) ⟨5221166, by rfl⟩ : syracuseStep 6961555 = 10442333) B10442333
theorem B9282073 : Blo 2171435 9282073 := bstep (se 2 (by rfl) ⟨3480777, by rfl⟩ : syracuseStep 9282073 = 6961555) B6961555
theorem B12376097 : Blo 2171435 12376097 := bstep (se 2 (by rfl) ⟨4641036, by rfl⟩ : syracuseStep 12376097 = 9282073) B9282073
theorem B8250731 : Blo 2171435 8250731 := bstep (se 1 (by rfl) ⟨6188048, by rfl⟩ : syracuseStep 8250731 = 12376097) B12376097
theorem B5500487 : Blo 2171435 5500487 := bstep (se 1 (by rfl) ⟨4125365, by rfl⟩ : syracuseStep 5500487 = 8250731) B8250731
theorem B3666991 : Blo 2171435 3666991 := bstep (se 1 (by rfl) ⟨2750243, by rfl⟩ : syracuseStep 3666991 = 5500487) B5500487
theorem B4889321 : Blo 2171435 4889321 := bstep (se 2 (by rfl) ⟨1833495, by rfl⟩ : syracuseStep 4889321 = 3666991) B3666991
theorem B3259547 : Blo 2171435 3259547 := bstep (se 1 (by rfl) ⟨2444660, by rfl⟩ : syracuseStep 3259547 = 4889321) B4889321
theorem B2173031 : Blo 2171435 2173031 := bstep (se 1 (by rfl) ⟨1629773, by rfl⟩ : syracuseStep 2173031 = 3259547) B3259547
theorem B2444665 : Blo 2171435 2444665 := bbase (se 2 (by rfl) ⟨916749, by rfl⟩ : syracuseStep 2444665 = 1833499) (by norm_num)
theorem B3259553 : Blo 2171435 3259553 := bstep (se 2 (by rfl) ⟨1222332, by rfl⟩ : syracuseStep 3259553 = 2444665) B2444665
theorem B2173035 : Blo 2171435 2173035 := bstep (se 1 (by rfl) ⟨1629776, by rfl⟩ : syracuseStep 2173035 = 3259553) B3259553
theorem B2936917 : Blo 2171435 2936917 := bbase (se 8 (by rfl) ⟨17208, by rfl⟩ : syracuseStep 2936917 = 34417) (by norm_num)
theorem B15663557 : Blo 2171435 15663557 := bstep (se 4 (by rfl) ⟨1468458, by rfl⟩ : syracuseStep 15663557 = 2936917) B2936917
theorem B10442371 : Blo 2171435 10442371 := bstep (se 1 (by rfl) ⟨7831778, by rfl⟩ : syracuseStep 10442371 = 15663557) B15663557
theorem B13923161 : Blo 2171435 13923161 := bstep (se 2 (by rfl) ⟨5221185, by rfl⟩ : syracuseStep 13923161 = 10442371) B10442371
theorem B9282107 : Blo 2171435 9282107 := bstep (se 1 (by rfl) ⟨6961580, by rfl⟩ : syracuseStep 9282107 = 13923161) B13923161
theorem B6188071 : Blo 2171435 6188071 := bstep (se 1 (by rfl) ⟨4641053, by rfl⟩ : syracuseStep 6188071 = 9282107) B9282107
theorem B8250761 : Blo 2171435 8250761 := bstep (se 2 (by rfl) ⟨3094035, by rfl⟩ : syracuseStep 8250761 = 6188071) B6188071
theorem B5500507 : Blo 2171435 5500507 := bstep (se 1 (by rfl) ⟨4125380, by rfl⟩ : syracuseStep 5500507 = 8250761) B8250761
theorem B7334009 : Blo 2171435 7334009 := bstep (se 2 (by rfl) ⟨2750253, by rfl⟩ : syracuseStep 7334009 = 5500507) B5500507
theorem B4889339 : Blo 2171435 4889339 := bstep (se 1 (by rfl) ⟨3667004, by rfl⟩ : syracuseStep 4889339 = 7334009) B7334009
theorem B3259559 : Blo 2171435 3259559 := bstep (se 1 (by rfl) ⟨2444669, by rfl⟩ : syracuseStep 3259559 = 4889339) B4889339
theorem B2173039 : Blo 2171435 2173039 := bstep (se 1 (by rfl) ⟨1629779, by rfl⟩ : syracuseStep 2173039 = 3259559) B3259559
theorem B3259565 : Blo 2171435 3259565 := bbase (se 3 (by rfl) ⟨611168, by rfl⟩ : syracuseStep 3259565 = 1222337) (by norm_num)
theorem B2173043 : Blo 2171435 2173043 := bstep (se 1 (by rfl) ⟨1629782, by rfl⟩ : syracuseStep 2173043 = 3259565) B3259565
theorem B4889357 : Blo 2171435 4889357 := bbase (se 3 (by rfl) ⟨916754, by rfl⟩ : syracuseStep 4889357 = 1833509) (by norm_num)
theorem B3259571 : Blo 2171435 3259571 := bstep (se 1 (by rfl) ⟨2444678, by rfl⟩ : syracuseStep 3259571 = 4889357) B4889357
theorem B2173047 : Blo 2171435 2173047 := bstep (se 1 (by rfl) ⟨1629785, by rfl⟩ : syracuseStep 2173047 = 3259571) B3259571
theorem B2750269 : Blo 2171435 2750269 := bbase (se 3 (by rfl) ⟨515675, by rfl⟩ : syracuseStep 2750269 = 1031351) (by norm_num)
theorem B3667025 : Blo 2171435 3667025 := bstep (se 2 (by rfl) ⟨1375134, by rfl⟩ : syracuseStep 3667025 = 2750269) B2750269
theorem B2444683 : Blo 2171435 2444683 := bstep (se 1 (by rfl) ⟨1833512, by rfl⟩ : syracuseStep 2444683 = 3667025) B3667025
theorem B3259577 : Blo 2171435 3259577 := bstep (se 2 (by rfl) ⟨1222341, by rfl⟩ : syracuseStep 3259577 = 2444683) B2444683
theorem B2173051 : Blo 2171435 2173051 := bstep (se 1 (by rfl) ⟨1629788, by rfl⟩ : syracuseStep 2173051 = 3259577) B3259577
theorem B80379221 : Blo 2171435 80379221 := bbase (se 11 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 80379221 = 117743) (by norm_num)
theorem B214344589 : Blo 2171435 214344589 := bstep (se 3 (by rfl) ⟨40189610, by rfl⟩ : syracuseStep 214344589 = 80379221) B80379221
theorem B285792785 : Blo 2171435 285792785 := bstep (se 2 (by rfl) ⟨107172294, by rfl⟩ : syracuseStep 285792785 = 214344589) B214344589
theorem B190528523 : Blo 2171435 190528523 := bstep (se 1 (by rfl) ⟨142896392, by rfl⟩ : syracuseStep 190528523 = 285792785) B285792785
theorem B127019015 : Blo 2171435 127019015 := bstep (se 1 (by rfl) ⟨95264261, by rfl⟩ : syracuseStep 127019015 = 190528523) B190528523
theorem B84679343 : Blo 2171435 84679343 := bstep (se 1 (by rfl) ⟨63509507, by rfl⟩ : syracuseStep 84679343 = 127019015) B127019015
theorem B56452895 : Blo 2171435 56452895 := bstep (se 1 (by rfl) ⟨42339671, by rfl⟩ : syracuseStep 56452895 = 84679343) B84679343
theorem B37635263 : Blo 2171435 37635263 := bstep (se 1 (by rfl) ⟨28226447, by rfl⟩ : syracuseStep 37635263 = 56452895) B56452895
theorem B25090175 : Blo 2171435 25090175 := bstep (se 1 (by rfl) ⟨18817631, by rfl⟩ : syracuseStep 25090175 = 37635263) B37635263
theorem B66907133 : Blo 2171435 66907133 := bstep (se 3 (by rfl) ⟨12545087, by rfl⟩ : syracuseStep 66907133 = 25090175) B25090175
theorem B44604755 : Blo 2171435 44604755 := bstep (se 1 (by rfl) ⟨33453566, by rfl⟩ : syracuseStep 44604755 = 66907133) B66907133
theorem B29736503 : Blo 2171435 29736503 := bstep (se 1 (by rfl) ⟨22302377, by rfl⟩ : syracuseStep 29736503 = 44604755) B44604755
theorem B19824335 : Blo 2171435 19824335 := bstep (se 1 (by rfl) ⟨14868251, by rfl⟩ : syracuseStep 19824335 = 29736503) B29736503
theorem B13216223 : Blo 2171435 13216223 := bstep (se 1 (by rfl) ⟨9912167, by rfl⟩ : syracuseStep 13216223 = 19824335) B19824335
theorem B35243261 : Blo 2171435 35243261 := bstep (se 3 (by rfl) ⟨6608111, by rfl⟩ : syracuseStep 35243261 = 13216223) B13216223
theorem B23495507 : Blo 2171435 23495507 := bstep (se 1 (by rfl) ⟨17621630, by rfl⟩ : syracuseStep 23495507 = 35243261) B35243261
theorem B15663671 : Blo 2171435 15663671 := bstep (se 1 (by rfl) ⟨11747753, by rfl⟩ : syracuseStep 15663671 = 23495507) B23495507
theorem B10442447 : Blo 2171435 10442447 := bstep (se 1 (by rfl) ⟨7831835, by rfl⟩ : syracuseStep 10442447 = 15663671) B15663671
theorem B6961631 : Blo 2171435 6961631 := bstep (se 1 (by rfl) ⟨5221223, by rfl⟩ : syracuseStep 6961631 = 10442447) B10442447
theorem B18564349 : Blo 2171435 18564349 := bstep (se 3 (by rfl) ⟨3480815, by rfl⟩ : syracuseStep 18564349 = 6961631) B6961631
theorem B24752465 : Blo 2171435 24752465 := bstep (se 2 (by rfl) ⟨9282174, by rfl⟩ : syracuseStep 24752465 = 18564349) B18564349
theorem B16501643 : Blo 2171435 16501643 := bstep (se 1 (by rfl) ⟨12376232, by rfl⟩ : syracuseStep 16501643 = 24752465) B24752465
theorem B11001095 : Blo 2171435 11001095 := bstep (se 1 (by rfl) ⟨8250821, by rfl⟩ : syracuseStep 11001095 = 16501643) B16501643
theorem B7334063 : Blo 2171435 7334063 := bstep (se 1 (by rfl) ⟨5500547, by rfl⟩ : syracuseStep 7334063 = 11001095) B11001095
theorem B4889375 : Blo 2171435 4889375 := bstep (se 1 (by rfl) ⟨3667031, by rfl⟩ : syracuseStep 4889375 = 7334063) B7334063
theorem B3259583 : Blo 2171435 3259583 := bstep (se 1 (by rfl) ⟨2444687, by rfl⟩ : syracuseStep 3259583 = 4889375) B4889375
theorem B2173055 : Blo 2171435 2173055 := bstep (se 1 (by rfl) ⟨1629791, by rfl⟩ : syracuseStep 2173055 = 3259583) B3259583
theorem B3259589 : Blo 2171435 3259589 := bbase (se 4 (by rfl) ⟨305586, by rfl⟩ : syracuseStep 3259589 = 611173) (by norm_num)
theorem B2173059 : Blo 2171435 2173059 := bstep (se 1 (by rfl) ⟨1629794, by rfl⟩ : syracuseStep 2173059 = 3259589) B3259589
theorem B3667045 : Blo 2171435 3667045 := bbase (se 4 (by rfl) ⟨343785, by rfl⟩ : syracuseStep 3667045 = 687571) (by norm_num)
theorem B4889393 : Blo 2171435 4889393 := bstep (se 2 (by rfl) ⟨1833522, by rfl⟩ : syracuseStep 4889393 = 3667045) B3667045
theorem B3259595 : Blo 2171435 3259595 := bstep (se 1 (by rfl) ⟨2444696, by rfl⟩ : syracuseStep 3259595 = 4889393) B4889393
theorem B2173063 : Blo 2171435 2173063 := bstep (se 1 (by rfl) ⟨1629797, by rfl⟩ : syracuseStep 2173063 = 3259595) B3259595
theorem B2444701 : Blo 2171435 2444701 := bbase (se 3 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 2444701 = 916763) (by norm_num)
theorem B3259601 : Blo 2171435 3259601 := bstep (se 2 (by rfl) ⟨1222350, by rfl⟩ : syracuseStep 3259601 = 2444701) B2444701
theorem B2173067 : Blo 2171435 2173067 := bstep (se 1 (by rfl) ⟨1629800, by rfl⟩ : syracuseStep 2173067 = 3259601) B3259601
theorem B7334117 : Blo 2171435 7334117 := bbase (se 4 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 7334117 = 1375147) (by norm_num)
theorem B4889411 : Blo 2171435 4889411 := bstep (se 1 (by rfl) ⟨3667058, by rfl⟩ : syracuseStep 4889411 = 7334117) B7334117
theorem B3259607 : Blo 2171435 3259607 := bstep (se 1 (by rfl) ⟨2444705, by rfl⟩ : syracuseStep 3259607 = 4889411) B4889411
theorem B2173071 : Blo 2171435 2173071 := bstep (se 1 (by rfl) ⟨1629803, by rfl⟩ : syracuseStep 2173071 = 3259607) B3259607
theorem B3259613 : Blo 2171435 3259613 := bbase (se 3 (by rfl) ⟨611177, by rfl⟩ : syracuseStep 3259613 = 1222355) (by norm_num)
theorem B2173075 : Blo 2171435 2173075 := bstep (se 1 (by rfl) ⟨1629806, by rfl⟩ : syracuseStep 2173075 = 3259613) B3259613
theorem B4889429 : Blo 2171435 4889429 := bbase (se 9 (by rfl) ⟨14324, by rfl⟩ : syracuseStep 4889429 = 28649) (by norm_num)
theorem B3259619 : Blo 2171435 3259619 := bstep (se 1 (by rfl) ⟨2444714, by rfl⟩ : syracuseStep 3259619 = 4889429) B4889429
theorem B2173079 : Blo 2171435 2173079 := bstep (se 1 (by rfl) ⟨1629809, by rfl⟩ : syracuseStep 2173079 = 3259619) B3259619
theorem B6188197 : Blo 2171435 6188197 := bbase (se 4 (by rfl) ⟨580143, by rfl⟩ : syracuseStep 6188197 = 1160287) (by norm_num)
theorem B8250929 : Blo 2171435 8250929 := bstep (se 2 (by rfl) ⟨3094098, by rfl⟩ : syracuseStep 8250929 = 6188197) B6188197
theorem B5500619 : Blo 2171435 5500619 := bstep (se 1 (by rfl) ⟨4125464, by rfl⟩ : syracuseStep 5500619 = 8250929) B8250929
theorem B3667079 : Blo 2171435 3667079 := bstep (se 1 (by rfl) ⟨2750309, by rfl⟩ : syracuseStep 3667079 = 5500619) B5500619
theorem B2444719 : Blo 2171435 2444719 := bstep (se 1 (by rfl) ⟨1833539, by rfl⟩ : syracuseStep 2444719 = 3667079) B3667079
theorem B3259625 : Blo 2171435 3259625 := bstep (se 2 (by rfl) ⟨1222359, by rfl⟩ : syracuseStep 3259625 = 2444719) B2444719
theorem B2173083 : Blo 2171435 2173083 := bstep (se 1 (by rfl) ⟨1629812, by rfl⟩ : syracuseStep 2173083 = 3259625) B3259625
theorem B4956157 : Blo 2171435 4956157 := bbase (se 3 (by rfl) ⟨929279, by rfl⟩ : syracuseStep 4956157 = 1858559) (by norm_num)
theorem B6608209 : Blo 2171435 6608209 := bstep (se 2 (by rfl) ⟨2478078, by rfl⟩ : syracuseStep 6608209 = 4956157) B4956157
theorem B8810945 : Blo 2171435 8810945 := bstep (se 2 (by rfl) ⟨3304104, by rfl⟩ : syracuseStep 8810945 = 6608209) B6608209
theorem B5873963 : Blo 2171435 5873963 := bstep (se 1 (by rfl) ⟨4405472, by rfl⟩ : syracuseStep 5873963 = 8810945) B8810945
theorem B62655605 : Blo 2171435 62655605 := bstep (se 5 (by rfl) ⟨2936981, by rfl⟩ : syracuseStep 62655605 = 5873963) B5873963
theorem B41770403 : Blo 2171435 41770403 := bstep (se 1 (by rfl) ⟨31327802, by rfl⟩ : syracuseStep 41770403 = 62655605) B62655605
theorem B27846935 : Blo 2171435 27846935 := bstep (se 1 (by rfl) ⟨20885201, by rfl⟩ : syracuseStep 27846935 = 41770403) B41770403
theorem B18564623 : Blo 2171435 18564623 := bstep (se 1 (by rfl) ⟨13923467, by rfl⟩ : syracuseStep 18564623 = 27846935) B27846935
theorem B12376415 : Blo 2171435 12376415 := bstep (se 1 (by rfl) ⟨9282311, by rfl⟩ : syracuseStep 12376415 = 18564623) B18564623
theorem B8250943 : Blo 2171435 8250943 := bstep (se 1 (by rfl) ⟨6188207, by rfl⟩ : syracuseStep 8250943 = 12376415) B12376415
theorem B11001257 : Blo 2171435 11001257 := bstep (se 2 (by rfl) ⟨4125471, by rfl⟩ : syracuseStep 11001257 = 8250943) B8250943
theorem B7334171 : Blo 2171435 7334171 := bstep (se 1 (by rfl) ⟨5500628, by rfl⟩ : syracuseStep 7334171 = 11001257) B11001257
theorem B4889447 : Blo 2171435 4889447 := bstep (se 1 (by rfl) ⟨3667085, by rfl⟩ : syracuseStep 4889447 = 7334171) B7334171
theorem B3259631 : Blo 2171435 3259631 := bstep (se 1 (by rfl) ⟨2444723, by rfl⟩ : syracuseStep 3259631 = 4889447) B4889447
theorem B2173087 : Blo 2171435 2173087 := bstep (se 1 (by rfl) ⟨1629815, by rfl⟩ : syracuseStep 2173087 = 3259631) B3259631
theorem B3259637 : Blo 2171435 3259637 := bbase (se 5 (by rfl) ⟨152795, by rfl⟩ : syracuseStep 3259637 = 305591) (by norm_num)
theorem B2173091 : Blo 2171435 2173091 := bstep (se 1 (by rfl) ⟨1629818, by rfl⟩ : syracuseStep 2173091 = 3259637) B3259637
theorem B2202745 : Blo 2171435 2202745 := bbase (se 2 (by rfl) ⟨826029, by rfl⟩ : syracuseStep 2202745 = 1652059) (by norm_num)
theorem B2936993 : Blo 2171435 2936993 := bstep (se 2 (by rfl) ⟨1101372, by rfl⟩ : syracuseStep 2936993 = 2202745) B2202745
theorem B7831981 : Blo 2171435 7831981 := bstep (se 3 (by rfl) ⟨1468496, by rfl⟩ : syracuseStep 7831981 = 2936993) B2936993
theorem B10442641 : Blo 2171435 10442641 := bstep (se 2 (by rfl) ⟨3915990, by rfl⟩ : syracuseStep 10442641 = 7831981) B7831981
theorem B13923521 : Blo 2171435 13923521 := bstep (se 2 (by rfl) ⟨5221320, by rfl⟩ : syracuseStep 13923521 = 10442641) B10442641
theorem B9282347 : Blo 2171435 9282347 := bstep (se 1 (by rfl) ⟨6961760, by rfl⟩ : syracuseStep 9282347 = 13923521) B13923521
theorem B6188231 : Blo 2171435 6188231 := bstep (se 1 (by rfl) ⟨4641173, by rfl⟩ : syracuseStep 6188231 = 9282347) B9282347
theorem B4125487 : Blo 2171435 4125487 := bstep (se 1 (by rfl) ⟨3094115, by rfl⟩ : syracuseStep 4125487 = 6188231) B6188231
theorem B5500649 : Blo 2171435 5500649 := bstep (se 2 (by rfl) ⟨2062743, by rfl⟩ : syracuseStep 5500649 = 4125487) B4125487
theorem B3667099 : Blo 2171435 3667099 := bstep (se 1 (by rfl) ⟨2750324, by rfl⟩ : syracuseStep 3667099 = 5500649) B5500649
theorem B4889465 : Blo 2171435 4889465 := bstep (se 2 (by rfl) ⟨1833549, by rfl⟩ : syracuseStep 4889465 = 3667099) B3667099
theorem B3259643 : Blo 2171435 3259643 := bstep (se 1 (by rfl) ⟨2444732, by rfl⟩ : syracuseStep 3259643 = 4889465) B4889465
theorem B2173095 : Blo 2171435 2173095 := bstep (se 1 (by rfl) ⟨1629821, by rfl⟩ : syracuseStep 2173095 = 3259643) B3259643
theorem B2444737 : Blo 2171435 2444737 := bbase (se 2 (by rfl) ⟨916776, by rfl⟩ : syracuseStep 2444737 = 1833553) (by norm_num)
theorem B3259649 : Blo 2171435 3259649 := bstep (se 2 (by rfl) ⟨1222368, by rfl⟩ : syracuseStep 3259649 = 2444737) B2444737
theorem B2173099 : Blo 2171435 2173099 := bstep (se 1 (by rfl) ⟨1629824, by rfl⟩ : syracuseStep 2173099 = 3259649) B3259649
theorem B5500669 : Blo 2171435 5500669 := bbase (se 3 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 5500669 = 2062751) (by norm_num)
theorem B7334225 : Blo 2171435 7334225 := bstep (se 2 (by rfl) ⟨2750334, by rfl⟩ : syracuseStep 7334225 = 5500669) B5500669
theorem B4889483 : Blo 2171435 4889483 := bstep (se 1 (by rfl) ⟨3667112, by rfl⟩ : syracuseStep 4889483 = 7334225) B7334225
theorem B3259655 : Blo 2171435 3259655 := bstep (se 1 (by rfl) ⟨2444741, by rfl⟩ : syracuseStep 3259655 = 4889483) B4889483
theorem B2173103 : Blo 2171435 2173103 := bstep (se 1 (by rfl) ⟨1629827, by rfl⟩ : syracuseStep 2173103 = 3259655) B3259655
theorem B3259661 : Blo 2171435 3259661 := bbase (se 3 (by rfl) ⟨611186, by rfl⟩ : syracuseStep 3259661 = 1222373) (by norm_num)
theorem B2173107 : Blo 2171435 2173107 := bstep (se 1 (by rfl) ⟨1629830, by rfl⟩ : syracuseStep 2173107 = 3259661) B3259661
theorem B4889501 : Blo 2171435 4889501 := bbase (se 3 (by rfl) ⟨916781, by rfl⟩ : syracuseStep 4889501 = 1833563) (by norm_num)
theorem B3259667 : Blo 2171435 3259667 := bstep (se 1 (by rfl) ⟨2444750, by rfl⟩ : syracuseStep 3259667 = 4889501) B4889501
theorem B2173111 : Blo 2171435 2173111 := bstep (se 1 (by rfl) ⟨1629833, by rfl⟩ : syracuseStep 2173111 = 3259667) B3259667
theorem B3667133 : Blo 2171435 3667133 := bbase (se 3 (by rfl) ⟨687587, by rfl⟩ : syracuseStep 3667133 = 1375175) (by norm_num)
theorem B2444755 : Blo 2171435 2444755 := bstep (se 1 (by rfl) ⟨1833566, by rfl⟩ : syracuseStep 2444755 = 3667133) B3667133
theorem B3259673 : Blo 2171435 3259673 := bstep (se 2 (by rfl) ⟨1222377, by rfl⟩ : syracuseStep 3259673 = 2444755) B2444755
theorem B2173115 : Blo 2171435 2173115 := bstep (se 1 (by rfl) ⟨1629836, by rfl⟩ : syracuseStep 2173115 = 3259673) B3259673
theorem B12376597 : Blo 2171435 12376597 := bbase (se 6 (by rfl) ⟨290076, by rfl⟩ : syracuseStep 12376597 = 580153) (by norm_num)
theorem B16502129 : Blo 2171435 16502129 := bstep (se 2 (by rfl) ⟨6188298, by rfl⟩ : syracuseStep 16502129 = 12376597) B12376597
theorem B11001419 : Blo 2171435 11001419 := bstep (se 1 (by rfl) ⟨8251064, by rfl⟩ : syracuseStep 11001419 = 16502129) B16502129
theorem B7334279 : Blo 2171435 7334279 := bstep (se 1 (by rfl) ⟨5500709, by rfl⟩ : syracuseStep 7334279 = 11001419) B11001419
theorem B4889519 : Blo 2171435 4889519 := bstep (se 1 (by rfl) ⟨3667139, by rfl⟩ : syracuseStep 4889519 = 7334279) B7334279
theorem B3259679 : Blo 2171435 3259679 := bstep (se 1 (by rfl) ⟨2444759, by rfl⟩ : syracuseStep 3259679 = 4889519) B4889519
theorem B2173119 : Blo 2171435 2173119 := bstep (se 1 (by rfl) ⟨1629839, by rfl⟩ : syracuseStep 2173119 = 3259679) B3259679
theorem B3259685 : Blo 2171435 3259685 := bbase (se 4 (by rfl) ⟨305595, by rfl⟩ : syracuseStep 3259685 = 611191) (by norm_num)
theorem B2173123 : Blo 2171435 2173123 := bstep (se 1 (by rfl) ⟨1629842, by rfl⟩ : syracuseStep 2173123 = 3259685) B3259685
theorem B2750365 : Blo 2171435 2750365 := bbase (se 3 (by rfl) ⟨515693, by rfl⟩ : syracuseStep 2750365 = 1031387) (by norm_num)
theorem B3667153 : Blo 2171435 3667153 := bstep (se 2 (by rfl) ⟨1375182, by rfl⟩ : syracuseStep 3667153 = 2750365) B2750365
theorem B4889537 : Blo 2171435 4889537 := bstep (se 2 (by rfl) ⟨1833576, by rfl⟩ : syracuseStep 4889537 = 3667153) B3667153
theorem B3259691 : Blo 2171435 3259691 := bstep (se 1 (by rfl) ⟨2444768, by rfl⟩ : syracuseStep 3259691 = 4889537) B4889537
theorem B2173127 : Blo 2171435 2173127 := bstep (se 1 (by rfl) ⟨1629845, by rfl⟩ : syracuseStep 2173127 = 3259691) B3259691
theorem B2444773 : Blo 2171435 2444773 := bbase (se 4 (by rfl) ⟨229197, by rfl⟩ : syracuseStep 2444773 = 458395) (by norm_num)
theorem B3259697 : Blo 2171435 3259697 := bstep (se 2 (by rfl) ⟨1222386, by rfl⟩ : syracuseStep 3259697 = 2444773) B2444773
theorem B2173131 : Blo 2171435 2173131 := bstep (se 1 (by rfl) ⟨1629848, by rfl⟩ : syracuseStep 2173131 = 3259697) B3259697
theorem B2787901 : Blo 2171435 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B14868805 : Blo 2171435 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B19825073 : Blo 2171435 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B13216715 : Blo 2171435 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B8811143 : Blo 2171435 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B5874095 : Blo 2171435 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B3916063 : Blo 2171435 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B5221417 : Blo 2171435 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B6961889 : Blo 2171435 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B4641259 : Blo 2171435 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B6188345 : Blo 2171435 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B4125563 : Blo 2171435 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B2750375 : Blo 2171435 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B7334333 : Blo 2171435 7334333 := bstep (se 3 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 7334333 = 2750375) B2750375
theorem B4889555 : Blo 2171435 4889555 := bstep (se 1 (by rfl) ⟨3667166, by rfl⟩ : syracuseStep 4889555 = 7334333) B7334333
theorem B3259703 : Blo 2171435 3259703 := bstep (se 1 (by rfl) ⟨2444777, by rfl⟩ : syracuseStep 3259703 = 4889555) B4889555
theorem B2173135 : Blo 2171435 2173135 := bstep (se 1 (by rfl) ⟨1629851, by rfl⟩ : syracuseStep 2173135 = 3259703) B3259703
theorem B3259709 : Blo 2171435 3259709 := bbase (se 3 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 3259709 = 1222391) (by norm_num)
theorem B2173139 : Blo 2171435 2173139 := bstep (se 1 (by rfl) ⟨1629854, by rfl⟩ : syracuseStep 2173139 = 3259709) B3259709
theorem B4889573 : Blo 2171435 4889573 := bbase (se 4 (by rfl) ⟨458397, by rfl⟩ : syracuseStep 4889573 = 916795) (by norm_num)
theorem B3259715 : Blo 2171435 3259715 := bstep (se 1 (by rfl) ⟨2444786, by rfl⟩ : syracuseStep 3259715 = 4889573) B4889573
theorem B2173143 : Blo 2171435 2173143 := bstep (se 1 (by rfl) ⟨1629857, by rfl⟩ : syracuseStep 2173143 = 3259715) B3259715
theorem B5500781 : Blo 2171435 5500781 := bbase (se 3 (by rfl) ⟨1031396, by rfl⟩ : syracuseStep 5500781 = 2062793) (by norm_num)
theorem B3667187 : Blo 2171435 3667187 := bstep (se 1 (by rfl) ⟨2750390, by rfl⟩ : syracuseStep 3667187 = 5500781) B5500781
theorem B2444791 : Blo 2171435 2444791 := bstep (se 1 (by rfl) ⟨1833593, by rfl⟩ : syracuseStep 2444791 = 3667187) B3667187
theorem B3259721 : Blo 2171435 3259721 := bstep (se 2 (by rfl) ⟨1222395, by rfl⟩ : syracuseStep 3259721 = 2444791) B2444791
theorem B2173147 : Blo 2171435 2173147 := bstep (se 1 (by rfl) ⟨1629860, by rfl⟩ : syracuseStep 2173147 = 3259721) B3259721
theorem B4641293 : Blo 2171435 4641293 := bbase (se 3 (by rfl) ⟨870242, by rfl⟩ : syracuseStep 4641293 = 1740485) (by norm_num)
theorem B3094195 : Blo 2171435 3094195 := bstep (se 1 (by rfl) ⟨2320646, by rfl⟩ : syracuseStep 3094195 = 4641293) B4641293
theorem B4125593 : Blo 2171435 4125593 := bstep (se 2 (by rfl) ⟨1547097, by rfl⟩ : syracuseStep 4125593 = 3094195) B3094195
theorem B11001581 : Blo 2171435 11001581 := bstep (se 3 (by rfl) ⟨2062796, by rfl⟩ : syracuseStep 11001581 = 4125593) B4125593
theorem B7334387 : Blo 2171435 7334387 := bstep (se 1 (by rfl) ⟨5500790, by rfl⟩ : syracuseStep 7334387 = 11001581) B11001581
theorem B4889591 : Blo 2171435 4889591 := bstep (se 1 (by rfl) ⟨3667193, by rfl⟩ : syracuseStep 4889591 = 7334387) B7334387
theorem B3259727 : Blo 2171435 3259727 := bstep (se 1 (by rfl) ⟨2444795, by rfl⟩ : syracuseStep 3259727 = 4889591) B4889591
theorem B2173151 : Blo 2171435 2173151 := bstep (se 1 (by rfl) ⟨1629863, by rfl⟩ : syracuseStep 2173151 = 3259727) B3259727
theorem B3259733 : Blo 2171435 3259733 := bbase (se 11 (by rfl) ⟨2387, by rfl⟩ : syracuseStep 3259733 = 4775) (by norm_num)
theorem B2173155 : Blo 2171435 2173155 := bstep (se 1 (by rfl) ⟨1629866, by rfl⟩ : syracuseStep 2173155 = 3259733) B3259733
theorem B7832213 : Blo 2171435 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B5221475 : Blo 2171435 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B3480983 : Blo 2171435 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B2320655 : Blo 2171435 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B6188413 : Blo 2171435 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B8251217 : Blo 2171435 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B5500811 : Blo 2171435 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B3667207 : Blo 2171435 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B4889609 : Blo 2171435 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B3259739 : Blo 2171435 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B2173159 : Blo 2171435 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B2444809 : Blo 2171435 2444809 := bbase (se 2 (by rfl) ⟨916803, by rfl⟩ : syracuseStep 2444809 = 1833607) (by norm_num)
theorem B3259745 : Blo 2171435 3259745 := bstep (se 2 (by rfl) ⟨1222404, by rfl⟩ : syracuseStep 3259745 = 2444809) B2444809
theorem B2173163 : Blo 2171435 2173163 := bstep (se 1 (by rfl) ⟨1629872, by rfl⟩ : syracuseStep 2173163 = 3259745) B3259745
theorem B2787941 : Blo 2171435 2787941 := bbase (se 4 (by rfl) ⟨261369, by rfl⟩ : syracuseStep 2787941 = 522739) (by norm_num)
theorem B7434509 : Blo 2171435 7434509 := bstep (se 3 (by rfl) ⟨1393970, by rfl⟩ : syracuseStep 7434509 = 2787941) B2787941
theorem B19825357 : Blo 2171435 19825357 := bstep (se 3 (by rfl) ⟨3717254, by rfl⟩ : syracuseStep 19825357 = 7434509) B7434509
theorem B26433809 : Blo 2171435 26433809 := bstep (se 2 (by rfl) ⟨9912678, by rfl⟩ : syracuseStep 26433809 = 19825357) B19825357
theorem B17622539 : Blo 2171435 17622539 := bstep (se 1 (by rfl) ⟨13216904, by rfl⟩ : syracuseStep 17622539 = 26433809) B26433809
theorem B11748359 : Blo 2171435 11748359 := bstep (se 1 (by rfl) ⟨8811269, by rfl⟩ : syracuseStep 11748359 = 17622539) B17622539
theorem B31328957 : Blo 2171435 31328957 := bstep (se 3 (by rfl) ⟨5874179, by rfl⟩ : syracuseStep 31328957 = 11748359) B11748359
theorem B20885971 : Blo 2171435 20885971 := bstep (se 1 (by rfl) ⟨15664478, by rfl⟩ : syracuseStep 20885971 = 31328957) B31328957
theorem B27847961 : Blo 2171435 27847961 := bstep (se 2 (by rfl) ⟨10442985, by rfl⟩ : syracuseStep 27847961 = 20885971) B20885971
theorem B18565307 : Blo 2171435 18565307 := bstep (se 1 (by rfl) ⟨13923980, by rfl⟩ : syracuseStep 18565307 = 27847961) B27847961
theorem B12376871 : Blo 2171435 12376871 := bstep (se 1 (by rfl) ⟨9282653, by rfl⟩ : syracuseStep 12376871 = 18565307) B18565307
theorem B8251247 : Blo 2171435 8251247 := bstep (se 1 (by rfl) ⟨6188435, by rfl⟩ : syracuseStep 8251247 = 12376871) B12376871
theorem B5500831 : Blo 2171435 5500831 := bstep (se 1 (by rfl) ⟨4125623, by rfl⟩ : syracuseStep 5500831 = 8251247) B8251247
theorem B7334441 : Blo 2171435 7334441 := bstep (se 2 (by rfl) ⟨2750415, by rfl⟩ : syracuseStep 7334441 = 5500831) B5500831
theorem B4889627 : Blo 2171435 4889627 := bstep (se 1 (by rfl) ⟨3667220, by rfl⟩ : syracuseStep 4889627 = 7334441) B7334441
theorem B3259751 : Blo 2171435 3259751 := bstep (se 1 (by rfl) ⟨2444813, by rfl⟩ : syracuseStep 3259751 = 4889627) B4889627
theorem B2173167 : Blo 2171435 2173167 := bstep (se 1 (by rfl) ⟨1629875, by rfl⟩ : syracuseStep 2173167 = 3259751) B3259751
theorem B3259757 : Blo 2171435 3259757 := bbase (se 3 (by rfl) ⟨611204, by rfl⟩ : syracuseStep 3259757 = 1222409) (by norm_num)
theorem B2173171 : Blo 2171435 2173171 := bstep (se 1 (by rfl) ⟨1629878, by rfl⟩ : syracuseStep 2173171 = 3259757) B3259757
theorem B4889645 : Blo 2171435 4889645 := bbase (se 3 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 4889645 = 1833617) (by norm_num)
theorem B3259763 : Blo 2171435 3259763 := bstep (se 1 (by rfl) ⟨2444822, by rfl⟩ : syracuseStep 3259763 = 4889645) B4889645
theorem B2173175 : Blo 2171435 2173175 := bstep (se 1 (by rfl) ⟨1629881, by rfl⟩ : syracuseStep 2173175 = 3259763) B3259763
theorem B4405661 : Blo 2171435 4405661 := bbase (se 3 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 4405661 = 1652123) (by norm_num)
theorem B2937107 : Blo 2171435 2937107 := bstep (se 1 (by rfl) ⟨2202830, by rfl⟩ : syracuseStep 2937107 = 4405661) B4405661
theorem B7832285 : Blo 2171435 7832285 := bstep (se 3 (by rfl) ⟨1468553, by rfl⟩ : syracuseStep 7832285 = 2937107) B2937107
theorem B5221523 : Blo 2171435 5221523 := bstep (se 1 (by rfl) ⟨3916142, by rfl⟩ : syracuseStep 5221523 = 7832285) B7832285
theorem B13924061 : Blo 2171435 13924061 := bstep (se 3 (by rfl) ⟨2610761, by rfl⟩ : syracuseStep 13924061 = 5221523) B5221523
theorem B9282707 : Blo 2171435 9282707 := bstep (se 1 (by rfl) ⟨6962030, by rfl⟩ : syracuseStep 9282707 = 13924061) B13924061
theorem B6188471 : Blo 2171435 6188471 := bstep (se 1 (by rfl) ⟨4641353, by rfl⟩ : syracuseStep 6188471 = 9282707) B9282707
theorem B4125647 : Blo 2171435 4125647 := bstep (se 1 (by rfl) ⟨3094235, by rfl⟩ : syracuseStep 4125647 = 6188471) B6188471
theorem B2750431 : Blo 2171435 2750431 := bstep (se 1 (by rfl) ⟨2062823, by rfl⟩ : syracuseStep 2750431 = 4125647) B4125647
theorem B3667241 : Blo 2171435 3667241 := bstep (se 2 (by rfl) ⟨1375215, by rfl⟩ : syracuseStep 3667241 = 2750431) B2750431
theorem B2444827 : Blo 2171435 2444827 := bstep (se 1 (by rfl) ⟨1833620, by rfl⟩ : syracuseStep 2444827 = 3667241) B3667241
theorem B3259769 : Blo 2171435 3259769 := bstep (se 2 (by rfl) ⟨1222413, by rfl⟩ : syracuseStep 3259769 = 2444827) B2444827
theorem B2173179 : Blo 2171435 2173179 := bstep (se 1 (by rfl) ⟨1629884, by rfl⟩ : syracuseStep 2173179 = 3259769) B3259769
theorem B21752725 : Blo 2171435 21752725 := bbase (se 6 (by rfl) ⟨509829, by rfl⟩ : syracuseStep 21752725 = 1019659) (by norm_num)
theorem B29003633 : Blo 2171435 29003633 := bstep (se 2 (by rfl) ⟨10876362, by rfl⟩ : syracuseStep 29003633 = 21752725) B21752725
theorem B19335755 : Blo 2171435 19335755 := bstep (se 1 (by rfl) ⟨14501816, by rfl⟩ : syracuseStep 19335755 = 29003633) B29003633
theorem B12890503 : Blo 2171435 12890503 := bstep (se 1 (by rfl) ⟨9667877, by rfl⟩ : syracuseStep 12890503 = 19335755) B19335755
theorem B17187337 : Blo 2171435 17187337 := bstep (se 2 (by rfl) ⟨6445251, by rfl⟩ : syracuseStep 17187337 = 12890503) B12890503
theorem B22916449 : Blo 2171435 22916449 := bstep (se 2 (by rfl) ⟨8593668, by rfl⟩ : syracuseStep 22916449 = 17187337) B17187337
theorem B30555265 : Blo 2171435 30555265 := bstep (se 2 (by rfl) ⟨11458224, by rfl⟩ : syracuseStep 30555265 = 22916449) B22916449
theorem B40740353 : Blo 2171435 40740353 := bstep (se 2 (by rfl) ⟨15277632, by rfl⟩ : syracuseStep 40740353 = 30555265) B30555265
theorem B27160235 : Blo 2171435 27160235 := bstep (se 1 (by rfl) ⟨20370176, by rfl⟩ : syracuseStep 27160235 = 40740353) B40740353
theorem B18106823 : Blo 2171435 18106823 := bstep (se 1 (by rfl) ⟨13580117, by rfl⟩ : syracuseStep 18106823 = 27160235) B27160235
theorem B12071215 : Blo 2171435 12071215 := bstep (se 1 (by rfl) ⟨9053411, by rfl⟩ : syracuseStep 12071215 = 18106823) B18106823
theorem B16094953 : Blo 2171435 16094953 := bstep (se 2 (by rfl) ⟨6035607, by rfl⟩ : syracuseStep 16094953 = 12071215) B12071215
theorem B21459937 : Blo 2171435 21459937 := bstep (se 2 (by rfl) ⟨8047476, by rfl⟩ : syracuseStep 21459937 = 16094953) B16094953
theorem B28613249 : Blo 2171435 28613249 := bstep (se 2 (by rfl) ⟨10729968, by rfl⟩ : syracuseStep 28613249 = 21459937) B21459937
theorem B19075499 : Blo 2171435 19075499 := bstep (se 1 (by rfl) ⟨14306624, by rfl⟩ : syracuseStep 19075499 = 28613249) B28613249
theorem B12716999 : Blo 2171435 12716999 := bstep (se 1 (by rfl) ⟨9537749, by rfl⟩ : syracuseStep 12716999 = 19075499) B19075499
theorem B8477999 : Blo 2171435 8477999 := bstep (se 1 (by rfl) ⟨6358499, by rfl⟩ : syracuseStep 8477999 = 12716999) B12716999
theorem B5651999 : Blo 2171435 5651999 := bstep (se 1 (by rfl) ⟨4238999, by rfl⟩ : syracuseStep 5651999 = 8477999) B8477999
theorem B3767999 : Blo 2171435 3767999 := bstep (se 1 (by rfl) ⟨2825999, by rfl⟩ : syracuseStep 3767999 = 5651999) B5651999
theorem B10047997 : Blo 2171435 10047997 := bstep (se 3 (by rfl) ⟨1883999, by rfl⟩ : syracuseStep 10047997 = 3767999) B3767999
theorem B13397329 : Blo 2171435 13397329 := bstep (se 2 (by rfl) ⟨5023998, by rfl⟩ : syracuseStep 13397329 = 10047997) B10047997
theorem B17863105 : Blo 2171435 17863105 := bstep (se 2 (by rfl) ⟨6698664, by rfl⟩ : syracuseStep 17863105 = 13397329) B13397329
theorem B23817473 : Blo 2171435 23817473 := bstep (se 2 (by rfl) ⟨8931552, by rfl⟩ : syracuseStep 23817473 = 17863105) B17863105
theorem B15878315 : Blo 2171435 15878315 := bstep (se 1 (by rfl) ⟨11908736, by rfl⟩ : syracuseStep 15878315 = 23817473) B23817473
theorem B42342173 : Blo 2171435 42342173 := bstep (se 3 (by rfl) ⟨7939157, by rfl⟩ : syracuseStep 42342173 = 15878315) B15878315
theorem B28228115 : Blo 2171435 28228115 := bstep (se 1 (by rfl) ⟨21171086, by rfl⟩ : syracuseStep 28228115 = 42342173) B42342173
theorem B18818743 : Blo 2171435 18818743 := bstep (se 1 (by rfl) ⟨14114057, by rfl⟩ : syracuseStep 18818743 = 28228115) B28228115
theorem B25091657 : Blo 2171435 25091657 := bstep (se 2 (by rfl) ⟨9409371, by rfl⟩ : syracuseStep 25091657 = 18818743) B18818743
theorem B16727771 : Blo 2171435 16727771 := bstep (se 1 (by rfl) ⟨12545828, by rfl⟩ : syracuseStep 16727771 = 25091657) B25091657
theorem B11151847 : Blo 2171435 11151847 := bstep (se 1 (by rfl) ⟨8363885, by rfl⟩ : syracuseStep 11151847 = 16727771) B16727771
theorem B14869129 : Blo 2171435 14869129 := bstep (se 2 (by rfl) ⟨5575923, by rfl⟩ : syracuseStep 14869129 = 11151847) B11151847
theorem B19825505 : Blo 2171435 19825505 := bstep (se 2 (by rfl) ⟨7434564, by rfl⟩ : syracuseStep 19825505 = 14869129) B14869129
theorem B13217003 : Blo 2171435 13217003 := bstep (se 1 (by rfl) ⟨9912752, by rfl⟩ : syracuseStep 13217003 = 19825505) B19825505
theorem B8811335 : Blo 2171435 8811335 := bstep (se 1 (by rfl) ⟨6608501, by rfl⟩ : syracuseStep 8811335 = 13217003) B13217003
theorem B5874223 : Blo 2171435 5874223 := bstep (se 1 (by rfl) ⟨4405667, by rfl⟩ : syracuseStep 5874223 = 8811335) B8811335
theorem B7832297 : Blo 2171435 7832297 := bstep (se 2 (by rfl) ⟨2937111, by rfl⟩ : syracuseStep 7832297 = 5874223) B5874223
theorem B5221531 : Blo 2171435 5221531 := bstep (se 1 (by rfl) ⟨3916148, by rfl⟩ : syracuseStep 5221531 = 7832297) B7832297
theorem B6962041 : Blo 2171435 6962041 := bstep (se 2 (by rfl) ⟨2610765, by rfl⟩ : syracuseStep 6962041 = 5221531) B5221531
theorem B37130885 : Blo 2171435 37130885 := bstep (se 4 (by rfl) ⟨3481020, by rfl⟩ : syracuseStep 37130885 = 6962041) B6962041
theorem B24753923 : Blo 2171435 24753923 := bstep (se 1 (by rfl) ⟨18565442, by rfl⟩ : syracuseStep 24753923 = 37130885) B37130885
theorem B16502615 : Blo 2171435 16502615 := bstep (se 1 (by rfl) ⟨12376961, by rfl⟩ : syracuseStep 16502615 = 24753923) B24753923
theorem B11001743 : Blo 2171435 11001743 := bstep (se 1 (by rfl) ⟨8251307, by rfl⟩ : syracuseStep 11001743 = 16502615) B16502615
theorem B7334495 : Blo 2171435 7334495 := bstep (se 1 (by rfl) ⟨5500871, by rfl⟩ : syracuseStep 7334495 = 11001743) B11001743
theorem B4889663 : Blo 2171435 4889663 := bstep (se 1 (by rfl) ⟨3667247, by rfl⟩ : syracuseStep 4889663 = 7334495) B7334495
theorem B3259775 : Blo 2171435 3259775 := bstep (se 1 (by rfl) ⟨2444831, by rfl⟩ : syracuseStep 3259775 = 4889663) B4889663
theorem B2173183 : Blo 2171435 2173183 := bstep (se 1 (by rfl) ⟨1629887, by rfl⟩ : syracuseStep 2173183 = 3259775) B3259775
theorem B3259781 : Blo 2171435 3259781 := bbase (se 4 (by rfl) ⟨305604, by rfl⟩ : syracuseStep 3259781 = 611209) (by norm_num)
theorem B2173187 : Blo 2171435 2173187 := bstep (se 1 (by rfl) ⟨1629890, by rfl⟩ : syracuseStep 2173187 = 3259781) B3259781
theorem B3667261 : Blo 2171435 3667261 := bbase (se 3 (by rfl) ⟨687611, by rfl⟩ : syracuseStep 3667261 = 1375223) (by norm_num)
theorem B4889681 : Blo 2171435 4889681 := bstep (se 2 (by rfl) ⟨1833630, by rfl⟩ : syracuseStep 4889681 = 3667261) B3667261
theorem B3259787 : Blo 2171435 3259787 := bstep (se 1 (by rfl) ⟨2444840, by rfl⟩ : syracuseStep 3259787 = 4889681) B4889681
theorem B2173191 : Blo 2171435 2173191 := bstep (se 1 (by rfl) ⟨1629893, by rfl⟩ : syracuseStep 2173191 = 3259787) B3259787
theorem B2444845 : Blo 2171435 2444845 := bbase (se 3 (by rfl) ⟨458408, by rfl⟩ : syracuseStep 2444845 = 916817) (by norm_num)
theorem B3259793 : Blo 2171435 3259793 := bstep (se 2 (by rfl) ⟨1222422, by rfl⟩ : syracuseStep 3259793 = 2444845) B2444845
theorem B2173195 : Blo 2171435 2173195 := bstep (se 1 (by rfl) ⟨1629896, by rfl⟩ : syracuseStep 2173195 = 3259793) B3259793
theorem B7334549 : Blo 2171435 7334549 := bbase (se 6 (by rfl) ⟨171903, by rfl⟩ : syracuseStep 7334549 = 343807) (by norm_num)
theorem B4889699 : Blo 2171435 4889699 := bstep (se 1 (by rfl) ⟨3667274, by rfl⟩ : syracuseStep 4889699 = 7334549) B7334549
theorem B3259799 : Blo 2171435 3259799 := bstep (se 1 (by rfl) ⟨2444849, by rfl⟩ : syracuseStep 3259799 = 4889699) B4889699
theorem B2173199 : Blo 2171435 2173199 := bstep (se 1 (by rfl) ⟨1629899, by rfl⟩ : syracuseStep 2173199 = 3259799) B3259799
theorem B3259805 : Blo 2171435 3259805 := bbase (se 3 (by rfl) ⟨611213, by rfl⟩ : syracuseStep 3259805 = 1222427) (by norm_num)
theorem B2173203 : Blo 2171435 2173203 := bstep (se 1 (by rfl) ⟨1629902, by rfl⟩ : syracuseStep 2173203 = 3259805) B3259805
theorem B4889717 : Blo 2171435 4889717 := bbase (se 5 (by rfl) ⟨229205, by rfl⟩ : syracuseStep 4889717 = 458411) (by norm_num)
theorem B3259811 : Blo 2171435 3259811 := bstep (se 1 (by rfl) ⟨2444858, by rfl⟩ : syracuseStep 3259811 = 4889717) B4889717
theorem B2173207 : Blo 2171435 2173207 := bstep (se 1 (by rfl) ⟨1629905, by rfl⟩ : syracuseStep 2173207 = 3259811) B3259811
theorem B18565685 : Blo 2171435 18565685 := bbase (se 5 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 18565685 = 1740533) (by norm_num)
theorem B12377123 : Blo 2171435 12377123 := bstep (se 1 (by rfl) ⟨9282842, by rfl⟩ : syracuseStep 12377123 = 18565685) B18565685
theorem B8251415 : Blo 2171435 8251415 := bstep (se 1 (by rfl) ⟨6188561, by rfl⟩ : syracuseStep 8251415 = 12377123) B12377123
theorem B5500943 : Blo 2171435 5500943 := bstep (se 1 (by rfl) ⟨4125707, by rfl⟩ : syracuseStep 5500943 = 8251415) B8251415
theorem B3667295 : Blo 2171435 3667295 := bstep (se 1 (by rfl) ⟨2750471, by rfl⟩ : syracuseStep 3667295 = 5500943) B5500943
theorem B2444863 : Blo 2171435 2444863 := bstep (se 1 (by rfl) ⟨1833647, by rfl⟩ : syracuseStep 2444863 = 3667295) B3667295
theorem B3259817 : Blo 2171435 3259817 := bstep (se 2 (by rfl) ⟨1222431, by rfl⟩ : syracuseStep 3259817 = 2444863) B2444863
theorem B2173211 : Blo 2171435 2173211 := bstep (se 1 (by rfl) ⟨1629908, by rfl⟩ : syracuseStep 2173211 = 3259817) B3259817
theorem B8251429 : Blo 2171435 8251429 := bbase (se 4 (by rfl) ⟨773571, by rfl⟩ : syracuseStep 8251429 = 1547143) (by norm_num)
theorem B11001905 : Blo 2171435 11001905 := bstep (se 2 (by rfl) ⟨4125714, by rfl⟩ : syracuseStep 11001905 = 8251429) B8251429
theorem B7334603 : Blo 2171435 7334603 := bstep (se 1 (by rfl) ⟨5500952, by rfl⟩ : syracuseStep 7334603 = 11001905) B11001905
theorem B4889735 : Blo 2171435 4889735 := bstep (se 1 (by rfl) ⟨3667301, by rfl⟩ : syracuseStep 4889735 = 7334603) B7334603
theorem B3259823 : Blo 2171435 3259823 := bstep (se 1 (by rfl) ⟨2444867, by rfl⟩ : syracuseStep 3259823 = 4889735) B4889735
theorem B2173215 : Blo 2171435 2173215 := bstep (se 1 (by rfl) ⟨1629911, by rfl⟩ : syracuseStep 2173215 = 3259823) B3259823
theorem B3259829 : Blo 2171435 3259829 := bbase (se 5 (by rfl) ⟨152804, by rfl⟩ : syracuseStep 3259829 = 305609) (by norm_num)
theorem B2173219 : Blo 2171435 2173219 := bstep (se 1 (by rfl) ⟨1629914, by rfl⟩ : syracuseStep 2173219 = 3259829) B3259829
theorem B5500973 : Blo 2171435 5500973 := bbase (se 3 (by rfl) ⟨1031432, by rfl⟩ : syracuseStep 5500973 = 2062865) (by norm_num)
theorem B3667315 : Blo 2171435 3667315 := bstep (se 1 (by rfl) ⟨2750486, by rfl⟩ : syracuseStep 3667315 = 5500973) B5500973
theorem B4889753 : Blo 2171435 4889753 := bstep (se 2 (by rfl) ⟨1833657, by rfl⟩ : syracuseStep 4889753 = 3667315) B3667315
theorem B3259835 : Blo 2171435 3259835 := bstep (se 1 (by rfl) ⟨2444876, by rfl⟩ : syracuseStep 3259835 = 4889753) B4889753
theorem B2173223 : Blo 2171435 2173223 := bstep (se 1 (by rfl) ⟨1629917, by rfl⟩ : syracuseStep 2173223 = 3259835) B3259835
theorem B2444881 : Blo 2171435 2444881 := bbase (se 2 (by rfl) ⟨916830, by rfl⟩ : syracuseStep 2444881 = 1833661) (by norm_num)
theorem B3259841 : Blo 2171435 3259841 := bstep (se 2 (by rfl) ⟨1222440, by rfl⟩ : syracuseStep 3259841 = 2444881) B2444881
theorem B2173227 : Blo 2171435 2173227 := bstep (se 1 (by rfl) ⟨1629920, by rfl⟩ : syracuseStep 2173227 = 3259841) B3259841
theorem B3094309 : Blo 2171435 3094309 := bbase (se 4 (by rfl) ⟨290091, by rfl⟩ : syracuseStep 3094309 = 580183) (by norm_num)
theorem B4125745 : Blo 2171435 4125745 := bstep (se 2 (by rfl) ⟨1547154, by rfl⟩ : syracuseStep 4125745 = 3094309) B3094309
theorem B5500993 : Blo 2171435 5500993 := bstep (se 2 (by rfl) ⟨2062872, by rfl⟩ : syracuseStep 5500993 = 4125745) B4125745
theorem B7334657 : Blo 2171435 7334657 := bstep (se 2 (by rfl) ⟨2750496, by rfl⟩ : syracuseStep 7334657 = 5500993) B5500993
theorem B4889771 : Blo 2171435 4889771 := bstep (se 1 (by rfl) ⟨3667328, by rfl⟩ : syracuseStep 4889771 = 7334657) B7334657
theorem B3259847 : Blo 2171435 3259847 := bstep (se 1 (by rfl) ⟨2444885, by rfl⟩ : syracuseStep 3259847 = 4889771) B4889771
theorem B2173231 : Blo 2171435 2173231 := bstep (se 1 (by rfl) ⟨1629923, by rfl⟩ : syracuseStep 2173231 = 3259847) B3259847
theorem B3259853 : Blo 2171435 3259853 := bbase (se 3 (by rfl) ⟨611222, by rfl⟩ : syracuseStep 3259853 = 1222445) (by norm_num)
theorem B2173235 : Blo 2171435 2173235 := bstep (se 1 (by rfl) ⟨1629926, by rfl⟩ : syracuseStep 2173235 = 3259853) B3259853
theorem B4889789 : Blo 2171435 4889789 := bbase (se 3 (by rfl) ⟨916835, by rfl⟩ : syracuseStep 4889789 = 1833671) (by norm_num)
theorem B3259859 : Blo 2171435 3259859 := bstep (se 1 (by rfl) ⟨2444894, by rfl⟩ : syracuseStep 3259859 = 4889789) B4889789
theorem B2173239 : Blo 2171435 2173239 := bstep (se 1 (by rfl) ⟨1629929, by rfl⟩ : syracuseStep 2173239 = 3259859) B3259859
theorem B3667349 : Blo 2171435 3667349 := bbase (se 6 (by rfl) ⟨85953, by rfl⟩ : syracuseStep 3667349 = 171907) (by norm_num)
theorem B2444899 : Blo 2171435 2444899 := bstep (se 1 (by rfl) ⟨1833674, by rfl⟩ : syracuseStep 2444899 = 3667349) B3667349
theorem B3259865 : Blo 2171435 3259865 := bstep (se 2 (by rfl) ⟨1222449, by rfl⟩ : syracuseStep 3259865 = 2444899) B2444899
theorem B2173243 : Blo 2171435 2173243 := bstep (se 1 (by rfl) ⟨1629932, by rfl⟩ : syracuseStep 2173243 = 3259865) B3259865
theorem B5221685 : Blo 2171435 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B13924493 : Blo 2171435 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B9282995 : Blo 2171435 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B6188663 : Blo 2171435 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B16503101 : Blo 2171435 16503101 := bstep (se 3 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 16503101 = 6188663) B6188663
theorem B11002067 : Blo 2171435 11002067 := bstep (se 1 (by rfl) ⟨8251550, by rfl⟩ : syracuseStep 11002067 = 16503101) B16503101
theorem B7334711 : Blo 2171435 7334711 := bstep (se 1 (by rfl) ⟨5501033, by rfl⟩ : syracuseStep 7334711 = 11002067) B11002067
theorem B4889807 : Blo 2171435 4889807 := bstep (se 1 (by rfl) ⟨3667355, by rfl⟩ : syracuseStep 4889807 = 7334711) B7334711
theorem B3259871 : Blo 2171435 3259871 := bstep (se 1 (by rfl) ⟨2444903, by rfl⟩ : syracuseStep 3259871 = 4889807) B4889807
theorem B2173247 : Blo 2171435 2173247 := bstep (se 1 (by rfl) ⟨1629935, by rfl⟩ : syracuseStep 2173247 = 3259871) B3259871
theorem B3259877 : Blo 2171435 3259877 := bbase (se 4 (by rfl) ⟨305613, by rfl⟩ : syracuseStep 3259877 = 611227) (by norm_num)
theorem B2173251 : Blo 2171435 2173251 := bstep (se 1 (by rfl) ⟨1629938, by rfl⟩ : syracuseStep 2173251 = 3259877) B3259877
theorem B2977285 : Blo 2171435 2977285 := bbase (se 4 (by rfl) ⟨279120, by rfl⟩ : syracuseStep 2977285 = 558241) (by norm_num)
theorem B3969713 : Blo 2171435 3969713 := bstep (se 2 (by rfl) ⟨1488642, by rfl⟩ : syracuseStep 3969713 = 2977285) B2977285
theorem B2646475 : Blo 2171435 2646475 := bstep (se 1 (by rfl) ⟨1984856, by rfl⟩ : syracuseStep 2646475 = 3969713) B3969713
theorem B14114533 : Blo 2171435 14114533 := bstep (se 4 (by rfl) ⟨1323237, by rfl⟩ : syracuseStep 14114533 = 2646475) B2646475
theorem B18819377 : Blo 2171435 18819377 := bstep (se 2 (by rfl) ⟨7057266, by rfl⟩ : syracuseStep 18819377 = 14114533) B14114533
theorem B12546251 : Blo 2171435 12546251 := bstep (se 1 (by rfl) ⟨9409688, by rfl⟩ : syracuseStep 12546251 = 18819377) B18819377
theorem B8364167 : Blo 2171435 8364167 := bstep (se 1 (by rfl) ⟨6273125, by rfl⟩ : syracuseStep 8364167 = 12546251) B12546251
theorem B5576111 : Blo 2171435 5576111 := bstep (se 1 (by rfl) ⟨4182083, by rfl⟩ : syracuseStep 5576111 = 8364167) B8364167
theorem B3717407 : Blo 2171435 3717407 := bstep (se 1 (by rfl) ⟨2788055, by rfl⟩ : syracuseStep 3717407 = 5576111) B5576111
theorem B2478271 : Blo 2171435 2478271 := bstep (se 1 (by rfl) ⟨1858703, by rfl⟩ : syracuseStep 2478271 = 3717407) B3717407
theorem B3304361 : Blo 2171435 3304361 := bstep (se 2 (by rfl) ⟨1239135, by rfl⟩ : syracuseStep 3304361 = 2478271) B2478271
theorem B8811629 : Blo 2171435 8811629 := bstep (se 3 (by rfl) ⟨1652180, by rfl⟩ : syracuseStep 8811629 = 3304361) B3304361
theorem B5874419 : Blo 2171435 5874419 := bstep (se 1 (by rfl) ⟨4405814, by rfl⟩ : syracuseStep 5874419 = 8811629) B8811629
theorem B3916279 : Blo 2171435 3916279 := bstep (se 1 (by rfl) ⟨2937209, by rfl⟩ : syracuseStep 3916279 = 5874419) B5874419
theorem B20886821 : Blo 2171435 20886821 := bstep (se 4 (by rfl) ⟨1958139, by rfl⟩ : syracuseStep 20886821 = 3916279) B3916279
theorem B13924547 : Blo 2171435 13924547 := bstep (se 1 (by rfl) ⟨10443410, by rfl⟩ : syracuseStep 13924547 = 20886821) B20886821
theorem B9283031 : Blo 2171435 9283031 := bstep (se 1 (by rfl) ⟨6962273, by rfl⟩ : syracuseStep 9283031 = 13924547) B13924547
theorem B6188687 : Blo 2171435 6188687 := bstep (se 1 (by rfl) ⟨4641515, by rfl⟩ : syracuseStep 6188687 = 9283031) B9283031
theorem B4125791 : Blo 2171435 4125791 := bstep (se 1 (by rfl) ⟨3094343, by rfl⟩ : syracuseStep 4125791 = 6188687) B6188687
theorem B2750527 : Blo 2171435 2750527 := bstep (se 1 (by rfl) ⟨2062895, by rfl⟩ : syracuseStep 2750527 = 4125791) B4125791
theorem B3667369 : Blo 2171435 3667369 := bstep (se 2 (by rfl) ⟨1375263, by rfl⟩ : syracuseStep 3667369 = 2750527) B2750527
theorem B4889825 : Blo 2171435 4889825 := bstep (se 2 (by rfl) ⟨1833684, by rfl⟩ : syracuseStep 4889825 = 3667369) B3667369
theorem B3259883 : Blo 2171435 3259883 := bstep (se 1 (by rfl) ⟨2444912, by rfl⟩ : syracuseStep 3259883 = 4889825) B4889825
theorem B2173255 : Blo 2171435 2173255 := bstep (se 1 (by rfl) ⟨1629941, by rfl⟩ : syracuseStep 2173255 = 3259883) B3259883
theorem B2444917 : Blo 2171435 2444917 := bbase (se 5 (by rfl) ⟨114605, by rfl⟩ : syracuseStep 2444917 = 229211) (by norm_num)
theorem B3259889 : Blo 2171435 3259889 := bstep (se 2 (by rfl) ⟨1222458, by rfl⟩ : syracuseStep 3259889 = 2444917) B2444917
theorem B2173259 : Blo 2171435 2173259 := bstep (se 1 (by rfl) ⟨1629944, by rfl⟩ : syracuseStep 2173259 = 3259889) B3259889
theorem B2750537 : Blo 2171435 2750537 := bbase (se 2 (by rfl) ⟨1031451, by rfl⟩ : syracuseStep 2750537 = 2062903) (by norm_num)
theorem B7334765 : Blo 2171435 7334765 := bstep (se 3 (by rfl) ⟨1375268, by rfl⟩ : syracuseStep 7334765 = 2750537) B2750537
theorem B4889843 : Blo 2171435 4889843 := bstep (se 1 (by rfl) ⟨3667382, by rfl⟩ : syracuseStep 4889843 = 7334765) B7334765
theorem B3259895 : Blo 2171435 3259895 := bstep (se 1 (by rfl) ⟨2444921, by rfl⟩ : syracuseStep 3259895 = 4889843) B4889843
theorem B2173263 : Blo 2171435 2173263 := bstep (se 1 (by rfl) ⟨1629947, by rfl⟩ : syracuseStep 2173263 = 3259895) B3259895
theorem B3259901 : Blo 2171435 3259901 := bbase (se 3 (by rfl) ⟨611231, by rfl⟩ : syracuseStep 3259901 = 1222463) (by norm_num)
theorem B2173267 : Blo 2171435 2173267 := bstep (se 1 (by rfl) ⟨1629950, by rfl⟩ : syracuseStep 2173267 = 3259901) B3259901
theorem B4889861 : Blo 2171435 4889861 := bbase (se 4 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 4889861 = 916849) (by norm_num)
theorem B3259907 : Blo 2171435 3259907 := bstep (se 1 (by rfl) ⟨2444930, by rfl⟩ : syracuseStep 3259907 = 4889861) B4889861
theorem B2173271 : Blo 2171435 2173271 := bstep (se 1 (by rfl) ⟨1629953, by rfl⟩ : syracuseStep 2173271 = 3259907) B3259907
theorem B4125829 : Blo 2171435 4125829 := bbase (se 4 (by rfl) ⟨386796, by rfl⟩ : syracuseStep 4125829 = 773593) (by norm_num)
theorem B5501105 : Blo 2171435 5501105 := bstep (se 2 (by rfl) ⟨2062914, by rfl⟩ : syracuseStep 5501105 = 4125829) B4125829
theorem B3667403 : Blo 2171435 3667403 := bstep (se 1 (by rfl) ⟨2750552, by rfl⟩ : syracuseStep 3667403 = 5501105) B5501105
theorem B2444935 : Blo 2171435 2444935 := bstep (se 1 (by rfl) ⟨1833701, by rfl⟩ : syracuseStep 2444935 = 3667403) B3667403
theorem B3259913 : Blo 2171435 3259913 := bstep (se 2 (by rfl) ⟨1222467, by rfl⟩ : syracuseStep 3259913 = 2444935) B2444935
theorem B2173275 : Blo 2171435 2173275 := bstep (se 1 (by rfl) ⟨1629956, by rfl⟩ : syracuseStep 2173275 = 3259913) B3259913
theorem B11002229 : Blo 2171435 11002229 := bbase (se 5 (by rfl) ⟨515729, by rfl⟩ : syracuseStep 11002229 = 1031459) (by norm_num)
theorem B7334819 : Blo 2171435 7334819 := bstep (se 1 (by rfl) ⟨5501114, by rfl⟩ : syracuseStep 7334819 = 11002229) B11002229
theorem B4889879 : Blo 2171435 4889879 := bstep (se 1 (by rfl) ⟨3667409, by rfl⟩ : syracuseStep 4889879 = 7334819) B7334819
theorem B3259919 : Blo 2171435 3259919 := bstep (se 1 (by rfl) ⟨2444939, by rfl⟩ : syracuseStep 3259919 = 4889879) B4889879
theorem B2173279 : Blo 2171435 2173279 := bstep (se 1 (by rfl) ⟨1629959, by rfl⟩ : syracuseStep 2173279 = 3259919) B3259919
theorem B3259925 : Blo 2171435 3259925 := bbase (se 6 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 3259925 = 152809) (by norm_num)
theorem B2173283 : Blo 2171435 2173283 := bstep (se 1 (by rfl) ⟨1629962, by rfl⟩ : syracuseStep 2173283 = 3259925) B3259925
theorem B3717461 : Blo 2171435 3717461 := bbase (se 10 (by rfl) ⟨5445, by rfl⟩ : syracuseStep 3717461 = 10891) (by norm_num)
theorem B2478307 : Blo 2171435 2478307 := bstep (se 1 (by rfl) ⟨1858730, by rfl⟩ : syracuseStep 2478307 = 3717461) B3717461
theorem B3304409 : Blo 2171435 3304409 := bstep (se 2 (by rfl) ⟨1239153, by rfl⟩ : syracuseStep 3304409 = 2478307) B2478307
theorem B8811757 : Blo 2171435 8811757 := bstep (se 3 (by rfl) ⟨1652204, by rfl⟩ : syracuseStep 8811757 = 3304409) B3304409
theorem B11749009 : Blo 2171435 11749009 := bstep (se 2 (by rfl) ⟨4405878, by rfl⟩ : syracuseStep 11749009 = 8811757) B8811757
theorem B15665345 : Blo 2171435 15665345 := bstep (se 2 (by rfl) ⟨5874504, by rfl⟩ : syracuseStep 15665345 = 11749009) B11749009
theorem B10443563 : Blo 2171435 10443563 := bstep (se 1 (by rfl) ⟨7832672, by rfl⟩ : syracuseStep 10443563 = 15665345) B15665345
theorem B6962375 : Blo 2171435 6962375 := bstep (se 1 (by rfl) ⟨5221781, by rfl⟩ : syracuseStep 6962375 = 10443563) B10443563
theorem B18566333 : Blo 2171435 18566333 := bstep (se 3 (by rfl) ⟨3481187, by rfl⟩ : syracuseStep 18566333 = 6962375) B6962375
theorem B12377555 : Blo 2171435 12377555 := bstep (se 1 (by rfl) ⟨9283166, by rfl⟩ : syracuseStep 12377555 = 18566333) B18566333
theorem B8251703 : Blo 2171435 8251703 := bstep (se 1 (by rfl) ⟨6188777, by rfl⟩ : syracuseStep 8251703 = 12377555) B12377555
theorem B5501135 : Blo 2171435 5501135 := bstep (se 1 (by rfl) ⟨4125851, by rfl⟩ : syracuseStep 5501135 = 8251703) B8251703
theorem B3667423 : Blo 2171435 3667423 := bstep (se 1 (by rfl) ⟨2750567, by rfl⟩ : syracuseStep 3667423 = 5501135) B5501135
theorem B4889897 : Blo 2171435 4889897 := bstep (se 2 (by rfl) ⟨1833711, by rfl⟩ : syracuseStep 4889897 = 3667423) B3667423
theorem B3259931 : Blo 2171435 3259931 := bstep (se 1 (by rfl) ⟨2444948, by rfl⟩ : syracuseStep 3259931 = 4889897) B4889897
theorem B2173287 : Blo 2171435 2173287 := bstep (se 1 (by rfl) ⟨1629965, by rfl⟩ : syracuseStep 2173287 = 3259931) B3259931
theorem B2444953 : Blo 2171435 2444953 := bbase (se 2 (by rfl) ⟨916857, by rfl⟩ : syracuseStep 2444953 = 1833715) (by norm_num)
theorem B3259937 : Blo 2171435 3259937 := bstep (se 2 (by rfl) ⟨1222476, by rfl⟩ : syracuseStep 3259937 = 2444953) B2444953
theorem B2173291 : Blo 2171435 2173291 := bstep (se 1 (by rfl) ⟨1629968, by rfl⟩ : syracuseStep 2173291 = 3259937) B3259937
theorem B8251733 : Blo 2171435 8251733 := bbase (se 10 (by rfl) ⟨12087, by rfl⟩ : syracuseStep 8251733 = 24175) (by norm_num)
theorem B5501155 : Blo 2171435 5501155 := bstep (se 1 (by rfl) ⟨4125866, by rfl⟩ : syracuseStep 5501155 = 8251733) B8251733
theorem B7334873 : Blo 2171435 7334873 := bstep (se 2 (by rfl) ⟨2750577, by rfl⟩ : syracuseStep 7334873 = 5501155) B5501155
theorem B4889915 : Blo 2171435 4889915 := bstep (se 1 (by rfl) ⟨3667436, by rfl⟩ : syracuseStep 4889915 = 7334873) B7334873
theorem B3259943 : Blo 2171435 3259943 := bstep (se 1 (by rfl) ⟨2444957, by rfl⟩ : syracuseStep 3259943 = 4889915) B4889915
theorem B2173295 : Blo 2171435 2173295 := bstep (se 1 (by rfl) ⟨1629971, by rfl⟩ : syracuseStep 2173295 = 3259943) B3259943
theorem B3259949 : Blo 2171435 3259949 := bbase (se 3 (by rfl) ⟨611240, by rfl⟩ : syracuseStep 3259949 = 1222481) (by norm_num)
theorem B2173299 : Blo 2171435 2173299 := bstep (se 1 (by rfl) ⟨1629974, by rfl⟩ : syracuseStep 2173299 = 3259949) B3259949
theorem B4889933 : Blo 2171435 4889933 := bbase (se 3 (by rfl) ⟨916862, by rfl⟩ : syracuseStep 4889933 = 1833725) (by norm_num)
theorem B3259955 : Blo 2171435 3259955 := bstep (se 1 (by rfl) ⟨2444966, by rfl⟩ : syracuseStep 3259955 = 4889933) B4889933
theorem B2173303 : Blo 2171435 2173303 := bstep (se 1 (by rfl) ⟨1629977, by rfl⟩ : syracuseStep 2173303 = 3259955) B3259955
theorem B2750593 : Blo 2171435 2750593 := bbase (se 2 (by rfl) ⟨1031472, by rfl⟩ : syracuseStep 2750593 = 2062945) (by norm_num)
theorem B3667457 : Blo 2171435 3667457 := bstep (se 2 (by rfl) ⟨1375296, by rfl⟩ : syracuseStep 3667457 = 2750593) B2750593
theorem B2444971 : Blo 2171435 2444971 := bstep (se 1 (by rfl) ⟨1833728, by rfl⟩ : syracuseStep 2444971 = 3667457) B3667457
theorem B3259961 : Blo 2171435 3259961 := bstep (se 2 (by rfl) ⟨1222485, by rfl⟩ : syracuseStep 3259961 = 2444971) B2444971
theorem B2173307 : Blo 2171435 2173307 := bstep (se 1 (by rfl) ⟨1629980, by rfl⟩ : syracuseStep 2173307 = 3259961) B3259961
theorem B2320817 : Blo 2171435 2320817 := bbase (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) (by norm_num)
theorem B24755381 : Blo 2171435 24755381 := bstep (se 5 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 24755381 = 2320817) B2320817
theorem B16503587 : Blo 2171435 16503587 := bstep (se 1 (by rfl) ⟨12377690, by rfl⟩ : syracuseStep 16503587 = 24755381) B24755381
theorem B11002391 : Blo 2171435 11002391 := bstep (se 1 (by rfl) ⟨8251793, by rfl⟩ : syracuseStep 11002391 = 16503587) B16503587
theorem B7334927 : Blo 2171435 7334927 := bstep (se 1 (by rfl) ⟨5501195, by rfl⟩ : syracuseStep 7334927 = 11002391) B11002391
theorem B4889951 : Blo 2171435 4889951 := bstep (se 1 (by rfl) ⟨3667463, by rfl⟩ : syracuseStep 4889951 = 7334927) B7334927
theorem B3259967 : Blo 2171435 3259967 := bstep (se 1 (by rfl) ⟨2444975, by rfl⟩ : syracuseStep 3259967 = 4889951) B4889951
theorem B2173311 : Blo 2171435 2173311 := bstep (se 1 (by rfl) ⟨1629983, by rfl⟩ : syracuseStep 2173311 = 3259967) B3259967
theorem B3259973 : Blo 2171435 3259973 := bbase (se 4 (by rfl) ⟨305622, by rfl⟩ : syracuseStep 3259973 = 611245) (by norm_num)
theorem B2173315 : Blo 2171435 2173315 := bstep (se 1 (by rfl) ⟨1629986, by rfl⟩ : syracuseStep 2173315 = 3259973) B3259973
theorem B3667477 : Blo 2171435 3667477 := bbase (se 6 (by rfl) ⟨85956, by rfl⟩ : syracuseStep 3667477 = 171913) (by norm_num)
theorem B4889969 : Blo 2171435 4889969 := bstep (se 2 (by rfl) ⟨1833738, by rfl⟩ : syracuseStep 4889969 = 3667477) B3667477
theorem B3259979 : Blo 2171435 3259979 := bstep (se 1 (by rfl) ⟨2444984, by rfl⟩ : syracuseStep 3259979 = 4889969) B4889969
theorem B2173319 : Blo 2171435 2173319 := bstep (se 1 (by rfl) ⟨1629989, by rfl⟩ : syracuseStep 2173319 = 3259979) B3259979
theorem B2444989 : Blo 2171435 2444989 := bbase (se 3 (by rfl) ⟨458435, by rfl⟩ : syracuseStep 2444989 = 916871) (by norm_num)
theorem B3259985 : Blo 2171435 3259985 := bstep (se 2 (by rfl) ⟨1222494, by rfl⟩ : syracuseStep 3259985 = 2444989) B2444989
theorem B2173323 : Blo 2171435 2173323 := bstep (se 1 (by rfl) ⟨1629992, by rfl⟩ : syracuseStep 2173323 = 3259985) B3259985
theorem B7334981 : Blo 2171435 7334981 := bbase (se 4 (by rfl) ⟨687654, by rfl⟩ : syracuseStep 7334981 = 1375309) (by norm_num)
theorem B4889987 : Blo 2171435 4889987 := bstep (se 1 (by rfl) ⟨3667490, by rfl⟩ : syracuseStep 4889987 = 7334981) B7334981
theorem B3259991 : Blo 2171435 3259991 := bstep (se 1 (by rfl) ⟨2444993, by rfl⟩ : syracuseStep 3259991 = 4889987) B4889987
theorem B2173327 : Blo 2171435 2173327 := bstep (se 1 (by rfl) ⟨1629995, by rfl⟩ : syracuseStep 2173327 = 3259991) B3259991
theorem B3259997 : Blo 2171435 3259997 := bbase (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) (by norm_num)
theorem B2173331 : Blo 2171435 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B4890005 : Blo 2171435 4890005 := bbase (se 6 (by rfl) ⟨114609, by rfl⟩ : syracuseStep 4890005 = 229219) (by norm_num)
theorem B3260003 : Blo 2171435 3260003 := bstep (se 1 (by rfl) ⟨2445002, by rfl⟩ : syracuseStep 3260003 = 4890005) B4890005
theorem B2173335 : Blo 2171435 2173335 := bstep (se 1 (by rfl) ⟨1630001, by rfl⟩ : syracuseStep 2173335 = 3260003) B3260003
theorem B4956733 : Blo 2171435 4956733 := bbase (se 3 (by rfl) ⟨929387, by rfl⟩ : syracuseStep 4956733 = 1858775) (by norm_num)
theorem B26435909 : Blo 2171435 26435909 := bstep (se 4 (by rfl) ⟨2478366, by rfl⟩ : syracuseStep 26435909 = 4956733) B4956733
theorem B17623939 : Blo 2171435 17623939 := bstep (se 1 (by rfl) ⟨13217954, by rfl⟩ : syracuseStep 17623939 = 26435909) B26435909
theorem B23498585 : Blo 2171435 23498585 := bstep (se 2 (by rfl) ⟨8811969, by rfl⟩ : syracuseStep 23498585 = 17623939) B17623939
theorem B15665723 : Blo 2171435 15665723 := bstep (se 1 (by rfl) ⟨11749292, by rfl⟩ : syracuseStep 15665723 = 23498585) B23498585
theorem B10443815 : Blo 2171435 10443815 := bstep (se 1 (by rfl) ⟨7832861, by rfl⟩ : syracuseStep 10443815 = 15665723) B15665723
theorem B6962543 : Blo 2171435 6962543 := bstep (se 1 (by rfl) ⟨5221907, by rfl⟩ : syracuseStep 6962543 = 10443815) B10443815
theorem B4641695 : Blo 2171435 4641695 := bstep (se 1 (by rfl) ⟨3481271, by rfl⟩ : syracuseStep 4641695 = 6962543) B6962543
theorem B3094463 : Blo 2171435 3094463 := bstep (se 1 (by rfl) ⟨2320847, by rfl⟩ : syracuseStep 3094463 = 4641695) B4641695
theorem B8251901 : Blo 2171435 8251901 := bstep (se 3 (by rfl) ⟨1547231, by rfl⟩ : syracuseStep 8251901 = 3094463) B3094463
theorem B5501267 : Blo 2171435 5501267 := bstep (se 1 (by rfl) ⟨4125950, by rfl⟩ : syracuseStep 5501267 = 8251901) B8251901
theorem B3667511 : Blo 2171435 3667511 := bstep (se 1 (by rfl) ⟨2750633, by rfl⟩ : syracuseStep 3667511 = 5501267) B5501267
theorem B2445007 : Blo 2171435 2445007 := bstep (se 1 (by rfl) ⟨1833755, by rfl⟩ : syracuseStep 2445007 = 3667511) B3667511
theorem B3260009 : Blo 2171435 3260009 := bstep (se 2 (by rfl) ⟨1222503, by rfl⟩ : syracuseStep 3260009 = 2445007) B2445007
theorem B2173339 : Blo 2171435 2173339 := bstep (se 1 (by rfl) ⟨1630004, by rfl⟩ : syracuseStep 2173339 = 3260009) B3260009
theorem B3481277 : Blo 2171435 3481277 := bbase (se 3 (by rfl) ⟨652739, by rfl⟩ : syracuseStep 3481277 = 1305479) (by norm_num)
theorem B9283405 : Blo 2171435 9283405 := bstep (se 3 (by rfl) ⟨1740638, by rfl⟩ : syracuseStep 9283405 = 3481277) B3481277
theorem B12377873 : Blo 2171435 12377873 := bstep (se 2 (by rfl) ⟨4641702, by rfl⟩ : syracuseStep 12377873 = 9283405) B9283405
theorem B8251915 : Blo 2171435 8251915 := bstep (se 1 (by rfl) ⟨6188936, by rfl⟩ : syracuseStep 8251915 = 12377873) B12377873
theorem B11002553 : Blo 2171435 11002553 := bstep (se 2 (by rfl) ⟨4125957, by rfl⟩ : syracuseStep 11002553 = 8251915) B8251915
theorem B7335035 : Blo 2171435 7335035 := bstep (se 1 (by rfl) ⟨5501276, by rfl⟩ : syracuseStep 7335035 = 11002553) B11002553
theorem B4890023 : Blo 2171435 4890023 := bstep (se 1 (by rfl) ⟨3667517, by rfl⟩ : syracuseStep 4890023 = 7335035) B7335035
theorem B3260015 : Blo 2171435 3260015 := bstep (se 1 (by rfl) ⟨2445011, by rfl⟩ : syracuseStep 3260015 = 4890023) B4890023
theorem B2173343 : Blo 2171435 2173343 := bstep (se 1 (by rfl) ⟨1630007, by rfl⟩ : syracuseStep 2173343 = 3260015) B3260015
theorem B3260021 : Blo 2171435 3260021 := bbase (se 5 (by rfl) ⟨152813, by rfl⟩ : syracuseStep 3260021 = 305627) (by norm_num)
theorem B2173347 : Blo 2171435 2173347 := bstep (se 1 (by rfl) ⟨1630010, by rfl⟩ : syracuseStep 2173347 = 3260021) B3260021
theorem B4125973 : Blo 2171435 4125973 := bbase (se 6 (by rfl) ⟨96702, by rfl⟩ : syracuseStep 4125973 = 193405) (by norm_num)
theorem B5501297 : Blo 2171435 5501297 := bstep (se 2 (by rfl) ⟨2062986, by rfl⟩ : syracuseStep 5501297 = 4125973) B4125973
theorem B3667531 : Blo 2171435 3667531 := bstep (se 1 (by rfl) ⟨2750648, by rfl⟩ : syracuseStep 3667531 = 5501297) B5501297
theorem B4890041 : Blo 2171435 4890041 := bstep (se 2 (by rfl) ⟨1833765, by rfl⟩ : syracuseStep 4890041 = 3667531) B3667531
theorem B3260027 : Blo 2171435 3260027 := bstep (se 1 (by rfl) ⟨2445020, by rfl⟩ : syracuseStep 3260027 = 4890041) B4890041
theorem B2173351 : Blo 2171435 2173351 := bstep (se 1 (by rfl) ⟨1630013, by rfl⟩ : syracuseStep 2173351 = 3260027) B3260027
theorem B2445025 : Blo 2171435 2445025 := bbase (se 2 (by rfl) ⟨916884, by rfl⟩ : syracuseStep 2445025 = 1833769) (by norm_num)
theorem B3260033 : Blo 2171435 3260033 := bstep (se 2 (by rfl) ⟨1222512, by rfl⟩ : syracuseStep 3260033 = 2445025) B2445025
theorem B2173355 : Blo 2171435 2173355 := bstep (se 1 (by rfl) ⟨1630016, by rfl⟩ : syracuseStep 2173355 = 3260033) B3260033
theorem B5501317 : Blo 2171435 5501317 := bbase (se 4 (by rfl) ⟨515748, by rfl⟩ : syracuseStep 5501317 = 1031497) (by norm_num)
theorem B7335089 : Blo 2171435 7335089 := bstep (se 2 (by rfl) ⟨2750658, by rfl⟩ : syracuseStep 7335089 = 5501317) B5501317
theorem B4890059 : Blo 2171435 4890059 := bstep (se 1 (by rfl) ⟨3667544, by rfl⟩ : syracuseStep 4890059 = 7335089) B7335089
theorem B3260039 : Blo 2171435 3260039 := bstep (se 1 (by rfl) ⟨2445029, by rfl⟩ : syracuseStep 3260039 = 4890059) B4890059
theorem B2173359 : Blo 2171435 2173359 := bstep (se 1 (by rfl) ⟨1630019, by rfl⟩ : syracuseStep 2173359 = 3260039) B3260039
theorem B3260045 : Blo 2171435 3260045 := bbase (se 3 (by rfl) ⟨611258, by rfl⟩ : syracuseStep 3260045 = 1222517) (by norm_num)
theorem B2173363 : Blo 2171435 2173363 := bstep (se 1 (by rfl) ⟨1630022, by rfl⟩ : syracuseStep 2173363 = 3260045) B3260045
theorem B4890077 : Blo 2171435 4890077 := bbase (se 3 (by rfl) ⟨916889, by rfl⟩ : syracuseStep 4890077 = 1833779) (by norm_num)
theorem B3260051 : Blo 2171435 3260051 := bstep (se 1 (by rfl) ⟨2445038, by rfl⟩ : syracuseStep 3260051 = 4890077) B4890077
theorem B2173367 : Blo 2171435 2173367 := bstep (se 1 (by rfl) ⟨1630025, by rfl⟩ : syracuseStep 2173367 = 3260051) B3260051
theorem B3667565 : Blo 2171435 3667565 := bbase (se 3 (by rfl) ⟨687668, by rfl⟩ : syracuseStep 3667565 = 1375337) (by norm_num)
theorem B2445043 : Blo 2171435 2445043 := bstep (se 1 (by rfl) ⟨1833782, by rfl⟩ : syracuseStep 2445043 = 3667565) B3667565
theorem B3260057 : Blo 2171435 3260057 := bstep (se 2 (by rfl) ⟨1222521, by rfl⟩ : syracuseStep 3260057 = 2445043) B2445043
theorem B2173371 : Blo 2171435 2173371 := bstep (se 1 (by rfl) ⟨1630028, by rfl⟩ : syracuseStep 2173371 = 3260057) B3260057
theorem B4024093 : Blo 2171435 4024093 := bbase (se 3 (by rfl) ⟨754517, by rfl⟩ : syracuseStep 4024093 = 1509035) (by norm_num)
theorem B5365457 : Blo 2171435 5365457 := bstep (se 2 (by rfl) ⟨2012046, by rfl⟩ : syracuseStep 5365457 = 4024093) B4024093
theorem B3576971 : Blo 2171435 3576971 := bstep (se 1 (by rfl) ⟨2682728, by rfl⟩ : syracuseStep 3576971 = 5365457) B5365457
theorem B9538589 : Blo 2171435 9538589 := bstep (se 3 (by rfl) ⟨1788485, by rfl⟩ : syracuseStep 9538589 = 3576971) B3576971
theorem B6359059 : Blo 2171435 6359059 := bstep (se 1 (by rfl) ⟨4769294, by rfl⟩ : syracuseStep 6359059 = 9538589) B9538589
theorem B8478745 : Blo 2171435 8478745 := bstep (se 2 (by rfl) ⟨3179529, by rfl⟩ : syracuseStep 8478745 = 6359059) B6359059
theorem B45219973 : Blo 2171435 45219973 := bstep (se 4 (by rfl) ⟨4239372, by rfl⟩ : syracuseStep 45219973 = 8478745) B8478745
theorem B60293297 : Blo 2171435 60293297 := bstep (se 2 (by rfl) ⟨22609986, by rfl⟩ : syracuseStep 60293297 = 45219973) B45219973
theorem B40195531 : Blo 2171435 40195531 := bstep (se 1 (by rfl) ⟨30146648, by rfl⟩ : syracuseStep 40195531 = 60293297) B60293297
theorem B214376165 : Blo 2171435 214376165 := bstep (se 4 (by rfl) ⟨20097765, by rfl⟩ : syracuseStep 214376165 = 40195531) B40195531
theorem B142917443 : Blo 2171435 142917443 := bstep (se 1 (by rfl) ⟨107188082, by rfl⟩ : syracuseStep 142917443 = 214376165) B214376165
theorem B95278295 : Blo 2171435 95278295 := bstep (se 1 (by rfl) ⟨71458721, by rfl⟩ : syracuseStep 95278295 = 142917443) B142917443
theorem B63518863 : Blo 2171435 63518863 := bstep (se 1 (by rfl) ⟨47639147, by rfl⟩ : syracuseStep 63518863 = 95278295) B95278295
theorem B84691817 : Blo 2171435 84691817 := bstep (se 2 (by rfl) ⟨31759431, by rfl⟩ : syracuseStep 84691817 = 63518863) B63518863
theorem B56461211 : Blo 2171435 56461211 := bstep (se 1 (by rfl) ⟨42345908, by rfl⟩ : syracuseStep 56461211 = 84691817) B84691817
theorem B37640807 : Blo 2171435 37640807 := bstep (se 1 (by rfl) ⟨28230605, by rfl⟩ : syracuseStep 37640807 = 56461211) B56461211
theorem B25093871 : Blo 2171435 25093871 := bstep (se 1 (by rfl) ⟨18820403, by rfl⟩ : syracuseStep 25093871 = 37640807) B37640807
theorem B16729247 : Blo 2171435 16729247 := bstep (se 1 (by rfl) ⟨12546935, by rfl⟩ : syracuseStep 16729247 = 25093871) B25093871
theorem B11152831 : Blo 2171435 11152831 := bstep (se 1 (by rfl) ⟨8364623, by rfl⟩ : syracuseStep 11152831 = 16729247) B16729247
theorem B14870441 : Blo 2171435 14870441 := bstep (se 2 (by rfl) ⟨5576415, by rfl⟩ : syracuseStep 14870441 = 11152831) B11152831
theorem B9913627 : Blo 2171435 9913627 := bstep (se 1 (by rfl) ⟨7435220, by rfl⟩ : syracuseStep 9913627 = 14870441) B14870441
theorem B13218169 : Blo 2171435 13218169 := bstep (se 2 (by rfl) ⟨4956813, by rfl⟩ : syracuseStep 13218169 = 9913627) B9913627
theorem B17624225 : Blo 2171435 17624225 := bstep (se 2 (by rfl) ⟨6609084, by rfl⟩ : syracuseStep 17624225 = 13218169) B13218169
theorem B11749483 : Blo 2171435 11749483 := bstep (se 1 (by rfl) ⟨8812112, by rfl⟩ : syracuseStep 11749483 = 17624225) B17624225
theorem B15665977 : Blo 2171435 15665977 := bstep (se 2 (by rfl) ⟨5874741, by rfl⟩ : syracuseStep 15665977 = 11749483) B11749483
theorem B20887969 : Blo 2171435 20887969 := bstep (se 2 (by rfl) ⟨7832988, by rfl⟩ : syracuseStep 20887969 = 15665977) B15665977
theorem B27850625 : Blo 2171435 27850625 := bstep (se 2 (by rfl) ⟨10443984, by rfl⟩ : syracuseStep 27850625 = 20887969) B20887969
theorem B18567083 : Blo 2171435 18567083 := bstep (se 1 (by rfl) ⟨13925312, by rfl⟩ : syracuseStep 18567083 = 27850625) B27850625
theorem B12378055 : Blo 2171435 12378055 := bstep (se 1 (by rfl) ⟨9283541, by rfl⟩ : syracuseStep 12378055 = 18567083) B18567083
theorem B16504073 : Blo 2171435 16504073 := bstep (se 2 (by rfl) ⟨6189027, by rfl⟩ : syracuseStep 16504073 = 12378055) B12378055
theorem B11002715 : Blo 2171435 11002715 := bstep (se 1 (by rfl) ⟨8252036, by rfl⟩ : syracuseStep 11002715 = 16504073) B16504073
theorem B7335143 : Blo 2171435 7335143 := bstep (se 1 (by rfl) ⟨5501357, by rfl⟩ : syracuseStep 7335143 = 11002715) B11002715
theorem B4890095 : Blo 2171435 4890095 := bstep (se 1 (by rfl) ⟨3667571, by rfl⟩ : syracuseStep 4890095 = 7335143) B7335143
theorem B3260063 : Blo 2171435 3260063 := bstep (se 1 (by rfl) ⟨2445047, by rfl⟩ : syracuseStep 3260063 = 4890095) B4890095
theorem B2173375 : Blo 2171435 2173375 := bstep (se 1 (by rfl) ⟨1630031, by rfl⟩ : syracuseStep 2173375 = 3260063) B3260063
theorem B3260069 : Blo 2171435 3260069 := bbase (se 4 (by rfl) ⟨305631, by rfl⟩ : syracuseStep 3260069 = 611263) (by norm_num)
theorem B2173379 : Blo 2171435 2173379 := bstep (se 1 (by rfl) ⟨1630034, by rfl⟩ : syracuseStep 2173379 = 3260069) B3260069
theorem B2750689 : Blo 2171435 2750689 := bbase (se 2 (by rfl) ⟨1031508, by rfl⟩ : syracuseStep 2750689 = 2063017) (by norm_num)
theorem B3667585 : Blo 2171435 3667585 := bstep (se 2 (by rfl) ⟨1375344, by rfl⟩ : syracuseStep 3667585 = 2750689) B2750689
theorem B4890113 : Blo 2171435 4890113 := bstep (se 2 (by rfl) ⟨1833792, by rfl⟩ : syracuseStep 4890113 = 3667585) B3667585
theorem B3260075 : Blo 2171435 3260075 := bstep (se 1 (by rfl) ⟨2445056, by rfl⟩ : syracuseStep 3260075 = 4890113) B4890113
theorem B2173383 : Blo 2171435 2173383 := bstep (se 1 (by rfl) ⟨1630037, by rfl⟩ : syracuseStep 2173383 = 3260075) B3260075
theorem B2445061 : Blo 2171435 2445061 := bbase (se 4 (by rfl) ⟨229224, by rfl⟩ : syracuseStep 2445061 = 458449) (by norm_num)
theorem B3260081 : Blo 2171435 3260081 := bstep (se 2 (by rfl) ⟨1222530, by rfl⟩ : syracuseStep 3260081 = 2445061) B2445061
theorem B2173387 : Blo 2171435 2173387 := bstep (se 1 (by rfl) ⟨1630040, by rfl⟩ : syracuseStep 2173387 = 3260081) B3260081
theorem B3916525 : Blo 2171435 3916525 := bbase (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) (by norm_num)
theorem B5222033 : Blo 2171435 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B3481355 : Blo 2171435 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B2320903 : Blo 2171435 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B3094537 : Blo 2171435 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B4126049 : Blo 2171435 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B2750699 : Blo 2171435 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B7335197 : Blo 2171435 7335197 := bstep (se 3 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 7335197 = 2750699) B2750699
theorem B4890131 : Blo 2171435 4890131 := bstep (se 1 (by rfl) ⟨3667598, by rfl⟩ : syracuseStep 4890131 = 7335197) B7335197
theorem B3260087 : Blo 2171435 3260087 := bstep (se 1 (by rfl) ⟨2445065, by rfl⟩ : syracuseStep 3260087 = 4890131) B4890131
theorem B2173391 : Blo 2171435 2173391 := bstep (se 1 (by rfl) ⟨1630043, by rfl⟩ : syracuseStep 2173391 = 3260087) B3260087
theorem B3260093 : Blo 2171435 3260093 := bbase (se 3 (by rfl) ⟨611267, by rfl⟩ : syracuseStep 3260093 = 1222535) (by norm_num)
theorem B2173395 : Blo 2171435 2173395 := bstep (se 1 (by rfl) ⟨1630046, by rfl⟩ : syracuseStep 2173395 = 3260093) B3260093
theorem B4890149 : Blo 2171435 4890149 := bbase (se 4 (by rfl) ⟨458451, by rfl⟩ : syracuseStep 4890149 = 916903) (by norm_num)
theorem B3260099 : Blo 2171435 3260099 := bstep (se 1 (by rfl) ⟨2445074, by rfl⟩ : syracuseStep 3260099 = 4890149) B4890149
theorem B2173399 : Blo 2171435 2173399 := bstep (se 1 (by rfl) ⟨1630049, by rfl⟩ : syracuseStep 2173399 = 3260099) B3260099
theorem B5501429 : Blo 2171435 5501429 := bbase (se 5 (by rfl) ⟨257879, by rfl⟩ : syracuseStep 5501429 = 515759) (by norm_num)
theorem B3667619 : Blo 2171435 3667619 := bstep (se 1 (by rfl) ⟨2750714, by rfl⟩ : syracuseStep 3667619 = 5501429) B5501429
theorem B2445079 : Blo 2171435 2445079 := bstep (se 1 (by rfl) ⟨1833809, by rfl⟩ : syracuseStep 2445079 = 3667619) B3667619
theorem B3260105 : Blo 2171435 3260105 := bstep (se 2 (by rfl) ⟨1222539, by rfl⟩ : syracuseStep 3260105 = 2445079) B2445079
theorem B2173403 : Blo 2171435 2173403 := bstep (se 1 (by rfl) ⟨1630052, by rfl⟩ : syracuseStep 2173403 = 3260105) B3260105
theorem B11152997 : Blo 2171435 11152997 := bbase (se 4 (by rfl) ⟨1045593, by rfl⟩ : syracuseStep 11152997 = 2091187) (by norm_num)
theorem B7435331 : Blo 2171435 7435331 := bstep (se 1 (by rfl) ⟨5576498, by rfl⟩ : syracuseStep 7435331 = 11152997) B11152997
theorem B4956887 : Blo 2171435 4956887 := bstep (se 1 (by rfl) ⟨3717665, by rfl⟩ : syracuseStep 4956887 = 7435331) B7435331
theorem B13218365 : Blo 2171435 13218365 := bstep (se 3 (by rfl) ⟨2478443, by rfl⟩ : syracuseStep 13218365 = 4956887) B4956887
theorem B8812243 : Blo 2171435 8812243 := bstep (se 1 (by rfl) ⟨6609182, by rfl⟩ : syracuseStep 8812243 = 13218365) B13218365
theorem B46998629 : Blo 2171435 46998629 := bstep (se 4 (by rfl) ⟨4406121, by rfl⟩ : syracuseStep 46998629 = 8812243) B8812243
theorem B31332419 : Blo 2171435 31332419 := bstep (se 1 (by rfl) ⟨23499314, by rfl⟩ : syracuseStep 31332419 = 46998629) B46998629
theorem B20888279 : Blo 2171435 20888279 := bstep (se 1 (by rfl) ⟨15666209, by rfl⟩ : syracuseStep 20888279 = 31332419) B31332419
theorem B13925519 : Blo 2171435 13925519 := bstep (se 1 (by rfl) ⟨10444139, by rfl⟩ : syracuseStep 13925519 = 20888279) B20888279
theorem B9283679 : Blo 2171435 9283679 := bstep (se 1 (by rfl) ⟨6962759, by rfl⟩ : syracuseStep 9283679 = 13925519) B13925519
theorem B6189119 : Blo 2171435 6189119 := bstep (se 1 (by rfl) ⟨4641839, by rfl⟩ : syracuseStep 6189119 = 9283679) B9283679
theorem B4126079 : Blo 2171435 4126079 := bstep (se 1 (by rfl) ⟨3094559, by rfl⟩ : syracuseStep 4126079 = 6189119) B6189119
theorem B11002877 : Blo 2171435 11002877 := bstep (se 3 (by rfl) ⟨2063039, by rfl⟩ : syracuseStep 11002877 = 4126079) B4126079
theorem B7335251 : Blo 2171435 7335251 := bstep (se 1 (by rfl) ⟨5501438, by rfl⟩ : syracuseStep 7335251 = 11002877) B11002877
theorem B4890167 : Blo 2171435 4890167 := bstep (se 1 (by rfl) ⟨3667625, by rfl⟩ : syracuseStep 4890167 = 7335251) B7335251
theorem B3260111 : Blo 2171435 3260111 := bstep (se 1 (by rfl) ⟨2445083, by rfl⟩ : syracuseStep 3260111 = 4890167) B4890167
theorem B2173407 : Blo 2171435 2173407 := bstep (se 1 (by rfl) ⟨1630055, by rfl⟩ : syracuseStep 2173407 = 3260111) B3260111
theorem B3260117 : Blo 2171435 3260117 := bbase (se 7 (by rfl) ⟨38204, by rfl⟩ : syracuseStep 3260117 = 76409) (by norm_num)
theorem B2173411 : Blo 2171435 2173411 := bstep (se 1 (by rfl) ⟨1630058, by rfl⟩ : syracuseStep 2173411 = 3260117) B3260117
theorem B2611045 : Blo 2171435 2611045 := bbase (se 4 (by rfl) ⟨244785, by rfl⟩ : syracuseStep 2611045 = 489571) (by norm_num)
theorem B3481393 : Blo 2171435 3481393 := bstep (se 2 (by rfl) ⟨1305522, by rfl⟩ : syracuseStep 3481393 = 2611045) B2611045
theorem B4641857 : Blo 2171435 4641857 := bstep (se 2 (by rfl) ⟨1740696, by rfl⟩ : syracuseStep 4641857 = 3481393) B3481393
theorem B3094571 : Blo 2171435 3094571 := bstep (se 1 (by rfl) ⟨2320928, by rfl⟩ : syracuseStep 3094571 = 4641857) B4641857
theorem B8252189 : Blo 2171435 8252189 := bstep (se 3 (by rfl) ⟨1547285, by rfl⟩ : syracuseStep 8252189 = 3094571) B3094571
theorem B5501459 : Blo 2171435 5501459 := bstep (se 1 (by rfl) ⟨4126094, by rfl⟩ : syracuseStep 5501459 = 8252189) B8252189
theorem B3667639 : Blo 2171435 3667639 := bstep (se 1 (by rfl) ⟨2750729, by rfl⟩ : syracuseStep 3667639 = 5501459) B5501459
theorem B4890185 : Blo 2171435 4890185 := bstep (se 2 (by rfl) ⟨1833819, by rfl⟩ : syracuseStep 4890185 = 3667639) B3667639
theorem B3260123 : Blo 2171435 3260123 := bstep (se 1 (by rfl) ⟨2445092, by rfl⟩ : syracuseStep 3260123 = 4890185) B4890185
theorem B2173415 : Blo 2171435 2173415 := bstep (se 1 (by rfl) ⟨1630061, by rfl⟩ : syracuseStep 2173415 = 3260123) B3260123
theorem B2445097 : Blo 2171435 2445097 := bbase (se 2 (by rfl) ⟨916911, by rfl⟩ : syracuseStep 2445097 = 1833823) (by norm_num)
theorem B3260129 : Blo 2171435 3260129 := bstep (se 2 (by rfl) ⟨1222548, by rfl⟩ : syracuseStep 3260129 = 2445097) B2445097
theorem B2173419 : Blo 2171435 2173419 := bstep (se 1 (by rfl) ⟨1630064, by rfl⟩ : syracuseStep 2173419 = 3260129) B3260129
theorem B13925621 : Blo 2171435 13925621 := bbase (se 5 (by rfl) ⟨652763, by rfl⟩ : syracuseStep 13925621 = 1305527) (by norm_num)
theorem B9283747 : Blo 2171435 9283747 := bstep (se 1 (by rfl) ⟨6962810, by rfl⟩ : syracuseStep 9283747 = 13925621) B13925621
theorem B12378329 : Blo 2171435 12378329 := bstep (se 2 (by rfl) ⟨4641873, by rfl⟩ : syracuseStep 12378329 = 9283747) B9283747
theorem B8252219 : Blo 2171435 8252219 := bstep (se 1 (by rfl) ⟨6189164, by rfl⟩ : syracuseStep 8252219 = 12378329) B12378329
theorem B5501479 : Blo 2171435 5501479 := bstep (se 1 (by rfl) ⟨4126109, by rfl⟩ : syracuseStep 5501479 = 8252219) B8252219
theorem B7335305 : Blo 2171435 7335305 := bstep (se 2 (by rfl) ⟨2750739, by rfl⟩ : syracuseStep 7335305 = 5501479) B5501479
theorem B4890203 : Blo 2171435 4890203 := bstep (se 1 (by rfl) ⟨3667652, by rfl⟩ : syracuseStep 4890203 = 7335305) B7335305
theorem B3260135 : Blo 2171435 3260135 := bstep (se 1 (by rfl) ⟨2445101, by rfl⟩ : syracuseStep 3260135 = 4890203) B4890203
theorem B2173423 : Blo 2171435 2173423 := bstep (se 1 (by rfl) ⟨1630067, by rfl⟩ : syracuseStep 2173423 = 3260135) B3260135
theorem B3260141 : Blo 2171435 3260141 := bbase (se 3 (by rfl) ⟨611276, by rfl⟩ : syracuseStep 3260141 = 1222553) (by norm_num)
theorem B2173427 : Blo 2171435 2173427 := bstep (se 1 (by rfl) ⟨1630070, by rfl⟩ : syracuseStep 2173427 = 3260141) B3260141
theorem B4890221 : Blo 2171435 4890221 := bbase (se 3 (by rfl) ⟨916916, by rfl⟩ : syracuseStep 4890221 = 1833833) (by norm_num)
theorem B3260147 : Blo 2171435 3260147 := bstep (se 1 (by rfl) ⟨2445110, by rfl⟩ : syracuseStep 3260147 = 4890221) B4890221
theorem B2173431 : Blo 2171435 2173431 := bstep (se 1 (by rfl) ⟨1630073, by rfl⟩ : syracuseStep 2173431 = 3260147) B3260147
theorem B4126133 : Blo 2171435 4126133 := bbase (se 5 (by rfl) ⟨193412, by rfl⟩ : syracuseStep 4126133 = 386825) (by norm_num)
theorem B2750755 : Blo 2171435 2750755 := bstep (se 1 (by rfl) ⟨2063066, by rfl⟩ : syracuseStep 2750755 = 4126133) B4126133
theorem B3667673 : Blo 2171435 3667673 := bstep (se 2 (by rfl) ⟨1375377, by rfl⟩ : syracuseStep 3667673 = 2750755) B2750755
theorem B2445115 : Blo 2171435 2445115 := bstep (se 1 (by rfl) ⟨1833836, by rfl⟩ : syracuseStep 2445115 = 3667673) B3667673
theorem B3260153 : Blo 2171435 3260153 := bstep (se 2 (by rfl) ⟨1222557, by rfl⟩ : syracuseStep 3260153 = 2445115) B2445115
theorem B2173435 : Blo 2171435 2173435 := bstep (se 1 (by rfl) ⟨1630076, by rfl⟩ : syracuseStep 2173435 = 3260153) B3260153
theorem C0 (j : ℕ) (h1 : 542858 ≤ j) (h2 : j ≤ 543358) : Blo 2171435 (4 * j + 3) := by
  interval_cases j
  · exact B2171435
  · exact B2171439
  · exact B2171443
  · exact B2171447
  · exact B2171451
  · exact B2171455
  · exact B2171459
  · exact B2171463
  · exact B2171467
  · exact B2171471
  · exact B2171475
  · exact B2171479
  · exact B2171483
  · exact B2171487
  · exact B2171491
  · exact B2171495
  · exact B2171499
  · exact B2171503
  · exact B2171507
  · exact B2171511
  · exact B2171515
  · exact B2171519
  · exact B2171523
  · exact B2171527
  · exact B2171531
  · exact B2171535
  · exact B2171539
  · exact B2171543
  · exact B2171547
  · exact B2171551
  · exact B2171555
  · exact B2171559
  · exact B2171563
  · exact B2171567
  · exact B2171571
  · exact B2171575
  · exact B2171579
  · exact B2171583
  · exact B2171587
  · exact B2171591
  · exact B2171595
  · exact B2171599
  · exact B2171603
  · exact B2171607
  · exact B2171611
  · exact B2171615
  · exact B2171619
  · exact B2171623
  · exact B2171627
  · exact B2171631
  · exact B2171635
  · exact B2171639
  · exact B2171643
  · exact B2171647
  · exact B2171651
  · exact B2171655
  · exact B2171659
  · exact B2171663
  · exact B2171667
  · exact B2171671
  · exact B2171675
  · exact B2171679
  · exact B2171683
  · exact B2171687
  · exact B2171691
  · exact B2171695
  · exact B2171699
  · exact B2171703
  · exact B2171707
  · exact B2171711
  · exact B2171715
  · exact B2171719
  · exact B2171723
  · exact B2171727
  · exact B2171731
  · exact B2171735
  · exact B2171739
  · exact B2171743
  · exact B2171747
  · exact B2171751
  · exact B2171755
  · exact B2171759
  · exact B2171763
  · exact B2171767
  · exact B2171771
  · exact B2171775
  · exact B2171779
  · exact B2171783
  · exact B2171787
  · exact B2171791
  · exact B2171795
  · exact B2171799
  · exact B2171803
  · exact B2171807
  · exact B2171811
  · exact B2171815
  · exact B2171819
  · exact B2171823
  · exact B2171827
  · exact B2171831
  · exact B2171835
  · exact B2171839
  · exact B2171843
  · exact B2171847
  · exact B2171851
  · exact B2171855
  · exact B2171859
  · exact B2171863
  · exact B2171867
  · exact B2171871
  · exact B2171875
  · exact B2171879
  · exact B2171883
  · exact B2171887
  · exact B2171891
  · exact B2171895
  · exact B2171899
  · exact B2171903
  · exact B2171907
  · exact B2171911
  · exact B2171915
  · exact B2171919
  · exact B2171923
  · exact B2171927
  · exact B2171931
  · exact B2171935
  · exact B2171939
  · exact B2171943
  · exact B2171947
  · exact B2171951
  · exact B2171955
  · exact B2171959
  · exact B2171963
  · exact B2171967
  · exact B2171971
  · exact B2171975
  · exact B2171979
  · exact B2171983
  · exact B2171987
  · exact B2171991
  · exact B2171995
  · exact B2171999
  · exact B2172003
  · exact B2172007
  · exact B2172011
  · exact B2172015
  · exact B2172019
  · exact B2172023
  · exact B2172027
  · exact B2172031
  · exact B2172035
  · exact B2172039
  · exact B2172043
  · exact B2172047
  · exact B2172051
  · exact B2172055
  · exact B2172059
  · exact B2172063
  · exact B2172067
  · exact B2172071
  · exact B2172075
  · exact B2172079
  · exact B2172083
  · exact B2172087
  · exact B2172091
  · exact B2172095
  · exact B2172099
  · exact B2172103
  · exact B2172107
  · exact B2172111
  · exact B2172115
  · exact B2172119
  · exact B2172123
  · exact B2172127
  · exact B2172131
  · exact B2172135
  · exact B2172139
  · exact B2172143
  · exact B2172147
  · exact B2172151
  · exact B2172155
  · exact B2172159
  · exact B2172163
  · exact B2172167
  · exact B2172171
  · exact B2172175
  · exact B2172179
  · exact B2172183
  · exact B2172187
  · exact B2172191
  · exact B2172195
  · exact B2172199
  · exact B2172203
  · exact B2172207
  · exact B2172211
  · exact B2172215
  · exact B2172219
  · exact B2172223
  · exact B2172227
  · exact B2172231
  · exact B2172235
  · exact B2172239
  · exact B2172243
  · exact B2172247
  · exact B2172251
  · exact B2172255
  · exact B2172259
  · exact B2172263
  · exact B2172267
  · exact B2172271
  · exact B2172275
  · exact B2172279
  · exact B2172283
  · exact B2172287
  · exact B2172291
  · exact B2172295
  · exact B2172299
  · exact B2172303
  · exact B2172307
  · exact B2172311
  · exact B2172315
  · exact B2172319
  · exact B2172323
  · exact B2172327
  · exact B2172331
  · exact B2172335
  · exact B2172339
  · exact B2172343
  · exact B2172347
  · exact B2172351
  · exact B2172355
  · exact B2172359
  · exact B2172363
  · exact B2172367
  · exact B2172371
  · exact B2172375
  · exact B2172379
  · exact B2172383
  · exact B2172387
  · exact B2172391
  · exact B2172395
  · exact B2172399
  · exact B2172403
  · exact B2172407
  · exact B2172411
  · exact B2172415
  · exact B2172419
  · exact B2172423
  · exact B2172427
  · exact B2172431
  · exact B2172435
  · exact B2172439
  · exact B2172443
  · exact B2172447
  · exact B2172451
  · exact B2172455
  · exact B2172459
  · exact B2172463
  · exact B2172467
  · exact B2172471
  · exact B2172475
  · exact B2172479
  · exact B2172483
  · exact B2172487
  · exact B2172491
  · exact B2172495
  · exact B2172499
  · exact B2172503
  · exact B2172507
  · exact B2172511
  · exact B2172515
  · exact B2172519
  · exact B2172523
  · exact B2172527
  · exact B2172531
  · exact B2172535
  · exact B2172539
  · exact B2172543
  · exact B2172547
  · exact B2172551
  · exact B2172555
  · exact B2172559
  · exact B2172563
  · exact B2172567
  · exact B2172571
  · exact B2172575
  · exact B2172579
  · exact B2172583
  · exact B2172587
  · exact B2172591
  · exact B2172595
  · exact B2172599
  · exact B2172603
  · exact B2172607
  · exact B2172611
  · exact B2172615
  · exact B2172619
  · exact B2172623
  · exact B2172627
  · exact B2172631
  · exact B2172635
  · exact B2172639
  · exact B2172643
  · exact B2172647
  · exact B2172651
  · exact B2172655
  · exact B2172659
  · exact B2172663
  · exact B2172667
  · exact B2172671
  · exact B2172675
  · exact B2172679
  · exact B2172683
  · exact B2172687
  · exact B2172691
  · exact B2172695
  · exact B2172699
  · exact B2172703
  · exact B2172707
  · exact B2172711
  · exact B2172715
  · exact B2172719
  · exact B2172723
  · exact B2172727
  · exact B2172731
  · exact B2172735
  · exact B2172739
  · exact B2172743
  · exact B2172747
  · exact B2172751
  · exact B2172755
  · exact B2172759
  · exact B2172763
  · exact B2172767
  · exact B2172771
  · exact B2172775
  · exact B2172779
  · exact B2172783
  · exact B2172787
  · exact B2172791
  · exact B2172795
  · exact B2172799
  · exact B2172803
  · exact B2172807
  · exact B2172811
  · exact B2172815
  · exact B2172819
  · exact B2172823
  · exact B2172827
  · exact B2172831
  · exact B2172835
  · exact B2172839
  · exact B2172843
  · exact B2172847
  · exact B2172851
  · exact B2172855
  · exact B2172859
  · exact B2172863
  · exact B2172867
  · exact B2172871
  · exact B2172875
  · exact B2172879
  · exact B2172883
  · exact B2172887
  · exact B2172891
  · exact B2172895
  · exact B2172899
  · exact B2172903
  · exact B2172907
  · exact B2172911
  · exact B2172915
  · exact B2172919
  · exact B2172923
  · exact B2172927
  · exact B2172931
  · exact B2172935
  · exact B2172939
  · exact B2172943
  · exact B2172947
  · exact B2172951
  · exact B2172955
  · exact B2172959
  · exact B2172963
  · exact B2172967
  · exact B2172971
  · exact B2172975
  · exact B2172979
  · exact B2172983
  · exact B2172987
  · exact B2172991
  · exact B2172995
  · exact B2172999
  · exact B2173003
  · exact B2173007
  · exact B2173011
  · exact B2173015
  · exact B2173019
  · exact B2173023
  · exact B2173027
  · exact B2173031
  · exact B2173035
  · exact B2173039
  · exact B2173043
  · exact B2173047
  · exact B2173051
  · exact B2173055
  · exact B2173059
  · exact B2173063
  · exact B2173067
  · exact B2173071
  · exact B2173075
  · exact B2173079
  · exact B2173083
  · exact B2173087
  · exact B2173091
  · exact B2173095
  · exact B2173099
  · exact B2173103
  · exact B2173107
  · exact B2173111
  · exact B2173115
  · exact B2173119
  · exact B2173123
  · exact B2173127
  · exact B2173131
  · exact B2173135
  · exact B2173139
  · exact B2173143
  · exact B2173147
  · exact B2173151
  · exact B2173155
  · exact B2173159
  · exact B2173163
  · exact B2173167
  · exact B2173171
  · exact B2173175
  · exact B2173179
  · exact B2173183
  · exact B2173187
  · exact B2173191
  · exact B2173195
  · exact B2173199
  · exact B2173203
  · exact B2173207
  · exact B2173211
  · exact B2173215
  · exact B2173219
  · exact B2173223
  · exact B2173227
  · exact B2173231
  · exact B2173235
  · exact B2173239
  · exact B2173243
  · exact B2173247
  · exact B2173251
  · exact B2173255
  · exact B2173259
  · exact B2173263
  · exact B2173267
  · exact B2173271
  · exact B2173275
  · exact B2173279
  · exact B2173283
  · exact B2173287
  · exact B2173291
  · exact B2173295
  · exact B2173299
  · exact B2173303
  · exact B2173307
  · exact B2173311
  · exact B2173315
  · exact B2173319
  · exact B2173323
  · exact B2173327
  · exact B2173331
  · exact B2173335
  · exact B2173339
  · exact B2173343
  · exact B2173347
  · exact B2173351
  · exact B2173355
  · exact B2173359
  · exact B2173363
  · exact B2173367
  · exact B2173371
  · exact B2173375
  · exact B2173379
  · exact B2173383
  · exact B2173387
  · exact B2173391
  · exact B2173395
  · exact B2173399
  · exact B2173403
  · exact B2173407
  · exact B2173411
  · exact B2173415
  · exact B2173419
  · exact B2173423
  · exact B2173427
  · exact B2173431
  · exact B2173435
theorem solution (m : ℕ) (hlo : 2171435 ≤ m) (hhi : m ≤ 2173435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 542858 ≤ j := by omega
    have hj2 : j ≤ 543358 := by omega
    have hb : Blo 2171435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
