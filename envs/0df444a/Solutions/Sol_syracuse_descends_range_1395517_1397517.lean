-- Prove2me | solution 1 for syracuse_descends_range_1395517_1397517
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:43.564163+00:00
-- url     : https://prove2.me/submissions/16592d4b-2d4c-471b-a034-316f3bdbdbb2

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


theorem B5963813 : Blo 1395517 5963813 := bbase (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) (by norm_num)
theorem B8953973 : Blo 1395517 8953973 := bbase (se 5 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 8953973 = 839435) (by norm_num)
theorem B4710581 : Blo 1395517 4710581 := bbase (se 5 (by rfl) ⟨220808, by rfl⟩ : syracuseStep 4710581 = 441617) (by norm_num)
theorem B5300437 : Blo 1395517 5300437 := bbase (se 7 (by rfl) ⟨62114, by rfl⟩ : syracuseStep 5300437 = 124229) (by norm_num)
theorem B1614053 : Blo 1395517 1614053 := bbase (se 4 (by rfl) ⟨151317, by rfl⟩ : syracuseStep 1614053 = 302635) (by norm_num)
theorem B2236661 : Blo 1395517 2236661 := bbase (se 5 (by rfl) ⟨104843, by rfl⟩ : syracuseStep 2236661 = 209687) (by norm_num)
theorem B14328085 : Blo 1395517 14328085 := bbase (se 6 (by rfl) ⟨335814, by rfl⟩ : syracuseStep 14328085 = 671629) (by norm_num)
theorem B2982197 : Blo 1395517 2982197 := bbase (se 5 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 2982197 = 279581) (by norm_num)
theorem B1491257 : Blo 1395517 1491257 := bbase (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) (by norm_num)
theorem B5661029 : Blo 1395517 5661029 := bbase (se 4 (by rfl) ⟨530721, by rfl⟩ : syracuseStep 5661029 = 1061443) (by norm_num)
theorem B2687357 : Blo 1395517 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B1491329 : Blo 1395517 1491329 := bbase (se 2 (by rfl) ⟨559248, by rfl⟩ : syracuseStep 1491329 = 1118497) (by norm_num)
theorem B2236853 : Blo 1395517 2236853 := bbase (se 5 (by rfl) ⟨104852, by rfl⟩ : syracuseStep 2236853 = 209705) (by norm_num)
theorem B2122181 : Blo 1395517 2122181 := bbase (se 4 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 2122181 = 397909) (by norm_num)
theorem B5374421 : Blo 1395517 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B7070165 : Blo 1395517 7070165 := bbase (se 7 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 7070165 = 165707) (by norm_num)
theorem B8487413 : Blo 1395517 8487413 := bbase (se 5 (by rfl) ⟨397847, by rfl⟩ : syracuseStep 8487413 = 795695) (by norm_num)
theorem B5300741 : Blo 1395517 5300741 := bbase (se 4 (by rfl) ⟨496944, by rfl⟩ : syracuseStep 5300741 = 993889) (by norm_num)
theorem B1491517 : Blo 1395517 1491517 := bbase (se 3 (by rfl) ⟨279659, by rfl⟩ : syracuseStep 1491517 = 559319) (by norm_num)
theorem B4244069 : Blo 1395517 4244069 := bbase (se 4 (by rfl) ⟨397881, by rfl⟩ : syracuseStep 4244069 = 795763) (by norm_num)
theorem B4711013 : Blo 1395517 4711013 := bbase (se 4 (by rfl) ⟨441657, by rfl⟩ : syracuseStep 4711013 = 883315) (by norm_num)
theorem B3023581 : Blo 1395517 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B13607669 : Blo 1395517 13607669 := bbase (se 5 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 13607669 = 1275719) (by norm_num)
theorem B1491701 : Blo 1395517 1491701 := bbase (se 5 (by rfl) ⟨69923, by rfl⟩ : syracuseStep 1491701 = 139847) (by norm_num)
theorem B3777349 : Blo 1395517 3777349 := bbase (se 4 (by rfl) ⟨354126, by rfl⟩ : syracuseStep 3777349 = 708253) (by norm_num)
theorem B4711445 : Blo 1395517 4711445 := bbase (se 6 (by rfl) ⟨110424, by rfl⟩ : syracuseStep 4711445 = 220849) (by norm_num)
theorem B7169093 : Blo 1395517 7169093 := bbase (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) (by norm_num)
theorem B2516093 : Blo 1395517 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B1434757 : Blo 1395517 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B2983061 : Blo 1395517 2983061 := bbase (se 6 (by rfl) ⟨69915, by rfl⟩ : syracuseStep 2983061 = 139831) (by norm_num)
theorem B3679445 : Blo 1395517 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2983205 : Blo 1395517 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B6710597 : Blo 1395517 6710597 := bbase (se 4 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 6710597 = 1258237) (by norm_num)
theorem B2237789 : Blo 1395517 2237789 := bbase (se 3 (by rfl) ⟨419585, by rfl⟩ : syracuseStep 2237789 = 839171) (by norm_num)
theorem B4711877 : Blo 1395517 4711877 := bbase (se 4 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 4711877 = 883477) (by norm_num)
theorem B3974645 : Blo 1395517 3974645 := bbase (se 5 (by rfl) ⟨186311, by rfl⟩ : syracuseStep 3974645 = 372623) (by norm_num)
theorem B2238173 : Blo 1395517 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B7071461 : Blo 1395517 7071461 := bbase (se 4 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 7071461 = 1325899) (by norm_num)
theorem B5965589 : Blo 1395517 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B6801221 : Blo 1395517 6801221 := bbase (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) (by norm_num)
theorem B4474693 : Blo 1395517 4474693 := bbase (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) (by norm_num)
theorem B2238301 : Blo 1395517 2238301 := bbase (se 3 (by rfl) ⟨419681, by rfl⟩ : syracuseStep 2238301 = 839363) (by norm_num)
theorem B4712309 : Blo 1395517 4712309 := bbase (se 5 (by rfl) ⟨220889, by rfl⟩ : syracuseStep 4712309 = 441779) (by norm_num)
theorem B4474757 : Blo 1395517 4474757 := bbase (se 4 (by rfl) ⟨419508, by rfl⟩ : syracuseStep 4474757 = 839017) (by norm_num)
theorem B3532693 : Blo 1395517 3532693 := bbase (se 6 (by rfl) ⟨82797, by rfl⟩ : syracuseStep 3532693 = 165595) (by norm_num)
theorem B3024877 : Blo 1395517 3024877 := bbase (se 3 (by rfl) ⟨567164, by rfl⟩ : syracuseStep 3024877 = 1134329) (by norm_num)
theorem B4777973 : Blo 1395517 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B3532805 : Blo 1395517 3532805 := bbase (se 4 (by rfl) ⟨331200, by rfl⟩ : syracuseStep 3532805 = 662401) (by norm_num)
theorem B2983949 : Blo 1395517 2983949 := bbase (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) (by norm_num)
theorem B20400149 : Blo 1395517 20400149 := bbase (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) (by norm_num)
theorem B6367349 : Blo 1395517 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B20400277 : Blo 1395517 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B10610837 : Blo 1395517 10610837 := bbase (se 6 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 10610837 = 497383) (by norm_num)
theorem B7948469 : Blo 1395517 7948469 := bbase (se 5 (by rfl) ⟨372584, by rfl⟩ : syracuseStep 7948469 = 745169) (by norm_num)
theorem B3532997 : Blo 1395517 3532997 := bbase (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) (by norm_num)
theorem B4712741 : Blo 1395517 4712741 := bbase (se 4 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 4712741 = 883639) (by norm_num)
theorem B3139973 : Blo 1395517 3139973 := bbase (se 4 (by rfl) ⟨294372, by rfl⟩ : syracuseStep 3139973 = 588745) (by norm_num)
theorem B2550197 : Blo 1395517 2550197 := bbase (se 5 (by rfl) ⟨119540, by rfl⟩ : syracuseStep 2550197 = 239081) (by norm_num)
theorem B3140045 : Blo 1395517 3140045 := bbase (se 3 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 3140045 = 1177517) (by norm_num)
theorem B3582413 : Blo 1395517 3582413 := bbase (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) (by norm_num)
theorem B1591781 : Blo 1395517 1591781 := bbase (se 4 (by rfl) ⟨149229, by rfl⟩ : syracuseStep 1591781 = 298459) (by norm_num)
theorem B6048229 : Blo 1395517 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B2550253 : Blo 1395517 2550253 := bbase (se 3 (by rfl) ⟨478172, by rfl⟩ : syracuseStep 2550253 = 956345) (by norm_num)
theorem B3140117 : Blo 1395517 3140117 := bbase (se 6 (by rfl) ⟨73596, by rfl⟩ : syracuseStep 3140117 = 147193) (by norm_num)
theorem B16116245 : Blo 1395517 16116245 := bbase (se 6 (by rfl) ⟨377724, by rfl⟩ : syracuseStep 16116245 = 755449) (by norm_num)
theorem B3533341 : Blo 1395517 3533341 := bbase (se 3 (by rfl) ⟨662501, by rfl⟩ : syracuseStep 3533341 = 1325003) (by norm_num)
theorem B10603061 : Blo 1395517 10603061 := bbase (se 5 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 10603061 = 994037) (by norm_num)
theorem B5302853 : Blo 1395517 5302853 := bbase (se 4 (by rfl) ⟨497142, by rfl⟩ : syracuseStep 5302853 = 994285) (by norm_num)
theorem B3140189 : Blo 1395517 3140189 := bbase (se 3 (by rfl) ⟨588785, by rfl⟩ : syracuseStep 3140189 = 1177571) (by norm_num)
theorem B3533453 : Blo 1395517 3533453 := bbase (se 3 (by rfl) ⟨662522, by rfl⟩ : syracuseStep 3533453 = 1325045) (by norm_num)
theorem B3140261 : Blo 1395517 3140261 := bbase (se 4 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 3140261 = 588799) (by norm_num)
theorem B2869925 : Blo 1395517 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B4713173 : Blo 1395517 4713173 := bbase (se 7 (by rfl) ⟨55232, by rfl⟩ : syracuseStep 4713173 = 110465) (by norm_num)
theorem B3140333 : Blo 1395517 3140333 := bbase (se 3 (by rfl) ⟨588812, by rfl⟩ : syracuseStep 3140333 = 1177625) (by norm_num)
theorem B5966581 : Blo 1395517 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B2984701 : Blo 1395517 2984701 := bbase (se 3 (by rfl) ⟨559631, by rfl⟩ : syracuseStep 2984701 = 1119263) (by norm_num)
theorem B3140405 : Blo 1395517 3140405 := bbase (se 5 (by rfl) ⟨147206, by rfl⟩ : syracuseStep 3140405 = 294413) (by norm_num)
theorem B3533645 : Blo 1395517 3533645 := bbase (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) (by norm_num)
theorem B5303141 : Blo 1395517 5303141 := bbase (se 4 (by rfl) ⟨497169, by rfl⟩ : syracuseStep 5303141 = 994339) (by norm_num)
theorem B3140477 : Blo 1395517 3140477 := bbase (se 3 (by rfl) ⟨588839, by rfl⟩ : syracuseStep 3140477 = 1177679) (by norm_num)
theorem B4533157 : Blo 1395517 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B3140549 : Blo 1395517 3140549 := bbase (se 4 (by rfl) ⟨294426, by rfl⟩ : syracuseStep 3140549 = 588853) (by norm_num)
theorem B11332565 : Blo 1395517 11332565 := bbase (se 7 (by rfl) ⟨132803, by rfl⟩ : syracuseStep 11332565 = 265607) (by norm_num)
theorem B7072757 : Blo 1395517 7072757 := bbase (se 5 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 7072757 = 663071) (by norm_num)
theorem B3140621 : Blo 1395517 3140621 := bbase (se 3 (by rfl) ⟨588866, by rfl⟩ : syracuseStep 3140621 = 1177733) (by norm_num)
theorem B3976229 : Blo 1395517 3976229 := bbase (se 4 (by rfl) ⟨372771, by rfl⟩ : syracuseStep 3976229 = 745543) (by norm_num)
theorem B4533317 : Blo 1395517 4533317 := bbase (se 4 (by rfl) ⟨424998, by rfl⟩ : syracuseStep 4533317 = 849997) (by norm_num)
theorem B3140693 : Blo 1395517 3140693 := bbase (se 8 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 3140693 = 36805) (by norm_num)
theorem B2518117 : Blo 1395517 2518117 := bbase (se 4 (by rfl) ⟨236073, by rfl⟩ : syracuseStep 2518117 = 472147) (by norm_num)
theorem B4713605 : Blo 1395517 4713605 := bbase (se 4 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 4713605 = 883801) (by norm_num)
theorem B3140765 : Blo 1395517 3140765 := bbase (se 3 (by rfl) ⟨588893, by rfl⟩ : syracuseStep 3140765 = 1177787) (by norm_num)
theorem B3533989 : Blo 1395517 3533989 := bbase (se 4 (by rfl) ⟨331311, by rfl⟩ : syracuseStep 3533989 = 662623) (by norm_num)
theorem B3140837 : Blo 1395517 3140837 := bbase (se 4 (by rfl) ⟨294453, by rfl⟩ : syracuseStep 3140837 = 588907) (by norm_num)
theorem B3534101 : Blo 1395517 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B10071317 : Blo 1395517 10071317 := bbase (se 6 (by rfl) ⟨236046, by rfl⟩ : syracuseStep 10071317 = 472093) (by norm_num)
theorem B3140909 : Blo 1395517 3140909 := bbase (se 3 (by rfl) ⟨588920, by rfl⟩ : syracuseStep 3140909 = 1177841) (by norm_num)
theorem B3140981 : Blo 1395517 3140981 := bbase (se 5 (by rfl) ⟨147233, by rfl⟩ : syracuseStep 3140981 = 294467) (by norm_num)
theorem B6991237 : Blo 1395517 6991237 := bbase (se 4 (by rfl) ⟨655428, by rfl⟩ : syracuseStep 6991237 = 1310857) (by norm_num)
theorem B7064981 : Blo 1395517 7064981 := bbase (se 6 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 7064981 = 331171) (by norm_num)
theorem B1887637 : Blo 1395517 1887637 := bbase (se 6 (by rfl) ⟨44241, by rfl⟩ : syracuseStep 1887637 = 88483) (by norm_num)
theorem B3141053 : Blo 1395517 3141053 := bbase (se 3 (by rfl) ⟨588947, by rfl⟩ : syracuseStep 3141053 = 1177895) (by norm_num)
theorem B3534293 : Blo 1395517 3534293 := bbase (se 7 (by rfl) ⟨41417, by rfl⟩ : syracuseStep 3534293 = 82835) (by norm_num)
theorem B4304341 : Blo 1395517 4304341 := bbase (se 7 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 4304341 = 100883) (by norm_num)
theorem B2649581 : Blo 1395517 2649581 := bbase (se 3 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 2649581 = 993593) (by norm_num)
theorem B3141125 : Blo 1395517 3141125 := bbase (se 4 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 3141125 = 588961) (by norm_num)
theorem B6458885 : Blo 1395517 6458885 := bbase (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) (by norm_num)
theorem B4714037 : Blo 1395517 4714037 := bbase (se 5 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 4714037 = 441941) (by norm_num)
theorem B3141197 : Blo 1395517 3141197 := bbase (se 3 (by rfl) ⟨588974, by rfl⟩ : syracuseStep 3141197 = 1177949) (by norm_num)
theorem B3141269 : Blo 1395517 3141269 := bbase (se 6 (by rfl) ⟨73623, by rfl⟩ : syracuseStep 3141269 = 147247) (by norm_num)
theorem B3976901 : Blo 1395517 3976901 := bbase (se 4 (by rfl) ⟨372834, by rfl⟩ : syracuseStep 3976901 = 745669) (by norm_num)
theorem B3141341 : Blo 1395517 3141341 := bbase (se 3 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 3141341 = 1178003) (by norm_num)
theorem B3141413 : Blo 1395517 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B3534637 : Blo 1395517 3534637 := bbase (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) (by norm_num)
theorem B7958357 : Blo 1395517 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B3141485 : Blo 1395517 3141485 := bbase (se 3 (by rfl) ⟨589028, by rfl⟩ : syracuseStep 3141485 = 1178057) (by norm_num)
theorem B2355061 : Blo 1395517 2355061 := bbase (se 5 (by rfl) ⟨110393, by rfl⟩ : syracuseStep 2355061 = 220787) (by norm_num)
theorem B3534749 : Blo 1395517 3534749 := bbase (se 3 (by rfl) ⟨662765, by rfl⟩ : syracuseStep 3534749 = 1325531) (by norm_num)
theorem B2387885 : Blo 1395517 2387885 := bbase (se 3 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 2387885 = 895457) (by norm_num)
theorem B3141557 : Blo 1395517 3141557 := bbase (se 5 (by rfl) ⟨147260, by rfl⟩ : syracuseStep 3141557 = 294521) (by norm_num)
theorem B4599749 : Blo 1395517 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B2355149 : Blo 1395517 2355149 := bbase (se 3 (by rfl) ⟨441590, by rfl⟩ : syracuseStep 2355149 = 883181) (by norm_num)
theorem B4714469 : Blo 1395517 4714469 := bbase (se 4 (by rfl) ⟨441981, by rfl⟩ : syracuseStep 4714469 = 883963) (by norm_num)
theorem B3141629 : Blo 1395517 3141629 := bbase (se 3 (by rfl) ⟨589055, by rfl⟩ : syracuseStep 3141629 = 1178111) (by norm_num)
theorem B5304325 : Blo 1395517 5304325 := bbase (se 4 (by rfl) ⟨497280, by rfl⟩ : syracuseStep 5304325 = 994561) (by norm_num)
theorem B3141701 : Blo 1395517 3141701 := bbase (se 4 (by rfl) ⟨294534, by rfl⟩ : syracuseStep 3141701 = 589069) (by norm_num)
theorem B2355277 : Blo 1395517 2355277 := bbase (se 3 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 2355277 = 883229) (by norm_num)
theorem B3534941 : Blo 1395517 3534941 := bbase (se 3 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 3534941 = 1325603) (by norm_num)
theorem B3977333 : Blo 1395517 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B3141773 : Blo 1395517 3141773 := bbase (se 3 (by rfl) ⟨589082, by rfl⟩ : syracuseStep 3141773 = 1178165) (by norm_num)
theorem B2355365 : Blo 1395517 2355365 := bbase (se 4 (by rfl) ⟨220815, by rfl⟩ : syracuseStep 2355365 = 441631) (by norm_num)
theorem B3141845 : Blo 1395517 3141845 := bbase (se 7 (by rfl) ⟨36818, by rfl⟩ : syracuseStep 3141845 = 73637) (by norm_num)
theorem B2650333 : Blo 1395517 2650333 := bbase (se 3 (by rfl) ⟨496937, by rfl⟩ : syracuseStep 2650333 = 993875) (by norm_num)
theorem B2093285 : Blo 1395517 2093285 := bbase (se 4 (by rfl) ⟨196245, by rfl⟩ : syracuseStep 2093285 = 392491) (by norm_num)
theorem B1593589 : Blo 1395517 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B2093309 : Blo 1395517 2093309 := bbase (se 3 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 2093309 = 784991) (by norm_num)
theorem B7074053 : Blo 1395517 7074053 := bbase (se 4 (by rfl) ⟨663192, by rfl⟩ : syracuseStep 7074053 = 1326385) (by norm_num)
theorem B2093333 : Blo 1395517 2093333 := bbase (se 6 (by rfl) ⟨49062, by rfl⟩ : syracuseStep 2093333 = 98125) (by norm_num)
theorem B3141917 : Blo 1395517 3141917 := bbase (se 3 (by rfl) ⟨589109, by rfl⟩ : syracuseStep 3141917 = 1178219) (by norm_num)
theorem B2355493 : Blo 1395517 2355493 := bbase (se 4 (by rfl) ⟨220827, by rfl⟩ : syracuseStep 2355493 = 441655) (by norm_num)
theorem B2093357 : Blo 1395517 2093357 := bbase (se 3 (by rfl) ⟨392504, by rfl⟩ : syracuseStep 2093357 = 785009) (by norm_num)
theorem B5304629 : Blo 1395517 5304629 := bbase (se 5 (by rfl) ⟨248654, by rfl⟩ : syracuseStep 5304629 = 497309) (by norm_num)
theorem B2093381 : Blo 1395517 2093381 := bbase (se 4 (by rfl) ⟨196254, by rfl⟩ : syracuseStep 2093381 = 392509) (by norm_num)
theorem B3584341 : Blo 1395517 3584341 := bbase (se 10 (by rfl) ⟨5250, by rfl⟩ : syracuseStep 3584341 = 10501) (by norm_num)
theorem B2093405 : Blo 1395517 2093405 := bbase (se 3 (by rfl) ⟨392513, by rfl⟩ : syracuseStep 2093405 = 785027) (by norm_num)
theorem B3141989 : Blo 1395517 3141989 := bbase (se 4 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 3141989 = 589123) (by norm_num)
theorem B2650477 : Blo 1395517 2650477 := bbase (se 3 (by rfl) ⟨496964, by rfl⟩ : syracuseStep 2650477 = 993929) (by norm_num)
theorem B2093429 : Blo 1395517 2093429 := bbase (se 5 (by rfl) ⟨98129, by rfl⟩ : syracuseStep 2093429 = 196259) (by norm_num)
theorem B2355581 : Blo 1395517 2355581 := bbase (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) (by norm_num)
theorem B2093453 : Blo 1395517 2093453 := bbase (se 3 (by rfl) ⟨392522, by rfl⟩ : syracuseStep 2093453 = 785045) (by norm_num)
theorem B4714901 : Blo 1395517 4714901 := bbase (se 6 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 4714901 = 221011) (by norm_num)
theorem B2093477 : Blo 1395517 2093477 := bbase (se 4 (by rfl) ⟨196263, by rfl⟩ : syracuseStep 2093477 = 392527) (by norm_num)
theorem B3142061 : Blo 1395517 3142061 := bbase (se 3 (by rfl) ⟨589136, by rfl⟩ : syracuseStep 3142061 = 1178273) (by norm_num)
theorem B3535285 : Blo 1395517 3535285 := bbase (se 5 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 3535285 = 331433) (by norm_num)
theorem B2093501 : Blo 1395517 2093501 := bbase (se 3 (by rfl) ⟨392531, by rfl⟩ : syracuseStep 2093501 = 785063) (by norm_num)
theorem B1987021 : Blo 1395517 1987021 := bbase (se 3 (by rfl) ⟨372566, by rfl⟩ : syracuseStep 1987021 = 745133) (by norm_num)
theorem B2093525 : Blo 1395517 2093525 := bbase (se 7 (by rfl) ⟨24533, by rfl⟩ : syracuseStep 2093525 = 49067) (by norm_num)
theorem B2093549 : Blo 1395517 2093549 := bbase (se 3 (by rfl) ⟨392540, by rfl⟩ : syracuseStep 2093549 = 785081) (by norm_num)
theorem B3142133 : Blo 1395517 3142133 := bbase (se 5 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 3142133 = 294575) (by norm_num)
theorem B2355709 : Blo 1395517 2355709 := bbase (se 3 (by rfl) ⟨441695, by rfl⟩ : syracuseStep 2355709 = 883391) (by norm_num)
theorem B2093573 : Blo 1395517 2093573 := bbase (se 4 (by rfl) ⟨196272, by rfl⟩ : syracuseStep 2093573 = 392545) (by norm_num)
theorem B2650637 : Blo 1395517 2650637 := bbase (se 3 (by rfl) ⟨496994, by rfl⟩ : syracuseStep 2650637 = 993989) (by norm_num)
theorem B17904149 : Blo 1395517 17904149 := bbase (se 6 (by rfl) ⟨419628, by rfl⟩ : syracuseStep 17904149 = 839257) (by norm_num)
theorem B2093597 : Blo 1395517 2093597 := bbase (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) (by norm_num)
theorem B3535397 : Blo 1395517 3535397 := bbase (se 4 (by rfl) ⟨331443, by rfl⟩ : syracuseStep 3535397 = 662887) (by norm_num)
theorem B2093621 : Blo 1395517 2093621 := bbase (se 5 (by rfl) ⟨98138, by rfl⟩ : syracuseStep 2093621 = 196277) (by norm_num)
theorem B3142205 : Blo 1395517 3142205 := bbase (se 3 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 3142205 = 1178327) (by norm_num)
theorem B2093645 : Blo 1395517 2093645 := bbase (se 3 (by rfl) ⟨392558, by rfl⟩ : syracuseStep 2093645 = 785117) (by norm_num)
theorem B2355797 : Blo 1395517 2355797 := bbase (se 8 (by rfl) ⟨13803, by rfl⟩ : syracuseStep 2355797 = 27607) (by norm_num)
theorem B3183197 : Blo 1395517 3183197 := bbase (se 3 (by rfl) ⟨596849, by rfl⟩ : syracuseStep 3183197 = 1193699) (by norm_num)
theorem B2093669 : Blo 1395517 2093669 := bbase (se 4 (by rfl) ⟨196281, by rfl⟩ : syracuseStep 2093669 = 392563) (by norm_num)
theorem B2093693 : Blo 1395517 2093693 := bbase (se 3 (by rfl) ⟨392567, by rfl⟩ : syracuseStep 2093693 = 785135) (by norm_num)
theorem B3142277 : Blo 1395517 3142277 := bbase (se 4 (by rfl) ⟨294588, by rfl⟩ : syracuseStep 3142277 = 589177) (by norm_num)
theorem B2093717 : Blo 1395517 2093717 := bbase (se 6 (by rfl) ⟨49071, by rfl⟩ : syracuseStep 2093717 = 98143) (by norm_num)
theorem B2650781 : Blo 1395517 2650781 := bbase (se 3 (by rfl) ⟨497021, by rfl⟩ : syracuseStep 2650781 = 994043) (by norm_num)
theorem B7066277 : Blo 1395517 7066277 := bbase (se 4 (by rfl) ⟨662463, by rfl⟩ : syracuseStep 7066277 = 1324927) (by norm_num)
theorem B2093741 : Blo 1395517 2093741 := bbase (se 3 (by rfl) ⟨392576, by rfl⟩ : syracuseStep 2093741 = 785153) (by norm_num)
theorem B2093765 : Blo 1395517 2093765 := bbase (se 4 (by rfl) ⟨196290, by rfl⟩ : syracuseStep 2093765 = 392581) (by norm_num)
theorem B3142349 : Blo 1395517 3142349 := bbase (se 3 (by rfl) ⟨589190, by rfl⟩ : syracuseStep 3142349 = 1178381) (by norm_num)
theorem B2355925 : Blo 1395517 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B2093789 : Blo 1395517 2093789 := bbase (se 3 (by rfl) ⟨392585, by rfl⟩ : syracuseStep 2093789 = 785171) (by norm_num)
theorem B3535589 : Blo 1395517 3535589 := bbase (se 4 (by rfl) ⟨331461, by rfl⟩ : syracuseStep 3535589 = 662923) (by norm_num)
theorem B2093813 : Blo 1395517 2093813 := bbase (se 5 (by rfl) ⟨98147, by rfl⟩ : syracuseStep 2093813 = 196295) (by norm_num)
theorem B7549685 : Blo 1395517 7549685 := bbase (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) (by norm_num)
theorem B2093837 : Blo 1395517 2093837 := bbase (se 3 (by rfl) ⟨392594, by rfl⟩ : syracuseStep 2093837 = 785189) (by norm_num)
theorem B3142421 : Blo 1395517 3142421 := bbase (se 6 (by rfl) ⟨73650, by rfl⟩ : syracuseStep 3142421 = 147301) (by norm_num)
theorem B1987357 : Blo 1395517 1987357 := bbase (se 3 (by rfl) ⟨372629, by rfl⟩ : syracuseStep 1987357 = 745259) (by norm_num)
theorem B2093861 : Blo 1395517 2093861 := bbase (se 4 (by rfl) ⟨196299, by rfl⟩ : syracuseStep 2093861 = 392599) (by norm_num)
theorem B2356013 : Blo 1395517 2356013 := bbase (se 3 (by rfl) ⟨441752, by rfl⟩ : syracuseStep 2356013 = 883505) (by norm_num)
theorem B2093885 : Blo 1395517 2093885 := bbase (se 3 (by rfl) ⟨392603, by rfl⟩ : syracuseStep 2093885 = 785207) (by norm_num)
theorem B4715333 : Blo 1395517 4715333 := bbase (se 4 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 4715333 = 884125) (by norm_num)
theorem B1766225 : Blo 1395517 1766225 := bbase (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) (by norm_num)
theorem B2093909 : Blo 1395517 2093909 := bbase (se 9 (by rfl) ⟨6134, by rfl⟩ : syracuseStep 2093909 = 12269) (by norm_num)
theorem B67982165 : Blo 1395517 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B5665621 : Blo 1395517 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B3142493 : Blo 1395517 3142493 := bbase (se 3 (by rfl) ⟨589217, by rfl⟩ : syracuseStep 3142493 = 1178435) (by norm_num)
theorem B3978085 : Blo 1395517 3978085 := bbase (se 4 (by rfl) ⟨372945, by rfl⟩ : syracuseStep 3978085 = 745891) (by norm_num)
theorem B2093933 : Blo 1395517 2093933 := bbase (se 3 (by rfl) ⟨392612, by rfl⟩ : syracuseStep 2093933 = 785225) (by norm_num)
theorem B2093957 : Blo 1395517 2093957 := bbase (se 4 (by rfl) ⟨196308, by rfl⟩ : syracuseStep 2093957 = 392617) (by norm_num)
theorem B1766281 : Blo 1395517 1766281 := bbase (se 2 (by rfl) ⟨662355, by rfl⟩ : syracuseStep 1766281 = 1324711) (by norm_num)
theorem B2093981 : Blo 1395517 2093981 := bbase (se 3 (by rfl) ⟨392621, by rfl⟩ : syracuseStep 2093981 = 785243) (by norm_num)
theorem B3142565 : Blo 1395517 3142565 := bbase (se 4 (by rfl) ⟨294615, by rfl⟩ : syracuseStep 3142565 = 589231) (by norm_num)
theorem B2356141 : Blo 1395517 2356141 := bbase (se 3 (by rfl) ⟨441776, by rfl⟩ : syracuseStep 2356141 = 883553) (by norm_num)
theorem B2094005 : Blo 1395517 2094005 := bbase (se 5 (by rfl) ⟨98156, by rfl⟩ : syracuseStep 2094005 = 196313) (by norm_num)
theorem B2651069 : Blo 1395517 2651069 := bbase (se 3 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 2651069 = 994151) (by norm_num)
theorem B2094029 : Blo 1395517 2094029 := bbase (se 3 (by rfl) ⟨392630, by rfl⟩ : syracuseStep 2094029 = 785261) (by norm_num)
theorem B1512413 : Blo 1395517 1512413 := bbase (se 3 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 1512413 = 567155) (by norm_num)
theorem B2094053 : Blo 1395517 2094053 := bbase (se 4 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 2094053 = 392635) (by norm_num)
theorem B1766377 : Blo 1395517 1766377 := bbase (se 2 (by rfl) ⟨662391, by rfl⟩ : syracuseStep 1766377 = 1324783) (by norm_num)
theorem B3142637 : Blo 1395517 3142637 := bbase (se 3 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 3142637 = 1178489) (by norm_num)
theorem B1987573 : Blo 1395517 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B2094077 : Blo 1395517 2094077 := bbase (se 3 (by rfl) ⟨392639, by rfl⟩ : syracuseStep 2094077 = 785279) (by norm_num)
theorem B2356229 : Blo 1395517 2356229 := bbase (se 4 (by rfl) ⟨220896, by rfl⟩ : syracuseStep 2356229 = 441793) (by norm_num)
theorem B1700869 : Blo 1395517 1700869 := bbase (se 4 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 1700869 = 318913) (by norm_num)
theorem B3183637 : Blo 1395517 3183637 := bbase (se 6 (by rfl) ⟨74616, by rfl⟩ : syracuseStep 3183637 = 149233) (by norm_num)
theorem B2094101 : Blo 1395517 2094101 := bbase (se 6 (by rfl) ⟨49080, by rfl⟩ : syracuseStep 2094101 = 98161) (by norm_num)
theorem B2094125 : Blo 1395517 2094125 := bbase (se 3 (by rfl) ⟨392648, by rfl⟩ : syracuseStep 2094125 = 785297) (by norm_num)
theorem B3142709 : Blo 1395517 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B3535933 : Blo 1395517 3535933 := bbase (se 3 (by rfl) ⟨662987, by rfl⟩ : syracuseStep 3535933 = 1325975) (by norm_num)
theorem B2094149 : Blo 1395517 2094149 := bbase (se 4 (by rfl) ⟨196326, by rfl⟩ : syracuseStep 2094149 = 392653) (by norm_num)
theorem B6370373 : Blo 1395517 6370373 := bbase (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) (by norm_num)
theorem B2651221 : Blo 1395517 2651221 := bbase (se 8 (by rfl) ⟨15534, by rfl⟩ : syracuseStep 2651221 = 31069) (by norm_num)
theorem B15914069 : Blo 1395517 15914069 := bbase (se 8 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 15914069 = 186493) (by norm_num)
theorem B2094173 : Blo 1395517 2094173 := bbase (se 3 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 2094173 = 785315) (by norm_num)
theorem B2094197 : Blo 1395517 2094197 := bbase (se 5 (by rfl) ⟨98165, by rfl⟩ : syracuseStep 2094197 = 196331) (by norm_num)
theorem B3142781 : Blo 1395517 3142781 := bbase (se 3 (by rfl) ⟨589271, by rfl⟩ : syracuseStep 3142781 = 1178543) (by norm_num)
theorem B2356357 : Blo 1395517 2356357 := bbase (se 4 (by rfl) ⟨220908, by rfl⟩ : syracuseStep 2356357 = 441817) (by norm_num)
theorem B2094221 : Blo 1395517 2094221 := bbase (se 3 (by rfl) ⟨392666, by rfl⟩ : syracuseStep 2094221 = 785333) (by norm_num)
theorem B1766549 : Blo 1395517 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B2094245 : Blo 1395517 2094245 := bbase (se 4 (by rfl) ⟨196335, by rfl⟩ : syracuseStep 2094245 = 392671) (by norm_num)
theorem B3536045 : Blo 1395517 3536045 := bbase (se 3 (by rfl) ⟨663008, by rfl⟩ : syracuseStep 3536045 = 1326017) (by norm_num)
theorem B1569973 : Blo 1395517 1569973 := bbase (se 5 (by rfl) ⟨73592, by rfl⟩ : syracuseStep 1569973 = 147185) (by norm_num)
theorem B2094269 : Blo 1395517 2094269 := bbase (se 3 (by rfl) ⟨392675, by rfl⟩ : syracuseStep 2094269 = 785351) (by norm_num)
theorem B3142853 : Blo 1395517 3142853 := bbase (se 4 (by rfl) ⟨294642, by rfl⟩ : syracuseStep 3142853 = 589285) (by norm_num)
theorem B1766605 : Blo 1395517 1766605 := bbase (se 3 (by rfl) ⟨331238, by rfl⟩ : syracuseStep 1766605 = 662477) (by norm_num)
theorem B2094293 : Blo 1395517 2094293 := bbase (se 7 (by rfl) ⟨24542, by rfl⟩ : syracuseStep 2094293 = 49085) (by norm_num)
theorem B1570009 : Blo 1395517 1570009 := bbase (se 2 (by rfl) ⟨588753, by rfl⟩ : syracuseStep 1570009 = 1177507) (by norm_num)
theorem B2356445 : Blo 1395517 2356445 := bbase (se 3 (by rfl) ⟨441833, by rfl⟩ : syracuseStep 2356445 = 883667) (by norm_num)
theorem B2094317 : Blo 1395517 2094317 := bbase (se 3 (by rfl) ⟨392684, by rfl⟩ : syracuseStep 2094317 = 785369) (by norm_num)
theorem B4715765 : Blo 1395517 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B1570045 : Blo 1395517 1570045 := bbase (se 3 (by rfl) ⟨294383, by rfl⟩ : syracuseStep 1570045 = 588767) (by norm_num)
theorem B2094341 : Blo 1395517 2094341 := bbase (se 4 (by rfl) ⟨196344, by rfl⟩ : syracuseStep 2094341 = 392689) (by norm_num)
theorem B3142925 : Blo 1395517 3142925 := bbase (se 3 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 3142925 = 1178597) (by norm_num)
theorem B2094365 : Blo 1395517 2094365 := bbase (se 3 (by rfl) ⟨392693, by rfl⟩ : syracuseStep 2094365 = 785387) (by norm_num)
theorem B1570081 : Blo 1395517 1570081 := bbase (se 2 (by rfl) ⟨588780, by rfl⟩ : syracuseStep 1570081 = 1177561) (by norm_num)
theorem B1766701 : Blo 1395517 1766701 := bbase (se 3 (by rfl) ⟨331256, by rfl⟩ : syracuseStep 1766701 = 662513) (by norm_num)
theorem B2094389 : Blo 1395517 2094389 := bbase (se 5 (by rfl) ⟨98174, by rfl⟩ : syracuseStep 2094389 = 196349) (by norm_num)
theorem B1570117 : Blo 1395517 1570117 := bbase (se 4 (by rfl) ⟨147198, by rfl⟩ : syracuseStep 1570117 = 294397) (by norm_num)
theorem B2094413 : Blo 1395517 2094413 := bbase (se 3 (by rfl) ⟨392702, by rfl⟩ : syracuseStep 2094413 = 785405) (by norm_num)
theorem B3142997 : Blo 1395517 3142997 := bbase (se 13 (by rfl) ⟨575, by rfl⟩ : syracuseStep 3142997 = 1151) (by norm_num)
theorem B2356573 : Blo 1395517 2356573 := bbase (se 3 (by rfl) ⟨441857, by rfl⟩ : syracuseStep 2356573 = 883715) (by norm_num)
theorem B1676641 : Blo 1395517 1676641 := bbase (se 2 (by rfl) ⟨628740, by rfl⟩ : syracuseStep 1676641 = 1257481) (by norm_num)
theorem B2094437 : Blo 1395517 2094437 := bbase (se 4 (by rfl) ⟨196353, by rfl⟩ : syracuseStep 2094437 = 392707) (by norm_num)
theorem B1570153 : Blo 1395517 1570153 := bbase (se 2 (by rfl) ⟨588807, by rfl⟩ : syracuseStep 1570153 = 1177615) (by norm_num)
theorem B1987949 : Blo 1395517 1987949 := bbase (se 3 (by rfl) ⟨372740, by rfl⟩ : syracuseStep 1987949 = 745481) (by norm_num)
theorem B3536237 : Blo 1395517 3536237 := bbase (se 3 (by rfl) ⟨663044, by rfl⟩ : syracuseStep 3536237 = 1326089) (by norm_num)
theorem B2094461 : Blo 1395517 2094461 := bbase (se 3 (by rfl) ⟨392711, by rfl⟩ : syracuseStep 2094461 = 785423) (by norm_num)
theorem B3356029 : Blo 1395517 3356029 := bbase (se 3 (by rfl) ⟨629255, by rfl⟩ : syracuseStep 3356029 = 1258511) (by norm_num)
theorem B2651525 : Blo 1395517 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B1570189 : Blo 1395517 1570189 := bbase (se 3 (by rfl) ⟨294410, by rfl⟩ : syracuseStep 1570189 = 588821) (by norm_num)
theorem B2094485 : Blo 1395517 2094485 := bbase (se 6 (by rfl) ⟨49089, by rfl⟩ : syracuseStep 2094485 = 98179) (by norm_num)
theorem B2831773 : Blo 1395517 2831773 := bbase (se 3 (by rfl) ⟨530957, by rfl⟩ : syracuseStep 2831773 = 1061915) (by norm_num)
theorem B3143069 : Blo 1395517 3143069 := bbase (se 3 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 3143069 = 1178651) (by norm_num)
theorem B2094509 : Blo 1395517 2094509 := bbase (se 3 (by rfl) ⟨392720, by rfl⟩ : syracuseStep 2094509 = 785441) (by norm_num)
theorem B1570225 : Blo 1395517 1570225 := bbase (se 2 (by rfl) ⟨588834, by rfl⟩ : syracuseStep 1570225 = 1177669) (by norm_num)
theorem B2356661 : Blo 1395517 2356661 := bbase (se 5 (by rfl) ⟨110468, by rfl⟩ : syracuseStep 2356661 = 220937) (by norm_num)
theorem B2094533 : Blo 1395517 2094533 := bbase (se 4 (by rfl) ⟨196362, by rfl⟩ : syracuseStep 2094533 = 392725) (by norm_num)
theorem B1570261 : Blo 1395517 1570261 := bbase (se 7 (by rfl) ⟨18401, by rfl⟩ : syracuseStep 1570261 = 36803) (by norm_num)
theorem B1766873 : Blo 1395517 1766873 := bbase (se 2 (by rfl) ⟨662577, by rfl⟩ : syracuseStep 1766873 = 1325155) (by norm_num)
theorem B2094557 : Blo 1395517 2094557 := bbase (se 3 (by rfl) ⟨392729, by rfl⟩ : syracuseStep 2094557 = 785459) (by norm_num)
theorem B3143141 : Blo 1395517 3143141 := bbase (se 4 (by rfl) ⟨294669, by rfl⟩ : syracuseStep 3143141 = 589339) (by norm_num)
theorem B2094581 : Blo 1395517 2094581 := bbase (se 5 (by rfl) ⟨98183, by rfl⟩ : syracuseStep 2094581 = 196367) (by norm_num)
theorem B1570297 : Blo 1395517 1570297 := bbase (se 2 (by rfl) ⟨588861, by rfl⟩ : syracuseStep 1570297 = 1177723) (by norm_num)
theorem B2094605 : Blo 1395517 2094605 := bbase (se 3 (by rfl) ⟨392738, by rfl⟩ : syracuseStep 2094605 = 785477) (by norm_num)
theorem B1766929 : Blo 1395517 1766929 := bbase (se 2 (by rfl) ⟨662598, by rfl⟩ : syracuseStep 1766929 = 1325197) (by norm_num)
theorem B1570333 : Blo 1395517 1570333 := bbase (se 3 (by rfl) ⟨294437, by rfl⟩ : syracuseStep 1570333 = 588875) (by norm_num)
theorem B2094629 : Blo 1395517 2094629 := bbase (se 4 (by rfl) ⟨196371, by rfl⟩ : syracuseStep 2094629 = 392743) (by norm_num)
theorem B3143213 : Blo 1395517 3143213 := bbase (se 3 (by rfl) ⟨589352, by rfl⟩ : syracuseStep 3143213 = 1178705) (by norm_num)
theorem B2356789 : Blo 1395517 2356789 := bbase (se 5 (by rfl) ⟨110474, by rfl⟩ : syracuseStep 2356789 = 220949) (by norm_num)
theorem B1676857 : Blo 1395517 1676857 := bbase (se 2 (by rfl) ⟨628821, by rfl⟩ : syracuseStep 1676857 = 1257643) (by norm_num)
theorem B2094653 : Blo 1395517 2094653 := bbase (se 3 (by rfl) ⟨392747, by rfl⟩ : syracuseStep 2094653 = 785495) (by norm_num)
theorem B1570369 : Blo 1395517 1570369 := bbase (se 2 (by rfl) ⟨588888, by rfl⟩ : syracuseStep 1570369 = 1177777) (by norm_num)
theorem B2094677 : Blo 1395517 2094677 := bbase (se 8 (by rfl) ⟨12273, by rfl⟩ : syracuseStep 2094677 = 24547) (by norm_num)
theorem B1570405 : Blo 1395517 1570405 := bbase (se 4 (by rfl) ⟨147225, by rfl⟩ : syracuseStep 1570405 = 294451) (by norm_num)
theorem B2094701 : Blo 1395517 2094701 := bbase (se 3 (by rfl) ⟨392756, by rfl⟩ : syracuseStep 2094701 = 785513) (by norm_num)
theorem B1767025 : Blo 1395517 1767025 := bbase (se 2 (by rfl) ⟨662634, by rfl⟩ : syracuseStep 1767025 = 1325269) (by norm_num)
theorem B3143285 : Blo 1395517 3143285 := bbase (se 5 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 3143285 = 294683) (by norm_num)
theorem B2094725 : Blo 1395517 2094725 := bbase (se 4 (by rfl) ⟨196380, by rfl⟩ : syracuseStep 2094725 = 392761) (by norm_num)
theorem B2389637 : Blo 1395517 2389637 := bbase (se 4 (by rfl) ⟨224028, by rfl⟩ : syracuseStep 2389637 = 448057) (by norm_num)
theorem B1570441 : Blo 1395517 1570441 := bbase (se 2 (by rfl) ⟨588915, by rfl⟩ : syracuseStep 1570441 = 1177831) (by norm_num)
theorem B2356877 : Blo 1395517 2356877 := bbase (se 3 (by rfl) ⟨441914, by rfl⟩ : syracuseStep 2356877 = 883829) (by norm_num)
theorem B2094749 : Blo 1395517 2094749 := bbase (se 3 (by rfl) ⟨392765, by rfl⟩ : syracuseStep 2094749 = 785531) (by norm_num)
theorem B1791653 : Blo 1395517 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B4716197 : Blo 1395517 4716197 := bbase (se 4 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 4716197 = 884287) (by norm_num)
theorem B1570477 : Blo 1395517 1570477 := bbase (se 3 (by rfl) ⟨294464, by rfl⟩ : syracuseStep 1570477 = 588929) (by norm_num)
theorem B2094773 : Blo 1395517 2094773 := bbase (se 5 (by rfl) ⟨98192, by rfl⟩ : syracuseStep 2094773 = 196385) (by norm_num)
theorem B11933365 : Blo 1395517 11933365 := bbase (se 5 (by rfl) ⟨559376, by rfl⟩ : syracuseStep 11933365 = 1118753) (by norm_num)
theorem B3143357 : Blo 1395517 3143357 := bbase (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) (by norm_num)
theorem B2422469 : Blo 1395517 2422469 := bbase (se 4 (by rfl) ⟨227106, by rfl⟩ : syracuseStep 2422469 = 454213) (by norm_num)
theorem B3536581 : Blo 1395517 3536581 := bbase (se 4 (by rfl) ⟨331554, by rfl⟩ : syracuseStep 3536581 = 663109) (by norm_num)
theorem B2094797 : Blo 1395517 2094797 := bbase (se 3 (by rfl) ⟨392774, by rfl⟩ : syracuseStep 2094797 = 785549) (by norm_num)
theorem B1570513 : Blo 1395517 1570513 := bbase (se 2 (by rfl) ⟨588942, by rfl⟩ : syracuseStep 1570513 = 1177885) (by norm_num)
theorem B1677025 : Blo 1395517 1677025 := bbase (se 2 (by rfl) ⟨628884, by rfl⟩ : syracuseStep 1677025 = 1257769) (by norm_num)
theorem B2094821 : Blo 1395517 2094821 := bbase (se 4 (by rfl) ⟨196389, by rfl⟩ : syracuseStep 2094821 = 392779) (by norm_num)
theorem B1570549 : Blo 1395517 1570549 := bbase (se 5 (by rfl) ⟨73619, by rfl⟩ : syracuseStep 1570549 = 147239) (by norm_num)
theorem B2094845 : Blo 1395517 2094845 := bbase (se 3 (by rfl) ⟨392783, by rfl⟩ : syracuseStep 2094845 = 785567) (by norm_num)
theorem B1414913 : Blo 1395517 1414913 := bbase (se 2 (by rfl) ⟨530592, by rfl⟩ : syracuseStep 1414913 = 1061185) (by norm_num)
theorem B3143429 : Blo 1395517 3143429 := bbase (se 4 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 3143429 = 589393) (by norm_num)
theorem B2357005 : Blo 1395517 2357005 := bbase (se 3 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 2357005 = 883877) (by norm_num)
theorem B2094869 : Blo 1395517 2094869 := bbase (se 6 (by rfl) ⟨49098, by rfl⟩ : syracuseStep 2094869 = 98197) (by norm_num)
theorem B1570585 : Blo 1395517 1570585 := bbase (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) (by norm_num)
theorem B1767197 : Blo 1395517 1767197 := bbase (se 3 (by rfl) ⟨331349, by rfl⟩ : syracuseStep 1767197 = 662699) (by norm_num)
theorem B3356453 : Blo 1395517 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B2094893 : Blo 1395517 2094893 := bbase (se 3 (by rfl) ⟨392792, by rfl⟩ : syracuseStep 2094893 = 785585) (by norm_num)
theorem B3536693 : Blo 1395517 3536693 := bbase (se 5 (by rfl) ⟨165782, by rfl⟩ : syracuseStep 3536693 = 331565) (by norm_num)
theorem B1570621 : Blo 1395517 1570621 := bbase (se 3 (by rfl) ⟨294491, by rfl⟩ : syracuseStep 1570621 = 588983) (by norm_num)
theorem B5658437 : Blo 1395517 5658437 := bbase (se 4 (by rfl) ⟨530478, by rfl⟩ : syracuseStep 5658437 = 1060957) (by norm_num)
theorem B2094917 : Blo 1395517 2094917 := bbase (se 4 (by rfl) ⟨196398, by rfl⟩ : syracuseStep 2094917 = 392797) (by norm_num)
theorem B3143501 : Blo 1395517 3143501 := bbase (se 3 (by rfl) ⟨589406, by rfl⟩ : syracuseStep 3143501 = 1178813) (by norm_num)
theorem B1767253 : Blo 1395517 1767253 := bbase (se 9 (by rfl) ⟨5177, by rfl⟩ : syracuseStep 1767253 = 10355) (by norm_num)
theorem B2094941 : Blo 1395517 2094941 := bbase (se 3 (by rfl) ⟨392801, by rfl⟩ : syracuseStep 2094941 = 785603) (by norm_num)
theorem B1570657 : Blo 1395517 1570657 := bbase (se 2 (by rfl) ⟨588996, by rfl⟩ : syracuseStep 1570657 = 1177993) (by norm_num)
theorem B2357093 : Blo 1395517 2357093 := bbase (se 4 (by rfl) ⟨220977, by rfl⟩ : syracuseStep 2357093 = 441955) (by norm_num)
theorem B5035877 : Blo 1395517 5035877 := bbase (se 4 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 5035877 = 944227) (by norm_num)
theorem B2094965 : Blo 1395517 2094965 := bbase (se 5 (by rfl) ⟨98201, by rfl⟩ : syracuseStep 2094965 = 196403) (by norm_num)
theorem B1570693 : Blo 1395517 1570693 := bbase (se 4 (by rfl) ⟨147252, by rfl⟩ : syracuseStep 1570693 = 294505) (by norm_num)
theorem B2094989 : Blo 1395517 2094989 := bbase (se 3 (by rfl) ⟨392810, by rfl⟩ : syracuseStep 2094989 = 785621) (by norm_num)
theorem B3143573 : Blo 1395517 3143573 := bbase (se 6 (by rfl) ⟨73677, by rfl⟩ : syracuseStep 3143573 = 147355) (by norm_num)
theorem B1701785 : Blo 1395517 1701785 := bbase (se 2 (by rfl) ⟨638169, by rfl⟩ : syracuseStep 1701785 = 1276339) (by norm_num)
theorem B2095013 : Blo 1395517 2095013 := bbase (se 4 (by rfl) ⟨196407, by rfl⟩ : syracuseStep 2095013 = 392815) (by norm_num)
theorem B1570729 : Blo 1395517 1570729 := bbase (se 2 (by rfl) ⟨589023, by rfl⟩ : syracuseStep 1570729 = 1178047) (by norm_num)
theorem B7067573 : Blo 1395517 7067573 := bbase (se 5 (by rfl) ⟨331292, by rfl⟩ : syracuseStep 7067573 = 662585) (by norm_num)
theorem B1767349 : Blo 1395517 1767349 := bbase (se 5 (by rfl) ⟨82844, by rfl⟩ : syracuseStep 1767349 = 165689) (by norm_num)
theorem B2095037 : Blo 1395517 2095037 := bbase (se 3 (by rfl) ⟨392819, by rfl⟩ : syracuseStep 2095037 = 785639) (by norm_num)
theorem B1570765 : Blo 1395517 1570765 := bbase (se 3 (by rfl) ⟨294518, by rfl⟩ : syracuseStep 1570765 = 589037) (by norm_num)
theorem B2095061 : Blo 1395517 2095061 := bbase (se 7 (by rfl) ⟨24551, by rfl⟩ : syracuseStep 2095061 = 49103) (by norm_num)
theorem B3143645 : Blo 1395517 3143645 := bbase (se 3 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 3143645 = 1178867) (by norm_num)
theorem B2357221 : Blo 1395517 2357221 := bbase (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) (by norm_num)
theorem B2095085 : Blo 1395517 2095085 := bbase (se 3 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 2095085 = 785657) (by norm_num)
theorem B1570801 : Blo 1395517 1570801 := bbase (se 2 (by rfl) ⟨589050, by rfl⟩ : syracuseStep 1570801 = 1178101) (by norm_num)
theorem B3536885 : Blo 1395517 3536885 := bbase (se 5 (by rfl) ⟨165791, by rfl⟩ : syracuseStep 3536885 = 331583) (by norm_num)
theorem B2095109 : Blo 1395517 2095109 := bbase (se 4 (by rfl) ⟨196416, by rfl⟩ : syracuseStep 2095109 = 392833) (by norm_num)
theorem B1570837 : Blo 1395517 1570837 := bbase (se 6 (by rfl) ⟨36816, by rfl⟩ : syracuseStep 1570837 = 73633) (by norm_num)
theorem B3774485 : Blo 1395517 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B2095133 : Blo 1395517 2095133 := bbase (se 3 (by rfl) ⟨392837, by rfl⟩ : syracuseStep 2095133 = 785675) (by norm_num)
theorem B3143717 : Blo 1395517 3143717 := bbase (se 4 (by rfl) ⟨294723, by rfl⟩ : syracuseStep 3143717 = 589447) (by norm_num)
theorem B2095157 : Blo 1395517 2095157 := bbase (se 5 (by rfl) ⟨98210, by rfl⟩ : syracuseStep 2095157 = 196421) (by norm_num)
theorem B1570873 : Blo 1395517 1570873 := bbase (se 2 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 1570873 = 1178155) (by norm_num)
theorem B2357309 : Blo 1395517 2357309 := bbase (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) (by norm_num)
theorem B3356741 : Blo 1395517 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B2095181 : Blo 1395517 2095181 := bbase (se 3 (by rfl) ⟨392846, by rfl⟩ : syracuseStep 2095181 = 785693) (by norm_num)
theorem B1570909 : Blo 1395517 1570909 := bbase (se 3 (by rfl) ⟨294545, by rfl⟩ : syracuseStep 1570909 = 589091) (by norm_num)
theorem B1767521 : Blo 1395517 1767521 := bbase (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) (by norm_num)
theorem B2095205 : Blo 1395517 2095205 := bbase (se 4 (by rfl) ⟨196425, by rfl⟩ : syracuseStep 2095205 = 392851) (by norm_num)
theorem B3143789 : Blo 1395517 3143789 := bbase (se 3 (by rfl) ⟨589460, by rfl⟩ : syracuseStep 3143789 = 1178921) (by norm_num)
theorem B2652277 : Blo 1395517 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B2095229 : Blo 1395517 2095229 := bbase (se 3 (by rfl) ⟨392855, by rfl⟩ : syracuseStep 2095229 = 785711) (by norm_num)
theorem B1570945 : Blo 1395517 1570945 := bbase (se 2 (by rfl) ⟨589104, by rfl⟩ : syracuseStep 1570945 = 1178209) (by norm_num)
theorem B2095253 : Blo 1395517 2095253 := bbase (se 6 (by rfl) ⟨49107, by rfl⟩ : syracuseStep 2095253 = 98215) (by norm_num)
theorem B1767577 : Blo 1395517 1767577 := bbase (se 2 (by rfl) ⟨662841, by rfl⟩ : syracuseStep 1767577 = 1325683) (by norm_num)
theorem B1570981 : Blo 1395517 1570981 := bbase (se 4 (by rfl) ⟨147279, by rfl⟩ : syracuseStep 1570981 = 294559) (by norm_num)
theorem B2095277 : Blo 1395517 2095277 := bbase (se 3 (by rfl) ⟨392864, by rfl⟩ : syracuseStep 2095277 = 785729) (by norm_num)
theorem B3143861 : Blo 1395517 3143861 := bbase (se 5 (by rfl) ⟨147368, by rfl⟩ : syracuseStep 3143861 = 294737) (by norm_num)
theorem B2357437 : Blo 1395517 2357437 := bbase (se 3 (by rfl) ⟨442019, by rfl⟩ : syracuseStep 2357437 = 884039) (by norm_num)
theorem B2095301 : Blo 1395517 2095301 := bbase (se 4 (by rfl) ⟨196434, by rfl⟩ : syracuseStep 2095301 = 392869) (by norm_num)
theorem B1571017 : Blo 1395517 1571017 := bbase (se 2 (by rfl) ⟨589131, by rfl⟩ : syracuseStep 1571017 = 1178263) (by norm_num)
theorem B2095325 : Blo 1395517 2095325 := bbase (se 3 (by rfl) ⟨392873, by rfl⟩ : syracuseStep 2095325 = 785747) (by norm_num)
theorem B1571053 : Blo 1395517 1571053 := bbase (se 3 (by rfl) ⟨294572, by rfl⟩ : syracuseStep 1571053 = 589145) (by norm_num)
theorem B1677553 : Blo 1395517 1677553 := bbase (se 2 (by rfl) ⟨629082, by rfl⟩ : syracuseStep 1677553 = 1258165) (by norm_num)
theorem B13424885 : Blo 1395517 13424885 := bbase (se 5 (by rfl) ⟨629291, by rfl⟩ : syracuseStep 13424885 = 1258583) (by norm_num)
theorem B2095349 : Blo 1395517 2095349 := bbase (se 5 (by rfl) ⟨98219, by rfl⟩ : syracuseStep 2095349 = 196439) (by norm_num)
theorem B1767673 : Blo 1395517 1767673 := bbase (se 2 (by rfl) ⟨662877, by rfl⟩ : syracuseStep 1767673 = 1325755) (by norm_num)
theorem B3143933 : Blo 1395517 3143933 := bbase (se 3 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 3143933 = 1178975) (by norm_num)
theorem B2652421 : Blo 1395517 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B2095373 : Blo 1395517 2095373 := bbase (se 3 (by rfl) ⟨392882, by rfl⟩ : syracuseStep 2095373 = 785765) (by norm_num)
theorem B1571089 : Blo 1395517 1571089 := bbase (se 2 (by rfl) ⟨589158, by rfl⟩ : syracuseStep 1571089 = 1178317) (by norm_num)
theorem B2357525 : Blo 1395517 2357525 := bbase (se 6 (by rfl) ⟨55254, by rfl⟩ : syracuseStep 2357525 = 110509) (by norm_num)
theorem B2390293 : Blo 1395517 2390293 := bbase (se 6 (by rfl) ⟨56022, by rfl⟩ : syracuseStep 2390293 = 112045) (by norm_num)
theorem B2095397 : Blo 1395517 2095397 := bbase (se 4 (by rfl) ⟨196443, by rfl⟩ : syracuseStep 2095397 = 392887) (by norm_num)
theorem B3184949 : Blo 1395517 3184949 := bbase (se 5 (by rfl) ⟨149294, by rfl⟩ : syracuseStep 3184949 = 298589) (by norm_num)
theorem B1571125 : Blo 1395517 1571125 := bbase (se 5 (by rfl) ⟨73646, by rfl⟩ : syracuseStep 1571125 = 147293) (by norm_num)
theorem B2095421 : Blo 1395517 2095421 := bbase (se 3 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 2095421 = 785783) (by norm_num)
theorem B3144005 : Blo 1395517 3144005 := bbase (se 4 (by rfl) ⟨294750, by rfl⟩ : syracuseStep 3144005 = 589501) (by norm_num)
theorem B3537229 : Blo 1395517 3537229 := bbase (se 3 (by rfl) ⟨663230, by rfl⟩ : syracuseStep 3537229 = 1326461) (by norm_num)
theorem B2095445 : Blo 1395517 2095445 := bbase (se 10 (by rfl) ⟨3069, by rfl⟩ : syracuseStep 2095445 = 6139) (by norm_num)
theorem B1571161 : Blo 1395517 1571161 := bbase (se 2 (by rfl) ⟨589185, by rfl⟩ : syracuseStep 1571161 = 1178371) (by norm_num)
theorem B2095469 : Blo 1395517 2095469 := bbase (se 3 (by rfl) ⟨392900, by rfl⟩ : syracuseStep 2095469 = 785801) (by norm_num)
theorem B1571197 : Blo 1395517 1571197 := bbase (se 3 (by rfl) ⟨294599, by rfl⟩ : syracuseStep 1571197 = 589199) (by norm_num)
theorem B2095493 : Blo 1395517 2095493 := bbase (se 4 (by rfl) ⟨196452, by rfl⟩ : syracuseStep 2095493 = 392905) (by norm_num)
theorem B3144077 : Blo 1395517 3144077 := bbase (se 3 (by rfl) ⟨589514, by rfl⟩ : syracuseStep 3144077 = 1179029) (by norm_num)
theorem B2357653 : Blo 1395517 2357653 := bbase (se 6 (by rfl) ⟨55257, by rfl⟩ : syracuseStep 2357653 = 110515) (by norm_num)
theorem B2095517 : Blo 1395517 2095517 := bbase (se 3 (by rfl) ⟨392909, by rfl⟩ : syracuseStep 2095517 = 785819) (by norm_num)
theorem B1571233 : Blo 1395517 1571233 := bbase (se 2 (by rfl) ⟨589212, by rfl⟩ : syracuseStep 1571233 = 1178425) (by norm_num)
theorem B1767845 : Blo 1395517 1767845 := bbase (se 4 (by rfl) ⟨165735, by rfl⟩ : syracuseStep 1767845 = 331471) (by norm_num)
theorem B2652581 : Blo 1395517 2652581 := bbase (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) (by norm_num)
theorem B2095541 : Blo 1395517 2095541 := bbase (se 5 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 2095541 = 196457) (by norm_num)
theorem B3537341 : Blo 1395517 3537341 := bbase (se 3 (by rfl) ⟨663251, by rfl⟩ : syracuseStep 3537341 = 1326503) (by norm_num)
theorem B1571269 : Blo 1395517 1571269 := bbase (se 4 (by rfl) ⟨147306, by rfl⟩ : syracuseStep 1571269 = 294613) (by norm_num)
theorem B2095565 : Blo 1395517 2095565 := bbase (se 3 (by rfl) ⟨392918, by rfl⟩ : syracuseStep 2095565 = 785837) (by norm_num)
theorem B3144149 : Blo 1395517 3144149 := bbase (se 7 (by rfl) ⟨36845, by rfl⟩ : syracuseStep 3144149 = 73691) (by norm_num)
theorem B1767901 : Blo 1395517 1767901 := bbase (se 3 (by rfl) ⟨331481, by rfl⟩ : syracuseStep 1767901 = 662963) (by norm_num)
theorem B2095589 : Blo 1395517 2095589 := bbase (se 4 (by rfl) ⟨196461, by rfl⟩ : syracuseStep 2095589 = 392923) (by norm_num)
theorem B1571305 : Blo 1395517 1571305 := bbase (se 2 (by rfl) ⟨589239, by rfl⟩ : syracuseStep 1571305 = 1178479) (by norm_num)
theorem B2357741 : Blo 1395517 2357741 := bbase (se 3 (by rfl) ⟨442076, by rfl⟩ : syracuseStep 2357741 = 884153) (by norm_num)
theorem B2095613 : Blo 1395517 2095613 := bbase (se 3 (by rfl) ⟨392927, by rfl⟩ : syracuseStep 2095613 = 785855) (by norm_num)
theorem B1571341 : Blo 1395517 1571341 := bbase (se 3 (by rfl) ⟨294626, by rfl⟩ : syracuseStep 1571341 = 589253) (by norm_num)
theorem B2095637 : Blo 1395517 2095637 := bbase (se 6 (by rfl) ⟨49116, by rfl⟩ : syracuseStep 2095637 = 98233) (by norm_num)
theorem B3144221 : Blo 1395517 3144221 := bbase (se 3 (by rfl) ⟨589541, by rfl⟩ : syracuseStep 3144221 = 1179083) (by norm_num)
theorem B2095661 : Blo 1395517 2095661 := bbase (se 3 (by rfl) ⟨392936, by rfl⟩ : syracuseStep 2095661 = 785873) (by norm_num)
theorem B1571377 : Blo 1395517 1571377 := bbase (se 2 (by rfl) ⟨589266, by rfl⟩ : syracuseStep 1571377 = 1178533) (by norm_num)
theorem B2652725 : Blo 1395517 2652725 := bbase (se 5 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 2652725 = 248693) (by norm_num)
theorem B1767997 : Blo 1395517 1767997 := bbase (se 3 (by rfl) ⟨331499, by rfl⟩ : syracuseStep 1767997 = 662999) (by norm_num)
theorem B2095685 : Blo 1395517 2095685 := bbase (se 4 (by rfl) ⟨196470, by rfl⟩ : syracuseStep 2095685 = 392941) (by norm_num)
theorem B2832965 : Blo 1395517 2832965 := bbase (se 4 (by rfl) ⟨265590, by rfl⟩ : syracuseStep 2832965 = 531181) (by norm_num)
theorem B1571413 : Blo 1395517 1571413 := bbase (se 8 (by rfl) ⟨9207, by rfl⟩ : syracuseStep 1571413 = 18415) (by norm_num)
theorem B2095709 : Blo 1395517 2095709 := bbase (se 3 (by rfl) ⟨392945, by rfl⟩ : syracuseStep 2095709 = 785891) (by norm_num)
theorem B3144293 : Blo 1395517 3144293 := bbase (se 4 (by rfl) ⟨294777, by rfl⟩ : syracuseStep 3144293 = 589555) (by norm_num)
theorem B2357869 : Blo 1395517 2357869 := bbase (se 3 (by rfl) ⟨442100, by rfl⟩ : syracuseStep 2357869 = 884201) (by norm_num)
theorem B2095733 : Blo 1395517 2095733 := bbase (se 5 (by rfl) ⟨98237, by rfl⟩ : syracuseStep 2095733 = 196475) (by norm_num)
theorem B1571449 : Blo 1395517 1571449 := bbase (se 2 (by rfl) ⟨589293, by rfl⟩ : syracuseStep 1571449 = 1178587) (by norm_num)
theorem B2095757 : Blo 1395517 2095757 := bbase (se 3 (by rfl) ⟨392954, by rfl⟩ : syracuseStep 2095757 = 785909) (by norm_num)
theorem B1571485 : Blo 1395517 1571485 := bbase (se 3 (by rfl) ⟨294653, by rfl⟩ : syracuseStep 1571485 = 589307) (by norm_num)
theorem B2095781 : Blo 1395517 2095781 := bbase (se 4 (by rfl) ⟨196479, by rfl⟩ : syracuseStep 2095781 = 392959) (by norm_num)
theorem B3144365 : Blo 1395517 3144365 := bbase (se 3 (by rfl) ⟨589568, by rfl⟩ : syracuseStep 3144365 = 1179137) (by norm_num)
theorem B2095805 : Blo 1395517 2095805 := bbase (se 3 (by rfl) ⟨392963, by rfl⟩ : syracuseStep 2095805 = 785927) (by norm_num)
theorem B1571521 : Blo 1395517 1571521 := bbase (se 2 (by rfl) ⟨589320, by rfl⟩ : syracuseStep 1571521 = 1178641) (by norm_num)
theorem B2357957 : Blo 1395517 2357957 := bbase (se 4 (by rfl) ⟨221058, by rfl⟩ : syracuseStep 2357957 = 442117) (by norm_num)
theorem B2095829 : Blo 1395517 2095829 := bbase (se 7 (by rfl) ⟨24560, by rfl⟩ : syracuseStep 2095829 = 49121) (by norm_num)
theorem B1571557 : Blo 1395517 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B1768169 : Blo 1395517 1768169 := bbase (se 2 (by rfl) ⟨663063, by rfl⟩ : syracuseStep 1768169 = 1326127) (by norm_num)
theorem B2095853 : Blo 1395517 2095853 := bbase (se 3 (by rfl) ⟨392972, by rfl⟩ : syracuseStep 2095853 = 785945) (by norm_num)
theorem B1989373 : Blo 1395517 1989373 := bbase (se 3 (by rfl) ⟨373007, by rfl⟩ : syracuseStep 1989373 = 746015) (by norm_num)
theorem B2095877 : Blo 1395517 2095877 := bbase (se 4 (by rfl) ⟨196488, by rfl⟩ : syracuseStep 2095877 = 392977) (by norm_num)
theorem B1571593 : Blo 1395517 1571593 := bbase (se 2 (by rfl) ⟨589347, by rfl⟩ : syracuseStep 1571593 = 1178695) (by norm_num)
theorem B5298965 : Blo 1395517 5298965 := bbase (se 6 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 5298965 = 248389) (by norm_num)
theorem B2095901 : Blo 1395517 2095901 := bbase (se 3 (by rfl) ⟨392981, by rfl⟩ : syracuseStep 2095901 = 785963) (by norm_num)
theorem B1768225 : Blo 1395517 1768225 := bbase (se 2 (by rfl) ⟨663084, by rfl⟩ : syracuseStep 1768225 = 1326169) (by norm_num)
theorem B1571629 : Blo 1395517 1571629 := bbase (se 3 (by rfl) ⟨294680, by rfl⟩ : syracuseStep 1571629 = 589361) (by norm_num)
theorem B3824437 : Blo 1395517 3824437 := bbase (se 5 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 3824437 = 358541) (by norm_num)
theorem B2095925 : Blo 1395517 2095925 := bbase (se 5 (by rfl) ⟨98246, by rfl⟩ : syracuseStep 2095925 = 196493) (by norm_num)
theorem B2358085 : Blo 1395517 2358085 := bbase (se 4 (by rfl) ⟨221070, by rfl⟩ : syracuseStep 2358085 = 442141) (by norm_num)
theorem B2095949 : Blo 1395517 2095949 := bbase (se 3 (by rfl) ⟨392990, by rfl⟩ : syracuseStep 2095949 = 785981) (by norm_num)
theorem B1571665 : Blo 1395517 1571665 := bbase (se 2 (by rfl) ⟨589374, by rfl⟩ : syracuseStep 1571665 = 1178749) (by norm_num)
theorem B2653013 : Blo 1395517 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B2095973 : Blo 1395517 2095973 := bbase (se 4 (by rfl) ⟨196497, by rfl⟩ : syracuseStep 2095973 = 392995) (by norm_num)
theorem B3824501 : Blo 1395517 3824501 := bbase (se 5 (by rfl) ⟨179273, by rfl⟩ : syracuseStep 3824501 = 358547) (by norm_num)
theorem B1571701 : Blo 1395517 1571701 := bbase (se 5 (by rfl) ⟨73673, by rfl⟩ : syracuseStep 1571701 = 147347) (by norm_num)
theorem B2095997 : Blo 1395517 2095997 := bbase (se 3 (by rfl) ⟨392999, by rfl⟩ : syracuseStep 2095997 = 785999) (by norm_num)
theorem B1768321 : Blo 1395517 1768321 := bbase (se 2 (by rfl) ⟨663120, by rfl⟩ : syracuseStep 1768321 = 1326241) (by norm_num)
theorem B2096021 : Blo 1395517 2096021 := bbase (se 6 (by rfl) ⟨49125, by rfl⟩ : syracuseStep 2096021 = 98251) (by norm_num)
theorem B1571737 : Blo 1395517 1571737 := bbase (se 2 (by rfl) ⟨589401, by rfl⟩ : syracuseStep 1571737 = 1178803) (by norm_num)
theorem B2358173 : Blo 1395517 2358173 := bbase (se 3 (by rfl) ⟨442157, by rfl⟩ : syracuseStep 2358173 = 884315) (by norm_num)
theorem B2096045 : Blo 1395517 2096045 := bbase (se 3 (by rfl) ⟨393008, by rfl⟩ : syracuseStep 2096045 = 786017) (by norm_num)
theorem B1571773 : Blo 1395517 1571773 := bbase (se 3 (by rfl) ⟨294707, by rfl⟩ : syracuseStep 1571773 = 589415) (by norm_num)
theorem B2096069 : Blo 1395517 2096069 := bbase (se 4 (by rfl) ⟨196506, by rfl⟩ : syracuseStep 2096069 = 393013) (by norm_num)
theorem B2980813 : Blo 1395517 2980813 := bbase (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) (by norm_num)
theorem B2096093 : Blo 1395517 2096093 := bbase (se 3 (by rfl) ⟨393017, by rfl⟩ : syracuseStep 2096093 = 786035) (by norm_num)
theorem B1571809 : Blo 1395517 1571809 := bbase (se 2 (by rfl) ⟨589428, by rfl⟩ : syracuseStep 1571809 = 1178857) (by norm_num)
theorem B6708197 : Blo 1395517 6708197 := bbase (se 4 (by rfl) ⟨628893, by rfl⟩ : syracuseStep 6708197 = 1257787) (by norm_num)
theorem B2096117 : Blo 1395517 2096117 := bbase (se 5 (by rfl) ⟨98255, by rfl⟩ : syracuseStep 2096117 = 196511) (by norm_num)
theorem B1571845 : Blo 1395517 1571845 := bbase (se 4 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 1571845 = 294721) (by norm_num)
theorem B2096141 : Blo 1395517 2096141 := bbase (se 3 (by rfl) ⟨393026, by rfl⟩ : syracuseStep 2096141 = 786053) (by norm_num)
theorem B2358301 : Blo 1395517 2358301 := bbase (se 3 (by rfl) ⟨442181, by rfl⟩ : syracuseStep 2358301 = 884363) (by norm_num)
theorem B2096165 : Blo 1395517 2096165 := bbase (se 4 (by rfl) ⟨196515, by rfl⟩ : syracuseStep 2096165 = 393031) (by norm_num)
theorem B1571881 : Blo 1395517 1571881 := bbase (se 2 (by rfl) ⟨589455, by rfl⟩ : syracuseStep 1571881 = 1178911) (by norm_num)
theorem B1768493 : Blo 1395517 1768493 := bbase (se 3 (by rfl) ⟨331592, by rfl⟩ : syracuseStep 1768493 = 663185) (by norm_num)
theorem B5299253 : Blo 1395517 5299253 := bbase (se 5 (by rfl) ⟨248402, by rfl⟩ : syracuseStep 5299253 = 496805) (by norm_num)
theorem B4471861 : Blo 1395517 4471861 := bbase (se 5 (by rfl) ⟨209618, by rfl⟩ : syracuseStep 4471861 = 419237) (by norm_num)
theorem B2096189 : Blo 1395517 2096189 := bbase (se 3 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 2096189 = 786071) (by norm_num)
theorem B1571917 : Blo 1395517 1571917 := bbase (se 3 (by rfl) ⟨294734, by rfl⟩ : syracuseStep 1571917 = 589469) (by norm_num)
theorem B2096213 : Blo 1395517 2096213 := bbase (se 8 (by rfl) ⟨12282, by rfl⟩ : syracuseStep 2096213 = 24565) (by norm_num)
theorem B1768549 : Blo 1395517 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B2096237 : Blo 1395517 2096237 := bbase (se 3 (by rfl) ⟨393044, by rfl⟩ : syracuseStep 2096237 = 786089) (by norm_num)
theorem B1571953 : Blo 1395517 1571953 := bbase (se 2 (by rfl) ⟨589482, by rfl⟩ : syracuseStep 1571953 = 1178965) (by norm_num)
theorem B2096261 : Blo 1395517 2096261 := bbase (se 4 (by rfl) ⟨196524, by rfl⟩ : syracuseStep 2096261 = 393049) (by norm_num)
theorem B1571989 : Blo 1395517 1571989 := bbase (se 6 (by rfl) ⟨36843, by rfl⟩ : syracuseStep 1571989 = 73687) (by norm_num)
theorem B1572025 : Blo 1395517 1572025 := bbase (se 2 (by rfl) ⟨589509, by rfl⟩ : syracuseStep 1572025 = 1179019) (by norm_num)
theorem B7068869 : Blo 1395517 7068869 := bbase (se 4 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 7068869 = 1325413) (by norm_num)
theorem B1768645 : Blo 1395517 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B1572061 : Blo 1395517 1572061 := bbase (se 3 (by rfl) ⟨294761, by rfl⟩ : syracuseStep 1572061 = 589523) (by norm_num)
theorem B1572097 : Blo 1395517 1572097 := bbase (se 2 (by rfl) ⟨589536, by rfl⟩ : syracuseStep 1572097 = 1179073) (by norm_num)
theorem B3398933 : Blo 1395517 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B7552277 : Blo 1395517 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B1572133 : Blo 1395517 1572133 := bbase (se 4 (by rfl) ⟨147387, by rfl⟩ : syracuseStep 1572133 = 294775) (by norm_num)
theorem B1678649 : Blo 1395517 1678649 := bbase (se 2 (by rfl) ⟨629493, by rfl⟩ : syracuseStep 1678649 = 1258987) (by norm_num)
theorem B1572169 : Blo 1395517 1572169 := bbase (se 2 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 1572169 = 1179127) (by norm_num)
theorem B2686285 : Blo 1395517 2686285 := bbase (se 3 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 2686285 = 1007357) (by norm_num)
theorem B1572205 : Blo 1395517 1572205 := bbase (se 3 (by rfl) ⟨294788, by rfl⟩ : syracuseStep 1572205 = 589577) (by norm_num)
theorem B3186109 : Blo 1395517 3186109 := bbase (se 3 (by rfl) ⟨597395, by rfl⟩ : syracuseStep 3186109 = 1194791) (by norm_num)
theorem B1490437 : Blo 1395517 1490437 := bbase (se 4 (by rfl) ⟨139728, by rfl⟩ : syracuseStep 1490437 = 279457) (by norm_num)
theorem B3776053 : Blo 1395517 3776053 := bbase (se 5 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 3776053 = 354005) (by norm_num)
theorem B1490509 : Blo 1395517 1490509 := bbase (se 3 (by rfl) ⟨279470, by rfl⟩ : syracuseStep 1490509 = 558941) (by norm_num)
theorem B11935349 : Blo 1395517 11935349 := bbase (se 5 (by rfl) ⟨559469, by rfl⟩ : syracuseStep 11935349 = 1118939) (by norm_num)
theorem B3399317 : Blo 1395517 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B4710149 : Blo 1395517 4710149 := bbase (se 4 (by rfl) ⟨441576, by rfl⟩ : syracuseStep 4710149 = 883153) (by norm_num)
theorem B6045461 : Blo 1395517 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B2981701 : Blo 1395517 2981701 := bbase (se 4 (by rfl) ⟨279534, by rfl⟩ : syracuseStep 2981701 = 559069) (by norm_num)
theorem B2514773 : Blo 1395517 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B2514845 : Blo 1395517 2514845 := bbase (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) (by norm_num)
theorem B1490881 : Blo 1395517 1490881 := bbase (se 2 (by rfl) ⟨559080, by rfl⟩ : syracuseStep 1490881 = 1118161) (by norm_num)
theorem B2236405 : Blo 1395517 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B1491107 : Blo 1395517 1491107 := bstep (se 1 (by rfl) ⟨1118330, by rfl⟩ : syracuseStep 1491107 = 2236661) B2236661
theorem B7954757 : Blo 1395517 7954757 := bstep (se 4 (by rfl) ⟨745758, by rfl⟩ : syracuseStep 7954757 = 1491517) B1491517
theorem B11936099 : Blo 1395517 11936099 := bstep (se 1 (by rfl) ⟨8952074, by rfl⟩ : syracuseStep 11936099 = 17904149) B17904149
theorem B19104113 : Blo 1395517 19104113 := bstep (se 2 (by rfl) ⟨7164042, by rfl⟩ : syracuseStep 19104113 = 14328085) B14328085
theorem B4710797 : Blo 1395517 4710797 := bstep (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) B1766549
theorem B4710851 : Blo 1395517 4710851 := bstep (se 1 (by rfl) ⟨3533138, by rfl⟩ : syracuseStep 4710851 = 7066277) B7066277
theorem B3400337 : Blo 1395517 3400337 := bstep (se 2 (by rfl) ⟨1275126, by rfl⟩ : syracuseStep 3400337 = 2550253) B2550253
theorem B4711121 : Blo 1395517 4711121 := bstep (se 2 (by rfl) ⟨1766670, by rfl⟩ : syracuseStep 4711121 = 3533341) B3533341
theorem B10609379 : Blo 1395517 10609379 := bstep (se 1 (by rfl) ⟨7957034, by rfl⟩ : syracuseStep 10609379 = 15914069) B15914069
theorem B4473731 : Blo 1395517 4473731 := bstep (se 1 (by rfl) ⟨3355298, by rfl⟩ : syracuseStep 4473731 = 6710597) B6710597
theorem B1491859 : Blo 1395517 1491859 := bstep (se 1 (by rfl) ⟨1118894, by rfl⟩ : syracuseStep 1491859 = 2237789) B2237789
theorem B5301197 : Blo 1395517 5301197 := bstep (se 3 (by rfl) ⟨993974, by rfl⟩ : syracuseStep 5301197 = 1987949) B1987949
theorem B4031441 : Blo 1395517 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B7955441 : Blo 1395517 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B7554161 : Blo 1395517 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1614979 : Blo 1395517 1614979 := bstep (se 1 (by rfl) ⟨1211234, by rfl⟩ : syracuseStep 1614979 = 2422469) B2422469
theorem B5964941 : Blo 1395517 5964941 := bstep (se 3 (by rfl) ⟨1118426, by rfl⟩ : syracuseStep 5964941 = 2236853) B2236853
theorem B1492115 : Blo 1395517 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B2237635 : Blo 1395517 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B4711661 : Blo 1395517 4711661 := bstep (se 3 (by rfl) ⟨883436, by rfl⟩ : syracuseStep 4711661 = 1766873) B1766873
theorem B2983171 : Blo 1395517 2983171 := bstep (se 1 (by rfl) ⟨2237378, by rfl⟩ : syracuseStep 2983171 = 4474757) B4474757
theorem B8946949 : Blo 1395517 8946949 := bstep (se 4 (by rfl) ⟨838776, by rfl⟩ : syracuseStep 8946949 = 1677553) B1677553
theorem B3974417 : Blo 1395517 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B4711715 : Blo 1395517 4711715 := bstep (se 1 (by rfl) ⟨3533786, by rfl⟩ : syracuseStep 4711715 = 7067573) B7067573
theorem B13600099 : Blo 1395517 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B4244849 : Blo 1395517 4244849 := bstep (se 2 (by rfl) ⟨1591818, by rfl⟩ : syracuseStep 4244849 = 3183637) B3183637
theorem B4244899 : Blo 1395517 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B12748229 : Blo 1395517 12748229 := bstep (se 4 (by rfl) ⟨1195146, by rfl⟩ : syracuseStep 12748229 = 2390293) B2390293
theorem B2123299 : Blo 1395517 2123299 := bstep (se 1 (by rfl) ⟨1592474, by rfl⟩ : syracuseStep 2123299 = 3184949) B3184949
theorem B4711985 : Blo 1395517 4711985 := bstep (se 2 (by rfl) ⟨1766994, by rfl⟩ : syracuseStep 4711985 = 3533989) B3533989
theorem B8488525 : Blo 1395517 8488525 := bstep (se 3 (by rfl) ⟨1591598, by rfl⟩ : syracuseStep 8488525 = 3183197) B3183197
theorem B15902405 : Blo 1395517 15902405 := bstep (se 4 (by rfl) ⟨1490850, by rfl⟩ : syracuseStep 15902405 = 2981701) B2981701
theorem B4777741 : Blo 1395517 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B7653133 : Blo 1395517 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B3581713 : Blo 1395517 3581713 := bstep (se 2 (by rfl) ⟨1343142, by rfl⟩ : syracuseStep 3581713 = 2686285) B2686285
theorem B4474705 : Blo 1395517 4474705 := bstep (se 2 (by rfl) ⟨1678014, by rfl⟩ : syracuseStep 4474705 = 3356029) B3356029
theorem B3532643 : Blo 1395517 3532643 := bstep (se 1 (by rfl) ⟨2649482, by rfl⟩ : syracuseStep 3532643 = 5298965) B5298965
theorem B2516849 : Blo 1395517 2516849 := bstep (se 2 (by rfl) ⟨943818, by rfl⟩ : syracuseStep 2516849 = 1887637) B1887637
theorem B7555043 : Blo 1395517 7555043 := bstep (se 1 (by rfl) ⟨5666282, by rfl⟩ : syracuseStep 7555043 = 11332565) B11332565
theorem B3532835 : Blo 1395517 3532835 := bstep (se 1 (by rfl) ⟨2649626, by rfl⟩ : syracuseStep 3532835 = 5299253) B5299253
theorem B4712525 : Blo 1395517 4712525 := bstep (se 3 (by rfl) ⟨883598, by rfl⟩ : syracuseStep 4712525 = 1767197) B1767197
theorem B4712579 : Blo 1395517 4712579 := bstep (se 1 (by rfl) ⟨3534434, by rfl⟩ : syracuseStep 4712579 = 7068869) B7068869
theorem B24176837 : Blo 1395517 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B15911153 : Blo 1395517 15911153 := bstep (se 2 (by rfl) ⟨5966682, by rfl⟩ : syracuseStep 15911153 = 11933365) B11933365
theorem B16132405 : Blo 1395517 16132405 := bstep (se 5 (by rfl) ⟨756206, by rfl⟩ : syracuseStep 16132405 = 1512413) B1512413
theorem B4712849 : Blo 1395517 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B7956899 : Blo 1395517 7956899 := bstep (se 1 (by rfl) ⟨5967674, by rfl⟩ : syracuseStep 7956899 = 11935349) B11935349
theorem B5966257 : Blo 1395517 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B6367693 : Blo 1395517 6367693 := bstep (se 3 (by rfl) ⟨1193942, by rfl⟩ : syracuseStep 6367693 = 2387885) B2387885
theorem B2984401 : Blo 1395517 2984401 := bstep (se 2 (by rfl) ⟨1119150, by rfl⟩ : syracuseStep 2984401 = 2238301) B2238301
theorem B3140081 : Blo 1395517 3140081 := bstep (se 2 (by rfl) ⟨1177530, by rfl⟩ : syracuseStep 3140081 = 2355061) B2355061
theorem B3140099 : Blo 1395517 3140099 := bstep (se 1 (by rfl) ⟨2355074, by rfl⟩ : syracuseStep 3140099 = 4710149) B4710149
theorem B3066499 : Blo 1395517 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B4033169 : Blo 1395517 4033169 := bstep (se 2 (by rfl) ⟨1512438, by rfl⟩ : syracuseStep 4033169 = 3024877) B3024877
theorem B7072433 : Blo 1395517 7072433 := bstep (se 2 (by rfl) ⟨2652162, by rfl⟩ : syracuseStep 7072433 = 5304325) B5304325
theorem B15092405 : Blo 1395517 15092405 := bstep (se 5 (by rfl) ⟨707456, by rfl⟩ : syracuseStep 15092405 = 1414913) B1414913
theorem B3975875 : Blo 1395517 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B3140369 : Blo 1395517 3140369 := bstep (se 2 (by rfl) ⟨1177638, by rfl⟩ : syracuseStep 3140369 = 2355277) B2355277
theorem B36285205 : Blo 1395517 36285205 := bstep (se 6 (by rfl) ⟨850434, by rfl⟩ : syracuseStep 36285205 = 1700869) B1700869
theorem B3140387 : Blo 1395517 3140387 := bstep (se 1 (by rfl) ⟨2355290, by rfl⟩ : syracuseStep 3140387 = 4710581) B4710581
theorem B1395523 : Blo 1395517 1395523 := bstep (se 1 (by rfl) ⟨1046642, by rfl⟩ : syracuseStep 1395523 = 2093285) B2093285
theorem B1395539 : Blo 1395517 1395539 := bstep (se 1 (by rfl) ⟨1046654, by rfl⟩ : syracuseStep 1395539 = 2093309) B2093309
theorem B1395555 : Blo 1395517 1395555 := bstep (se 1 (by rfl) ⟨1046666, by rfl⟩ : syracuseStep 1395555 = 2093333) B2093333
theorem B27200369 : Blo 1395517 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B1395571 : Blo 1395517 1395571 := bstep (se 1 (by rfl) ⟨1046678, by rfl⟩ : syracuseStep 1395571 = 2093357) B2093357
theorem B1395587 : Blo 1395517 1395587 := bstep (se 1 (by rfl) ⟨1046690, by rfl⟩ : syracuseStep 1395587 = 2093381) B2093381
theorem B1395603 : Blo 1395517 1395603 := bstep (se 1 (by rfl) ⟨1046702, by rfl⟩ : syracuseStep 1395603 = 2093405) B2093405
theorem B1395619 : Blo 1395517 1395619 := bstep (se 1 (by rfl) ⟨1046714, by rfl⟩ : syracuseStep 1395619 = 2093429) B2093429
theorem B4713389 : Blo 1395517 4713389 := bstep (se 3 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 4713389 = 1767521) B1767521
theorem B1395635 : Blo 1395517 1395635 := bstep (se 1 (by rfl) ⟨1046726, by rfl⟩ : syracuseStep 1395635 = 2093453) B2093453
theorem B1395651 : Blo 1395517 1395651 := bstep (se 1 (by rfl) ⟨1046738, by rfl⟩ : syracuseStep 1395651 = 2093477) B2093477
theorem B3533777 : Blo 1395517 3533777 := bstep (se 2 (by rfl) ⟨1325166, by rfl⟩ : syracuseStep 3533777 = 2650333) B2650333
theorem B1395667 : Blo 1395517 1395667 := bstep (se 1 (by rfl) ⟨1046750, by rfl⟩ : syracuseStep 1395667 = 2093501) B2093501
theorem B1395683 : Blo 1395517 1395683 := bstep (se 1 (by rfl) ⟨1046762, by rfl⟩ : syracuseStep 1395683 = 2093525) B2093525
theorem B3582947 : Blo 1395517 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B4713443 : Blo 1395517 4713443 := bstep (se 1 (by rfl) ⟨3535082, by rfl⟩ : syracuseStep 4713443 = 7070165) B7070165
theorem B2124785 : Blo 1395517 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B1395699 : Blo 1395517 1395699 := bstep (se 1 (by rfl) ⟨1046774, by rfl⟩ : syracuseStep 1395699 = 2093549) B2093549
theorem B1395715 : Blo 1395517 1395715 := bstep (se 1 (by rfl) ⟨1046786, by rfl⟩ : syracuseStep 1395715 = 2093573) B2093573
theorem B3533827 : Blo 1395517 3533827 := bstep (se 1 (by rfl) ⟨2650370, by rfl⟩ : syracuseStep 3533827 = 5300741) B5300741
theorem B1395731 : Blo 1395517 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B1395747 : Blo 1395517 1395747 := bstep (se 1 (by rfl) ⟨1046810, by rfl⟩ : syracuseStep 1395747 = 2093621) B2093621
theorem B3140657 : Blo 1395517 3140657 := bstep (se 2 (by rfl) ⟨1177746, by rfl⟩ : syracuseStep 3140657 = 2355493) B2355493
theorem B1395763 : Blo 1395517 1395763 := bstep (se 1 (by rfl) ⟨1046822, by rfl⟩ : syracuseStep 1395763 = 2093645) B2093645
theorem B2829379 : Blo 1395517 2829379 := bstep (se 1 (by rfl) ⟨2122034, by rfl⟩ : syracuseStep 2829379 = 4244069) B4244069
theorem B1395779 : Blo 1395517 1395779 := bstep (se 1 (by rfl) ⟨1046834, by rfl⟩ : syracuseStep 1395779 = 2093669) B2093669
theorem B3140675 : Blo 1395517 3140675 := bstep (se 1 (by rfl) ⟨2355506, by rfl⟩ : syracuseStep 3140675 = 4711013) B4711013
theorem B1395795 : Blo 1395517 1395795 := bstep (se 1 (by rfl) ⟨1046846, by rfl⟩ : syracuseStep 1395795 = 2093693) B2093693
theorem B1395811 : Blo 1395517 1395811 := bstep (se 1 (by rfl) ⟨1046858, by rfl⟩ : syracuseStep 1395811 = 2093717) B2093717
theorem B1395827 : Blo 1395517 1395827 := bstep (se 1 (by rfl) ⟨1046870, by rfl⟩ : syracuseStep 1395827 = 2093741) B2093741
theorem B1395843 : Blo 1395517 1395843 := bstep (se 1 (by rfl) ⟨1046882, by rfl⟩ : syracuseStep 1395843 = 2093765) B2093765
theorem B3533969 : Blo 1395517 3533969 := bstep (se 2 (by rfl) ⟨1325238, by rfl⟩ : syracuseStep 3533969 = 2650477) B2650477
theorem B1395859 : Blo 1395517 1395859 := bstep (se 1 (by rfl) ⟨1046894, by rfl⟩ : syracuseStep 1395859 = 2093789) B2093789
theorem B1395875 : Blo 1395517 1395875 := bstep (se 1 (by rfl) ⟨1046906, by rfl⟩ : syracuseStep 1395875 = 2093813) B2093813
theorem B5033123 : Blo 1395517 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B9071779 : Blo 1395517 9071779 := bstep (se 1 (by rfl) ⟨6803834, by rfl⟩ : syracuseStep 9071779 = 13607669) B13607669
theorem B1395891 : Blo 1395517 1395891 := bstep (se 1 (by rfl) ⟨1046918, by rfl⟩ : syracuseStep 1395891 = 2093837) B2093837
theorem B1395907 : Blo 1395517 1395907 := bstep (se 1 (by rfl) ⟨1046930, by rfl⟩ : syracuseStep 1395907 = 2093861) B2093861
theorem B13429957 : Blo 1395517 13429957 := bstep (se 4 (by rfl) ⟨1259058, by rfl⟩ : syracuseStep 13429957 = 2518117) B2518117
theorem B1395923 : Blo 1395517 1395923 := bstep (se 1 (by rfl) ⟨1046942, by rfl⟩ : syracuseStep 1395923 = 2093885) B2093885
theorem B1395939 : Blo 1395517 1395939 := bstep (se 1 (by rfl) ⟨1046954, by rfl⟩ : syracuseStep 1395939 = 2093909) B2093909
theorem B45321443 : Blo 1395517 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B4713713 : Blo 1395517 4713713 := bstep (se 2 (by rfl) ⟨1767642, by rfl⟩ : syracuseStep 4713713 = 3535285) B3535285
theorem B1395955 : Blo 1395517 1395955 := bstep (se 1 (by rfl) ⟨1046966, by rfl⟩ : syracuseStep 1395955 = 2093933) B2093933
theorem B1395971 : Blo 1395517 1395971 := bstep (se 1 (by rfl) ⟨1046978, by rfl⟩ : syracuseStep 1395971 = 2093957) B2093957
theorem B4304141 : Blo 1395517 4304141 := bstep (se 3 (by rfl) ⟨807026, by rfl⟩ : syracuseStep 4304141 = 1614053) B1614053
theorem B2649361 : Blo 1395517 2649361 := bstep (se 2 (by rfl) ⟨993510, by rfl⟩ : syracuseStep 2649361 = 1987021) B1987021
theorem B1395987 : Blo 1395517 1395987 := bstep (se 1 (by rfl) ⟨1046990, by rfl⟩ : syracuseStep 1395987 = 2093981) B2093981
theorem B1396003 : Blo 1395517 1396003 := bstep (se 1 (by rfl) ⟨1047002, by rfl⟩ : syracuseStep 1396003 = 2094005) B2094005
theorem B8064305 : Blo 1395517 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B1396019 : Blo 1395517 1396019 := bstep (se 1 (by rfl) ⟨1047014, by rfl⟩ : syracuseStep 1396019 = 2094029) B2094029
theorem B1396035 : Blo 1395517 1396035 := bstep (se 1 (by rfl) ⟨1047026, by rfl⟩ : syracuseStep 1396035 = 2094053) B2094053
theorem B3140945 : Blo 1395517 3140945 := bstep (se 2 (by rfl) ⟨1177854, by rfl⟩ : syracuseStep 3140945 = 2355709) B2355709
theorem B1396051 : Blo 1395517 1396051 := bstep (se 1 (by rfl) ⟨1047038, by rfl⟩ : syracuseStep 1396051 = 2094077) B2094077
theorem B3140963 : Blo 1395517 3140963 := bstep (se 1 (by rfl) ⟨2355722, by rfl⟩ : syracuseStep 3140963 = 4711445) B4711445
theorem B1396067 : Blo 1395517 1396067 := bstep (se 1 (by rfl) ⟨1047050, by rfl⟩ : syracuseStep 1396067 = 2094101) B2094101
theorem B1396083 : Blo 1395517 1396083 := bstep (se 1 (by rfl) ⟨1047062, by rfl⟩ : syracuseStep 1396083 = 2094125) B2094125
theorem B1396099 : Blo 1395517 1396099 := bstep (se 1 (by rfl) ⟨1047074, by rfl⟩ : syracuseStep 1396099 = 2094149) B2094149
theorem B4246915 : Blo 1395517 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B4779395 : Blo 1395517 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B9063821 : Blo 1395517 9063821 := bstep (se 3 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 9063821 = 3398933) B3398933
theorem B1396115 : Blo 1395517 1396115 := bstep (se 1 (by rfl) ⟨1047086, by rfl⟩ : syracuseStep 1396115 = 2094173) B2094173
theorem B1396131 : Blo 1395517 1396131 := bstep (se 1 (by rfl) ⟨1047098, by rfl⟩ : syracuseStep 1396131 = 2094197) B2094197
theorem B1396147 : Blo 1395517 1396147 := bstep (se 1 (by rfl) ⟨1047110, by rfl⟩ : syracuseStep 1396147 = 2094221) B2094221
theorem B1396163 : Blo 1395517 1396163 := bstep (se 1 (by rfl) ⟨1047122, by rfl⟩ : syracuseStep 1396163 = 2094245) B2094245
theorem B1396179 : Blo 1395517 1396179 := bstep (se 1 (by rfl) ⟨1047134, by rfl⟩ : syracuseStep 1396179 = 2094269) B2094269
theorem B1396195 : Blo 1395517 1396195 := bstep (se 1 (by rfl) ⟨1047146, by rfl⟩ : syracuseStep 1396195 = 2094293) B2094293
theorem B3976685 : Blo 1395517 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B4476397 : Blo 1395517 4476397 := bstep (se 3 (by rfl) ⟨839324, by rfl⟩ : syracuseStep 4476397 = 1678649) B1678649
theorem B1396211 : Blo 1395517 1396211 := bstep (se 1 (by rfl) ⟨1047158, by rfl⟩ : syracuseStep 1396211 = 2094317) B2094317
theorem B1396227 : Blo 1395517 1396227 := bstep (se 1 (by rfl) ⟨1047170, by rfl⟩ : syracuseStep 1396227 = 2094341) B2094341
theorem B1396243 : Blo 1395517 1396243 := bstep (se 1 (by rfl) ⟨1047182, by rfl⟩ : syracuseStep 1396243 = 2094365) B2094365
theorem B1396259 : Blo 1395517 1396259 := bstep (se 1 (by rfl) ⟨1047194, by rfl⟩ : syracuseStep 1396259 = 2094389) B2094389
theorem B1396275 : Blo 1395517 1396275 := bstep (se 1 (by rfl) ⟨1047206, by rfl⟩ : syracuseStep 1396275 = 2094413) B2094413
theorem B1396291 : Blo 1395517 1396291 := bstep (se 1 (by rfl) ⟨1047218, by rfl⟩ : syracuseStep 1396291 = 2094437) B2094437
theorem B1396307 : Blo 1395517 1396307 := bstep (se 1 (by rfl) ⟨1047230, by rfl⟩ : syracuseStep 1396307 = 2094461) B2094461
theorem B1396323 : Blo 1395517 1396323 := bstep (se 1 (by rfl) ⟨1047242, by rfl⟩ : syracuseStep 1396323 = 2094485) B2094485
theorem B3141233 : Blo 1395517 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B1396339 : Blo 1395517 1396339 := bstep (se 1 (by rfl) ⟨1047254, by rfl⟩ : syracuseStep 1396339 = 2094509) B2094509
theorem B3141251 : Blo 1395517 3141251 := bstep (se 1 (by rfl) ⟨2355938, by rfl⟩ : syracuseStep 3141251 = 4711877) B4711877
theorem B1396355 : Blo 1395517 1396355 := bstep (se 1 (by rfl) ⟨1047266, by rfl⟩ : syracuseStep 1396355 = 2094533) B2094533
theorem B1396371 : Blo 1395517 1396371 := bstep (se 1 (by rfl) ⟨1047278, by rfl⟩ : syracuseStep 1396371 = 2094557) B2094557
theorem B2649763 : Blo 1395517 2649763 := bstep (se 1 (by rfl) ⟨1987322, by rfl⟩ : syracuseStep 2649763 = 3974645) B3974645
theorem B1396387 : Blo 1395517 1396387 := bstep (se 1 (by rfl) ⟨1047290, by rfl⟩ : syracuseStep 1396387 = 2094581) B2094581
theorem B3976877 : Blo 1395517 3976877 := bstep (se 3 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 3976877 = 1491329) B1491329
theorem B1396403 : Blo 1395517 1396403 := bstep (se 1 (by rfl) ⟨1047302, by rfl⟩ : syracuseStep 1396403 = 2094605) B2094605
theorem B1396419 : Blo 1395517 1396419 := bstep (se 1 (by rfl) ⟨1047314, by rfl⟩ : syracuseStep 1396419 = 2094629) B2094629
theorem B2649809 : Blo 1395517 2649809 := bstep (se 2 (by rfl) ⟨993678, by rfl⟩ : syracuseStep 2649809 = 1987357) B1987357
theorem B1396435 : Blo 1395517 1396435 := bstep (se 1 (by rfl) ⟨1047326, by rfl⟩ : syracuseStep 1396435 = 2094653) B2094653
theorem B1396451 : Blo 1395517 1396451 := bstep (se 1 (by rfl) ⟨1047338, by rfl⟩ : syracuseStep 1396451 = 2094677) B2094677
theorem B5099249 : Blo 1395517 5099249 := bstep (se 2 (by rfl) ⟨1912218, by rfl⟩ : syracuseStep 5099249 = 3824437) B3824437
theorem B1396467 : Blo 1395517 1396467 := bstep (se 1 (by rfl) ⟨1047350, by rfl⟩ : syracuseStep 1396467 = 2094701) B2094701
theorem B1396483 : Blo 1395517 1396483 := bstep (se 1 (by rfl) ⟨1047362, by rfl⟩ : syracuseStep 1396483 = 2094725) B2094725
theorem B1593091 : Blo 1395517 1593091 := bstep (se 1 (by rfl) ⟨1194818, by rfl⟩ : syracuseStep 1593091 = 2389637) B2389637
theorem B4714253 : Blo 1395517 4714253 := bstep (se 3 (by rfl) ⟨883922, by rfl⟩ : syracuseStep 4714253 = 1767845) B1767845
theorem B1396499 : Blo 1395517 1396499 := bstep (se 1 (by rfl) ⟨1047374, by rfl⟩ : syracuseStep 1396499 = 2094749) B2094749
theorem B1396515 : Blo 1395517 1396515 := bstep (se 1 (by rfl) ⟨1047386, by rfl⟩ : syracuseStep 1396515 = 2094773) B2094773
theorem B5304113 : Blo 1395517 5304113 := bstep (se 2 (by rfl) ⟨1989042, by rfl⟩ : syracuseStep 5304113 = 3978085) B3978085
theorem B1396531 : Blo 1395517 1396531 := bstep (se 1 (by rfl) ⟨1047398, by rfl⟩ : syracuseStep 1396531 = 2094797) B2094797
theorem B1396547 : Blo 1395517 1396547 := bstep (se 1 (by rfl) ⟨1047410, by rfl⟩ : syracuseStep 1396547 = 2094821) B2094821
theorem B4714307 : Blo 1395517 4714307 := bstep (se 1 (by rfl) ⟨3535730, by rfl⟩ : syracuseStep 4714307 = 7071461) B7071461
theorem B1396563 : Blo 1395517 1396563 := bstep (se 1 (by rfl) ⟨1047422, by rfl⟩ : syracuseStep 1396563 = 2094845) B2094845
theorem B2355041 : Blo 1395517 2355041 := bstep (se 2 (by rfl) ⟨883140, by rfl⟩ : syracuseStep 2355041 = 1766281) B1766281
theorem B1396579 : Blo 1395517 1396579 := bstep (se 1 (by rfl) ⟨1047434, by rfl⟩ : syracuseStep 1396579 = 2094869) B2094869
theorem B1396595 : Blo 1395517 1396595 := bstep (se 1 (by rfl) ⟨1047446, by rfl⟩ : syracuseStep 1396595 = 2094893) B2094893
theorem B3772291 : Blo 1395517 3772291 := bstep (se 1 (by rfl) ⟨2829218, by rfl⟩ : syracuseStep 3772291 = 5658437) B5658437
theorem B4534147 : Blo 1395517 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B1396611 : Blo 1395517 1396611 := bstep (se 1 (by rfl) ⟨1047458, by rfl⟩ : syracuseStep 1396611 = 2094917) B2094917
theorem B3141521 : Blo 1395517 3141521 := bstep (se 2 (by rfl) ⟨1178070, by rfl⟩ : syracuseStep 3141521 = 2356141) B2356141
theorem B1396627 : Blo 1395517 1396627 := bstep (se 1 (by rfl) ⟨1047470, by rfl⟩ : syracuseStep 1396627 = 2094941) B2094941
theorem B3141539 : Blo 1395517 3141539 := bstep (se 1 (by rfl) ⟨2356154, by rfl⟩ : syracuseStep 3141539 = 4712309) B4712309
theorem B1396643 : Blo 1395517 1396643 := bstep (se 1 (by rfl) ⟨1047482, by rfl⟩ : syracuseStep 1396643 = 2094965) B2094965
theorem B1396659 : Blo 1395517 1396659 := bstep (se 1 (by rfl) ⟨1047494, by rfl⟩ : syracuseStep 1396659 = 2094989) B2094989
theorem B1396675 : Blo 1395517 1396675 := bstep (se 1 (by rfl) ⟨1047506, by rfl⟩ : syracuseStep 1396675 = 2095013) B2095013
theorem B1396691 : Blo 1395517 1396691 := bstep (se 1 (by rfl) ⟨1047518, by rfl⟩ : syracuseStep 1396691 = 2095037) B2095037
theorem B2355169 : Blo 1395517 2355169 := bstep (se 2 (by rfl) ⟨883188, by rfl⟩ : syracuseStep 2355169 = 1766377) B1766377
theorem B1396707 : Blo 1395517 1396707 := bstep (se 1 (by rfl) ⟨1047530, by rfl⟩ : syracuseStep 1396707 = 2095061) B2095061
theorem B2650097 : Blo 1395517 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B1396723 : Blo 1395517 1396723 := bstep (se 1 (by rfl) ⟨1047542, by rfl⟩ : syracuseStep 1396723 = 2095085) B2095085
theorem B2355203 : Blo 1395517 2355203 := bstep (se 1 (by rfl) ⟨1766402, by rfl⟩ : syracuseStep 2355203 = 3532805) B3532805
theorem B1396739 : Blo 1395517 1396739 := bstep (se 1 (by rfl) ⟨1047554, by rfl⟩ : syracuseStep 1396739 = 2095109) B2095109
theorem B1396755 : Blo 1395517 1396755 := bstep (se 1 (by rfl) ⟨1047566, by rfl⟩ : syracuseStep 1396755 = 2095133) B2095133
theorem B1396771 : Blo 1395517 1396771 := bstep (se 1 (by rfl) ⟨1047578, by rfl⟩ : syracuseStep 1396771 = 2095157) B2095157
theorem B1396787 : Blo 1395517 1396787 := bstep (se 1 (by rfl) ⟨1047590, by rfl⟩ : syracuseStep 1396787 = 2095181) B2095181
theorem B1396803 : Blo 1395517 1396803 := bstep (se 1 (by rfl) ⟨1047602, by rfl⟩ : syracuseStep 1396803 = 2095205) B2095205
theorem B4714577 : Blo 1395517 4714577 := bstep (se 2 (by rfl) ⟨1767966, by rfl⟩ : syracuseStep 4714577 = 3535933) B3535933
theorem B1396819 : Blo 1395517 1396819 := bstep (se 1 (by rfl) ⟨1047614, by rfl⟩ : syracuseStep 1396819 = 2095229) B2095229
theorem B1396835 : Blo 1395517 1396835 := bstep (se 1 (by rfl) ⟨1047626, by rfl⟩ : syracuseStep 1396835 = 2095253) B2095253
theorem B7073891 : Blo 1395517 7073891 := bstep (se 1 (by rfl) ⟨5305418, by rfl⟩ : syracuseStep 7073891 = 10610837) B10610837
theorem B3534961 : Blo 1395517 3534961 := bstep (se 2 (by rfl) ⟨1325610, by rfl⟩ : syracuseStep 3534961 = 2651221) B2651221
theorem B1396851 : Blo 1395517 1396851 := bstep (se 1 (by rfl) ⟨1047638, by rfl⟩ : syracuseStep 1396851 = 2095277) B2095277
theorem B2355331 : Blo 1395517 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B1396867 : Blo 1395517 1396867 := bstep (se 1 (by rfl) ⟨1047650, by rfl⟩ : syracuseStep 1396867 = 2095301) B2095301
theorem B1396883 : Blo 1395517 1396883 := bstep (se 1 (by rfl) ⟨1047662, by rfl⟩ : syracuseStep 1396883 = 2095325) B2095325
theorem B8949923 : Blo 1395517 8949923 := bstep (se 1 (by rfl) ⟨6712442, by rfl⟩ : syracuseStep 8949923 = 13424885) B13424885
theorem B1396899 : Blo 1395517 1396899 := bstep (se 1 (by rfl) ⟨1047674, by rfl⟩ : syracuseStep 1396899 = 2095349) B2095349
theorem B3141809 : Blo 1395517 3141809 := bstep (se 2 (by rfl) ⟨1178178, by rfl⟩ : syracuseStep 3141809 = 2356357) B2356357
theorem B1913009 : Blo 1395517 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B1396915 : Blo 1395517 1396915 := bstep (se 1 (by rfl) ⟨1047686, by rfl⟩ : syracuseStep 1396915 = 2095373) B2095373
theorem B3141827 : Blo 1395517 3141827 := bstep (se 1 (by rfl) ⟨2356370, by rfl⟩ : syracuseStep 3141827 = 4712741) B4712741
theorem B1396931 : Blo 1395517 1396931 := bstep (se 1 (by rfl) ⟨1047698, by rfl⟩ : syracuseStep 1396931 = 2095397) B2095397
theorem B1396947 : Blo 1395517 1396947 := bstep (se 1 (by rfl) ⟨1047710, by rfl⟩ : syracuseStep 1396947 = 2095421) B2095421
theorem B1396963 : Blo 1395517 1396963 := bstep (se 1 (by rfl) ⟨1047722, by rfl⟩ : syracuseStep 1396963 = 2095445) B2095445
theorem B2093297 : Blo 1395517 2093297 := bstep (se 2 (by rfl) ⟨784986, by rfl⟩ : syracuseStep 2093297 = 1569973) B1569973
theorem B1396979 : Blo 1395517 1396979 := bstep (se 1 (by rfl) ⟨1047734, by rfl⟩ : syracuseStep 1396979 = 2095469) B2095469
theorem B2093315 : Blo 1395517 2093315 := bstep (se 1 (by rfl) ⟨1569986, by rfl⟩ : syracuseStep 2093315 = 3139973) B3139973
theorem B1396995 : Blo 1395517 1396995 := bstep (se 1 (by rfl) ⟨1047746, by rfl⟩ : syracuseStep 1396995 = 2095493) B2095493
theorem B2355473 : Blo 1395517 2355473 := bstep (se 2 (by rfl) ⟨883302, by rfl⟩ : syracuseStep 2355473 = 1766605) B1766605
theorem B1397011 : Blo 1395517 1397011 := bstep (se 1 (by rfl) ⟨1047758, by rfl⟩ : syracuseStep 1397011 = 2095517) B2095517
theorem B2093345 : Blo 1395517 2093345 := bstep (se 2 (by rfl) ⟨785004, by rfl⟩ : syracuseStep 2093345 = 1570009) B1570009
theorem B1700131 : Blo 1395517 1700131 := bstep (se 1 (by rfl) ⟨1275098, by rfl⟩ : syracuseStep 1700131 = 2550197) B2550197
theorem B1397027 : Blo 1395517 1397027 := bstep (se 1 (by rfl) ⟨1047770, by rfl⟩ : syracuseStep 1397027 = 2095541) B2095541
theorem B2093363 : Blo 1395517 2093363 := bstep (se 1 (by rfl) ⟨1570022, by rfl⟩ : syracuseStep 2093363 = 3140045) B3140045
theorem B2388275 : Blo 1395517 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1397043 : Blo 1395517 1397043 := bstep (se 1 (by rfl) ⟨1047782, by rfl⟩ : syracuseStep 1397043 = 2095565) B2095565
theorem B1397059 : Blo 1395517 1397059 := bstep (se 1 (by rfl) ⟨1047794, by rfl⟩ : syracuseStep 1397059 = 2095589) B2095589
theorem B2093393 : Blo 1395517 2093393 := bstep (se 2 (by rfl) ⟨785022, by rfl⟩ : syracuseStep 2093393 = 1570045) B1570045
theorem B1397075 : Blo 1395517 1397075 := bstep (se 1 (by rfl) ⟨1047806, by rfl⟩ : syracuseStep 1397075 = 2095613) B2095613
theorem B2093411 : Blo 1395517 2093411 := bstep (se 1 (by rfl) ⟨1570058, by rfl⟩ : syracuseStep 2093411 = 3140117) B3140117
theorem B10744163 : Blo 1395517 10744163 := bstep (se 1 (by rfl) ⟨8058122, by rfl⟩ : syracuseStep 10744163 = 16116245) B16116245
theorem B1397091 : Blo 1395517 1397091 := bstep (se 1 (by rfl) ⟨1047818, by rfl⟩ : syracuseStep 1397091 = 2095637) B2095637
theorem B1397107 : Blo 1395517 1397107 := bstep (se 1 (by rfl) ⟨1047830, by rfl⟩ : syracuseStep 1397107 = 2095661) B2095661
theorem B2093441 : Blo 1395517 2093441 := bstep (se 2 (by rfl) ⟨785040, by rfl⟩ : syracuseStep 2093441 = 1570081) B1570081
theorem B3535235 : Blo 1395517 3535235 := bstep (se 1 (by rfl) ⟨2651426, by rfl⟩ : syracuseStep 3535235 = 5302853) B5302853
theorem B1397123 : Blo 1395517 1397123 := bstep (se 1 (by rfl) ⟨1047842, by rfl⟩ : syracuseStep 1397123 = 2095685) B2095685
theorem B1888643 : Blo 1395517 1888643 := bstep (se 1 (by rfl) ⟨1416482, by rfl⟩ : syracuseStep 1888643 = 2832965) B2832965
theorem B2355601 : Blo 1395517 2355601 := bstep (se 2 (by rfl) ⟨883350, by rfl⟩ : syracuseStep 2355601 = 1766701) B1766701
theorem B2093459 : Blo 1395517 2093459 := bstep (se 1 (by rfl) ⟨1570094, by rfl⟩ : syracuseStep 2093459 = 3140189) B3140189
theorem B1397139 : Blo 1395517 1397139 := bstep (se 1 (by rfl) ⟨1047854, by rfl⟩ : syracuseStep 1397139 = 2095709) B2095709
theorem B1397155 : Blo 1395517 1397155 := bstep (se 1 (by rfl) ⟨1047866, by rfl⟩ : syracuseStep 1397155 = 2095733) B2095733
theorem B2093489 : Blo 1395517 2093489 := bstep (se 2 (by rfl) ⟨785058, by rfl⟩ : syracuseStep 2093489 = 1570117) B1570117
theorem B2355635 : Blo 1395517 2355635 := bstep (se 1 (by rfl) ⟨1766726, by rfl⟩ : syracuseStep 2355635 = 3533453) B3533453
theorem B1397171 : Blo 1395517 1397171 := bstep (se 1 (by rfl) ⟨1047878, by rfl⟩ : syracuseStep 1397171 = 2095757) B2095757
theorem B2093507 : Blo 1395517 2093507 := bstep (se 1 (by rfl) ⟨1570130, by rfl⟩ : syracuseStep 2093507 = 3140261) B3140261
theorem B1397187 : Blo 1395517 1397187 := bstep (se 1 (by rfl) ⟨1047890, by rfl⟩ : syracuseStep 1397187 = 2095781) B2095781
theorem B19116485 : Blo 1395517 19116485 := bstep (se 4 (by rfl) ⟨1792170, by rfl⟩ : syracuseStep 19116485 = 3584341) B3584341
theorem B3142097 : Blo 1395517 3142097 := bstep (se 2 (by rfl) ⟨1178286, by rfl⟩ : syracuseStep 3142097 = 2356573) B2356573
theorem B1397203 : Blo 1395517 1397203 := bstep (se 1 (by rfl) ⟨1047902, by rfl⟩ : syracuseStep 1397203 = 2095805) B2095805
theorem B2093537 : Blo 1395517 2093537 := bstep (se 2 (by rfl) ⟨785076, by rfl⟩ : syracuseStep 2093537 = 1570153) B1570153
theorem B3142115 : Blo 1395517 3142115 := bstep (se 1 (by rfl) ⟨2356586, by rfl⟩ : syracuseStep 3142115 = 4713173) B4713173
theorem B1397219 : Blo 1395517 1397219 := bstep (se 1 (by rfl) ⟨1047914, by rfl⟩ : syracuseStep 1397219 = 2095829) B2095829
theorem B2093555 : Blo 1395517 2093555 := bstep (se 1 (by rfl) ⟨1570166, by rfl⟩ : syracuseStep 2093555 = 3140333) B3140333
theorem B1397235 : Blo 1395517 1397235 := bstep (se 1 (by rfl) ⟨1047926, by rfl⟩ : syracuseStep 1397235 = 2095853) B2095853
theorem B1397251 : Blo 1395517 1397251 := bstep (se 1 (by rfl) ⟨1047938, by rfl⟩ : syracuseStep 1397251 = 2095877) B2095877
theorem B2093585 : Blo 1395517 2093585 := bstep (se 2 (by rfl) ⟨785094, by rfl⟩ : syracuseStep 2093585 = 1570189) B1570189
theorem B1397267 : Blo 1395517 1397267 := bstep (se 1 (by rfl) ⟨1047950, by rfl⟩ : syracuseStep 1397267 = 2095901) B2095901
theorem B2093603 : Blo 1395517 2093603 := bstep (se 1 (by rfl) ⟨1570202, by rfl⟩ : syracuseStep 2093603 = 3140405) B3140405
theorem B1397283 : Blo 1395517 1397283 := bstep (se 1 (by rfl) ⟨1047962, by rfl⟩ : syracuseStep 1397283 = 2095925) B2095925
theorem B2355763 : Blo 1395517 2355763 := bstep (se 1 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 2355763 = 3533645) B3533645
theorem B1397299 : Blo 1395517 1397299 := bstep (se 1 (by rfl) ⟨1047974, by rfl⟩ : syracuseStep 1397299 = 2095949) B2095949
theorem B2093633 : Blo 1395517 2093633 := bstep (se 2 (by rfl) ⟨785112, by rfl⟩ : syracuseStep 2093633 = 1570225) B1570225
theorem B3535427 : Blo 1395517 3535427 := bstep (se 1 (by rfl) ⟨2651570, by rfl⟩ : syracuseStep 3535427 = 5303141) B5303141
theorem B1397315 : Blo 1395517 1397315 := bstep (se 1 (by rfl) ⟨1047986, by rfl⟩ : syracuseStep 1397315 = 2095973) B2095973
theorem B4248145 : Blo 1395517 4248145 := bstep (se 2 (by rfl) ⟨1593054, by rfl⟩ : syracuseStep 4248145 = 3186109) B3186109
theorem B2093651 : Blo 1395517 2093651 := bstep (se 1 (by rfl) ⟨1570238, by rfl⟩ : syracuseStep 2093651 = 3140477) B3140477
theorem B1397331 : Blo 1395517 1397331 := bstep (se 1 (by rfl) ⟨1047998, by rfl⟩ : syracuseStep 1397331 = 2095997) B2095997
theorem B1397347 : Blo 1395517 1397347 := bstep (se 1 (by rfl) ⟨1048010, by rfl⟩ : syracuseStep 1397347 = 2096021) B2096021
theorem B4715117 : Blo 1395517 4715117 := bstep (se 3 (by rfl) ⟨884084, by rfl⟩ : syracuseStep 4715117 = 1768169) B1768169
theorem B2093681 : Blo 1395517 2093681 := bstep (se 2 (by rfl) ⟨785130, by rfl⟩ : syracuseStep 2093681 = 1570261) B1570261
theorem B5739121 : Blo 1395517 5739121 := bstep (se 2 (by rfl) ⟨2152170, by rfl⟩ : syracuseStep 5739121 = 4304341) B4304341
theorem B1397363 : Blo 1395517 1397363 := bstep (se 1 (by rfl) ⟨1048022, by rfl⟩ : syracuseStep 1397363 = 2096045) B2096045
theorem B2093699 : Blo 1395517 2093699 := bstep (se 1 (by rfl) ⟨1570274, by rfl⟩ : syracuseStep 2093699 = 3140549) B3140549
theorem B1397379 : Blo 1395517 1397379 := bstep (se 1 (by rfl) ⟨1048034, by rfl⟩ : syracuseStep 1397379 = 2096069) B2096069
theorem B3977869 : Blo 1395517 3977869 := bstep (se 3 (by rfl) ⟨745850, by rfl⟩ : syracuseStep 3977869 = 1491701) B1491701
theorem B1397395 : Blo 1395517 1397395 := bstep (se 1 (by rfl) ⟨1048046, by rfl⟩ : syracuseStep 1397395 = 2096093) B2096093
theorem B2093729 : Blo 1395517 2093729 := bstep (se 2 (by rfl) ⟨785148, by rfl⟩ : syracuseStep 2093729 = 1570297) B1570297
theorem B4715171 : Blo 1395517 4715171 := bstep (se 1 (by rfl) ⟨3536378, by rfl⟩ : syracuseStep 4715171 = 7072757) B7072757
theorem B1397411 : Blo 1395517 1397411 := bstep (se 1 (by rfl) ⟨1048058, by rfl⟩ : syracuseStep 1397411 = 2096117) B2096117
theorem B1987249 : Blo 1395517 1987249 := bstep (se 2 (by rfl) ⟨745218, by rfl⟩ : syracuseStep 1987249 = 1490437) B1490437
theorem B2093747 : Blo 1395517 2093747 := bstep (se 1 (by rfl) ⟨1570310, by rfl⟩ : syracuseStep 2093747 = 3140621) B3140621
theorem B1397427 : Blo 1395517 1397427 := bstep (se 1 (by rfl) ⟨1048070, by rfl⟩ : syracuseStep 1397427 = 2096141) B2096141
theorem B2355905 : Blo 1395517 2355905 := bstep (se 2 (by rfl) ⟨883464, by rfl⟩ : syracuseStep 2355905 = 1766929) B1766929
theorem B2650819 : Blo 1395517 2650819 := bstep (se 1 (by rfl) ⟨1988114, by rfl⟩ : syracuseStep 2650819 = 3976229) B3976229
theorem B1397443 : Blo 1395517 1397443 := bstep (se 1 (by rfl) ⟨1048082, by rfl⟩ : syracuseStep 1397443 = 2096165) B2096165
theorem B2093777 : Blo 1395517 2093777 := bstep (se 2 (by rfl) ⟨785166, by rfl⟩ : syracuseStep 2093777 = 1570333) B1570333
theorem B1397459 : Blo 1395517 1397459 := bstep (se 1 (by rfl) ⟨1048094, by rfl⟩ : syracuseStep 1397459 = 2096189) B2096189
theorem B2093795 : Blo 1395517 2093795 := bstep (se 1 (by rfl) ⟨1570346, by rfl⟩ : syracuseStep 2093795 = 3140693) B3140693
theorem B1397475 : Blo 1395517 1397475 := bstep (se 1 (by rfl) ⟨1048106, by rfl⟩ : syracuseStep 1397475 = 2096213) B2096213
theorem B3142385 : Blo 1395517 3142385 := bstep (se 2 (by rfl) ⟨1178394, by rfl⟩ : syracuseStep 3142385 = 2356789) B2356789
theorem B5034737 : Blo 1395517 5034737 := bstep (se 2 (by rfl) ⟨1888026, by rfl⟩ : syracuseStep 5034737 = 3776053) B3776053
theorem B1397491 : Blo 1395517 1397491 := bstep (se 1 (by rfl) ⟨1048118, by rfl⟩ : syracuseStep 1397491 = 2096237) B2096237
theorem B2093825 : Blo 1395517 2093825 := bstep (se 2 (by rfl) ⟨785184, by rfl⟩ : syracuseStep 2093825 = 1570369) B1570369
theorem B3142403 : Blo 1395517 3142403 := bstep (se 1 (by rfl) ⟨2356802, by rfl⟩ : syracuseStep 3142403 = 4713605) B4713605
theorem B1397507 : Blo 1395517 1397507 := bstep (se 1 (by rfl) ⟨1048130, by rfl⟩ : syracuseStep 1397507 = 2096261) B2096261
theorem B1987345 : Blo 1395517 1987345 := bstep (se 2 (by rfl) ⟨745254, by rfl⟩ : syracuseStep 1987345 = 1490509) B1490509
theorem B2093843 : Blo 1395517 2093843 := bstep (se 1 (by rfl) ⟨1570382, by rfl⟩ : syracuseStep 2093843 = 3140765) B3140765
theorem B2093873 : Blo 1395517 2093873 := bstep (se 2 (by rfl) ⟨785202, by rfl⟩ : syracuseStep 2093873 = 1570405) B1570405
theorem B2356033 : Blo 1395517 2356033 := bstep (se 2 (by rfl) ⟨883512, by rfl⟩ : syracuseStep 2356033 = 1767025) B1767025
theorem B2093891 : Blo 1395517 2093891 := bstep (se 1 (by rfl) ⟨1570418, by rfl⟩ : syracuseStep 2093891 = 3140837) B3140837
theorem B2093921 : Blo 1395517 2093921 := bstep (se 2 (by rfl) ⟨785220, by rfl⟩ : syracuseStep 2093921 = 1570441) B1570441
theorem B2356067 : Blo 1395517 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B5034851 : Blo 1395517 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B6714211 : Blo 1395517 6714211 := bstep (se 1 (by rfl) ⟨5035658, by rfl⟩ : syracuseStep 6714211 = 10071317) B10071317
theorem B2093939 : Blo 1395517 2093939 := bstep (se 1 (by rfl) ⟨1570454, by rfl⟩ : syracuseStep 2093939 = 3140909) B3140909
theorem B6706061 : Blo 1395517 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B7074701 : Blo 1395517 7074701 := bstep (se 3 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 7074701 = 2653013) B2653013
theorem B2093969 : Blo 1395517 2093969 := bstep (se 2 (by rfl) ⟨785238, by rfl⟩ : syracuseStep 2093969 = 1570477) B1570477
theorem B2093987 : Blo 1395517 2093987 := bstep (se 1 (by rfl) ⟨1570490, by rfl⟩ : syracuseStep 2093987 = 3140981) B3140981
theorem B4715441 : Blo 1395517 4715441 := bstep (se 2 (by rfl) ⟨1768290, by rfl⟩ : syracuseStep 4715441 = 3536581) B3536581
theorem B2094017 : Blo 1395517 2094017 := bstep (se 2 (by rfl) ⟨785256, by rfl⟩ : syracuseStep 2094017 = 1570513) B1570513
theorem B2094035 : Blo 1395517 2094035 := bstep (se 1 (by rfl) ⟨1570526, by rfl⟩ : syracuseStep 2094035 = 3141053) B3141053
theorem B2356195 : Blo 1395517 2356195 := bstep (se 1 (by rfl) ⟨1767146, by rfl⟩ : syracuseStep 2356195 = 3534293) B3534293
theorem B2094065 : Blo 1395517 2094065 := bstep (se 2 (by rfl) ⟨785274, by rfl⟩ : syracuseStep 2094065 = 1570549) B1570549
theorem B1766387 : Blo 1395517 1766387 := bstep (se 1 (by rfl) ⟨1324790, by rfl⟩ : syracuseStep 1766387 = 2649581) B2649581
theorem B2094083 : Blo 1395517 2094083 := bstep (se 1 (by rfl) ⟨1570562, by rfl⟩ : syracuseStep 2094083 = 3141125) B3141125
theorem B4305923 : Blo 1395517 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B3142673 : Blo 1395517 3142673 := bstep (se 2 (by rfl) ⟨1178502, by rfl⟩ : syracuseStep 3142673 = 2357005) B2357005
theorem B2094113 : Blo 1395517 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B3142691 : Blo 1395517 3142691 := bstep (se 1 (by rfl) ⟨2357018, by rfl⟩ : syracuseStep 3142691 = 4714037) B4714037
theorem B2094131 : Blo 1395517 2094131 := bstep (se 1 (by rfl) ⟨1570598, by rfl⟩ : syracuseStep 2094131 = 3141197) B3141197
theorem B16978997 : Blo 1395517 16978997 := bstep (se 5 (by rfl) ⟨795890, by rfl⟩ : syracuseStep 16978997 = 1591781) B1591781
theorem B6706253 : Blo 1395517 6706253 := bstep (se 3 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 6706253 = 2514845) B2514845
theorem B2094161 : Blo 1395517 2094161 := bstep (se 2 (by rfl) ⟨785310, by rfl⟩ : syracuseStep 2094161 = 1570621) B1570621
theorem B2266211 : Blo 1395517 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B2094179 : Blo 1395517 2094179 := bstep (se 1 (by rfl) ⟨1570634, by rfl⟩ : syracuseStep 2094179 = 3141269) B3141269
theorem B2356337 : Blo 1395517 2356337 := bstep (se 2 (by rfl) ⟨883626, by rfl⟩ : syracuseStep 2356337 = 1767253) B1767253
theorem B2094209 : Blo 1395517 2094209 := bstep (se 2 (by rfl) ⟨785328, by rfl⟩ : syracuseStep 2094209 = 1570657) B1570657
theorem B2651267 : Blo 1395517 2651267 := bstep (se 1 (by rfl) ⟨1988450, by rfl⟩ : syracuseStep 2651267 = 3976901) B3976901
theorem B2094227 : Blo 1395517 2094227 := bstep (se 1 (by rfl) ⟨1570670, by rfl⟩ : syracuseStep 2094227 = 3141341) B3141341
theorem B2094257 : Blo 1395517 2094257 := bstep (se 2 (by rfl) ⟨785346, by rfl⟩ : syracuseStep 2094257 = 1570693) B1570693
theorem B2094275 : Blo 1395517 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B2094305 : Blo 1395517 2094305 := bstep (se 2 (by rfl) ⟨785364, by rfl⟩ : syracuseStep 2094305 = 1570729) B1570729
theorem B5305571 : Blo 1395517 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B2356465 : Blo 1395517 2356465 := bstep (se 2 (by rfl) ⟨883674, by rfl⟩ : syracuseStep 2356465 = 1767349) B1767349
theorem B2094323 : Blo 1395517 2094323 := bstep (se 1 (by rfl) ⟨1570742, by rfl⟩ : syracuseStep 2094323 = 3141485) B3141485
theorem B1987841 : Blo 1395517 1987841 := bstep (se 2 (by rfl) ⟨745440, by rfl⟩ : syracuseStep 1987841 = 1490881) B1490881
theorem B2094353 : Blo 1395517 2094353 := bstep (se 2 (by rfl) ⟨785382, by rfl⟩ : syracuseStep 2094353 = 1570765) B1570765
theorem B2356499 : Blo 1395517 2356499 := bstep (se 1 (by rfl) ⟨1767374, by rfl⟩ : syracuseStep 2356499 = 3534749) B3534749
theorem B2094371 : Blo 1395517 2094371 := bstep (se 1 (by rfl) ⟨1570778, by rfl⟩ : syracuseStep 2094371 = 3141557) B3141557
theorem B3142961 : Blo 1395517 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B1570099 : Blo 1395517 1570099 := bstep (se 1 (by rfl) ⟨1177574, by rfl⟩ : syracuseStep 1570099 = 2355149) B2355149
theorem B2094401 : Blo 1395517 2094401 := bstep (se 2 (by rfl) ⟨785400, by rfl⟩ : syracuseStep 2094401 = 1570801) B1570801
theorem B3142979 : Blo 1395517 3142979 := bstep (se 1 (by rfl) ⟨2357234, by rfl⟩ : syracuseStep 3142979 = 4714469) B4714469
theorem B2094419 : Blo 1395517 2094419 := bstep (se 1 (by rfl) ⟨1570814, by rfl⟩ : syracuseStep 2094419 = 3141629) B3141629
theorem B2094449 : Blo 1395517 2094449 := bstep (se 2 (by rfl) ⟨785418, by rfl⟩ : syracuseStep 2094449 = 1570837) B1570837
theorem B2094467 : Blo 1395517 2094467 := bstep (se 1 (by rfl) ⟨1570850, by rfl⟩ : syracuseStep 2094467 = 3141701) B3141701
theorem B10065293 : Blo 1395517 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B2356627 : Blo 1395517 2356627 := bstep (se 1 (by rfl) ⟨1767470, by rfl⟩ : syracuseStep 2356627 = 3534941) B3534941
theorem B2094497 : Blo 1395517 2094497 := bstep (se 2 (by rfl) ⟨785436, by rfl⟩ : syracuseStep 2094497 = 1570873) B1570873
theorem B2651555 : Blo 1395517 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B5969315 : Blo 1395517 5969315 := bstep (se 1 (by rfl) ⟨4476986, by rfl⟩ : syracuseStep 5969315 = 8953973) B8953973
theorem B2094515 : Blo 1395517 2094515 := bstep (se 1 (by rfl) ⟨1570886, by rfl⟩ : syracuseStep 2094515 = 3141773) B3141773
theorem B1570243 : Blo 1395517 1570243 := bstep (se 1 (by rfl) ⟨1177682, by rfl⟩ : syracuseStep 1570243 = 2355365) B2355365
theorem B4715981 : Blo 1395517 4715981 := bstep (se 3 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 4715981 = 1768493) B1768493
theorem B2094545 : Blo 1395517 2094545 := bstep (se 2 (by rfl) ⟨785454, by rfl⟩ : syracuseStep 2094545 = 1570909) B1570909
theorem B2094563 : Blo 1395517 2094563 := bstep (se 1 (by rfl) ⟨1570922, by rfl⟩ : syracuseStep 2094563 = 3141845) B3141845
theorem B3536369 : Blo 1395517 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B2094593 : Blo 1395517 2094593 := bstep (se 2 (by rfl) ⟨785472, by rfl⟩ : syracuseStep 2094593 = 1570945) B1570945
theorem B4716035 : Blo 1395517 4716035 := bstep (se 1 (by rfl) ⟨3537026, by rfl⟩ : syracuseStep 4716035 = 7074053) B7074053
theorem B8951309 : Blo 1395517 8951309 := bstep (se 3 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 8951309 = 3356741) B3356741
theorem B2094611 : Blo 1395517 2094611 := bstep (se 1 (by rfl) ⟨1570958, by rfl⟩ : syracuseStep 2094611 = 3141917) B3141917
theorem B2356769 : Blo 1395517 2356769 := bstep (se 2 (by rfl) ⟨883788, by rfl⟩ : syracuseStep 2356769 = 1767577) B1767577
theorem B3536419 : Blo 1395517 3536419 := bstep (se 1 (by rfl) ⟨2652314, by rfl⟩ : syracuseStep 3536419 = 5304629) B5304629
theorem B2094641 : Blo 1395517 2094641 := bstep (se 2 (by rfl) ⟨785490, by rfl⟩ : syracuseStep 2094641 = 1570981) B1570981
theorem B2094659 : Blo 1395517 2094659 := bstep (se 1 (by rfl) ⟨1570994, by rfl⟩ : syracuseStep 2094659 = 3141989) B3141989
theorem B3143249 : Blo 1395517 3143249 := bstep (se 2 (by rfl) ⟨1178718, by rfl⟩ : syracuseStep 3143249 = 2357437) B2357437
theorem B1570387 : Blo 1395517 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B1791571 : Blo 1395517 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B2094689 : Blo 1395517 2094689 := bstep (se 2 (by rfl) ⟨785508, by rfl⟩ : syracuseStep 2094689 = 1571017) B1571017
theorem B3143267 : Blo 1395517 3143267 := bstep (se 1 (by rfl) ⟨2357450, by rfl⟩ : syracuseStep 3143267 = 4714901) B4714901
theorem B7067249 : Blo 1395517 7067249 := bstep (se 2 (by rfl) ⟨2650218, by rfl⟩ : syracuseStep 7067249 = 5300437) B5300437
theorem B2094707 : Blo 1395517 2094707 := bstep (se 1 (by rfl) ⟨1571030, by rfl⟩ : syracuseStep 2094707 = 3142061) B3142061
theorem B1414787 : Blo 1395517 1414787 := bstep (se 1 (by rfl) ⟨1061090, by rfl⟩ : syracuseStep 1414787 = 2122181) B2122181
theorem B2094737 : Blo 1395517 2094737 := bstep (se 2 (by rfl) ⟨785526, by rfl⟩ : syracuseStep 2094737 = 1571053) B1571053
theorem B2356897 : Blo 1395517 2356897 := bstep (se 2 (by rfl) ⟨883836, by rfl⟩ : syracuseStep 2356897 = 1767673) B1767673
theorem B5658275 : Blo 1395517 5658275 := bstep (se 1 (by rfl) ⟨4243706, by rfl⟩ : syracuseStep 5658275 = 8487413) B8487413
theorem B2094755 : Blo 1395517 2094755 := bstep (se 1 (by rfl) ⟨1571066, by rfl⟩ : syracuseStep 2094755 = 3142133) B3142133
theorem B3536561 : Blo 1395517 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B1767091 : Blo 1395517 1767091 := bstep (se 1 (by rfl) ⟨1325318, by rfl⟩ : syracuseStep 1767091 = 2650637) B2650637
theorem B2094785 : Blo 1395517 2094785 := bstep (se 2 (by rfl) ⟨785544, by rfl⟩ : syracuseStep 2094785 = 1571089) B1571089
theorem B2356931 : Blo 1395517 2356931 := bstep (se 1 (by rfl) ⟨1767698, by rfl⟩ : syracuseStep 2356931 = 3535397) B3535397
theorem B2094803 : Blo 1395517 2094803 := bstep (se 1 (by rfl) ⟨1571102, by rfl⟩ : syracuseStep 2094803 = 3142205) B3142205
theorem B1570531 : Blo 1395517 1570531 := bstep (se 1 (by rfl) ⟨1177898, by rfl⟩ : syracuseStep 1570531 = 2355797) B2355797
theorem B2094833 : Blo 1395517 2094833 := bstep (se 2 (by rfl) ⟨785562, by rfl⟩ : syracuseStep 2094833 = 1571125) B1571125
theorem B2094851 : Blo 1395517 2094851 := bstep (se 1 (by rfl) ⟨1571138, by rfl⟩ : syracuseStep 2094851 = 3142277) B3142277
theorem B4716305 : Blo 1395517 4716305 := bstep (se 2 (by rfl) ⟨1768614, by rfl⟩ : syracuseStep 4716305 = 3537229) B3537229
theorem B1767187 : Blo 1395517 1767187 := bstep (se 1 (by rfl) ⟨1325390, by rfl⟩ : syracuseStep 1767187 = 2650781) B2650781
theorem B2094881 : Blo 1395517 2094881 := bstep (se 2 (by rfl) ⟨785580, by rfl⟩ : syracuseStep 2094881 = 1571161) B1571161
theorem B2094899 : Blo 1395517 2094899 := bstep (se 1 (by rfl) ⟨1571174, by rfl⟩ : syracuseStep 2094899 = 3142349) B3142349
theorem B2357059 : Blo 1395517 2357059 := bstep (se 1 (by rfl) ⟨1767794, by rfl⟩ : syracuseStep 2357059 = 3535589) B3535589
theorem B2094929 : Blo 1395517 2094929 := bstep (se 2 (by rfl) ⟨785598, by rfl⟩ : syracuseStep 2094929 = 1571197) B1571197
theorem B2094947 : Blo 1395517 2094947 := bstep (se 1 (by rfl) ⟨1571210, by rfl⟩ : syracuseStep 2094947 = 3142421) B3142421
theorem B3143537 : Blo 1395517 3143537 := bstep (se 2 (by rfl) ⟨1178826, by rfl⟩ : syracuseStep 3143537 = 2357653) B2357653
theorem B1570675 : Blo 1395517 1570675 := bstep (se 1 (by rfl) ⟨1178006, by rfl⟩ : syracuseStep 1570675 = 2356013) B2356013
theorem B2094977 : Blo 1395517 2094977 := bstep (se 2 (by rfl) ⟨785616, by rfl⟩ : syracuseStep 2094977 = 1571233) B1571233
theorem B3143555 : Blo 1395517 3143555 := bstep (se 1 (by rfl) ⟨2357666, by rfl⟩ : syracuseStep 3143555 = 4715333) B4715333
theorem B9811853 : Blo 1395517 9811853 := bstep (se 3 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 9811853 = 3679445) B3679445
theorem B2094995 : Blo 1395517 2094995 := bstep (se 1 (by rfl) ⟨1571246, by rfl⟩ : syracuseStep 2094995 = 3142493) B3142493
theorem B2095025 : Blo 1395517 2095025 := bstep (se 2 (by rfl) ⟨785634, by rfl⟩ : syracuseStep 2095025 = 1571269) B1571269
theorem B2095043 : Blo 1395517 2095043 := bstep (se 1 (by rfl) ⟨1571282, by rfl⟩ : syracuseStep 2095043 = 3142565) B3142565
theorem B2357201 : Blo 1395517 2357201 := bstep (se 2 (by rfl) ⟨883950, by rfl⟩ : syracuseStep 2357201 = 1767901) B1767901
theorem B2095073 : Blo 1395517 2095073 := bstep (se 2 (by rfl) ⟨785652, by rfl⟩ : syracuseStep 2095073 = 1571305) B1571305
theorem B2095091 : Blo 1395517 2095091 := bstep (se 1 (by rfl) ⟨1571318, by rfl⟩ : syracuseStep 2095091 = 3142637) B3142637
theorem B1570819 : Blo 1395517 1570819 := bstep (se 1 (by rfl) ⟨1178114, by rfl⟩ : syracuseStep 1570819 = 2356229) B2356229
theorem B2095121 : Blo 1395517 2095121 := bstep (se 2 (by rfl) ⟨785670, by rfl⟩ : syracuseStep 2095121 = 1571341) B1571341
theorem B2095139 : Blo 1395517 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B2095169 : Blo 1395517 2095169 := bstep (se 2 (by rfl) ⟨785688, by rfl⟩ : syracuseStep 2095169 = 1571377) B1571377
theorem B2357329 : Blo 1395517 2357329 := bstep (se 2 (by rfl) ⟨883998, by rfl⟩ : syracuseStep 2357329 = 1767997) B1767997
theorem B1677395 : Blo 1395517 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B2095187 : Blo 1395517 2095187 := bstep (se 1 (by rfl) ⟨1571390, by rfl⟩ : syracuseStep 2095187 = 3142781) B3142781
theorem B1988707 : Blo 1395517 1988707 := bstep (se 1 (by rfl) ⟨1491530, by rfl⟩ : syracuseStep 1988707 = 2983061) B2983061
theorem B2095217 : Blo 1395517 2095217 := bstep (se 2 (by rfl) ⟨785706, by rfl⟩ : syracuseStep 2095217 = 1571413) B1571413
theorem B2357363 : Blo 1395517 2357363 := bstep (se 1 (by rfl) ⟨1768022, by rfl⟩ : syracuseStep 2357363 = 3536045) B3536045
theorem B2095235 : Blo 1395517 2095235 := bstep (se 1 (by rfl) ⟨1571426, by rfl⟩ : syracuseStep 2095235 = 3142853) B3142853
theorem B7952525 : Blo 1395517 7952525 := bstep (se 3 (by rfl) ⟨1491098, by rfl⟩ : syracuseStep 7952525 = 2982197) B2982197
theorem B3143825 : Blo 1395517 3143825 := bstep (se 2 (by rfl) ⟨1178934, by rfl⟩ : syracuseStep 3143825 = 2357869) B2357869
theorem B1570963 : Blo 1395517 1570963 := bstep (se 1 (by rfl) ⟨1178222, by rfl⟩ : syracuseStep 1570963 = 2356445) B2356445
theorem B2095265 : Blo 1395517 2095265 := bstep (se 2 (by rfl) ⟨785724, by rfl⟩ : syracuseStep 2095265 = 1571449) B1571449
theorem B3143843 : Blo 1395517 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B2095283 : Blo 1395517 2095283 := bstep (se 1 (by rfl) ⟨1571462, by rfl⟩ : syracuseStep 2095283 = 3142925) B3142925
theorem B1988803 : Blo 1395517 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B2095313 : Blo 1395517 2095313 := bstep (se 2 (by rfl) ⟨785742, by rfl⟩ : syracuseStep 2095313 = 1571485) B1571485
theorem B2095331 : Blo 1395517 2095331 := bstep (se 1 (by rfl) ⟨1571498, by rfl⟩ : syracuseStep 2095331 = 3142997) B3142997
theorem B2357491 : Blo 1395517 2357491 := bstep (se 1 (by rfl) ⟨1768118, by rfl⟩ : syracuseStep 2357491 = 3536237) B3536237
theorem B2095361 : Blo 1395517 2095361 := bstep (se 2 (by rfl) ⟨785760, by rfl⟩ : syracuseStep 2095361 = 1571521) B1571521
theorem B1767683 : Blo 1395517 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B15096077 : Blo 1395517 15096077 := bstep (se 3 (by rfl) ⟨2830514, by rfl⟩ : syracuseStep 15096077 = 5661029) B5661029
theorem B2095379 : Blo 1395517 2095379 := bstep (se 1 (by rfl) ⟨1571534, by rfl⟩ : syracuseStep 2095379 = 3143069) B3143069
theorem B1571107 : Blo 1395517 1571107 := bstep (se 1 (by rfl) ⟨1178330, by rfl⟩ : syracuseStep 1571107 = 2356661) B2356661
theorem B2095409 : Blo 1395517 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B2095427 : Blo 1395517 2095427 := bstep (se 1 (by rfl) ⟨1571570, by rfl⟩ : syracuseStep 2095427 = 3143141) B3143141
theorem B2652497 : Blo 1395517 2652497 := bstep (se 2 (by rfl) ⟨994686, by rfl⟩ : syracuseStep 2652497 = 1989373) B1989373
theorem B3979601 : Blo 1395517 3979601 := bstep (se 2 (by rfl) ⟨1492350, by rfl⟩ : syracuseStep 3979601 = 2984701) B2984701
theorem B2095457 : Blo 1395517 2095457 := bstep (se 2 (by rfl) ⟨785796, by rfl⟩ : syracuseStep 2095457 = 1571593) B1571593
theorem B2095475 : Blo 1395517 2095475 := bstep (se 1 (by rfl) ⟨1571606, by rfl⟩ : syracuseStep 2095475 = 3143213) B3143213
theorem B2357633 : Blo 1395517 2357633 := bstep (se 2 (by rfl) ⟨884112, by rfl⟩ : syracuseStep 2357633 = 1768225) B1768225
theorem B2095505 : Blo 1395517 2095505 := bstep (se 2 (by rfl) ⟨785814, by rfl⟩ : syracuseStep 2095505 = 1571629) B1571629
theorem B2095523 : Blo 1395517 2095523 := bstep (se 1 (by rfl) ⟨1571642, by rfl⟩ : syracuseStep 2095523 = 3143285) B3143285
theorem B3144113 : Blo 1395517 3144113 := bstep (se 2 (by rfl) ⟨1179042, by rfl⟩ : syracuseStep 3144113 = 2358085) B2358085
theorem B5036465 : Blo 1395517 5036465 := bstep (se 2 (by rfl) ⟨1888674, by rfl⟩ : syracuseStep 5036465 = 3777349) B3777349
theorem B1571251 : Blo 1395517 1571251 := bstep (se 1 (by rfl) ⟨1178438, by rfl⟩ : syracuseStep 1571251 = 2356877) B2356877
theorem B2095553 : Blo 1395517 2095553 := bstep (se 2 (by rfl) ⟨785832, by rfl⟩ : syracuseStep 2095553 = 1571665) B1571665
theorem B3144131 : Blo 1395517 3144131 := bstep (se 1 (by rfl) ⟨2358098, by rfl⟩ : syracuseStep 3144131 = 4716197) B4716197
theorem B2095571 : Blo 1395517 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B2095601 : Blo 1395517 2095601 := bstep (se 2 (by rfl) ⟨785850, by rfl⟩ : syracuseStep 2095601 = 1571701) B1571701
theorem B2357761 : Blo 1395517 2357761 := bstep (se 2 (by rfl) ⟨884160, by rfl⟩ : syracuseStep 2357761 = 1768321) B1768321
theorem B2095619 : Blo 1395517 2095619 := bstep (se 1 (by rfl) ⟨1571714, by rfl⟩ : syracuseStep 2095619 = 3143429) B3143429
theorem B2095649 : Blo 1395517 2095649 := bstep (se 2 (by rfl) ⟨785868, by rfl⟩ : syracuseStep 2095649 = 1571737) B1571737
theorem B2357795 : Blo 1395517 2357795 := bstep (se 1 (by rfl) ⟨1768346, by rfl⟩ : syracuseStep 2357795 = 3536693) B3536693
theorem B2095667 : Blo 1395517 2095667 := bstep (se 1 (by rfl) ⟨1571750, by rfl⟩ : syracuseStep 2095667 = 3143501) B3143501
theorem B1571395 : Blo 1395517 1571395 := bstep (se 1 (by rfl) ⟨1178546, by rfl⟩ : syracuseStep 1571395 = 2357093) B2357093
theorem B3357251 : Blo 1395517 3357251 := bstep (se 1 (by rfl) ⟨2517938, by rfl⟩ : syracuseStep 3357251 = 5035877) B5035877
theorem B2095697 : Blo 1395517 2095697 := bstep (se 2 (by rfl) ⟨785886, by rfl⟩ : syracuseStep 2095697 = 1571773) B1571773
theorem B2095715 : Blo 1395517 2095715 := bstep (se 1 (by rfl) ⟨1571786, by rfl⟩ : syracuseStep 2095715 = 3143573) B3143573
theorem B2095745 : Blo 1395517 2095745 := bstep (se 2 (by rfl) ⟨785904, by rfl⟩ : syracuseStep 2095745 = 1571809) B1571809
theorem B2095763 : Blo 1395517 2095763 := bstep (se 1 (by rfl) ⟨1571822, by rfl⟩ : syracuseStep 2095763 = 3143645) B3143645
theorem B3185315 : Blo 1395517 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B2357923 : Blo 1395517 2357923 := bstep (se 1 (by rfl) ⟨1768442, by rfl⟩ : syracuseStep 2357923 = 3536885) B3536885
theorem B2095793 : Blo 1395517 2095793 := bstep (se 2 (by rfl) ⟨785922, by rfl⟩ : syracuseStep 2095793 = 1571845) B1571845
theorem B1989299 : Blo 1395517 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B2095811 : Blo 1395517 2095811 := bstep (se 1 (by rfl) ⟨1571858, by rfl⟩ : syracuseStep 2095811 = 3143717) B3143717
theorem B3144401 : Blo 1395517 3144401 := bstep (se 2 (by rfl) ⟨1179150, by rfl⟩ : syracuseStep 3144401 = 2358301) B2358301
theorem B1571539 : Blo 1395517 1571539 := bstep (se 1 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 1571539 = 2357309) B2357309
theorem B2095841 : Blo 1395517 2095841 := bstep (se 2 (by rfl) ⟨785940, by rfl⟩ : syracuseStep 2095841 = 1571881) B1571881
theorem B5962481 : Blo 1395517 5962481 := bstep (se 2 (by rfl) ⟨2235930, by rfl⟩ : syracuseStep 5962481 = 4471861) B4471861
theorem B2095859 : Blo 1395517 2095859 := bstep (se 1 (by rfl) ⟨1571894, by rfl⟩ : syracuseStep 2095859 = 3143789) B3143789
theorem B2095889 : Blo 1395517 2095889 := bstep (se 2 (by rfl) ⟨785958, by rfl⟩ : syracuseStep 2095889 = 1571917) B1571917
theorem B5298979 : Blo 1395517 5298979 := bstep (se 1 (by rfl) ⟨3974234, by rfl⟩ : syracuseStep 5298979 = 7948469) B7948469
theorem B2095907 : Blo 1395517 2095907 := bstep (se 1 (by rfl) ⟨1571930, by rfl⟩ : syracuseStep 2095907 = 3143861) B3143861
theorem B2358065 : Blo 1395517 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B2095937 : Blo 1395517 2095937 := bstep (se 2 (by rfl) ⟨785976, by rfl⟩ : syracuseStep 2095937 = 1571953) B1571953
theorem B2095955 : Blo 1395517 2095955 := bstep (se 1 (by rfl) ⟨1571966, by rfl⟩ : syracuseStep 2095955 = 3143933) B3143933
theorem B290437973 : Blo 1395517 290437973 := bstep (se 9 (by rfl) ⟨850892, by rfl⟩ : syracuseStep 290437973 = 1701785) B1701785
theorem B1571683 : Blo 1395517 1571683 := bstep (se 1 (by rfl) ⟨1178762, by rfl⟩ : syracuseStep 1571683 = 2357525) B2357525
theorem B2095985 : Blo 1395517 2095985 := bstep (se 2 (by rfl) ⟨785994, by rfl⟩ : syracuseStep 2095985 = 1571989) B1571989
theorem B2096003 : Blo 1395517 2096003 := bstep (se 1 (by rfl) ⟨1572002, by rfl⟩ : syracuseStep 2096003 = 3144005) B3144005
theorem B2096033 : Blo 1395517 2096033 := bstep (se 2 (by rfl) ⟨786012, by rfl⟩ : syracuseStep 2096033 = 1572025) B1572025
theorem B2358193 : Blo 1395517 2358193 := bstep (se 2 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 2358193 = 1768645) B1768645
theorem B2096051 : Blo 1395517 2096051 := bstep (se 1 (by rfl) ⟨1572038, by rfl⟩ : syracuseStep 2096051 = 3144077) B3144077
theorem B1768387 : Blo 1395517 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B2096081 : Blo 1395517 2096081 := bstep (se 2 (by rfl) ⟨786030, by rfl⟩ : syracuseStep 2096081 = 1572061) B1572061
theorem B2358227 : Blo 1395517 2358227 := bstep (se 1 (by rfl) ⟨1768670, by rfl⟩ : syracuseStep 2358227 = 3537341) B3537341
theorem B2096099 : Blo 1395517 2096099 := bstep (se 1 (by rfl) ⟨1572074, by rfl⟩ : syracuseStep 2096099 = 3144149) B3144149
theorem B1571827 : Blo 1395517 1571827 := bstep (se 1 (by rfl) ⟨1178870, by rfl⟩ : syracuseStep 1571827 = 2357741) B2357741
theorem B2096129 : Blo 1395517 2096129 := bstep (se 2 (by rfl) ⟨786048, by rfl⟩ : syracuseStep 2096129 = 1572097) B1572097
theorem B2096147 : Blo 1395517 2096147 := bstep (se 1 (by rfl) ⟨1572110, by rfl⟩ : syracuseStep 2096147 = 3144221) B3144221
theorem B7068707 : Blo 1395517 7068707 := bstep (se 1 (by rfl) ⟨5301530, by rfl⟩ : syracuseStep 7068707 = 10603061) B10603061
theorem B1768483 : Blo 1395517 1768483 := bstep (se 1 (by rfl) ⟨1326362, by rfl⟩ : syracuseStep 1768483 = 2652725) B2652725
theorem B2096177 : Blo 1395517 2096177 := bstep (se 2 (by rfl) ⟨786066, by rfl⟩ : syracuseStep 2096177 = 1572133) B1572133
theorem B2096195 : Blo 1395517 2096195 := bstep (se 1 (by rfl) ⟨1572146, by rfl⟩ : syracuseStep 2096195 = 3144293) B3144293
theorem B2096225 : Blo 1395517 2096225 := bstep (se 2 (by rfl) ⟨786084, by rfl⟩ : syracuseStep 2096225 = 1572169) B1572169
theorem B2096243 : Blo 1395517 2096243 := bstep (se 1 (by rfl) ⟨1572182, by rfl⟩ : syracuseStep 2096243 = 3144365) B3144365
theorem B2235521 : Blo 1395517 2235521 := bstep (se 2 (by rfl) ⟨838320, by rfl⟩ : syracuseStep 2235521 = 1676641) B1676641
theorem B1571971 : Blo 1395517 1571971 := bstep (se 1 (by rfl) ⟨1178978, by rfl⟩ : syracuseStep 1571971 = 2357957) B2357957
theorem B2096273 : Blo 1395517 2096273 := bstep (se 2 (by rfl) ⟨786102, by rfl⟩ : syracuseStep 2096273 = 1572205) B1572205
theorem B9321649 : Blo 1395517 9321649 := bstep (se 2 (by rfl) ⟨3495618, by rfl⟩ : syracuseStep 9321649 = 6991237) B6991237
theorem B3775697 : Blo 1395517 3775697 := bstep (se 2 (by rfl) ⟨1415886, by rfl⟩ : syracuseStep 3775697 = 2831773) B2831773
theorem B1572115 : Blo 1395517 1572115 := bstep (se 1 (by rfl) ⟨1179086, by rfl⟩ : syracuseStep 1572115 = 2358173) B2358173
theorem B4472131 : Blo 1395517 4472131 := bstep (se 1 (by rfl) ⟨3354098, by rfl⟩ : syracuseStep 4472131 = 6708197) B6708197
theorem B3022211 : Blo 1395517 3022211 := bstep (se 1 (by rfl) ⟨2266658, by rfl⟩ : syracuseStep 3022211 = 4533317) B4533317
theorem B15908237 : Blo 1395517 15908237 := bstep (se 3 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 15908237 = 5965589) B5965589
theorem B2235809 : Blo 1395517 2235809 := bstep (se 2 (by rfl) ⟨838428, by rfl⟩ : syracuseStep 2235809 = 1676857) B1676857
theorem B4709933 : Blo 1395517 4709933 := bstep (se 3 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 4709933 = 1766225) B1766225
theorem B4709987 : Blo 1395517 4709987 := bstep (se 1 (by rfl) ⟨3532490, by rfl⟩ : syracuseStep 4709987 = 7064981) B7064981
theorem B2236033 : Blo 1395517 2236033 := bstep (se 2 (by rfl) ⟨838512, by rfl⟩ : syracuseStep 2236033 = 1677025) B1677025
theorem B10198669 : Blo 1395517 10198669 := bstep (se 3 (by rfl) ⟨1912250, by rfl⟩ : syracuseStep 10198669 = 3824501) B3824501
theorem B7069517 : Blo 1395517 7069517 := bstep (se 3 (by rfl) ⟨1325534, by rfl⟩ : syracuseStep 7069517 = 2651069) B2651069
theorem B4030307 : Blo 1395517 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B4710257 : Blo 1395517 4710257 := bstep (se 2 (by rfl) ⟨1766346, by rfl⟩ : syracuseStep 4710257 = 3532693) B3532693
theorem B2981873 : Blo 1395517 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B45277325 : Blo 1395517 45277325 := bstep (se 3 (by rfl) ⟨8489498, by rfl⟩ : syracuseStep 45277325 = 16978997) B16978997
theorem B17883341 : Blo 1395517 17883341 := bstep (se 3 (by rfl) ⟨3353126, by rfl⟩ : syracuseStep 17883341 = 6706253) B6706253
theorem B4473053 : Blo 1395517 4473053 := bstep (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) B1677395
theorem B64471565 : Blo 1395517 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B7955009 : Blo 1395517 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B2687627 : Blo 1395517 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B5300909 : Blo 1395517 5300909 := bstep (se 3 (by rfl) ⟨993920, by rfl⟩ : syracuseStep 5300909 = 1987841) B1987841
theorem B7652161 : Blo 1395517 7652161 := bstep (se 2 (by rfl) ⟨2869560, by rfl⟩ : syracuseStep 7652161 = 5739121) B5739121
theorem B4088665 : Blo 1395517 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B6710195 : Blo 1395517 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B4711499 : Blo 1395517 4711499 := bstep (se 1 (by rfl) ⟨3533624, by rfl⟩ : syracuseStep 4711499 = 7067249) B7067249
theorem B7070813 : Blo 1395517 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B10601603 : Blo 1395517 10601603 := bstep (se 1 (by rfl) ⟨7951202, by rfl⟩ : syracuseStep 10601603 = 15902405) B15902405
theorem B4711769 : Blo 1395517 4711769 := bstep (se 2 (by rfl) ⟨1766913, by rfl⟩ : syracuseStep 4711769 = 3533827) B3533827
theorem B8496485 : Blo 1395517 8496485 := bstep (se 4 (by rfl) ⟨796545, by rfl⟩ : syracuseStep 8496485 = 1593091) B1593091
theorem B5301683 : Blo 1395517 5301683 := bstep (se 1 (by rfl) ⟨3976262, by rfl⟩ : syracuseStep 5301683 = 7952525) B7952525
theorem B2983513 : Blo 1395517 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B11929265 : Blo 1395517 11929265 := bstep (se 2 (by rfl) ⟨4473474, by rfl⟩ : syracuseStep 11929265 = 8946949) B8946949
theorem B3532481 : Blo 1395517 3532481 := bstep (se 2 (by rfl) ⟨1324680, by rfl⟩ : syracuseStep 3532481 = 2649361) B2649361
theorem B2238167 : Blo 1395517 2238167 := bstep (se 1 (by rfl) ⟨1678625, by rfl⟩ : syracuseStep 2238167 = 3357251) B3357251
theorem B2688779 : Blo 1395517 2688779 := bstep (se 1 (by rfl) ⟨2016584, by rfl⟩ : syracuseStep 2688779 = 4033169) B4033169
theorem B2123543 : Blo 1395517 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B10061603 : Blo 1395517 10061603 := bstep (se 1 (by rfl) ⟨7546202, by rfl⟩ : syracuseStep 10061603 = 15092405) B15092405
theorem B3974987 : Blo 1395517 3974987 := bstep (se 1 (by rfl) ⟨2981240, by rfl⟩ : syracuseStep 3974987 = 5962481) B5962481
theorem B5662553 : Blo 1395517 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B4712471 : Blo 1395517 4712471 := bstep (se 1 (by rfl) ⟨3534353, by rfl⟩ : syracuseStep 4712471 = 7068707) B7068707
theorem B2517131 : Blo 1395517 2517131 := bstep (se 1 (by rfl) ⟨1887848, by rfl⟩ : syracuseStep 2517131 = 3775697) B3775697
theorem B30214295 : Blo 1395517 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B5376203 : Blo 1395517 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B3533017 : Blo 1395517 3533017 := bstep (se 2 (by rfl) ⟨1324881, by rfl⟩ : syracuseStep 3533017 = 2649763) B2649763
theorem B11929949 : Blo 1395517 11929949 := bstep (se 3 (by rfl) ⟨2236865, by rfl⟩ : syracuseStep 11929949 = 4473731) B4473731
theorem B3139955 : Blo 1395517 3139955 := bstep (se 1 (by rfl) ⟨2354966, by rfl⟩ : syracuseStep 3139955 = 4709933) B4709933
theorem B3139991 : Blo 1395517 3139991 := bstep (se 1 (by rfl) ⟨2354993, by rfl⟩ : syracuseStep 3139991 = 4709987) B4709987
theorem B5966273 : Blo 1395517 5966273 := bstep (se 2 (by rfl) ⟨2237352, by rfl⟩ : syracuseStep 5966273 = 4474705) B4474705
theorem B4713011 : Blo 1395517 4713011 := bstep (se 1 (by rfl) ⟨3534758, by rfl⟩ : syracuseStep 4713011 = 7069517) B7069517
theorem B3140171 : Blo 1395517 3140171 := bstep (se 1 (by rfl) ⟨2355128, by rfl⟩ : syracuseStep 3140171 = 4710257) B4710257
theorem B20146781 : Blo 1395517 20146781 := bstep (se 3 (by rfl) ⟨3777521, by rfl⟩ : syracuseStep 20146781 = 7555043) B7555043
theorem B3140225 : Blo 1395517 3140225 := bstep (se 2 (by rfl) ⟨1177584, by rfl⟩ : syracuseStep 3140225 = 2355169) B2355169
theorem B5966615 : Blo 1395517 5966615 := bstep (se 1 (by rfl) ⟨4474961, by rfl⟩ : syracuseStep 5966615 = 8949923) B8949923
theorem B45910837 : Blo 1395517 45910837 := bstep (se 5 (by rfl) ⟨2152070, by rfl⟩ : syracuseStep 45910837 = 4304141) B4304141
theorem B4713281 : Blo 1395517 4713281 := bstep (se 2 (by rfl) ⟨1767480, by rfl⟩ : syracuseStep 4713281 = 3534961) B3534961
theorem B1395531 : Blo 1395517 1395531 := bstep (se 1 (by rfl) ⟨1046648, by rfl⟩ : syracuseStep 1395531 = 2093297) B2093297
theorem B1395543 : Blo 1395517 1395543 := bstep (se 1 (by rfl) ⟨1046657, by rfl⟩ : syracuseStep 1395543 = 2093315) B2093315
theorem B3140441 : Blo 1395517 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B11324261 : Blo 1395517 11324261 := bstep (se 4 (by rfl) ⟨1061649, by rfl⟩ : syracuseStep 11324261 = 2123299) B2123299
theorem B1395563 : Blo 1395517 1395563 := bstep (se 1 (by rfl) ⟨1046672, by rfl⟩ : syracuseStep 1395563 = 2093345) B2093345
theorem B1395575 : Blo 1395517 1395575 := bstep (se 1 (by rfl) ⟨1046681, by rfl⟩ : syracuseStep 1395575 = 2093363) B2093363
theorem B1592183 : Blo 1395517 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B5303171 : Blo 1395517 5303171 := bstep (se 1 (by rfl) ⟨3977378, by rfl⟩ : syracuseStep 5303171 = 7954757) B7954757
theorem B1395595 : Blo 1395517 1395595 := bstep (se 1 (by rfl) ⟨1046696, by rfl⟩ : syracuseStep 1395595 = 2093393) B2093393
theorem B1395607 : Blo 1395517 1395607 := bstep (se 1 (by rfl) ⟨1046705, by rfl⟩ : syracuseStep 1395607 = 2093411) B2093411
theorem B7162775 : Blo 1395517 7162775 := bstep (se 1 (by rfl) ⟨5372081, by rfl⟩ : syracuseStep 7162775 = 10744163) B10744163
theorem B7957399 : Blo 1395517 7957399 := bstep (se 1 (by rfl) ⟨5968049, by rfl⟩ : syracuseStep 7957399 = 11936099) B11936099
theorem B1395627 : Blo 1395517 1395627 := bstep (se 1 (by rfl) ⟨1046720, by rfl⟩ : syracuseStep 1395627 = 2093441) B2093441
theorem B3140531 : Blo 1395517 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B1395639 : Blo 1395517 1395639 := bstep (se 1 (by rfl) ⟨1046729, by rfl⟩ : syracuseStep 1395639 = 2093459) B2093459
theorem B1395659 : Blo 1395517 1395659 := bstep (se 1 (by rfl) ⟨1046744, by rfl⟩ : syracuseStep 1395659 = 2093489) B2093489
theorem B1395671 : Blo 1395517 1395671 := bstep (se 1 (by rfl) ⟨1046753, by rfl⟩ : syracuseStep 1395671 = 2093507) B2093507
theorem B3140567 : Blo 1395517 3140567 := bstep (se 1 (by rfl) ⟨2355425, by rfl⟩ : syracuseStep 3140567 = 4710851) B4710851
theorem B1395691 : Blo 1395517 1395691 := bstep (se 1 (by rfl) ⟨1046768, by rfl⟩ : syracuseStep 1395691 = 2093537) B2093537
theorem B1395703 : Blo 1395517 1395703 := bstep (se 1 (by rfl) ⟨1046777, by rfl⟩ : syracuseStep 1395703 = 2093555) B2093555
theorem B1395723 : Blo 1395517 1395723 := bstep (se 1 (by rfl) ⟨1046792, by rfl⟩ : syracuseStep 1395723 = 2093585) B2093585
theorem B1395735 : Blo 1395517 1395735 := bstep (se 1 (by rfl) ⟨1046801, by rfl⟩ : syracuseStep 1395735 = 2093603) B2093603
theorem B1395755 : Blo 1395517 1395755 := bstep (se 1 (by rfl) ⟨1046816, by rfl⟩ : syracuseStep 1395755 = 2093633) B2093633
theorem B1395767 : Blo 1395517 1395767 := bstep (se 1 (by rfl) ⟨1046825, by rfl⟩ : syracuseStep 1395767 = 2093651) B2093651
theorem B1395787 : Blo 1395517 1395787 := bstep (se 1 (by rfl) ⟨1046840, by rfl⟩ : syracuseStep 1395787 = 2093681) B2093681
theorem B1395799 : Blo 1395517 1395799 := bstep (se 1 (by rfl) ⟨1046849, by rfl⟩ : syracuseStep 1395799 = 2093699) B2093699
theorem B3976285 : Blo 1395517 3976285 := bstep (se 3 (by rfl) ⟨745553, by rfl⟩ : syracuseStep 3976285 = 1491107) B1491107
theorem B1395819 : Blo 1395517 1395819 := bstep (se 1 (by rfl) ⟨1046864, by rfl⟩ : syracuseStep 1395819 = 2093729) B2093729
theorem B1395831 : Blo 1395517 1395831 := bstep (se 1 (by rfl) ⟨1046873, by rfl⟩ : syracuseStep 1395831 = 2093747) B2093747
theorem B1395851 : Blo 1395517 1395851 := bstep (se 1 (by rfl) ⟨1046888, by rfl⟩ : syracuseStep 1395851 = 2093777) B2093777
theorem B3140747 : Blo 1395517 3140747 := bstep (se 1 (by rfl) ⟨2355560, by rfl⟩ : syracuseStep 3140747 = 4711121) B4711121
theorem B1395863 : Blo 1395517 1395863 := bstep (se 1 (by rfl) ⟨1046897, by rfl⟩ : syracuseStep 1395863 = 2093795) B2093795
theorem B7072919 : Blo 1395517 7072919 := bstep (se 1 (by rfl) ⟨5304689, by rfl⟩ : syracuseStep 7072919 = 10609379) B10609379
theorem B1395883 : Blo 1395517 1395883 := bstep (se 1 (by rfl) ⟨1046912, by rfl⟩ : syracuseStep 1395883 = 2093825) B2093825
theorem B1395895 : Blo 1395517 1395895 := bstep (se 1 (by rfl) ⟨1046921, by rfl⟩ : syracuseStep 1395895 = 2093843) B2093843
theorem B3140801 : Blo 1395517 3140801 := bstep (se 2 (by rfl) ⟨1177800, by rfl⟩ : syracuseStep 3140801 = 2355601) B2355601
theorem B1395915 : Blo 1395517 1395915 := bstep (se 1 (by rfl) ⟨1046936, by rfl⟩ : syracuseStep 1395915 = 2093873) B2093873
theorem B1395927 : Blo 1395517 1395927 := bstep (se 1 (by rfl) ⟨1046945, by rfl⟩ : syracuseStep 1395927 = 2093891) B2093891
theorem B1395947 : Blo 1395517 1395947 := bstep (se 1 (by rfl) ⟨1046960, by rfl⟩ : syracuseStep 1395947 = 2093921) B2093921
theorem B1395959 : Blo 1395517 1395959 := bstep (se 1 (by rfl) ⟨1046969, by rfl⟩ : syracuseStep 1395959 = 2093939) B2093939
theorem B1395979 : Blo 1395517 1395979 := bstep (se 1 (by rfl) ⟨1046984, by rfl⟩ : syracuseStep 1395979 = 2093969) B2093969
theorem B8490257 : Blo 1395517 8490257 := bstep (se 2 (by rfl) ⟨3183846, by rfl⟩ : syracuseStep 8490257 = 6367693) B6367693
theorem B1395991 : Blo 1395517 1395991 := bstep (se 1 (by rfl) ⟨1046993, by rfl⟩ : syracuseStep 1395991 = 2093987) B2093987
theorem B1396011 : Blo 1395517 1396011 := bstep (se 1 (by rfl) ⟨1047008, by rfl⟩ : syracuseStep 1396011 = 2094017) B2094017
theorem B3534131 : Blo 1395517 3534131 := bstep (se 1 (by rfl) ⟨2650598, by rfl⟩ : syracuseStep 3534131 = 5301197) B5301197
theorem B1396023 : Blo 1395517 1396023 := bstep (se 1 (by rfl) ⟨1047017, by rfl⟩ : syracuseStep 1396023 = 2094035) B2094035
theorem B1396043 : Blo 1395517 1396043 := bstep (se 1 (by rfl) ⟨1047032, by rfl⟩ : syracuseStep 1396043 = 2094065) B2094065
theorem B5303627 : Blo 1395517 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B1396055 : Blo 1395517 1396055 := bstep (se 1 (by rfl) ⟨1047041, by rfl⟩ : syracuseStep 1396055 = 2094083) B2094083
theorem B2870615 : Blo 1395517 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B4713821 : Blo 1395517 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B1396075 : Blo 1395517 1396075 := bstep (se 1 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 1396075 = 2094113) B2094113
theorem B1396087 : Blo 1395517 1396087 := bstep (se 1 (by rfl) ⟨1047065, by rfl⟩ : syracuseStep 1396087 = 2094131) B2094131
theorem B1396107 : Blo 1395517 1396107 := bstep (se 1 (by rfl) ⟨1047080, by rfl⟩ : syracuseStep 1396107 = 2094161) B2094161
theorem B1510807 : Blo 1395517 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B1396119 : Blo 1395517 1396119 := bstep (se 1 (by rfl) ⟨1047089, by rfl⟩ : syracuseStep 1396119 = 2094179) B2094179
theorem B3141017 : Blo 1395517 3141017 := bstep (se 2 (by rfl) ⟨1177881, by rfl⟩ : syracuseStep 3141017 = 2355763) B2355763
theorem B1396139 : Blo 1395517 1396139 := bstep (se 1 (by rfl) ⟨1047104, by rfl⟩ : syracuseStep 1396139 = 2094209) B2094209
theorem B3976627 : Blo 1395517 3976627 := bstep (se 1 (by rfl) ⟨2982470, by rfl⟩ : syracuseStep 3976627 = 5964941) B5964941
theorem B1396151 : Blo 1395517 1396151 := bstep (se 1 (by rfl) ⟨1047113, by rfl⟩ : syracuseStep 1396151 = 2094227) B2094227
theorem B1396171 : Blo 1395517 1396171 := bstep (se 1 (by rfl) ⟨1047128, by rfl⟩ : syracuseStep 1396171 = 2094257) B2094257
theorem B1396183 : Blo 1395517 1396183 := bstep (se 1 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 1396183 = 2094275) B2094275
theorem B1396203 : Blo 1395517 1396203 := bstep (se 1 (by rfl) ⟨1047152, by rfl⟩ : syracuseStep 1396203 = 2094305) B2094305
theorem B3141107 : Blo 1395517 3141107 := bstep (se 1 (by rfl) ⟨2355830, by rfl⟩ : syracuseStep 3141107 = 4711661) B4711661
theorem B1396215 : Blo 1395517 1396215 := bstep (se 1 (by rfl) ⟨1047161, by rfl⟩ : syracuseStep 1396215 = 2094323) B2094323
theorem B2649611 : Blo 1395517 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B1396235 : Blo 1395517 1396235 := bstep (se 1 (by rfl) ⟨1047176, by rfl⟩ : syracuseStep 1396235 = 2094353) B2094353
theorem B5303825 : Blo 1395517 5303825 := bstep (se 2 (by rfl) ⟨1988934, by rfl⟩ : syracuseStep 5303825 = 3977869) B3977869
theorem B3141143 : Blo 1395517 3141143 := bstep (se 1 (by rfl) ⟨2355857, by rfl⟩ : syracuseStep 3141143 = 4711715) B4711715
theorem B1396247 : Blo 1395517 1396247 := bstep (se 1 (by rfl) ⟨1047185, by rfl⟩ : syracuseStep 1396247 = 2094371) B2094371
theorem B1396267 : Blo 1395517 1396267 := bstep (se 1 (by rfl) ⟨1047200, by rfl⟩ : syracuseStep 1396267 = 2094401) B2094401
theorem B1396279 : Blo 1395517 1396279 := bstep (se 1 (by rfl) ⟨1047209, by rfl⟩ : syracuseStep 1396279 = 2094419) B2094419
theorem B2649665 : Blo 1395517 2649665 := bstep (se 2 (by rfl) ⟨993624, by rfl⟩ : syracuseStep 2649665 = 1987249) B1987249
theorem B2829899 : Blo 1395517 2829899 := bstep (se 1 (by rfl) ⟨2122424, by rfl⟩ : syracuseStep 2829899 = 4244849) B4244849
theorem B1396299 : Blo 1395517 1396299 := bstep (se 1 (by rfl) ⟨1047224, by rfl⟩ : syracuseStep 1396299 = 2094449) B2094449
theorem B1396311 : Blo 1395517 1396311 := bstep (se 1 (by rfl) ⟨1047233, by rfl⟩ : syracuseStep 1396311 = 2094467) B2094467
theorem B3534425 : Blo 1395517 3534425 := bstep (se 2 (by rfl) ⟨1325409, by rfl⟩ : syracuseStep 3534425 = 2650819) B2650819
theorem B1396331 : Blo 1395517 1396331 := bstep (se 1 (by rfl) ⟨1047248, by rfl⟩ : syracuseStep 1396331 = 2094497) B2094497
theorem B1396343 : Blo 1395517 1396343 := bstep (se 1 (by rfl) ⟨1047257, by rfl⟩ : syracuseStep 1396343 = 2094515) B2094515
theorem B8498819 : Blo 1395517 8498819 := bstep (se 1 (by rfl) ⟨6374114, by rfl⟩ : syracuseStep 8498819 = 12748229) B12748229
theorem B1396363 : Blo 1395517 1396363 := bstep (se 1 (by rfl) ⟨1047272, by rfl⟩ : syracuseStep 1396363 = 2094545) B2094545
theorem B1396375 : Blo 1395517 1396375 := bstep (se 1 (by rfl) ⟨1047281, by rfl⟩ : syracuseStep 1396375 = 2094563) B2094563
theorem B1396395 : Blo 1395517 1396395 := bstep (se 1 (by rfl) ⟨1047296, by rfl⟩ : syracuseStep 1396395 = 2094593) B2094593
theorem B5967539 : Blo 1395517 5967539 := bstep (se 1 (by rfl) ⟨4475654, by rfl⟩ : syracuseStep 5967539 = 8951309) B8951309
theorem B1396407 : Blo 1395517 1396407 := bstep (se 1 (by rfl) ⟨1047305, by rfl⟩ : syracuseStep 1396407 = 2094611) B2094611
theorem B3141323 : Blo 1395517 3141323 := bstep (se 1 (by rfl) ⟨2355992, by rfl⟩ : syracuseStep 3141323 = 4711985) B4711985
theorem B1396427 : Blo 1395517 1396427 := bstep (se 1 (by rfl) ⟨1047320, by rfl⟩ : syracuseStep 1396427 = 2094641) B2094641
theorem B1396439 : Blo 1395517 1396439 := bstep (se 1 (by rfl) ⟨1047329, by rfl⟩ : syracuseStep 1396439 = 2094659) B2094659
theorem B7065305 : Blo 1395517 7065305 := bstep (se 2 (by rfl) ⟨2649489, by rfl⟩ : syracuseStep 7065305 = 5298979) B5298979
theorem B1396459 : Blo 1395517 1396459 := bstep (se 1 (by rfl) ⟨1047344, by rfl⟩ : syracuseStep 1396459 = 2094689) B2094689
theorem B1396471 : Blo 1395517 1396471 := bstep (se 1 (by rfl) ⟨1047353, by rfl⟩ : syracuseStep 1396471 = 2094707) B2094707
theorem B3141377 : Blo 1395517 3141377 := bstep (se 2 (by rfl) ⟨1178016, by rfl⟩ : syracuseStep 3141377 = 2356033) B2356033
theorem B1396491 : Blo 1395517 1396491 := bstep (se 1 (by rfl) ⟨1047368, by rfl⟩ : syracuseStep 1396491 = 2094737) B2094737
theorem B3772183 : Blo 1395517 3772183 := bstep (se 1 (by rfl) ⟨2829137, by rfl⟩ : syracuseStep 3772183 = 5658275) B5658275
theorem B1396503 : Blo 1395517 1396503 := bstep (se 1 (by rfl) ⟨1047377, by rfl⟩ : syracuseStep 1396503 = 2094755) B2094755
theorem B1396523 : Blo 1395517 1396523 := bstep (se 1 (by rfl) ⟨1047392, by rfl⟩ : syracuseStep 1396523 = 2094785) B2094785
theorem B13430573 : Blo 1395517 13430573 := bstep (se 3 (by rfl) ⟨2518232, by rfl⟩ : syracuseStep 13430573 = 5036465) B5036465
theorem B1396535 : Blo 1395517 1396535 := bstep (se 1 (by rfl) ⟨1047401, by rfl⟩ : syracuseStep 1396535 = 2094803) B2094803
theorem B1396555 : Blo 1395517 1396555 := bstep (se 1 (by rfl) ⟨1047416, by rfl⟩ : syracuseStep 1396555 = 2094833) B2094833
theorem B1396567 : Blo 1395517 1396567 := bstep (se 1 (by rfl) ⟨1047425, by rfl⟩ : syracuseStep 1396567 = 2094851) B2094851
theorem B1396587 : Blo 1395517 1396587 := bstep (se 1 (by rfl) ⟨1047440, by rfl⟩ : syracuseStep 1396587 = 2094881) B2094881
theorem B1396599 : Blo 1395517 1396599 := bstep (se 1 (by rfl) ⟨1047449, by rfl⟩ : syracuseStep 1396599 = 2094899) B2094899
theorem B1396619 : Blo 1395517 1396619 := bstep (se 1 (by rfl) ⟨1047464, by rfl⟩ : syracuseStep 1396619 = 2094929) B2094929
theorem B2355095 : Blo 1395517 2355095 := bstep (se 1 (by rfl) ⟨1766321, by rfl⟩ : syracuseStep 2355095 = 3532643) B3532643
theorem B1396631 : Blo 1395517 1396631 := bstep (se 1 (by rfl) ⟨1047473, by rfl⟩ : syracuseStep 1396631 = 2094947) B2094947
theorem B1396651 : Blo 1395517 1396651 := bstep (se 1 (by rfl) ⟨1047488, by rfl⟩ : syracuseStep 1396651 = 2094977) B2094977
theorem B6541235 : Blo 1395517 6541235 := bstep (se 1 (by rfl) ⟨4905926, by rfl⟩ : syracuseStep 6541235 = 9811853) B9811853
theorem B1396663 : Blo 1395517 1396663 := bstep (se 1 (by rfl) ⟨1047497, by rfl⟩ : syracuseStep 1396663 = 2094995) B2094995
theorem B1396683 : Blo 1395517 1396683 := bstep (se 1 (by rfl) ⟨1047512, by rfl⟩ : syracuseStep 1396683 = 2095025) B2095025
theorem B1396695 : Blo 1395517 1396695 := bstep (se 1 (by rfl) ⟨1047521, by rfl⟩ : syracuseStep 1396695 = 2095043) B2095043
theorem B3141593 : Blo 1395517 3141593 := bstep (se 2 (by rfl) ⟨1178097, by rfl⟩ : syracuseStep 3141593 = 2356195) B2356195
theorem B1396715 : Blo 1395517 1396715 := bstep (se 1 (by rfl) ⟨1047536, by rfl⟩ : syracuseStep 1396715 = 2095073) B2095073
theorem B1396727 : Blo 1395517 1396727 := bstep (se 1 (by rfl) ⟨1047545, by rfl⟩ : syracuseStep 1396727 = 2095091) B2095091
theorem B1396747 : Blo 1395517 1396747 := bstep (se 1 (by rfl) ⟨1047560, by rfl⟩ : syracuseStep 1396747 = 2095121) B2095121
theorem B2355223 : Blo 1395517 2355223 := bstep (se 1 (by rfl) ⟨1766417, by rfl⟩ : syracuseStep 2355223 = 3532835) B3532835
theorem B1396759 : Blo 1395517 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B1396779 : Blo 1395517 1396779 := bstep (se 1 (by rfl) ⟨1047584, by rfl⟩ : syracuseStep 1396779 = 2095169) B2095169
theorem B3141683 : Blo 1395517 3141683 := bstep (se 1 (by rfl) ⟨2356262, by rfl⟩ : syracuseStep 3141683 = 4712525) B4712525
theorem B1396791 : Blo 1395517 1396791 := bstep (se 1 (by rfl) ⟨1047593, by rfl⟩ : syracuseStep 1396791 = 2095187) B2095187
theorem B1396811 : Blo 1395517 1396811 := bstep (se 1 (by rfl) ⟨1047608, by rfl⟩ : syracuseStep 1396811 = 2095217) B2095217
theorem B3141719 : Blo 1395517 3141719 := bstep (se 1 (by rfl) ⟨2356289, by rfl⟩ : syracuseStep 3141719 = 4712579) B4712579
theorem B1396823 : Blo 1395517 1396823 := bstep (se 1 (by rfl) ⟨1047617, by rfl⟩ : syracuseStep 1396823 = 2095235) B2095235
theorem B3772505 : Blo 1395517 3772505 := bstep (se 2 (by rfl) ⟨1414689, by rfl⟩ : syracuseStep 3772505 = 2829379) B2829379
theorem B1396843 : Blo 1395517 1396843 := bstep (se 1 (by rfl) ⟨1047632, by rfl⟩ : syracuseStep 1396843 = 2095265) B2095265
theorem B1396855 : Blo 1395517 1396855 := bstep (se 1 (by rfl) ⟨1047641, by rfl⟩ : syracuseStep 1396855 = 2095283) B2095283
theorem B1396875 : Blo 1395517 1396875 := bstep (se 1 (by rfl) ⟨1047656, by rfl⟩ : syracuseStep 1396875 = 2095313) B2095313
theorem B1396887 : Blo 1395517 1396887 := bstep (se 1 (by rfl) ⟨1047665, by rfl⟩ : syracuseStep 1396887 = 2095331) B2095331
theorem B1396907 : Blo 1395517 1396907 := bstep (se 1 (by rfl) ⟨1047680, by rfl⟩ : syracuseStep 1396907 = 2095361) B2095361
theorem B10064051 : Blo 1395517 10064051 := bstep (se 1 (by rfl) ⟨7548038, by rfl⟩ : syracuseStep 10064051 = 15096077) B15096077
theorem B1396919 : Blo 1395517 1396919 := bstep (se 1 (by rfl) ⟨1047689, by rfl⟩ : syracuseStep 1396919 = 2095379) B2095379
theorem B1396939 : Blo 1395517 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B1396951 : Blo 1395517 1396951 := bstep (se 1 (by rfl) ⟨1047713, by rfl⟩ : syracuseStep 1396951 = 2095427) B2095427
theorem B12095705 : Blo 1395517 12095705 := bstep (se 2 (by rfl) ⟨4535889, by rfl⟩ : syracuseStep 12095705 = 9071779) B9071779
theorem B1396971 : Blo 1395517 1396971 := bstep (se 1 (by rfl) ⟨1047728, by rfl⟩ : syracuseStep 1396971 = 2095457) B2095457
theorem B1396983 : Blo 1395517 1396983 := bstep (se 1 (by rfl) ⟨1047737, by rfl⟩ : syracuseStep 1396983 = 2095475) B2095475
theorem B3141899 : Blo 1395517 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B1397003 : Blo 1395517 1397003 := bstep (se 1 (by rfl) ⟨1047752, by rfl⟩ : syracuseStep 1397003 = 2095505) B2095505
theorem B1397015 : Blo 1395517 1397015 := bstep (se 1 (by rfl) ⟨1047761, by rfl⟩ : syracuseStep 1397015 = 2095523) B2095523
theorem B5304599 : Blo 1395517 5304599 := bstep (se 1 (by rfl) ⟨3978449, by rfl⟩ : syracuseStep 5304599 = 7956899) B7956899
theorem B1397035 : Blo 1395517 1397035 := bstep (se 1 (by rfl) ⟨1047776, by rfl⟩ : syracuseStep 1397035 = 2095553) B2095553
theorem B1397047 : Blo 1395517 1397047 := bstep (se 1 (by rfl) ⟨1047785, by rfl⟩ : syracuseStep 1397047 = 2095571) B2095571
theorem B3141953 : Blo 1395517 3141953 := bstep (se 2 (by rfl) ⟨1178232, by rfl⟩ : syracuseStep 3141953 = 2356465) B2356465
theorem B2093387 : Blo 1395517 2093387 := bstep (se 1 (by rfl) ⟨1570040, by rfl⟩ : syracuseStep 2093387 = 3140081) B3140081
theorem B1397067 : Blo 1395517 1397067 := bstep (se 1 (by rfl) ⟨1047800, by rfl⟩ : syracuseStep 1397067 = 2095601) B2095601
theorem B2093399 : Blo 1395517 2093399 := bstep (se 1 (by rfl) ⟨1570049, by rfl⟩ : syracuseStep 2093399 = 3140099) B3140099
theorem B1397079 : Blo 1395517 1397079 := bstep (se 1 (by rfl) ⟨1047809, by rfl⟩ : syracuseStep 1397079 = 2095619) B2095619
theorem B3977561 : Blo 1395517 3977561 := bstep (se 2 (by rfl) ⟨1491585, by rfl⟩ : syracuseStep 3977561 = 2983171) B2983171
theorem B3772765 : Blo 1395517 3772765 := bstep (se 3 (by rfl) ⟨707393, by rfl⟩ : syracuseStep 3772765 = 1414787) B1414787
theorem B1397099 : Blo 1395517 1397099 := bstep (se 1 (by rfl) ⟨1047824, by rfl⟩ : syracuseStep 1397099 = 2095649) B2095649
theorem B1397111 : Blo 1395517 1397111 := bstep (se 1 (by rfl) ⟨1047833, by rfl⟩ : syracuseStep 1397111 = 2095667) B2095667
theorem B1397131 : Blo 1395517 1397131 := bstep (se 1 (by rfl) ⟨1047848, by rfl⟩ : syracuseStep 1397131 = 2095697) B2095697
theorem B1397143 : Blo 1395517 1397143 := bstep (se 1 (by rfl) ⟨1047857, by rfl⟩ : syracuseStep 1397143 = 2095715) B2095715
theorem B2093465 : Blo 1395517 2093465 := bstep (se 2 (by rfl) ⟨785049, by rfl⟩ : syracuseStep 2093465 = 1570099) B1570099
theorem B1397163 : Blo 1395517 1397163 := bstep (se 1 (by rfl) ⟨1047872, by rfl⟩ : syracuseStep 1397163 = 2095745) B2095745
theorem B1397175 : Blo 1395517 1397175 := bstep (se 1 (by rfl) ⟨1047881, by rfl⟩ : syracuseStep 1397175 = 2095763) B2095763
theorem B4714955 : Blo 1395517 4714955 := bstep (se 1 (by rfl) ⟨3536216, by rfl⟩ : syracuseStep 4714955 = 7072433) B7072433
theorem B1397195 : Blo 1395517 1397195 := bstep (se 1 (by rfl) ⟨1047896, by rfl⟩ : syracuseStep 1397195 = 2095793) B2095793
theorem B10605005 : Blo 1395517 10605005 := bstep (se 3 (by rfl) ⟨1988438, by rfl⟩ : syracuseStep 10605005 = 3976877) B3976877
theorem B2650583 : Blo 1395517 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B18133465 : Blo 1395517 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B1397207 : Blo 1395517 1397207 := bstep (se 1 (by rfl) ⟨1047905, by rfl⟩ : syracuseStep 1397207 = 2095811) B2095811
theorem B5304797 : Blo 1395517 5304797 := bstep (se 3 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 5304797 = 1989299) B1989299
theorem B1397227 : Blo 1395517 1397227 := bstep (se 1 (by rfl) ⟨1047920, by rfl⟩ : syracuseStep 1397227 = 2095841) B2095841
theorem B1397239 : Blo 1395517 1397239 := bstep (se 1 (by rfl) ⟨1047929, by rfl⟩ : syracuseStep 1397239 = 2095859) B2095859
theorem B2093579 : Blo 1395517 2093579 := bstep (se 1 (by rfl) ⟨1570184, by rfl⟩ : syracuseStep 2093579 = 3140369) B3140369
theorem B1397259 : Blo 1395517 1397259 := bstep (se 1 (by rfl) ⟨1047944, by rfl⟩ : syracuseStep 1397259 = 2095889) B2095889
theorem B2093591 : Blo 1395517 2093591 := bstep (se 1 (by rfl) ⟨1570193, by rfl⟩ : syracuseStep 2093591 = 3140387) B3140387
theorem B1397271 : Blo 1395517 1397271 := bstep (se 1 (by rfl) ⟨1047953, by rfl⟩ : syracuseStep 1397271 = 2095907) B2095907
theorem B3142169 : Blo 1395517 3142169 := bstep (se 2 (by rfl) ⟨1178313, by rfl⟩ : syracuseStep 3142169 = 2356627) B2356627
theorem B1397291 : Blo 1395517 1397291 := bstep (se 1 (by rfl) ⟨1047968, by rfl⟩ : syracuseStep 1397291 = 2095937) B2095937
theorem B1397303 : Blo 1395517 1397303 := bstep (se 1 (by rfl) ⟨1047977, by rfl⟩ : syracuseStep 1397303 = 2095955) B2095955
theorem B18133579 : Blo 1395517 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B1397323 : Blo 1395517 1397323 := bstep (se 1 (by rfl) ⟨1047992, by rfl⟩ : syracuseStep 1397323 = 2095985) B2095985
theorem B1397335 : Blo 1395517 1397335 := bstep (se 1 (by rfl) ⟨1048001, by rfl⟩ : syracuseStep 1397335 = 2096003) B2096003
theorem B2093657 : Blo 1395517 2093657 := bstep (se 2 (by rfl) ⟨785121, by rfl⟩ : syracuseStep 2093657 = 1570243) B1570243
theorem B1397355 : Blo 1395517 1397355 := bstep (se 1 (by rfl) ⟨1048016, by rfl⟩ : syracuseStep 1397355 = 2096033) B2096033
theorem B3142259 : Blo 1395517 3142259 := bstep (se 1 (by rfl) ⟨2356694, by rfl⟩ : syracuseStep 3142259 = 4713389) B4713389
theorem B1397367 : Blo 1395517 1397367 := bstep (se 1 (by rfl) ⟨1048025, by rfl⟩ : syracuseStep 1397367 = 2096051) B2096051
theorem B2355851 : Blo 1395517 2355851 := bstep (se 1 (by rfl) ⟨1766888, by rfl⟩ : syracuseStep 2355851 = 3533777) B3533777
theorem B1397387 : Blo 1395517 1397387 := bstep (se 1 (by rfl) ⟨1048040, by rfl⟩ : syracuseStep 1397387 = 2096081) B2096081
theorem B5968529 : Blo 1395517 5968529 := bstep (se 2 (by rfl) ⟨2238198, by rfl⟩ : syracuseStep 5968529 = 4476397) B4476397
theorem B2388631 : Blo 1395517 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B3142295 : Blo 1395517 3142295 := bstep (se 1 (by rfl) ⟨2356721, by rfl⟩ : syracuseStep 3142295 = 4713443) B4713443
theorem B1397399 : Blo 1395517 1397399 := bstep (se 1 (by rfl) ⟨1048049, by rfl⟩ : syracuseStep 1397399 = 2096099) B2096099
theorem B1397419 : Blo 1395517 1397419 := bstep (se 1 (by rfl) ⟨1048064, by rfl⟩ : syracuseStep 1397419 = 2096129) B2096129
theorem B1397431 : Blo 1395517 1397431 := bstep (se 1 (by rfl) ⟨1048073, by rfl⟩ : syracuseStep 1397431 = 2096147) B2096147
theorem B2093771 : Blo 1395517 2093771 := bstep (se 1 (by rfl) ⟨1570328, by rfl⟩ : syracuseStep 2093771 = 3140657) B3140657
theorem B1397451 : Blo 1395517 1397451 := bstep (se 1 (by rfl) ⟨1048088, by rfl⟩ : syracuseStep 1397451 = 2096177) B2096177
theorem B2093783 : Blo 1395517 2093783 := bstep (se 1 (by rfl) ⟨1570337, by rfl⟩ : syracuseStep 2093783 = 3140675) B3140675
theorem B1397463 : Blo 1395517 1397463 := bstep (se 1 (by rfl) ⟨1048097, by rfl⟩ : syracuseStep 1397463 = 2096195) B2096195
theorem B4715225 : Blo 1395517 4715225 := bstep (se 2 (by rfl) ⟨1768209, by rfl⟩ : syracuseStep 4715225 = 3536419) B3536419
theorem B1397483 : Blo 1395517 1397483 := bstep (se 1 (by rfl) ⟨1048112, by rfl⟩ : syracuseStep 1397483 = 2096225) B2096225
theorem B1397495 : Blo 1395517 1397495 := bstep (se 1 (by rfl) ⟨1048121, by rfl⟩ : syracuseStep 1397495 = 2096243) B2096243
theorem B2355979 : Blo 1395517 2355979 := bstep (se 1 (by rfl) ⟨1766984, by rfl⟩ : syracuseStep 2355979 = 3533969) B3533969
theorem B1397515 : Blo 1395517 1397515 := bstep (se 1 (by rfl) ⟨1048136, by rfl⟩ : syracuseStep 1397515 = 2096273) B2096273
theorem B11318033 : Blo 1395517 11318033 := bstep (se 2 (by rfl) ⟨4244262, by rfl⟩ : syracuseStep 11318033 = 8488525) B8488525
theorem B3355415 : Blo 1395517 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B2093849 : Blo 1395517 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B2388761 : Blo 1395517 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B3142475 : Blo 1395517 3142475 := bstep (se 1 (by rfl) ⟨2356856, by rfl⟩ : syracuseStep 3142475 = 4713713) B4713713
theorem B3142529 : Blo 1395517 3142529 := bstep (se 2 (by rfl) ⟨1178448, by rfl⟩ : syracuseStep 3142529 = 2356897) B2356897
theorem B2093963 : Blo 1395517 2093963 := bstep (se 1 (by rfl) ⟨1570472, by rfl⟩ : syracuseStep 2093963 = 3140945) B3140945
theorem B2093975 : Blo 1395517 2093975 := bstep (se 1 (by rfl) ⟨1570481, by rfl⟩ : syracuseStep 2093975 = 3140963) B3140963
theorem B2356121 : Blo 1395517 2356121 := bstep (se 2 (by rfl) ⟨883545, by rfl⟩ : syracuseStep 2356121 = 1767091) B1767091
theorem B6042547 : Blo 1395517 6042547 := bstep (se 1 (by rfl) ⟨4531910, by rfl⟩ : syracuseStep 6042547 = 9063821) B9063821
theorem B10605491 : Blo 1395517 10605491 := bstep (se 1 (by rfl) ⟨7954118, by rfl⟩ : syracuseStep 10605491 = 15908237) B15908237
theorem B2094041 : Blo 1395517 2094041 := bstep (se 2 (by rfl) ⟨785265, by rfl⟩ : syracuseStep 2094041 = 1570531) B1570531
theorem B2651123 : Blo 1395517 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B6370321 : Blo 1395517 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B10204177 : Blo 1395517 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B2356249 : Blo 1395517 2356249 := bstep (se 2 (by rfl) ⟨883593, by rfl⟩ : syracuseStep 2356249 = 1767187) B1767187
theorem B2094155 : Blo 1395517 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B2094167 : Blo 1395517 2094167 := bstep (se 1 (by rfl) ⟨1570625, by rfl⟩ : syracuseStep 2094167 = 3141251) B3141251
theorem B3142745 : Blo 1395517 3142745 := bstep (se 2 (by rfl) ⟨1178529, by rfl⟩ : syracuseStep 3142745 = 2357059) B2357059
theorem B1766539 : Blo 1395517 1766539 := bstep (se 1 (by rfl) ⟨1324904, by rfl⟩ : syracuseStep 1766539 = 2649809) B2649809
theorem B2094233 : Blo 1395517 2094233 := bstep (se 2 (by rfl) ⟨785337, by rfl⟩ : syracuseStep 2094233 = 1570675) B1570675
theorem B3142835 : Blo 1395517 3142835 := bstep (se 1 (by rfl) ⟨2357126, by rfl⟩ : syracuseStep 3142835 = 4714253) B4714253
theorem B3536075 : Blo 1395517 3536075 := bstep (se 1 (by rfl) ⟨2652056, by rfl⟩ : syracuseStep 3536075 = 5304113) B5304113
theorem B3142871 : Blo 1395517 3142871 := bstep (se 1 (by rfl) ⟨2357153, by rfl⟩ : syracuseStep 3142871 = 4714307) B4714307
theorem B1570027 : Blo 1395517 1570027 := bstep (se 1 (by rfl) ⟨1177520, by rfl⟩ : syracuseStep 1570027 = 2355041) B2355041
theorem B2094347 : Blo 1395517 2094347 := bstep (se 1 (by rfl) ⟨1570760, by rfl⟩ : syracuseStep 2094347 = 3141521) B3141521
theorem B2094359 : Blo 1395517 2094359 := bstep (se 1 (by rfl) ⟨1570769, by rfl⟩ : syracuseStep 2094359 = 3141539) B3141539
theorem B7066925 : Blo 1395517 7066925 := bstep (se 3 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 7066925 = 2650097) B2650097
theorem B1987915 : Blo 1395517 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B1570135 : Blo 1395517 1570135 := bstep (se 1 (by rfl) ⟨1177601, by rfl⟩ : syracuseStep 1570135 = 2355203) B2355203
theorem B2094425 : Blo 1395517 2094425 := bstep (se 2 (by rfl) ⟨785409, by rfl⟩ : syracuseStep 2094425 = 1570819) B1570819
theorem B3143051 : Blo 1395517 3143051 := bstep (se 1 (by rfl) ⟨2357288, by rfl⟩ : syracuseStep 3143051 = 4714577) B4714577
theorem B4715927 : Blo 1395517 4715927 := bstep (se 1 (by rfl) ⟨3536945, by rfl⟩ : syracuseStep 4715927 = 7073891) B7073891
theorem B3143105 : Blo 1395517 3143105 := bstep (se 2 (by rfl) ⟨1178664, by rfl⟩ : syracuseStep 3143105 = 2357329) B2357329
theorem B2094539 : Blo 1395517 2094539 := bstep (se 1 (by rfl) ⟨1570904, by rfl⟩ : syracuseStep 2094539 = 3141809) B3141809
theorem B2094551 : Blo 1395517 2094551 := bstep (se 1 (by rfl) ⟨1570913, by rfl⟩ : syracuseStep 2094551 = 3141827) B3141827
theorem B2651609 : Blo 1395517 2651609 := bstep (se 2 (by rfl) ⟨994353, by rfl⟩ : syracuseStep 2651609 = 1988707) B1988707
theorem B1570315 : Blo 1395517 1570315 := bstep (se 1 (by rfl) ⟨1177736, by rfl⟩ : syracuseStep 1570315 = 2355473) B2355473
theorem B2094617 : Blo 1395517 2094617 := bstep (se 2 (by rfl) ⟨785481, by rfl⟩ : syracuseStep 2094617 = 1570963) B1570963
theorem B12736075 : Blo 1395517 12736075 := bstep (se 1 (by rfl) ⟨9552056, by rfl⟩ : syracuseStep 12736075 = 19104113) B19104113
theorem B2356823 : Blo 1395517 2356823 := bstep (se 1 (by rfl) ⟨1767617, by rfl⟩ : syracuseStep 2356823 = 3535235) B3535235
theorem B1570423 : Blo 1395517 1570423 := bstep (se 1 (by rfl) ⟨1177817, by rfl⟩ : syracuseStep 1570423 = 2355635) B2355635
theorem B12744323 : Blo 1395517 12744323 := bstep (se 1 (by rfl) ⟨9558242, by rfl⟩ : syracuseStep 12744323 = 19116485) B19116485
theorem B2094731 : Blo 1395517 2094731 := bstep (se 1 (by rfl) ⟨1571048, by rfl⟩ : syracuseStep 2094731 = 3142097) B3142097
theorem B2094743 : Blo 1395517 2094743 := bstep (se 1 (by rfl) ⟨1571057, by rfl⟩ : syracuseStep 2094743 = 3142115) B3142115
theorem B3143321 : Blo 1395517 3143321 := bstep (se 2 (by rfl) ⟨1178745, by rfl⟩ : syracuseStep 3143321 = 2357491) B2357491
theorem B2356951 : Blo 1395517 2356951 := bstep (se 1 (by rfl) ⟨1767713, by rfl⟩ : syracuseStep 2356951 = 3535427) B3535427
theorem B2266841 : Blo 1395517 2266841 := bstep (se 2 (by rfl) ⟨850065, by rfl⟩ : syracuseStep 2266841 = 1700131) B1700131
theorem B2094809 : Blo 1395517 2094809 := bstep (se 2 (by rfl) ⟨785553, by rfl⟩ : syracuseStep 2094809 = 1571107) B1571107
theorem B3978973 : Blo 1395517 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B21509873 : Blo 1395517 21509873 := bstep (se 2 (by rfl) ⟨8066202, by rfl⟩ : syracuseStep 21509873 = 16132405) B16132405
theorem B3143411 : Blo 1395517 3143411 := bstep (se 1 (by rfl) ⟨2357558, by rfl⟩ : syracuseStep 3143411 = 4715117) B4715117
theorem B22656773 : Blo 1395517 22656773 := bstep (se 4 (by rfl) ⟨2124072, by rfl⟩ : syracuseStep 22656773 = 4248145) B4248145
theorem B3143447 : Blo 1395517 3143447 := bstep (se 1 (by rfl) ⟨2357585, by rfl⟩ : syracuseStep 3143447 = 4715171) B4715171
theorem B1570603 : Blo 1395517 1570603 := bstep (se 1 (by rfl) ⟨1177952, by rfl⟩ : syracuseStep 1570603 = 2355905) B2355905
theorem B2094923 : Blo 1395517 2094923 := bstep (se 1 (by rfl) ⟨1571192, by rfl⟩ : syracuseStep 2094923 = 3142385) B3142385
theorem B3356491 : Blo 1395517 3356491 := bstep (se 1 (by rfl) ⟨2517368, by rfl⟩ : syracuseStep 3356491 = 5034737) B5034737
theorem B2094935 : Blo 1395517 2094935 := bstep (se 1 (by rfl) ⟨1571201, by rfl⟩ : syracuseStep 2094935 = 3142403) B3142403
theorem B1570711 : Blo 1395517 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B3356567 : Blo 1395517 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B2095001 : Blo 1395517 2095001 := bstep (se 2 (by rfl) ⟨785625, by rfl⟩ : syracuseStep 2095001 = 1571251) B1571251
theorem B4470707 : Blo 1395517 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B4716467 : Blo 1395517 4716467 := bstep (se 1 (by rfl) ⟨3537350, by rfl⟩ : syracuseStep 4716467 = 7074701) B7074701
theorem B3979201 : Blo 1395517 3979201 := bstep (se 2 (by rfl) ⟨1492200, by rfl⟩ : syracuseStep 3979201 = 2984401) B2984401
theorem B3143627 : Blo 1395517 3143627 := bstep (se 1 (by rfl) ⟨2357720, by rfl⟩ : syracuseStep 3143627 = 4715441) B4715441
theorem B3143681 : Blo 1395517 3143681 := bstep (se 2 (by rfl) ⟨1178880, by rfl⟩ : syracuseStep 3143681 = 2357761) B2357761
theorem B2095115 : Blo 1395517 2095115 := bstep (se 1 (by rfl) ⟨1571336, by rfl⟩ : syracuseStep 2095115 = 3142673) B3142673
theorem B2095127 : Blo 1395517 2095127 := bstep (se 1 (by rfl) ⟨1571345, by rfl⟩ : syracuseStep 2095127 = 3142691) B3142691
theorem B1570891 : Blo 1395517 1570891 := bstep (se 1 (by rfl) ⟨1178168, by rfl⟩ : syracuseStep 1570891 = 2356337) B2356337
theorem B5036107 : Blo 1395517 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B1767511 : Blo 1395517 1767511 := bstep (se 1 (by rfl) ⟨1325633, by rfl⟩ : syracuseStep 1767511 = 2651267) B2651267
theorem B2095193 : Blo 1395517 2095193 := bstep (se 2 (by rfl) ⟨785697, by rfl⟩ : syracuseStep 2095193 = 1571395) B1571395
theorem B3537047 : Blo 1395517 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B1570999 : Blo 1395517 1570999 := bstep (se 1 (by rfl) ⟨1178249, by rfl⟩ : syracuseStep 1570999 = 2356499) B2356499
theorem B2095307 : Blo 1395517 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B2095319 : Blo 1395517 2095319 := bstep (se 1 (by rfl) ⟨1571489, by rfl⟩ : syracuseStep 2095319 = 3142979) B3142979
theorem B3143897 : Blo 1395517 3143897 := bstep (se 2 (by rfl) ⟨1178961, by rfl⟩ : syracuseStep 3143897 = 2357923) B2357923
theorem B49715461 : Blo 1395517 49715461 := bstep (se 4 (by rfl) ⟨4660824, by rfl⟩ : syracuseStep 49715461 = 9321649) B9321649
theorem B3979543 : Blo 1395517 3979543 := bstep (se 1 (by rfl) ⟨2984657, by rfl⟩ : syracuseStep 3979543 = 5969315) B5969315
theorem B2095385 : Blo 1395517 2095385 := bstep (se 2 (by rfl) ⟨785769, by rfl⟩ : syracuseStep 2095385 = 1571539) B1571539
theorem B3143987 : Blo 1395517 3143987 := bstep (se 1 (by rfl) ⟨2357990, by rfl⟩ : syracuseStep 3143987 = 4715981) B4715981
theorem B2357579 : Blo 1395517 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B3144023 : Blo 1395517 3144023 := bstep (se 1 (by rfl) ⟨2358017, by rfl⟩ : syracuseStep 3144023 = 4716035) B4716035
theorem B8059229 : Blo 1395517 8059229 := bstep (se 3 (by rfl) ⟨1511105, by rfl⟩ : syracuseStep 8059229 = 3022211) B3022211
theorem B5036381 : Blo 1395517 5036381 := bstep (se 3 (by rfl) ⟨944321, by rfl⟩ : syracuseStep 5036381 = 1888643) B1888643
theorem B10606949 : Blo 1395517 10606949 := bstep (se 4 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 10606949 = 1988803) B1988803
theorem B1571179 : Blo 1395517 1571179 := bstep (se 1 (by rfl) ⟨1178384, by rfl⟩ : syracuseStep 1571179 = 2356769) B2356769
theorem B48380273 : Blo 1395517 48380273 := bstep (se 2 (by rfl) ⟨18142602, by rfl⟩ : syracuseStep 48380273 = 36285205) B36285205
theorem B2095499 : Blo 1395517 2095499 := bstep (se 1 (by rfl) ⟨1571624, by rfl⟩ : syracuseStep 2095499 = 3143249) B3143249
theorem B2095511 : Blo 1395517 2095511 := bstep (se 1 (by rfl) ⟨1571633, by rfl⟩ : syracuseStep 2095511 = 3143267) B3143267
theorem B5962157 : Blo 1395517 5962157 := bstep (se 3 (by rfl) ⟨1117904, by rfl⟩ : syracuseStep 5962157 = 2235809) B2235809
theorem B2357707 : Blo 1395517 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B1571287 : Blo 1395517 1571287 := bstep (se 1 (by rfl) ⟨1178465, by rfl⟩ : syracuseStep 1571287 = 2356931) B2356931
theorem B2095577 : Blo 1395517 2095577 := bstep (se 2 (by rfl) ⟨785841, by rfl⟩ : syracuseStep 2095577 = 1571683) B1571683
theorem B8952281 : Blo 1395517 8952281 := bstep (se 2 (by rfl) ⟨3357105, by rfl⟩ : syracuseStep 8952281 = 6714211) B6714211
theorem B3144203 : Blo 1395517 3144203 := bstep (se 1 (by rfl) ⟨2358152, by rfl⟩ : syracuseStep 3144203 = 4716305) B4716305
theorem B1989145 : Blo 1395517 1989145 := bstep (se 2 (by rfl) ⟨745929, by rfl⟩ : syracuseStep 1989145 = 1491859) B1491859
theorem B3144257 : Blo 1395517 3144257 := bstep (se 2 (by rfl) ⟨1179096, by rfl⟩ : syracuseStep 3144257 = 2358193) B2358193
theorem B1677899 : Blo 1395517 1677899 := bstep (se 1 (by rfl) ⟨1258424, by rfl⟩ : syracuseStep 1677899 = 2516849) B2516849
theorem B2095691 : Blo 1395517 2095691 := bstep (se 1 (by rfl) ⟨1571768, by rfl⟩ : syracuseStep 2095691 = 3143537) B3143537
theorem B2095703 : Blo 1395517 2095703 := bstep (se 1 (by rfl) ⟨1571777, by rfl⟩ : syracuseStep 2095703 = 3143555) B3143555
theorem B2357849 : Blo 1395517 2357849 := bstep (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) B1768387
theorem B1571467 : Blo 1395517 1571467 := bstep (se 1 (by rfl) ⟨1178600, by rfl⟩ : syracuseStep 1571467 = 2357201) B2357201
theorem B2095769 : Blo 1395517 2095769 := bstep (se 2 (by rfl) ⟨785913, by rfl⟩ : syracuseStep 2095769 = 1571827) B1571827
theorem B2357977 : Blo 1395517 2357977 := bstep (se 2 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 2357977 = 1768483) B1768483
theorem B1571575 : Blo 1395517 1571575 := bstep (se 1 (by rfl) ⟨1178681, by rfl⟩ : syracuseStep 1571575 = 2357363) B2357363
theorem B10599173 : Blo 1395517 10599173 := bstep (se 4 (by rfl) ⟨993672, by rfl⟩ : syracuseStep 10599173 = 1987345) B1987345
theorem B2095883 : Blo 1395517 2095883 := bstep (se 1 (by rfl) ⟨1571912, by rfl⟩ : syracuseStep 2095883 = 3143825) B3143825
theorem B2095895 : Blo 1395517 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B10607435 : Blo 1395517 10607435 := bstep (se 1 (by rfl) ⟨7955576, by rfl⟩ : syracuseStep 10607435 = 15911153) B15911153
theorem B2153305 : Blo 1395517 2153305 := bstep (se 2 (by rfl) ⟨807489, by rfl⟩ : syracuseStep 2153305 = 1614979) B1614979
theorem B2095961 : Blo 1395517 2095961 := bstep (se 2 (by rfl) ⟨785985, by rfl⟩ : syracuseStep 2095961 = 1571971) B1571971
theorem B1768331 : Blo 1395517 1768331 := bstep (se 1 (by rfl) ⟨1326248, by rfl⟩ : syracuseStep 1768331 = 2652497) B2652497
theorem B2653067 : Blo 1395517 2653067 := bstep (se 1 (by rfl) ⟨1989800, by rfl⟩ : syracuseStep 2653067 = 3979601) B3979601
theorem B1571755 : Blo 1395517 1571755 := bstep (se 1 (by rfl) ⟨1178816, by rfl⟩ : syracuseStep 1571755 = 2357633) B2357633
theorem B17906609 : Blo 1395517 17906609 := bstep (se 2 (by rfl) ⟨6714978, by rfl⟩ : syracuseStep 17906609 = 13429957) B13429957
theorem B2096075 : Blo 1395517 2096075 := bstep (se 1 (by rfl) ⟨1572056, by rfl⟩ : syracuseStep 2096075 = 3144113) B3144113
theorem B2096087 : Blo 1395517 2096087 := bstep (se 1 (by rfl) ⟨1572065, by rfl⟩ : syracuseStep 2096087 = 3144131) B3144131
theorem B1571863 : Blo 1395517 1571863 := bstep (se 1 (by rfl) ⟨1178897, by rfl⟩ : syracuseStep 1571863 = 2357795) B2357795
theorem B2096153 : Blo 1395517 2096153 := bstep (se 2 (by rfl) ⟨786057, by rfl⟩ : syracuseStep 2096153 = 1572115) B1572115
theorem B9067565 : Blo 1395517 9067565 := bstep (se 3 (by rfl) ⟨1700168, by rfl⟩ : syracuseStep 9067565 = 3400337) B3400337
theorem B5962841 : Blo 1395517 5962841 := bstep (se 2 (by rfl) ⟨2236065, by rfl⟩ : syracuseStep 5962841 = 4472131) B4472131
theorem B2096267 : Blo 1395517 2096267 := bstep (se 1 (by rfl) ⟨1572200, by rfl⟩ : syracuseStep 2096267 = 3144401) B3144401
theorem B20405429 : Blo 1395517 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B1572043 : Blo 1395517 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B5659865 : Blo 1395517 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B193625315 : Blo 1395517 193625315 := bstep (se 1 (by rfl) ⟨145218986, by rfl⟩ : syracuseStep 193625315 = 290437973) B290437973
theorem B1572151 : Blo 1395517 1572151 := bstep (se 1 (by rfl) ⟨1179113, by rfl⟩ : syracuseStep 1572151 = 2358227) B2358227
theorem B1416523 : Blo 1395517 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1490347 : Blo 1395517 1490347 := bstep (se 1 (by rfl) ⟨1117760, by rfl⟩ : syracuseStep 1490347 = 2235521) B2235521
theorem B2981377 : Blo 1395517 2981377 := bstep (se 2 (by rfl) ⟨1118016, by rfl⟩ : syracuseStep 2981377 = 2236033) B2236033
theorem B13598225 : Blo 1395517 13598225 := bstep (se 2 (by rfl) ⟨5099334, by rfl⟩ : syracuseStep 13598225 = 10198669) B10198669
theorem B3186263 : Blo 1395517 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B4775617 : Blo 1395517 4775617 := bstep (se 2 (by rfl) ⟨1790856, by rfl⟩ : syracuseStep 4775617 = 3581713) B3581713
theorem B3399499 : Blo 1395517 3399499 := bstep (se 1 (by rfl) ⟨2549624, by rfl⟩ : syracuseStep 3399499 = 5099249) B5099249
theorem B5029721 : Blo 1395517 5029721 := bstep (se 2 (by rfl) ⟨1886145, by rfl⟩ : syracuseStep 5029721 = 3772291) B3772291
theorem B6045529 : Blo 1395517 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B2686871 : Blo 1395517 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B4710365 : Blo 1395517 4710365 := bstep (se 3 (by rfl) ⟨883193, by rfl⟩ : syracuseStep 4710365 = 1766387) B1766387
theorem B6709367 : Blo 1395517 6709367 := bstep (se 1 (by rfl) ⟨5032025, by rfl⟩ : syracuseStep 6709367 = 10064051) B10064051
theorem B2982035 : Blo 1395517 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B10060013 : Blo 1395517 10060013 := bstep (se 3 (by rfl) ⟨1886252, by rfl⟩ : syracuseStep 10060013 = 3772505) B3772505
theorem B4710689 : Blo 1395517 4710689 := bstep (se 2 (by rfl) ⟨1766508, by rfl⟩ : syracuseStep 4710689 = 3533017) B3533017
theorem B7070003 : Blo 1395517 7070003 := bstep (se 1 (by rfl) ⟨5302502, by rfl⟩ : syracuseStep 7070003 = 10605005) B10605005
theorem B5030353 : Blo 1395517 5030353 := bstep (se 2 (by rfl) ⟨1886382, by rfl⟩ : syracuseStep 5030353 = 3772765) B3772765
theorem B7545355 : Blo 1395517 7545355 := bstep (se 1 (by rfl) ⟨5659016, by rfl⟩ : syracuseStep 7545355 = 11318033) B11318033
theorem B2236943 : Blo 1395517 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B4473463 : Blo 1395517 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B7070327 : Blo 1395517 7070327 := bstep (se 1 (by rfl) ⟨5302745, by rfl⟩ : syracuseStep 7070327 = 10605491) B10605491
theorem B4711283 : Blo 1395517 4711283 := bstep (se 1 (by rfl) ⟨3533462, by rfl⟩ : syracuseStep 4711283 = 7066925) B7066925
theorem B60400565 : Blo 1395517 60400565 := bstep (se 5 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 60400565 = 5662553) B5662553
theorem B25469957 : Blo 1395517 25469957 := bstep (se 4 (by rfl) ⟨2387808, by rfl⟩ : syracuseStep 25469957 = 4775617) B4775617
theorem B8496215 : Blo 1395517 8496215 := bstep (se 1 (by rfl) ⟨6372161, by rfl⟩ : syracuseStep 8496215 = 12744323) B12744323
theorem B1492111 : Blo 1395517 1492111 := bstep (se 1 (by rfl) ⟨1119083, by rfl⟩ : syracuseStep 1492111 = 2238167) B2238167
theorem B10609865 : Blo 1395517 10609865 := bstep (se 2 (by rfl) ⟨3978699, by rfl⟩ : syracuseStep 10609865 = 7957399) B7957399
theorem B2237711 : Blo 1395517 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B5301713 : Blo 1395517 5301713 := bstep (se 2 (by rfl) ⟨1988142, by rfl⟩ : syracuseStep 5301713 = 3976285) B3976285
theorem B4474397 : Blo 1395517 4474397 := bstep (se 3 (by rfl) ⟨838949, by rfl⟩ : syracuseStep 4474397 = 1677899) B1677899
theorem B8496701 : Blo 1395517 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B7071299 : Blo 1395517 7071299 := bstep (se 1 (by rfl) ⟨5303474, by rfl⟩ : syracuseStep 7071299 = 10606949) B10606949
theorem B32253515 : Blo 1395517 32253515 := bstep (se 1 (by rfl) ⟨24190136, by rfl⟩ : syracuseStep 32253515 = 48380273) B48380273
theorem B3974771 : Blo 1395517 3974771 := bstep (se 1 (by rfl) ⟨2981078, by rfl⟩ : syracuseStep 3974771 = 5962157) B5962157
theorem B7071623 : Blo 1395517 7071623 := bstep (se 1 (by rfl) ⟨5303717, by rfl⟩ : syracuseStep 7071623 = 10607435) B10607435
theorem B5302169 : Blo 1395517 5302169 := bstep (se 2 (by rfl) ⟨1988313, by rfl⟩ : syracuseStep 5302169 = 3976627) B3976627
theorem B11937739 : Blo 1395517 11937739 := bstep (se 1 (by rfl) ⟨8953304, by rfl⟩ : syracuseStep 11937739 = 17906609) B17906609
theorem B3975169 : Blo 1395517 3975169 := bstep (se 2 (by rfl) ⟨1490688, by rfl⟩ : syracuseStep 3975169 = 2981377) B2981377
theorem B3975227 : Blo 1395517 3975227 := bstep (se 1 (by rfl) ⟨2981420, by rfl⟩ : syracuseStep 3975227 = 5962841) B5962841
theorem B5662781 : Blo 1395517 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B129083543 : Blo 1395517 129083543 := bstep (se 1 (by rfl) ⟨96812657, by rfl⟩ : syracuseStep 129083543 = 193625315) B193625315
theorem B4245821 : Blo 1395517 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B1886599 : Blo 1395517 1886599 := bstep (se 1 (by rfl) ⟨1414949, by rfl⟩ : syracuseStep 1886599 = 2829899) B2829899
theorem B4532665 : Blo 1395517 4532665 := bstep (se 2 (by rfl) ⟨1699749, by rfl⟩ : syracuseStep 4532665 = 3399499) B3399499
theorem B4475321 : Blo 1395517 4475321 := bstep (se 2 (by rfl) ⟨1678245, by rfl⟩ : syracuseStep 4475321 = 3356491) B3356491
theorem B3353147 : Blo 1395517 3353147 := bstep (se 1 (by rfl) ⟨2514860, by rfl⟩ : syracuseStep 3353147 = 5029721) B5029721
theorem B4360823 : Blo 1395517 4360823 := bstep (se 1 (by rfl) ⟨3270617, by rfl⟩ : syracuseStep 4360823 = 6541235) B6541235
theorem B3140243 : Blo 1395517 3140243 := bstep (se 1 (by rfl) ⟨2355182, by rfl⟩ : syracuseStep 3140243 = 4710365) B4710365
theorem B3140297 : Blo 1395517 3140297 := bstep (se 2 (by rfl) ⟨1177611, by rfl⟩ : syracuseStep 3140297 = 2355223) B2355223
theorem B11922227 : Blo 1395517 11922227 := bstep (se 1 (by rfl) ⟨8941670, by rfl⟩ : syracuseStep 11922227 = 17883341) B17883341
theorem B8063803 : Blo 1395517 8063803 := bstep (se 1 (by rfl) ⟨6047852, by rfl⟩ : syracuseStep 8063803 = 12095705) B12095705
theorem B1395591 : Blo 1395517 1395591 := bstep (se 1 (by rfl) ⟨1046693, by rfl⟩ : syracuseStep 1395591 = 2093387) B2093387
theorem B1395599 : Blo 1395517 1395599 := bstep (se 1 (by rfl) ⟨1046699, by rfl⟩ : syracuseStep 1395599 = 2093399) B2093399
theorem B1395643 : Blo 1395517 1395643 := bstep (se 1 (by rfl) ⟨1046732, by rfl⟩ : syracuseStep 1395643 = 2093465) B2093465
theorem B1395719 : Blo 1395517 1395719 := bstep (se 1 (by rfl) ⟨1046789, by rfl⟩ : syracuseStep 1395719 = 2093579) B2093579
theorem B1395727 : Blo 1395517 1395727 := bstep (se 1 (by rfl) ⟨1046795, by rfl⟩ : syracuseStep 1395727 = 2093591) B2093591
theorem B5303339 : Blo 1395517 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B1395771 : Blo 1395517 1395771 := bstep (se 1 (by rfl) ⟨1046828, by rfl⟩ : syracuseStep 1395771 = 2093657) B2093657
theorem B3533939 : Blo 1395517 3533939 := bstep (se 1 (by rfl) ⟨2650454, by rfl⟩ : syracuseStep 3533939 = 5300909) B5300909
theorem B1395847 : Blo 1395517 1395847 := bstep (se 1 (by rfl) ⟨1046885, by rfl⟩ : syracuseStep 1395847 = 2093771) B2093771
theorem B1395855 : Blo 1395517 1395855 := bstep (se 1 (by rfl) ⟨1046891, by rfl⟩ : syracuseStep 1395855 = 2093783) B2093783
theorem B1395899 : Blo 1395517 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B1592507 : Blo 1395517 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B1395975 : Blo 1395517 1395975 := bstep (se 1 (by rfl) ⟨1046981, by rfl⟩ : syracuseStep 1395975 = 2093963) B2093963
theorem B1395983 : Blo 1395517 1395983 := bstep (se 1 (by rfl) ⟨1046987, by rfl⟩ : syracuseStep 1395983 = 2093975) B2093975
theorem B24177953 : Blo 1395517 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B1396027 : Blo 1395517 1396027 := bstep (se 1 (by rfl) ⟨1047020, by rfl⟩ : syracuseStep 1396027 = 2094041) B2094041
theorem B3140999 : Blo 1395517 3140999 := bstep (se 1 (by rfl) ⟨2355749, by rfl⟩ : syracuseStep 3140999 = 4711499) B4711499
theorem B1396103 : Blo 1395517 1396103 := bstep (se 1 (by rfl) ⟨1047077, by rfl⟩ : syracuseStep 1396103 = 2094155) B2094155
theorem B1396111 : Blo 1395517 1396111 := bstep (se 1 (by rfl) ⟨1047083, by rfl⟩ : syracuseStep 1396111 = 2094167) B2094167
theorem B4713875 : Blo 1395517 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B24178105 : Blo 1395517 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B1396155 : Blo 1395517 1396155 := bstep (se 1 (by rfl) ⟨1047116, by rfl⟩ : syracuseStep 1396155 = 2094233) B2094233
theorem B1396231 : Blo 1395517 1396231 := bstep (se 1 (by rfl) ⟨1047173, by rfl⟩ : syracuseStep 1396231 = 2094347) B2094347
theorem B1396239 : Blo 1395517 1396239 := bstep (se 1 (by rfl) ⟨1047179, by rfl⟩ : syracuseStep 1396239 = 2094359) B2094359
theorem B3141179 : Blo 1395517 3141179 := bstep (se 1 (by rfl) ⟨2355884, by rfl⟩ : syracuseStep 3141179 = 4711769) B4711769
theorem B1396283 : Blo 1395517 1396283 := bstep (se 1 (by rfl) ⟨1047212, by rfl⟩ : syracuseStep 1396283 = 2094425) B2094425
theorem B5664323 : Blo 1395517 5664323 := bstep (se 1 (by rfl) ⟨4248242, by rfl⟩ : syracuseStep 5664323 = 8496485) B8496485
theorem B3534455 : Blo 1395517 3534455 := bstep (se 1 (by rfl) ⟨2650841, by rfl⟩ : syracuseStep 3534455 = 5301683) B5301683
theorem B1396359 : Blo 1395517 1396359 := bstep (se 1 (by rfl) ⟨1047269, by rfl⟩ : syracuseStep 1396359 = 2094539) B2094539
theorem B1396367 : Blo 1395517 1396367 := bstep (se 1 (by rfl) ⟨1047275, by rfl⟩ : syracuseStep 1396367 = 2094551) B2094551
theorem B3141305 : Blo 1395517 3141305 := bstep (se 2 (by rfl) ⟨1177989, by rfl⟩ : syracuseStep 3141305 = 2355979) B2355979
theorem B1396411 : Blo 1395517 1396411 := bstep (se 1 (by rfl) ⟨1047308, by rfl⟩ : syracuseStep 1396411 = 2094617) B2094617
theorem B61214449 : Blo 1395517 61214449 := bstep (se 2 (by rfl) ⟨22955418, by rfl⟩ : syracuseStep 61214449 = 45910837) B45910837
theorem B1396487 : Blo 1395517 1396487 := bstep (se 1 (by rfl) ⟨1047365, by rfl⟩ : syracuseStep 1396487 = 2094731) B2094731
theorem B1396495 : Blo 1395517 1396495 := bstep (se 1 (by rfl) ⟨1047371, by rfl⟩ : syracuseStep 1396495 = 2094743) B2094743
theorem B2871073 : Blo 1395517 2871073 := bstep (se 2 (by rfl) ⟨1076652, by rfl⟩ : syracuseStep 2871073 = 2153305) B2153305
theorem B5451553 : Blo 1395517 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B2354987 : Blo 1395517 2354987 := bstep (se 1 (by rfl) ⟨1766240, by rfl⟩ : syracuseStep 2354987 = 3532481) B3532481
theorem B1511227 : Blo 1395517 1511227 := bstep (se 1 (by rfl) ⟨1133420, by rfl⟩ : syracuseStep 1511227 = 2266841) B2266841
theorem B1396539 : Blo 1395517 1396539 := bstep (se 1 (by rfl) ⟨1047404, by rfl⟩ : syracuseStep 1396539 = 2094809) B2094809
theorem B14339915 : Blo 1395517 14339915 := bstep (se 1 (by rfl) ⟨10754936, by rfl⟩ : syracuseStep 14339915 = 21509873) B21509873
theorem B2649991 : Blo 1395517 2649991 := bstep (se 1 (by rfl) ⟨1987493, by rfl⟩ : syracuseStep 2649991 = 3974987) B3974987
theorem B1396615 : Blo 1395517 1396615 := bstep (se 1 (by rfl) ⟨1047461, by rfl⟩ : syracuseStep 1396615 = 2094923) B2094923
theorem B1396623 : Blo 1395517 1396623 := bstep (se 1 (by rfl) ⟨1047467, by rfl⟩ : syracuseStep 1396623 = 2094935) B2094935
theorem B8056729 : Blo 1395517 8056729 := bstep (se 2 (by rfl) ⟨3021273, by rfl⟩ : syracuseStep 8056729 = 6042547) B6042547
theorem B1396667 : Blo 1395517 1396667 := bstep (se 1 (by rfl) ⟨1047500, by rfl⟩ : syracuseStep 1396667 = 2095001) B2095001
theorem B1396743 : Blo 1395517 1396743 := bstep (se 1 (by rfl) ⟨1047557, by rfl⟩ : syracuseStep 1396743 = 2095115) B2095115
theorem B3141647 : Blo 1395517 3141647 := bstep (se 1 (by rfl) ⟨2356235, by rfl⟩ : syracuseStep 3141647 = 4712471) B4712471
theorem B1396751 : Blo 1395517 1396751 := bstep (se 1 (by rfl) ⟨1047563, by rfl⟩ : syracuseStep 1396751 = 2095127) B2095127
theorem B7065629 : Blo 1395517 7065629 := bstep (se 3 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 7065629 = 2649611) B2649611
theorem B3141665 : Blo 1395517 3141665 := bstep (se 2 (by rfl) ⟨1178124, by rfl⟩ : syracuseStep 3141665 = 2356249) B2356249
theorem B1396795 : Blo 1395517 1396795 := bstep (se 1 (by rfl) ⟨1047596, by rfl⟩ : syracuseStep 1396795 = 2095193) B2095193
theorem B1396871 : Blo 1395517 1396871 := bstep (se 1 (by rfl) ⟨1047653, by rfl⟩ : syracuseStep 1396871 = 2095307) B2095307
theorem B3584135 : Blo 1395517 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B1396879 : Blo 1395517 1396879 := bstep (se 1 (by rfl) ⟨1047659, by rfl⟩ : syracuseStep 1396879 = 2095319) B2095319
theorem B2355385 : Blo 1395517 2355385 := bstep (se 2 (by rfl) ⟨883269, by rfl⟩ : syracuseStep 2355385 = 1766539) B1766539
theorem B1396923 : Blo 1395517 1396923 := bstep (se 1 (by rfl) ⟨1047692, by rfl⟩ : syracuseStep 1396923 = 2095385) B2095385
theorem B2093303 : Blo 1395517 2093303 := bstep (se 1 (by rfl) ⟨1569977, by rfl⟩ : syracuseStep 2093303 = 3139955) B3139955
theorem B1396999 : Blo 1395517 1396999 := bstep (se 1 (by rfl) ⟨1047749, by rfl⟩ : syracuseStep 1396999 = 2095499) B2095499
theorem B2093327 : Blo 1395517 2093327 := bstep (se 1 (by rfl) ⟨1569995, by rfl⟩ : syracuseStep 2093327 = 3139991) B3139991
theorem B1397007 : Blo 1395517 1397007 := bstep (se 1 (by rfl) ⟨1047755, by rfl⟩ : syracuseStep 1397007 = 2095511) B2095511
theorem B3977515 : Blo 1395517 3977515 := bstep (se 1 (by rfl) ⟨2983136, by rfl⟩ : syracuseStep 3977515 = 5966273) B5966273
theorem B2093369 : Blo 1395517 2093369 := bstep (se 2 (by rfl) ⟨785013, by rfl⟩ : syracuseStep 2093369 = 1570027) B1570027
theorem B1397051 : Blo 1395517 1397051 := bstep (se 1 (by rfl) ⟨1047788, by rfl⟩ : syracuseStep 1397051 = 2095577) B2095577
theorem B5968187 : Blo 1395517 5968187 := bstep (se 1 (by rfl) ⟨4476140, by rfl⟩ : syracuseStep 5968187 = 8952281) B8952281
theorem B3142007 : Blo 1395517 3142007 := bstep (se 1 (by rfl) ⟨2356505, by rfl⟩ : syracuseStep 3142007 = 4713011) B4713011
theorem B2093447 : Blo 1395517 2093447 := bstep (se 1 (by rfl) ⟨1570085, by rfl⟩ : syracuseStep 2093447 = 3140171) B3140171
theorem B1397127 : Blo 1395517 1397127 := bstep (se 1 (by rfl) ⟨1047845, by rfl⟩ : syracuseStep 1397127 = 2095691) B2095691
theorem B1397135 : Blo 1395517 1397135 := bstep (se 1 (by rfl) ⟨1047851, by rfl⟩ : syracuseStep 1397135 = 2095703) B2095703
theorem B13431187 : Blo 1395517 13431187 := bstep (se 1 (by rfl) ⟨10073390, by rfl⟩ : syracuseStep 13431187 = 20146781) B20146781
theorem B2093483 : Blo 1395517 2093483 := bstep (se 1 (by rfl) ⟨1570112, by rfl⟩ : syracuseStep 2093483 = 3140225) B3140225
theorem B2650553 : Blo 1395517 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B1888697 : Blo 1395517 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B1397179 : Blo 1395517 1397179 := bstep (se 1 (by rfl) ⟨1047884, by rfl⟩ : syracuseStep 1397179 = 2095769) B2095769
theorem B2093513 : Blo 1395517 2093513 := bstep (se 2 (by rfl) ⟨785067, by rfl⟩ : syracuseStep 2093513 = 1570135) B1570135
theorem B7066115 : Blo 1395517 7066115 := bstep (se 1 (by rfl) ⟨5299586, by rfl⟩ : syracuseStep 7066115 = 10599173) B10599173
theorem B1397255 : Blo 1395517 1397255 := bstep (se 1 (by rfl) ⟨1047941, by rfl⟩ : syracuseStep 1397255 = 2095883) B2095883
theorem B3977743 : Blo 1395517 3977743 := bstep (se 1 (by rfl) ⟨2983307, by rfl⟩ : syracuseStep 3977743 = 5966615) B5966615
theorem B1397263 : Blo 1395517 1397263 := bstep (se 1 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 1397263 = 2095895) B2095895
theorem B3142187 : Blo 1395517 3142187 := bstep (se 1 (by rfl) ⟨2356640, by rfl⟩ : syracuseStep 3142187 = 4713281) B4713281
theorem B1987129 : Blo 1395517 1987129 := bstep (se 2 (by rfl) ⟨745173, by rfl⟩ : syracuseStep 1987129 = 1490347) B1490347
theorem B2093627 : Blo 1395517 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B1397307 : Blo 1395517 1397307 := bstep (se 1 (by rfl) ⟨1047980, by rfl⟩ : syracuseStep 1397307 = 2095961) B2095961
theorem B7549507 : Blo 1395517 7549507 := bstep (se 1 (by rfl) ⟨5662130, by rfl⟩ : syracuseStep 7549507 = 11324261) B11324261
theorem B3535447 : Blo 1395517 3535447 := bstep (se 1 (by rfl) ⟨2651585, by rfl⟩ : syracuseStep 3535447 = 5303171) B5303171
theorem B2093687 : Blo 1395517 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B1397383 : Blo 1395517 1397383 := bstep (se 1 (by rfl) ⟨1048037, by rfl⟩ : syracuseStep 1397383 = 2096075) B2096075
theorem B2093711 : Blo 1395517 2093711 := bstep (se 1 (by rfl) ⟨1570283, by rfl⟩ : syracuseStep 2093711 = 3140567) B3140567
theorem B1397391 : Blo 1395517 1397391 := bstep (se 1 (by rfl) ⟨1048043, by rfl⟩ : syracuseStep 1397391 = 2096087) B2096087
theorem B2093753 : Blo 1395517 2093753 := bstep (se 2 (by rfl) ⟨785157, by rfl⟩ : syracuseStep 2093753 = 1570315) B1570315
theorem B1397435 : Blo 1395517 1397435 := bstep (se 1 (by rfl) ⟨1048076, by rfl⟩ : syracuseStep 1397435 = 2096153) B2096153
theorem B2093831 : Blo 1395517 2093831 := bstep (se 1 (by rfl) ⟨1570373, by rfl⟩ : syracuseStep 2093831 = 3140747) B3140747
theorem B1397511 : Blo 1395517 1397511 := bstep (se 1 (by rfl) ⟨1048133, by rfl⟩ : syracuseStep 1397511 = 2096267) B2096267
theorem B4715279 : Blo 1395517 4715279 := bstep (se 1 (by rfl) ⟨3536459, by rfl⟩ : syracuseStep 4715279 = 7072919) B7072919
theorem B3978017 : Blo 1395517 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B13603619 : Blo 1395517 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B2093867 : Blo 1395517 2093867 := bstep (se 1 (by rfl) ⟨1570400, by rfl⟩ : syracuseStep 2093867 = 3140801) B3140801
theorem B3773243 : Blo 1395517 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B2093897 : Blo 1395517 2093897 := bstep (se 2 (by rfl) ⟨785211, by rfl⟩ : syracuseStep 2093897 = 1570423) B1570423
theorem B2356087 : Blo 1395517 2356087 := bstep (se 1 (by rfl) ⟨1767065, by rfl⟩ : syracuseStep 2356087 = 3534131) B3534131
theorem B3535751 : Blo 1395517 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B1913743 : Blo 1395517 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B3142547 : Blo 1395517 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B2094011 : Blo 1395517 2094011 := bstep (se 1 (by rfl) ⟨1570508, by rfl⟩ : syracuseStep 2094011 = 3141017) B3141017
theorem B3142601 : Blo 1395517 3142601 := bstep (se 2 (by rfl) ⟨1178475, by rfl⟩ : syracuseStep 3142601 = 2356951) B2356951
theorem B5305297 : Blo 1395517 5305297 := bstep (se 2 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 5305297 = 3978973) B3978973
theorem B2094071 : Blo 1395517 2094071 := bstep (se 1 (by rfl) ⟨1570553, by rfl⟩ : syracuseStep 2094071 = 3141107) B3141107
theorem B9065483 : Blo 1395517 9065483 := bstep (se 1 (by rfl) ⟨6799112, by rfl⟩ : syracuseStep 9065483 = 13598225) B13598225
theorem B3535883 : Blo 1395517 3535883 := bstep (se 1 (by rfl) ⟨2651912, by rfl⟩ : syracuseStep 3535883 = 5303825) B5303825
theorem B2094095 : Blo 1395517 2094095 := bstep (se 1 (by rfl) ⟨1570571, by rfl⟩ : syracuseStep 2094095 = 3141143) B3141143
theorem B4715549 : Blo 1395517 4715549 := bstep (se 3 (by rfl) ⟨884165, by rfl⟩ : syracuseStep 4715549 = 1768331) B1768331
theorem B1766443 : Blo 1395517 1766443 := bstep (se 1 (by rfl) ⟨1324832, by rfl⟩ : syracuseStep 1766443 = 2649665) B2649665
theorem B2094137 : Blo 1395517 2094137 := bstep (se 2 (by rfl) ⟨785301, by rfl⟩ : syracuseStep 2094137 = 1570603) B1570603
theorem B2356283 : Blo 1395517 2356283 := bstep (se 1 (by rfl) ⟨1767212, by rfl⟩ : syracuseStep 2356283 = 3534425) B3534425
theorem B7164989 : Blo 1395517 7164989 := bstep (se 3 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 7164989 = 2686871) B2686871
theorem B5665879 : Blo 1395517 5665879 := bstep (se 1 (by rfl) ⟨4249409, by rfl⟩ : syracuseStep 5665879 = 8498819) B8498819
theorem B3978359 : Blo 1395517 3978359 := bstep (se 1 (by rfl) ⟨2983769, by rfl⟩ : syracuseStep 3978359 = 5967539) B5967539
theorem B2094215 : Blo 1395517 2094215 := bstep (se 1 (by rfl) ⟨1570661, by rfl⟩ : syracuseStep 2094215 = 3141323) B3141323
theorem B2094251 : Blo 1395517 2094251 := bstep (se 1 (by rfl) ⟨1570688, by rfl⟩ : syracuseStep 2094251 = 3141377) B3141377
theorem B2094281 : Blo 1395517 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B5305601 : Blo 1395517 5305601 := bstep (se 2 (by rfl) ⟨1989600, by rfl⟩ : syracuseStep 5305601 = 3979201) B3979201
theorem B1570063 : Blo 1395517 1570063 := bstep (se 1 (by rfl) ⟨1177547, by rfl⟩ : syracuseStep 1570063 = 2355095) B2355095
theorem B2094395 : Blo 1395517 2094395 := bstep (se 1 (by rfl) ⟨1570796, by rfl⟩ : syracuseStep 2094395 = 3141593) B3141593
theorem B2094455 : Blo 1395517 2094455 := bstep (se 1 (by rfl) ⟨1570841, by rfl⟩ : syracuseStep 2094455 = 3141683) B3141683
theorem B2094479 : Blo 1395517 2094479 := bstep (se 1 (by rfl) ⟨1570859, by rfl⟩ : syracuseStep 2094479 = 3141719) B3141719
theorem B30184883 : Blo 1395517 30184883 := bstep (se 1 (by rfl) ⟨22638662, by rfl⟩ : syracuseStep 30184883 = 45277325) B45277325
theorem B2094521 : Blo 1395517 2094521 := bstep (se 2 (by rfl) ⟨785445, by rfl⟩ : syracuseStep 2094521 = 1570891) B1570891
theorem B6714809 : Blo 1395517 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B2356681 : Blo 1395517 2356681 := bstep (se 2 (by rfl) ⟨883755, by rfl⟩ : syracuseStep 2356681 = 1767511) B1767511
theorem B2094599 : Blo 1395517 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B3536399 : Blo 1395517 3536399 := bstep (se 1 (by rfl) ⟨2652299, by rfl⟩ : syracuseStep 3536399 = 5304599) B5304599
theorem B2094635 : Blo 1395517 2094635 := bstep (se 1 (by rfl) ⟨1570976, by rfl⟩ : syracuseStep 2094635 = 3141953) B3141953
theorem B2651707 : Blo 1395517 2651707 := bstep (se 1 (by rfl) ⟨1988780, by rfl⟩ : syracuseStep 2651707 = 3977561) B3977561
theorem B2094665 : Blo 1395517 2094665 := bstep (se 2 (by rfl) ⟨785499, by rfl⟩ : syracuseStep 2094665 = 1570999) B1570999
theorem B3143303 : Blo 1395517 3143303 := bstep (se 1 (by rfl) ⟨2357477, by rfl⟩ : syracuseStep 3143303 = 4714955) B4714955
theorem B3536531 : Blo 1395517 3536531 := bstep (se 1 (by rfl) ⟨2652398, by rfl⟩ : syracuseStep 3536531 = 5304797) B5304797
theorem B42981043 : Blo 1395517 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B2094779 : Blo 1395517 2094779 := bstep (se 1 (by rfl) ⟨1571084, by rfl⟩ : syracuseStep 2094779 = 3142169) B3142169
theorem B5306057 : Blo 1395517 5306057 := bstep (se 2 (by rfl) ⟨1989771, by rfl⟩ : syracuseStep 5306057 = 3979543) B3979543
theorem B2094839 : Blo 1395517 2094839 := bstep (se 1 (by rfl) ⟨1571129, by rfl⟩ : syracuseStep 2094839 = 3142259) B3142259
theorem B1570567 : Blo 1395517 1570567 := bstep (se 1 (by rfl) ⟨1177925, by rfl⟩ : syracuseStep 1570567 = 2355851) B2355851
theorem B3979019 : Blo 1395517 3979019 := bstep (se 1 (by rfl) ⟨2984264, by rfl⟩ : syracuseStep 3979019 = 5968529) B5968529
theorem B2094863 : Blo 1395517 2094863 := bstep (se 1 (by rfl) ⟨1571147, by rfl⟩ : syracuseStep 2094863 = 3142295) B3142295
theorem B2094905 : Blo 1395517 2094905 := bstep (se 2 (by rfl) ⟨785589, by rfl⟩ : syracuseStep 2094905 = 1571179) B1571179
theorem B3143483 : Blo 1395517 3143483 := bstep (se 1 (by rfl) ⟨2357612, by rfl⟩ : syracuseStep 3143483 = 4715225) B4715225
theorem B2094983 : Blo 1395517 2094983 := bstep (se 1 (by rfl) ⟨1571237, by rfl⟩ : syracuseStep 2094983 = 3142475) B3142475
theorem B2095019 : Blo 1395517 2095019 := bstep (se 1 (by rfl) ⟨1571264, by rfl⟩ : syracuseStep 2095019 = 3142529) B3142529
theorem B3143609 : Blo 1395517 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B1570747 : Blo 1395517 1570747 := bstep (se 1 (by rfl) ⟨1178060, by rfl⟩ : syracuseStep 1570747 = 2356121) B2356121
theorem B2095049 : Blo 1395517 2095049 := bstep (se 2 (by rfl) ⟨785643, by rfl⟩ : syracuseStep 2095049 = 1571287) B1571287
theorem B1767415 : Blo 1395517 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B2652193 : Blo 1395517 2652193 := bstep (se 2 (by rfl) ⟨994572, by rfl⟩ : syracuseStep 2652193 = 1989145) B1989145
theorem B2095163 : Blo 1395517 2095163 := bstep (se 1 (by rfl) ⟨1571372, by rfl⟩ : syracuseStep 2095163 = 3142745) B3142745
theorem B7067735 : Blo 1395517 7067735 := bstep (se 1 (by rfl) ⟨5300801, by rfl⟩ : syracuseStep 7067735 = 10601603) B10601603
theorem B2095223 : Blo 1395517 2095223 := bstep (se 1 (by rfl) ⟨1571417, by rfl⟩ : syracuseStep 2095223 = 3142835) B3142835
theorem B2357383 : Blo 1395517 2357383 := bstep (se 1 (by rfl) ⟨1768037, by rfl⟩ : syracuseStep 2357383 = 3536075) B3536075
theorem B2095247 : Blo 1395517 2095247 := bstep (se 1 (by rfl) ⟨1571435, by rfl⟩ : syracuseStep 2095247 = 3142871) B3142871
theorem B2095289 : Blo 1395517 2095289 := bstep (se 2 (by rfl) ⟨785733, by rfl⟩ : syracuseStep 2095289 = 1571467) B1571467
theorem B3184841 : Blo 1395517 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B2095367 : Blo 1395517 2095367 := bstep (se 1 (by rfl) ⟨1571525, by rfl⟩ : syracuseStep 2095367 = 3143051) B3143051
theorem B3143951 : Blo 1395517 3143951 := bstep (se 1 (by rfl) ⟨2357963, by rfl⟩ : syracuseStep 3143951 = 4715927) B4715927
theorem B3143969 : Blo 1395517 3143969 := bstep (se 2 (by rfl) ⟨1178988, by rfl⟩ : syracuseStep 3143969 = 2357977) B2357977
theorem B2095403 : Blo 1395517 2095403 := bstep (se 1 (by rfl) ⟨1571552, by rfl⟩ : syracuseStep 2095403 = 3143105) B3143105
theorem B1767739 : Blo 1395517 1767739 := bstep (se 1 (by rfl) ⟨1325804, by rfl⟩ : syracuseStep 1767739 = 2651609) B2651609
theorem B2095433 : Blo 1395517 2095433 := bstep (se 2 (by rfl) ⟨785787, by rfl⟩ : syracuseStep 2095433 = 1571575) B1571575
theorem B1571215 : Blo 1395517 1571215 := bstep (se 1 (by rfl) ⟨1178411, by rfl⟩ : syracuseStep 1571215 = 2356823) B2356823
theorem B2095547 : Blo 1395517 2095547 := bstep (se 1 (by rfl) ⟨1571660, by rfl⟩ : syracuseStep 2095547 = 3143321) B3143321
theorem B7952843 : Blo 1395517 7952843 := bstep (se 1 (by rfl) ⟨5964632, by rfl⟩ : syracuseStep 7952843 = 11929265) B11929265
theorem B2095607 : Blo 1395517 2095607 := bstep (se 1 (by rfl) ⟨1571705, by rfl⟩ : syracuseStep 2095607 = 3143411) B3143411
theorem B15104515 : Blo 1395517 15104515 := bstep (se 1 (by rfl) ⟨11328386, by rfl⟩ : syracuseStep 15104515 = 22656773) B22656773
theorem B1792519 : Blo 1395517 1792519 := bstep (se 1 (by rfl) ⟨1344389, by rfl⟩ : syracuseStep 1792519 = 2688779) B2688779
theorem B2095631 : Blo 1395517 2095631 := bstep (se 1 (by rfl) ⟨1571723, by rfl⟩ : syracuseStep 2095631 = 3143447) B3143447
theorem B6707735 : Blo 1395517 6707735 := bstep (se 1 (by rfl) ⟨5030801, by rfl⟩ : syracuseStep 6707735 = 10061603) B10061603
theorem B2095673 : Blo 1395517 2095673 := bstep (se 2 (by rfl) ⟨785877, by rfl⟩ : syracuseStep 2095673 = 1571755) B1571755
theorem B7068221 : Blo 1395517 7068221 := bstep (se 3 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 7068221 = 2650583) B2650583
theorem B2980471 : Blo 1395517 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B3144311 : Blo 1395517 3144311 := bstep (se 1 (by rfl) ⟨2358233, by rfl⟩ : syracuseStep 3144311 = 4716467) B4716467
theorem B2095751 : Blo 1395517 2095751 := bstep (se 1 (by rfl) ⟨1571813, by rfl⟩ : syracuseStep 2095751 = 3143627) B3143627
theorem B2095787 : Blo 1395517 2095787 := bstep (se 1 (by rfl) ⟨1571840, by rfl⟩ : syracuseStep 2095787 = 3143681) B3143681
theorem B8493761 : Blo 1395517 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B13605569 : Blo 1395517 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B265149125 : Blo 1395517 265149125 := bstep (se 4 (by rfl) ⟨24857730, by rfl⟩ : syracuseStep 265149125 = 49715461) B49715461
theorem B2095817 : Blo 1395517 2095817 := bstep (se 2 (by rfl) ⟨785931, by rfl⟩ : syracuseStep 2095817 = 1571863) B1571863
theorem B1678087 : Blo 1395517 1678087 := bstep (se 1 (by rfl) ⟨1258565, by rfl⟩ : syracuseStep 1678087 = 2517131) B2517131
theorem B20142863 : Blo 1395517 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B2358031 : Blo 1395517 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B2095931 : Blo 1395517 2095931 := bstep (se 1 (by rfl) ⟨1571948, by rfl⟩ : syracuseStep 2095931 = 3143897) B3143897
theorem B2095991 : Blo 1395517 2095991 := bstep (se 1 (by rfl) ⟨1571993, by rfl⟩ : syracuseStep 2095991 = 3143987) B3143987
theorem B1571719 : Blo 1395517 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B2096015 : Blo 1395517 2096015 := bstep (se 1 (by rfl) ⟨1572011, by rfl⟩ : syracuseStep 2096015 = 3144023) B3144023
theorem B5372819 : Blo 1395517 5372819 := bstep (se 1 (by rfl) ⟨4029614, by rfl⟩ : syracuseStep 5372819 = 8059229) B8059229
theorem B7953299 : Blo 1395517 7953299 := bstep (se 1 (by rfl) ⟨5964974, by rfl⟩ : syracuseStep 7953299 = 11929949) B11929949
theorem B3357587 : Blo 1395517 3357587 := bstep (se 1 (by rfl) ⟨2518190, by rfl⟩ : syracuseStep 3357587 = 5036381) B5036381
theorem B2096057 : Blo 1395517 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B40811525 : Blo 1395517 40811525 := bstep (se 4 (by rfl) ⟨3826080, by rfl⟩ : syracuseStep 40811525 = 7652161) B7652161
theorem B2096135 : Blo 1395517 2096135 := bstep (se 1 (by rfl) ⟨1572101, by rfl⟩ : syracuseStep 2096135 = 3144203) B3144203
theorem B7167005 : Blo 1395517 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B2096171 : Blo 1395517 2096171 := bstep (se 1 (by rfl) ⟨1572128, by rfl⟩ : syracuseStep 2096171 = 3144257) B3144257
theorem B1571899 : Blo 1395517 1571899 := bstep (se 1 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 1571899 = 2357849) B2357849
theorem B2096201 : Blo 1395517 2096201 := bstep (se 2 (by rfl) ⟨786075, by rfl⟩ : syracuseStep 2096201 = 1572151) B1572151
theorem B2014409 : Blo 1395517 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B1768711 : Blo 1395517 1768711 := bstep (se 1 (by rfl) ⟨1326533, by rfl⟩ : syracuseStep 1768711 = 2653067) B2653067
theorem B4775183 : Blo 1395517 4775183 := bstep (se 1 (by rfl) ⟨3581387, by rfl⟩ : syracuseStep 4775183 = 7162775) B7162775
theorem B6045043 : Blo 1395517 6045043 := bstep (se 1 (by rfl) ⟨4533782, by rfl⟩ : syracuseStep 6045043 = 9067565) B9067565
theorem B16981433 : Blo 1395517 16981433 := bstep (se 2 (by rfl) ⟨6368037, by rfl⟩ : syracuseStep 16981433 = 12736075) B12736075
theorem B5660171 : Blo 1395517 5660171 := bstep (se 1 (by rfl) ⟨4245128, by rfl⟩ : syracuseStep 5660171 = 8490257) B8490257
theorem B5029577 : Blo 1395517 5029577 := bstep (se 2 (by rfl) ⟨1886091, by rfl⟩ : syracuseStep 5029577 = 3772183) B3772183
theorem B8060705 : Blo 1395517 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B4710203 : Blo 1395517 4710203 := bstep (se 1 (by rfl) ⟨3532652, by rfl⟩ : syracuseStep 4710203 = 7065305) B7065305
theorem B8953715 : Blo 1395517 8953715 := bstep (se 1 (by rfl) ⟨6715286, by rfl⟩ : syracuseStep 8953715 = 13430573) B13430573
theorem B5300225 : Blo 1395517 5300225 := bstep (se 2 (by rfl) ⟨1987584, by rfl⟩ : syracuseStep 5300225 = 3975169) B3975169
theorem B4710419 : Blo 1395517 4710419 := bstep (se 1 (by rfl) ⟨3532814, by rfl⟩ : syracuseStep 4710419 = 7065629) B7065629
theorem B9560101 : Blo 1395517 9560101 := bstep (se 4 (by rfl) ⟨896259, by rfl⟩ : syracuseStep 9560101 = 1792519) B1792519
theorem B4472911 : Blo 1395517 4472911 := bstep (se 1 (by rfl) ⟨3354683, by rfl⟩ : syracuseStep 4472911 = 6709367) B6709367
theorem B4710743 : Blo 1395517 4710743 := bstep (se 1 (by rfl) ⟨3533057, by rfl⟩ : syracuseStep 4710743 = 7066115) B7066115
theorem B1491295 : Blo 1395517 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B40264037 : Blo 1395517 40264037 := bstep (se 4 (by rfl) ⟨3774753, by rfl⟩ : syracuseStep 40264037 = 7549507) B7549507
theorem B2515465 : Blo 1395517 2515465 := bstep (se 2 (by rfl) ⟨943299, by rfl⟩ : syracuseStep 2515465 = 1886599) B1886599
theorem B9069079 : Blo 1395517 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B17908249 : Blo 1395517 17908249 := bstep (se 2 (by rfl) ⟨6715593, by rfl⟩ : syracuseStep 17908249 = 13431187) B13431187
theorem B2515495 : Blo 1395517 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B4776659 : Blo 1395517 4776659 := bstep (se 1 (by rfl) ⟨3582494, by rfl⟩ : syracuseStep 4776659 = 7164989) B7164989
theorem B3973961 : Blo 1395517 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B5964617 : Blo 1395517 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B4711823 : Blo 1395517 4711823 := bstep (se 1 (by rfl) ⟨3533867, by rfl⟩ : syracuseStep 4711823 = 7067735) B7067735
theorem B2123227 : Blo 1395517 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B2983547 : Blo 1395517 2983547 := bstep (se 1 (by rfl) ⟨2237660, by rfl⟩ : syracuseStep 2983547 = 4475321) B4475321
theorem B5301895 : Blo 1395517 5301895 := bstep (se 1 (by rfl) ⟨3976421, by rfl⟩ : syracuseStep 5301895 = 7952843) B7952843
theorem B4712147 : Blo 1395517 4712147 := bstep (se 1 (by rfl) ⟨3534110, by rfl⟩ : syracuseStep 4712147 = 7068221) B7068221
theorem B9070379 : Blo 1395517 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B13428575 : Blo 1395517 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B7948151 : Blo 1395517 7948151 := bstep (se 1 (by rfl) ⟨5961113, by rfl⟩ : syracuseStep 7948151 = 11922227) B11922227
theorem B32237473 : Blo 1395517 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B3581879 : Blo 1395517 3581879 := bstep (se 1 (by rfl) ⟨2686409, by rfl⟩ : syracuseStep 3581879 = 5372819) B5372819
theorem B5302199 : Blo 1395517 5302199 := bstep (se 1 (by rfl) ⟨3976649, by rfl⟩ : syracuseStep 5302199 = 7953299) B7953299
theorem B2238391 : Blo 1395517 2238391 := bstep (se 1 (by rfl) ⟨1678793, by rfl⟩ : syracuseStep 2238391 = 3357587) B3357587
theorem B27207683 : Blo 1395517 27207683 := bstep (se 1 (by rfl) ⟨20405762, by rfl⟩ : syracuseStep 27207683 = 40811525) B40811525
theorem B4778003 : Blo 1395517 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B81619265 : Blo 1395517 81619265 := bstep (se 2 (by rfl) ⟨30607224, by rfl⟩ : syracuseStep 81619265 = 61214449) B61214449
theorem B3828097 : Blo 1395517 3828097 := bstep (se 2 (by rfl) ⟨1435536, by rfl⟩ : syracuseStep 3828097 = 2871073) B2871073
theorem B7268737 : Blo 1395517 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B3353051 : Blo 1395517 3353051 := bstep (se 1 (by rfl) ⟨2514788, by rfl⟩ : syracuseStep 3353051 = 5029577) B5029577
theorem B3533321 : Blo 1395517 3533321 := bstep (se 2 (by rfl) ⟨1324995, by rfl⟩ : syracuseStep 3533321 = 2649991) B2649991
theorem B10742305 : Blo 1395517 10742305 := bstep (se 2 (by rfl) ⟨4028364, by rfl⟩ : syracuseStep 10742305 = 8056729) B8056729
theorem B3140135 : Blo 1395517 3140135 := bstep (se 1 (by rfl) ⟨2355101, by rfl⟩ : syracuseStep 3140135 = 4710203) B4710203
theorem B40241893 : Blo 1395517 40241893 := bstep (se 4 (by rfl) ⟨3772677, by rfl⟩ : syracuseStep 40241893 = 7545355) B7545355
theorem B1395535 : Blo 1395517 1395535 := bstep (se 1 (by rfl) ⟨1046651, by rfl⟩ : syracuseStep 1395535 = 2093303) B2093303
theorem B1395551 : Blo 1395517 1395551 := bstep (se 1 (by rfl) ⟨1046663, by rfl⟩ : syracuseStep 1395551 = 2093327) B2093327
theorem B3140459 : Blo 1395517 3140459 := bstep (se 1 (by rfl) ⟨2355344, by rfl⟩ : syracuseStep 3140459 = 4710689) B4710689
theorem B1395579 : Blo 1395517 1395579 := bstep (se 1 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 1395579 = 2093369) B2093369
theorem B4713335 : Blo 1395517 4713335 := bstep (se 1 (by rfl) ⟨3535001, by rfl⟩ : syracuseStep 4713335 = 7070003) B7070003
theorem B3140513 : Blo 1395517 3140513 := bstep (se 2 (by rfl) ⟨1177692, by rfl⟩ : syracuseStep 3140513 = 2355385) B2355385
theorem B1395631 : Blo 1395517 1395631 := bstep (se 1 (by rfl) ⟨1046723, by rfl⟩ : syracuseStep 1395631 = 2093447) B2093447
theorem B1395655 : Blo 1395517 1395655 := bstep (se 1 (by rfl) ⟨1046741, by rfl⟩ : syracuseStep 1395655 = 2093483) B2093483
theorem B1395675 : Blo 1395517 1395675 := bstep (se 1 (by rfl) ⟨1046756, by rfl⟩ : syracuseStep 1395675 = 2093513) B2093513
theorem B1395751 : Blo 1395517 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B5303353 : Blo 1395517 5303353 := bstep (se 2 (by rfl) ⟨1988757, by rfl⟩ : syracuseStep 5303353 = 3977515) B3977515
theorem B1395791 : Blo 1395517 1395791 := bstep (se 1 (by rfl) ⟨1046843, by rfl⟩ : syracuseStep 1395791 = 2093687) B2093687
theorem B4713551 : Blo 1395517 4713551 := bstep (se 1 (by rfl) ⟨3535163, by rfl⟩ : syracuseStep 4713551 = 7070327) B7070327
theorem B1395807 : Blo 1395517 1395807 := bstep (se 1 (by rfl) ⟨1046855, by rfl⟩ : syracuseStep 1395807 = 2093711) B2093711
theorem B1395835 : Blo 1395517 1395835 := bstep (se 1 (by rfl) ⟨1046876, by rfl⟩ : syracuseStep 1395835 = 2093753) B2093753
theorem B4246685 : Blo 1395517 4246685 := bstep (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) B1592507
theorem B1395887 : Blo 1395517 1395887 := bstep (se 1 (by rfl) ⟨1046915, by rfl⟩ : syracuseStep 1395887 = 2093831) B2093831
theorem B1395911 : Blo 1395517 1395911 := bstep (se 1 (by rfl) ⟨1046933, by rfl⟩ : syracuseStep 1395911 = 2093867) B2093867
theorem B1395931 : Blo 1395517 1395931 := bstep (se 1 (by rfl) ⟨1046948, by rfl⟩ : syracuseStep 1395931 = 2093897) B2093897
theorem B3140855 : Blo 1395517 3140855 := bstep (se 1 (by rfl) ⟨2355641, by rfl⟩ : syracuseStep 3140855 = 4711283) B4711283
theorem B40267043 : Blo 1395517 40267043 := bstep (se 1 (by rfl) ⟨30200282, by rfl⟩ : syracuseStep 40267043 = 60400565) B60400565
theorem B1396007 : Blo 1395517 1396007 := bstep (se 1 (by rfl) ⟨1047005, by rfl⟩ : syracuseStep 1396007 = 2094011) B2094011
theorem B1396047 : Blo 1395517 1396047 := bstep (se 1 (by rfl) ⟨1047035, by rfl⟩ : syracuseStep 1396047 = 2094071) B2094071
theorem B20139353 : Blo 1395517 20139353 := bstep (se 2 (by rfl) ⟨7552257, by rfl⟩ : syracuseStep 20139353 = 15104515) B15104515
theorem B1396063 : Blo 1395517 1396063 := bstep (se 1 (by rfl) ⟨1047047, by rfl⟩ : syracuseStep 1396063 = 2094095) B2094095
theorem B5303657 : Blo 1395517 5303657 := bstep (se 2 (by rfl) ⟨1988871, by rfl⟩ : syracuseStep 5303657 = 3977743) B3977743
theorem B1396091 : Blo 1395517 1396091 := bstep (se 1 (by rfl) ⟨1047068, by rfl⟩ : syracuseStep 1396091 = 2094137) B2094137
theorem B5664143 : Blo 1395517 5664143 := bstep (se 1 (by rfl) ⟨4248107, by rfl⟩ : syracuseStep 5664143 = 8496215) B8496215
theorem B2649505 : Blo 1395517 2649505 := bstep (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) B1987129
theorem B7957925 : Blo 1395517 7957925 := bstep (se 4 (by rfl) ⟨746055, by rfl⟩ : syracuseStep 7957925 = 1492111) B1492111
theorem B1396143 : Blo 1395517 1396143 := bstep (se 1 (by rfl) ⟨1047107, by rfl⟩ : syracuseStep 1396143 = 2094215) B2094215
theorem B1396167 : Blo 1395517 1396167 := bstep (se 1 (by rfl) ⟨1047125, by rfl⟩ : syracuseStep 1396167 = 2094251) B2094251
theorem B4713929 : Blo 1395517 4713929 := bstep (se 2 (by rfl) ⟨1767723, by rfl⟩ : syracuseStep 4713929 = 3535447) B3535447
theorem B1396187 : Blo 1395517 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B7073243 : Blo 1395517 7073243 := bstep (se 1 (by rfl) ⟨5304932, by rfl⟩ : syracuseStep 7073243 = 10609865) B10609865
theorem B1396263 : Blo 1395517 1396263 := bstep (se 1 (by rfl) ⟨1047197, by rfl⟩ : syracuseStep 1396263 = 2094395) B2094395
theorem B1396303 : Blo 1395517 1396303 := bstep (se 1 (by rfl) ⟨1047227, by rfl⟩ : syracuseStep 1396303 = 2094455) B2094455
theorem B1396319 : Blo 1395517 1396319 := bstep (se 1 (by rfl) ⟨1047239, by rfl⟩ : syracuseStep 1396319 = 2094479) B2094479
theorem B20123255 : Blo 1395517 20123255 := bstep (se 1 (by rfl) ⟨15092441, by rfl⟩ : syracuseStep 20123255 = 30184883) B30184883
theorem B1396347 : Blo 1395517 1396347 := bstep (se 1 (by rfl) ⟨1047260, by rfl⟩ : syracuseStep 1396347 = 2094521) B2094521
theorem B4476539 : Blo 1395517 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B3534475 : Blo 1395517 3534475 := bstep (se 1 (by rfl) ⟨2650856, by rfl⟩ : syracuseStep 3534475 = 5301713) B5301713
theorem B1396399 : Blo 1395517 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B1396423 : Blo 1395517 1396423 := bstep (se 1 (by rfl) ⟨1047317, by rfl⟩ : syracuseStep 1396423 = 2094635) B2094635
theorem B5664467 : Blo 1395517 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B4714199 : Blo 1395517 4714199 := bstep (se 1 (by rfl) ⟨3535649, by rfl⟩ : syracuseStep 4714199 = 7071299) B7071299
theorem B1396443 : Blo 1395517 1396443 := bstep (se 1 (by rfl) ⟨1047332, by rfl⟩ : syracuseStep 1396443 = 2094665) B2094665
theorem B2649847 : Blo 1395517 2649847 := bstep (se 1 (by rfl) ⟨1987385, by rfl⟩ : syracuseStep 2649847 = 3974771) B3974771
theorem B10751737 : Blo 1395517 10751737 := bstep (se 2 (by rfl) ⟨4031901, by rfl⟩ : syracuseStep 10751737 = 8063803) B8063803
theorem B1396519 : Blo 1395517 1396519 := bstep (se 1 (by rfl) ⟨1047389, by rfl⟩ : syracuseStep 1396519 = 2094779) B2094779
theorem B3141449 : Blo 1395517 3141449 := bstep (se 2 (by rfl) ⟨1178043, by rfl⟩ : syracuseStep 3141449 = 2356087) B2356087
theorem B1396559 : Blo 1395517 1396559 := bstep (se 1 (by rfl) ⟨1047419, by rfl⟩ : syracuseStep 1396559 = 2094839) B2094839
theorem B1396575 : Blo 1395517 1396575 := bstep (se 1 (by rfl) ⟨1047431, by rfl⟩ : syracuseStep 1396575 = 2094863) B2094863
theorem B2551657 : Blo 1395517 2551657 := bstep (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) B1913743
theorem B1396603 : Blo 1395517 1396603 := bstep (se 1 (by rfl) ⟨1047452, by rfl⟩ : syracuseStep 1396603 = 2094905) B2094905
theorem B1396655 : Blo 1395517 1396655 := bstep (se 1 (by rfl) ⟨1047491, by rfl⟩ : syracuseStep 1396655 = 2094983) B2094983
theorem B4714415 : Blo 1395517 4714415 := bstep (se 1 (by rfl) ⟨3535811, by rfl⟩ : syracuseStep 4714415 = 7071623) B7071623
theorem B3534779 : Blo 1395517 3534779 := bstep (se 1 (by rfl) ⟨2651084, by rfl⟩ : syracuseStep 3534779 = 5302169) B5302169
theorem B7073729 : Blo 1395517 7073729 := bstep (se 2 (by rfl) ⟨2652648, by rfl⟩ : syracuseStep 7073729 = 5305297) B5305297
theorem B1396679 : Blo 1395517 1396679 := bstep (se 1 (by rfl) ⟨1047509, by rfl⟩ : syracuseStep 1396679 = 2095019) B2095019
theorem B1396699 : Blo 1395517 1396699 := bstep (se 1 (by rfl) ⟨1047524, by rfl⟩ : syracuseStep 1396699 = 2095049) B2095049
theorem B8949797 : Blo 1395517 8949797 := bstep (se 4 (by rfl) ⟨839043, by rfl⟩ : syracuseStep 8949797 = 1678087) B1678087
theorem B2650151 : Blo 1395517 2650151 := bstep (se 1 (by rfl) ⟨1987613, by rfl⟩ : syracuseStep 2650151 = 3975227) B3975227
theorem B1396775 : Blo 1395517 1396775 := bstep (se 1 (by rfl) ⟨1047581, by rfl⟩ : syracuseStep 1396775 = 2095163) B2095163
theorem B2355257 : Blo 1395517 2355257 := bstep (se 2 (by rfl) ⟨883221, by rfl⟩ : syracuseStep 2355257 = 1766443) B1766443
theorem B11931725 : Blo 1395517 11931725 := bstep (se 3 (by rfl) ⟨2237198, by rfl⟩ : syracuseStep 11931725 = 4474397) B4474397
theorem B1396815 : Blo 1395517 1396815 := bstep (se 1 (by rfl) ⟨1047611, by rfl⟩ : syracuseStep 1396815 = 2095223) B2095223
theorem B1396831 : Blo 1395517 1396831 := bstep (se 1 (by rfl) ⟨1047623, by rfl⟩ : syracuseStep 1396831 = 2095247) B2095247
theorem B1396859 : Blo 1395517 1396859 := bstep (se 1 (by rfl) ⟨1047644, by rfl⟩ : syracuseStep 1396859 = 2095289) B2095289
theorem B1396911 : Blo 1395517 1396911 := bstep (se 1 (by rfl) ⟨1047683, by rfl⟩ : syracuseStep 1396911 = 2095367) B2095367
theorem B1396935 : Blo 1395517 1396935 := bstep (se 1 (by rfl) ⟨1047701, by rfl⟩ : syracuseStep 1396935 = 2095403) B2095403
theorem B2830547 : Blo 1395517 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B1396955 : Blo 1395517 1396955 := bstep (se 1 (by rfl) ⟨1047716, by rfl⟩ : syracuseStep 1396955 = 2095433) B2095433
theorem B1397031 : Blo 1395517 1397031 := bstep (se 1 (by rfl) ⟨1047773, by rfl⟩ : syracuseStep 1397031 = 2095547) B2095547
theorem B1397071 : Blo 1395517 1397071 := bstep (se 1 (by rfl) ⟨1047803, by rfl⟩ : syracuseStep 1397071 = 2095607) B2095607
theorem B1397087 : Blo 1395517 1397087 := bstep (se 1 (by rfl) ⟨1047815, by rfl⟩ : syracuseStep 1397087 = 2095631) B2095631
theorem B2093417 : Blo 1395517 2093417 := bstep (se 2 (by rfl) ⟨785031, by rfl⟩ : syracuseStep 2093417 = 1570063) B1570063
theorem B1397115 : Blo 1395517 1397115 := bstep (se 1 (by rfl) ⟨1047836, by rfl⟩ : syracuseStep 1397115 = 2095673) B2095673
theorem B1397167 : Blo 1395517 1397167 := bstep (se 1 (by rfl) ⟨1047875, by rfl⟩ : syracuseStep 1397167 = 2095751) B2095751
theorem B2093495 : Blo 1395517 2093495 := bstep (se 1 (by rfl) ⟨1570121, by rfl⟩ : syracuseStep 2093495 = 3140243) B3140243
theorem B1397191 : Blo 1395517 1397191 := bstep (se 1 (by rfl) ⟨1047893, by rfl⟩ : syracuseStep 1397191 = 2095787) B2095787
theorem B2093531 : Blo 1395517 2093531 := bstep (se 1 (by rfl) ⟨1570148, by rfl⟩ : syracuseStep 2093531 = 3140297) B3140297
theorem B1397211 : Blo 1395517 1397211 := bstep (se 1 (by rfl) ⟨1047908, by rfl⟩ : syracuseStep 1397211 = 2095817) B2095817
theorem B1397287 : Blo 1395517 1397287 := bstep (se 1 (by rfl) ⟨1047965, by rfl⟩ : syracuseStep 1397287 = 2095931) B2095931
theorem B1397327 : Blo 1395517 1397327 := bstep (se 1 (by rfl) ⟨1047995, by rfl⟩ : syracuseStep 1397327 = 2095991) B2095991
theorem B1397343 : Blo 1395517 1397343 := bstep (se 1 (by rfl) ⟨1048007, by rfl⟩ : syracuseStep 1397343 = 2096015) B2096015
theorem B3142241 : Blo 1395517 3142241 := bstep (se 2 (by rfl) ⟨1178340, by rfl⟩ : syracuseStep 3142241 = 2356681) B2356681
theorem B1397371 : Blo 1395517 1397371 := bstep (se 1 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 1397371 = 2096057) B2096057
theorem B1397423 : Blo 1395517 1397423 := bstep (se 1 (by rfl) ⟨1048067, by rfl⟩ : syracuseStep 1397423 = 2096135) B2096135
theorem B3535559 : Blo 1395517 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B1397447 : Blo 1395517 1397447 := bstep (se 1 (by rfl) ⟨1048085, by rfl⟩ : syracuseStep 1397447 = 2096171) B2096171
theorem B1397467 : Blo 1395517 1397467 := bstep (se 1 (by rfl) ⟨1048100, by rfl⟩ : syracuseStep 1397467 = 2096201) B2096201
theorem B2355959 : Blo 1395517 2355959 := bstep (se 1 (by rfl) ⟨1766969, by rfl⟩ : syracuseStep 2355959 = 3533939) B3533939
theorem B3535609 : Blo 1395517 3535609 := bstep (se 2 (by rfl) ⟨1325853, by rfl⟩ : syracuseStep 3535609 = 2651707) B2651707
theorem B3183455 : Blo 1395517 3183455 := bstep (se 1 (by rfl) ⟨2387591, by rfl⟩ : syracuseStep 3183455 = 4775183) B4775183
theorem B16118635 : Blo 1395517 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B57308057 : Blo 1395517 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B2093999 : Blo 1395517 2093999 := bstep (se 1 (by rfl) ⟨1570499, by rfl⟩ : syracuseStep 2093999 = 3140999) B3140999
theorem B3142583 : Blo 1395517 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B3773447 : Blo 1395517 3773447 := bstep (se 1 (by rfl) ⟨2830085, by rfl⟩ : syracuseStep 3773447 = 5660171) B5660171
theorem B2094089 : Blo 1395517 2094089 := bstep (se 2 (by rfl) ⟨785283, by rfl⟩ : syracuseStep 2094089 = 1570567) B1570567
theorem B2094119 : Blo 1395517 2094119 := bstep (se 1 (by rfl) ⟨1570589, by rfl⟩ : syracuseStep 2094119 = 3141179) B3141179
theorem B2356303 : Blo 1395517 2356303 := bstep (se 1 (by rfl) ⟨1767227, by rfl⟩ : syracuseStep 2356303 = 3534455) B3534455
theorem B2094203 : Blo 1395517 2094203 := bstep (se 1 (by rfl) ⟨1570652, by rfl⟩ : syracuseStep 2094203 = 3141305) B3141305
theorem B1569991 : Blo 1395517 1569991 := bstep (se 1 (by rfl) ⟨1177493, by rfl⟩ : syracuseStep 1569991 = 2354987) B2354987
theorem B5969143 : Blo 1395517 5969143 := bstep (se 1 (by rfl) ⟨4476857, by rfl⟩ : syracuseStep 5969143 = 8953715) B8953715
theorem B2094329 : Blo 1395517 2094329 := bstep (se 2 (by rfl) ⟨785373, by rfl⟩ : syracuseStep 2094329 = 1570747) B1570747
theorem B2356553 : Blo 1395517 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B2094431 : Blo 1395517 2094431 := bstep (se 1 (by rfl) ⟨1570823, by rfl⟩ : syracuseStep 2094431 = 3141647) B3141647
theorem B2094443 : Blo 1395517 2094443 := bstep (se 1 (by rfl) ⟨1570832, by rfl⟩ : syracuseStep 2094443 = 3141665) B3141665
theorem B3536257 : Blo 1395517 3536257 := bstep (se 2 (by rfl) ⟨1326096, by rfl⟩ : syracuseStep 3536257 = 2652193) B2652193
theorem B6706675 : Blo 1395517 6706675 := bstep (se 1 (by rfl) ⟨5030006, by rfl⟩ : syracuseStep 6706675 = 10060013) B10060013
theorem B23868917 : Blo 1395517 23868917 := bstep (se 5 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 23868917 = 2237711) B2237711
theorem B3143177 : Blo 1395517 3143177 := bstep (se 2 (by rfl) ⟨1178691, by rfl⟩ : syracuseStep 3143177 = 2357383) B2357383
theorem B3978791 : Blo 1395517 3978791 := bstep (se 1 (by rfl) ⟨2984093, by rfl⟩ : syracuseStep 3978791 = 5968187) B5968187
theorem B2094671 : Blo 1395517 2094671 := bstep (se 1 (by rfl) ⟨1571003, by rfl⟩ : syracuseStep 2094671 = 3142007) B3142007
theorem B1767035 : Blo 1395517 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B9557693 : Blo 1395517 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B2094791 : Blo 1395517 2094791 := bstep (se 1 (by rfl) ⟨1571093, by rfl⟩ : syracuseStep 2094791 = 3142187) B3142187
theorem B7952093 : Blo 1395517 7952093 := bstep (se 3 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 7952093 = 2982035) B2982035
theorem B2356985 : Blo 1395517 2356985 := bstep (se 2 (by rfl) ⟨883869, by rfl⟩ : syracuseStep 2356985 = 1767739) B1767739
theorem B30218021 : Blo 1395517 30218021 := bstep (se 4 (by rfl) ⟨2832939, by rfl⟩ : syracuseStep 30218021 = 5665879) B5665879
theorem B3143519 : Blo 1395517 3143519 := bstep (se 1 (by rfl) ⟨2357639, by rfl⟩ : syracuseStep 3143519 = 4715279) B4715279
theorem B2094953 : Blo 1395517 2094953 := bstep (se 2 (by rfl) ⟨785607, by rfl⟩ : syracuseStep 2094953 = 1571215) B1571215
theorem B2652011 : Blo 1395517 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B5371757 : Blo 1395517 5371757 := bstep (se 3 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 5371757 = 2014409) B2014409
theorem B6043553 : Blo 1395517 6043553 := bstep (se 2 (by rfl) ⟨2266332, by rfl⟩ : syracuseStep 6043553 = 4532665) B4532665
theorem B2357167 : Blo 1395517 2357167 := bstep (se 1 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 2357167 = 3535751) B3535751
theorem B2095031 : Blo 1395517 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B6707137 : Blo 1395517 6707137 := bstep (se 2 (by rfl) ⟨2515176, by rfl⟩ : syracuseStep 6707137 = 5030353) B5030353
theorem B2095067 : Blo 1395517 2095067 := bstep (se 1 (by rfl) ⟨1571300, by rfl⟩ : syracuseStep 2095067 = 3142601) B3142601
theorem B16979971 : Blo 1395517 16979971 := bstep (se 1 (by rfl) ⟨12734978, by rfl⟩ : syracuseStep 16979971 = 25469957) B25469957
theorem B6043655 : Blo 1395517 6043655 := bstep (se 1 (by rfl) ⟨4532741, by rfl⟩ : syracuseStep 6043655 = 9065483) B9065483
theorem B2357255 : Blo 1395517 2357255 := bstep (se 1 (by rfl) ⟨1767941, by rfl⟩ : syracuseStep 2357255 = 3535883) B3535883
theorem B3143699 : Blo 1395517 3143699 := bstep (se 1 (by rfl) ⟨2357774, by rfl⟩ : syracuseStep 3143699 = 4715549) B4715549
theorem B1570855 : Blo 1395517 1570855 := bstep (se 1 (by rfl) ⟨1178141, by rfl⟩ : syracuseStep 1570855 = 2356283) B2356283
theorem B2652239 : Blo 1395517 2652239 := bstep (se 1 (by rfl) ⟨1989179, by rfl⟩ : syracuseStep 2652239 = 3978359) B3978359
theorem B3537067 : Blo 1395517 3537067 := bstep (se 1 (by rfl) ⟨2652800, by rfl⟩ : syracuseStep 3537067 = 5305601) B5305601
theorem B2357599 : Blo 1395517 2357599 := bstep (se 1 (by rfl) ⟨1768199, by rfl⟩ : syracuseStep 2357599 = 3536399) B3536399
theorem B3144041 : Blo 1395517 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B21502343 : Blo 1395517 21502343 := bstep (se 1 (by rfl) ⟨16126757, by rfl⟩ : syracuseStep 21502343 = 32253515) B32253515
theorem B2095535 : Blo 1395517 2095535 := bstep (se 1 (by rfl) ⟨1571651, by rfl⟩ : syracuseStep 2095535 = 3143303) B3143303
theorem B2357687 : Blo 1395517 2357687 := bstep (se 1 (by rfl) ⟨1768265, by rfl⟩ : syracuseStep 2357687 = 3536531) B3536531
theorem B3537371 : Blo 1395517 3537371 := bstep (se 1 (by rfl) ⟨2653028, by rfl⟩ : syracuseStep 3537371 = 5306057) B5306057
theorem B5036525 : Blo 1395517 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B2095625 : Blo 1395517 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B2652679 : Blo 1395517 2652679 := bstep (se 1 (by rfl) ⟨1989509, by rfl⟩ : syracuseStep 2652679 = 3979019) B3979019
theorem B2095655 : Blo 1395517 2095655 := bstep (se 1 (by rfl) ⟨1571741, by rfl⟩ : syracuseStep 2095655 = 3143483) B3143483
theorem B2095739 : Blo 1395517 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B3775187 : Blo 1395517 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B2095865 : Blo 1395517 2095865 := bstep (se 2 (by rfl) ⟨785949, by rfl⟩ : syracuseStep 2095865 = 1571899) B1571899
theorem B86055695 : Blo 1395517 86055695 := bstep (se 1 (by rfl) ⟨64541771, by rfl⟩ : syracuseStep 86055695 = 129083543) B129083543
theorem B2095967 : Blo 1395517 2095967 := bstep (se 1 (by rfl) ⟨1571975, by rfl⟩ : syracuseStep 2095967 = 3143951) B3143951
theorem B2095979 : Blo 1395517 2095979 := bstep (se 1 (by rfl) ⟨1571984, by rfl⟩ : syracuseStep 2095979 = 3143969) B3143969
theorem B2358281 : Blo 1395517 2358281 := bstep (se 2 (by rfl) ⟨884355, by rfl⟩ : syracuseStep 2358281 = 1768711) B1768711
theorem B4471823 : Blo 1395517 4471823 := bstep (se 1 (by rfl) ⟨3353867, by rfl⟩ : syracuseStep 4471823 = 6707735) B6707735
theorem B2235431 : Blo 1395517 2235431 := bstep (se 1 (by rfl) ⟨1676573, by rfl⟩ : syracuseStep 2235431 = 3353147) B3353147
theorem B2907215 : Blo 1395517 2907215 := bstep (se 1 (by rfl) ⟨2180411, by rfl⟩ : syracuseStep 2907215 = 4360823) B4360823
theorem B2096207 : Blo 1395517 2096207 := bstep (se 1 (by rfl) ⟨1572155, by rfl⟩ : syracuseStep 2096207 = 3144311) B3144311
theorem B176766083 : Blo 1395517 176766083 := bstep (se 1 (by rfl) ⟨132574562, by rfl⟩ : syracuseStep 176766083 = 265149125) B265149125
theorem B8060057 : Blo 1395517 8060057 := bstep (se 2 (by rfl) ⟨3022521, by rfl⟩ : syracuseStep 8060057 = 6045043) B6045043
theorem B22650029 : Blo 1395517 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B11320955 : Blo 1395517 11320955 := bstep (se 1 (by rfl) ⟨8490716, by rfl⟩ : syracuseStep 11320955 = 16981433) B16981433
theorem B3776215 : Blo 1395517 3776215 := bstep (se 1 (by rfl) ⟨2832161, by rfl⟩ : syracuseStep 3776215 = 5664323) B5664323
theorem B2014969 : Blo 1395517 2014969 := bstep (se 2 (by rfl) ⟨755613, by rfl⟩ : syracuseStep 2014969 = 1511227) B1511227
theorem B5373803 : Blo 1395517 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B9559943 : Blo 1395517 9559943 := bstep (se 1 (by rfl) ⟨7169957, by rfl⟩ : syracuseStep 9559943 = 14339915) B14339915
theorem B15916985 : Blo 1395517 15916985 := bstep (se 2 (by rfl) ⟨5968869, by rfl⟩ : syracuseStep 15916985 = 11937739) B11937739
theorem B12746801 : Blo 1395517 12746801 := bstep (se 2 (by rfl) ⟨4780050, by rfl⟩ : syracuseStep 12746801 = 9560101) B9560101
theorem B7954483 : Blo 1395517 7954483 := bstep (se 1 (by rfl) ⟨5965862, by rfl⟩ : syracuseStep 7954483 = 11931725) B11931725
theorem B5963881 : Blo 1395517 5963881 := bstep (se 2 (by rfl) ⟨2236455, by rfl⟩ : syracuseStep 5963881 = 4472911) B4472911
theorem B5104129 : Blo 1395517 5104129 := bstep (se 2 (by rfl) ⟨1914048, by rfl⟩ : syracuseStep 5104129 = 3828097) B3828097
theorem B9691649 : Blo 1395517 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B2122303 : Blo 1395517 2122303 := bstep (se 1 (by rfl) ⟨1591727, by rfl⟩ : syracuseStep 2122303 = 3183455) B3183455
theorem B2515631 : Blo 1395517 2515631 := bstep (se 1 (by rfl) ⟨1886723, by rfl⟩ : syracuseStep 2515631 = 3773447) B3773447
theorem B12092105 : Blo 1395517 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B5301395 : Blo 1395517 5301395 := bstep (se 1 (by rfl) ⟨3976046, by rfl⟩ : syracuseStep 5301395 = 7952093) B7952093
theorem B20145347 : Blo 1395517 20145347 := bstep (se 1 (by rfl) ⟨15109010, by rfl⟩ : syracuseStep 20145347 = 30218021) B30218021
theorem B6046919 : Blo 1395517 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B3581171 : Blo 1395517 3581171 := bstep (se 1 (by rfl) ⟨2685878, by rfl⟩ : syracuseStep 3581171 = 5371757) B5371757
theorem B18138455 : Blo 1395517 18138455 := bstep (se 1 (by rfl) ⟨13603841, by rfl⟩ : syracuseStep 18138455 = 27207683) B27207683
theorem B7071137 : Blo 1395517 7071137 := bstep (se 2 (by rfl) ⟨2651676, by rfl⟩ : syracuseStep 7071137 = 5303353) B5303353
theorem B54412843 : Blo 1395517 54412843 := bstep (se 1 (by rfl) ⟨40809632, by rfl⟩ : syracuseStep 54412843 = 81619265) B81619265
theorem B4712093 : Blo 1395517 4712093 := bstep (se 3 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 4712093 = 1767035) B1767035
theorem B57370463 : Blo 1395517 57370463 := bstep (se 1 (by rfl) ⟨43027847, by rfl⟩ : syracuseStep 57370463 = 86055695) B86055695
theorem B3532673 : Blo 1395517 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B117844055 : Blo 1395517 117844055 := bstep (se 1 (by rfl) ⟨88383041, by rfl⟩ : syracuseStep 117844055 = 176766083) B176766083
theorem B15100019 : Blo 1395517 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B4712633 : Blo 1395517 4712633 := bstep (se 2 (by rfl) ⟨1767237, by rfl⟩ : syracuseStep 4712633 = 3534475) B3534475
theorem B14330141 : Blo 1395517 14330141 := bstep (se 3 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 14330141 = 5373803) B5373803
theorem B3533129 : Blo 1395517 3533129 := bstep (se 2 (by rfl) ⟨1324923, by rfl⟩ : syracuseStep 3533129 = 2649847) B2649847
theorem B7547303 : Blo 1395517 7547303 := bstep (se 1 (by rfl) ⟨5660477, by rfl⟩ : syracuseStep 7547303 = 11320955) B11320955
theorem B2984359 : Blo 1395517 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B3402209 : Blo 1395517 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B2984521 : Blo 1395517 2984521 := bstep (se 2 (by rfl) ⟨1119195, by rfl⟩ : syracuseStep 2984521 = 2238391) B2238391
theorem B10611323 : Blo 1395517 10611323 := bstep (se 1 (by rfl) ⟨7958492, by rfl⟩ : syracuseStep 10611323 = 15916985) B15916985
theorem B3533483 : Blo 1395517 3533483 := bstep (se 1 (by rfl) ⟨2650112, by rfl⟩ : syracuseStep 3533483 = 5300225) B5300225
theorem B3140279 : Blo 1395517 3140279 := bstep (se 1 (by rfl) ⟨2355209, by rfl⟩ : syracuseStep 3140279 = 4710419) B4710419
theorem B16116413 : Blo 1395517 16116413 := bstep (se 3 (by rfl) ⟨3021827, by rfl⟩ : syracuseStep 16116413 = 6043655) B6043655
theorem B5966531 : Blo 1395517 5966531 := bstep (se 1 (by rfl) ⟨4474898, by rfl⟩ : syracuseStep 5966531 = 8949797) B8949797
theorem B1887031 : Blo 1395517 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B3140495 : Blo 1395517 3140495 := bstep (se 1 (by rfl) ⟨2355371, by rfl⟩ : syracuseStep 3140495 = 4710743) B4710743
theorem B1395611 : Blo 1395517 1395611 := bstep (se 1 (by rfl) ⟨1046708, by rfl⟩ : syracuseStep 1395611 = 2093417) B2093417
theorem B1395663 : Blo 1395517 1395663 := bstep (se 1 (by rfl) ⟨1046747, by rfl⟩ : syracuseStep 1395663 = 2093495) B2093495
theorem B1395687 : Blo 1395517 1395687 := bstep (se 1 (by rfl) ⟨1046765, by rfl⟩ : syracuseStep 1395687 = 2093531) B2093531
theorem B3976411 : Blo 1395517 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B1395999 : Blo 1395517 1395999 := bstep (se 1 (by rfl) ⟨1046999, by rfl⟩ : syracuseStep 1395999 = 2093999) B2093999
theorem B1396059 : Blo 1395517 1396059 := bstep (se 1 (by rfl) ⟨1047044, by rfl⟩ : syracuseStep 1396059 = 2094089) B2094089
theorem B3353953 : Blo 1395517 3353953 := bstep (se 2 (by rfl) ⟨1257732, by rfl⟩ : syracuseStep 3353953 = 2515465) B2515465
theorem B1396079 : Blo 1395517 1396079 := bstep (se 1 (by rfl) ⟨1047059, by rfl⟩ : syracuseStep 1396079 = 2094119) B2094119
theorem B14323073 : Blo 1395517 14323073 := bstep (se 2 (by rfl) ⟨5371152, by rfl⟩ : syracuseStep 14323073 = 10742305) B10742305
theorem B3353993 : Blo 1395517 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B1396135 : Blo 1395517 1396135 := bstep (se 1 (by rfl) ⟨1047101, by rfl⟩ : syracuseStep 1396135 = 2094203) B2094203
theorem B1396219 : Blo 1395517 1396219 := bstep (se 1 (by rfl) ⟨1047164, by rfl⟩ : syracuseStep 1396219 = 2094329) B2094329
theorem B1396287 : Blo 1395517 1396287 := bstep (se 1 (by rfl) ⟨1047215, by rfl⟩ : syracuseStep 1396287 = 2094431) B2094431
theorem B1396295 : Blo 1395517 1396295 := bstep (se 1 (by rfl) ⟨1047221, by rfl⟩ : syracuseStep 1396295 = 2094443) B2094443
theorem B3141215 : Blo 1395517 3141215 := bstep (se 1 (by rfl) ⟨2355911, by rfl⟩ : syracuseStep 3141215 = 4711823) B4711823
theorem B4714145 : Blo 1395517 4714145 := bstep (se 2 (by rfl) ⟨1767804, by rfl⟩ : syracuseStep 4714145 = 3535609) B3535609
theorem B15912611 : Blo 1395517 15912611 := bstep (se 1 (by rfl) ⟨11934458, by rfl⟩ : syracuseStep 15912611 = 23868917) B23868917
theorem B1396447 : Blo 1395517 1396447 := bstep (se 1 (by rfl) ⟨1047335, by rfl⟩ : syracuseStep 1396447 = 2094671) B2094671
theorem B1396527 : Blo 1395517 1396527 := bstep (se 1 (by rfl) ⟨1047395, by rfl⟩ : syracuseStep 1396527 = 2094791) B2094791
theorem B3141431 : Blo 1395517 3141431 := bstep (se 1 (by rfl) ⟨2356073, by rfl⟩ : syracuseStep 3141431 = 4712147) B4712147
theorem B21491513 : Blo 1395517 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B1396635 : Blo 1395517 1396635 := bstep (se 1 (by rfl) ⟨1047476, by rfl⟩ : syracuseStep 1396635 = 2094953) B2094953
theorem B3534799 : Blo 1395517 3534799 := bstep (se 1 (by rfl) ⟨2651099, by rfl⟩ : syracuseStep 3534799 = 5302199) B5302199
theorem B1396687 : Blo 1395517 1396687 := bstep (se 1 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 1396687 = 2095031) B2095031
theorem B1396711 : Blo 1395517 1396711 := bstep (se 1 (by rfl) ⟨1047533, by rfl⟩ : syracuseStep 1396711 = 2095067) B2095067
theorem B3141737 : Blo 1395517 3141737 := bstep (se 2 (by rfl) ⟨1178151, by rfl⟩ : syracuseStep 3141737 = 2356303) B2356303
theorem B2093321 : Blo 1395517 2093321 := bstep (se 2 (by rfl) ⟨784995, by rfl⟩ : syracuseStep 2093321 = 1569991) B1569991
theorem B1397023 : Blo 1395517 1397023 := bstep (se 1 (by rfl) ⟨1047767, by rfl⟩ : syracuseStep 1397023 = 2095535) B2095535
theorem B7958857 : Blo 1395517 7958857 := bstep (se 2 (by rfl) ⟨2984571, by rfl⟩ : syracuseStep 7958857 = 5969143) B5969143
theorem B2355547 : Blo 1395517 2355547 := bstep (se 1 (by rfl) ⟨1766660, by rfl⟩ : syracuseStep 2355547 = 3533321) B3533321
theorem B1397083 : Blo 1395517 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B2093423 : Blo 1395517 2093423 := bstep (se 1 (by rfl) ⟨1570067, by rfl⟩ : syracuseStep 2093423 = 3140135) B3140135
theorem B1397103 : Blo 1395517 1397103 := bstep (se 1 (by rfl) ⟨1047827, by rfl⟩ : syracuseStep 1397103 = 2095655) B2095655
theorem B1397159 : Blo 1395517 1397159 := bstep (se 1 (by rfl) ⟨1047869, by rfl⟩ : syracuseStep 1397159 = 2095739) B2095739
theorem B1397243 : Blo 1395517 1397243 := bstep (se 1 (by rfl) ⟨1047932, by rfl⟩ : syracuseStep 1397243 = 2095865) B2095865
theorem B4715009 : Blo 1395517 4715009 := bstep (se 2 (by rfl) ⟨1768128, by rfl⟩ : syracuseStep 4715009 = 3536257) B3536257
theorem B1397311 : Blo 1395517 1397311 := bstep (se 1 (by rfl) ⟨1047983, by rfl⟩ : syracuseStep 1397311 = 2095967) B2095967
theorem B2093639 : Blo 1395517 2093639 := bstep (se 1 (by rfl) ⟨1570229, by rfl⟩ : syracuseStep 2093639 = 3140459) B3140459
theorem B1397319 : Blo 1395517 1397319 := bstep (se 1 (by rfl) ⟨1047989, by rfl⟩ : syracuseStep 1397319 = 2095979) B2095979
theorem B3142223 : Blo 1395517 3142223 := bstep (se 1 (by rfl) ⟨2356667, by rfl⟩ : syracuseStep 3142223 = 4713335) B4713335
theorem B2093675 : Blo 1395517 2093675 := bstep (se 1 (by rfl) ⟨1570256, by rfl⟩ : syracuseStep 2093675 = 3140513) B3140513
theorem B2830969 : Blo 1395517 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B8942233 : Blo 1395517 8942233 := bstep (se 2 (by rfl) ⟨3353337, by rfl⟩ : syracuseStep 8942233 = 6706675) B6706675
theorem B1938143 : Blo 1395517 1938143 := bstep (se 1 (by rfl) ⟨1453607, by rfl⟩ : syracuseStep 1938143 = 2907215) B2907215
theorem B3142367 : Blo 1395517 3142367 := bstep (se 1 (by rfl) ⟨2356775, by rfl⟩ : syracuseStep 3142367 = 4713551) B4713551
theorem B1397471 : Blo 1395517 1397471 := bstep (se 1 (by rfl) ⟨1048103, by rfl⟩ : syracuseStep 1397471 = 2096207) B2096207
theorem B2831123 : Blo 1395517 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B2093903 : Blo 1395517 2093903 := bstep (se 1 (by rfl) ⟨1570427, by rfl⟩ : syracuseStep 2093903 = 3140855) B3140855
theorem B10597229 : Blo 1395517 10597229 := bstep (se 3 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 10597229 = 3973961) B3973961
theorem B3535771 : Blo 1395517 3535771 := bstep (se 1 (by rfl) ⟨2651828, by rfl⟩ : syracuseStep 3535771 = 5303657) B5303657
theorem B5305283 : Blo 1395517 5305283 := bstep (se 1 (by rfl) ⟨3978962, by rfl⟩ : syracuseStep 5305283 = 7957925) B7957925
theorem B5034953 : Blo 1395517 5034953 := bstep (se 2 (by rfl) ⟨1888107, by rfl⟩ : syracuseStep 5034953 = 3776215) B3776215
theorem B3142619 : Blo 1395517 3142619 := bstep (se 1 (by rfl) ⟨2356964, by rfl⟩ : syracuseStep 3142619 = 4713929) B4713929
theorem B4715495 : Blo 1395517 4715495 := bstep (se 1 (by rfl) ⟨3536621, by rfl⟩ : syracuseStep 4715495 = 7073243) B7073243
theorem B13415503 : Blo 1395517 13415503 := bstep (se 1 (by rfl) ⟨10061627, by rfl⟩ : syracuseStep 13415503 = 20123255) B20123255
theorem B3142799 : Blo 1395517 3142799 := bstep (se 1 (by rfl) ⟨2357099, by rfl⟩ : syracuseStep 3142799 = 4714199) B4714199
theorem B2094299 : Blo 1395517 2094299 := bstep (se 1 (by rfl) ⟨1570724, by rfl⟩ : syracuseStep 2094299 = 3141449) B3141449
theorem B3142889 : Blo 1395517 3142889 := bstep (se 2 (by rfl) ⟨1178583, by rfl⟩ : syracuseStep 3142889 = 2357167) B2357167
theorem B8942849 : Blo 1395517 8942849 := bstep (se 2 (by rfl) ⟨3353568, by rfl⟩ : syracuseStep 8942849 = 6707137) B6707137
theorem B3142943 : Blo 1395517 3142943 := bstep (se 1 (by rfl) ⟨2357207, by rfl⟩ : syracuseStep 3142943 = 4714415) B4714415
theorem B2356519 : Blo 1395517 2356519 := bstep (se 1 (by rfl) ⟨1767389, by rfl⟩ : syracuseStep 2356519 = 3534779) B3534779
theorem B4715819 : Blo 1395517 4715819 := bstep (se 1 (by rfl) ⟨3536864, by rfl⟩ : syracuseStep 4715819 = 7073729) B7073729
theorem B22639961 : Blo 1395517 22639961 := bstep (se 2 (by rfl) ⟨8489985, by rfl⟩ : syracuseStep 22639961 = 16979971) B16979971
theorem B1766767 : Blo 1395517 1766767 := bstep (se 1 (by rfl) ⟨1325075, by rfl⟩ : syracuseStep 1766767 = 2650151) B2650151
theorem B1570171 : Blo 1395517 1570171 := bstep (se 1 (by rfl) ⟨1177628, by rfl⟩ : syracuseStep 1570171 = 2355257) B2355257
theorem B2094473 : Blo 1395517 2094473 := bstep (se 2 (by rfl) ⟨785427, by rfl⟩ : syracuseStep 2094473 = 1570855) B1570855
theorem B4716089 : Blo 1395517 4716089 := bstep (se 2 (by rfl) ⟨1768533, by rfl⟩ : syracuseStep 4716089 = 3537067) B3537067
theorem B26842691 : Blo 1395517 26842691 := bstep (se 1 (by rfl) ⟨20132018, by rfl⟩ : syracuseStep 26842691 = 40264037) B40264037
theorem B2094827 : Blo 1395517 2094827 := bstep (se 1 (by rfl) ⟨1571120, by rfl⟩ : syracuseStep 2094827 = 3142241) B3142241
theorem B1988393 : Blo 1395517 1988393 := bstep (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) B1491295
theorem B3143465 : Blo 1395517 3143465 := bstep (se 2 (by rfl) ⟨1178799, by rfl⟩ : syracuseStep 3143465 = 2357599) B2357599
theorem B2357039 : Blo 1395517 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B3184439 : Blo 1395517 3184439 := bstep (se 1 (by rfl) ⟨2388329, by rfl⟩ : syracuseStep 3184439 = 4776659) B4776659
theorem B1570639 : Blo 1395517 1570639 := bstep (se 1 (by rfl) ⟨1177979, by rfl⟩ : syracuseStep 1570639 = 2355959) B2355959
theorem B38205371 : Blo 1395517 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B2095055 : Blo 1395517 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B3536905 : Blo 1395517 3536905 := bstep (se 2 (by rfl) ⟨1326339, by rfl⟩ : syracuseStep 3536905 = 2652679) B2652679
theorem B23877665 : Blo 1395517 23877665 := bstep (se 2 (by rfl) ⟨8954124, by rfl⟩ : syracuseStep 23877665 = 17908249) B17908249
theorem B1571035 : Blo 1395517 1571035 := bstep (se 1 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 1571035 = 2356553) B2356553
theorem B53655857 : Blo 1395517 53655857 := bstep (se 2 (by rfl) ⟨20120946, by rfl⟩ : syracuseStep 53655857 = 40241893) B40241893
theorem B2095451 : Blo 1395517 2095451 := bstep (se 1 (by rfl) ⟨1571588, by rfl⟩ : syracuseStep 2095451 = 3143177) B3143177
theorem B2652527 : Blo 1395517 2652527 := bstep (se 1 (by rfl) ⟨1989395, by rfl⟩ : syracuseStep 2652527 = 3978791) B3978791
theorem B1989031 : Blo 1395517 1989031 := bstep (se 1 (by rfl) ⟨1491773, by rfl⟩ : syracuseStep 1989031 = 2983547) B2983547
theorem B6371795 : Blo 1395517 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B1571323 : Blo 1395517 1571323 := bstep (se 1 (by rfl) ⟨1178492, by rfl⟩ : syracuseStep 1571323 = 2356985) B2356985
theorem B2095679 : Blo 1395517 2095679 := bstep (se 1 (by rfl) ⟨1571759, by rfl⟩ : syracuseStep 2095679 = 3143519) B3143519
theorem B8952383 : Blo 1395517 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B1768007 : Blo 1395517 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B5298767 : Blo 1395517 5298767 := bstep (se 1 (by rfl) ⟨3974075, by rfl⟩ : syracuseStep 5298767 = 7948151) B7948151
theorem B4029035 : Blo 1395517 4029035 := bstep (se 1 (by rfl) ⟨3021776, by rfl⟩ : syracuseStep 4029035 = 6043553) B6043553
theorem B1571503 : Blo 1395517 1571503 := bstep (se 1 (by rfl) ⟨1178627, by rfl⟩ : syracuseStep 1571503 = 2357255) B2357255
theorem B3185335 : Blo 1395517 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B2095799 : Blo 1395517 2095799 := bstep (se 1 (by rfl) ⟨1571849, by rfl⟩ : syracuseStep 2095799 = 3143699) B3143699
theorem B1768159 : Blo 1395517 1768159 := bstep (se 1 (by rfl) ⟨1326119, by rfl⟩ : syracuseStep 1768159 = 2652239) B2652239
theorem B2096027 : Blo 1395517 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B14334895 : Blo 1395517 14334895 := bstep (se 1 (by rfl) ⟨10751171, by rfl⟩ : syracuseStep 14334895 = 21502343) B21502343
theorem B1571791 : Blo 1395517 1571791 := bstep (se 1 (by rfl) ⟨1178843, by rfl⟩ : syracuseStep 1571791 = 2357687) B2357687
theorem B2235367 : Blo 1395517 2235367 := bstep (se 1 (by rfl) ⟨1676525, by rfl⟩ : syracuseStep 2235367 = 3353051) B3353051
theorem B2358247 : Blo 1395517 2358247 := bstep (se 1 (by rfl) ⟨1768685, by rfl⟩ : syracuseStep 2358247 = 3537371) B3537371
theorem B3357683 : Blo 1395517 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B10067165 : Blo 1395517 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B1572187 : Blo 1395517 1572187 := bstep (se 1 (by rfl) ⟨1179140, by rfl⟩ : syracuseStep 1572187 = 2358281) B2358281
theorem B2981215 : Blo 1395517 2981215 := bstep (se 1 (by rfl) ⟨2235911, by rfl⟩ : syracuseStep 2981215 = 4471823) B4471823
theorem B1490287 : Blo 1395517 1490287 := bstep (se 1 (by rfl) ⟨1117715, by rfl⟩ : syracuseStep 1490287 = 2235431) B2235431
theorem B5373371 : Blo 1395517 5373371 := bstep (se 1 (by rfl) ⟨4030028, by rfl⟩ : syracuseStep 5373371 = 8060057) B8060057
theorem B7069193 : Blo 1395517 7069193 := bstep (se 2 (by rfl) ⟨2650947, by rfl⟩ : syracuseStep 7069193 = 5301895) B5301895
theorem B26844695 : Blo 1395517 26844695 := bstep (se 1 (by rfl) ⟨20133521, by rfl⟩ : syracuseStep 26844695 = 40267043) B40267043
theorem B13426235 : Blo 1395517 13426235 := bstep (se 1 (by rfl) ⟨10069676, by rfl⟩ : syracuseStep 13426235 = 20139353) B20139353
theorem B3776095 : Blo 1395517 3776095 := bstep (se 1 (by rfl) ⟨2832071, by rfl⟩ : syracuseStep 3776095 = 5664143) B5664143
theorem B2686625 : Blo 1395517 2686625 := bstep (se 2 (by rfl) ⟨1007484, by rfl⟩ : syracuseStep 2686625 = 2014969) B2014969
theorem B14335649 : Blo 1395517 14335649 := bstep (se 2 (by rfl) ⟨5375868, by rfl⟩ : syracuseStep 14335649 = 10751737) B10751737
theorem B3776311 : Blo 1395517 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B9551677 : Blo 1395517 9551677 := bstep (se 3 (by rfl) ⟨1790939, by rfl⟩ : syracuseStep 9551677 = 3581879) B3581879
theorem B42983297 : Blo 1395517 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B6373295 : Blo 1395517 6373295 := bstep (se 1 (by rfl) ⟨4779971, by rfl⟩ : syracuseStep 6373295 = 9559943) B9559943
theorem B8061403 : Blo 1395517 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B15098501 : Blo 1395517 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B4031279 : Blo 1395517 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B12092303 : Blo 1395517 12092303 := bstep (se 1 (by rfl) ⟨9069227, by rfl⟩ : syracuseStep 12092303 = 18138455) B18138455
theorem B2516041 : Blo 1395517 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B16991453 : Blo 1395517 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B19113193 : Blo 1395517 19113193 := bstep (se 2 (by rfl) ⟨7167447, by rfl⟩ : syracuseStep 19113193 = 14334895) B14334895
theorem B25470247 : Blo 1395517 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B15918443 : Blo 1395517 15918443 := bstep (se 1 (by rfl) ⟨11938832, by rfl⟩ : syracuseStep 15918443 = 23877665) B23877665
theorem B78562703 : Blo 1395517 78562703 := bstep (se 1 (by rfl) ⟨58922027, by rfl⟩ : syracuseStep 78562703 = 117844055) B117844055
theorem B9553427 : Blo 1395517 9553427 := bstep (se 1 (by rfl) ⟨7165070, by rfl⟩ : syracuseStep 9553427 = 14330141) B14330141
theorem B5301881 : Blo 1395517 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B3532511 : Blo 1395517 3532511 := bstep (se 1 (by rfl) ⟨2649383, by rfl⟩ : syracuseStep 3532511 = 5298767) B5298767
theorem B3974953 : Blo 1395517 3974953 := bstep (se 2 (by rfl) ⟨1490607, by rfl⟩ : syracuseStep 3974953 = 2981215) B2981215
theorem B2238455 : Blo 1395517 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B72550457 : Blo 1395517 72550457 := bstep (se 2 (by rfl) ⟨27206421, by rfl⟩ : syracuseStep 72550457 = 54412843) B54412843
theorem B5302381 : Blo 1395517 5302381 := bstep (se 3 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 5302381 = 1988393) B1988393
theorem B6711443 : Blo 1395517 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B3582247 : Blo 1395517 3582247 := bstep (se 1 (by rfl) ⟨2686685, by rfl⟩ : syracuseStep 3582247 = 5373371) B5373371
theorem B4712795 : Blo 1395517 4712795 := bstep (se 1 (by rfl) ⟨3534596, by rfl⟩ : syracuseStep 4712795 = 7069193) B7069193
theorem B4713065 : Blo 1395517 4713065 := bstep (se 2 (by rfl) ⟨1767399, by rfl⟩ : syracuseStep 4713065 = 3534799) B3534799
theorem B8497867 : Blo 1395517 8497867 := bstep (se 1 (by rfl) ⟨6373400, by rfl⟩ : syracuseStep 8497867 = 12746801) B12746801
theorem B1395547 : Blo 1395517 1395547 := bstep (se 1 (by rfl) ⟨1046660, by rfl⟩ : syracuseStep 1395547 = 2093321) B2093321
theorem B1395615 : Blo 1395517 1395615 := bstep (se 1 (by rfl) ⟨1046711, by rfl⟩ : syracuseStep 1395615 = 2093423) B2093423
theorem B1395759 : Blo 1395517 1395759 := bstep (se 1 (by rfl) ⟨1046819, by rfl⟩ : syracuseStep 1395759 = 2093639) B2093639
theorem B1395783 : Blo 1395517 1395783 := bstep (se 1 (by rfl) ⟨1046837, by rfl⟩ : syracuseStep 1395783 = 2093675) B2093675
theorem B10611809 : Blo 1395517 10611809 := bstep (se 2 (by rfl) ⟨3979428, by rfl⟩ : syracuseStep 10611809 = 7958857) B7958857
theorem B3140729 : Blo 1395517 3140729 := bstep (se 2 (by rfl) ⟨1177773, by rfl⟩ : syracuseStep 3140729 = 2355547) B2355547
theorem B1395935 : Blo 1395517 1395935 := bstep (se 1 (by rfl) ⟨1046951, by rfl⟩ : syracuseStep 1395935 = 2093903) B2093903
theorem B7064819 : Blo 1395517 7064819 := bstep (se 1 (by rfl) ⟨5298614, by rfl⟩ : syracuseStep 7064819 = 10597229) B10597229
theorem B2829737 : Blo 1395517 2829737 := bstep (se 2 (by rfl) ⟨1061151, by rfl⟩ : syracuseStep 2829737 = 2122303) B2122303
theorem B3534263 : Blo 1395517 3534263 := bstep (se 1 (by rfl) ⟨2650697, by rfl⟩ : syracuseStep 3534263 = 5301395) B5301395
theorem B13430231 : Blo 1395517 13430231 := bstep (se 1 (by rfl) ⟨10072673, by rfl⟩ : syracuseStep 13430231 = 20145347) B20145347
theorem B1396199 : Blo 1395517 1396199 := bstep (se 1 (by rfl) ⟨1047149, by rfl⟩ : syracuseStep 1396199 = 2094299) B2094299
theorem B2387447 : Blo 1395517 2387447 := bstep (se 1 (by rfl) ⟨1790585, by rfl⟩ : syracuseStep 2387447 = 3581171) B3581171
theorem B11922977 : Blo 1395517 11922977 := bstep (se 2 (by rfl) ⟨4471116, by rfl⟩ : syracuseStep 11922977 = 8942233) B8942233
theorem B15093307 : Blo 1395517 15093307 := bstep (se 1 (by rfl) ⟨11319980, by rfl⟩ : syracuseStep 15093307 = 22639961) B22639961
theorem B4247113 : Blo 1395517 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B1396315 : Blo 1395517 1396315 := bstep (se 1 (by rfl) ⟨1047236, by rfl⟩ : syracuseStep 1396315 = 2094473) B2094473
theorem B4714091 : Blo 1395517 4714091 := bstep (se 1 (by rfl) ⟨3535568, by rfl⟩ : syracuseStep 4714091 = 7071137) B7071137
theorem B7073405 : Blo 1395517 7073405 := bstep (se 3 (by rfl) ⟨1326263, by rfl⟩ : syracuseStep 7073405 = 2652527) B2652527
theorem B17895127 : Blo 1395517 17895127 := bstep (se 1 (by rfl) ⟨13421345, by rfl⟩ : syracuseStep 17895127 = 26842691) B26842691
theorem B3141395 : Blo 1395517 3141395 := bstep (se 1 (by rfl) ⟨2356046, by rfl⟩ : syracuseStep 3141395 = 4712093) B4712093
theorem B1396551 : Blo 1395517 1396551 := bstep (se 1 (by rfl) ⟨1047413, by rfl⟩ : syracuseStep 1396551 = 2094827) B2094827
theorem B4714361 : Blo 1395517 4714361 := bstep (se 2 (by rfl) ⟨1767885, by rfl⟩ : syracuseStep 4714361 = 3535771) B3535771
theorem B2355115 : Blo 1395517 2355115 := bstep (se 1 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 2355115 = 3532673) B3532673
theorem B9072557 : Blo 1395517 9072557 := bstep (se 3 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 9072557 = 3402209) B3402209
theorem B1396703 : Blo 1395517 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B17887337 : Blo 1395517 17887337 := bstep (se 2 (by rfl) ⟨6707751, by rfl⟩ : syracuseStep 17887337 = 13415503) B13415503
theorem B3141755 : Blo 1395517 3141755 := bstep (se 1 (by rfl) ⟨2356316, by rfl⟩ : syracuseStep 3141755 = 4712633) B4712633
theorem B4714685 : Blo 1395517 4714685 := bstep (se 3 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 4714685 = 1768007) B1768007
theorem B35770571 : Blo 1395517 35770571 := bstep (se 1 (by rfl) ⟨26827928, by rfl⟩ : syracuseStep 35770571 = 53655857) B53655857
theorem B2355419 : Blo 1395517 2355419 := bstep (se 1 (by rfl) ⟨1766564, by rfl⟩ : syracuseStep 2355419 = 3533129) B3533129
theorem B1396967 : Blo 1395517 1396967 := bstep (se 1 (by rfl) ⟨1047725, by rfl⟩ : syracuseStep 1396967 = 2095451) B2095451
theorem B10744093 : Blo 1395517 10744093 := bstep (se 3 (by rfl) ⟨2014517, by rfl⟩ : syracuseStep 10744093 = 4029035) B4029035
theorem B20140325 : Blo 1395517 20140325 := bstep (se 4 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 20140325 = 3776311) B3776311
theorem B1397119 : Blo 1395517 1397119 := bstep (se 1 (by rfl) ⟨1047839, by rfl⟩ : syracuseStep 1397119 = 2095679) B2095679
theorem B5968255 : Blo 1395517 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B3142025 : Blo 1395517 3142025 := bstep (se 2 (by rfl) ⟨1178259, by rfl⟩ : syracuseStep 3142025 = 2356519) B2356519
theorem B7074215 : Blo 1395517 7074215 := bstep (se 1 (by rfl) ⟨5305661, by rfl⟩ : syracuseStep 7074215 = 10611323) B10611323
theorem B2355655 : Blo 1395517 2355655 := bstep (se 1 (by rfl) ⟨1766741, by rfl⟩ : syracuseStep 2355655 = 3533483) B3533483
theorem B2093519 : Blo 1395517 2093519 := bstep (se 1 (by rfl) ⟨1570139, by rfl⟩ : syracuseStep 2093519 = 3140279) B3140279
theorem B1397199 : Blo 1395517 1397199 := bstep (se 1 (by rfl) ⟨1047899, by rfl⟩ : syracuseStep 1397199 = 2095799) B2095799
theorem B3977687 : Blo 1395517 3977687 := bstep (se 1 (by rfl) ⟨2983265, by rfl⟩ : syracuseStep 3977687 = 5966531) B5966531
theorem B1987049 : Blo 1395517 1987049 := bstep (se 2 (by rfl) ⟨745143, by rfl⟩ : syracuseStep 1987049 = 1490287) B1490287
theorem B2355689 : Blo 1395517 2355689 := bstep (se 2 (by rfl) ⟨883383, by rfl⟩ : syracuseStep 2355689 = 1766767) B1766767
theorem B2093561 : Blo 1395517 2093561 := bstep (se 2 (by rfl) ⟨785085, by rfl⟩ : syracuseStep 2093561 = 1570171) B1570171
theorem B2093663 : Blo 1395517 2093663 := bstep (se 1 (by rfl) ⟨1570247, by rfl⟩ : syracuseStep 2093663 = 3140495) B3140495
theorem B1397351 : Blo 1395517 1397351 := bstep (se 1 (by rfl) ⟨1048013, by rfl⟩ : syracuseStep 1397351 = 2096027) B2096027
theorem B7549661 : Blo 1395517 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B5034793 : Blo 1395517 5034793 := bstep (se 2 (by rfl) ⟨1888047, by rfl⟩ : syracuseStep 5034793 = 3776095) B3776095
theorem B8491837 : Blo 1395517 8491837 := bstep (se 3 (by rfl) ⟨1592219, by rfl⟩ : syracuseStep 8491837 = 3184439) B3184439
theorem B17896463 : Blo 1395517 17896463 := bstep (se 1 (by rfl) ⟨13422347, by rfl⟩ : syracuseStep 17896463 = 26844695) B26844695
theorem B8950823 : Blo 1395517 8950823 := bstep (se 1 (by rfl) ⟨6713117, by rfl⟩ : syracuseStep 8950823 = 13426235) B13426235
theorem B2094143 : Blo 1395517 2094143 := bstep (se 1 (by rfl) ⟨1570607, by rfl⟩ : syracuseStep 2094143 = 3141215) B3141215
theorem B12735569 : Blo 1395517 12735569 := bstep (se 2 (by rfl) ⟨4775838, by rfl⟩ : syracuseStep 12735569 = 9551677) B9551677
theorem B2094185 : Blo 1395517 2094185 := bstep (se 2 (by rfl) ⟨785319, by rfl⟩ : syracuseStep 2094185 = 1570639) B1570639
theorem B1791083 : Blo 1395517 1791083 := bstep (se 1 (by rfl) ⟨1343312, by rfl⟩ : syracuseStep 1791083 = 2686625) B2686625
theorem B3142763 : Blo 1395517 3142763 := bstep (se 1 (by rfl) ⟨2357072, by rfl⟩ : syracuseStep 3142763 = 4714145) B4714145
theorem B9557099 : Blo 1395517 9557099 := bstep (se 1 (by rfl) ⟨7167824, by rfl⟩ : syracuseStep 9557099 = 14335649) B14335649
theorem B2094287 : Blo 1395517 2094287 := bstep (se 1 (by rfl) ⟨1570715, by rfl⟩ : syracuseStep 2094287 = 3141431) B3141431
theorem B4248863 : Blo 1395517 4248863 := bstep (se 1 (by rfl) ⟨3186647, by rfl⟩ : syracuseStep 4248863 = 6373295) B6373295
theorem B4715873 : Blo 1395517 4715873 := bstep (se 2 (by rfl) ⟨1768452, by rfl⟩ : syracuseStep 4715873 = 3536905) B3536905
theorem B10605977 : Blo 1395517 10605977 := bstep (se 2 (by rfl) ⟨3977241, by rfl⟩ : syracuseStep 10605977 = 7954483) B7954483
theorem B2094491 : Blo 1395517 2094491 := bstep (se 1 (by rfl) ⟨1570868, by rfl⟩ : syracuseStep 2094491 = 3141737) B3141737
theorem B7951841 : Blo 1395517 7951841 := bstep (se 2 (by rfl) ⟨2981940, by rfl⟩ : syracuseStep 7951841 = 5963881) B5963881
theorem B2094713 : Blo 1395517 2094713 := bstep (se 2 (by rfl) ⟨785517, by rfl⟩ : syracuseStep 2094713 = 1571035) B1571035
theorem B3143339 : Blo 1395517 3143339 := bstep (se 1 (by rfl) ⟨2357504, by rfl⟩ : syracuseStep 3143339 = 4715009) B4715009
theorem B6461099 : Blo 1395517 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B2094815 : Blo 1395517 2094815 := bstep (se 1 (by rfl) ⟨1571111, by rfl⟩ : syracuseStep 2094815 = 3142223) B3142223
theorem B2094911 : Blo 1395517 2094911 := bstep (se 1 (by rfl) ⟨1571183, by rfl⟩ : syracuseStep 2094911 = 3142367) B3142367
theorem B2652041 : Blo 1395517 2652041 := bstep (se 2 (by rfl) ⟨994515, by rfl⟩ : syracuseStep 2652041 = 1989031) B1989031
theorem B3979145 : Blo 1395517 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B3536855 : Blo 1395517 3536855 := bstep (se 1 (by rfl) ⟨2652641, by rfl⟩ : syracuseStep 3536855 = 5305283) B5305283
theorem B3356635 : Blo 1395517 3356635 := bstep (se 1 (by rfl) ⟨2517476, by rfl⟩ : syracuseStep 3356635 = 5034953) B5034953
theorem B2095079 : Blo 1395517 2095079 := bstep (se 1 (by rfl) ⟨1571309, by rfl⟩ : syracuseStep 2095079 = 3142619) B3142619
theorem B3143663 : Blo 1395517 3143663 := bstep (se 1 (by rfl) ⟨2357747, by rfl⟩ : syracuseStep 3143663 = 4715495) B4715495
theorem B2095097 : Blo 1395517 2095097 := bstep (se 2 (by rfl) ⟨785661, by rfl⟩ : syracuseStep 2095097 = 1571323) B1571323
theorem B6805505 : Blo 1395517 6805505 := bstep (se 2 (by rfl) ⟨2552064, by rfl⟩ : syracuseStep 6805505 = 5104129) B5104129
theorem B2095199 : Blo 1395517 2095199 := bstep (se 1 (by rfl) ⟨1571399, by rfl⟩ : syracuseStep 2095199 = 3142799) B3142799
theorem B3979361 : Blo 1395517 3979361 := bstep (se 2 (by rfl) ⟨1492260, by rfl⟩ : syracuseStep 3979361 = 2984521) B2984521
theorem B2095259 : Blo 1395517 2095259 := bstep (se 1 (by rfl) ⟨1571444, by rfl⟩ : syracuseStep 2095259 = 3142889) B3142889
theorem B5961899 : Blo 1395517 5961899 := bstep (se 1 (by rfl) ⟨4471424, by rfl⟩ : syracuseStep 5961899 = 8942849) B8942849
theorem B2095295 : Blo 1395517 2095295 := bstep (se 1 (by rfl) ⟨1571471, by rfl⟩ : syracuseStep 2095295 = 3142943) B3142943
theorem B3143879 : Blo 1395517 3143879 := bstep (se 1 (by rfl) ⟨2357909, by rfl⟩ : syracuseStep 3143879 = 4715819) B4715819
theorem B2095337 : Blo 1395517 2095337 := bstep (se 2 (by rfl) ⟨785751, by rfl⟩ : syracuseStep 2095337 = 1571503) B1571503
theorem B2357545 : Blo 1395517 2357545 := bstep (se 2 (by rfl) ⟨884079, by rfl⟩ : syracuseStep 2357545 = 1768159) B1768159
theorem B3144059 : Blo 1395517 3144059 := bstep (se 1 (by rfl) ⟨2358044, by rfl⟩ : syracuseStep 3144059 = 4716089) B4716089
theorem B20126141 : Blo 1395517 20126141 := bstep (se 3 (by rfl) ⟨3773651, by rfl⟩ : syracuseStep 20126141 = 7547303) B7547303
theorem B2095643 : Blo 1395517 2095643 := bstep (se 1 (by rfl) ⟨1571732, by rfl⟩ : syracuseStep 2095643 = 3143465) B3143465
theorem B1571359 : Blo 1395517 1571359 := bstep (se 1 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 1571359 = 2357039) B2357039
theorem B38246975 : Blo 1395517 38246975 := bstep (se 1 (by rfl) ⟨28685231, by rfl⟩ : syracuseStep 38246975 = 57370463) B57370463
theorem B2095721 : Blo 1395517 2095721 := bstep (se 2 (by rfl) ⟨785895, by rfl⟩ : syracuseStep 2095721 = 1571791) B1571791
theorem B2980489 : Blo 1395517 2980489 := bstep (se 2 (by rfl) ⟨1117683, by rfl⟩ : syracuseStep 2980489 = 2235367) B2235367
theorem B3144329 : Blo 1395517 3144329 := bstep (se 2 (by rfl) ⟨1179123, by rfl⟩ : syracuseStep 3144329 = 2358247) B2358247
theorem B152779445 : Blo 1395517 152779445 := bstep (se 5 (by rfl) ⟨7161536, by rfl⟩ : syracuseStep 152779445 = 14323073) B14323073
theorem B10066679 : Blo 1395517 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B2096249 : Blo 1395517 2096249 := bstep (se 2 (by rfl) ⟨786093, by rfl⟩ : syracuseStep 2096249 = 1572187) B1572187
theorem B6708349 : Blo 1395517 6708349 := bstep (se 3 (by rfl) ⟨1257815, by rfl⟩ : syracuseStep 6708349 = 2515631) B2515631
theorem B4471937 : Blo 1395517 4471937 := bstep (se 2 (by rfl) ⟨1676976, by rfl⟩ : syracuseStep 4471937 = 3353953) B3353953
theorem B5168381 : Blo 1395517 5168381 := bstep (se 3 (by rfl) ⟨969071, by rfl⟩ : syracuseStep 5168381 = 1938143) B1938143
theorem B171908405 : Blo 1395517 171908405 := bstep (se 5 (by rfl) ⟨8058206, by rfl⟩ : syracuseStep 171908405 = 16116413) B16116413
theorem B2235995 : Blo 1395517 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B10608407 : Blo 1395517 10608407 := bstep (se 1 (by rfl) ⟨7956305, by rfl⟩ : syracuseStep 10608407 = 15912611) B15912611
theorem B14327675 : Blo 1395517 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B28655531 : Blo 1395517 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B23847047 : Blo 1395517 23847047 := bstep (se 1 (by rfl) ⟨17885285, by rfl⟩ : syracuseStep 23847047 = 35770571) B35770571
theorem B7069841 : Blo 1395517 7069841 := bstep (se 2 (by rfl) ⟨2651190, by rfl⟩ : syracuseStep 7069841 = 5302381) B5302381
theorem B13426883 : Blo 1395517 13426883 := bstep (se 1 (by rfl) ⟨10070162, by rfl⟩ : syracuseStep 13426883 = 20140325) B20140325
theorem B4776221 : Blo 1395517 4776221 := bstep (se 3 (by rfl) ⟨895541, by rfl⟩ : syracuseStep 4776221 = 1791083) B1791083
theorem B13418885 : Blo 1395517 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B4776329 : Blo 1395517 4776329 := bstep (se 2 (by rfl) ⟨1791123, by rfl⟩ : syracuseStep 4776329 = 3582247) B3582247
theorem B2687519 : Blo 1395517 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B8061535 : Blo 1395517 8061535 := bstep (se 1 (by rfl) ⟨6046151, by rfl⟩ : syracuseStep 8061535 = 12092303) B12092303
theorem B10748537 : Blo 1395517 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B3973985 : Blo 1395517 3973985 := bstep (se 2 (by rfl) ⟨1490244, by rfl⟩ : syracuseStep 3973985 = 2980489) B2980489
theorem B11330489 : Blo 1395517 11330489 := bstep (se 2 (by rfl) ⟨4248933, by rfl⟩ : syracuseStep 11330489 = 8497867) B8497867
theorem B7070651 : Blo 1395517 7070651 := bstep (se 1 (by rfl) ⟨5302988, by rfl⟩ : syracuseStep 7070651 = 10605977) B10605977
theorem B5301227 : Blo 1395517 5301227 := bstep (se 1 (by rfl) ⟨3975920, by rfl⟩ : syracuseStep 5301227 = 7951841) B7951841
theorem B11322449 : Blo 1395517 11322449 := bstep (se 2 (by rfl) ⟨4245918, by rfl⟩ : syracuseStep 11322449 = 8491837) B8491837
theorem B48366971 : Blo 1395517 48366971 := bstep (se 1 (by rfl) ⟨36275228, by rfl⟩ : syracuseStep 48366971 = 72550457) B72550457
theorem B4474295 : Blo 1395517 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B3974599 : Blo 1395517 3974599 := bstep (se 1 (by rfl) ⟨2980949, by rfl⟩ : syracuseStep 3974599 = 5961899) B5961899
theorem B101852963 : Blo 1395517 101852963 := bstep (se 1 (by rfl) ⟨76389722, by rfl⟩ : syracuseStep 101852963 = 152779445) B152779445
theorem B6711119 : Blo 1395517 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B5662817 : Blo 1395517 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B1886491 : Blo 1395517 1886491 := bstep (se 1 (by rfl) ⟨1414868, by rfl⟩ : syracuseStep 1886491 = 2829737) B2829737
theorem B1591631 : Blo 1395517 1591631 := bstep (se 1 (by rfl) ⟨1193723, by rfl⟩ : syracuseStep 1591631 = 2387447) B2387447
theorem B7948651 : Blo 1395517 7948651 := bstep (se 1 (by rfl) ⟨5961488, by rfl⟩ : syracuseStep 7948651 = 11922977) B11922977
theorem B7072109 : Blo 1395517 7072109 := bstep (se 3 (by rfl) ⟨1326020, by rfl⟩ : syracuseStep 7072109 = 2652041) B2652041
theorem B7072271 : Blo 1395517 7072271 := bstep (se 1 (by rfl) ⟨5304203, by rfl⟩ : syracuseStep 7072271 = 10608407) B10608407
theorem B3140153 : Blo 1395517 3140153 := bstep (se 2 (by rfl) ⟨1177557, by rfl⟩ : syracuseStep 3140153 = 2355115) B2355115
theorem B6048371 : Blo 1395517 6048371 := bstep (se 1 (by rfl) ⟨4536278, by rfl⟩ : syracuseStep 6048371 = 9072557) B9072557
theorem B4475513 : Blo 1395517 4475513 := bstep (se 2 (by rfl) ⟨1678317, by rfl⟩ : syracuseStep 4475513 = 3356635) B3356635
theorem B1395679 : Blo 1395517 1395679 := bstep (se 1 (by rfl) ⟨1046759, by rfl⟩ : syracuseStep 1395679 = 2093519) B2093519
theorem B1395707 : Blo 1395517 1395707 := bstep (se 1 (by rfl) ⟨1046780, by rfl⟩ : syracuseStep 1395707 = 2093561) B2093561
theorem B1395775 : Blo 1395517 1395775 := bstep (se 1 (by rfl) ⟨1046831, by rfl⟩ : syracuseStep 1395775 = 2093663) B2093663
theorem B5033107 : Blo 1395517 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B7957673 : Blo 1395517 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B3140873 : Blo 1395517 3140873 := bstep (se 2 (by rfl) ⟨1177827, by rfl⟩ : syracuseStep 3140873 = 2355655) B2355655
theorem B13782349 : Blo 1395517 13782349 := bstep (se 3 (by rfl) ⟨2584190, by rfl⟩ : syracuseStep 13782349 = 5168381) B5168381
theorem B11930975 : Blo 1395517 11930975 := bstep (se 1 (by rfl) ⟨8948231, by rfl⟩ : syracuseStep 11930975 = 17896463) B17896463
theorem B5967215 : Blo 1395517 5967215 := bstep (se 1 (by rfl) ⟨4475411, by rfl⟩ : syracuseStep 5967215 = 8950823) B8950823
theorem B1396095 : Blo 1395517 1396095 := bstep (se 1 (by rfl) ⟨1047071, by rfl⟩ : syracuseStep 1396095 = 2094143) B2094143
theorem B8490379 : Blo 1395517 8490379 := bstep (se 1 (by rfl) ⟨6367784, by rfl⟩ : syracuseStep 8490379 = 12735569) B12735569
theorem B1396123 : Blo 1395517 1396123 := bstep (se 1 (by rfl) ⟨1047092, by rfl⟩ : syracuseStep 1396123 = 2094185) B2094185
theorem B1396191 : Blo 1395517 1396191 := bstep (se 1 (by rfl) ⟨1047143, by rfl⟩ : syracuseStep 1396191 = 2094287) B2094287
theorem B10612295 : Blo 1395517 10612295 := bstep (se 1 (by rfl) ⟨7959221, by rfl⟩ : syracuseStep 10612295 = 15918443) B15918443
theorem B52375135 : Blo 1395517 52375135 := bstep (se 1 (by rfl) ⟨39281351, by rfl⟩ : syracuseStep 52375135 = 78562703) B78562703
theorem B1396327 : Blo 1395517 1396327 := bstep (se 1 (by rfl) ⟨1047245, by rfl⟩ : syracuseStep 1396327 = 2094491) B2094491
theorem B6368951 : Blo 1395517 6368951 := bstep (se 1 (by rfl) ⟨4776713, by rfl⟩ : syracuseStep 6368951 = 9553427) B9553427
theorem B6713057 : Blo 1395517 6713057 := bstep (se 2 (by rfl) ⟨2517396, by rfl⟩ : syracuseStep 6713057 = 5034793) B5034793
theorem B3534587 : Blo 1395517 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B1396475 : Blo 1395517 1396475 := bstep (se 1 (by rfl) ⟨1047356, by rfl⟩ : syracuseStep 1396475 = 2094713) B2094713
theorem B2355007 : Blo 1395517 2355007 := bstep (se 1 (by rfl) ⟨1766255, by rfl⟩ : syracuseStep 2355007 = 3532511) B3532511
theorem B1396543 : Blo 1395517 1396543 := bstep (se 1 (by rfl) ⟨1047407, by rfl⟩ : syracuseStep 1396543 = 2094815) B2094815
theorem B1396607 : Blo 1395517 1396607 := bstep (se 1 (by rfl) ⟨1047455, by rfl⟩ : syracuseStep 1396607 = 2094911) B2094911
theorem B1396719 : Blo 1395517 1396719 := bstep (se 1 (by rfl) ⟨1047539, by rfl⟩ : syracuseStep 1396719 = 2095079) B2095079
theorem B1396731 : Blo 1395517 1396731 := bstep (se 1 (by rfl) ⟨1047548, by rfl⟩ : syracuseStep 1396731 = 2095097) B2095097
theorem B1396799 : Blo 1395517 1396799 := bstep (se 1 (by rfl) ⟨1047599, by rfl⟩ : syracuseStep 1396799 = 2095199) B2095199
theorem B1396839 : Blo 1395517 1396839 := bstep (se 1 (by rfl) ⟨1047629, by rfl⟩ : syracuseStep 1396839 = 2095259) B2095259
theorem B1396863 : Blo 1395517 1396863 := bstep (se 1 (by rfl) ⟨1047647, by rfl⟩ : syracuseStep 1396863 = 2095295) B2095295
theorem B1396891 : Blo 1395517 1396891 := bstep (se 1 (by rfl) ⟨1047668, by rfl⟩ : syracuseStep 1396891 = 2095337) B2095337
theorem B3141863 : Blo 1395517 3141863 := bstep (se 1 (by rfl) ⟨2356397, by rfl⟩ : syracuseStep 3141863 = 4712795) B4712795
theorem B1397095 : Blo 1395517 1397095 := bstep (se 1 (by rfl) ⟨1047821, by rfl⟩ : syracuseStep 1397095 = 2095643) B2095643
theorem B25497983 : Blo 1395517 25497983 := bstep (se 1 (by rfl) ⟨19123487, by rfl⟩ : syracuseStep 25497983 = 38246975) B38246975
theorem B33960329 : Blo 1395517 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B3142043 : Blo 1395517 3142043 := bstep (se 1 (by rfl) ⟨2356532, by rfl⟩ : syracuseStep 3142043 = 4713065) B4713065
theorem B1397147 : Blo 1395517 1397147 := bstep (se 1 (by rfl) ⟨1047860, by rfl⟩ : syracuseStep 1397147 = 2095721) B2095721
theorem B7074539 : Blo 1395517 7074539 := bstep (se 1 (by rfl) ⟨5305904, by rfl⟩ : syracuseStep 7074539 = 10611809) B10611809
theorem B20124409 : Blo 1395517 20124409 := bstep (se 2 (by rfl) ⟨7546653, by rfl⟩ : syracuseStep 20124409 = 15093307) B15093307
theorem B2093819 : Blo 1395517 2093819 := bstep (se 1 (by rfl) ⟨1570364, by rfl⟩ : syracuseStep 2093819 = 3140729) B3140729
theorem B1397499 : Blo 1395517 1397499 := bstep (se 1 (by rfl) ⟨1048124, by rfl⟩ : syracuseStep 1397499 = 2096249) B2096249
theorem B23860169 : Blo 1395517 23860169 := bstep (se 2 (by rfl) ⟨8947563, by rfl⟩ : syracuseStep 23860169 = 17895127) B17895127
theorem B2356175 : Blo 1395517 2356175 := bstep (se 1 (by rfl) ⟨1767131, by rfl⟩ : syracuseStep 2356175 = 3534263) B3534263
theorem B3142727 : Blo 1395517 3142727 := bstep (se 1 (by rfl) ⟨2357045, by rfl⟩ : syracuseStep 3142727 = 4714091) B4714091
theorem B4715603 : Blo 1395517 4715603 := bstep (se 1 (by rfl) ⟨3536702, by rfl⟩ : syracuseStep 4715603 = 7073405) B7073405
theorem B2094263 : Blo 1395517 2094263 := bstep (se 1 (by rfl) ⟨1570697, by rfl⟩ : syracuseStep 2094263 = 3141395) B3141395
theorem B3142907 : Blo 1395517 3142907 := bstep (se 1 (by rfl) ⟨2357180, by rfl⟩ : syracuseStep 3142907 = 4714361) B4714361
theorem B5969213 : Blo 1395517 5969213 := bstep (se 3 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 5969213 = 2238455) B2238455
theorem B11924891 : Blo 1395517 11924891 := bstep (se 1 (by rfl) ⟨8943668, by rfl⟩ : syracuseStep 11924891 = 17887337) B17887337
theorem B2094503 : Blo 1395517 2094503 := bstep (se 1 (by rfl) ⟨1570877, by rfl⟩ : syracuseStep 2094503 = 3141755) B3141755
theorem B3143123 : Blo 1395517 3143123 := bstep (se 1 (by rfl) ⟨2357342, by rfl⟩ : syracuseStep 3143123 = 4714685) B4714685
theorem B1570279 : Blo 1395517 1570279 := bstep (se 1 (by rfl) ⟨1177709, by rfl⟩ : syracuseStep 1570279 = 2355419) B2355419
theorem B2094683 : Blo 1395517 2094683 := bstep (se 1 (by rfl) ⟨1571012, by rfl⟩ : syracuseStep 2094683 = 3142025) B3142025
theorem B4716143 : Blo 1395517 4716143 := bstep (se 1 (by rfl) ⟨3537107, by rfl⟩ : syracuseStep 4716143 = 7074215) B7074215
theorem B2651791 : Blo 1395517 2651791 := bstep (se 1 (by rfl) ⟨1988843, by rfl⟩ : syracuseStep 2651791 = 3977687) B3977687
theorem B1570459 : Blo 1395517 1570459 := bstep (se 1 (by rfl) ⟨1177844, by rfl⟩ : syracuseStep 1570459 = 2355689) B2355689
theorem B3143393 : Blo 1395517 3143393 := bstep (se 2 (by rfl) ⟨1178772, by rfl⟩ : syracuseStep 3143393 = 2357545) B2357545
theorem B10065667 : Blo 1395517 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B2095145 : Blo 1395517 2095145 := bstep (se 2 (by rfl) ⟨785679, by rfl⟩ : syracuseStep 2095145 = 1571359) B1571359
theorem B2095175 : Blo 1395517 2095175 := bstep (se 1 (by rfl) ⟨1571381, by rfl⟩ : syracuseStep 2095175 = 3142763) B3142763
theorem B6371399 : Blo 1395517 6371399 := bstep (se 1 (by rfl) ⟨4778549, by rfl⟩ : syracuseStep 6371399 = 9557099) B9557099
theorem B11327635 : Blo 1395517 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B2832575 : Blo 1395517 2832575 := bstep (se 1 (by rfl) ⟨2124431, by rfl⟩ : syracuseStep 2832575 = 4248863) B4248863
theorem B3143915 : Blo 1395517 3143915 := bstep (se 1 (by rfl) ⟨2357936, by rfl⟩ : syracuseStep 3143915 = 4715873) B4715873
theorem B2095559 : Blo 1395517 2095559 := bstep (se 1 (by rfl) ⟨1571669, by rfl⟩ : syracuseStep 2095559 = 3143339) B3143339
theorem B4307399 : Blo 1395517 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B2652763 : Blo 1395517 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B5298797 : Blo 1395517 5298797 := bstep (se 3 (by rfl) ⟨993524, by rfl⟩ : syracuseStep 5298797 = 1987049) B1987049
theorem B2357903 : Blo 1395517 2357903 := bstep (se 1 (by rfl) ⟨1768427, by rfl⟩ : syracuseStep 2357903 = 3536855) B3536855
theorem B2095775 : Blo 1395517 2095775 := bstep (se 1 (by rfl) ⟨1571831, by rfl⟩ : syracuseStep 2095775 = 3143663) B3143663
theorem B4537003 : Blo 1395517 4537003 := bstep (se 1 (by rfl) ⟨3402752, by rfl⟩ : syracuseStep 4537003 = 6805505) B6805505
theorem B2652907 : Blo 1395517 2652907 := bstep (se 1 (by rfl) ⟨1989680, by rfl⟩ : syracuseStep 2652907 = 3979361) B3979361
theorem B2095919 : Blo 1395517 2095919 := bstep (se 1 (by rfl) ⟨1571939, by rfl⟩ : syracuseStep 2095919 = 3143879) B3143879
theorem B57301829 : Blo 1395517 57301829 := bstep (se 4 (by rfl) ⟨5372046, by rfl⟩ : syracuseStep 57301829 = 10744093) B10744093
theorem B8944465 : Blo 1395517 8944465 := bstep (se 2 (by rfl) ⟨3354174, by rfl⟩ : syracuseStep 8944465 = 6708349) B6708349
theorem B2096039 : Blo 1395517 2096039 := bstep (se 1 (by rfl) ⟨1572029, by rfl⟩ : syracuseStep 2096039 = 3144059) B3144059
theorem B13417427 : Blo 1395517 13417427 := bstep (se 1 (by rfl) ⟨10063070, by rfl⟩ : syracuseStep 13417427 = 20126141) B20126141
theorem B25484257 : Blo 1395517 25484257 := bstep (se 2 (by rfl) ⟨9556596, by rfl⟩ : syracuseStep 25484257 = 19113193) B19113193
theorem B2096219 : Blo 1395517 2096219 := bstep (se 1 (by rfl) ⟨1572164, by rfl⟩ : syracuseStep 2096219 = 3144329) B3144329
theorem B2981291 : Blo 1395517 2981291 := bstep (se 1 (by rfl) ⟨2235968, by rfl⟩ : syracuseStep 2981291 = 4471937) B4471937
theorem B4709879 : Blo 1395517 4709879 := bstep (se 1 (by rfl) ⟨3532409, by rfl⟩ : syracuseStep 4709879 = 7064819) B7064819
theorem B114605603 : Blo 1395517 114605603 := bstep (se 1 (by rfl) ⟨85954202, by rfl⟩ : syracuseStep 114605603 = 171908405) B171908405
theorem B8953487 : Blo 1395517 8953487 := bstep (se 1 (by rfl) ⟨6715115, by rfl⟩ : syracuseStep 8953487 = 13430231) B13430231
theorem B5299937 : Blo 1395517 5299937 := bstep (se 2 (by rfl) ⟨1987476, by rfl⟩ : syracuseStep 5299937 = 3974953) B3974953
theorem B1490663 : Blo 1395517 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B9551783 : Blo 1395517 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B19103687 : Blo 1395517 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B16998655 : Blo 1395517 16998655 := bstep (se 1 (by rfl) ⟨12748991, by rfl⟩ : syracuseStep 16998655 = 25497983) B25497983
theorem B2515321 : Blo 1395517 2515321 := bstep (se 2 (by rfl) ⟨943245, by rfl⟩ : syracuseStep 2515321 = 1886491) B1886491
theorem B7553533 : Blo 1395517 7553533 := bstep (se 3 (by rfl) ⟨1416287, by rfl⟩ : syracuseStep 7553533 = 2832575) B2832575
theorem B7553659 : Blo 1395517 7553659 := bstep (se 1 (by rfl) ⟨5665244, by rfl⟩ : syracuseStep 7553659 = 11330489) B11330489
theorem B10748713 : Blo 1395517 10748713 := bstep (se 2 (by rfl) ⟨4030767, by rfl⟩ : syracuseStep 10748713 = 8061535) B8061535
theorem B32244647 : Blo 1395517 32244647 := bstep (se 1 (by rfl) ⟨24183485, by rfl⟩ : syracuseStep 32244647 = 48366971) B48366971
theorem B2982863 : Blo 1395517 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B35783693 : Blo 1395517 35783693 := bstep (se 3 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 35783693 = 13418885) B13418885
theorem B4474079 : Blo 1395517 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B3532531 : Blo 1395517 3532531 := bstep (se 1 (by rfl) ⟨2649398, by rfl⟩ : syracuseStep 3532531 = 5298797) B5298797
theorem B18376465 : Blo 1395517 18376465 := bstep (se 2 (by rfl) ⟨6891174, by rfl⟩ : syracuseStep 18376465 = 13782349) B13782349
theorem B38201219 : Blo 1395517 38201219 := bstep (se 1 (by rfl) ⟨28650914, by rfl⟩ : syracuseStep 38201219 = 57301829) B57301829
theorem B17901485 : Blo 1395517 17901485 := bstep (se 3 (by rfl) ⟨3356528, by rfl⟩ : syracuseStep 17901485 = 6713057) B6713057
theorem B3975101 : Blo 1395517 3975101 := bstep (se 3 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 3975101 = 1490663) B1490663
theorem B3139919 : Blo 1395517 3139919 := bstep (se 1 (by rfl) ⟨2354939, by rfl⟩ : syracuseStep 3139919 = 4709879) B4709879
theorem B13420889 : Blo 1395517 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B3140009 : Blo 1395517 3140009 := bstep (se 2 (by rfl) ⟨1177503, by rfl⟩ : syracuseStep 3140009 = 2355007) B2355007
theorem B25471421 : Blo 1395517 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B4245967 : Blo 1395517 4245967 := bstep (se 1 (by rfl) ⟨3184475, by rfl⟩ : syracuseStep 4245967 = 6368951) B6368951
theorem B3533291 : Blo 1395517 3533291 := bstep (se 1 (by rfl) ⟨2649968, by rfl⟩ : syracuseStep 3533291 = 5299937) B5299937
theorem B4713227 : Blo 1395517 4713227 := bstep (se 1 (by rfl) ⟨3534920, by rfl⟩ : syracuseStep 4713227 = 7069841) B7069841
theorem B1395879 : Blo 1395517 1395879 := bstep (se 1 (by rfl) ⟨1046909, by rfl⟩ : syracuseStep 1395879 = 2093819) B2093819
theorem B2649323 : Blo 1395517 2649323 := bstep (se 1 (by rfl) ⟨1986992, by rfl⟩ : syracuseStep 2649323 = 3973985) B3973985
theorem B4713767 : Blo 1395517 4713767 := bstep (se 1 (by rfl) ⟨3535325, by rfl⟩ : syracuseStep 4713767 = 7070651) B7070651
theorem B3534151 : Blo 1395517 3534151 := bstep (se 1 (by rfl) ⟨2650613, by rfl⟩ : syracuseStep 3534151 = 5301227) B5301227
theorem B7548299 : Blo 1395517 7548299 := bstep (se 1 (by rfl) ⟨5661224, by rfl⟩ : syracuseStep 7548299 = 11322449) B11322449
theorem B1396175 : Blo 1395517 1396175 := bstep (se 1 (by rfl) ⟨1047131, by rfl⟩ : syracuseStep 1396175 = 2094263) B2094263
theorem B16977397 : Blo 1395517 16977397 := bstep (se 5 (by rfl) ⟨795815, by rfl⟩ : syracuseStep 16977397 = 1591631) B1591631
theorem B6049337 : Blo 1395517 6049337 := bstep (se 2 (by rfl) ⟨2268501, by rfl⟩ : syracuseStep 6049337 = 4537003) B4537003
theorem B7949927 : Blo 1395517 7949927 := bstep (se 1 (by rfl) ⟨5962445, by rfl⟩ : syracuseStep 7949927 = 11924891) B11924891
theorem B1396335 : Blo 1395517 1396335 := bstep (se 1 (by rfl) ⟨1047251, by rfl⟩ : syracuseStep 1396335 = 2094503) B2094503
theorem B26832545 : Blo 1395517 26832545 := bstep (se 2 (by rfl) ⟨10062204, by rfl⟩ : syracuseStep 26832545 = 20124409) B20124409
theorem B1396455 : Blo 1395517 1396455 := bstep (se 1 (by rfl) ⟨1047341, by rfl⟩ : syracuseStep 1396455 = 2094683) B2094683
theorem B7950109 : Blo 1395517 7950109 := bstep (se 3 (by rfl) ⟨1490645, by rfl⟩ : syracuseStep 7950109 = 2981291) B2981291
theorem B1396763 : Blo 1395517 1396763 := bstep (se 1 (by rfl) ⟨1047572, by rfl⟩ : syracuseStep 1396763 = 2095145) B2095145
theorem B1396783 : Blo 1395517 1396783 := bstep (se 1 (by rfl) ⟨1047587, by rfl⟩ : syracuseStep 1396783 = 2095175) B2095175
theorem B4247599 : Blo 1395517 4247599 := bstep (se 1 (by rfl) ⟨3185699, by rfl⟩ : syracuseStep 4247599 = 6371399) B6371399
theorem B4714739 : Blo 1395517 4714739 := bstep (se 1 (by rfl) ⟨3536054, by rfl⟩ : syracuseStep 4714739 = 7072109) B7072109
theorem B1397039 : Blo 1395517 1397039 := bstep (se 1 (by rfl) ⟨1047779, by rfl⟩ : syracuseStep 1397039 = 2095559) B2095559
theorem B2871599 : Blo 1395517 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B4714847 : Blo 1395517 4714847 := bstep (se 1 (by rfl) ⟨3536135, by rfl⟩ : syracuseStep 4714847 = 7072271) B7072271
theorem B2093435 : Blo 1395517 2093435 := bstep (se 1 (by rfl) ⟨1570076, by rfl⟩ : syracuseStep 2093435 = 3140153) B3140153
theorem B1397183 : Blo 1395517 1397183 := bstep (se 1 (by rfl) ⟨1047887, by rfl⟩ : syracuseStep 1397183 = 2095775) B2095775
theorem B1397279 : Blo 1395517 1397279 := bstep (se 1 (by rfl) ⟨1047959, by rfl⟩ : syracuseStep 1397279 = 2095919) B2095919
theorem B1397359 : Blo 1395517 1397359 := bstep (se 1 (by rfl) ⟨1048019, by rfl⟩ : syracuseStep 1397359 = 2096039) B2096039
theorem B2093705 : Blo 1395517 2093705 := bstep (se 2 (by rfl) ⟨785139, by rfl⟩ : syracuseStep 2093705 = 1570279) B1570279
theorem B1397479 : Blo 1395517 1397479 := bstep (se 1 (by rfl) ⟨1048109, by rfl⟩ : syracuseStep 1397479 = 2096219) B2096219
theorem B5305115 : Blo 1395517 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B69833513 : Blo 1395517 69833513 := bstep (se 2 (by rfl) ⟨26187567, by rfl⟩ : syracuseStep 69833513 = 52375135) B52375135
theorem B2093915 : Blo 1395517 2093915 := bstep (se 1 (by rfl) ⟨1570436, by rfl⟩ : syracuseStep 2093915 = 3140873) B3140873
theorem B3535721 : Blo 1395517 3535721 := bstep (se 2 (by rfl) ⟨1325895, by rfl⟩ : syracuseStep 3535721 = 2651791) B2651791
theorem B2093945 : Blo 1395517 2093945 := bstep (se 2 (by rfl) ⟨785229, by rfl⟩ : syracuseStep 2093945 = 1570459) B1570459
theorem B3978143 : Blo 1395517 3978143 := bstep (se 1 (by rfl) ⟨2983607, by rfl⟩ : syracuseStep 3978143 = 5967215) B5967215
theorem B76403735 : Blo 1395517 76403735 := bstep (se 1 (by rfl) ⟨57302801, by rfl⟩ : syracuseStep 76403735 = 114605603) B114605603
theorem B7074863 : Blo 1395517 7074863 := bstep (se 1 (by rfl) ⟨5306147, by rfl⟩ : syracuseStep 7074863 = 10612295) B10612295
theorem B5968991 : Blo 1395517 5968991 := bstep (se 1 (by rfl) ⟨4476743, by rfl⟩ : syracuseStep 5968991 = 8953487) B8953487
theorem B2356391 : Blo 1395517 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B12735791 : Blo 1395517 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B15898031 : Blo 1395517 15898031 := bstep (se 1 (by rfl) ⟨11923523, by rfl⟩ : syracuseStep 15898031 = 23847047) B23847047
theorem B8951255 : Blo 1395517 8951255 := bstep (se 1 (by rfl) ⟨6713441, by rfl⟩ : syracuseStep 8951255 = 13426883) B13426883
theorem B2094575 : Blo 1395517 2094575 := bstep (se 1 (by rfl) ⟨1570931, by rfl⟩ : syracuseStep 2094575 = 3141863) B3141863
theorem B3184147 : Blo 1395517 3184147 := bstep (se 1 (by rfl) ⟨2388110, by rfl⟩ : syracuseStep 3184147 = 4776221) B4776221
theorem B15103513 : Blo 1395517 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B22640219 : Blo 1395517 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B3184219 : Blo 1395517 3184219 := bstep (se 1 (by rfl) ⟨2388164, by rfl⟩ : syracuseStep 3184219 = 4776329) B4776329
theorem B2094695 : Blo 1395517 2094695 := bstep (se 1 (by rfl) ⟨1571021, by rfl⟩ : syracuseStep 2094695 = 3142043) B3142043
theorem B7165691 : Blo 1395517 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B10598201 : Blo 1395517 10598201 := bstep (se 2 (by rfl) ⟨3974325, by rfl⟩ : syracuseStep 10598201 = 7948651) B7948651
theorem B4716359 : Blo 1395517 4716359 := bstep (se 1 (by rfl) ⟨3537269, by rfl⟩ : syracuseStep 4716359 = 7074539) B7074539
theorem B15906779 : Blo 1395517 15906779 := bstep (se 1 (by rfl) ⟨11930084, by rfl⟩ : syracuseStep 15906779 = 23860169) B23860169
theorem B1570783 : Blo 1395517 1570783 := bstep (se 1 (by rfl) ⟨1178087, by rfl⟩ : syracuseStep 1570783 = 2356175) B2356175
theorem B2095151 : Blo 1395517 2095151 := bstep (se 1 (by rfl) ⟨1571363, by rfl⟩ : syracuseStep 2095151 = 3142727) B3142727
theorem B3143735 : Blo 1395517 3143735 := bstep (se 1 (by rfl) ⟨2357801, by rfl⟩ : syracuseStep 3143735 = 4715603) B4715603
theorem B26843237 : Blo 1395517 26843237 := bstep (se 4 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 26843237 = 5033107) B5033107
theorem B3537017 : Blo 1395517 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B2095271 : Blo 1395517 2095271 := bstep (se 1 (by rfl) ⟨1571453, by rfl⟩ : syracuseStep 2095271 = 3142907) B3142907
theorem B3979475 : Blo 1395517 3979475 := bstep (se 1 (by rfl) ⟨2984606, by rfl⟩ : syracuseStep 3979475 = 5969213) B5969213
theorem B2095415 : Blo 1395517 2095415 := bstep (se 1 (by rfl) ⟨1571561, by rfl⟩ : syracuseStep 2095415 = 3143123) B3143123
theorem B3537209 : Blo 1395517 3537209 := bstep (se 2 (by rfl) ⟨1326453, by rfl⟩ : syracuseStep 3537209 = 2652907) B2652907
theorem B3144095 : Blo 1395517 3144095 := bstep (se 1 (by rfl) ⟨2358071, by rfl⟩ : syracuseStep 3144095 = 4716143) B4716143
theorem B11925953 : Blo 1395517 11925953 := bstep (se 2 (by rfl) ⟨4472232, by rfl⟩ : syracuseStep 11925953 = 8944465) B8944465
theorem B2095595 : Blo 1395517 2095595 := bstep (se 1 (by rfl) ⟨1571696, by rfl⟩ : syracuseStep 2095595 = 3143393) B3143393
theorem B67901975 : Blo 1395517 67901975 := bstep (se 1 (by rfl) ⟨50926481, by rfl⟩ : syracuseStep 67901975 = 101852963) B101852963
theorem B33979009 : Blo 1395517 33979009 := bstep (se 2 (by rfl) ⟨12742128, by rfl⟩ : syracuseStep 33979009 = 25484257) B25484257
theorem B3775211 : Blo 1395517 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B7166717 : Blo 1395517 7166717 := bstep (se 3 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 7166717 = 2687519) B2687519
theorem B2095943 : Blo 1395517 2095943 := bstep (se 1 (by rfl) ⟨1571957, by rfl⟩ : syracuseStep 2095943 = 3143915) B3143915
theorem B16128989 : Blo 1395517 16128989 := bstep (se 3 (by rfl) ⟨3024185, by rfl⟩ : syracuseStep 16128989 = 6048371) B6048371
theorem B11934701 : Blo 1395517 11934701 := bstep (se 3 (by rfl) ⟨2237756, by rfl⟩ : syracuseStep 11934701 = 4475513) B4475513
theorem B1571935 : Blo 1395517 1571935 := bstep (se 1 (by rfl) ⟨1178951, by rfl⟩ : syracuseStep 1571935 = 2357903) B2357903
theorem B11320505 : Blo 1395517 11320505 := bstep (se 2 (by rfl) ⟨4245189, by rfl⟩ : syracuseStep 11320505 = 8490379) B8490379
theorem B5299465 : Blo 1395517 5299465 := bstep (se 2 (by rfl) ⟨1987299, by rfl⟩ : syracuseStep 5299465 = 3974599) B3974599
theorem B8944951 : Blo 1395517 8944951 := bstep (se 1 (by rfl) ⟨6708713, by rfl⟩ : syracuseStep 8944951 = 13417427) B13417427
theorem B7953983 : Blo 1395517 7953983 := bstep (se 1 (by rfl) ⟨5965487, by rfl⟩ : syracuseStep 7953983 = 11930975) B11930975
theorem B5661289 : Blo 1395517 5661289 := bstep (se 2 (by rfl) ⟨2122983, by rfl⟩ : syracuseStep 5661289 = 4245967) B4245967
theorem B23855795 : Blo 1395517 23855795 := bstep (se 1 (by rfl) ⟨17891846, by rfl⟩ : syracuseStep 23855795 = 35783693) B35783693
theorem B2982719 : Blo 1395517 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B4777127 : Blo 1395517 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B16131565 : Blo 1395517 16131565 := bstep (se 3 (by rfl) ⟨3024668, by rfl⟩ : syracuseStep 16131565 = 6049337) B6049337
theorem B8947259 : Blo 1395517 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B4712201 : Blo 1395517 4712201 := bstep (se 2 (by rfl) ⟨1767075, by rfl⟩ : syracuseStep 4712201 = 3534151) B3534151
theorem B2516807 : Blo 1395517 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B4777811 : Blo 1395517 4777811 := bstep (se 1 (by rfl) ⟨3583358, by rfl⟩ : syracuseStep 4777811 = 7166717) B7166717
theorem B22636529 : Blo 1395517 22636529 := bstep (se 2 (by rfl) ⟨8488698, by rfl⟩ : syracuseStep 22636529 = 16977397) B16977397
theorem B7956467 : Blo 1395517 7956467 := bstep (se 1 (by rfl) ⟨5967350, by rfl⟩ : syracuseStep 7956467 = 11934701) B11934701
theorem B4245529 : Blo 1395517 4245529 := bstep (se 2 (by rfl) ⟨1592073, by rfl⟩ : syracuseStep 4245529 = 3184147) B3184147
theorem B20138017 : Blo 1395517 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B186222701 : Blo 1395517 186222701 := bstep (se 3 (by rfl) ⟨34916756, by rfl⟩ : syracuseStep 186222701 = 69833513) B69833513
theorem B4245625 : Blo 1395517 4245625 := bstep (se 2 (by rfl) ⟨1592109, by rfl⟩ : syracuseStep 4245625 = 3184219) B3184219
theorem B7547003 : Blo 1395517 7547003 := bstep (se 1 (by rfl) ⟨5660252, by rfl⟩ : syracuseStep 7547003 = 11320505) B11320505
theorem B5032199 : Blo 1395517 5032199 := bstep (se 1 (by rfl) ⟨3774149, by rfl⟩ : syracuseStep 5032199 = 7548299) B7548299
theorem B5302655 : Blo 1395517 5302655 := bstep (se 1 (by rfl) ⟨3976991, by rfl⟩ : syracuseStep 5302655 = 7953983) B7953983
theorem B85985725 : Blo 1395517 85985725 := bstep (se 3 (by rfl) ⟨16122323, by rfl⟩ : syracuseStep 85985725 = 32244647) B32244647
theorem B5663465 : Blo 1395517 5663465 := bstep (se 2 (by rfl) ⟨2123799, by rfl⟩ : syracuseStep 5663465 = 4247599) B4247599
theorem B1395623 : Blo 1395517 1395623 := bstep (se 1 (by rfl) ⟨1046717, by rfl⟩ : syracuseStep 1395623 = 2093435) B2093435
theorem B1395803 : Blo 1395517 1395803 := bstep (se 1 (by rfl) ⟨1046852, by rfl⟩ : syracuseStep 1395803 = 2093705) B2093705
theorem B3353761 : Blo 1395517 3353761 := bstep (se 2 (by rfl) ⟨1257660, by rfl⟩ : syracuseStep 3353761 = 2515321) B2515321
theorem B1395943 : Blo 1395517 1395943 := bstep (se 1 (by rfl) ⟨1046957, by rfl⟩ : syracuseStep 1395943 = 2093915) B2093915
theorem B1395963 : Blo 1395517 1395963 := bstep (se 1 (by rfl) ⟨1046972, by rfl⟩ : syracuseStep 1395963 = 2093945) B2093945
theorem B10071377 : Blo 1395517 10071377 := bstep (se 2 (by rfl) ⟨3776766, by rfl⟩ : syracuseStep 10071377 = 7553533) B7553533
theorem B10071545 : Blo 1395517 10071545 := bstep (se 2 (by rfl) ⟨3776829, by rfl⟩ : syracuseStep 10071545 = 7553659) B7553659
theorem B45305345 : Blo 1395517 45305345 := bstep (se 2 (by rfl) ⟨16989504, by rfl⟩ : syracuseStep 45305345 = 33979009) B33979009
theorem B8490527 : Blo 1395517 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B5967503 : Blo 1395517 5967503 := bstep (se 1 (by rfl) ⟨4475627, by rfl⟩ : syracuseStep 5967503 = 8951255) B8951255
theorem B1396383 : Blo 1395517 1396383 := bstep (se 1 (by rfl) ⟨1047287, by rfl⟩ : syracuseStep 1396383 = 2094575) B2094575
theorem B14331617 : Blo 1395517 14331617 := bstep (se 2 (by rfl) ⟨5374356, by rfl⟩ : syracuseStep 14331617 = 10748713) B10748713
theorem B15093479 : Blo 1395517 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B1396463 : Blo 1395517 1396463 := bstep (se 1 (by rfl) ⟨1047347, by rfl⟩ : syracuseStep 1396463 = 2094695) B2094695
theorem B7065467 : Blo 1395517 7065467 := bstep (se 1 (by rfl) ⟨5299100, by rfl⟩ : syracuseStep 7065467 = 10598201) B10598201
theorem B2650067 : Blo 1395517 2650067 := bstep (se 1 (by rfl) ⟨1987550, by rfl⟩ : syracuseStep 2650067 = 3975101) B3975101
theorem B10604519 : Blo 1395517 10604519 := bstep (se 1 (by rfl) ⟨7953389, by rfl⟩ : syracuseStep 10604519 = 15906779) B15906779
theorem B1396767 : Blo 1395517 1396767 := bstep (se 1 (by rfl) ⟨1047575, by rfl⟩ : syracuseStep 1396767 = 2095151) B2095151
theorem B17895491 : Blo 1395517 17895491 := bstep (se 1 (by rfl) ⟨13421618, by rfl⟩ : syracuseStep 17895491 = 26843237) B26843237
theorem B1396847 : Blo 1395517 1396847 := bstep (se 1 (by rfl) ⟨1047635, by rfl⟩ : syracuseStep 1396847 = 2095271) B2095271
theorem B1396943 : Blo 1395517 1396943 := bstep (se 1 (by rfl) ⟨1047707, by rfl⟩ : syracuseStep 1396943 = 2095415) B2095415
theorem B2093279 : Blo 1395517 2093279 := bstep (se 1 (by rfl) ⟨1569959, by rfl⟩ : syracuseStep 2093279 = 3139919) B3139919
theorem B2093339 : Blo 1395517 2093339 := bstep (se 1 (by rfl) ⟨1570004, by rfl⟩ : syracuseStep 2093339 = 3140009) B3140009
theorem B7950635 : Blo 1395517 7950635 := bstep (se 1 (by rfl) ⟨5962976, by rfl⟩ : syracuseStep 7950635 = 11925953) B11925953
theorem B2355527 : Blo 1395517 2355527 := bstep (se 1 (by rfl) ⟨1766645, by rfl⟩ : syracuseStep 2355527 = 3533291) B3533291
theorem B1397063 : Blo 1395517 1397063 := bstep (se 1 (by rfl) ⟨1047797, by rfl⟩ : syracuseStep 1397063 = 2095595) B2095595
theorem B7065953 : Blo 1395517 7065953 := bstep (se 2 (by rfl) ⟨2649732, by rfl⟩ : syracuseStep 7065953 = 5299465) B5299465
theorem B3142151 : Blo 1395517 3142151 := bstep (se 1 (by rfl) ⟨2356613, by rfl⟩ : syracuseStep 3142151 = 4713227) B4713227
theorem B1397295 : Blo 1395517 1397295 := bstep (se 1 (by rfl) ⟨1047971, by rfl⟩ : syracuseStep 1397295 = 2095943) B2095943
theorem B10752659 : Blo 1395517 10752659 := bstep (se 1 (by rfl) ⟨8064494, by rfl⟩ : syracuseStep 10752659 = 16128989) B16128989
theorem B1766215 : Blo 1395517 1766215 := bstep (se 1 (by rfl) ⟨1324661, by rfl⟩ : syracuseStep 1766215 = 2649323) B2649323
theorem B3142511 : Blo 1395517 3142511 := bstep (se 1 (by rfl) ⟨2356883, by rfl⟩ : syracuseStep 3142511 = 4713767) B4713767
theorem B17888363 : Blo 1395517 17888363 := bstep (se 1 (by rfl) ⟨13416272, by rfl⟩ : syracuseStep 17888363 = 26832545) B26832545
theorem B2094377 : Blo 1395517 2094377 := bstep (se 2 (by rfl) ⟨785391, by rfl⟩ : syracuseStep 2094377 = 1570783) B1570783
theorem B3143159 : Blo 1395517 3143159 := bstep (se 1 (by rfl) ⟨2357369, by rfl⟩ : syracuseStep 3143159 = 4714739) B4714739
theorem B3143231 : Blo 1395517 3143231 := bstep (se 1 (by rfl) ⟨2357423, by rfl⟩ : syracuseStep 3143231 = 4714847) B4714847
theorem B22664873 : Blo 1395517 22664873 := bstep (se 2 (by rfl) ⟨8499327, by rfl⟩ : syracuseStep 22664873 = 16998655) B16998655
theorem B3536743 : Blo 1395517 3536743 := bstep (se 1 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 3536743 = 5305115) B5305115
theorem B2357147 : Blo 1395517 2357147 := bstep (se 1 (by rfl) ⟨1767860, by rfl⟩ : syracuseStep 2357147 = 3535721) B3535721
theorem B2652095 : Blo 1395517 2652095 := bstep (se 1 (by rfl) ⟨1989071, by rfl⟩ : syracuseStep 2652095 = 3978143) B3978143
theorem B50935823 : Blo 1395517 50935823 := bstep (se 1 (by rfl) ⟨38201867, by rfl⟩ : syracuseStep 50935823 = 76403735) B76403735
theorem B4716575 : Blo 1395517 4716575 := bstep (se 1 (by rfl) ⟨3537431, by rfl⟩ : syracuseStep 4716575 = 7074863) B7074863
theorem B3979327 : Blo 1395517 3979327 := bstep (se 1 (by rfl) ⟨2984495, by rfl⟩ : syracuseStep 3979327 = 5968991) B5968991
theorem B1570927 : Blo 1395517 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B7657597 : Blo 1395517 7657597 := bstep (se 3 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 7657597 = 2871599) B2871599
theorem B10598687 : Blo 1395517 10598687 := bstep (se 1 (by rfl) ⟨7949015, by rfl⟩ : syracuseStep 10598687 = 15898031) B15898031
theorem B3144239 : Blo 1395517 3144239 := bstep (se 1 (by rfl) ⟨2358179, by rfl⟩ : syracuseStep 3144239 = 4716359) B4716359
theorem B25467479 : Blo 1395517 25467479 := bstep (se 1 (by rfl) ⟨19100609, by rfl⟩ : syracuseStep 25467479 = 38201219) B38201219
theorem B11934323 : Blo 1395517 11934323 := bstep (se 1 (by rfl) ⟨8950742, by rfl⟩ : syracuseStep 11934323 = 17901485) B17901485
theorem B2095823 : Blo 1395517 2095823 := bstep (se 1 (by rfl) ⟨1571867, by rfl⟩ : syracuseStep 2095823 = 3143735) B3143735
theorem B2358011 : Blo 1395517 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B2095913 : Blo 1395517 2095913 := bstep (se 2 (by rfl) ⟨785967, by rfl⟩ : syracuseStep 2095913 = 1571935) B1571935
theorem B2652983 : Blo 1395517 2652983 := bstep (se 1 (by rfl) ⟨1989737, by rfl⟩ : syracuseStep 2652983 = 3979475) B3979475
theorem B2358139 : Blo 1395517 2358139 := bstep (se 1 (by rfl) ⟨1768604, by rfl⟩ : syracuseStep 2358139 = 3537209) B3537209
theorem B2096063 : Blo 1395517 2096063 := bstep (se 1 (by rfl) ⟨1572047, by rfl⟩ : syracuseStep 2096063 = 3144095) B3144095
theorem B16980947 : Blo 1395517 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B45267983 : Blo 1395517 45267983 := bstep (se 1 (by rfl) ⟨33950987, by rfl⟩ : syracuseStep 45267983 = 67901975) B67901975
theorem B11926601 : Blo 1395517 11926601 := bstep (se 2 (by rfl) ⟨4472475, by rfl⟩ : syracuseStep 11926601 = 8944951) B8944951
theorem B4710041 : Blo 1395517 4710041 := bstep (se 2 (by rfl) ⟨1766265, by rfl⟩ : syracuseStep 4710041 = 3532531) B3532531
theorem B24501953 : Blo 1395517 24501953 := bstep (se 2 (by rfl) ⟨9188232, by rfl⟩ : syracuseStep 24501953 = 18376465) B18376465
theorem B10600145 : Blo 1395517 10600145 := bstep (se 2 (by rfl) ⟨3975054, by rfl⟩ : syracuseStep 10600145 = 7950109) B7950109
theorem B5299951 : Blo 1395517 5299951 := bstep (se 1 (by rfl) ⟨3974963, by rfl⟩ : syracuseStep 5299951 = 7949927) B7949927
theorem B7954301 : Blo 1395517 7954301 := bstep (se 3 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 7954301 = 2982863) B2982863
theorem B5660705 : Blo 1395517 5660705 := bstep (se 2 (by rfl) ⟨2122764, by rfl⟩ : syracuseStep 5660705 = 4245529) B4245529
theorem B5300423 : Blo 1395517 5300423 := bstep (se 1 (by rfl) ⟨3975317, by rfl⟩ : syracuseStep 5300423 = 7950635) B7950635
theorem B4710635 : Blo 1395517 4710635 := bstep (se 1 (by rfl) ⟨3532976, by rfl⟩ : syracuseStep 4710635 = 7065953) B7065953
theorem B7168439 : Blo 1395517 7168439 := bstep (se 1 (by rfl) ⟨5376329, by rfl⟩ : syracuseStep 7168439 = 10752659) B10752659
theorem B114647633 : Blo 1395517 114647633 := bstep (se 2 (by rfl) ⟨42992862, by rfl⟩ : syracuseStep 114647633 = 85985725) B85985725
theorem B22643333 : Blo 1395517 22643333 := bstep (se 4 (by rfl) ⟨2122812, by rfl⟩ : syracuseStep 22643333 = 4245625) B4245625
theorem B5964839 : Blo 1395517 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B15091019 : Blo 1395517 15091019 := bstep (se 1 (by rfl) ⟨11318264, by rfl⟩ : syracuseStep 15091019 = 22636529) B22636529
theorem B33957215 : Blo 1395517 33957215 := bstep (se 1 (by rfl) ⟨25467911, by rfl⟩ : syracuseStep 33957215 = 50935823) B50935823
theorem B5031335 : Blo 1395517 5031335 := bstep (se 1 (by rfl) ⟨3773501, by rfl⟩ : syracuseStep 5031335 = 7547003) B7547003
theorem B7956215 : Blo 1395517 7956215 := bstep (se 1 (by rfl) ⟨5967161, by rfl⟩ : syracuseStep 7956215 = 11934323) B11934323
theorem B3140027 : Blo 1395517 3140027 := bstep (se 1 (by rfl) ⟨2355020, by rfl⟩ : syracuseStep 3140027 = 4710041) B4710041
theorem B9554411 : Blo 1395517 9554411 := bstep (se 1 (by rfl) ⟨7165808, by rfl⟩ : syracuseStep 9554411 = 14331617) B14331617
theorem B10062319 : Blo 1395517 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B5302867 : Blo 1395517 5302867 := bstep (se 1 (by rfl) ⟨3977150, by rfl⟩ : syracuseStep 5302867 = 7954301) B7954301
theorem B11930327 : Blo 1395517 11930327 := bstep (se 1 (by rfl) ⟨8947745, by rfl⟩ : syracuseStep 11930327 = 17895491) B17895491
theorem B1395519 : Blo 1395517 1395519 := bstep (se 1 (by rfl) ⟨1046639, by rfl⟩ : syracuseStep 1395519 = 2093279) B2093279
theorem B1395559 : Blo 1395517 1395559 := bstep (se 1 (by rfl) ⟨1046669, by rfl⟩ : syracuseStep 1395559 = 2093339) B2093339
theorem B15903863 : Blo 1395517 15903863 := bstep (se 1 (by rfl) ⟨11927897, by rfl⟩ : syracuseStep 15903863 = 23855795) B23855795
theorem B40840517 : Blo 1395517 40840517 := bstep (se 4 (by rfl) ⟨3828798, by rfl⟩ : syracuseStep 40840517 = 7657597) B7657597
theorem B7548385 : Blo 1395517 7548385 := bstep (se 2 (by rfl) ⟨2830644, by rfl⟩ : syracuseStep 7548385 = 5661289) B5661289
theorem B1396251 : Blo 1395517 1396251 := bstep (se 1 (by rfl) ⟨1047188, by rfl⟩ : syracuseStep 1396251 = 2094377) B2094377
theorem B2354953 : Blo 1395517 2354953 := bstep (se 2 (by rfl) ⟨883107, by rfl⟩ : syracuseStep 2354953 = 1766215) B1766215
theorem B15109915 : Blo 1395517 15109915 := bstep (se 1 (by rfl) ⟨11332436, by rfl⟩ : syracuseStep 15109915 = 22664873) B22664873
theorem B3141467 : Blo 1395517 3141467 := bstep (se 1 (by rfl) ⟨2356100, by rfl⟩ : syracuseStep 3141467 = 4712201) B4712201
theorem B26857453 : Blo 1395517 26857453 := bstep (se 3 (by rfl) ⟨5035772, by rfl⟩ : syracuseStep 26857453 = 10071545) B10071545
theorem B5304311 : Blo 1395517 5304311 := bstep (se 1 (by rfl) ⟨3978233, by rfl⟩ : syracuseStep 5304311 = 7956467) B7956467
theorem B3354799 : Blo 1395517 3354799 := bstep (se 1 (by rfl) ⟨2516099, by rfl⟩ : syracuseStep 3354799 = 5032199) B5032199
theorem B7065791 : Blo 1395517 7065791 := bstep (se 1 (by rfl) ⟨5299343, by rfl⟩ : syracuseStep 7065791 = 10598687) B10598687
theorem B3535103 : Blo 1395517 3535103 := bstep (se 1 (by rfl) ⟨2651327, by rfl⟩ : syracuseStep 3535103 = 5302655) B5302655
theorem B16978319 : Blo 1395517 16978319 := bstep (se 1 (by rfl) ⟨12733739, by rfl⟩ : syracuseStep 16978319 = 25467479) B25467479
theorem B1397215 : Blo 1395517 1397215 := bstep (se 1 (by rfl) ⟨1047911, by rfl⟩ : syracuseStep 1397215 = 2095823) B2095823
theorem B1397275 : Blo 1395517 1397275 := bstep (se 1 (by rfl) ⟨1047956, by rfl⟩ : syracuseStep 1397275 = 2095913) B2095913
theorem B1397375 : Blo 1395517 1397375 := bstep (se 1 (by rfl) ⟨1048031, by rfl⟩ : syracuseStep 1397375 = 2096063) B2096063
theorem B21508753 : Blo 1395517 21508753 := bstep (se 2 (by rfl) ⟨8065782, by rfl⟩ : syracuseStep 21508753 = 16131565) B16131565
theorem B7951067 : Blo 1395517 7951067 := bstep (se 1 (by rfl) ⟨5963300, by rfl⟩ : syracuseStep 7951067 = 11926601) B11926601
theorem B6714251 : Blo 1395517 6714251 := bstep (se 1 (by rfl) ⟨5035688, by rfl⟩ : syracuseStep 6714251 = 10071377) B10071377
theorem B7066601 : Blo 1395517 7066601 := bstep (se 2 (by rfl) ⟨2649975, by rfl⟩ : syracuseStep 7066601 = 5299951) B5299951
theorem B3978335 : Blo 1395517 3978335 := bstep (se 1 (by rfl) ⟨2983751, by rfl⟩ : syracuseStep 3978335 = 5967503) B5967503
theorem B4715657 : Blo 1395517 4715657 := bstep (se 2 (by rfl) ⟨1768371, by rfl⟩ : syracuseStep 4715657 = 3536743) B3536743
theorem B7066763 : Blo 1395517 7066763 := bstep (se 1 (by rfl) ⟨5300072, by rfl⟩ : syracuseStep 7066763 = 10600145) B10600145
theorem B1766711 : Blo 1395517 1766711 := bstep (se 1 (by rfl) ⟨1325033, by rfl⟩ : syracuseStep 1766711 = 2650067) B2650067
theorem B26850689 : Blo 1395517 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B5305769 : Blo 1395517 5305769 := bstep (se 2 (by rfl) ⟨1989663, by rfl⟩ : syracuseStep 5305769 = 3979327) B3979327
theorem B2094569 : Blo 1395517 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B1570351 : Blo 1395517 1570351 := bstep (se 1 (by rfl) ⟨1177763, by rfl⟩ : syracuseStep 1570351 = 2355527) B2355527
theorem B2094767 : Blo 1395517 2094767 := bstep (se 1 (by rfl) ⟨1571075, by rfl⟩ : syracuseStep 2094767 = 3142151) B3142151
theorem B1988479 : Blo 1395517 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B2095007 : Blo 1395517 2095007 := bstep (se 1 (by rfl) ⟨1571255, by rfl⟩ : syracuseStep 2095007 = 3142511) B3142511
theorem B11925575 : Blo 1395517 11925575 := bstep (se 1 (by rfl) ⟨8944181, by rfl⟩ : syracuseStep 11925575 = 17888363) B17888363
theorem B3184751 : Blo 1395517 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B2095439 : Blo 1395517 2095439 := bstep (se 1 (by rfl) ⟨1571579, by rfl⟩ : syracuseStep 2095439 = 3143159) B3143159
theorem B2095487 : Blo 1395517 2095487 := bstep (se 1 (by rfl) ⟨1571615, by rfl⟩ : syracuseStep 2095487 = 3143231) B3143231
theorem B3144185 : Blo 1395517 3144185 := bstep (se 2 (by rfl) ⟨1179069, by rfl⟩ : syracuseStep 3144185 = 2358139) B2358139
theorem B1677871 : Blo 1395517 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B3185207 : Blo 1395517 3185207 := bstep (se 1 (by rfl) ⟨2388905, by rfl⟩ : syracuseStep 3185207 = 4777811) B4777811
theorem B1571431 : Blo 1395517 1571431 := bstep (se 1 (by rfl) ⟨1178573, by rfl⟩ : syracuseStep 1571431 = 2357147) B2357147
theorem B1768063 : Blo 1395517 1768063 := bstep (se 1 (by rfl) ⟨1326047, by rfl⟩ : syracuseStep 1768063 = 2652095) B2652095
theorem B120814253 : Blo 1395517 120814253 := bstep (se 3 (by rfl) ⟨22652672, by rfl⟩ : syracuseStep 120814253 = 45305345) B45305345
theorem B3144383 : Blo 1395517 3144383 := bstep (se 1 (by rfl) ⟨2358287, by rfl⟩ : syracuseStep 3144383 = 4716575) B4716575
theorem B124148467 : Blo 1395517 124148467 := bstep (se 1 (by rfl) ⟨93111350, by rfl⟩ : syracuseStep 124148467 = 186222701) B186222701
theorem B4471681 : Blo 1395517 4471681 := bstep (se 2 (by rfl) ⟨1676880, by rfl⟩ : syracuseStep 4471681 = 3353761) B3353761
theorem B2096159 : Blo 1395517 2096159 := bstep (se 1 (by rfl) ⟨1572119, by rfl⟩ : syracuseStep 2096159 = 3144239) B3144239
theorem B3775643 : Blo 1395517 3775643 := bstep (se 1 (by rfl) ⟨2831732, by rfl⟩ : syracuseStep 3775643 = 5663465) B5663465
theorem B1572007 : Blo 1395517 1572007 := bstep (se 1 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 1572007 = 2358011) B2358011
theorem B1768655 : Blo 1395517 1768655 := bstep (se 1 (by rfl) ⟨1326491, by rfl⟩ : syracuseStep 1768655 = 2652983) B2652983
theorem B11320631 : Blo 1395517 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B30178655 : Blo 1395517 30178655 := bstep (se 1 (by rfl) ⟨22633991, by rfl⟩ : syracuseStep 30178655 = 45267983) B45267983
theorem B5660351 : Blo 1395517 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B16334635 : Blo 1395517 16334635 := bstep (se 1 (by rfl) ⟨12250976, by rfl⟩ : syracuseStep 16334635 = 24501953) B24501953
theorem B4710311 : Blo 1395517 4710311 := bstep (se 1 (by rfl) ⟨3532733, by rfl⟩ : syracuseStep 4710311 = 7065467) B7065467
theorem B7069679 : Blo 1395517 7069679 := bstep (se 1 (by rfl) ⟨5302259, by rfl⟩ : syracuseStep 7069679 = 10604519) B10604519
theorem B4710527 : Blo 1395517 4710527 := bstep (se 1 (by rfl) ⟨3532895, by rfl⟩ : syracuseStep 4710527 = 7065791) B7065791
theorem B4473065 : Blo 1395517 4473065 := bstep (se 2 (by rfl) ⟨1677399, by rfl⟩ : syracuseStep 4473065 = 3354799) B3354799
theorem B10608893 : Blo 1395517 10608893 := bstep (se 3 (by rfl) ⟨1989167, by rfl⟩ : syracuseStep 10608893 = 3978335) B3978335
theorem B76431755 : Blo 1395517 76431755 := bstep (se 1 (by rfl) ⟨57323816, by rfl⟩ : syracuseStep 76431755 = 114647633) B114647633
theorem B5300711 : Blo 1395517 5300711 := bstep (se 1 (by rfl) ⟨3975533, by rfl⟩ : syracuseStep 5300711 = 7951067) B7951067
theorem B4711067 : Blo 1395517 4711067 := bstep (se 1 (by rfl) ⟨3533300, by rfl⟩ : syracuseStep 4711067 = 7066601) B7066601
theorem B2237161 : Blo 1395517 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B4711175 : Blo 1395517 4711175 := bstep (se 1 (by rfl) ⟨3533381, by rfl⟩ : syracuseStep 4711175 = 7066763) B7066763
theorem B7070489 : Blo 1395517 7070489 := bstep (se 2 (by rfl) ⟨2651433, by rfl⟩ : syracuseStep 7070489 = 5302867) B5302867
theorem B4711229 : Blo 1395517 4711229 := bstep (se 3 (by rfl) ⟨883355, by rfl⟩ : syracuseStep 4711229 = 1766711) B1766711
theorem B10060679 : Blo 1395517 10060679 := bstep (se 1 (by rfl) ⟨7545509, by rfl⟩ : syracuseStep 10060679 = 15091019) B15091019
theorem B17900459 : Blo 1395517 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B2123167 : Blo 1395517 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B2123471 : Blo 1395517 2123471 := bstep (se 1 (by rfl) ⟨1592603, by rfl⟩ : syracuseStep 2123471 = 3185207) B3185207
theorem B10602575 : Blo 1395517 10602575 := bstep (se 1 (by rfl) ⟨7951931, by rfl⟩ : syracuseStep 10602575 = 15903863) B15903863
theorem B2517095 : Blo 1395517 2517095 := bstep (se 1 (by rfl) ⟨1887821, by rfl⟩ : syracuseStep 2517095 = 3775643) B3775643
theorem B7547087 : Blo 1395517 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B3139937 : Blo 1395517 3139937 := bstep (se 2 (by rfl) ⟨1177476, by rfl⟩ : syracuseStep 3139937 = 2354953) B2354953
theorem B20146553 : Blo 1395517 20146553 := bstep (se 2 (by rfl) ⟨7554957, by rfl⟩ : syracuseStep 20146553 = 15109915) B15109915
theorem B3140207 : Blo 1395517 3140207 := bstep (se 1 (by rfl) ⟨2355155, by rfl⟩ : syracuseStep 3140207 = 4710311) B4710311
theorem B35809937 : Blo 1395517 35809937 := bstep (se 2 (by rfl) ⟨13428726, by rfl⟩ : syracuseStep 35809937 = 26857453) B26857453
theorem B4713119 : Blo 1395517 4713119 := bstep (se 1 (by rfl) ⟨3534839, by rfl⟩ : syracuseStep 4713119 = 7069679) B7069679
theorem B3533615 : Blo 1395517 3533615 := bstep (se 1 (by rfl) ⟨2650211, by rfl⟩ : syracuseStep 3533615 = 5300423) B5300423
theorem B3140423 : Blo 1395517 3140423 := bstep (se 1 (by rfl) ⟨2355317, by rfl⟩ : syracuseStep 3140423 = 4710635) B4710635
theorem B4476167 : Blo 1395517 4476167 := bstep (se 1 (by rfl) ⟨3357125, by rfl⟩ : syracuseStep 4476167 = 6714251) B6714251
theorem B3976559 : Blo 1395517 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B22638143 : Blo 1395517 22638143 := bstep (se 1 (by rfl) ⟨16978607, by rfl⟩ : syracuseStep 22638143 = 33957215) B33957215
theorem B3354223 : Blo 1395517 3354223 := bstep (se 1 (by rfl) ⟨2515667, by rfl⟩ : syracuseStep 3354223 = 5031335) B5031335
theorem B165531289 : Blo 1395517 165531289 := bstep (se 2 (by rfl) ⟨62074233, by rfl⟩ : syracuseStep 165531289 = 124148467) B124148467
theorem B1396379 : Blo 1395517 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1396511 : Blo 1395517 1396511 := bstep (se 1 (by rfl) ⟨1047383, by rfl⟩ : syracuseStep 1396511 = 2094767) B2094767
theorem B19115837 : Blo 1395517 19115837 := bstep (se 3 (by rfl) ⟨3584219, by rfl⟩ : syracuseStep 19115837 = 7168439) B7168439
theorem B5304143 : Blo 1395517 5304143 := bstep (se 1 (by rfl) ⟨3978107, by rfl⟩ : syracuseStep 5304143 = 7956215) B7956215
theorem B1396671 : Blo 1395517 1396671 := bstep (se 1 (by rfl) ⟨1047503, by rfl⟩ : syracuseStep 1396671 = 2095007) B2095007
theorem B7950383 : Blo 1395517 7950383 := bstep (se 1 (by rfl) ⟨5962787, by rfl⟩ : syracuseStep 7950383 = 11925575) B11925575
theorem B1396959 : Blo 1395517 1396959 := bstep (se 1 (by rfl) ⟨1047719, by rfl⟩ : syracuseStep 1396959 = 2095439) B2095439
theorem B1396991 : Blo 1395517 1396991 := bstep (se 1 (by rfl) ⟨1047743, by rfl⟩ : syracuseStep 1396991 = 2095487) B2095487
theorem B2093351 : Blo 1395517 2093351 := bstep (se 1 (by rfl) ⟨1570013, by rfl⟩ : syracuseStep 2093351 = 3140027) B3140027
theorem B6369607 : Blo 1395517 6369607 := bstep (se 1 (by rfl) ⟨4777205, by rfl⟩ : syracuseStep 6369607 = 9554411) B9554411
theorem B10064513 : Blo 1395517 10064513 := bstep (se 2 (by rfl) ⟨3774192, by rfl⟩ : syracuseStep 10064513 = 7548385) B7548385
theorem B1397439 : Blo 1395517 1397439 := bstep (se 1 (by rfl) ⟨1048079, by rfl⟩ : syracuseStep 1397439 = 2096159) B2096159
theorem B2093801 : Blo 1395517 2093801 := bstep (se 2 (by rfl) ⟨785175, by rfl⟩ : syracuseStep 2093801 = 1570351) B1570351
theorem B27227011 : Blo 1395517 27227011 := bstep (se 1 (by rfl) ⟨20420258, by rfl⟩ : syracuseStep 27227011 = 40840517) B40840517
theorem B21779513 : Blo 1395517 21779513 := bstep (se 2 (by rfl) ⟨8167317, by rfl⟩ : syracuseStep 21779513 = 16334635) B16334635
theorem B3773567 : Blo 1395517 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B2651305 : Blo 1395517 2651305 := bstep (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) B1988479
theorem B2094311 : Blo 1395517 2094311 := bstep (se 1 (by rfl) ⟨1570733, by rfl⟩ : syracuseStep 2094311 = 3141467) B3141467
theorem B3536207 : Blo 1395517 3536207 := bstep (se 1 (by rfl) ⟨2652155, by rfl⟩ : syracuseStep 3536207 = 5304311) B5304311
theorem B3773803 : Blo 1395517 3773803 := bstep (se 1 (by rfl) ⟨2830352, by rfl⟩ : syracuseStep 3773803 = 5660705) B5660705
theorem B2356735 : Blo 1395517 2356735 := bstep (se 1 (by rfl) ⟨1767551, by rfl⟩ : syracuseStep 2356735 = 3535103) B3535103
theorem B11318879 : Blo 1395517 11318879 := bstep (se 1 (by rfl) ⟨8489159, by rfl⟩ : syracuseStep 11318879 = 16978319) B16978319
theorem B15095555 : Blo 1395517 15095555 := bstep (se 1 (by rfl) ⟨11321666, by rfl⟩ : syracuseStep 15095555 = 22643333) B22643333
theorem B4716413 : Blo 1395517 4716413 := bstep (se 3 (by rfl) ⟨884327, by rfl⟩ : syracuseStep 4716413 = 1768655) B1768655
theorem B13416425 : Blo 1395517 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B3143771 : Blo 1395517 3143771 := bstep (se 1 (by rfl) ⟨2357828, by rfl⟩ : syracuseStep 3143771 = 4715657) B4715657
theorem B2095241 : Blo 1395517 2095241 := bstep (se 2 (by rfl) ⟨785715, by rfl⟩ : syracuseStep 2095241 = 1571431) B1571431
theorem B2357417 : Blo 1395517 2357417 := bstep (se 2 (by rfl) ⟨884031, by rfl⟩ : syracuseStep 2357417 = 1768063) B1768063
theorem B28678337 : Blo 1395517 28678337 := bstep (se 2 (by rfl) ⟨10754376, by rfl⟩ : syracuseStep 28678337 = 21508753) B21508753
theorem B3537179 : Blo 1395517 3537179 := bstep (se 1 (by rfl) ⟨2652884, by rfl⟩ : syracuseStep 3537179 = 5305769) B5305769
theorem B5962241 : Blo 1395517 5962241 := bstep (se 2 (by rfl) ⟨2235840, by rfl⟩ : syracuseStep 5962241 = 4471681) B4471681
theorem B2096009 : Blo 1395517 2096009 := bstep (se 2 (by rfl) ⟨786003, by rfl⟩ : syracuseStep 2096009 = 1572007) B1572007
theorem B2096123 : Blo 1395517 2096123 := bstep (se 1 (by rfl) ⟨1572092, by rfl⟩ : syracuseStep 2096123 = 3144185) B3144185
theorem B80542835 : Blo 1395517 80542835 := bstep (se 1 (by rfl) ⟨60407126, by rfl⟩ : syracuseStep 80542835 = 120814253) B120814253
theorem B2096255 : Blo 1395517 2096255 := bstep (se 1 (by rfl) ⟨1572191, by rfl⟩ : syracuseStep 2096255 = 3144383) B3144383
theorem B7953551 : Blo 1395517 7953551 := bstep (se 1 (by rfl) ⟨5965163, by rfl⟩ : syracuseStep 7953551 = 11930327) B11930327
theorem B20119103 : Blo 1395517 20119103 := bstep (se 1 (by rfl) ⟨15089327, by rfl⟩ : syracuseStep 20119103 = 30178655) B30178655
theorem B5300255 : Blo 1395517 5300255 := bstep (se 1 (by rfl) ⟨3975191, by rfl⟩ : syracuseStep 5300255 = 7950383) B7950383
theorem B2982043 : Blo 1395517 2982043 := bstep (se 1 (by rfl) ⟨2236532, by rfl⟩ : syracuseStep 2982043 = 4473065) B4473065
theorem B50954503 : Blo 1395517 50954503 := bstep (se 1 (by rfl) ⟨38215877, by rfl⟩ : syracuseStep 50954503 = 76431755) B76431755
theorem B6709675 : Blo 1395517 6709675 := bstep (se 1 (by rfl) ⟨5032256, by rfl⟩ : syracuseStep 6709675 = 10064513) B10064513
theorem B2515711 : Blo 1395517 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B2982881 : Blo 1395517 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B5031391 : Blo 1395517 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B3974827 : Blo 1395517 3974827 := bstep (se 1 (by rfl) ⟨2981120, by rfl⟩ : syracuseStep 3974827 = 5962241) B5962241
theorem B23873291 : Blo 1395517 23873291 := bstep (se 1 (by rfl) ⟨17904968, by rfl⟩ : syracuseStep 23873291 = 35809937) B35809937
theorem B5031737 : Blo 1395517 5031737 := bstep (se 2 (by rfl) ⟨1886901, by rfl⟩ : syracuseStep 5031737 = 3773803) B3773803
theorem B5302367 : Blo 1395517 5302367 := bstep (se 1 (by rfl) ⟨3976775, by rfl⟩ : syracuseStep 5302367 = 7953551) B7953551
theorem B2984111 : Blo 1395517 2984111 := bstep (se 1 (by rfl) ⟨2238083, by rfl⟩ : syracuseStep 2984111 = 4476167) B4476167
theorem B13412735 : Blo 1395517 13412735 := bstep (se 1 (by rfl) ⟨10059551, by rfl⟩ : syracuseStep 13412735 = 20119103) B20119103
theorem B15092095 : Blo 1395517 15092095 := bstep (se 1 (by rfl) ⟨11319071, by rfl⟩ : syracuseStep 15092095 = 22638143) B22638143
theorem B3140351 : Blo 1395517 3140351 := bstep (se 1 (by rfl) ⟨2355263, by rfl⟩ : syracuseStep 3140351 = 4710527) B4710527
theorem B7072595 : Blo 1395517 7072595 := bstep (se 1 (by rfl) ⟨5304446, by rfl⟩ : syracuseStep 7072595 = 10608893) B10608893
theorem B1395567 : Blo 1395517 1395567 := bstep (se 1 (by rfl) ⟨1046675, by rfl⟩ : syracuseStep 1395567 = 2093351) B2093351
theorem B6712253 : Blo 1395517 6712253 := bstep (se 3 (by rfl) ⟨1258547, by rfl⟩ : syracuseStep 6712253 = 2517095) B2517095
theorem B3533807 : Blo 1395517 3533807 := bstep (se 1 (by rfl) ⟨2650355, by rfl⟩ : syracuseStep 3533807 = 5300711) B5300711
theorem B3140711 : Blo 1395517 3140711 := bstep (se 1 (by rfl) ⟨2355533, by rfl⟩ : syracuseStep 3140711 = 4711067) B4711067
theorem B1395867 : Blo 1395517 1395867 := bstep (se 1 (by rfl) ⟨1046900, by rfl⟩ : syracuseStep 1395867 = 2093801) B2093801
theorem B3140783 : Blo 1395517 3140783 := bstep (se 1 (by rfl) ⟨2355587, by rfl⟩ : syracuseStep 3140783 = 4711175) B4711175
theorem B4713659 : Blo 1395517 4713659 := bstep (se 1 (by rfl) ⟨3535244, by rfl⟩ : syracuseStep 4713659 = 7070489) B7070489
theorem B3140819 : Blo 1395517 3140819 := bstep (se 1 (by rfl) ⟨2355614, by rfl⟩ : syracuseStep 3140819 = 4711229) B4711229
theorem B14519675 : Blo 1395517 14519675 := bstep (se 1 (by rfl) ⟨10889756, by rfl⟩ : syracuseStep 14519675 = 21779513) B21779513
theorem B1396207 : Blo 1395517 1396207 := bstep (se 1 (by rfl) ⟨1047155, by rfl⟩ : syracuseStep 1396207 = 2094311) B2094311
theorem B10063703 : Blo 1395517 10063703 := bstep (se 1 (by rfl) ⟨7547777, by rfl⟩ : syracuseStep 10063703 = 15095555) B15095555
theorem B36302681 : Blo 1395517 36302681 := bstep (se 2 (by rfl) ⟨13613505, by rfl⟩ : syracuseStep 36302681 = 27227011) B27227011
theorem B1396827 : Blo 1395517 1396827 := bstep (se 1 (by rfl) ⟨1047620, by rfl⟩ : syracuseStep 1396827 = 2095241) B2095241
theorem B3535073 : Blo 1395517 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B2093291 : Blo 1395517 2093291 := bstep (se 1 (by rfl) ⟨1569968, by rfl⟩ : syracuseStep 2093291 = 3139937) B3139937
theorem B13431035 : Blo 1395517 13431035 := bstep (se 1 (by rfl) ⟨10073276, by rfl⟩ : syracuseStep 13431035 = 20146553) B20146553
theorem B30183677 : Blo 1395517 30183677 := bstep (se 3 (by rfl) ⟨5659439, by rfl⟩ : syracuseStep 30183677 = 11318879) B11318879
theorem B2093471 : Blo 1395517 2093471 := bstep (se 1 (by rfl) ⟨1570103, by rfl⟩ : syracuseStep 2093471 = 3140207) B3140207
theorem B3142079 : Blo 1395517 3142079 := bstep (se 1 (by rfl) ⟨2356559, by rfl⟩ : syracuseStep 3142079 = 4713119) B4713119
theorem B2355743 : Blo 1395517 2355743 := bstep (se 1 (by rfl) ⟨1766807, by rfl⟩ : syracuseStep 2355743 = 3533615) B3533615
theorem B2830889 : Blo 1395517 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B2093615 : Blo 1395517 2093615 := bstep (se 1 (by rfl) ⟨1570211, by rfl⟩ : syracuseStep 2093615 = 3140423) B3140423
theorem B1397339 : Blo 1395517 1397339 := bstep (se 1 (by rfl) ⟨1048004, by rfl⟩ : syracuseStep 1397339 = 2096009) B2096009
theorem B1397415 : Blo 1395517 1397415 := bstep (se 1 (by rfl) ⟨1048061, by rfl⟩ : syracuseStep 1397415 = 2096123) B2096123
theorem B3142313 : Blo 1395517 3142313 := bstep (se 2 (by rfl) ⟨1178367, by rfl⟩ : syracuseStep 3142313 = 2356735) B2356735
theorem B53695223 : Blo 1395517 53695223 := bstep (se 1 (by rfl) ⟨40271417, by rfl⟩ : syracuseStep 53695223 = 80542835) B80542835
theorem B1397503 : Blo 1395517 1397503 := bstep (se 1 (by rfl) ⟨1048127, by rfl⟩ : syracuseStep 1397503 = 2096255) B2096255
theorem B2651039 : Blo 1395517 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B12743891 : Blo 1395517 12743891 := bstep (se 1 (by rfl) ⟨9557918, by rfl⟩ : syracuseStep 12743891 = 19115837) B19115837
theorem B3536095 : Blo 1395517 3536095 := bstep (se 1 (by rfl) ⟨2652071, by rfl⟩ : syracuseStep 3536095 = 5304143) B5304143
theorem B8492809 : Blo 1395517 8492809 := bstep (se 2 (by rfl) ⟨3184803, by rfl⟩ : syracuseStep 8492809 = 6369607) B6369607
theorem B6707119 : Blo 1395517 6707119 := bstep (se 1 (by rfl) ⟨5030339, by rfl⟩ : syracuseStep 6707119 = 10060679) B10060679
theorem B11933639 : Blo 1395517 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B2357471 : Blo 1395517 2357471 := bstep (se 1 (by rfl) ⟨1768103, by rfl⟩ : syracuseStep 2357471 = 3536207) B3536207
theorem B1415647 : Blo 1395517 1415647 := bstep (se 1 (by rfl) ⟨1061735, by rfl⟩ : syracuseStep 1415647 = 2123471) B2123471
theorem B3144275 : Blo 1395517 3144275 := bstep (se 1 (by rfl) ⟨2358206, by rfl⟩ : syracuseStep 3144275 = 4716413) B4716413
theorem B8944283 : Blo 1395517 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B7068383 : Blo 1395517 7068383 := bstep (se 1 (by rfl) ⟨5301287, by rfl⟩ : syracuseStep 7068383 = 10602575) B10602575
theorem B2095847 : Blo 1395517 2095847 := bstep (se 1 (by rfl) ⟨1571885, by rfl⟩ : syracuseStep 2095847 = 3143771) B3143771
theorem B1571611 : Blo 1395517 1571611 := bstep (se 1 (by rfl) ⟨1178708, by rfl⟩ : syracuseStep 1571611 = 2357417) B2357417
theorem B19118891 : Blo 1395517 19118891 := bstep (se 1 (by rfl) ⟨14339168, by rfl⟩ : syracuseStep 19118891 = 28678337) B28678337
theorem B2358119 : Blo 1395517 2358119 := bstep (se 1 (by rfl) ⟨1768589, by rfl⟩ : syracuseStep 2358119 = 3537179) B3537179
theorem B4472297 : Blo 1395517 4472297 := bstep (se 2 (by rfl) ⟨1677111, by rfl⟩ : syracuseStep 4472297 = 3354223) B3354223
theorem B220708385 : Blo 1395517 220708385 := bstep (se 2 (by rfl) ⟨82765644, by rfl⟩ : syracuseStep 220708385 = 165531289) B165531289
theorem B8954023 : Blo 1395517 8954023 := bstep (se 1 (by rfl) ⟨6715517, by rfl⟩ : syracuseStep 8954023 = 13431035) B13431035
theorem B8946233 : Blo 1395517 8946233 := bstep (se 2 (by rfl) ⟨3354837, by rfl⟩ : syracuseStep 8946233 = 6709675) B6709675
theorem B8495927 : Blo 1395517 8495927 := bstep (se 1 (by rfl) ⟨6371945, by rfl⟩ : syracuseStep 8495927 = 12743891) B12743891
theorem B7955759 : Blo 1395517 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B4712255 : Blo 1395517 4712255 := bstep (se 1 (by rfl) ⟨3534191, by rfl⟩ : syracuseStep 4712255 = 7068383) B7068383
theorem B4474835 : Blo 1395517 4474835 := bstep (se 1 (by rfl) ⟨3356126, by rfl⟩ : syracuseStep 4474835 = 6712253) B6712253
theorem B11323745 : Blo 1395517 11323745 := bstep (se 2 (by rfl) ⟨4246404, by rfl⟩ : syracuseStep 11323745 = 8492809) B8492809
theorem B147138923 : Blo 1395517 147138923 := bstep (se 1 (by rfl) ⟨110354192, by rfl⟩ : syracuseStep 147138923 = 220708385) B220708385
theorem B24201787 : Blo 1395517 24201787 := bstep (se 1 (by rfl) ⟨18151340, by rfl⟩ : syracuseStep 24201787 = 36302681) B36302681
theorem B3533503 : Blo 1395517 3533503 := bstep (se 1 (by rfl) ⟨2650127, by rfl⟩ : syracuseStep 3533503 = 5300255) B5300255
theorem B1395527 : Blo 1395517 1395527 := bstep (se 1 (by rfl) ⟨1046645, by rfl⟩ : syracuseStep 1395527 = 2093291) B2093291
theorem B20122451 : Blo 1395517 20122451 := bstep (se 1 (by rfl) ⟨15091838, by rfl⟩ : syracuseStep 20122451 = 30183677) B30183677
theorem B3976057 : Blo 1395517 3976057 := bstep (se 2 (by rfl) ⟨1491021, by rfl⟩ : syracuseStep 3976057 = 2982043) B2982043
theorem B1395647 : Blo 1395517 1395647 := bstep (se 1 (by rfl) ⟨1046735, by rfl⟩ : syracuseStep 1395647 = 2093471) B2093471
theorem B67939337 : Blo 1395517 67939337 := bstep (se 2 (by rfl) ⟨25477251, by rfl⟩ : syracuseStep 67939337 = 50954503) B50954503
theorem B1395743 : Blo 1395517 1395743 := bstep (se 1 (by rfl) ⟨1046807, by rfl⟩ : syracuseStep 1395743 = 2093615) B2093615
theorem B20122793 : Blo 1395517 20122793 := bstep (se 2 (by rfl) ⟨7546047, by rfl⟩ : syracuseStep 20122793 = 15092095) B15092095
theorem B3354281 : Blo 1395517 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B3354491 : Blo 1395517 3354491 := bstep (se 1 (by rfl) ⟨2515868, by rfl⟩ : syracuseStep 3354491 = 5031737) B5031737
theorem B3534911 : Blo 1395517 3534911 := bstep (se 1 (by rfl) ⟨2651183, by rfl⟩ : syracuseStep 3534911 = 5302367) B5302367
theorem B7549037 : Blo 1395517 7549037 := bstep (se 3 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 7549037 = 2830889) B2830889
theorem B8941823 : Blo 1395517 8941823 := bstep (se 1 (by rfl) ⟨6706367, by rfl⟩ : syracuseStep 8941823 = 13412735) B13412735
theorem B4714793 : Blo 1395517 4714793 := bstep (se 2 (by rfl) ⟨1768047, by rfl⟩ : syracuseStep 4714793 = 3536095) B3536095
theorem B23851421 : Blo 1395517 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B1397231 : Blo 1395517 1397231 := bstep (se 1 (by rfl) ⟨1047923, by rfl⟩ : syracuseStep 1397231 = 2095847) B2095847
theorem B2093567 : Blo 1395517 2093567 := bstep (se 1 (by rfl) ⟨1570175, by rfl⟩ : syracuseStep 2093567 = 3140351) B3140351
theorem B4715063 : Blo 1395517 4715063 := bstep (se 1 (by rfl) ⟨3536297, by rfl⟩ : syracuseStep 4715063 = 7072595) B7072595
theorem B2355871 : Blo 1395517 2355871 := bstep (se 1 (by rfl) ⟨1766903, by rfl⟩ : syracuseStep 2355871 = 3533807) B3533807
theorem B2093807 : Blo 1395517 2093807 := bstep (se 1 (by rfl) ⟨1570355, by rfl⟩ : syracuseStep 2093807 = 3140711) B3140711
theorem B2093855 : Blo 1395517 2093855 := bstep (se 1 (by rfl) ⟨1570391, by rfl⟩ : syracuseStep 2093855 = 3140783) B3140783
theorem B3142439 : Blo 1395517 3142439 := bstep (se 1 (by rfl) ⟨2356829, by rfl⟩ : syracuseStep 3142439 = 4713659) B4713659
theorem B2093879 : Blo 1395517 2093879 := bstep (se 1 (by rfl) ⟨1570409, by rfl⟩ : syracuseStep 2093879 = 3140819) B3140819
theorem B9679783 : Blo 1395517 9679783 := bstep (se 1 (by rfl) ⟨7259837, by rfl⟩ : syracuseStep 9679783 = 14519675) B14519675
theorem B7550117 : Blo 1395517 7550117 := bstep (se 4 (by rfl) ⟨707823, by rfl⟩ : syracuseStep 7550117 = 1415647) B1415647
theorem B8942825 : Blo 1395517 8942825 := bstep (se 2 (by rfl) ⟨3353559, by rfl⟩ : syracuseStep 8942825 = 6707119) B6707119
theorem B2356715 : Blo 1395517 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B2094719 : Blo 1395517 2094719 := bstep (se 1 (by rfl) ⟨1571039, by rfl⟩ : syracuseStep 2094719 = 3142079) B3142079
theorem B1570495 : Blo 1395517 1570495 := bstep (se 1 (by rfl) ⟨1177871, by rfl⟩ : syracuseStep 1570495 = 2355743) B2355743
theorem B2094875 : Blo 1395517 2094875 := bstep (se 1 (by rfl) ⟨1571156, by rfl⟩ : syracuseStep 2094875 = 3142313) B3142313
theorem B35796815 : Blo 1395517 35796815 := bstep (se 1 (by rfl) ⟨26847611, by rfl⟩ : syracuseStep 35796815 = 53695223) B53695223
theorem B1767359 : Blo 1395517 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B1988587 : Blo 1395517 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B2095481 : Blo 1395517 2095481 := bstep (se 2 (by rfl) ⟨785805, by rfl⟩ : syracuseStep 2095481 = 1571611) B1571611
theorem B15915527 : Blo 1395517 15915527 := bstep (se 1 (by rfl) ⟨11936645, by rfl⟩ : syracuseStep 15915527 = 23873291) B23873291
theorem B1989407 : Blo 1395517 1989407 := bstep (se 1 (by rfl) ⟨1492055, by rfl⟩ : syracuseStep 1989407 = 2984111) B2984111
theorem B1571647 : Blo 1395517 1571647 := bstep (se 1 (by rfl) ⟨1178735, by rfl⟩ : syracuseStep 1571647 = 2357471) B2357471
theorem B2096183 : Blo 1395517 2096183 := bstep (se 1 (by rfl) ⟨1572137, by rfl⟩ : syracuseStep 2096183 = 3144275) B3144275
theorem B12745927 : Blo 1395517 12745927 := bstep (se 1 (by rfl) ⟨9559445, by rfl⟩ : syracuseStep 12745927 = 19118891) B19118891
theorem B1572079 : Blo 1395517 1572079 := bstep (se 1 (by rfl) ⟨1179059, by rfl⟩ : syracuseStep 1572079 = 2358119) B2358119
theorem B6708521 : Blo 1395517 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B5299769 : Blo 1395517 5299769 := bstep (se 2 (by rfl) ⟨1987413, by rfl⟩ : syracuseStep 5299769 = 3974827) B3974827
theorem B26836541 : Blo 1395517 26836541 := bstep (se 3 (by rfl) ⟨5031851, by rfl⟩ : syracuseStep 26836541 = 10063703) B10063703
theorem B2981531 : Blo 1395517 2981531 := bstep (se 1 (by rfl) ⟨2236148, by rfl⟩ : syracuseStep 2981531 = 4472297) B4472297
theorem B15900947 : Blo 1395517 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B5964155 : Blo 1395517 5964155 := bstep (se 1 (by rfl) ⟨4473116, by rfl⟩ : syracuseStep 5964155 = 8946233) B8946233
theorem B32269049 : Blo 1395517 32269049 := bstep (se 2 (by rfl) ⟨12100893, by rfl⟩ : syracuseStep 32269049 = 24201787) B24201787
theorem B4711337 : Blo 1395517 4711337 := bstep (se 2 (by rfl) ⟨1766751, by rfl⟩ : syracuseStep 4711337 = 3533503) B3533503
theorem B5301409 : Blo 1395517 5301409 := bstep (se 2 (by rfl) ⟨1988028, by rfl⟩ : syracuseStep 5301409 = 3976057) B3976057
theorem B23864543 : Blo 1395517 23864543 := bstep (se 1 (by rfl) ⟨17898407, by rfl⟩ : syracuseStep 23864543 = 35796815) B35796815
theorem B2983223 : Blo 1395517 2983223 := bstep (se 1 (by rfl) ⟨2237417, by rfl⟩ : syracuseStep 2983223 = 4474835) B4474835
theorem B98092615 : Blo 1395517 98092615 := bstep (se 1 (by rfl) ⟨73569461, by rfl⟩ : syracuseStep 98092615 = 147138923) B147138923
theorem B10610351 : Blo 1395517 10610351 := bstep (se 1 (by rfl) ⟨7957763, by rfl⟩ : syracuseStep 10610351 = 15915527) B15915527
theorem B3533179 : Blo 1395517 3533179 := bstep (se 1 (by rfl) ⟨2649884, by rfl⟩ : syracuseStep 3533179 = 5299769) B5299769
theorem B4712957 : Blo 1395517 4712957 := bstep (se 3 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 4712957 = 1767359) B1767359
theorem B5032691 : Blo 1395517 5032691 := bstep (se 1 (by rfl) ⟨3774518, by rfl⟩ : syracuseStep 5032691 = 7549037) B7549037
theorem B11938697 : Blo 1395517 11938697 := bstep (se 2 (by rfl) ⟨4477011, by rfl⟩ : syracuseStep 11938697 = 8954023) B8954023
theorem B1395711 : Blo 1395517 1395711 := bstep (se 1 (by rfl) ⟨1046783, by rfl⟩ : syracuseStep 1395711 = 2093567) B2093567
theorem B1395871 : Blo 1395517 1395871 := bstep (se 1 (by rfl) ⟨1046903, by rfl⟩ : syracuseStep 1395871 = 2093807) B2093807
theorem B1395903 : Blo 1395517 1395903 := bstep (se 1 (by rfl) ⟨1046927, by rfl⟩ : syracuseStep 1395903 = 2093855) B2093855
theorem B1395919 : Blo 1395517 1395919 := bstep (se 1 (by rfl) ⟨1046939, by rfl⟩ : syracuseStep 1395919 = 2093879) B2093879
theorem B5663951 : Blo 1395517 5663951 := bstep (se 1 (by rfl) ⟨4247963, by rfl⟩ : syracuseStep 5663951 = 8495927) B8495927
theorem B5033411 : Blo 1395517 5033411 := bstep (se 1 (by rfl) ⟨3775058, by rfl⟩ : syracuseStep 5033411 = 7550117) B7550117
theorem B5303839 : Blo 1395517 5303839 := bstep (se 1 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 5303839 = 7955759) B7955759
theorem B3141161 : Blo 1395517 3141161 := bstep (se 2 (by rfl) ⟨1177935, by rfl⟩ : syracuseStep 3141161 = 2355871) B2355871
theorem B1396479 : Blo 1395517 1396479 := bstep (se 1 (by rfl) ⟨1047359, by rfl⟩ : syracuseStep 1396479 = 2094719) B2094719
theorem B1396583 : Blo 1395517 1396583 := bstep (se 1 (by rfl) ⟨1047437, by rfl⟩ : syracuseStep 1396583 = 2094875) B2094875
theorem B3141503 : Blo 1395517 3141503 := bstep (se 1 (by rfl) ⟨2356127, by rfl⟩ : syracuseStep 3141503 = 4712255) B4712255
theorem B12906377 : Blo 1395517 12906377 := bstep (se 2 (by rfl) ⟨4839891, by rfl⟩ : syracuseStep 12906377 = 9679783) B9679783
theorem B7549163 : Blo 1395517 7549163 := bstep (se 1 (by rfl) ⟨5661872, by rfl⟩ : syracuseStep 7549163 = 11323745) B11323745
theorem B1396987 : Blo 1395517 1396987 := bstep (se 1 (by rfl) ⟨1047740, by rfl⟩ : syracuseStep 1396987 = 2095481) B2095481
theorem B16994569 : Blo 1395517 16994569 := bstep (se 2 (by rfl) ⟨6372963, by rfl⟩ : syracuseStep 16994569 = 12745927) B12745927
theorem B13414967 : Blo 1395517 13414967 := bstep (se 1 (by rfl) ⟨10061225, by rfl⟩ : syracuseStep 13414967 = 20122451) B20122451
theorem B1397455 : Blo 1395517 1397455 := bstep (se 1 (by rfl) ⟨1048091, by rfl⟩ : syracuseStep 1397455 = 2096183) B2096183
theorem B5305085 : Blo 1395517 5305085 := bstep (se 3 (by rfl) ⟨994703, by rfl⟩ : syracuseStep 5305085 = 1989407) B1989407
theorem B13415195 : Blo 1395517 13415195 := bstep (se 1 (by rfl) ⟨10061396, by rfl⟩ : syracuseStep 13415195 = 20122793) B20122793
theorem B2093993 : Blo 1395517 2093993 := bstep (se 2 (by rfl) ⟨785247, by rfl⟩ : syracuseStep 2093993 = 1570495) B1570495
theorem B1987687 : Blo 1395517 1987687 := bstep (se 1 (by rfl) ⟨1490765, by rfl⟩ : syracuseStep 1987687 = 2981531) B2981531
theorem B2651449 : Blo 1395517 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B2356607 : Blo 1395517 2356607 := bstep (se 1 (by rfl) ⟨1767455, by rfl⟩ : syracuseStep 2356607 = 3534911) B3534911
theorem B5961215 : Blo 1395517 5961215 := bstep (se 1 (by rfl) ⟨4470911, by rfl⟩ : syracuseStep 5961215 = 8941823) B8941823
theorem B3143195 : Blo 1395517 3143195 := bstep (se 1 (by rfl) ⟨2357396, by rfl⟩ : syracuseStep 3143195 = 4714793) B4714793
theorem B3143375 : Blo 1395517 3143375 := bstep (se 1 (by rfl) ⟨2357531, by rfl⟩ : syracuseStep 3143375 = 4715063) B4715063
theorem B2094959 : Blo 1395517 2094959 := bstep (se 1 (by rfl) ⟨1571219, by rfl⟩ : syracuseStep 2094959 = 3142439) B3142439
theorem B5961883 : Blo 1395517 5961883 := bstep (se 1 (by rfl) ⟨4471412, by rfl⟩ : syracuseStep 5961883 = 8942825) B8942825
theorem B1571143 : Blo 1395517 1571143 := bstep (se 1 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 1571143 = 2356715) B2356715
theorem B2095529 : Blo 1395517 2095529 := bstep (se 2 (by rfl) ⟨785823, by rfl⟩ : syracuseStep 2095529 = 1571647) B1571647
theorem B2096105 : Blo 1395517 2096105 := bstep (se 2 (by rfl) ⟨786039, by rfl⟩ : syracuseStep 2096105 = 1572079) B1572079
theorem B45292891 : Blo 1395517 45292891 := bstep (se 1 (by rfl) ⟨33969668, by rfl⟩ : syracuseStep 45292891 = 67939337) B67939337
theorem B4472347 : Blo 1395517 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B8945309 : Blo 1395517 8945309 := bstep (se 3 (by rfl) ⟨1677245, by rfl⟩ : syracuseStep 8945309 = 3354491) B3354491
theorem B17891027 : Blo 1395517 17891027 := bstep (se 1 (by rfl) ⟨13418270, by rfl⟩ : syracuseStep 17891027 = 26836541) B26836541
theorem B2236187 : Blo 1395517 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B10600631 : Blo 1395517 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B22659425 : Blo 1395517 22659425 := bstep (se 2 (by rfl) ⟨8497284, by rfl⟩ : syracuseStep 22659425 = 16994569) B16994569
theorem B4710905 : Blo 1395517 4710905 := bstep (se 2 (by rfl) ⟨1766589, by rfl⟩ : syracuseStep 4710905 = 3533179) B3533179
theorem B21512699 : Blo 1395517 21512699 := bstep (se 1 (by rfl) ⟨16134524, by rfl⟩ : syracuseStep 21512699 = 32269049) B32269049
theorem B15909695 : Blo 1395517 15909695 := bstep (se 1 (by rfl) ⟨11932271, by rfl⟩ : syracuseStep 15909695 = 23864543) B23864543
theorem B7071785 : Blo 1395517 7071785 := bstep (se 2 (by rfl) ⟨2651919, by rfl⟩ : syracuseStep 7071785 = 5303839) B5303839
theorem B8604251 : Blo 1395517 8604251 := bstep (se 1 (by rfl) ⟨6453188, by rfl⟩ : syracuseStep 8604251 = 12906377) B12906377
theorem B5032775 : Blo 1395517 5032775 := bstep (se 1 (by rfl) ⟨3774581, by rfl⟩ : syracuseStep 5032775 = 7549163) B7549163
theorem B7949177 : Blo 1395517 7949177 := bstep (se 2 (by rfl) ⟨2980941, by rfl⟩ : syracuseStep 7949177 = 5961883) B5961883
theorem B3976103 : Blo 1395517 3976103 := bstep (se 1 (by rfl) ⟨2982077, by rfl⟩ : syracuseStep 3976103 = 5964155) B5964155
theorem B3140891 : Blo 1395517 3140891 := bstep (se 1 (by rfl) ⟨2355668, by rfl⟩ : syracuseStep 3140891 = 4711337) B4711337
theorem B1395995 : Blo 1395517 1395995 := bstep (se 1 (by rfl) ⟨1046996, by rfl⟩ : syracuseStep 1395995 = 2093993) B2093993
theorem B7073567 : Blo 1395517 7073567 := bstep (se 1 (by rfl) ⟨5305175, by rfl⟩ : syracuseStep 7073567 = 10610351) B10610351
theorem B1396639 : Blo 1395517 1396639 := bstep (se 1 (by rfl) ⟨1047479, by rfl⟩ : syracuseStep 1396639 = 2094959) B2094959
theorem B15896573 : Blo 1395517 15896573 := bstep (se 3 (by rfl) ⟨2980607, by rfl⟩ : syracuseStep 15896573 = 5961215) B5961215
theorem B2650249 : Blo 1395517 2650249 := bstep (se 2 (by rfl) ⟨993843, by rfl⟩ : syracuseStep 2650249 = 1987687) B1987687
theorem B1397019 : Blo 1395517 1397019 := bstep (se 1 (by rfl) ⟨1047764, by rfl⟩ : syracuseStep 1397019 = 2095529) B2095529
theorem B3141971 : Blo 1395517 3141971 := bstep (se 1 (by rfl) ⟨2356478, by rfl⟩ : syracuseStep 3141971 = 4712957) B4712957
theorem B3535265 : Blo 1395517 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B3355127 : Blo 1395517 3355127 := bstep (se 1 (by rfl) ⟨2516345, by rfl⟩ : syracuseStep 3355127 = 5032691) B5032691
theorem B7959131 : Blo 1395517 7959131 := bstep (se 1 (by rfl) ⟨5969348, by rfl⟩ : syracuseStep 7959131 = 11938697) B11938697
theorem B1397403 : Blo 1395517 1397403 := bstep (se 1 (by rfl) ⟨1048052, by rfl⟩ : syracuseStep 1397403 = 2096105) B2096105
theorem B130790153 : Blo 1395517 130790153 := bstep (se 2 (by rfl) ⟨49046307, by rfl⟩ : syracuseStep 130790153 = 98092615) B98092615
theorem B3355607 : Blo 1395517 3355607 := bstep (se 1 (by rfl) ⟨2516705, by rfl⟩ : syracuseStep 3355607 = 5033411) B5033411
theorem B2094107 : Blo 1395517 2094107 := bstep (se 1 (by rfl) ⟨1570580, by rfl⟩ : syracuseStep 2094107 = 3141161) B3141161
theorem B2094335 : Blo 1395517 2094335 := bstep (se 1 (by rfl) ⟨1570751, by rfl⟩ : syracuseStep 2094335 = 3141503) B3141503
theorem B8943311 : Blo 1395517 8943311 := bstep (se 1 (by rfl) ⟨6707483, by rfl⟩ : syracuseStep 8943311 = 13414967) B13414967
theorem B2094857 : Blo 1395517 2094857 := bstep (se 2 (by rfl) ⟨785571, by rfl⟩ : syracuseStep 2094857 = 1571143) B1571143
theorem B3536723 : Blo 1395517 3536723 := bstep (se 1 (by rfl) ⟨2652542, by rfl⟩ : syracuseStep 3536723 = 5305085) B5305085
theorem B8943463 : Blo 1395517 8943463 := bstep (se 1 (by rfl) ⟨6707597, by rfl⟩ : syracuseStep 8943463 = 13415195) B13415195
theorem B1988815 : Blo 1395517 1988815 := bstep (se 1 (by rfl) ⟨1491611, by rfl⟩ : syracuseStep 1988815 = 2983223) B2983223
theorem B1571071 : Blo 1395517 1571071 := bstep (se 1 (by rfl) ⟨1178303, by rfl⟩ : syracuseStep 1571071 = 2356607) B2356607
theorem B2095463 : Blo 1395517 2095463 := bstep (se 1 (by rfl) ⟨1571597, by rfl⟩ : syracuseStep 2095463 = 3143195) B3143195
theorem B2095583 : Blo 1395517 2095583 := bstep (se 1 (by rfl) ⟨1571687, by rfl⟩ : syracuseStep 2095583 = 3143375) B3143375
theorem B7068545 : Blo 1395517 7068545 := bstep (se 2 (by rfl) ⟨2650704, by rfl⟩ : syracuseStep 7068545 = 5301409) B5301409
theorem B60390521 : Blo 1395517 60390521 := bstep (se 2 (by rfl) ⟨22646445, by rfl⟩ : syracuseStep 60390521 = 45292891) B45292891
theorem B5963129 : Blo 1395517 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B5963165 : Blo 1395517 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B3775967 : Blo 1395517 3775967 := bstep (se 1 (by rfl) ⟨2831975, by rfl⟩ : syracuseStep 3775967 = 5663951) B5663951
theorem B5963539 : Blo 1395517 5963539 := bstep (se 1 (by rfl) ⟨4472654, by rfl⟩ : syracuseStep 5963539 = 8945309) B8945309
theorem B11927351 : Blo 1395517 11927351 := bstep (se 1 (by rfl) ⟨8945513, by rfl⟩ : syracuseStep 11927351 = 17891027) B17891027
theorem B15106283 : Blo 1395517 15106283 := bstep (se 1 (by rfl) ⟨11329712, by rfl⟩ : syracuseStep 15106283 = 22659425) B22659425
theorem B2236751 : Blo 1395517 2236751 := bstep (se 1 (by rfl) ⟨1677563, by rfl⟩ : syracuseStep 2236751 = 3355127) B3355127
theorem B2237071 : Blo 1395517 2237071 := bstep (se 1 (by rfl) ⟨1677803, by rfl⟩ : syracuseStep 2237071 = 3355607) B3355607
theorem B5736167 : Blo 1395517 5736167 := bstep (se 1 (by rfl) ⟨4302125, by rfl⟩ : syracuseStep 5736167 = 8604251) B8604251
theorem B4712363 : Blo 1395517 4712363 := bstep (se 1 (by rfl) ⟨3534272, by rfl⟩ : syracuseStep 4712363 = 7068545) B7068545
theorem B3975419 : Blo 1395517 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B3975443 : Blo 1395517 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B2517311 : Blo 1395517 2517311 := bstep (se 1 (by rfl) ⟨1887983, by rfl⟩ : syracuseStep 2517311 = 3775967) B3775967
theorem B3533665 : Blo 1395517 3533665 := bstep (se 2 (by rfl) ⟨1325124, by rfl⟩ : syracuseStep 3533665 = 2650249) B2650249
theorem B3140603 : Blo 1395517 3140603 := bstep (se 1 (by rfl) ⟨2355452, by rfl⟩ : syracuseStep 3140603 = 4710905) B4710905
theorem B1396071 : Blo 1395517 1396071 := bstep (se 1 (by rfl) ⟨1047053, by rfl⟩ : syracuseStep 1396071 = 2094107) B2094107
theorem B1396223 : Blo 1395517 1396223 := bstep (se 1 (by rfl) ⟨1047167, by rfl⟩ : syracuseStep 1396223 = 2094335) B2094335
theorem B1396571 : Blo 1395517 1396571 := bstep (se 1 (by rfl) ⟨1047428, by rfl⟩ : syracuseStep 1396571 = 2094857) B2094857
theorem B4714523 : Blo 1395517 4714523 := bstep (se 1 (by rfl) ⟨3535892, by rfl⟩ : syracuseStep 4714523 = 7071785) B7071785
theorem B1396975 : Blo 1395517 1396975 := bstep (se 1 (by rfl) ⟨1047731, by rfl⟩ : syracuseStep 1396975 = 2095463) B2095463
theorem B1397055 : Blo 1395517 1397055 := bstep (se 1 (by rfl) ⟨1047791, by rfl⟩ : syracuseStep 1397055 = 2095583) B2095583
theorem B3355183 : Blo 1395517 3355183 := bstep (se 1 (by rfl) ⟨2516387, by rfl⟩ : syracuseStep 3355183 = 5032775) B5032775
theorem B2650735 : Blo 1395517 2650735 := bstep (se 1 (by rfl) ⟨1988051, by rfl⟩ : syracuseStep 2650735 = 3976103) B3976103
theorem B40260347 : Blo 1395517 40260347 := bstep (se 1 (by rfl) ⟨30195260, by rfl⟩ : syracuseStep 40260347 = 60390521) B60390521
theorem B2093927 : Blo 1395517 2093927 := bstep (se 1 (by rfl) ⟨1570445, by rfl⟩ : syracuseStep 2093927 = 3140891) B3140891
theorem B7951385 : Blo 1395517 7951385 := bstep (se 2 (by rfl) ⟨2981769, by rfl⟩ : syracuseStep 7951385 = 5963539) B5963539
theorem B11924617 : Blo 1395517 11924617 := bstep (se 2 (by rfl) ⟨4471731, by rfl⟩ : syracuseStep 11924617 = 8943463) B8943463
theorem B4715711 : Blo 1395517 4715711 := bstep (se 1 (by rfl) ⟨3536783, by rfl⟩ : syracuseStep 4715711 = 7073567) B7073567
theorem B7951567 : Blo 1395517 7951567 := bstep (se 1 (by rfl) ⟨5963675, by rfl⟩ : syracuseStep 7951567 = 11927351) B11927351
theorem B10597715 : Blo 1395517 10597715 := bstep (se 1 (by rfl) ⟨7948286, by rfl⟩ : syracuseStep 10597715 = 15896573) B15896573
theorem B7067087 : Blo 1395517 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B2094647 : Blo 1395517 2094647 := bstep (se 1 (by rfl) ⟨1570985, by rfl⟩ : syracuseStep 2094647 = 3141971) B3141971
theorem B2651753 : Blo 1395517 2651753 := bstep (se 2 (by rfl) ⟨994407, by rfl⟩ : syracuseStep 2651753 = 1988815) B1988815
theorem B2356843 : Blo 1395517 2356843 := bstep (se 1 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 2356843 = 3535265) B3535265
theorem B14341799 : Blo 1395517 14341799 := bstep (se 1 (by rfl) ⟨10756349, by rfl⟩ : syracuseStep 14341799 = 21512699) B21512699
theorem B2094761 : Blo 1395517 2094761 := bstep (se 2 (by rfl) ⟨785535, by rfl⟩ : syracuseStep 2094761 = 1571071) B1571071
theorem B5306087 : Blo 1395517 5306087 := bstep (se 1 (by rfl) ⟨3979565, by rfl⟩ : syracuseStep 5306087 = 7959131) B7959131
theorem B87193435 : Blo 1395517 87193435 := bstep (se 1 (by rfl) ⟨65395076, by rfl⟩ : syracuseStep 87193435 = 130790153) B130790153
theorem B10606463 : Blo 1395517 10606463 := bstep (se 1 (by rfl) ⟨7954847, by rfl⟩ : syracuseStep 10606463 = 15909695) B15909695
theorem B5962207 : Blo 1395517 5962207 := bstep (se 1 (by rfl) ⟨4471655, by rfl⟩ : syracuseStep 5962207 = 8943311) B8943311
theorem B2357815 : Blo 1395517 2357815 := bstep (se 1 (by rfl) ⟨1768361, by rfl⟩ : syracuseStep 2357815 = 3536723) B3536723
theorem B5299451 : Blo 1395517 5299451 := bstep (se 1 (by rfl) ⟨3974588, by rfl⟩ : syracuseStep 5299451 = 7949177) B7949177
theorem B1491167 : Blo 1395517 1491167 := bstep (se 1 (by rfl) ⟨1118375, by rfl⟩ : syracuseStep 1491167 = 2236751) B2236751
theorem B10601117 : Blo 1395517 10601117 := bstep (se 3 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 10601117 = 3975419) B3975419
theorem B5300923 : Blo 1395517 5300923 := bstep (se 1 (by rfl) ⟨3975692, by rfl⟩ : syracuseStep 5300923 = 7951385) B7951385
theorem B4473577 : Blo 1395517 4473577 := bstep (se 2 (by rfl) ⟨1677591, by rfl⟩ : syracuseStep 4473577 = 3355183) B3355183
theorem B2982761 : Blo 1395517 2982761 := bstep (se 2 (by rfl) ⟨1118535, by rfl⟩ : syracuseStep 2982761 = 2237071) B2237071
theorem B4711391 : Blo 1395517 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B9561199 : Blo 1395517 9561199 := bstep (se 1 (by rfl) ⟨7170899, by rfl⟩ : syracuseStep 9561199 = 14341799) B14341799
theorem B4711553 : Blo 1395517 4711553 := bstep (se 2 (by rfl) ⟨1766832, by rfl⟩ : syracuseStep 4711553 = 3533665) B3533665
theorem B7070975 : Blo 1395517 7070975 := bstep (se 1 (by rfl) ⟨5303231, by rfl⟩ : syracuseStep 7070975 = 10606463) B10606463
theorem B10602089 : Blo 1395517 10602089 := bstep (se 2 (by rfl) ⟨3975783, by rfl⟩ : syracuseStep 10602089 = 7951567) B7951567
theorem B3532967 : Blo 1395517 3532967 := bstep (se 1 (by rfl) ⟨2649725, by rfl⟩ : syracuseStep 3532967 = 5299451) B5299451
theorem B10070855 : Blo 1395517 10070855 := bstep (se 1 (by rfl) ⟨7553141, by rfl⟩ : syracuseStep 10070855 = 15106283) B15106283
theorem B26840231 : Blo 1395517 26840231 := bstep (se 1 (by rfl) ⟨20130173, by rfl⟩ : syracuseStep 26840231 = 40260347) B40260347
theorem B1395951 : Blo 1395517 1395951 := bstep (se 1 (by rfl) ⟨1046963, by rfl⟩ : syracuseStep 1395951 = 2093927) B2093927
theorem B7949609 : Blo 1395517 7949609 := bstep (se 2 (by rfl) ⟨2981103, by rfl⟩ : syracuseStep 7949609 = 5962207) B5962207
theorem B3534313 : Blo 1395517 3534313 := bstep (se 2 (by rfl) ⟨1325367, by rfl⟩ : syracuseStep 3534313 = 2650735) B2650735
theorem B7065143 : Blo 1395517 7065143 := bstep (se 1 (by rfl) ⟨5298857, by rfl⟩ : syracuseStep 7065143 = 10597715) B10597715
theorem B1396431 : Blo 1395517 1396431 := bstep (se 1 (by rfl) ⟨1047323, by rfl⟩ : syracuseStep 1396431 = 2094647) B2094647
theorem B1396507 : Blo 1395517 1396507 := bstep (se 1 (by rfl) ⟨1047380, by rfl⟩ : syracuseStep 1396507 = 2094761) B2094761
theorem B3141575 : Blo 1395517 3141575 := bstep (se 1 (by rfl) ⟨2356181, by rfl⟩ : syracuseStep 3141575 = 4712363) B4712363
theorem B2650295 : Blo 1395517 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B2093735 : Blo 1395517 2093735 := bstep (se 1 (by rfl) ⟨1570301, by rfl⟩ : syracuseStep 2093735 = 3140603) B3140603
theorem B3142457 : Blo 1395517 3142457 := bstep (se 2 (by rfl) ⟨1178421, by rfl⟩ : syracuseStep 3142457 = 2356843) B2356843
theorem B116257913 : Blo 1395517 116257913 := bstep (se 2 (by rfl) ⟨43596717, by rfl⟩ : syracuseStep 116257913 = 87193435) B87193435
theorem B3143015 : Blo 1395517 3143015 := bstep (se 1 (by rfl) ⟨2357261, by rfl⟩ : syracuseStep 3143015 = 4714523) B4714523
theorem B3143753 : Blo 1395517 3143753 := bstep (se 2 (by rfl) ⟨1178907, by rfl⟩ : syracuseStep 3143753 = 2357815) B2357815
theorem B3143807 : Blo 1395517 3143807 := bstep (se 1 (by rfl) ⟨2357855, by rfl⟩ : syracuseStep 3143807 = 4715711) B4715711
theorem B1767835 : Blo 1395517 1767835 := bstep (se 1 (by rfl) ⟨1325876, by rfl⟩ : syracuseStep 1767835 = 2651753) B2651753
theorem B3824111 : Blo 1395517 3824111 := bstep (se 1 (by rfl) ⟨2868083, by rfl⟩ : syracuseStep 3824111 = 5736167) B5736167
theorem B3537391 : Blo 1395517 3537391 := bstep (se 1 (by rfl) ⟨2653043, by rfl⟩ : syracuseStep 3537391 = 5306087) B5306087
theorem B15899489 : Blo 1395517 15899489 := bstep (se 2 (by rfl) ⟨5962308, by rfl⟩ : syracuseStep 15899489 = 11924617) B11924617
theorem B1678207 : Blo 1395517 1678207 := bstep (se 1 (by rfl) ⟨1258655, by rfl⟩ : syracuseStep 1678207 = 2517311) B2517311
theorem B77505275 : Blo 1395517 77505275 := bstep (se 1 (by rfl) ⟨58128956, by rfl⟩ : syracuseStep 77505275 = 116257913) B116257913
theorem B5964769 : Blo 1395517 5964769 := bstep (se 2 (by rfl) ⟨2236788, by rfl⟩ : syracuseStep 5964769 = 4473577) B4473577
theorem B2237609 : Blo 1395517 2237609 := bstep (se 2 (by rfl) ⟨839103, by rfl⟩ : syracuseStep 2237609 = 1678207) B1678207
theorem B12748265 : Blo 1395517 12748265 := bstep (se 2 (by rfl) ⟨4780599, by rfl⟩ : syracuseStep 12748265 = 9561199) B9561199
theorem B2549407 : Blo 1395517 2549407 := bstep (se 1 (by rfl) ⟨1912055, by rfl⟩ : syracuseStep 2549407 = 3824111) B3824111
theorem B4712417 : Blo 1395517 4712417 := bstep (se 2 (by rfl) ⟨1767156, by rfl⟩ : syracuseStep 4712417 = 3534313) B3534313
theorem B17893487 : Blo 1395517 17893487 := bstep (se 1 (by rfl) ⟨13420115, by rfl⟩ : syracuseStep 17893487 = 26840231) B26840231
theorem B1395823 : Blo 1395517 1395823 := bstep (se 1 (by rfl) ⟨1046867, by rfl⟩ : syracuseStep 1395823 = 2093735) B2093735
theorem B3976445 : Blo 1395517 3976445 := bstep (se 3 (by rfl) ⟨745583, by rfl⟩ : syracuseStep 3976445 = 1491167) B1491167
theorem B3140927 : Blo 1395517 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B3141035 : Blo 1395517 3141035 := bstep (se 1 (by rfl) ⟨2355776, by rfl⟩ : syracuseStep 3141035 = 4711553) B4711553
theorem B4713983 : Blo 1395517 4713983 := bstep (se 1 (by rfl) ⟨3535487, by rfl⟩ : syracuseStep 4713983 = 7070975) B7070975
theorem B2355311 : Blo 1395517 2355311 := bstep (se 1 (by rfl) ⟨1766483, by rfl⟩ : syracuseStep 2355311 = 3532967) B3532967
theorem B6713903 : Blo 1395517 6713903 := bstep (se 1 (by rfl) ⟨5035427, by rfl⟩ : syracuseStep 6713903 = 10070855) B10070855
theorem B2094383 : Blo 1395517 2094383 := bstep (se 1 (by rfl) ⟨1570787, by rfl⟩ : syracuseStep 2094383 = 3141575) B3141575
theorem B1766863 : Blo 1395517 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B7067411 : Blo 1395517 7067411 := bstep (se 1 (by rfl) ⟨5300558, by rfl⟩ : syracuseStep 7067411 = 10601117) B10601117
theorem B2357113 : Blo 1395517 2357113 := bstep (se 2 (by rfl) ⟨883917, by rfl⟩ : syracuseStep 2357113 = 1767835) B1767835
theorem B2094971 : Blo 1395517 2094971 := bstep (se 1 (by rfl) ⟨1571228, by rfl⟩ : syracuseStep 2094971 = 3142457) B3142457
theorem B1988507 : Blo 1395517 1988507 := bstep (se 1 (by rfl) ⟨1491380, by rfl⟩ : syracuseStep 1988507 = 2982761) B2982761
theorem B4716521 : Blo 1395517 4716521 := bstep (se 2 (by rfl) ⟨1768695, by rfl⟩ : syracuseStep 4716521 = 3537391) B3537391
theorem B2095343 : Blo 1395517 2095343 := bstep (se 1 (by rfl) ⟨1571507, by rfl⟩ : syracuseStep 2095343 = 3143015) B3143015
theorem B7067897 : Blo 1395517 7067897 := bstep (se 2 (by rfl) ⟨2650461, by rfl⟩ : syracuseStep 7067897 = 5300923) B5300923
theorem B7068059 : Blo 1395517 7068059 := bstep (se 1 (by rfl) ⟨5301044, by rfl⟩ : syracuseStep 7068059 = 10602089) B10602089
theorem B2095835 : Blo 1395517 2095835 := bstep (se 1 (by rfl) ⟨1571876, by rfl⟩ : syracuseStep 2095835 = 3143753) B3143753
theorem B2095871 : Blo 1395517 2095871 := bstep (se 1 (by rfl) ⟨1571903, by rfl⟩ : syracuseStep 2095871 = 3143807) B3143807
theorem B10599659 : Blo 1395517 10599659 := bstep (se 1 (by rfl) ⟨7949744, by rfl⟩ : syracuseStep 10599659 = 15899489) B15899489
theorem B5299739 : Blo 1395517 5299739 := bstep (se 1 (by rfl) ⟨3974804, by rfl⟩ : syracuseStep 5299739 = 7949609) B7949609
theorem B4710095 : Blo 1395517 4710095 := bstep (se 1 (by rfl) ⟨3532571, by rfl⟩ : syracuseStep 4710095 = 7065143) B7065143
theorem B1491739 : Blo 1395517 1491739 := bstep (se 1 (by rfl) ⟨1118804, by rfl⟩ : syracuseStep 1491739 = 2237609) B2237609
theorem B4711607 : Blo 1395517 4711607 := bstep (se 1 (by rfl) ⟨3533705, by rfl⟩ : syracuseStep 4711607 = 7067411) B7067411
theorem B11928991 : Blo 1395517 11928991 := bstep (se 1 (by rfl) ⟨8946743, by rfl⟩ : syracuseStep 11928991 = 17893487) B17893487
theorem B4711931 : Blo 1395517 4711931 := bstep (se 1 (by rfl) ⟨3533948, by rfl⟩ : syracuseStep 4711931 = 7067897) B7067897
theorem B4712039 : Blo 1395517 4712039 := bstep (se 1 (by rfl) ⟨3534029, by rfl⟩ : syracuseStep 4712039 = 7068059) B7068059
theorem B3533159 : Blo 1395517 3533159 := bstep (se 1 (by rfl) ⟨2649869, by rfl⟩ : syracuseStep 3533159 = 5299739) B5299739
theorem B5302685 : Blo 1395517 5302685 := bstep (se 3 (by rfl) ⟨994253, by rfl⟩ : syracuseStep 5302685 = 1988507) B1988507
theorem B3140063 : Blo 1395517 3140063 := bstep (se 1 (by rfl) ⟨2355047, by rfl⟩ : syracuseStep 3140063 = 4710095) B4710095
theorem B4475935 : Blo 1395517 4475935 := bstep (se 1 (by rfl) ⟨3356951, by rfl⟩ : syracuseStep 4475935 = 6713903) B6713903
theorem B51670183 : Blo 1395517 51670183 := bstep (se 1 (by rfl) ⟨38752637, by rfl⟩ : syracuseStep 51670183 = 77505275) B77505275
theorem B1396255 : Blo 1395517 1396255 := bstep (se 1 (by rfl) ⟨1047191, by rfl⟩ : syracuseStep 1396255 = 2094383) B2094383
theorem B8498843 : Blo 1395517 8498843 := bstep (se 1 (by rfl) ⟨6374132, by rfl⟩ : syracuseStep 8498843 = 12748265) B12748265
theorem B1396647 : Blo 1395517 1396647 := bstep (se 1 (by rfl) ⟨1047485, by rfl⟩ : syracuseStep 1396647 = 2094971) B2094971
theorem B3141611 : Blo 1395517 3141611 := bstep (se 1 (by rfl) ⟨2356208, by rfl⟩ : syracuseStep 3141611 = 4712417) B4712417
theorem B1396895 : Blo 1395517 1396895 := bstep (se 1 (by rfl) ⟨1047671, by rfl⟩ : syracuseStep 1396895 = 2095343) B2095343
theorem B1397223 : Blo 1395517 1397223 := bstep (se 1 (by rfl) ⟨1047917, by rfl⟩ : syracuseStep 1397223 = 2095835) B2095835
theorem B1397247 : Blo 1395517 1397247 := bstep (se 1 (by rfl) ⟨1047935, by rfl⟩ : syracuseStep 1397247 = 2095871) B2095871
theorem B2355817 : Blo 1395517 2355817 := bstep (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) B1766863
theorem B7066439 : Blo 1395517 7066439 := bstep (se 1 (by rfl) ⟨5299829, by rfl⟩ : syracuseStep 7066439 = 10599659) B10599659
theorem B2650963 : Blo 1395517 2650963 := bstep (se 1 (by rfl) ⟨1988222, by rfl⟩ : syracuseStep 2650963 = 3976445) B3976445
theorem B2093951 : Blo 1395517 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B2094023 : Blo 1395517 2094023 := bstep (se 1 (by rfl) ⟨1570517, by rfl⟩ : syracuseStep 2094023 = 3141035) B3141035
theorem B3142655 : Blo 1395517 3142655 := bstep (se 1 (by rfl) ⟨2356991, by rfl⟩ : syracuseStep 3142655 = 4713983) B4713983
theorem B3142817 : Blo 1395517 3142817 := bstep (se 2 (by rfl) ⟨1178556, by rfl⟩ : syracuseStep 3142817 = 2357113) B2357113
theorem B1570207 : Blo 1395517 1570207 := bstep (se 1 (by rfl) ⟨1177655, by rfl⟩ : syracuseStep 1570207 = 2355311) B2355311
theorem B7953025 : Blo 1395517 7953025 := bstep (se 2 (by rfl) ⟨2982384, by rfl⟩ : syracuseStep 7953025 = 5964769) B5964769
theorem B3144347 : Blo 1395517 3144347 := bstep (se 1 (by rfl) ⟨2358260, by rfl⟩ : syracuseStep 3144347 = 4716521) B4716521
theorem B3399209 : Blo 1395517 3399209 := bstep (se 2 (by rfl) ⟨1274703, by rfl⟩ : syracuseStep 3399209 = 2549407) B2549407
theorem B4710959 : Blo 1395517 4710959 := bstep (se 1 (by rfl) ⟨3533219, by rfl⟩ : syracuseStep 4710959 = 7066439) B7066439
theorem B7955941 : Blo 1395517 7955941 := bstep (se 4 (by rfl) ⟨745869, by rfl⟩ : syracuseStep 7955941 = 1491739) B1491739
theorem B1395967 : Blo 1395517 1395967 := bstep (se 1 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 1395967 = 2093951) B2093951
theorem B1396015 : Blo 1395517 1396015 := bstep (se 1 (by rfl) ⟨1047011, by rfl⟩ : syracuseStep 1396015 = 2094023) B2094023
theorem B3141071 : Blo 1395517 3141071 := bstep (se 1 (by rfl) ⟨2355803, by rfl⟩ : syracuseStep 3141071 = 4711607) B4711607
theorem B3141089 : Blo 1395517 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B10604033 : Blo 1395517 10604033 := bstep (se 2 (by rfl) ⟨3976512, by rfl⟩ : syracuseStep 10604033 = 7953025) B7953025
theorem B3141287 : Blo 1395517 3141287 := bstep (se 1 (by rfl) ⟨2355965, by rfl⟩ : syracuseStep 3141287 = 4711931) B4711931
theorem B3141359 : Blo 1395517 3141359 := bstep (se 1 (by rfl) ⟨2356019, by rfl⟩ : syracuseStep 3141359 = 4712039) B4712039
theorem B3534617 : Blo 1395517 3534617 := bstep (se 2 (by rfl) ⟨1325481, by rfl⟩ : syracuseStep 3534617 = 2650963) B2650963
theorem B5967913 : Blo 1395517 5967913 := bstep (se 2 (by rfl) ⟨2237967, by rfl⟩ : syracuseStep 5967913 = 4475935) B4475935
theorem B2355439 : Blo 1395517 2355439 := bstep (se 1 (by rfl) ⟨1766579, by rfl⟩ : syracuseStep 2355439 = 3533159) B3533159
theorem B3535123 : Blo 1395517 3535123 := bstep (se 1 (by rfl) ⟨2651342, by rfl⟩ : syracuseStep 3535123 = 5302685) B5302685
theorem B2093375 : Blo 1395517 2093375 := bstep (se 1 (by rfl) ⟨1570031, by rfl⟩ : syracuseStep 2093375 = 3140063) B3140063
theorem B2093609 : Blo 1395517 2093609 := bstep (se 2 (by rfl) ⟨785103, by rfl⟩ : syracuseStep 2093609 = 1570207) B1570207
theorem B15905321 : Blo 1395517 15905321 := bstep (se 2 (by rfl) ⟨5964495, by rfl⟩ : syracuseStep 15905321 = 11928991) B11928991
theorem B2266139 : Blo 1395517 2266139 := bstep (se 1 (by rfl) ⟨1699604, by rfl⟩ : syracuseStep 2266139 = 3399209) B3399209
theorem B5665895 : Blo 1395517 5665895 := bstep (se 1 (by rfl) ⟨4249421, by rfl⟩ : syracuseStep 5665895 = 8498843) B8498843
theorem B2094407 : Blo 1395517 2094407 := bstep (se 1 (by rfl) ⟨1570805, by rfl⟩ : syracuseStep 2094407 = 3141611) B3141611
theorem B2095103 : Blo 1395517 2095103 := bstep (se 1 (by rfl) ⟨1571327, by rfl⟩ : syracuseStep 2095103 = 3142655) B3142655
theorem B2095211 : Blo 1395517 2095211 := bstep (se 1 (by rfl) ⟨1571408, by rfl⟩ : syracuseStep 2095211 = 3142817) B3142817
theorem B68893577 : Blo 1395517 68893577 := bstep (se 2 (by rfl) ⟨25835091, by rfl⟩ : syracuseStep 68893577 = 51670183) B51670183
theorem B2096231 : Blo 1395517 2096231 := bstep (se 1 (by rfl) ⟨1572173, by rfl⟩ : syracuseStep 2096231 = 3144347) B3144347
theorem B3777263 : Blo 1395517 3777263 := bstep (se 1 (by rfl) ⟨2832947, by rfl⟩ : syracuseStep 3777263 = 5665895) B5665895
theorem B7957217 : Blo 1395517 7957217 := bstep (se 2 (by rfl) ⟨2983956, by rfl⟩ : syracuseStep 7957217 = 5967913) B5967913
theorem B1395583 : Blo 1395517 1395583 := bstep (se 1 (by rfl) ⟨1046687, by rfl⟩ : syracuseStep 1395583 = 2093375) B2093375
theorem B3140585 : Blo 1395517 3140585 := bstep (se 2 (by rfl) ⟨1177719, by rfl⟩ : syracuseStep 3140585 = 2355439) B2355439
theorem B4713497 : Blo 1395517 4713497 := bstep (se 2 (by rfl) ⟨1767561, by rfl⟩ : syracuseStep 4713497 = 3535123) B3535123
theorem B1395739 : Blo 1395517 1395739 := bstep (se 1 (by rfl) ⟨1046804, by rfl⟩ : syracuseStep 1395739 = 2093609) B2093609
theorem B10603547 : Blo 1395517 10603547 := bstep (se 1 (by rfl) ⟨7952660, by rfl⟩ : syracuseStep 10603547 = 15905321) B15905321
theorem B3140639 : Blo 1395517 3140639 := bstep (se 1 (by rfl) ⟨2355479, by rfl⟩ : syracuseStep 3140639 = 4710959) B4710959
theorem B1510759 : Blo 1395517 1510759 := bstep (se 1 (by rfl) ⟨1133069, by rfl⟩ : syracuseStep 1510759 = 2266139) B2266139
theorem B1396271 : Blo 1395517 1396271 := bstep (se 1 (by rfl) ⟨1047203, by rfl⟩ : syracuseStep 1396271 = 2094407) B2094407
theorem B1396735 : Blo 1395517 1396735 := bstep (se 1 (by rfl) ⟨1047551, by rfl⟩ : syracuseStep 1396735 = 2095103) B2095103
theorem B1396807 : Blo 1395517 1396807 := bstep (se 1 (by rfl) ⟨1047605, by rfl⟩ : syracuseStep 1396807 = 2095211) B2095211
theorem B45929051 : Blo 1395517 45929051 := bstep (se 1 (by rfl) ⟨34446788, by rfl⟩ : syracuseStep 45929051 = 68893577) B68893577
theorem B1397487 : Blo 1395517 1397487 := bstep (se 1 (by rfl) ⟨1048115, by rfl⟩ : syracuseStep 1397487 = 2096231) B2096231
theorem B2094047 : Blo 1395517 2094047 := bstep (se 1 (by rfl) ⟨1570535, by rfl⟩ : syracuseStep 2094047 = 3141071) B3141071
theorem B2094059 : Blo 1395517 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B2094191 : Blo 1395517 2094191 := bstep (se 1 (by rfl) ⟨1570643, by rfl⟩ : syracuseStep 2094191 = 3141287) B3141287
theorem B2094239 : Blo 1395517 2094239 := bstep (se 1 (by rfl) ⟨1570679, by rfl⟩ : syracuseStep 2094239 = 3141359) B3141359
theorem B2356411 : Blo 1395517 2356411 := bstep (se 1 (by rfl) ⟨1767308, by rfl⟩ : syracuseStep 2356411 = 3534617) B3534617
theorem B10607921 : Blo 1395517 10607921 := bstep (se 2 (by rfl) ⟨3977970, by rfl⟩ : syracuseStep 10607921 = 7955941) B7955941
theorem B7069355 : Blo 1395517 7069355 := bstep (se 1 (by rfl) ⟨5302016, by rfl⟩ : syracuseStep 7069355 = 10604033) B10604033
theorem B7071947 : Blo 1395517 7071947 := bstep (se 1 (by rfl) ⟨5303960, by rfl⟩ : syracuseStep 7071947 = 10607921) B10607921
theorem B4712903 : Blo 1395517 4712903 := bstep (se 1 (by rfl) ⟨3534677, by rfl⟩ : syracuseStep 4712903 = 7069355) B7069355
theorem B2518175 : Blo 1395517 2518175 := bstep (se 1 (by rfl) ⟨1888631, by rfl⟩ : syracuseStep 2518175 = 3777263) B3777263
theorem B1396031 : Blo 1395517 1396031 := bstep (se 1 (by rfl) ⟨1047023, by rfl⟩ : syracuseStep 1396031 = 2094047) B2094047
theorem B1396039 : Blo 1395517 1396039 := bstep (se 1 (by rfl) ⟨1047029, by rfl⟩ : syracuseStep 1396039 = 2094059) B2094059
theorem B1396127 : Blo 1395517 1396127 := bstep (se 1 (by rfl) ⟨1047095, by rfl⟩ : syracuseStep 1396127 = 2094191) B2094191
theorem B1396159 : Blo 1395517 1396159 := bstep (se 1 (by rfl) ⟨1047119, by rfl⟩ : syracuseStep 1396159 = 2094239) B2094239
theorem B3141881 : Blo 1395517 3141881 := bstep (se 2 (by rfl) ⟨1178205, by rfl⟩ : syracuseStep 3141881 = 2356411) B2356411
theorem B5304811 : Blo 1395517 5304811 := bstep (se 1 (by rfl) ⟨3978608, by rfl⟩ : syracuseStep 5304811 = 7957217) B7957217
theorem B2093723 : Blo 1395517 2093723 := bstep (se 1 (by rfl) ⟨1570292, by rfl⟩ : syracuseStep 2093723 = 3140585) B3140585
theorem B3142331 : Blo 1395517 3142331 := bstep (se 1 (by rfl) ⟨2356748, by rfl⟩ : syracuseStep 3142331 = 4713497) B4713497
theorem B2093759 : Blo 1395517 2093759 := bstep (se 1 (by rfl) ⟨1570319, by rfl⟩ : syracuseStep 2093759 = 3140639) B3140639
theorem B30619367 : Blo 1395517 30619367 := bstep (se 1 (by rfl) ⟨22964525, by rfl⟩ : syracuseStep 30619367 = 45929051) B45929051
theorem B2014345 : Blo 1395517 2014345 := bstep (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) B1510759
theorem B7069031 : Blo 1395517 7069031 := bstep (se 1 (by rfl) ⟨5301773, by rfl⟩ : syracuseStep 7069031 = 10603547) B10603547
theorem B4712687 : Blo 1395517 4712687 := bstep (se 1 (by rfl) ⟨3534515, by rfl⟩ : syracuseStep 4712687 = 7069031) B7069031
theorem B1395815 : Blo 1395517 1395815 := bstep (se 1 (by rfl) ⟨1046861, by rfl⟩ : syracuseStep 1395815 = 2093723) B2093723
theorem B1395839 : Blo 1395517 1395839 := bstep (se 1 (by rfl) ⟨1046879, by rfl⟩ : syracuseStep 1395839 = 2093759) B2093759
theorem B7073081 : Blo 1395517 7073081 := bstep (se 2 (by rfl) ⟨2652405, by rfl⟩ : syracuseStep 7073081 = 5304811) B5304811
theorem B4714631 : Blo 1395517 4714631 := bstep (se 1 (by rfl) ⟨3535973, by rfl⟩ : syracuseStep 4714631 = 7071947) B7071947
theorem B3141935 : Blo 1395517 3141935 := bstep (se 1 (by rfl) ⟨2356451, by rfl⟩ : syracuseStep 3141935 = 4712903) B4712903
theorem B2094587 : Blo 1395517 2094587 := bstep (se 1 (by rfl) ⟨1570940, by rfl⟩ : syracuseStep 2094587 = 3141881) B3141881
theorem B6715133 : Blo 1395517 6715133 := bstep (se 3 (by rfl) ⟨1259087, by rfl⟩ : syracuseStep 6715133 = 2518175) B2518175
theorem B2094887 : Blo 1395517 2094887 := bstep (se 1 (by rfl) ⟨1571165, by rfl⟩ : syracuseStep 2094887 = 3142331) B3142331
theorem B20412911 : Blo 1395517 20412911 := bstep (se 1 (by rfl) ⟨15309683, by rfl⟩ : syracuseStep 20412911 = 30619367) B30619367
theorem B2685793 : Blo 1395517 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B3581057 : Blo 1395517 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B13608607 : Blo 1395517 13608607 := bstep (se 1 (by rfl) ⟨10206455, by rfl⟩ : syracuseStep 13608607 = 20412911) B20412911
theorem B1396391 : Blo 1395517 1396391 := bstep (se 1 (by rfl) ⟨1047293, by rfl⟩ : syracuseStep 1396391 = 2094587) B2094587
theorem B4476755 : Blo 1395517 4476755 := bstep (se 1 (by rfl) ⟨3357566, by rfl⟩ : syracuseStep 4476755 = 6715133) B6715133
theorem B1396591 : Blo 1395517 1396591 := bstep (se 1 (by rfl) ⟨1047443, by rfl⟩ : syracuseStep 1396591 = 2094887) B2094887
theorem B3141791 : Blo 1395517 3141791 := bstep (se 1 (by rfl) ⟨2356343, by rfl⟩ : syracuseStep 3141791 = 4712687) B4712687
theorem B4715387 : Blo 1395517 4715387 := bstep (se 1 (by rfl) ⟨3536540, by rfl⟩ : syracuseStep 4715387 = 7073081) B7073081
theorem B3143087 : Blo 1395517 3143087 := bstep (se 1 (by rfl) ⟨2357315, by rfl⟩ : syracuseStep 3143087 = 4714631) B4714631
theorem B2094623 : Blo 1395517 2094623 := bstep (se 1 (by rfl) ⟨1570967, by rfl⟩ : syracuseStep 2094623 = 3141935) B3141935
theorem B11938013 : Blo 1395517 11938013 := bstep (se 3 (by rfl) ⟨2238377, by rfl⟩ : syracuseStep 11938013 = 4476755) B4476755
theorem B1396415 : Blo 1395517 1396415 := bstep (se 1 (by rfl) ⟨1047311, by rfl⟩ : syracuseStep 1396415 = 2094623) B2094623
theorem B2094527 : Blo 1395517 2094527 := bstep (se 1 (by rfl) ⟨1570895, by rfl⟩ : syracuseStep 2094527 = 3141791) B3141791
theorem B9549485 : Blo 1395517 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B3143591 : Blo 1395517 3143591 := bstep (se 1 (by rfl) ⟨2357693, by rfl⟩ : syracuseStep 3143591 = 4715387) B4715387
theorem B2095391 : Blo 1395517 2095391 := bstep (se 1 (by rfl) ⟨1571543, by rfl⟩ : syracuseStep 2095391 = 3143087) B3143087
theorem B18144809 : Blo 1395517 18144809 := bstep (se 2 (by rfl) ⟨6804303, by rfl⟩ : syracuseStep 18144809 = 13608607) B13608607
theorem B6366323 : Blo 1395517 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B1396351 : Blo 1395517 1396351 := bstep (se 1 (by rfl) ⟨1047263, by rfl⟩ : syracuseStep 1396351 = 2094527) B2094527
theorem B7958675 : Blo 1395517 7958675 := bstep (se 1 (by rfl) ⟨5969006, by rfl⟩ : syracuseStep 7958675 = 11938013) B11938013
theorem B1396927 : Blo 1395517 1396927 := bstep (se 1 (by rfl) ⟨1047695, by rfl⟩ : syracuseStep 1396927 = 2095391) B2095391
theorem B12096539 : Blo 1395517 12096539 := bstep (se 1 (by rfl) ⟨9072404, by rfl⟩ : syracuseStep 12096539 = 18144809) B18144809
theorem B2095727 : Blo 1395517 2095727 := bstep (se 1 (by rfl) ⟨1571795, by rfl⟩ : syracuseStep 2095727 = 3143591) B3143591
theorem B16976861 : Blo 1395517 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B8064359 : Blo 1395517 8064359 := bstep (se 1 (by rfl) ⟨6048269, by rfl⟩ : syracuseStep 8064359 = 12096539) B12096539
theorem B1397151 : Blo 1395517 1397151 := bstep (se 1 (by rfl) ⟨1047863, by rfl⟩ : syracuseStep 1397151 = 2095727) B2095727
theorem B5305783 : Blo 1395517 5305783 := bstep (se 1 (by rfl) ⟨3979337, by rfl⟩ : syracuseStep 5305783 = 7958675) B7958675
theorem B5376239 : Blo 1395517 5376239 := bstep (se 1 (by rfl) ⟨4032179, by rfl⟩ : syracuseStep 5376239 = 8064359) B8064359
theorem B7074377 : Blo 1395517 7074377 := bstep (se 2 (by rfl) ⟨2652891, by rfl⟩ : syracuseStep 7074377 = 5305783) B5305783
theorem B11317907 : Blo 1395517 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B7545271 : Blo 1395517 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B3584159 : Blo 1395517 3584159 := bstep (se 1 (by rfl) ⟨2688119, by rfl⟩ : syracuseStep 3584159 = 5376239) B5376239
theorem B4716251 : Blo 1395517 4716251 := bstep (se 1 (by rfl) ⟨3537188, by rfl⟩ : syracuseStep 4716251 = 7074377) B7074377
theorem B10060361 : Blo 1395517 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B2389439 : Blo 1395517 2389439 := bstep (se 1 (by rfl) ⟨1792079, by rfl⟩ : syracuseStep 2389439 = 3584159) B3584159
theorem B3144167 : Blo 1395517 3144167 := bstep (se 1 (by rfl) ⟨2358125, by rfl⟩ : syracuseStep 3144167 = 4716251) B4716251
theorem B1592959 : Blo 1395517 1592959 := bstep (se 1 (by rfl) ⟨1194719, by rfl⟩ : syracuseStep 1592959 = 2389439) B2389439
theorem B6706907 : Blo 1395517 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B2096111 : Blo 1395517 2096111 := bstep (se 1 (by rfl) ⟨1572083, by rfl⟩ : syracuseStep 2096111 = 3144167) B3144167
theorem B2123945 : Blo 1395517 2123945 := bstep (se 2 (by rfl) ⟨796479, by rfl⟩ : syracuseStep 2123945 = 1592959) B1592959
theorem B1397407 : Blo 1395517 1397407 := bstep (se 1 (by rfl) ⟨1048055, by rfl⟩ : syracuseStep 1397407 = 2096111) B2096111
theorem B4471271 : Blo 1395517 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B1415963 : Blo 1395517 1415963 := bstep (se 1 (by rfl) ⟨1061972, by rfl⟩ : syracuseStep 1415963 = 2123945) B2123945
theorem B2980847 : Blo 1395517 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B7948925 : Blo 1395517 7948925 := bstep (se 3 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 7948925 = 2980847) B2980847
theorem B3775901 : Blo 1395517 3775901 := bstep (se 3 (by rfl) ⟨707981, by rfl⟩ : syracuseStep 3775901 = 1415963) B1415963
theorem B10069069 : Blo 1395517 10069069 := bstep (se 3 (by rfl) ⟨1887950, by rfl⟩ : syracuseStep 10069069 = 3775901) B3775901
theorem B5299283 : Blo 1395517 5299283 := bstep (se 1 (by rfl) ⟨3974462, by rfl⟩ : syracuseStep 5299283 = 7948925) B7948925
theorem B3532855 : Blo 1395517 3532855 := bstep (se 1 (by rfl) ⟨2649641, by rfl⟩ : syracuseStep 3532855 = 5299283) B5299283
theorem B13425425 : Blo 1395517 13425425 := bstep (se 2 (by rfl) ⟨5034534, by rfl⟩ : syracuseStep 13425425 = 10069069) B10069069
theorem B4710473 : Blo 1395517 4710473 := bstep (se 2 (by rfl) ⟨1766427, by rfl⟩ : syracuseStep 4710473 = 3532855) B3532855
theorem B8950283 : Blo 1395517 8950283 := bstep (se 1 (by rfl) ⟨6712712, by rfl⟩ : syracuseStep 8950283 = 13425425) B13425425
theorem B3140315 : Blo 1395517 3140315 := bstep (se 1 (by rfl) ⟨2355236, by rfl⟩ : syracuseStep 3140315 = 4710473) B4710473
theorem B5966855 : Blo 1395517 5966855 := bstep (se 1 (by rfl) ⟨4475141, by rfl⟩ : syracuseStep 5966855 = 8950283) B8950283
theorem B2093543 : Blo 1395517 2093543 := bstep (se 1 (by rfl) ⟨1570157, by rfl⟩ : syracuseStep 2093543 = 3140315) B3140315
theorem B3977903 : Blo 1395517 3977903 := bstep (se 1 (by rfl) ⟨2983427, by rfl⟩ : syracuseStep 3977903 = 5966855) B5966855
theorem B1395695 : Blo 1395517 1395695 := bstep (se 1 (by rfl) ⟨1046771, by rfl⟩ : syracuseStep 1395695 = 2093543) B2093543
theorem B2651935 : Blo 1395517 2651935 := bstep (se 1 (by rfl) ⟨1988951, by rfl⟩ : syracuseStep 2651935 = 3977903) B3977903
theorem B3535913 : Blo 1395517 3535913 := bstep (se 2 (by rfl) ⟨1325967, by rfl⟩ : syracuseStep 3535913 = 2651935) B2651935
theorem B2357275 : Blo 1395517 2357275 := bstep (se 1 (by rfl) ⟨1767956, by rfl⟩ : syracuseStep 2357275 = 3535913) B3535913
theorem B3143033 : Blo 1395517 3143033 := bstep (se 2 (by rfl) ⟨1178637, by rfl⟩ : syracuseStep 3143033 = 2357275) B2357275
theorem B2095355 : Blo 1395517 2095355 := bstep (se 1 (by rfl) ⟨1571516, by rfl⟩ : syracuseStep 2095355 = 3143033) B3143033
theorem B1396903 : Blo 1395517 1396903 := bstep (se 1 (by rfl) ⟨1047677, by rfl⟩ : syracuseStep 1396903 = 2095355) B2095355

theorem C0 (j : ℕ) (h1 : 348879 ≤ j) (h2 : j ≤ 349378) : Blo 1395517 (4 * j + 3) := by
  interval_cases j
  · exact B1395519
  · exact B1395523
  · exact B1395527
  · exact B1395531
  · exact B1395535
  · exact B1395539
  · exact B1395543
  · exact B1395547
  · exact B1395551
  · exact B1395555
  · exact B1395559
  · exact B1395563
  · exact B1395567
  · exact B1395571
  · exact B1395575
  · exact B1395579
  · exact B1395583
  · exact B1395587
  · exact B1395591
  · exact B1395595
  · exact B1395599
  · exact B1395603
  · exact B1395607
  · exact B1395611
  · exact B1395615
  · exact B1395619
  · exact B1395623
  · exact B1395627
  · exact B1395631
  · exact B1395635
  · exact B1395639
  · exact B1395643
  · exact B1395647
  · exact B1395651
  · exact B1395655
  · exact B1395659
  · exact B1395663
  · exact B1395667
  · exact B1395671
  · exact B1395675
  · exact B1395679
  · exact B1395683
  · exact B1395687
  · exact B1395691
  · exact B1395695
  · exact B1395699
  · exact B1395703
  · exact B1395707
  · exact B1395711
  · exact B1395715
  · exact B1395719
  · exact B1395723
  · exact B1395727
  · exact B1395731
  · exact B1395735
  · exact B1395739
  · exact B1395743
  · exact B1395747
  · exact B1395751
  · exact B1395755
  · exact B1395759
  · exact B1395763
  · exact B1395767
  · exact B1395771
  · exact B1395775
  · exact B1395779
  · exact B1395783
  · exact B1395787
  · exact B1395791
  · exact B1395795
  · exact B1395799
  · exact B1395803
  · exact B1395807
  · exact B1395811
  · exact B1395815
  · exact B1395819
  · exact B1395823
  · exact B1395827
  · exact B1395831
  · exact B1395835
  · exact B1395839
  · exact B1395843
  · exact B1395847
  · exact B1395851
  · exact B1395855
  · exact B1395859
  · exact B1395863
  · exact B1395867
  · exact B1395871
  · exact B1395875
  · exact B1395879
  · exact B1395883
  · exact B1395887
  · exact B1395891
  · exact B1395895
  · exact B1395899
  · exact B1395903
  · exact B1395907
  · exact B1395911
  · exact B1395915
  · exact B1395919
  · exact B1395923
  · exact B1395927
  · exact B1395931
  · exact B1395935
  · exact B1395939
  · exact B1395943
  · exact B1395947
  · exact B1395951
  · exact B1395955
  · exact B1395959
  · exact B1395963
  · exact B1395967
  · exact B1395971
  · exact B1395975
  · exact B1395979
  · exact B1395983
  · exact B1395987
  · exact B1395991
  · exact B1395995
  · exact B1395999
  · exact B1396003
  · exact B1396007
  · exact B1396011
  · exact B1396015
  · exact B1396019
  · exact B1396023
  · exact B1396027
  · exact B1396031
  · exact B1396035
  · exact B1396039
  · exact B1396043
  · exact B1396047
  · exact B1396051
  · exact B1396055
  · exact B1396059
  · exact B1396063
  · exact B1396067
  · exact B1396071
  · exact B1396075
  · exact B1396079
  · exact B1396083
  · exact B1396087
  · exact B1396091
  · exact B1396095
  · exact B1396099
  · exact B1396103
  · exact B1396107
  · exact B1396111
  · exact B1396115
  · exact B1396119
  · exact B1396123
  · exact B1396127
  · exact B1396131
  · exact B1396135
  · exact B1396139
  · exact B1396143
  · exact B1396147
  · exact B1396151
  · exact B1396155
  · exact B1396159
  · exact B1396163
  · exact B1396167
  · exact B1396171
  · exact B1396175
  · exact B1396179
  · exact B1396183
  · exact B1396187
  · exact B1396191
  · exact B1396195
  · exact B1396199
  · exact B1396203
  · exact B1396207
  · exact B1396211
  · exact B1396215
  · exact B1396219
  · exact B1396223
  · exact B1396227
  · exact B1396231
  · exact B1396235
  · exact B1396239
  · exact B1396243
  · exact B1396247
  · exact B1396251
  · exact B1396255
  · exact B1396259
  · exact B1396263
  · exact B1396267
  · exact B1396271
  · exact B1396275
  · exact B1396279
  · exact B1396283
  · exact B1396287
  · exact B1396291
  · exact B1396295
  · exact B1396299
  · exact B1396303
  · exact B1396307
  · exact B1396311
  · exact B1396315
  · exact B1396319
  · exact B1396323
  · exact B1396327
  · exact B1396331
  · exact B1396335
  · exact B1396339
  · exact B1396343
  · exact B1396347
  · exact B1396351
  · exact B1396355
  · exact B1396359
  · exact B1396363
  · exact B1396367
  · exact B1396371
  · exact B1396375
  · exact B1396379
  · exact B1396383
  · exact B1396387
  · exact B1396391
  · exact B1396395
  · exact B1396399
  · exact B1396403
  · exact B1396407
  · exact B1396411
  · exact B1396415
  · exact B1396419
  · exact B1396423
  · exact B1396427
  · exact B1396431
  · exact B1396435
  · exact B1396439
  · exact B1396443
  · exact B1396447
  · exact B1396451
  · exact B1396455
  · exact B1396459
  · exact B1396463
  · exact B1396467
  · exact B1396471
  · exact B1396475
  · exact B1396479
  · exact B1396483
  · exact B1396487
  · exact B1396491
  · exact B1396495
  · exact B1396499
  · exact B1396503
  · exact B1396507
  · exact B1396511
  · exact B1396515
  · exact B1396519
  · exact B1396523
  · exact B1396527
  · exact B1396531
  · exact B1396535
  · exact B1396539
  · exact B1396543
  · exact B1396547
  · exact B1396551
  · exact B1396555
  · exact B1396559
  · exact B1396563
  · exact B1396567
  · exact B1396571
  · exact B1396575
  · exact B1396579
  · exact B1396583
  · exact B1396587
  · exact B1396591
  · exact B1396595
  · exact B1396599
  · exact B1396603
  · exact B1396607
  · exact B1396611
  · exact B1396615
  · exact B1396619
  · exact B1396623
  · exact B1396627
  · exact B1396631
  · exact B1396635
  · exact B1396639
  · exact B1396643
  · exact B1396647
  · exact B1396651
  · exact B1396655
  · exact B1396659
  · exact B1396663
  · exact B1396667
  · exact B1396671
  · exact B1396675
  · exact B1396679
  · exact B1396683
  · exact B1396687
  · exact B1396691
  · exact B1396695
  · exact B1396699
  · exact B1396703
  · exact B1396707
  · exact B1396711
  · exact B1396715
  · exact B1396719
  · exact B1396723
  · exact B1396727
  · exact B1396731
  · exact B1396735
  · exact B1396739
  · exact B1396743
  · exact B1396747
  · exact B1396751
  · exact B1396755
  · exact B1396759
  · exact B1396763
  · exact B1396767
  · exact B1396771
  · exact B1396775
  · exact B1396779
  · exact B1396783
  · exact B1396787
  · exact B1396791
  · exact B1396795
  · exact B1396799
  · exact B1396803
  · exact B1396807
  · exact B1396811
  · exact B1396815
  · exact B1396819
  · exact B1396823
  · exact B1396827
  · exact B1396831
  · exact B1396835
  · exact B1396839
  · exact B1396843
  · exact B1396847
  · exact B1396851
  · exact B1396855
  · exact B1396859
  · exact B1396863
  · exact B1396867
  · exact B1396871
  · exact B1396875
  · exact B1396879
  · exact B1396883
  · exact B1396887
  · exact B1396891
  · exact B1396895
  · exact B1396899
  · exact B1396903
  · exact B1396907
  · exact B1396911
  · exact B1396915
  · exact B1396919
  · exact B1396923
  · exact B1396927
  · exact B1396931
  · exact B1396935
  · exact B1396939
  · exact B1396943
  · exact B1396947
  · exact B1396951
  · exact B1396955
  · exact B1396959
  · exact B1396963
  · exact B1396967
  · exact B1396971
  · exact B1396975
  · exact B1396979
  · exact B1396983
  · exact B1396987
  · exact B1396991
  · exact B1396995
  · exact B1396999
  · exact B1397003
  · exact B1397007
  · exact B1397011
  · exact B1397015
  · exact B1397019
  · exact B1397023
  · exact B1397027
  · exact B1397031
  · exact B1397035
  · exact B1397039
  · exact B1397043
  · exact B1397047
  · exact B1397051
  · exact B1397055
  · exact B1397059
  · exact B1397063
  · exact B1397067
  · exact B1397071
  · exact B1397075
  · exact B1397079
  · exact B1397083
  · exact B1397087
  · exact B1397091
  · exact B1397095
  · exact B1397099
  · exact B1397103
  · exact B1397107
  · exact B1397111
  · exact B1397115
  · exact B1397119
  · exact B1397123
  · exact B1397127
  · exact B1397131
  · exact B1397135
  · exact B1397139
  · exact B1397143
  · exact B1397147
  · exact B1397151
  · exact B1397155
  · exact B1397159
  · exact B1397163
  · exact B1397167
  · exact B1397171
  · exact B1397175
  · exact B1397179
  · exact B1397183
  · exact B1397187
  · exact B1397191
  · exact B1397195
  · exact B1397199
  · exact B1397203
  · exact B1397207
  · exact B1397211
  · exact B1397215
  · exact B1397219
  · exact B1397223
  · exact B1397227
  · exact B1397231
  · exact B1397235
  · exact B1397239
  · exact B1397243
  · exact B1397247
  · exact B1397251
  · exact B1397255
  · exact B1397259
  · exact B1397263
  · exact B1397267
  · exact B1397271
  · exact B1397275
  · exact B1397279
  · exact B1397283
  · exact B1397287
  · exact B1397291
  · exact B1397295
  · exact B1397299
  · exact B1397303
  · exact B1397307
  · exact B1397311
  · exact B1397315
  · exact B1397319
  · exact B1397323
  · exact B1397327
  · exact B1397331
  · exact B1397335
  · exact B1397339
  · exact B1397343
  · exact B1397347
  · exact B1397351
  · exact B1397355
  · exact B1397359
  · exact B1397363
  · exact B1397367
  · exact B1397371
  · exact B1397375
  · exact B1397379
  · exact B1397383
  · exact B1397387
  · exact B1397391
  · exact B1397395
  · exact B1397399
  · exact B1397403
  · exact B1397407
  · exact B1397411
  · exact B1397415
  · exact B1397419
  · exact B1397423
  · exact B1397427
  · exact B1397431
  · exact B1397435
  · exact B1397439
  · exact B1397443
  · exact B1397447
  · exact B1397451
  · exact B1397455
  · exact B1397459
  · exact B1397463
  · exact B1397467
  · exact B1397471
  · exact B1397475
  · exact B1397479
  · exact B1397483
  · exact B1397487
  · exact B1397491
  · exact B1397495
  · exact B1397499
  · exact B1397503
  · exact B1397507
  · exact B1397511
  · exact B1397515

theorem solution (m : ℕ) (hlo : 1395517 ≤ m) (hhi : m ≤ 1397517) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 348879 ≤ j := by omega
    have hj2 : j ≤ 349378 := by omega
    have hb : Blo 1395517 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
